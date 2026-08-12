#!/usr/bin/env python3
"""Verify intra-workspace version pins are in lockstep (issue #145).

A release bumps `[workspace.package].version` in the root `Cargo.toml`. Every
intra-workspace path dependency also carries an explicit `version = "X.Y.Z"`
pin (added in #136 so `cargo publish` has real crates.io coordinates), and
`MODULE.bazel` carries a matching `module(version = ...)`. If any of these drift
from the workspace version, `cargo` refuses to resolve and BOTH `release.yml`
and `publish-to-crates-io.yml` break at tag-push time — exactly what sank the
v0.7.0 tag (recovered by the 23-pin sweep in #143).

This gate fails at PR-merge time instead, making the desync structurally
uncatchable-too-late. Run with no args from the repo root; exits non-zero and
prints every offending pin on mismatch.
"""

from __future__ import annotations

import glob
import re
import sys
from pathlib import Path

VERSION_RE = re.compile(r'version\s*=\s*"([^"]+)"')


def workspace_version(root: Path) -> str:
    """Extract `version` from the root Cargo.toml `[workspace.package]` table."""
    in_section = False
    for line in (root / "Cargo.toml").read_text().splitlines():
        stripped = line.strip()
        if stripped.startswith("["):
            in_section = stripped == "[workspace.package]"
            continue
        if in_section:
            m = VERSION_RE.match(stripped)
            if m:
                return m.group(1)
    sys.exit("ERROR: no [workspace.package] version found in Cargo.toml")


def check_path_dep_pins(root: Path, expected: str) -> list[str]:
    """Every `{ path = "../sibling", version = "X" }` pin must equal `expected`."""
    errors: list[str] = []
    for path in sorted(glob.glob(str(root / "crates" / "*" / "Cargo.toml"))):
        rel = Path(path).relative_to(root)
        for n, line in enumerate(Path(path).read_text().splitlines(), 1):
            # An intra-workspace pin is a single inline table carrying BOTH a
            # relative `path =` and a `version =`. (Plain `version = "..."` for
            # the crate's own [package] or for external deps is ignored.)
            if 'path = "../' in line and "version" in line:
                m = VERSION_RE.search(line)
                if m and m.group(1) != expected:
                    name = line.split("=", 1)[0].strip()
                    errors.append(
                        f"{rel}:{n}: path-dep `{name}` pinned at "
                        f'"{m.group(1)}" but workspace is "{expected}"'
                    )
    return errors


def check_module_bazel(root: Path, expected: str) -> list[str]:
    """`module(version = ...)` in MODULE.bazel must equal `expected`."""
    mod = root / "MODULE.bazel"
    if not mod.exists():
        return []
    in_module = False
    for n, line in enumerate(mod.read_text().splitlines(), 1):
        if line.startswith("module("):
            in_module = True
        if in_module:
            m = VERSION_RE.search(line)
            if m:
                if m.group(1) != expected:
                    return [
                        f"MODULE.bazel:{n}: module version "
                        f'"{m.group(1)}" but workspace is "{expected}"'
                    ]
                return []
        if in_module and line.startswith(")"):
            break
    return []


def workspace_members(root: Path) -> list[str]:
    """Crate names from `[workspace] members` — the set `Cargo.lock` must carry."""
    members: list[str] = []
    in_members = False
    for line in (root / "Cargo.toml").read_text().splitlines():
        stripped = line.strip()
        if stripped.startswith("members"):
            in_members = True
            continue
        if in_members:
            if stripped.startswith("]"):
                break
            m = re.match(r'"crates/([^"]+)"', stripped)
            if m:
                members.append(m.group(1))
    return members


def check_cargo_lock(root: Path, expected: str) -> list[str]:
    """#924: every workspace member must appear in `Cargo.lock` at `expected`.

    This surface had NO gate. The only `--locked` anywhere in `ci.yml` is
    `cargo install --locked kani-verifier` — installing a tool, not verifying
    this lockfile — so a lock left at the previous version builds and tests
    green all the way to a tag. Measured twice by hand and never by a gate: the
    v0.52 cold review, and again during v0.55 assembly where the lock held ZERO
    `0.55.0` entries after the bump.
    """
    lock = root / "Cargo.lock"
    if not lock.exists():
        return [f"Cargo.lock missing at {lock}"]
    text = lock.read_text()
    # `name = "x"` followed within the same [[package]] block by `version = "y"`.
    versions: dict[str, str] = {}
    name: str | None = None
    for line in text.splitlines():
        s = line.strip()
        if s == "[[package]]":
            name = None
        elif s.startswith("name = "):
            q = re.match(r'name\s*=\s*"([^"]+)"', s)
            name = q.group(1) if q else None
        elif s.startswith("version = ") and name is not None:
            q = VERSION_RE.match(s)
            if q:
                versions[name] = q.group(1)
                name = None
    errors: list[str] = []
    for member in workspace_members(root):
        got = versions.get(member)
        if got is None:
            errors.append(f"Cargo.lock: workspace member `{member}` has no entry")
        elif got != expected:
            errors.append(
                f'Cargo.lock: `{member}` locked at "{got}" but workspace is "{expected}"'
            )
    return errors


def check_npm_package(root: Path, expected: str) -> list[str]:
    """#924: `npm/package.json` version must equal the workspace version.

    The npm wrapper is a published release surface; nothing gated it.
    """
    pkg = root / "npm" / "package.json"
    if not pkg.exists():
        return []
    for n, line in enumerate(pkg.read_text().splitlines(), 1):
        m = re.match(r'\s*"version"\s*:\s*"([^"]+)"', line)
        if m:
            if m.group(1) != expected:
                return [
                    f'npm/package.json:{n}: version "{m.group(1)}" '
                    f'but workspace is "{expected}"'
                ]
            return []
    return ["npm/package.json: no `version` key found"]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    expected = workspace_version(root)
    errors = (
        check_path_dep_pins(root, expected)
        + check_module_bazel(root, expected)
        + check_cargo_lock(root, expected)
        + check_npm_package(root, expected)
    )
    if errors:
        print(f"Version-pin desync (workspace = {expected}) — issues #145/#924:\n")
        for e in errors:
            print(f"  {e}")
        print(
            "\nBump every release surface in lockstep with "
            "[workspace.package].version before tagging:\n"
            "  1. intra-workspace path-dep `version =` pins (crates/*/Cargo.toml)\n"
            "  2. MODULE.bazel `module(version = ...)`\n"
            "  3. Cargo.lock          — regenerate with `cargo metadata`\n"
            "  4. npm/package.json\n"
        )
        return 1
    print(
        f"OK: path-dep pins + MODULE.bazel + Cargo.lock + npm/package.json "
        f"all at {expected}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
