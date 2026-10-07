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
import tomllib
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
    """Every intra-workspace `path` dependency carrying a `version` must equal
    `expected`.

    RQ-81-PINSWEEP (#1457): this was a LINE SCAN requiring `path` and `version`
    on ONE line, so the equivalent block form was invisible —

        [dependencies.synth-core]
        path = "../synth-core"
        version = "0.78.0"        # stale; the scan printed OK

    Measured with a paired control on the v0.80 tree: the block form at a stale
    version gave 0 errors while the inline equivalent gave 1. Latent there (no
    crate used the block form), which is why it was cheap to close.

    Now parsed with `tomllib`, so BOTH spellings are the same thing to the gate
    — the project's own rule against hand-rolling a parser to measure the
    codebase, applied to the gate that measures the release.
    """
    errors: list[str] = []
    for path in sorted(glob.glob(str(root / "crates" / "*" / "Cargo.toml"))):
        rel = Path(path).relative_to(root)
        try:
            doc = tomllib.loads(Path(path).read_text())
        except tomllib.TOMLDecodeError as why:
            errors.append(f"{rel}: not parseable as TOML ({why}) — a gate that "
                          f"cannot read a manifest must not pass it")
            continue
        for table in ("dependencies", "dev-dependencies", "build-dependencies"):
            for name, spec in (doc.get(table) or {}).items():
                if not isinstance(spec, dict):
                    continue
                if "path" not in spec or "version" not in spec:
                    continue
                if spec["version"] != expected:
                    errors.append(
                        f'{rel}: path-dep `{name}` in [{table}] pinned at '
                        f'"{spec["version"]}" but workspace is "{expected}"')
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
    """Crate names from `[workspace] members` — the set `Cargo.lock` must carry.

    RQ-81-PINSWEEP (#1457): this walked lines and required `members` to open a
    multi-line array, so `members = [...]` on ONE line returned an EMPTY LIST.
    `check_cargo_lock` then iterated nothing and the gate printed OK over a
    lockfile whose every entry was wrong. Measured: `members` on one line plus
    all 19 workspace entries set to `0.1.0` gave rc=0, while the SAME lock
    damage with `members` multi-line gave rc=1 — so the lock check worked and
    the members parse was what disabled it.

    A DERIVED POPULATION OF ZERO IS A REFUSAL, NOT A PASS, so the empty case is
    now raised by the caller rather than silently iterating nothing.
    """
    doc = tomllib.loads((root / "Cargo.toml").read_text())
    members = (doc.get("workspace") or {}).get("members") or []
    out: list[str] = []
    for m in members:
        if isinstance(m, str) and m.startswith("crates/"):
            out.append(m.split("/", 1)[1])
    return out


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
    members = workspace_members(root)
    if not members:
        # RQ-81-PINSWEEP (#1457): with no members this loop asserts NOTHING and
        # the gate used to print OK. A derived population of zero is a refusal.
        return [
            "Cargo.toml: [workspace] members derived EMPTY, so the Cargo.lock "
            "check would assert nothing at all. That is a parse failure or a "
            "malformed manifest, not a clean workspace"
        ]
    for member in members:
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
