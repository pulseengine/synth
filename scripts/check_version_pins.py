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


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    expected = workspace_version(root)
    errors = check_path_dep_pins(root, expected) + check_module_bazel(root, expected)
    if errors:
        print(f"Version-pin desync (workspace = {expected}) — issue #145:\n")
        for e in errors:
            print(f"  {e}")
        print(
            "\nBump every intra-workspace path-dep `version =` pin + MODULE.bazel "
            "in lockstep with [workspace.package].version before tagging.\n"
            "Helper: scripts/check_version_pins.py is the gate; the sweep itself "
            "is a one-liner perl over Cargo.toml + MODULE.bazel."
        )
        return 1
    print(f"OK: all intra-workspace pins + MODULE.bazel at {expected}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
