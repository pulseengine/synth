#!/usr/bin/env python3
"""repo_metadata_check — pin the GitHub About surface (description + topics).

The repo description and topic set are part of the public claim surface (they
say what synth IS), and they drifted badly once already (pre-v0.47 they named
neither AArch64 nor WCET nor the proof story). The EXPECTED values live in
`claims.yaml` under `repo_metadata:`; this script fetches the live values from
the GitHub API and fails on mismatch — so the About box can only change
together with the ledger.

Failure semantics (deliberate):
  * metadata MISMATCH        -> exit 1 (red)  — fix GitHub or the ledger
  * API/network unavailable  -> exit 0 with a LOUD SKIP warning — a network
    flake or an unauthenticated rate-limit must never false-red a merge.
    The check is best-effort infrastructure, the ledger is the truth.

Usage:  scripts/repo_metadata_check.py [claims.yaml]
Auth:   uses $GITHUB_TOKEN / $GH_TOKEN when set (CI passes the job token).
"""

import json
import os
import pathlib
import sys
import urllib.error
import urllib.request

try:
    import yaml
except ImportError:
    sys.exit("repo_metadata_check: needs PyYAML  (pip install pyyaml)")


def skip(reason):
    print("=" * 72)
    print(f"WARNING: repo metadata check SKIPPED — {reason}")
    print("The GitHub About surface was NOT verified this run. If this")
    print("persists across runs, check it manually against claims.yaml's")
    print("repo_metadata section.")
    print("=" * 72)
    sys.exit(0)


def fetch(repo):
    url = f"https://api.github.com/repos/{repo}"
    req = urllib.request.Request(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "synth-repo-metadata-check",
        },
    )
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode())


def main():
    path = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "claims.yaml")
    if not path.exists():
        sys.exit(f"repo_metadata_check: {path} not found")
    data = yaml.safe_load(path.read_text()) or {}
    expected = data.get("repo_metadata")
    if not expected:
        sys.exit("repo_metadata_check: claims.yaml has no repo_metadata section")

    repo = expected["repo"]
    try:
        live = fetch(repo)
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, OSError) as e:
        skip(f"GitHub API unreachable for {repo}: {e}")
    except json.JSONDecodeError as e:
        skip(f"GitHub API returned unparseable JSON for {repo}: {e}")

    fails = []
    want_desc = expected["description"]
    got_desc = live.get("description")
    if got_desc != want_desc:
        fails.append(
            "description drifted:\n"
            f"  pinned: {want_desc!r}\n"
            f"  live:   {got_desc!r}"
        )
    want_topics = sorted(expected.get("topics", []))
    got_topics = sorted(live.get("topics", []))
    if got_topics != want_topics:
        missing = sorted(set(want_topics) - set(got_topics))
        extra = sorted(set(got_topics) - set(want_topics))
        fails.append(
            f"topics drifted: missing={missing} unexpected={extra}\n"
            f"  pinned: {want_topics}\n"
            f"  live:   {got_topics}"
        )

    if fails:
        print(f"FAIL repo metadata for {repo} drifted from claims.yaml:")
        for f in fails:
            print(f"  {f}")
        print(
            "\nEither restore the GitHub About settings or change the ledger "
            "TOGETHER with the intent — never leave them disagreeing."
        )
        sys.exit(1)
    print(f"ok   repo metadata for {repo} matches claims.yaml (description + topics)")


if __name__ == "__main__":
    main()
