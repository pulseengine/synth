#!/usr/bin/env python3
"""Oracle for compliance.yml's `Sync rivet externals` step (#1453, RQ-82-COMPLIANCE2).

WHY THIS EXISTS. The step as first shipped reported `synced N of N` with rc=0 while
every external directory was EMPTY -- the exact condition it was written to refuse.
Two independent defects:

  1. `dest.exists()` treated directory EXISTENCE as a synced external, so an empty
     or partial `.rivet/repos/<prefix>` counted.
  2. the non-vacuity check compared `len(cloned)` against `len(ext)`, where `cloned`
     was appended to by the very loop it guarded. A counter the loop increments can
     only ever equal the population, so the check was UNREACHABLE by construction.

This test runs the SHIPPED heredoc extracted from the workflow -- never a copy --
because a hand-written mirror of the thing under test is the drift the North Star
forbids, and because the defect above lived in the shipped text, not in a model of it.
"""
import pathlib
import re
import subprocess
import sys
import tempfile

WORKFLOW = pathlib.Path(__file__).resolve().parent.parent / ".github/workflows/compliance.yml"
# Anchored on the heredoc delimiters so a reindent or a surrounding-step edit cannot
# silently select a different block.
HEREDOC = re.compile(r"python3 - <<'PYEOF'\n(.*?)^\s*PYEOF$", re.S | re.M)


def shipped_script() -> str:
    text = WORKFLOW.read_text()
    blocks = HEREDOC.findall(text)
    if len(blocks) != 1:
        raise SystemExit(
            f"REFUSE: expected exactly ONE PYEOF heredoc in {WORKFLOW.name}, found "
            f"{len(blocks)}. The extractor must not guess which block is the sync step."
        )
    body = blocks[0]
    # strip the uniform YAML block indent; measured, not assumed
    lines = [ln for ln in body.split("\n")]
    indents = [len(ln) - len(ln.lstrip()) for ln in lines if ln.strip()]
    pad = min(indents)
    return "\n".join(ln[pad:] if ln.strip() else "" for ln in lines)


def _make_source(path: pathlib.Path, with_yaml: bool):
    """A real local git repo, so `git clone` DETERMINISTICALLY succeeds offline.

    The first version of this test used `https://example.invalid/...`, so every
    clone failed with 'Could not resolve host' and the red-first case passed
    because the NETWORK failed -- not because the resolution check fired. A test
    that cannot say WHICH refusal it got cannot certify the fix.
    """
    path.mkdir(parents=True)
    if with_yaml:
        (path / "artifact.yaml").write_text("artifacts: []\n")
    (path / "README.md").write_text("src\n")
    env = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
           "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t",
           "PATH": __import__("os").environ["PATH"], "HOME": str(path)}
    for cmd in (["git", "init", "-q", "-b", "main"], ["git", "add", "-A"],
                ["git", "commit", "-q", "-m", "src"]):
        r = subprocess.run(cmd, cwd=path, capture_output=True, text=True, env=env)
        if r.returncode != 0:
            raise SystemExit(f"fixture setup failed: {cmd} -> {r.stderr}")


def _rivet_yaml(src_a: pathlib.Path, src_b: pathlib.Path) -> str:
    return (
        "externals:\n"
        f"  alpha:\n    git: {src_a}\n    prefix: alpha\n    ref: main\n"
        f"  beta:\n    git: {src_b}\n    prefix: beta\n    ref: main\n"
    )


def _run(tmp: pathlib.Path, script: str, rivet: str):
    (tmp / "rivet.yaml").write_text(rivet)
    return subprocess.run([sys.executable, "-c", script], cwd=tmp,
                          capture_output=True, text=True)


def case_empty_dirs_self_heal(script):
    """Empty `.rivet/repos/<prefix>` dirs + valid sources -> RECOVER, rc=0.

    The old step accepted these as synced (`synced 2 of 2`, rc=0, nothing cloned).
    The fix removes the stale tree and re-clones, so the outcome is still green --
    but green because the externals ARE now resolved, which is a different fact.
    """
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        a, b = tmp / "src_a", tmp / "src_b"
        _make_source(a, True); _make_source(b, True)
        work = tmp / "work"; work.mkdir()
        for pfx in ("alpha", "beta"):
            (work / ".rivet/repos" / pfx).mkdir(parents=True)
        r = _run(work, script, _rivet_yaml(a, b))
        resolved = all((work / ".rivet/repos" / p / "artifact.yaml").exists()
                       for p in ("alpha", "beta"))
        ok = r.returncode == 0 and "synced 2 of 2" in r.stdout and resolved
        return ok, f"rc={r.returncode} resolved={resolved} out={(r.stdout + r.stderr).strip()[:110]!r}"


def case_clone_without_artifacts_refused(script):
    """THE CRITICAL CASE: clone SUCCEEDS but yields no artifacts -> REFUSE, naming it.

    This is the branch the original check could not reach, because it compared
    `len(cloned)` -- a counter its own loop incremented -- against `len(ext)`.
    The refusal must come from the RESOLUTION check, so the assertion requires the
    word RESOLVED and the external's name, and forbids a clone-failure refusal.
    """
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        a, b = tmp / "src_a", tmp / "src_b"
        _make_source(a, True); _make_source(b, False)   # beta carries NO yaml
        work = tmp / "work"; work.mkdir()
        r = _run(work, script, _rivet_yaml(a, b))
        blob = r.stdout + r.stderr
        ok = (r.returncode != 0 and "UNRESOLVED" in blob and "beta" in blob
              and "clone of" not in blob)
        return ok, f"rc={r.returncode} out={blob.strip()[:150]!r}"


def case_resolved_dirs_accepted(script):
    """POSITIVE CONTROL: already-resolved dirs -> rc=0 without touching the network."""
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        work = tmp / "work"; work.mkdir()
        for pfx in ("alpha", "beta"):
            dest = work / ".rivet/repos" / pfx
            (dest / ".git").mkdir(parents=True)
            (dest / "artifact.yaml").write_text("artifacts: []\n")
        r = _run(work, script, _rivet_yaml(tmp / "nonexistent_a", tmp / "nonexistent_b"))
        ok = r.returncode == 0 and "synced 2 of 2" in r.stdout
        return ok, f"rc={r.returncode} out={(r.stdout + r.stderr).strip()[:110]!r}"


def case_clone_failure_refused(script):
    """A genuinely unreachable source -> REFUSE from the CLONE branch, named as such.

    Paired with the case above: together they show the two refusals are
    DISTINGUISHABLE, which is what the first version of this test could not do.
    """
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        a = tmp / "src_a"; _make_source(a, True)
        work = tmp / "work"; work.mkdir()
        r = _run(work, script, _rivet_yaml(a, tmp / "does_not_exist_at_all"))
        blob = r.stdout + r.stderr
        ok = r.returncode != 0 and "clone of beta failed" in blob
        return ok, f"rc={r.returncode} out={blob.strip()[:110]!r}"


def case_zero_population_refused(script):
    """The pre-existing zero-population guard, kept honest."""
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        r = _run(tmp, script, "externals: {}\n")
        blob = r.stdout + r.stderr
        return (r.returncode != 0 and "NO externals" in blob), f"rc={r.returncode}"


CASES = (
    ("empty dirs SELF-HEAL to resolved", case_empty_dirs_self_heal),
    ("clone w/o artifacts REFUSED as UNRESOLVED (was unreachable)", case_clone_without_artifacts_refused),
    ("already-resolved ACCEPTED (positive control)", case_resolved_dirs_accepted),
    ("clone failure REFUSED, distinguishably", case_clone_failure_refused),
    ("zero population REFUSED", case_zero_population_refused),
)


def main():
    script = shipped_script()
    print(f"extracted {len(script.splitlines())} lines of SHIPPED sync script")
    failures = 0
    for label, fn in CASES:
        ok, detail = fn(script)
        print(f"  [{'PASS' if ok else 'FAIL'}] {label}: {detail}")
        failures += not ok
    print(f"\n{len(CASES) - failures}/{len(CASES)} cases pass")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
