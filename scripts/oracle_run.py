#!/usr/bin/env python3
r"""oracle_run — run an execution oracle and assert that it EXECUTED something.

The problem this exists to kill (#910 F10, on top of #890)
--------------------------------------------------------------------------
#890 wired 63 forgotten oracles into CI. Measured on the result: **152 of the
160 workflow steps that run a `scripts/repro/` oracle asserted nothing beyond
the process exit code** — not only the newly wired ones, the pre-existing
hand-wired steps too. Exactly 8 asserted a printed verdict or a count.

Exit 0 does not distinguish

    "compiled 40 fixtures, emulated 240 vectors, all bit-identical to wasmtime"

from

    "the fixture list came back empty, the loop body never ran, printed PASS".

That is #890's inert gate one level down: the oracle is wired, but *what it
attests* is unstated. A differential that executes zero comparisons and exits 0
is the exact shape of a green-but-meaningless number.

WHAT IS COUNTED, and why that word
--------------------------------------------------------------------------
This driver runs the oracle IN-PROCESS (`runpy`) with three entry points
wrapped:

    unicorn.Uc.emu_start   -> `emulations`     (a real emulator entry)
    wasmtime.Func.__call__ -> `wasmtime_calls` (a real reference execution)
    subprocess `synth … compile …` -> `compiles` (a real compilation)

The first two are the ends of a differential: run the compiled bytes, run the
reference, compare. Counting them counts EXECUTION — a comparison loop that
never runs cannot fake it, because the count comes from the emulator, not from
the harness's own bookkeeping.

`compiles` exists for the oracles whose work is not emulation: decline
matrices, byte-identity legs, symtab/relocation validators, and the native
(non-unicorn) aarch64 matrix. Those still drive the compiler, and "the harness
compiled nothing" is exactly the vacuity that needs catching there. It is the
WEAKEST of the three and is only declared where the stronger two cannot hold on
every invocation of that script.

The unit is named `emulations`, NOT "checks", and that is deliberate. The
calibration (docs in scripts/repro/ORACLE_WIRING.md) found the ratio to a
harness's self-reported check count is NOT 1:1 — some harnesses emulate once
per vector, some enter the emulator several times per vector, some compare
several values out of one run. This lane exists because an instrument was
reporting something other than what its name implied; shipping a number
labelled "checks" that actually counts emulator entries would repeat the defect
being fixed. `emulations` is what is measured, so `emulations` is what it is
called.

THE DECLARATION — one `# ci-checks:` header per oracle
--------------------------------------------------------------------------
Same locality argument as `# ci-status:` (see ORACLE_WIRING.md): the floor
lives in the file it describes, so it shows up in the diff of the PR that adds
the oracle, and it cannot outlive its file the way a manifest entry can.

    # ci-checks: emulations >= 24
    # ci-checks: wasmtime >= 8
    # ci-checks: compiles >= 2
    # ci-checks: stdout /^#846 CHECKS=(\d+)\/75$/ >= 75
    # ci-checks: none — <>= 20 chars saying why nothing can be bound>

Declare the STRONGEST mode that holds on EVERY invocation of that script in
CI — several oracles are run twice, once executing and once on a decline /
byte-identity leg that executes nothing by design, and a floor that only holds
for the good leg is not a floor. What the weaker floor gives up is not lost:
every counter is still MEASURED and recorded, so the ledger reports what ran
while the gate asserts what is guaranteed.

`stdout` mode is for the oracles that execute nothing emulatable (structural
validators, decline matrices, symtab differentials). Its regex must carry
exactly one capture group holding an integer, so it asserts a COUNT and not
merely the presence of a happy-path string.

FLOORS, NEVER EQUALITY. `>=` so that adding a fixture cannot redden a step; the
ratchet direction is up. `scripts/oracle_wiring_check.py` sums the declared
floors, and `claims.yaml` pins the total.

Exit: the oracle's own exit code, unless a floor is unmet (then 1). An oracle
that exits 0 having emulated nothing FAILS here.
"""

import argparse
import io
import os
import pathlib
import re
import runpy
import sys
import time

DECL_RE = re.compile(
    r"^#\s*ci-checks:\s*"
    r"(?P<mode>emulations|wasmtime|compiles|stdout|none)\b"
    r"\s*(?P<rest>.*)$",
    re.MULTILINE,
)

# `stdout /<regex>/ >= N`
STDOUT_RE = re.compile(r"^/(?P<rx>.+)/\s*>=\s*(?P<min>\d+)\s*$")
# `emulations >= N` / `wasmtime >= N`
NUM_RE = re.compile(r"^>=\s*(?P<min>\d+)\s*$")

MIN_REASON_CHARS = 20

# Resolved at IMPORT, before any oracle has had the chance to chdir.
# `ORACLE_EVIDENCE_JSONL` is set to a *relative* path by the workflow, and
# oracles run in-process (`runpy`), so a harness that chdir's into a scratch
# directory silently redirects the append into that directory — which is then
# deleted. The record vanishes, the ledger comes up short, and the job reads as
# "an oracle is missing" when in fact it ran and passed. Exactly one of the four
# WCET phase scripts chdir's, and exactly that one went missing.
_LEDGER_PATH = (
    os.path.abspath(os.environ["ORACLE_EVIDENCE_JSONL"])
    if os.environ.get("ORACLE_EVIDENCE_JSONL")
    else None
)


class Decl:
    """A parsed `# ci-checks:` declaration."""

    def __init__(self, mode, minimum=0, regex=None, reason=""):
        self.mode = mode
        self.minimum = minimum
        self.regex = regex
        self.reason = reason

    def __repr__(self):  # pragma: no cover - diagnostics only
        return f"Decl({self.mode}, min={self.minimum}, rx={self.regex})"


def parse_decl(text, rel):
    """Parse the single `# ci-checks:` header. Returns (Decl, error-or-None)."""
    decls = list(DECL_RE.finditer(text))
    if not decls:
        return None, (
            f"{rel}: no `# ci-checks:` header. Every oracle must declare what it "
            f"attests: `emulations >= N` | `wasmtime >= N` | "
            f"`stdout /<rx with one int group>/ >= N` | `none — <reason>`."
        )
    if len(decls) > 1:
        return None, f"{rel}: {len(decls)} `# ci-checks:` lines — exactly one is allowed"

    m = decls[0]
    mode = m.group("mode")
    rest = (m.group("rest") or "").strip()

    if mode == "none":
        reason = rest.lstrip("-—: ").strip()
        if len(reason) < MIN_REASON_CHARS:
            return None, (
                f"{rel}: `ci-checks: none` needs a REAL reason "
                f"(>= {MIN_REASON_CHARS} chars) saying what cannot be bound; "
                f"got {reason!r}"
            )
        return Decl("none", reason=reason), None

    if mode == "stdout":
        sm = STDOUT_RE.match(rest)
        if not sm:
            return None, (
                f"{rel}: `ci-checks: stdout` wants `/<regex>/ >= N`; got {rest!r}"
            )
        try:
            rx = re.compile(sm.group("rx"), re.MULTILINE)
        except re.error as exc:
            return None, f"{rel}: `ci-checks: stdout` regex does not compile: {exc}"
        if rx.groups != 1:
            return None, (
                f"{rel}: `ci-checks: stdout` regex must have EXACTLY ONE capture "
                f"group holding the count (got {rx.groups}) — a pattern with no "
                f"group asserts a happy-path STRING, not that anything ran."
            )
        return Decl("stdout", int(sm.group("min")), regex=rx), None

    nm = NUM_RE.match(rest)
    if not nm:
        return None, f"{rel}: `ci-checks: {mode}` wants `>= N`; got {rest!r}"
    return Decl(mode, int(nm.group("min"))), None


class Counters:
    def __init__(self):
        self.emulations = 0
        self.wasmtime_calls = 0
        self.compiles = 0


def _is_synth_compile(argv):
    """True for a subprocess that is `<...>/synth … compile …`.

    Deliberately narrow: `nm`, `objdump` and `wat2wasm` runs are not evidence
    that the thing under test did anything.
    """
    try:
        if isinstance(argv, (str, bytes, os.PathLike)):
            return False
        parts = [os.fsdecode(a) for a in argv]
    except (TypeError, ValueError):
        return False
    if not parts:
        return False
    exe = os.path.basename(parts[0]).lower()
    if not (exe == "synth" or exe.startswith("synth")):
        return False
    return "compile" in parts[1:]


def install_probes(counters):
    """Wrap the two library entry points. Returns the list of names wrapped.

    Deliberately NOT an import hook or a `sitecustomize` shim: the wrap happens
    here, before the oracle runs, and `sys.modules` caching means a later
    `import unicorn` / `from unicorn import Uc` inside the oracle gets the same
    already-patched class object.
    """
    wrapped = []

    try:
        import unicorn
    except ImportError:
        unicorn = None
    if unicorn is not None and hasattr(unicorn, "Uc"):
        orig_emu = unicorn.Uc.emu_start

        def emu_start(self, *a, **kw):
            counters.emulations += 1
            return orig_emu(self, *a, **kw)

        unicorn.Uc.emu_start = emu_start
        wrapped.append("unicorn.Uc.emu_start")

    try:
        import wasmtime
    except ImportError:
        wasmtime = None
    if wasmtime is not None and hasattr(wasmtime, "Func"):
        orig_call = wasmtime.Func.__call__

        def func_call(self, *a, **kw):
            counters.wasmtime_calls += 1
            return orig_call(self, *a, **kw)

        wasmtime.Func.__call__ = func_call
        wrapped.append("wasmtime.Func.__call__")

    # Every harness reaches the compiler through subprocess.Popen — `run`,
    # `check_output`, `call` and `check_call` are all thin wrappers over it, so
    # patching the class catches all of them, including a harness that imported
    # `run` by name before this ran.
    import subprocess

    orig_popen_init = subprocess.Popen.__init__

    def popen_init(self, args, *a, **kw):
        if _is_synth_compile(args):
            counters.compiles += 1
        return orig_popen_init(self, args, *a, **kw)

    subprocess.Popen.__init__ = popen_init
    wrapped.append("subprocess.Popen")

    return wrapped


class Tee(io.TextIOBase):
    """Mirror the oracle's stdout to the real stdout AND to a buffer.

    The CI log must keep showing exactly what the oracle printed — a driver that
    swallowed the harness output would make every failure harder to read than
    before, which is not a trade worth making for a count.
    """

    def __init__(self, real):
        self.real = real
        self.buf = io.StringIO()

    def write(self, s):
        self.buf.write(s)
        return self.real.write(s)

    def flush(self):
        self.real.flush()

    @property
    def encoding(self):  # some harnesses inspect it
        return getattr(self.real, "encoding", "utf-8")

    def isatty(self):
        return False

    def writable(self):
        return True


def run_oracle(script, argv):
    """Execute `script` in-process. Returns (exit_code, counters, stdout_text)."""
    counters = Counters()
    install_probes(counters)

    real_out = sys.stdout
    tee = Tee(real_out)
    saved_argv, saved_path, saved_cwd = sys.argv[:], sys.path[:], os.getcwd()

    # `python script.py` puts the script's OWN directory at sys.path[0];
    # runpy.run_path does not, and several repro harnesses import sibling
    # helpers. Reproduce the plain-interpreter behaviour so the driver is not
    # observably different from the invocation it replaces.
    sys.path.insert(0, os.path.dirname(os.path.abspath(script)))
    sys.argv = [script] + list(argv)
    sys.stdout = tee
    code = 0
    try:
        runpy.run_path(script, run_name="__main__")
    except SystemExit as exc:  # the normal exit path of every repro harness
        c = exc.code
        code = 0 if c is None else (c if isinstance(c, int) else 1)
    finally:
        sys.stdout = real_out
        sys.argv, sys.path = saved_argv, saved_path
        # The third piece of interpreter state an in-process oracle can move.
        # Restoring argv and sys.path but not cwd is what let a chdir'ing
        # harness redirect everything written afterwards on a relative path.
        os.chdir(saved_cwd)
    return code, counters, tee.buf.getvalue()


def evaluate(decl, code, counters, out, rel):
    """Apply the declared floor. Returns (ok, measured, failures)."""
    fails = []
    if decl.mode == "emulations":
        measured = counters.emulations
    elif decl.mode == "wasmtime":
        measured = counters.wasmtime_calls
    elif decl.mode == "compiles":
        measured = counters.compiles
    elif decl.mode == "stdout":
        hits = decl.regex.findall(out)
        try:
            measured = max(int(h) for h in hits) if hits else 0
        except (TypeError, ValueError):
            measured = 0
            fails.append(
                f"{rel}: `ci-checks: stdout` regex matched, but its capture group "
                f"is not an integer: {hits[:3]!r}"
            )
        if not hits:
            fails.append(
                f"{rel}: `ci-checks: stdout` pattern {decl.regex.pattern!r} did NOT "
                f"match the oracle's output — the declared evidence line is gone "
                f"or renamed."
            )
    else:  # none
        measured = None

    if measured is not None and measured < decl.minimum:
        fails.append(
            f"{rel}: VACUOUS — declared floor {decl.mode} >= {decl.minimum}, "
            f"measured {measured}. The oracle exited {code} having executed "
            f"{'nothing' if measured == 0 else 'less than it claims'}; that is a "
            f"gate that cannot fail, not a passing gate."
        )
    return not fails, measured, fails


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("script", help="path to the scripts/repro/ oracle")
    ap.add_argument("args", nargs=argparse.REMAINDER, help="arguments for it")
    ap.add_argument(
        "--report-only",
        action="store_true",
        help="print the measurement, do not enforce the floor (calibration only)",
    )
    args = ap.parse_args()

    script = args.script
    rel = os.path.relpath(script)
    if not os.path.isfile(script):
        sys.exit(f"oracle_run: no such oracle: {script}")

    decl, err = parse_decl(pathlib.Path(script).read_text(errors="ignore"), rel)
    if err and not args.report_only:
        sys.exit(f"oracle_run: {err}")

    t0 = time.time()
    code, counters, out = run_oracle(script, args.args)
    dt = time.time() - t0

    if args.report_only:
        print(
            f"ORACLE-CALIBRATION script={os.path.basename(script)} "
            f"emulations={counters.emulations} "
            f"wasmtime_calls={counters.wasmtime_calls} "
            f"compiles={counters.compiles} "
            f"exit={code} secs={dt:.1f}"
        )
        return 0

    ok, measured, fails = evaluate(decl, code, counters, out, rel)

    print(
        f"ORACLE-EVIDENCE script={os.path.basename(script)} "
        f"mode={decl.mode} floor={decl.minimum} measured={measured} "
        f"emulations={counters.emulations} wasmtime_calls={counters.wasmtime_calls} "
        f"compiles={counters.compiles} exit={code}"
    )

    # Append to the per-job ledger, if the job asked for one. Written even on
    # failure: a run that fell BELOW its floor is exactly the datum worth having.
    ledger = _LEDGER_PATH
    if ledger:
        import json

        with open(ledger, "a") as fh:
            fh.write(
                json.dumps(
                    {
                        "script": rel,
                        "mode": decl.mode,
                        "floor": decl.minimum,
                        "measured": measured,
                        "emulations": counters.emulations,
                        "wasmtime_calls": counters.wasmtime_calls,
                        "compiles": counters.compiles,
                        "exit": code,
                        "ok": bool(ok and code == 0),
                    },
                    sort_keys=True,
                )
                + "\n"
            )

    for f in fails:
        print(f"FAIL {f}", file=sys.stderr)

    # The oracle's own verdict still rules: a differential that found a
    # miscompile must stay red even if it emulated plenty.
    if code != 0:
        return code
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
