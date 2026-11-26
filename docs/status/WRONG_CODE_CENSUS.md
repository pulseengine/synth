# Wrong-code census

RQ-91-WRONGCODECENSUS (Refs #1741), the week-one census of the v0.92 plan's
Bet A ("wrong code, with a number").

## What is counted

Every issue open in the population snapshot (the timestamp, command and
highest issue number are in the generated block below), and every issue filed
after it that was still open at the re-measurement, was read in full, not by
its title, and put in exactly one class. An issue closed since the snapshot
keeps its row, which still asserts its status both ways:

- **wrong-code**: synth exits 0 and its output is wrong. That covers a wrong
  value, a call bound to the wrong function, a spurious trap, an instruction
  the declared target cannot execute, and an export silently dropped from the
  object (#1746).
- **loud decline / missing feature**: synth refuses, or a feature is absent.
  A refusal is reach, not wrong code.
- **machinery / docs / tooling**: CI, release gates, process, documentation,
  and tools that print wrong text without emitting wrong code (#1704, the
  disassembler listing).
- **unclear**: no defined right answer to compare against. #1207 is an
  invalid module, which has no semantics to be wrong about. #1450 is a
  multi-result return convention that no contract states.
- **no output / compile does not finish**: synth neither emits nor refuses
  (#1769, a table of 2^32-1 elements allocates without bound).

Each wrong-code issue's own repro was then run on the census commit. Its
status is one of the following:

- **LIVE-WRONG**: still wrong.
- **FIXED**: correct now. Most of these are fixed on main but the issue stays
  open, because closure happens at release; they are the closure candidates.
- **NOW-DECLINES**: refused loudly now, with the diagnostic the row names.
- **CANNOT-REPRO**: no runnable repro.

## The population is typed, not fetched

A test may not reach the network, so the population is a typed list in
`crates/synth-oracle/tests/wrong_code_census.rs`, checked against the
snapshot count. **A new open issue needs a row there, or a place in the
not-wrong-code lists.** Two things catch a gap:

- The `oracle-kiln` workflow fails when an open issue whose title says wrong
  code (miscompile, wrong value, wrong code, wrong result) is in neither the
  table nor the lists. It sees titles only, so an issue that reports wrong
  code under another title still needs a row at review.
- At the tag, re-run `gh issue list --repo pulseengine/synth --state open
  --limit 300` and compare it with the lists.

## How it is re-run

```sh
# the measured rows (kiln + unicorn); SDKROOT is needed on macOS for unicorn
SYNTH=$PWD/target/debug/synth cargo test -p synth-oracle --features exec \
  --test wrong_code_census -- --nocapture
# the table, the population sums and the cited oracles (no engine; part of
# the workspace Test job)
cargo test -p synth-oracle --test wrong_code_census
```

The table below is generated from `CENSUS` and checked byte-for-byte. To
record a status change, edit the row and re-bless with
`WRONG_CODE_CENSUS_BLESS=1`.

**What asserts what.** The 34 measured rows (exec, exec on arm64, and
structural) assert their status exactly, both ways: a fix turns a LIVE-WRONG
row red, a regression turns a FIXED row red, and a result the row cannot
decide (a crash, an unnamed refusal, bytes that are neither the defect nor a
fix) reds as RE-MEASURE, never as FIXED. The six cited rows, #1568, #1604,
#1661, #1672, #1676 and #1684, are NOT re-run by the Rust test. For those,
the test checks that the cited oracle is CI-wired and still pins the result
the row records: the exact `--expect` line, the named refusal, or the
oracle's executed-comparison floor. The oracle's run in CI is what decides
the status.

There are four kinds of evidence:

- **exec**: the issue's repro runs on kiln and on unicorn through
  `synth_oracle::run_case`. An ARM call whose module has imports or a memory,
  or whose export carries a relocation, runs instead on the hosted emulator
  (`synth_oracle::run_hosted`, one fresh image per call): each import call is
  linked to a stub by its bare field name, kiln and the stub are given the
  same host function, the stub clobbers R0-R3 and R12 as any AAPCS callee
  may, and a call agrees only when the values AND the host-call traces are
  equal (#1696, #1699, #1755, #1758, #1761, #1789). Memory 0 is mapped at
  0x20010000, not at synth's self-contained base 0x20000100, so code that
  ignores R11 misses it. `exec_paths_can_red` shows each path measuring
  LIVE-WRONG on a compiled body that differs from the reference's.
- **exec on arm64**: AArch64 rows (#1745, #1747, #1763) run on a small
  unicorn arm64 runner in the test against kiln, with x1-x7 and d0 poisoned.
- **structural**: the test reads the property the issue names from the
  emitted object or the library: a link-time binding (#1752), an ISA
  extension and `e_flags` (#1744), dropped export symbols (#1746), the
  required diagnostic of a refusal (#1191, #1698), and a library encoding
  (#1677).
- **cited**: a named, CI-wired `scripts/repro` oracle (see above). The issue's
  shape needs linear memory and a link step, which the Rust harness does not
  provide yet.

## Limits, stated

- **#1691**: the census runs the reduced integer shapes from the issue's own
  fixture, `scripts/repro/if_arm_dead_value_1691.wat`, on cortex-m4. The
  reporter's float attachment (`repro.zip`, cortex-m7) was not re-run. It
  must be re-run before the issue is closed on this row.
- **#1710, #1711**: reported on cortex-m4f and cortex-m7dp. The rows compile
  for `cortex-m4`. The cited CI oracles cover the m4f, m7dp, r5 and booted
  image legs.
- **#1699**: the hosted emulator serves no stub for `__meld_dispatch_import`.
  An object that calls it again is a harness error that reds the row for
  re-measurement, never FIXED.
- **#1758**: the issue stores through one export and loads through another
  on one image. The census probe does both inside one export, `st_ld2`, which
  calls an optimized-path store and a direct-path load.
- **#1761**: kiln runs one module holding module 1's `a` and module 2's
  imports and `b`; synth compiles the issue's two-module `.wast`.
- **#1745**: a debug build panics on the value-carrying-block shape. That
  panic is the issue's documented debug symptom and counts as LIVE. The
  release-build wrong value is not executed by the test.
- **#1752**: the ARM shape only. The issue's AArch64 mirror shape is not
  probed.
- **Default flags** means `--target cortex-m4` with no other codegen flag.
  `--all-exports` selects the emitted functions, and `--allow-skipped-exports`
  keeps a fixture's other declines from failing the compile. Neither changes
  codegen. This is the population behind Bet A's zero target.

## Census

<!-- census:begin (generated by crates/synth-oracle/tests/wrong_code_census.rs) -->
Measured: 2026-11-27, main cc36ff38.

Population snapshot: 2026-11-20T00:34:42Z, `gh issue list --repo pulseengine/synth --state open --limit 300`, 88 open, highest #1755; plus the 9 issues filed after it and open on 2026-11-27 (#1758, #1761, #1762, #1763, #1769, #1785, #1786, #1789, #1798).

| Count | Value |
|---|---|
| population (open on the snapshot, or filed after it and open) | 97 |
| wrong-code | 40 |
| loud decline / missing feature | 20 |
| machinery / docs / tooling | 34 |
| unclear | 2 |
| no output / compile does not finish | 1 |
| wrong-code, LIVE-WRONG | 0 |
| wrong-code, FIXED | 32 |
| wrong-code, NOW-DECLINES | 8 |
| wrong-code, CANNOT-REPRO | 0 |
| wrong-code, LIVE-WRONG on cortex-m4 with default flags | 0 |

| Issue | Backend / target | Flags | Status | M4 default | Evidence | Moved by / note |
|---|---|---|---|---|---|---|
| #1191 | arm cortex-m3 | --relocatable --all-exports (a component) | NOW-DECLINES | no | structural: object bytes, symbols or library output (this test) | components refused, f5b72988 (#1687) |
| #1205 | arm cortex-m4 | --all-exports (default image) | FIXED | yes | exec: kiln vs unicorn (this test) | routed to the direct selector, 761c6922 (#1228) |
| #1210 | arm cortex-m4 | --all-exports (default image) | FIXED | yes | exec: kiln vs unicorn (this test) | 4a3f6080 (#1249) |
| #1214 | arm cortex-m4 | --all-exports (default image) | FIXED | yes | exec: kiln vs unicorn (this test) |  |
| #1226 | arm cortex-m4 | --relocatable --all-exports, .wast input | FIXED | no | exec: kiln vs unicorn (this test) | single-module .wast homes as .wat; a multi-module merge is refused |
| #1241 | arm cortex-m4 | --all-exports (default image) | FIXED | yes | exec: kiln vs unicorn (this test) | 31980043 (#1271), 6aed6daa (#1728) |
| #1568 | arm cortex-m3 | --relocatable --native-pointer-abi | FIXED | no | cited: `scripts/repro/npa_const_addr_matrix_1568.py` pins `--expect ok=158,refused=4,guard=0,wrong=0` | 162 cells: 158 equal, 0 wrong, 4 refused; 2ef015ee (#1682) |
| #1604 | arm cortex-m3 | --relocatable --native-pointer-abi | NOW-DECLINES | no | cited: `scripts/repro/npa_model_differential.py` pins `npa-region-straddle (#1604)` | refused `npa-region-straddle (#1604)`, 2ef015ee (#1682) |
| #1661 | arm cortex-m3 | --relocatable --native-pointer-abi --safety-bounds software | NOW-DECLINES | no | cited: `scripts/repro/npa_model_differential.py` pins `npa-software-bounds (#1661)` | refused `npa-software-bounds (#1661)`, 2ef015ee (#1682) |
| #1672 | arm cortex-m3 | --relocatable --native-pointer-abi | NOW-DECLINES | no | cited: `scripts/repro/npa_model_differential.py` pins `npa-data-pointer (#1672)` | refused `npa-data-pointer (#1672)`, 2ef015ee (#1682) |
| #1676 | arm cortex-m3 | --relocatable --native-pointer-abi; self-contained | FIXED | no | cited: `scripts/repro/imported_global_slots_rq91_differential.py` pins `# ci-checks: emulations >= 42` | defined globals execute equal; reading the imported global itself is refused, 0d22bafe (#1680) |
| #1677 | synth-backend library (mpu.rs) | MPURegion::rasr() | FIXED | no | structural: object bytes, symbols or library output (this test) | 6b697bcf (#1678) |
| #1684 | arm cortex-m3 | --relocatable --native-pointer-abi | NOW-DECLINES | no | cited: `scripts/repro/npa_model_differential.py` pins `npa-i64-static-const (#1684)` | refused `npa-i64-static-const (#1684)`, 2ef015ee (#1682) |
| #1691 | arm cortex-m7 (reduced: cortex-m4) | --relocatable --all-exports | FIXED | no | exec: kiln vs unicorn (this test) | 0185ba07 (#1694); the reporter's float attachment is not re-run |
| #1696 | arm cortex-m4 | --all-exports (default flags: an ET_REL object, direct `bl log`), hosted | FIXED | yes | exec: kiln vs unicorn (this test) | 0213a5a0 (#1767): the optimized path calls an import directly; executed on the hosted emulator, which clobbers R0-R3 and R12 |
| #1698 | arm cortex-m4 | --relocatable --all-exports | NOW-DECLINES | no | structural: object bytes, symbols or library output (this test) | 6b3d5c2a (#1700) |
| #1699 | arm cortex-m4 | --all-exports (default flags: an ET_REL object, direct `bl g`), hosted | FIXED | yes | exec: kiln vs unicorn (this test) | 0213a5a0 (#1767): `__meld_dispatch_import` is gone; the import is called by its field name |
| #1710 | arm cortex-m4f/m7dp (run: cortex-m4) | --relocatable | FIXED | no | exec: kiln vs unicorn (this test); also `scripts/repro/i64_explicit_return_1710_differential.py` | 34781a8c (#1718) |
| #1711 | arm cortex-m4f/m7dp (run: cortex-m4) | --relocatable | FIXED | no | exec: kiln vs unicorn (this test); also `scripts/repro/i64_select_fused_cmp_1711_differential.py` | 547729fe (#1719) |
| #1712 | arm cortex-m4 | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | a2649209 (#1722) |
| #1713 | arm cortex-m4 | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | 6aed6daa (#1728) |
| #1714 | arm cortex-m4 + rv32imac | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | a155ca7f (#1725) |
| #1715 | arm cortex-m4 | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | a2649209 (#1722) |
| #1716 | arm cortex-m4 | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | a2649209 (#1722) |
| #1717 | rv32imac | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | c0790baa (#1727) |
| #1720 | rv32imac | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | 265235dc (#1729) |
| #1721 | arm cortex-m4 | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | a2649209 (#1722) |
| #1739 | rv32imac | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | 4d80d9d6 (#1748) |
| #1744 | rv32i | -b riscv --target rv32i --relocatable | NOW-DECLINES | no | structural: object bytes, symbols or library output (this test) | 0efe82af (#1792): rv32i refuses an M lowering, naming the profile; e_flags carry RVC iff C |
| #1745 | synth-backend-aarch64 library (compile_module) | cortex-a53, relocatable, software bounds | FIXED | no | exec: kiln vs unicorn arm64 (this test) | 0213a5a0 (#1767): compile_module carries the per-function facts |
| #1746 | arm cortex-m4, rv32imac, aarch64 | --relocatable --all-exports | FIXED | no | structural: object bytes, symbols or library output (this test) | 0213a5a0 (#1767): every export name of a function is a defined global symbol |
| #1747 | aarch64 | -b aarch64 --relocatable | FIXED | no | exec: kiln vs unicorn arm64 (this test) | 6641efec (#1749) |
| #1752 | arm cortex-m4 (also cortex-r5, aarch64) | --relocatable --all-exports | NOW-DECLINES | no | structural: object bytes, symbols or library output (this test) | 0213a5a0 (#1767): an export spelled like the in-object label `func_N` is refused, naming #1752 |
| #1754 | arm cortex-m4 | --relocatable; and default flags when the function routes to the direct selector | FIXED | yes | exec: kiln vs unicorn (this test) | 0213a5a0 (#1767); added by cold review 16 |
| #1755 | arm cortex-m4 | --all-exports (default flags: an ET_REL object, direct `bl add2`), hosted | FIXED | yes | exec: kiln vs unicorn (this test) | 0213a5a0 (#1767): import arguments are marshalled into R0-R3; same root as #1696 |
| #1758 | arm cortex-m4 | --all-exports (default flags, a module with an import and a memory), hosted | FIXED | yes | exec: kiln vs unicorn (this test) | 0213a5a0 (#1767): every function of an ET_REL object addresses memory through R11; filed after the snapshot |
| #1761 | arm cortex-m4 | --relocatable --all-exports, multi-module .wast input, hosted | FIXED | no | exec: kiln vs unicorn (this test) | c2544ec9 (#1780): a call binds within its own module; filed after the snapshot |
| #1762 | rv32imac | --relocatable | FIXED | no | exec: kiln vs unicorn (this test) | c2544ec9 (#1780): a never-written i64 local is 64 bits wide; filed after the snapshot |
| #1763 | aarch64 | -b aarch64 --relocatable | FIXED | no | exec: kiln vs unicorn arm64 (this test) | c2544ec9 (#1780): a float local lives in the FP register file; filed after the snapshot |
| #1789 | arm cortex-m4 | --relocatable, hosted | FIXED | no | exec: kiln vs unicorn (this test) | 7aea43d1 (#1791): a reload avoids the registers the op already popped; filed after the snapshot |

Not wrong-code (classified from the issue body):

- loud decline / missing feature: #380, #1145, #1229, #1230, #1231, #1254, #1267, #1301, #1426, #1441, #1447, #1448, #1673, #1703, #1724, #1726, #1740, #1785, #1786, #1798
- machinery / docs / tooling: #242, #1057, #1062, #1063, #1085, #1132, #1136, #1159, #1217, #1236, #1238, #1308, #1359, #1373, #1403, #1418, #1422, #1428, #1433, #1437, #1451, #1460, #1476, #1515, #1516, #1517, #1567, #1609, #1613, #1704, #1723, #1731, #1738, #1741
- unclear: #1207, #1450
- no output / compile does not finish: #1769
<!-- census:end -->
