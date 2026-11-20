# Wrong-code census

RQ-91-WRONGCODECENSUS (Refs #1741), the week-one census of the v0.92 plan's
Bet A ("wrong code, with a number").

## What is counted

Every issue open in the population snapshot (the timestamp, command and
highest issue number are in the generated block below) was read in full, not
by its title, and put in exactly one class:

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

**What asserts what.** The 29 measured rows (exec, exec on arm64, and
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
  `synth_oracle::run_case`. An import is served to kiln and stubbed at the
  undefined symbol the compiled call relocates against. The stub clobbers
  r1-r3 and r12, as any AAPCS callee may (#1696, #1699, #1755).
- **exec on arm64**: AArch64 rows (#1745, #1747) run on a small unicorn
  arm64 runner in the test against kiln, with x1-x7 and d0 poisoned.
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
- **#1699**: the stub reads the wasm arguments from r1 and r2 after the index
  in r0. A fix that picks a different dispatcher contract (KB-001's pointer
  block) reds the row for re-measurement. It does not read as FIXED.
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
Measured: 2026-11-20, main 3dc31524 (+ the unmerged oracle-kiln and x86objplan stack).

Population snapshot: 2026-11-20T00:34:42Z, `gh issue list --repo pulseengine/synth --state open --limit 300`, 88 open, highest #1755.

| Count | Value |
|---|---|
| open issues | 88 |
| wrong-code | 35 |
| loud decline / missing feature | 17 |
| machinery / docs / tooling | 34 |
| unclear | 2 |
| wrong-code, LIVE-WRONG | 9 |
| wrong-code, FIXED | 20 |
| wrong-code, NOW-DECLINES | 6 |
| wrong-code, CANNOT-REPRO | 0 |
| wrong-code, LIVE-WRONG on cortex-m4 with default flags | 4 |

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
| #1696 | arm cortex-m4 | --all-exports (default, optimized path), import stub | LIVE-WRONG | yes | exec: kiln vs unicorn (this test) | executed with an import stub that clobbers r0-r3 as AAPCS allows |
| #1698 | arm cortex-m4 | --relocatable --all-exports | NOW-DECLINES | no | structural: object bytes, symbols or library output (this test) | 6b3d5c2a (#1700) |
| #1699 | arm cortex-m4 | --all-exports (default, direct selector), dispatcher stub | LIVE-WRONG | yes | exec: kiln vs unicorn (this test) | executed with a `__meld_dispatch_import` stub reading the args from r1, r2 |
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
| #1744 | rv32i | -b riscv --target rv32i --relocatable | LIVE-WRONG | no | structural: object bytes, symbols or library output (this test) |  |
| #1745 | synth-backend-aarch64 library (compile_module) | cortex-a53, relocatable, software bounds | LIVE-WRONG | no | exec: kiln vs unicorn arm64 (this test) |  |
| #1746 | arm cortex-m4, rv32imac, aarch64 | --relocatable --all-exports | LIVE-WRONG | no | structural: object bytes, symbols or library output (this test) | an export aliasing another export's function is dropped from the symtab, exit 0 |
| #1747 | aarch64 | -b aarch64 --relocatable | LIVE-WRONG | no | exec: kiln vs unicorn arm64 (this test) | fix on the unmerged v092-a64below branch |
| #1752 | arm cortex-m4 (also cortex-r5, aarch64) | --relocatable --all-exports | LIVE-WRONG | no | structural: object bytes, symbols or library output (this test) |  |
| #1754 | arm cortex-m4 | --relocatable; and default flags when the function routes to the direct selector | LIVE-WRONG | yes | exec: kiln vs unicorn (this test) | filed after the first census commit; added by cold review 16 |
| #1755 | arm cortex-m4 | --all-exports (default, optimized path), import stub | LIVE-WRONG | yes | exec: kiln vs unicorn (this test) | found by this census; same root as #1696 |

Not wrong-code (classified from the issue body):

- loud decline / missing feature: #380, #1145, #1229, #1230, #1231, #1254, #1267, #1301, #1426, #1441, #1447, #1448, #1673, #1703, #1724, #1726, #1740
- machinery / docs / tooling: #242, #1057, #1062, #1063, #1085, #1132, #1136, #1159, #1217, #1236, #1238, #1308, #1359, #1373, #1403, #1418, #1422, #1428, #1433, #1437, #1451, #1460, #1476, #1515, #1516, #1517, #1567, #1609, #1613, #1704, #1723, #1731, #1738, #1741
- unclear: #1207, #1450
<!-- census:end -->
