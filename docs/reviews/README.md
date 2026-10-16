# The cold-review record contract

Each release's record lives at `docs/reviews/v0.NN-cold-review.md`. This file is
the contract those records are written against; `scripts/loop_conformance_check.py`
step 7 and `scripts/review_record_provenance_check.py` are what check it.

## The declared commit

The record's header must be exactly:

    **Commit reviewed:** `<sha>`

The backticks are mandatory; the bold is optional. The sha must be on main's
FIRST-PARENT line. `DECLARED_COMMIT_RE` in `scripts/loop_conformance_check.py` is
the single source for that spelling — import it rather than restating the pattern.

**The declared commit is deliberately NOT ancestor-tested.** This repository
squash-merges, so squashing DISCARDS a branch's own commits, and an ancestor test
fails on a record that declares a pre-squash branch head. A sha on main's
first-parent line is by definition an ancestor of main, so declaring one keeps the
record checkable. On v0.63 an ancestor test rejected the correct declared sha and
silently accepted one the record merely CITES.

## Commit citations are a FORWARD-ONLY obligation (RQ-87-PROVENANCE3, #1516)

A record's body cites commits as evidence. The obligation on those citations is
**forward-only**: a record written from now on cites shas a reader can follow —
the MERGED sha, since a branch head never becomes an ancestor here — and
historical citations are **NOT** going to be reconciled.

That is a decision, not an oversight, and it is written here rather than left to
be inferred, because the alternative was measured and refused:

* Ancestry failures are **systemic** in shipped records, not incidental. Measured
  across all 25 records in the authoring checkout: **243** commit citations
  tested, **105** flagged non-ancestors, all pre-squash commits: most were a pushed
  branch tip at some point, but nine were intermediate commits never pushed as a tip.
* So wiring the gating form would red on day one over history it cannot change —
  the trap this repository has already measured once and declined to build. CI
  therefore gates the provenance checker's **self-test**, never its report, and
  that choice is stated in the workflow step itself.
* And the count is **VENUE-DEPENDENT BY CONSTRUCTION**, which is why no figure
  here appears without its venue. The same 25 records in a fresh
  `git clone` of the remote — what CI checks out, and what a reader following a
  citation has — test **139** and flag **1**. The arithmetic closes: 243 − 139 =
  104 skipped, 105 − 1 = 104 fewer flags, so *every* token the fresh clone
  skipped was one the authoring checkout had flagged. The ancestry half goes
  blind precisely where a citation has become unfollowable.

**Consequence for a reader:** a non-ancestor citation in a record older than
v0.87 is expected and is not a defect in that record. For a record written after
it, cite the merged sha, or state the mapping in the record itself.

**Consequence for a tool:** report the unresolvable tokens rather than skipping
them, and name the venue beside any ancestry figure. A figure without a venue is
not a measurement.
