#!/usr/bin/env python3
"""Unit tests for proof_inventory.py's constructor<->variant join.

WHY THIS FILE EXISTS (RQ-64-CFOBLIG, #1057). The manifest's join between the
Rocq `wasm_instr` constructors and the shipped `WasmOp` variants is exact-name
by design, so that theorem names never become a hand-maintained key. `End` is
a reserved Rocq vernacular keyword, so the model spells `WasmOp::End`'s
constructor `End_` and the join strips exactly that. An escape that strips
underscores is one step from an alias table — the failure the join exists to
prevent — so BOTH branches are driven here: the keyword escape joins, and a
non-keyword trailing underscore still REFUSES. The third test runs the real
generator over the real tree and checks the `End` row is keyed by op with the
real constructor name, so a regression in either reader is red here before
the byte-compare notices.

Stdlib `unittest` only.

    python3 scripts/test_proof_inventory.py   (wired in the claim-check CI job)
"""

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import proof_inventory  # noqa: E402
from proof_inventory import constructor_op  # noqa: E402


class ConstructorOpTest(unittest.TestCase):
    def test_identity_for_ordinary_constructors(self):
        for name in ("I32Add", "BrIf", "Block", "Loop", "Br", "LocalGet"):
            self.assertEqual(constructor_op(name), name)

    def test_keyword_escape_joins_end(self):
        self.assertEqual(constructor_op("End_"), "End")

    def test_non_keyword_underscore_is_not_an_alias(self):
        # `Foo_` must NOT become `Foo`: the escape is a language fact, not an
        # alias mechanism. Returned unchanged, it fails the exact-name join
        # and the generator refuses.
        self.assertEqual(constructor_op("Block_"), "Block_")
        self.assertEqual(constructor_op("Nop_"), "Nop_")

    def test_double_underscore_is_not_stripped_twice(self):
        self.assertEqual(constructor_op("End__"), "End__")

    def test_reserved_set_is_exactly_end(self):
        # Widening the set is a deliberate, reviewed change — pin it.
        self.assertEqual(proof_inventory.ROCQ_RESERVED_WORDS, frozenset({"End"}))


class RealTreeJoinTest(unittest.TestCase):
    def test_end_row_is_keyed_by_op_with_real_constructor(self):
        data = proof_inventory.build()
        rows = {e["op"]: e for e in data["entries"]}
        self.assertIn("End", rows)
        self.assertNotIn("End_", rows)  # the universe is WasmOp, not Rocq
        end = rows["End"]
        self.assertTrue(end["modeled"])
        self.assertEqual(end["constructor"], "End_")
        # Modeled but unproven: no ARM-side theorem binds it (RQ-64-CFOBLIG
        # branch B). If this flips to "qed", the obstruction record in
        # coq/Synth/Synth/BlockEndObligation.v must be revisited in the same
        # PR — that is the point of pinning it.
        self.assertEqual(end["status"], "absent")
        self.assertFalse(end["result_correspondence"])
        for op in ("Block", "Loop", "Br"):
            self.assertTrue(rows[op]["modeled"], op)
            self.assertEqual(rows[op]["constructor"], op)
            self.assertEqual(rows[op]["status"], "absent", op)

    def test_brif_row_unchanged_by_the_structured_executor(self):
        data = proof_inventory.build()
        rows = {e["op"]: e for e in data["entries"]}
        brif = rows["BrIf"]
        self.assertEqual(brif["status"], "qed")
        self.assertTrue(brif["result_correspondence"])
        self.assertIn(
            ("coq/Synth/Synth/CorrectnessBrIf.v", "brif_correct"),
            {(t["file"], t["name"]) for t in brif["theorems"]},
        )


if __name__ == "__main__":
    unittest.main()
