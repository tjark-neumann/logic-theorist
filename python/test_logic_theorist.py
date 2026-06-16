"""
tests for the Logic Theorist.
these check three things:
  1. The parser and printer round-trip.
  2. The matcher is sound (a successful match yields a literal instance).
  3. Every proof the prover emits is *valid* — we re-check each proof step
     independently (substitution = instance; detachment = modus ponens;
     chaining = syllogism), so a buggy search can never pass the tests.

run with:  python -m unittest test_logic_theorist   (or: python test_logic_theorist.py)
"""

import unittest

from logic_theorist import (
    LogicTheorist, Theorem, Proof, parse, axioms,
    substitute, match, is_implication, implies,
)


def check_proof(proof: Proof, theorems) -> bool:
    """Independently verify a proof tree is sound. Returns True if valid.

    `theorems` is the set of statements considered already-established
    (axioms plus anything proved earlier). The conclusion of each premise must
    itself check out, and the step relating premises to the conclusion must be
    a valid application of the named method.
    """
    by_name = {t.name: t.statement for t in theorems}

    # Premises must be valid proofs first.
    for p in proof.premises:
        if not check_proof(p, theorems):
            return False

    method = proof.method
    goal = proof.conclusion

    if method == "substitution":
        ref = by_name.get(proof.reference)
        return ref is not None and match(ref, goal) is not None

    if method == "detachment":
        # Need a theorem A -> B and a proved A, giving B == goal.
        assert len(proof.premises) == 1
        a = proof.premises[0].conclusion
        ref = by_name.get(proof.reference)
        if ref is None:
            return False
        # Some instance of ref must equal  a -> goal.
        target = implies(a, goal)
        return match(ref, target) is not None

    if method in ("forward-chaining", "backward-chaining"):
        # goal must be  x -> z ; premise is the other leg; the named theorem
        # supplies the remaining leg. Validity rests on the syllogism principle,
        # which is itself a PM theorem (*2.06). We confirm the legs compose.
        imp = is_implication(goal)
        if imp is None:
            return False
        x, z = imp
        leg = proof.premises[0].conclusion
        leg_imp = is_implication(leg)
        if leg_imp is None:
            return False
        ref = by_name.get(proof.reference)
        if ref is None:
            return False
        if method == "forward-chaining":
            # theorem:  x -> b ;  premise:  b -> z
            b1, b2 = leg_imp  # b -> z
            if b2 != z:
                return False
            return match(ref, implies(x, b1)) is not None
        else:
            # theorem:  b -> z ;  premise:  x -> b
            b1, b2 = leg_imp  # x -> b
            if b1 != x:
                return False
            return match(ref, implies(b2, z)) is not None

    return False


class TestParser(unittest.TestCase):
    def test_roundtrip(self):
        for text in ["p -> p", "(p | q) -> (q | p)", "~p | p", "p -> (q | r)"]:
            e = parse(text)
            self.assertEqual(parse(str(e)), e)

    def test_implication_is_sugar(self):
        self.assertEqual(parse("p -> q"), parse("~p | q"))

    def test_unicode(self):
        self.assertEqual(parse("p ⊃ q"), parse("p -> q"))
        self.assertEqual(parse("¬p ∨ p"), parse("~p | p"))


class TestMatch(unittest.TestCase):
    def test_match_yields_instance(self):
        pat = parse("p -> (p | q)")
        tgt = parse("(a | b) -> ((a | b) | c)")
        s = match(pat, tgt)
        self.assertIsNotNone(s)
        self.assertEqual(substitute(pat, s), tgt)

    def test_no_match(self):
        self.assertIsNone(match(parse("p -> p"), parse("p -> q")))


class TestProver(unittest.TestCase):
    def setUp(self):
        self.lt = LogicTheorist(max_depth=7)

    def _prove_and_check(self, goal_text):
        goal = parse(goal_text)
        # Snapshot the KB *before* proving (the proof may only use these).
        known = list(self.lt.theorems)
        proof = self.lt.prove(goal)
        self.assertIsNotNone(proof, f"failed to prove {goal_text}")
        self.assertEqual(proof.conclusion, goal)
        self.assertTrue(check_proof(proof, known),
                        f"proof of {goal_text} did not verify")
        return proof

    def test_axiom_instances(self):
        self._prove_and_check("(p | q) -> (q | p)")
        self._prove_and_check("(a | a) -> a")

    def test_classic_theorems(self):
        self._prove_and_check("(q -> r) -> ((p -> q) -> (p -> r))")  # *2.05
        self._prove_and_check("p -> p")                              # *2.08
        self._prove_and_check("p -> (q | p)")

    def test_learning_enables_later_proofs(self):
        self.lt.learn("2.08", parse("p -> p"))
        proof = self._prove_and_check("~p | p")  # *2.1, an instance of *2.08
        self.assertEqual(proof.conclusion, parse("~p | p"))

    def test_excluded_middle(self):
        self.lt.learn("2.08", parse("p -> p"))
        self.lt.learn("2.1", parse("~p | p"))
        self._prove_and_check("p | ~p")          # *2.11

    def test_unprovable_returns_none(self):
        # A non-theorem must not be "proved".
        self.assertIsNone(self.lt.prove(parse("p -> q"), max_depth=5))


if __name__ == "__main__":
    unittest.main(verbosity=2)
