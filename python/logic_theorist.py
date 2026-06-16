"""
logic theorist 
a re-creation of the 1956 program by
Allen Newell, Cliff Shaw, and Herbert Simon
the first artificial-intelligence program

the original proved theorems of propositional logic taken from Chapter 2 of
Whitehead & Russell's PM. it worked from five axioms
and three rules of inference, searching for proofs with a handful of heuristic
methods. this implementation reproduces that machinery:

primitive connectives (as in PM):  negation (~)  and  disjunction (|)
implication is defined:            a -> b   ==   ~a | b      (the "Replacement" rule)

rules of inference:
    substitution  — uniformly replace a variable by any formula
    replacement   — swap a connective for its definition (handled by normalising
                    everything to the ~/| primitives)
    detachment    — from  A  and  A -> B  infer  B   (modus ponens)

search methods (exactly the four the original used):
    substitution method  — is the goal an instance of a known theorem?
    detachment method    — find a theorem  A -> goal,  then prove  A
    forward chaining     — to prove a -> c, find a -> b, then prove b -> c
    backward chaining     — to prove a -> c, find b -> c, then prove a -> b
        (chaining is justified by the syllogism principle, PM *2.06)

newly proved theorems are added to the knowledge base and reused, just as the
original LT accumulated results while working through PM Chapter 2.

this module has no dependencies beyond the standard library.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Iterable


# the internal representation uses only the PM primitives: variables, negation,
# and disjunction. implication is sugar that the parser expands and the printer
# re-sugars, which is how the "Replacement" rule is realised. every formula
# already lives in primitive form, so a -> b and ~a | b are literally the same
# object and need no run-time conversion.



class Expr:
    """Base class for propositional formulas (immutable, hashable)."""

    __slots__ = ()

    def __or__(self, other: "Expr") -> "Or":
        return Or(self, other)


@dataclass(frozen=True)
class Var(Expr):
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Not(Expr):
    operand: Expr

    def __str__(self) -> str:
        return f"~{_paren(self.operand, self)}"


@dataclass(frozen=True)
class Or(Expr):
    left: Expr
    right: Expr

    def __str__(self) -> str:
        # Re-sugar  ~a | b  back into  a -> b  for readability.
        if isinstance(self.left, Not):
            return f"({self.left.operand} -> {self.right})"
        return f"({self.left} | {self.right})"


def implies(a: Expr, b: Expr) -> Expr:
    """Construct  a -> b  as the primitive  ~a | b  (PM's definition of ->)."""
    return Or(Not(a), b)


def _paren(inner: Expr, outer: Expr) -> str:
    if isinstance(inner, (Or,)):
        return str(inner)  # Or already prints its own parens
    return str(inner)


# convenience variables
P, Q, R, S = Var("p"), Var("q"), Var("r"), Var("s")


# substitution and one-way pattern matching

Subst = Dict[str, Expr]


def substitute(expr: Expr, subst: Subst) -> Expr:
    """Apply a substitution (variable name -> formula) throughout an expression."""
    if isinstance(expr, Var):
        return subst.get(expr.name, expr)
    if isinstance(expr, Not):
        return Not(substitute(expr.operand, subst))
    if isinstance(expr, Or):
        return Or(substitute(expr.left, subst), substitute(expr.right, subst))
    raise TypeError(f"unknown expression: {expr!r}")


def match(pattern: Expr, target: Expr, subst: Optional[Subst] = None) -> Optional[Subst]:
    """One-way match: find a substitution s such that substitute(pattern, s) == target.

    Variables in `pattern` may be bound; `target` is treated as a constant
    structure. Returns the binding dict on success, or None on failure.
    """
    if subst is None:
        subst = {}
    if isinstance(pattern, Var):
        bound = subst.get(pattern.name)
        if bound is None:
            subst = dict(subst)
            subst[pattern.name] = target
            return subst
        return subst if bound == target else None
    if isinstance(pattern, Not):
        if isinstance(target, Not):
            return match(pattern.operand, target.operand, subst)
        return None
    if isinstance(pattern, Or):
        if isinstance(target, Or):
            s = match(pattern.left, target.left, subst)
            if s is None:
                return None
            return match(pattern.right, target.right, s)
        return None
    raise TypeError(f"unknown expression: {pattern!r}")


def variables(expr: Expr) -> set[str]:
    if isinstance(expr, Var):
        return {expr.name}
    if isinstance(expr, Not):
        return variables(expr.operand)
    if isinstance(expr, Or):
        return variables(expr.left) | variables(expr.right)
    return set()


def rename_apart(expr: Expr, suffix: str) -> Expr:
    """Rename every variable to avoid clashes when reusing a theorem."""
    sub: Subst = {v: Var(v + suffix) for v in variables(expr)}
    return substitute(expr, sub)


def is_implication(expr: Expr) -> Optional[Tuple[Expr, Expr]]:
    """If expr has the form  a -> b  (i.e. ~a | b), return (a, b); else None."""
    if isinstance(expr, Or) and isinstance(expr.left, Not):
        return (expr.left.operand, expr.right)
    return None


# proofs


@dataclass
class Proof:
    """A node in a proof tree: a conclusion, the method used, and sub-proofs."""

    conclusion: Expr
    method: str
    reference: str = ""           # axiom/theorem name used, if any
    premises: List["Proof"] = field(default_factory=list)

    def render(self) -> str:
        lines: List[str] = []
        self._render(lines, depth=0)
        return "\n".join(lines)

    def _render(self, lines: List[str], depth: int) -> None:
        indent = "  " * depth
        tag = f"[{self.method}"
        if self.reference:
            tag += f" via {self.reference}"
        tag += "]"
        lines.append(f"{indent}{self.conclusion}    {tag}")
        for p in self.premises:
            p._render(lines, depth + 1)

    def step_count(self) -> int:
        return 1 + sum(p.step_count() for p in self.premises)


# knowledge base


@dataclass
class Theorem:
    name: str
    statement: Expr


# the five axioms of PM propositional calculus that LT was given, written in
# primitive ~/| form (implication shown in comments).
def axioms() -> List[Theorem]:
    return [
        # *1.2   (p | p) -> p
        Theorem("1.2", implies(Or(P, P), P)),
        # *1.3   p -> (p | q)
        Theorem("1.3", implies(P, Or(P, Q))),
        # *1.4   (p | q) -> (q | p)
        Theorem("1.4", implies(Or(P, Q), Or(Q, P))),
        # *1.5   (p | (q | r)) -> (q | (p | r))
        Theorem("1.5", implies(Or(P, Or(Q, R)), Or(Q, Or(P, R)))),
        # *1.6   (p -> q) -> ((r | p) -> (r | q))
        Theorem("1.6", implies(implies(P, Q), implies(Or(R, P), Or(R, Q)))),
    ]


# the Logic Theorist


class LogicTheorist:
    """Backward-search theorem prover using the original LT methods."""

    def __init__(self, theorems: Optional[Iterable[Theorem]] = None,
                 max_depth: int = 6) -> None:
        self.theorems: List[Theorem] = list(theorems) if theorems else axioms()
        self.max_depth = max_depth
        self._gensym = 0

    # -- public API

    def prove(self, goal: Expr, max_depth: Optional[int] = None) -> Optional[Proof]:
        """Attempt to prove `goal`. Returns a Proof tree or None.

        Uses iterative deepening so the first proof found is among the shortest.
        """
        limit = max_depth if max_depth is not None else self.max_depth
        for depth in range(1, limit + 1):
            self._gensym = 0
            proof = self._search(goal, depth, frozenset())
            if proof is not None:
                return proof
        return None

    def learn(self, name: str, goal: Expr,
              max_depth: Optional[int] = None) -> Optional[Proof]:
        """Prove a theorem and, on success, add it to the knowledge base so it
        can be reused — mirroring how the original LT accumulated results."""
        proof = self.prove(goal, max_depth)
        if proof is not None:
            self.theorems.append(Theorem(name, goal))
        return proof

    # -- search

    def _fresh(self) -> str:
        self._gensym += 1
        return f"#{self._gensym}"

    def _search(self, goal: Expr, depth: int, seen: frozenset) -> Optional[Proof]:
        if goal in seen:
            return None
        seen = seen | {goal}

        # 1) substitution method (base case): is the goal an instance of a
        #    known axiom or theorem?
        proof = self._substitution_method(goal)
        if proof is not None:
            return proof

        if depth <= 0:
            return None

        # 2) detachment method.
        proof = self._detachment_method(goal, depth, seen)
        if proof is not None:
            return proof

        # 3) chaining (only meaningful when the goal is itself an implication).
        imp = is_implication(goal)
        if imp is not None:
            a, c = imp
            proof = self._forward_chaining(a, c, depth, seen)
            if proof is not None:
                return proof
            proof = self._backward_chaining(a, c, depth, seen)
            if proof is not None:
                return proof

        return None

    def _substitution_method(self, goal: Expr) -> Optional[Proof]:
        for thm in self.theorems:
            if match(thm.statement, goal) is not None:
                return Proof(goal, method="substitution", reference=thm.name)
        return None

    def _detachment_method(self, goal: Expr, depth: int,
                           seen: frozenset) -> Optional[Proof]:
        # look for a theorem  A -> B  whose consequent B matches the goal;
        # then it suffices to prove the (substituted) antecedent A.
        for thm in self.theorems:
            stmt = rename_apart(thm.statement, self._fresh())
            imp = is_implication(stmt)
            if imp is None:
                continue
            ante, cons = imp
            s = match(cons, goal)
            if s is None:
                continue
            subgoal = substitute(ante, s)
            if subgoal == goal:
                continue  # no progress
            sub = self._search(subgoal, depth - 1, seen)
            if sub is not None:
                return Proof(goal, method="detachment", reference=thm.name,
                             premises=[sub])
        return None

    def _forward_chaining(self, a: Expr, c: Expr, depth: int,
                          seen: frozenset) -> Optional[Proof]:
        # goal  a -> c.  Find theorem  a -> b,  then prove  b -> c.
        for thm in self.theorems:
            stmt = rename_apart(thm.statement, self._fresh())
            imp = is_implication(stmt)
            if imp is None:
                continue
            ante, cons = imp
            s = match(ante, a)
            if s is None:
                continue
            b = substitute(cons, s)
            subgoal = implies(b, c)
            if subgoal == implies(a, c):
                continue
            sub = self._search(subgoal, depth - 1, seen)
            if sub is not None:
                return Proof(implies(a, c), method="forward-chaining",
                             reference=thm.name, premises=[sub])
        return None

    def _backward_chaining(self, a: Expr, c: Expr, depth: int,
                           seen: frozenset) -> Optional[Proof]:
        # goal  a -> c.  Find theorem  b -> c,  then prove  a -> b.
        for thm in self.theorems:
            stmt = rename_apart(thm.statement, self._fresh())
            imp = is_implication(stmt)
            if imp is None:
                continue
            ante, cons = imp
            s = match(cons, c)
            if s is None:
                continue
            b = substitute(ante, s)
            subgoal = implies(a, b)
            if subgoal == implies(a, c):
                continue
            sub = self._search(subgoal, depth - 1, seen)
            if sub is not None:
                return Proof(implies(a, c), method="backward-chaining",
                             reference=thm.name, premises=[sub])
        return None


# A tiny parser, so theorems can be written as strings.
#
# Grammar (precedence: ~ tightest, then |, then ->, right-associative):
#     expr   := imp
#     imp    := orx ('->' imp)?
#     orx    := unary ('|' unary)*
#     unary  := '~' unary | atom
#     atom   := IDENT | '(' expr ')'
# Accepts ascii (~ | ->) and unicode (¬ ∨ ⊃ →) interchangeably.


def parse(text: str) -> Expr:
    return _Parser(text).parse()


class _Parser:
    def __init__(self, text: str) -> None:
        self.s = (text.replace("¬", "~").replace("∨", "|")
                      .replace("⊃", "->").replace("→", "->"))
        self.i = 0

    def parse(self) -> Expr:
        e = self._imp()
        self._skip()
        if self.i != len(self.s):
            raise SyntaxError(f"unexpected text at position {self.i}: {self.s[self.i:]!r}")
        return e

    def _skip(self) -> None:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def _peek(self) -> str:
        self._skip()
        return self.s[self.i] if self.i < len(self.s) else ""

    def _eat(self, token: str) -> bool:
        self._skip()
        if self.s.startswith(token, self.i):
            self.i += len(token)
            return True
        return False

    def _imp(self) -> Expr:
        left = self._orx()
        if self._eat("->"):
            right = self._imp()  # right-associative
            return implies(left, right)
        return left

    def _orx(self) -> Expr:
        left = self._unary()
        while self._eat("|"):
            right = self._unary()
            left = Or(left, right)
        return left

    def _unary(self) -> Expr:
        if self._eat("~"):
            return Not(self._unary())
        return self._atom()

    def _atom(self) -> Expr:
        if self._eat("("):
            e = self._imp()
            if not self._eat(")"):
                raise SyntaxError("missing closing parenthesis")
            return e
        self._skip()
        start = self.i
        while self.i < len(self.s) and (self.s[self.i].isalnum() or self.s[self.i] == "_"):
            self.i += 1
        if start == self.i:
            raise SyntaxError(f"expected a variable at position {self.i}")
        return Var(self.s[start:self.i])
