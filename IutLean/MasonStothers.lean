import Mathlib.NumberTheory.FLT.MasonStothers

/-!
# A characteristic-zero corollary of the polynomial ABC theorem

`Mathlib.NumberTheory.FLT.MasonStothers` already contains a complete, `sorry`-free proof of the
**Mason–Stothers theorem** (`Polynomial.abc`): the polynomial function-field analogue of the ABC
conjecture. It is a genuine *theorem*, not a conjecture — unlike the classical ABC conjecture over
the integers, which remains open (and is the subject Mochizuki's disputed inter-universal
Teichmüller theory attempts to settle; see the project README).

`Polynomial.abc` concludes a disjunction: either the expected degree bound holds, or the
derivatives of `a`, `b`, `c` are all zero (which can only happen via inseparability, e.g. in
positive characteristic where `a`, `b`, `c` can be nontrivial `p`-th powers of the variable). This
file removes that escape clause under the natural hypothesis that the ambient field is
torsion-free (in particular, any field of characteristic zero) and that at least one of the three
polynomials is non-constant: in that setting a zero derivative would force every one of `a`, `b`,
`c` to be constant, contradicting the hypothesis, so the degree bound holds unconditionally.
-/

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k] [DecidableEq k] [IsAddTorsionFree k]

/-- **Polynomial ABC theorem, torsion-free coefficient field, non-constant case.**

If `a, b, c` are pairwise coprime nonzero polynomials over a torsion-free field (e.g. any
characteristic-zero field) with `a + b + c = 0`, and at least one of them is non-constant, then
the Mason–Stothers degree bound holds unconditionally: the "all derivatives vanish" alternative
from `Polynomial.abc` is impossible, since a zero derivative forces `natDegree = 0`
(`Polynomial.derivative_eq_zero`) for every one of `a`, `b`, `c`. -/
theorem Polynomial.abc_of_ne_const {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b + c = 0)
    (hnc : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) :
    natDegree a + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree b + 1 ≤ (radical (a * b * c)).natDegree ∧
      natDegree c + 1 ≤ (radical (a * b * c)).natDegree := by
  rcases Polynomial.abc ha hb hc hab hsum with h | ⟨da, db, dc⟩
  · exact h
  · exfalso
    rw [derivative_eq_zero] at da db dc
    rcases hnc with h | h | h
    · exact h da
    · exact h db
    · exact h dc
