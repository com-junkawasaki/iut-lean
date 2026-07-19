import Mathlib.Tactic.IntervalCases

/-!
# Hyperbolicity type of a curve

Grothendieck's anabelian program (and, downstream, Mochizuki's inter-universal Teichmüller
theory) is only concerned with *hyperbolic* curves: a smooth curve of genus `g` with `n` marked
points / punctures is admissible exactly when `2 * g - 2 + n > 0`. This is the very first
definition of the whole subject — every later object (the curve itself, its étale fundamental
group, its Galois category of finite étale covers) is indexed by such a pair `(g, n)`.

This file formalizes the numerical type `(g, n)` and the hyperbolicity predicate, and proves the
standard classification of the (finitely many) non-hyperbolic types. Nothing here touches
fundamental groups, Galois categories, or schemes yet — see the module docstring of
`IutLean.MasonStothers` and the repository README for how this fits into the project's honestly
long-horizon roadmap.
-/

namespace Anabelian

/-- The numerical type `(g, n)` of a curve: genus `g` with `n` marked points (punctures). -/
structure CurveType where
  /-- The genus of the curve. -/
  genus : ℕ
  /-- The number of marked points (punctures) removed from the curve. -/
  punctures : ℕ
  deriving DecidableEq, Repr

namespace CurveType

/-- **Hyperbolicity condition.** Written as `2 * genus + punctures > 2` rather than the more
familiar `2 * genus - 2 + punctures > 0` to avoid truncated subtraction in `ℕ`; the two are
equivalent for natural numbers. -/
def IsHyperbolic (t : CurveType) : Prop := 2 * t.genus + t.punctures > 2

instance : DecidablePred IsHyperbolic :=
  fun t => inferInstanceAs (Decidable (2 * t.genus + t.punctures > 2))

/-- The four excluded (non-hyperbolic) numerical types: the sphere with at most two punctures,
and the once-punctureless elliptic curve. These are, up to the trivial symmetry of the
definition, exactly the classical list of non-hyperbolic curves in Grothendieck's program. -/
theorem not_isHyperbolic_iff (t : CurveType) :
    ¬ IsHyperbolic t ↔
      t = ⟨0, 0⟩ ∨ t = ⟨0, 1⟩ ∨ t = ⟨0, 2⟩ ∨ t = ⟨1, 0⟩ := by
  obtain ⟨g, n⟩ := t
  simp only [IsHyperbolic, CurveType.mk.injEq]
  omega

/-- Any curve of genus at least `2` is hyperbolic, regardless of the number of punctures. -/
theorem isHyperbolic_of_two_le_genus {t : CurveType} (h : 2 ≤ t.genus) : IsHyperbolic t := by
  simp only [IsHyperbolic]; omega

/-- A genus-`0` curve is hyperbolic iff it has at least `3` punctures. -/
theorem isHyperbolic_genus_zero_iff {n : ℕ} :
    IsHyperbolic ⟨0, n⟩ ↔ 3 ≤ n := by
  simp only [IsHyperbolic]; omega

/-- A genus-`1` curve is hyperbolic iff it has at least one puncture. -/
theorem isHyperbolic_genus_one_iff {n : ℕ} :
    IsHyperbolic ⟨1, n⟩ ↔ 1 ≤ n := by
  simp only [IsHyperbolic]; omega

/-- Adding a puncture to a hyperbolic curve keeps it hyperbolic. -/
theorem IsHyperbolic.add_puncture {t : CurveType} (h : IsHyperbolic t) :
    IsHyperbolic ⟨t.genus, t.punctures + 1⟩ := by
  simp only [IsHyperbolic] at h ⊢; omega

/-- Increasing the genus of a hyperbolic curve keeps it hyperbolic. -/
theorem IsHyperbolic.add_genus {t : CurveType} (h : IsHyperbolic t) :
    IsHyperbolic ⟨t.genus + 1, t.punctures⟩ := by
  simp only [IsHyperbolic] at h ⊢; omega

end CurveType

end Anabelian
