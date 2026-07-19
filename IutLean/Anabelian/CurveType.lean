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

/-- **Euler characteristic** of the numerical type `(g, n)`: `χ = 2 - 2g - n`. This is the Euler
characteristic of the underlying compact Riemann surface (genus `g`) with `n` points removed,
and is the standard bookkeeping quantity used throughout the anabelian geometry literature
(including Mochizuki's papers, which routinely refer to a curve "of type `(g, r)`" via this
Euler characteristic). -/
def eulerChar (t : CurveType) : ℤ := 2 - 2 * (t.genus : ℤ) - (t.punctures : ℤ)

/-- **Standard reformulation of hyperbolicity via the Euler characteristic**: a curve type is
hyperbolic iff its Euler characteristic is negative. This is the form in which hyperbolicity is
usually stated in the literature (`2g - 2 + n > 0 ↔ χ < 0`); `IsHyperbolic` above is the
`ℕ`-subtraction-free definition used for computation, and this lemma certifies the two agree. -/
theorem isHyperbolic_iff_eulerChar_neg (t : CurveType) :
    IsHyperbolic t ↔ eulerChar t < 0 := by
  simp only [IsHyperbolic, eulerChar]
  omega

/-- The Euler characteristic is additive in punctures: removing one more point drops `χ` by
exactly `1`. -/
theorem eulerChar_add_puncture (t : CurveType) :
    eulerChar ⟨t.genus, t.punctures + 1⟩ = eulerChar t - 1 := by
  simp only [eulerChar]; push_cast; omega

/-- The Euler characteristic drops by `2` for each unit of genus. -/
theorem eulerChar_add_genus (t : CurveType) :
    eulerChar ⟨t.genus + 1, t.punctures⟩ = eulerChar t - 2 := by
  simp only [eulerChar]; push_cast; omega

/-- **Numerical degree formula for unramified covers.** If `X` is (the numerical type of) a
degree-`d` *unramified* cover of `Y` — i.e. `χ(X) = d · χ(Y)`, the unramified case of the
Riemann–Hurwitz formula (no ramification correction term) — then `X` is hyperbolic iff `Y` is.
This is the basic fact that lets anabelian geometry restrict attention to hyperbolic curves
consistently when passing to finite (unramified) covers: since `d > 0`, `χ(X)` and `χ(Y)` have
the same sign, so `IsHyperbolic X ↔ eulerChar X < 0 ↔ eulerChar Y < 0 ↔ IsHyperbolic Y`.

This is purely the numerical/combinatorial shadow of the degree formula on Euler
characteristics — it does not (yet) model actual covering maps of curves or their ramification
data; see the module docstring for how this fits the project's roadmap. -/
def IsUnramifiedCoverType (d : ℕ) (X Y : CurveType) : Prop :=
  0 < d ∧ eulerChar X = (d : ℤ) * eulerChar Y

theorem IsUnramifiedCoverType.isHyperbolic_iff {d : ℕ} {X Y : CurveType}
    (h : IsUnramifiedCoverType d X Y) : IsHyperbolic X ↔ IsHyperbolic Y := by
  obtain ⟨hd, heq⟩ := h
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  rw [isHyperbolic_iff_eulerChar_neg, isHyperbolic_iff_eulerChar_neg, heq]
  constructor
  · intro h
    by_contra hy
    push Not at hy
    have : (0 : ℤ) ≤ (d : ℤ) * eulerChar Y := mul_nonneg hd'.le hy
    omega
  · exact mul_neg_of_pos_of_neg hd'

end CurveType

end Anabelian
