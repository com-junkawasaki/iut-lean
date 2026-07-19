import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image

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

/-- **Computable witness for `not_isHyperbolic_iff`.** The same four excluded types, packaged
as an explicit `Finset` (rather than a disjunction of propositional equalities) so that
membership, cardinality, and other properties of the non-hyperbolic exception set can be
checked by `decide` / `native_decide` instead of only reasoned about propositionally. -/
def nonHyperbolicTypes : Finset CurveType := {⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩}

/-- The `nonHyperbolicTypes` Finset really does compute the non-hyperbolic types: its
coercion to a `Set` is exactly `{t | ¬ IsHyperbolic t}`. -/
theorem coe_nonHyperbolicTypes :
    (↑nonHyperbolicTypes : Set CurveType) = {t | ¬ IsHyperbolic t} := by
  ext t
  simp only [nonHyperbolicTypes, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq, not_isHyperbolic_iff]

/-- There are exactly four non-hyperbolic curve types, verified by direct computation. -/
theorem card_nonHyperbolicTypes : nonHyperbolicTypes.card = 4 := by decide

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

/-- **Every negative integer is realized as the Euler characteristic of a hyperbolic curve
type.** In fact a genus-`0` curve always suffices: `eulerChar ⟨0, n⟩ = 2 - n`, so choosing
`n = 2 - v` realizes any target `v < 0`. This shows the numerical invariant `eulerChar`
surjects onto the negative integers already restricted to hyperbolic types — the classification
`not_isHyperbolic_iff` above shows the non-hyperbolic types are a sparse, finite exception, while
this shows the hyperbolic side is numerically as rich as it could possibly be. -/
theorem exists_hyperbolic_eulerChar {v : ℤ} (hv : v < 0) :
    ∃ t : CurveType, IsHyperbolic t ∧ eulerChar t = v := by
  have hn : ((2 - v).toNat : ℤ) = 2 - v := Int.toNat_of_nonneg (by omega)
  refine ⟨⟨0, (2 - v).toNat⟩, ?_, ?_⟩
  · rw [isHyperbolic_genus_zero_iff]
    omega
  · simp only [eulerChar]
    omega

/-- **Dimension of the moduli space** `M_{g,n}` of the numerical type `(g, n)`:
`dim M_{g,n} = 3g - 3 + n`. This is the other standard invariant of a curve type (alongside
`eulerChar`) used throughout Teichmüller theory, Grothendieck–Teichmüller theory, and Mochizuki's
IUT papers. -/
def moduliDim (t : CurveType) : ℤ := 3 * (t.genus : ℤ) - 3 + t.punctures

/-- **Every hyperbolic curve type has non-negative moduli dimension.** This is the basic fact
underlying why hyperbolic curves form a sensible geometric moduli problem: their parameter space
is never "negative-dimensional". -/
theorem moduliDim_nonneg_of_isHyperbolic {t : CurveType} (h : IsHyperbolic t) :
    0 ≤ moduliDim t := by
  simp only [IsHyperbolic] at h
  simp only [moduliDim]
  omega

/-- **The unique rigid hyperbolic curve type** (zero moduli dimension) is `(g, n) = (0, 3)`,
the thrice-punctured sphere — the classical base case of Grothendieck–Teichmüller theory, whose
moduli space `M_{0,3}` is a single point. -/
theorem moduliDim_eq_zero_iff_of_isHyperbolic {t : CurveType} (h : IsHyperbolic t) :
    moduliDim t = 0 ↔ t = ⟨0, 3⟩ := by
  obtain ⟨g, n⟩ := t
  simp only [IsHyperbolic, moduliDim, CurveType.mk.injEq] at h ⊢
  omega

/-- **The two moduli-dimension-`1` hyperbolic types** are exactly `(g, n) = (0, 4)` (the
four-punctured sphere) and `(1, 1)` (the once-punctured elliptic curve, i.e. the classical
modular curve type). Alongside `(0, 3)`, these are precisely the fundamental building blocks
whose Teichmüller/moduli theory underlies the Grothendieck–Teichmüller group's defining
compatibility conditions. -/
theorem moduliDim_eq_one_iff_of_isHyperbolic {t : CurveType} (h : IsHyperbolic t) :
    moduliDim t = 1 ↔ t = ⟨0, 4⟩ ∨ t = ⟨1, 1⟩ := by
  obtain ⟨g, n⟩ := t
  simp only [IsHyperbolic, moduliDim, CurveType.mk.injEq] at h ⊢
  omega

/-- **Bounded moduli dimension bounds both genus and puncture count.** This holds for every
curve type, not just hyperbolic ones: it is the numerical input to the classical finiteness
fact that only finitely many types have moduli dimension below a given bound (the actual
`Set.Finite` statement is left for a future step). -/
theorem genus_le_of_moduliDim_le {t : CurveType} {N : ℤ} (hN : moduliDim t ≤ N) :
    (t.genus : ℤ) ≤ N + 3 := by
  simp only [moduliDim] at hN; omega

/-- See `genus_le_of_moduliDim_le`: the puncture-count analogue. -/
theorem punctures_le_of_moduliDim_le {t : CurveType} {N : ℤ} (hN : moduliDim t ≤ N) :
    (t.punctures : ℤ) ≤ N + 3 := by
  simp only [moduliDim] at hN; omega

/-- **Finiteness of hyperbolic types with bounded moduli dimension.** Only finitely many
hyperbolic curve types have moduli dimension at most `N`, for any bound `N` — the classical
finiteness fact anticipated by `genus_le_of_moduliDim_le` / `punctures_le_of_moduliDim_le`,
made precise as an explicit `Set.Finite` witnessed by an actual bounding `Finset`. -/
theorem finite_hyperbolic_of_moduliDim_le (N : ℤ) :
    {t : CurveType | IsHyperbolic t ∧ moduliDim t ≤ N}.Finite := by
  set n := (N + 3).toNat with hn
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image
      (fun p : ℕ × ℕ => (⟨p.1, p.2⟩ : CurveType))))
  rintro t ⟨-, hmod⟩
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨(t.genus, t.punctures), ?_, rfl⟩
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have hg := genus_le_of_moduliDim_le hmod
  have hp := punctures_le_of_moduliDim_le hmod
  omega

/-! ## Nodal degeneration and the boundary of `M̄_{g,n}`

The Deligne–Mumford compactification `M̄_{g,n}` of the moduli space of curves adjoins *stable
nodal curves* at its boundary. Every boundary divisor arises from one of two combinatorial
degenerations of the numerical type `(g, n)`: a curve splitting into two components joined at a
node (a *separating* node), or a single component acquiring a *non-separating* self-node. Both
operations are numerically well known to preserve the Euler characteristic exactly; the two
theorems below record this. -/

/-- **Separating nodal degeneration.** `t` degenerates into two components `t₁`, `t₂` glued along
a single separating node: genus is additive (`g = g₁ + g₂`), and each side of the node
contributes one new marked point, so `n₁ + n₂ = n + 2`. -/
def IsSeparatingSplit (t t₁ t₂ : CurveType) : Prop :=
  t.genus = t₁.genus + t₂.genus ∧ t₁.punctures + t₂.punctures = t.punctures + 2

/-- The Euler characteristic is additive under a separating nodal degeneration:
`χ(t) = χ(t₁) + χ(t₂)`. -/
theorem IsSeparatingSplit.eulerChar_eq {t t₁ t₂ : CurveType} (h : IsSeparatingSplit t t₁ t₂) :
    eulerChar t = eulerChar t₁ + eulerChar t₂ := by
  obtain ⟨hg, hn⟩ := h
  simp only [eulerChar] at *
  omega

/-- **Non-separating nodal degeneration.** `t` degenerates by acquiring a single self-node
(gluing two points of one irreducible component together): the genus drops by one
(`g = g' + 1`) while the node's two branches each contribute one new marked point on the
normalization, so `n' = n + 2`. -/
def IsNonSeparatingSplit (t t' : CurveType) : Prop :=
  t.genus = t'.genus + 1 ∧ t'.punctures = t.punctures + 2

/-- The Euler characteristic is also preserved (exactly, not just additively split) under a
non-separating nodal degeneration: `χ(t) = χ(t')`. -/
theorem IsNonSeparatingSplit.eulerChar_eq {t t' : CurveType} (h : IsNonSeparatingSplit t t') :
    eulerChar t = eulerChar t' := by
  obtain ⟨hg, hn⟩ := h
  simp only [eulerChar] at *
  omega

/-- **Boundary divisors of `M̄_{g,n}` have codimension exactly `1`.** Under a separating nodal
degeneration, the moduli dimensions of the two components add up to exactly one less than the
dimension of the original type: `dim(t₁) + dim(t₂) = dim(t) - 1`. This is the standard fact
that the boundary of the Deligne–Mumford compactification is a codimension-`1` divisor, now
recorded numerically alongside the Euler characteristic identity above. -/
theorem IsSeparatingSplit.moduliDim_eq {t t₁ t₂ : CurveType} (h : IsSeparatingSplit t t₁ t₂) :
    moduliDim t₁ + moduliDim t₂ = moduliDim t - 1 := by
  obtain ⟨hg, hn⟩ := h
  simp only [moduliDim] at *
  omega

/-- See `IsSeparatingSplit.moduliDim_eq`: the non-separating analogue. A non-separating nodal
degeneration also drops the moduli dimension by exactly `1`. -/
theorem IsNonSeparatingSplit.moduliDim_eq {t t' : CurveType} (h : IsNonSeparatingSplit t t') :
    moduliDim t' = moduliDim t - 1 := by
  obtain ⟨hg, hn⟩ := h
  simp only [moduliDim] at *
  omega

end CurveType

end Anabelian
