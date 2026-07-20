import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Real.Irrational

/-!
# The absolute Galois group of `ℚ` is nontrivial

`absoluteGaloisGroup ℚ = Gal(ℚ‾/ℚ)` is one of the deepest objects in all of mathematics — almost
nothing about its structure is known in closed form, which is exactly why it is central to the
Langlands program and to the arithmetic side of anabelian geometry / IUT. This file records the
first, most basic fact: it is not the trivial group.

The strategy avoids the two mathlib4 instance-resolution obstacles documented in
ADR-2607210000 (`IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` and
`Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` both failing `infer_instance`, even when the exact
matching named instances are supplied via `haveI`) by working with `AlgebraicClosure ℚ` directly
and always projecting the needed field off an *explicit* term
(`(AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x`) rather than relying on instance search to find
it via a re-derived `Algebra.IsAlgebraic` instance.

The classical argument: `√2` and `-√2` are distinct elements of `AlgebraicClosure ℚ` with the
same minimal polynomial `X² - 2` over `ℚ`, so (since `AlgebraicClosure ℚ` is a normal extension)
they lie in the same orbit of `Gal(ℚ‾/ℚ)` — i.e. some automorphism sends one to the other. Such
an automorphism cannot be the identity, so the group has at least two elements.
-/

open Polynomial Field

/-- No rational number squares to `2` — the classical irrationality of `√2`, stated purely
algebraically (no explicit reference to `Irrational` needed downstream). Derived from mathlib4's
`irrational_sqrt_two` via `ℝ`. -/
theorem no_rat_sq_two : ∀ q : ℚ, q ^ 2 ≠ 2 := by
  intro q hq
  have h1 : (q : ℝ) ^ 2 = 2 := by exact_mod_cast hq
  have h2 : (q : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 := by rw [h1, Real.sq_sqrt]; norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact irrational_sqrt_two ⟨q, h⟩
  · exact irrational_sqrt_two ⟨-q, by push_cast; linarith [h]⟩

/-- `AlgebraicClosure ℚ`, being algebraically closed, contains a root of `X² - 2`. -/
theorem exists_sqrt_two : ∃ r : AlgebraicClosure ℚ, r ^ 2 = 2 := by
  have hdeg : (X ^ 2 - C (2 : AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (by norm_num)]; decide
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨r, ?_⟩
  have h : r ^ 2 - 2 = 0 := by simpa [IsRoot] using hr
  rwa [sub_eq_zero] at h

/-- The minimal polynomial of any square root of `2` in `AlgebraicClosure ℚ` is exactly
`X² - 2`: it is irreducible over `ℚ` (Kummer's criterion, `X_pow_sub_C_irreducible_of_prime`,
using `no_rat_sq_two`), monic, and killed by `r`. -/
theorem minpoly_sqrt_two (r : AlgebraicClosure ℚ) (hr : r ^ 2 = 2) :
    minpoly ℚ r = X ^ 2 - C 2 := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact X_pow_sub_C_irreducible_of_prime Nat.prime_two no_rat_sq_two
  · simp [aeval_def, eval₂_sub, eval₂_pow, hr]
  · exact monic_X_pow_sub_C 2 (by norm_num)

/-- `AlgebraicClosure ℚ` is a normal extension of `ℚ` — needed for the Galois-orbit argument
below. Constructed directly via `normal_iff` rather than relying on `infer_instance` to find
`Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)`, which (per ADR-2607210000) fails even when supplied
explicitly via `haveI`; instead the needed field is projected directly off the named term
`AlgebraicClosure.isAlgebraic ℚ`. -/
instance : Normal ℚ (AlgebraicClosure ℚ) :=
  normal_iff.2 fun x =>
    ⟨((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩

/-- **`Gal(ℚ‾/ℚ)` is not the trivial group.** `√2` and `-√2` are distinct roots of the same
irreducible polynomial `X² - 2`, so by normality they lie in a common `Gal(ℚ‾/ℚ)`-orbit
(`Normal.minpoly_eq_iff_mem_orbit`): some automorphism `g` sends `-√2` to `√2`. If the group were
trivial, `g` would be the identity, forcing `-√2 = √2`, i.e. `2 * √2 = 0` in a field where `2 ≠ 0`
— contradicting `√2 ≠ 0`. -/
theorem absoluteGaloisGroup_rat_not_subsingleton :
    ¬ Subsingleton (Field.absoluteGaloisGroup ℚ) := by
  show ¬ Subsingleton (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  obtain ⟨r, hr⟩ := exists_sqrt_two
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  have hmr : minpoly ℚ r = X ^ 2 - C 2 := minpoly_sqrt_two r hr
  have hmnr : minpoly ℚ (-r) = X ^ 2 - C 2 := minpoly_sqrt_two (-r) (by rw [neg_pow]; simp [hr])
  have heq : minpoly ℚ r = minpoly ℚ (-r) := by rw [hmr, hmnr]
  have hmem := (Normal.minpoly_eq_iff_mem_orbit
    (F := ℚ) (E := AlgebraicClosure ℚ) (x := r) (y := -r)).mp heq
  obtain ⟨g, hg⟩ := hmem
  intro hsub
  have hg1 : g = 1 := Subsingleton.elim g 1
  rw [hg1] at hg
  simp at hg
  apply hr0
  have h2 : r + r = 0 := by
    calc r + r = -r + r := by rw [hg]
    _ = 0 := by ring
  have h3 : (2 : AlgebraicClosure ℚ) * r = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
