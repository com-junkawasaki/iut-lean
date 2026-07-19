import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The absolute Galois group and the anabelian program

Grothendieck's anabelian program identifies `π₁(Spec K) = Gal(K^sep/K)`, the absolute Galois
group, as the "fundamental group of a point" — the base case that the fundamental groups of
hyperbolic curves over `K` sit over (via the arithmetic-geometric exact sequence
`1 → π₁^geom → π₁(X) → Gal(K^sep/K) → 1`, not modeled here).

`Mathlib.FieldTheory.AbsoluteGaloisGroup` already defines `Field.absoluteGaloisGroup K` directly
as `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` — this is a real, already-existing object, in
contrast to the abstract `Mathlib.CategoryTheory.Galois` framework, which is not yet connected
to any actual field or scheme anywhere in mathlib4 (see the README's "Roadmap" section). This
file adds a first genuinely new fact about it: the degenerate case where the base field is
already algebraically closed.

Grep-verified (2026-07-20): `absoluteGaloisGroup` appears nowhere else in mathlib4 outside its
own definition file and the abelianization file, so this is unexplored territory.
-/

open Field

/-- **The absolute Galois group of an algebraically closed field is trivial.** If `K` is already
algebraically closed, `K` is its own algebraic closure (`IsAlgClosure K K`), so
`AlgebraicClosure K` is `K`-algebra-isomorphic to `K` itself (`IsAlgClosure.equiv`); transporting
along this isomorphism via `AlgEquiv.autCongr` turns `absoluteGaloisGroup K` into
`K ≃ₐ[K] K`, which is a subsingleton (already known to mathlib4) since any `K`-algebra
endomorphism of `K` is forced to be the identity. This is the expected degenerate case of
`π₁(Spec K) = 1` for `K` "already algebraically closed" (no nontrivial finite étale covers of a
point over an algebraically closed field). -/
theorem Field.absoluteGaloisGroup_subsingleton_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] : Subsingleton (Field.absoluteGaloisGroup K) := by
  have e : AlgebraicClosure K ≃ₐ[K] K := IsAlgClosure.equiv K (AlgebraicClosure K) K
  exact (AlgEquiv.autCongr e).toEquiv.subsingleton_congr.mpr inferInstance

/-- **Usable upgrade of the previous theorem to a `Unique` instance.** `absoluteGaloisGroup K`
is not just subsingleton but has an explicit inhabitant (the identity automorphism, `1` in its
`Group` structure), giving `Unique (absoluteGaloisGroup K)` — the form actually convenient for
downstream use (e.g. `default`/`Unique.eq_default` rather than needing to invoke
`Subsingleton.elim` against an arbitrary witness each time). -/
noncomputable instance Field.absoluteGaloisGroup.instUnique_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] : Unique (Field.absoluteGaloisGroup K) :=
  haveI := absoluteGaloisGroup_subsingleton_of_isAlgClosed (K := K)
  uniqueOfSubsingleton 1

/-- **The absolute Galois group of `ℝ` has exactly two elements** — the archetypal nontrivial
example of a Galois group in all of mathematics, `Gal(ℂ/ℝ) ≅ ℤ/2` (identity and complex
conjugation). `ℂ` is `ℝ`'s algebraic closure (`Complex.isAlgClosed` is the Fundamental Theorem
of Algebra, and `ℂ` is algebraic — indeed finite — over `ℝ`), so `absoluteGaloisGroup ℝ`
transports along `IsAlgClosure.equiv`/`AlgEquiv.autCongr` to `ℂ ≃ₐ[ℝ] ℂ`, whose cardinality is
computed by the general Galois-theory fact `IsGalois.card_aut_eq_finrank` together with
`Complex.finrank_real_complex : Module.finrank ℝ ℂ = 2`. -/
theorem Field.absoluteGaloisGroup_real_card :
    Nat.card (Field.absoluteGaloisGroup ℝ) = 2 := by
  haveI : IsAlgClosure ℝ ℂ := ⟨Complex.isAlgClosed, inferInstance⟩
  have e : AlgebraicClosure ℝ ≃ₐ[ℝ] ℂ := IsAlgClosure.equiv ℝ (AlgebraicClosure ℝ) ℂ
  have heq : Nat.card (Field.absoluteGaloisGroup ℝ) = Nat.card (ℂ ≃ₐ[ℝ] ℂ) :=
    Nat.card_congr (AlgEquiv.autCongr e).toEquiv
  rw [heq, IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

/-- **`Gal(ℂ/ℝ)` as an actual group, not just a cardinality fact**: `absoluteGaloisGroup ℝ` is
isomorphic to `Multiplicative (ZMod 2)`, i.e. it really is (a copy of) `ℤ/2`. Any two groups of
the same prime order are isomorphic (`mulEquivOfPrimeCardEq`, via both being cyclic of that
order), so this follows immediately from `absoluteGaloisGroup_real_card` together with the
(trivial) fact that `Multiplicative (ZMod 2)` itself has cardinality `2`. -/
theorem Field.absoluteGaloisGroup_real_mulEquiv :
    Nonempty (Multiplicative (ZMod 2) ≃* Field.absoluteGaloisGroup ℝ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card]
  exact ⟨mulEquivOfPrimeCardEq h1 absoluteGaloisGroup_real_card⟩

/-- **A sanity-check corollary tying the file together**: `ℝ` is not algebraically closed. Of
course this is elementary on its own (e.g. `X² + 1` has no real root), but it also follows for
free by combining the two previous theorems: if `ℝ` were algebraically closed,
`absoluteGaloisGroup_subsingleton_of_isAlgClosed` would force `Nat.card (absoluteGaloisGroup ℝ)`
to be at most `1`, contradicting `absoluteGaloisGroup_real_card` (`= 2`). -/
theorem Field.not_isAlgClosed_real : ¬ IsAlgClosed ℝ := by
  intro h
  haveI hsub := absoluteGaloisGroup_subsingleton_of_isAlgClosed (K := ℝ)
  have hle : Nat.card (Field.absoluteGaloisGroup ℝ) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  rw [absoluteGaloisGroup_real_card] at hle
  omega
