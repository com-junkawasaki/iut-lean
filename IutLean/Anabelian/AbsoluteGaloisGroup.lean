import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic

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
