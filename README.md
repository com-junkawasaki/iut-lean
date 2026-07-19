# iut-lean

An independent, from-scratch attempt at formalizing anabelian geometry and
inter-universal Teichmüller theory (IUT) — Shinichi Mochizuki's claimed proof
of the ABC conjecture — in [Lean 4](https://leanprover.github.io/) on top of
[mathlib4](https://github.com/leanprover-community/mathlib4).

## Status

`lake update` and `lake build` have now been run and verified against
[mathlib4](https://github.com/leanprover-community/mathlib4) (`elan`/`lake`
installed via Homebrew's `elan-init`). The project builds cleanly.

The repository contains:

- `IutLean/Basic.lean` — trivial placeholder, no mathematical content.
- `IutLean/MasonStothers.lean` — a genuine, `sorry`-free corollary of
  mathlib4's existing proof of the **Mason–Stothers theorem**
  (`Polynomial.abc` in `Mathlib.NumberTheory.FLT.MasonStothers`): the
  polynomial function-field analogue of the ABC conjecture, which (unlike
  the integer ABC conjecture) is a fully proven theorem, already formalized
  in mathlib4. `Polynomial.abc_of_ne_const` removes the "all derivatives
  vanish" escape clause of that theorem under the natural hypothesis that
  the coefficient field is torsion-free (e.g. any characteristic-zero
  field) and at least one of the three polynomials is non-constant.
  Verified with `#print axioms`: depends only on the standard
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra axioms.

- `IutLean/Anabelian/CurveType.lean` — the numerical/combinatorial type
  `(g, n)` (genus, punctures) that anabelian geometry restricts attention to
  (the *hyperbolicity* condition `2g - 2 + n > 0`), plus a chain of genuine,
  `sorry`-free facts built on it: the classification of the four
  non-hyperbolic types (both as a proposition and as a computable `Finset`);
  the Euler characteristic `eulerChar` and moduli dimension `moduliDim`
  invariants, the identity linking them, and their behavior under adding
  punctures/genus; the numerical (unramified) degree formula and its
  hyperbolicity-preservation consequence; finiteness of hyperbolic types
  below a given moduli dimension; the classification of the dimension-`0`
  and dimension-`1` types (`(0,3)`, `(0,4)`, `(1,1)` — the classical building
  blocks of Grothendieck–Teichmüller theory); and the numerical shadow of
  nodal degeneration (separating/non-separating splits) at the boundary of
  the Deligne–Mumford compactification `M̄_{g,n}`, including its
  codimension-`1` property. All of this is purely combinatorial: no
  fundamental groups, Galois categories, or schemes are modeled yet.

**This is not progress toward proving the (open, integer) ABC conjecture or
IUT** — it is real, verified, but modest work in the immediate neighborhood
of the topic. No anabelian geometry or IUT-specific formalization exists in
this repository yet in the sense of actual fundamental groups or covering
spaces; that remains a long-horizon, likely multi-year goal (see below and
"Roadmap: the next real milestone"), and this project does not claim
otherwise.

## Roadmap: the next real milestone (researched, not yet attempted)

The genuinely next-level piece of anabelian geometry — actually defining
the étale fundamental group `π₁(X)` of a curve (or `Gal(k_sep/k)` for a
field `k`) — requires connecting mathlib4's existing abstract Galois
category framework (`Mathlib.CategoryTheory.Galois`, which proves the
SGA1 main theorem in the abstract, and already instantiates it for finite
`G`-sets of an *externally given* group `G` in `Galois/Examples.lean`) to an
*actual* field or scheme, so that the group itself is recovered intrinsically
as `Aut(fiber functor)` rather than assumed. As of this writing, **no such
instantiation exists anywhere in mathlib4** (`grep`-verified: zero hits for
`PreGaloisCategory`/`GaloisCategory` outside the `CategoryTheory/Galois`
directory itself).

Concretely, for the field case (the simplest, and the natural first target:
`π₁(Spec k) = Gal(k_sep/k)`), the category needed is finite étale
`k`-algebras (not just field extensions — finite products of separable
extensions are needed to get finite coproducts). Investigated so far:

- `Mathlib.Algebra.Category.CommAlgCat` exists (the category of commutative
  `R`-algebras) but has **no `HasTerminal`/`IsInitial` instance** and no
  finite-étale full subcategory anywhere.
- The atomic fact one might expect to need first — that `k` behaves as an
  initial object, i.e. `Subsingleton (k →ₐ[k] A)` for any `k`-algebra `A` —
  is **already available** in mathlib4 via `infer_instance` (verified
  2026-07-20), so that is not new territory.
- What is missing is the actual category-theoretic package: a
  `CommAlgCat`/`CommEtaleAlgCat`-style bundled category restricted to
  finite étale `k`-algebras, plus proofs of all five `PreGaloisCategory`
  axioms (`HasTerminal`, `HasPullbacks`, `HasFiniteCoproducts`,
  `HasQuotientsByFiniteGroups`, the mono/direct-summand splitting axiom) and
  the six `FiberFunctor` axioms for the forgetful functor to `FintypeCat`.
  This is a substantial, multi-lemma undertaking (comparable in scope to
  what a specialized effort like LANA is attempting) — not something to
  rush in a single small step, and not attempted in this repository yet.

## Relationship to LANA / anabelian.org

This project is inspired by, but is **not affiliated with, endorsed by, or a
fork of**, the RIMS "LANA" initiative (a project associated with Mochizuki,
Johan Commelin, and Adam Topaz aiming to formalize anabelian geometry / IUT
in Lean). As of this writing, LANA's official site (`anabelian.org`) is only
a stub with no public repository or code released, so there is nothing to
fork from — this repository is an independent, original effort built from
scratch. If and when LANA (or any other group) publishes code, this project
may look to align terminology and scope with it, but currently tracks no
upstream beyond mathlib4 itself.

## Goals (aspirational, tracking the publicly stated aims of efforts like LANA)

- Formalize the basic objects of anabelian geometry (fundamental groups of
  hyperbolic curves over number fields, Grothendieck's anabelian conjectures,
  etc.) as a foundation.
- Work toward formalizing the core constructions of inter-universal
  Teichmüller theory as originally proposed by Mochizuki.
- Eventually formalize enough of the argument to state (and, aspirationally,
  verify) the claimed proof of the ABC conjecture / Szpiro's conjecture that
  IUT purports to establish.

These are long-horizon, likely multi-year goals. This repository currently
contains none of that mathematics — it is scaffolding only.

## Building

```sh
lake update   # fetches mathlib4 (large; uses the mathlib4 build cache)
lake build
```

## License

No license has been chosen yet.
