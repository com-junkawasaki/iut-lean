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

**This is not progress toward proving the (open, integer) ABC conjecture or
IUT** — it is real, verified, but modest work in the immediate neighborhood
of the topic, building on a theorem mathlib4 already had. No anabelian
geometry or IUT-specific formalization exists in this repository yet; that
remains a long-horizon, likely multi-year goal (see below), and this project
does not claim otherwise.

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
