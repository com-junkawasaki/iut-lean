# iut-lean

An independent, from-scratch attempt at formalizing anabelian geometry and
inter-universal Teichmüller theory (IUT) — Shinichi Mochizuki's claimed proof
of the ABC conjecture — in [Lean 4](https://leanprover.github.io/) on top of
[mathlib4](https://github.com/leanprover-community/mathlib4).

## Status

This is a bare scaffold: a `lakefile.lean`, a `lean-toolchain` pinned to
whatever version [mathlib4](https://github.com/leanprover-community/mathlib4)
currently requires, and a single placeholder file
(`IutLean/Basic.lean`) with no mathematical content. No anabelian geometry or
IUT formalization work has started yet.

`lake update` (which would pull down `mathlib4`, a very large repository)
has **not** been run or verified as part of this scaffolding pass, and
`lake build` has not been attempted, because neither `lake` nor `elan` were
available in the environment that created this scaffold. Getting a clean
`lake update && lake build` is a follow-up task, not something this commit
claims to have verified.

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
lake update   # not yet run/verified in this repo — will fetch mathlib4
lake build
```

## License

No license has been chosen yet.
