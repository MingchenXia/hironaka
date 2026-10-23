# De Jong alterations over arbitrary fields

The library exposes de Jong's alteration theorem through the original native
scheme-theoretic proposition from `DeJongAlterations`. The input field can be
imperfect and can have any characteristic.

```lean
import Hironaka.DeJong

#check Hironaka.deJongAlterationTheorem
#check Hironaka.exists_alterationWithBoundary
```

Both declarations are also exported by the full library root:

```lean
import Hironaka

universe u

example (k : Type u) [Field k] :
    DeJongAlterations.DeJongAlterationTheorem k :=
  Hironaka.deJongAlterationTheorem k
```

## Mathematical statement

Let `k` be a field, let `p : X ⟶ Spec (.of k)` be an integral separated
finite-type variety, and let `Z` be any proper closed subset of `X`.
There exist an alteration `f : Y → X`, an open immersion `j : Y → Ybar`,
and an integral regular projective `k`-variety `Ybar` such that

```text
j(f⁻¹(Z)) ∪ (Ybar \ j(Y))
```

is exactly the support of a reduced strict normal-crossings divisor.
The alteration and inclusion commute with the original structure maps to
`Spec k`. No morphism from the compactification `Ybar` to `X` is required.

The native `DeJongAlterations.IsAlteration` requires a proper dominant map
between integral schemes, finite over a nonempty open in the target. The
native boundary structure retains effective Cartier and reducedness
conditions, regularity of all actual component intersections, and their
expected pure codimensions. The conclusion is not replaced by a support
inclusion or by a different boundary ideal.

`Hironaka.deJongAlterationTheorem` takes only `(k : Type u) [Field k]`.
The explicitly specialized public theorem has the type:

```lean
Hironaka.exists_alterationWithBoundary
    (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    (p : X ⟶ AlgebraicGeometry.Spec (.of k))
    (hX : DeJongAlterations.IsVariety p)
    (Z : TopologicalSpace.Closeds X) (hZ : Z ≠ ⊤) :
    Nonempty (DeJongAlterations.AlterationWithBoundary p (Z : Set X))
```

This display records the declaration's arguments and result; the source is
[`Hironaka/DeJong.lean`](../Hironaka/DeJong.lean).

## Proof route

Over an algebraically closed field, the proof supplies the actual valuation
stable-modification existence and uniqueness theorems, marked-dualizing-bundle
projectivity, and generic-smooth numerical-stability openness to the integrated
alteration construction. The openness argument constructs original-fibre
sections, an actual relative affine polarization and whole line-bundle power
comparisons; positive native component degrees give stability. Nodal-family
resolution supplies the strict SNC output.

For an arbitrary field `k`, pass to its algebraic closure. The scalar extension
of the original integral variety may be reducible or nonreduced. The proof
selects a dominating reduced irreducible component and descends it to a finite
intermediate extension. The alteration, open immersion, projective
compactification and all boundary components and intersections then descend
together to one finite field extension. Faithfully-flat Cartier descent,
whole ideal identities, regularity and pure codimension reconstruct every
strict SNC condition and the exact original prescribed-boundary support.
Composition with the finite component alteration returns an alteration of
the original `X`. The compactification is regular and projective over `k`.
This argument does not assume geometric integrality of `X`.

The public declarations apply that proved endpoint directly; no remaining
stability, projectivity, finite-model or alteration-existence premise is added.
The mathematical blueprint is in
[`blueprint/dejong-alterations.tex`](../blueprint/dejong-alterations.tex).

## Source and verification

The proof is included as the local Lake package
[`vendor/DeJongAlterations`](../vendor/DeJongAlterations). It contains the native
producer import cone for the completed theorem, extracted from
`MingchenXia/archon-nakamaye` at source commit
`187095a1888ecadb1f365e6d4dc0cb75dcd61eff`. The native proof sources retain
their original bytes. A narrow package root exposes the completed theorem;
unrelated project modules and unpublished drafts are excluded.

- Proved endpoint: [`DeJongAlterations.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem`](../vendor/DeJongAlterations/DeJongAlterations/StableModificationBridge/AlterationUnconditional.lean).
- Native statement and full output: [`Theorem.lean`](../vendor/DeJongAlterations/DeJongAlterations/Theorem.lean).
- Local package guide: [`vendor/DeJongAlterations/README.md`](../vendor/DeJongAlterations/README.md).
- Provenance and source-hash inventory:
  [`vendor/DeJongAlterations/SOURCE.json`](../vendor/DeJongAlterations/SOURCE.json).

The original source repository is private. Every proof source needed by this
integration is included here, so public builds do not depend on access to that
repository. The vendored package has no `Hironaka` dependency; the package
dependency direction remains acyclic.

Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` agree with this repository's pins.
The original contributor/license headers are preserved in the vendored source;
this integration does not relicense those files.

The integration's local commands are:

```sh
python3 scripts/check_dejong_source.py
lake build Hironaka.DeJong
lake build
lake test
```

The source check verifies every vendored source hash and Git blob, the complete
import closure, and the shared dependency/toolchain pins without contacting the
original repository.

The root package treats its warnings as errors. Upstream warnings in the
unchanged vendored source are preserved and inventoried in the verification
receipt; a global `--wfail` would also reject those dependency warnings.

The recursive module-ownership audit covers both `Hironaka` and
`DeJongAlterations`, including private and generated declarations, and rejects
axioms other than `propext`, `Classical.choice` and `Quot.sound`.
The combined-import build and audit results are recorded in
[`audit/dejong-integration-20261023/validation.json`](../audit/dejong-integration-20261023/validation.json).
GitHub CI is skipped by the repository owner's instruction.

The mathematical source is A. J. de Jong, *Smoothness, semi-stability and
alterations*, Publications Mathématiques de l'IHÉS **83** (1996), 51–93,
Theorem 4.1 (printed page 66),
[DOI: 10.1007/BF02698644](https://doi.org/10.1007/BF02698644),
[Numdam](https://www.numdam.org/item/PMIHES_1996__83__51_0/).
The independent paper results and the separate perfect-field generically-étale
refinement are not claimed by this API. The original analytic gaps G1, G3, G4,
G8 and G9 retain their existing scope and status.
