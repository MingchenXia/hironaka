# De Jong alterations over arbitrary fields

The library exposes de Jong's alteration theorem through the original native
scheme-theoretic proposition from `Hironaka`. The input field can be
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
    Hironaka.DeJongAlterationTheorem k :=
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

The native `Hironaka.IsAlteration` requires a proper dominant map
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
    (hX : Hironaka.IsVariety p)
    (Z : TopologicalSpace.Closeds X) (hZ : Z ≠ ⊤) :
    Nonempty (Hironaka.AlterationWithBoundary p (Z : Set X))
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

The proof is part of Hironaka. Its algebra and geometry modules are under
`Hironaka.Algebra` and `Hironaka.Geometry`. The original contributor and
license headers are retained throughout the proof.

- The public entry points are in [Hironaka.DeJong](../Hironaka/DeJong.lean).
- The native statement and output are in
  [Hironaka.Geometry.AlterationTheorem](../Hironaka/Geometry/AlterationTheorem.lean).
- The proved endpoint is in
  [Hironaka.Geometry.StableModificationBridge.AlterationUnconditional](../Hironaka/Geometry/StableModificationBridge/AlterationUnconditional.lean).
- The source revision and normalized module hashes are in the
  [source inventory](../audit/dejong-source.json).

Build and verify the proof with the pinned Lean and Mathlib versions.

```sh
python3 scripts/check_dejong_source.py
lake build +Hironaka.DeJong
lake build
lake test
```

The source check validates the complete local import closure and its module
hashes. The axiom check audits Hironaka-owned declarations, including private
and generated declarations, against `propext`, `Classical.choice`, and
`Quot.sound`.

The mathematical source is A. J. de Jong, *Smoothness, semi-stability and
alterations*, Publications Mathématiques de l'IHÉS **83** (1996), 51–93,
Theorem 4.1 (printed page 66),
[DOI: 10.1007/BF02698644](https://doi.org/10.1007/BF02698644),
[Numdam](https://www.numdam.org/item/PMIHES_1996__83__51_0/).
The independent paper results and the separate perfect-field generically-étale
refinement are not claimed by this API. For the complex-analytic theorems, see
the [current resolution scope](../STATUS.md#resolution-goals).
