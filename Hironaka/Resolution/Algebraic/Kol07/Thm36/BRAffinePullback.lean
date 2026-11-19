/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BR
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex
import Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenterEraseEmpty
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenterPullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ReducedComponents
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Scheme.DisjointIntegralComponents

/-!
# The affine resolution along a smooth pullback of admissible pairs

Kollár's functoriality under smooth morphisms [Kol07, 34.1] for the affine resolution `BRAffine`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) on ONE smooth pullback pair of admissible pairs.
Given admissible pairs `(TX, embX)` of `X` and `(TZ, embZ)` of `Z`, both reduced equidimensional
(`IsReducedEquidimensional`) and affine, with `TZ` the pullback triple of `TX` along a smooth
`g : TZ.X.left ⟶ TX.X.left` and a flat `f : Z ⟶ X` with `embZ ≫ g = f ≫ embX`,

  `BRAffine k Z = ((BRAffine k X).pullback f).eraseEmpty`.

The proof is the mechanism Kollár states in one sentence — "(34.1) is a local property"
([Kol07, Theorem 36, proof]), for the functor "commutes with smooth morphisms" of [Kol07, 34.1]:

* `BP TZ = ((BP TX).pullback g).eraseEmpty` ([Kol07, Theorem 35 (4)], `BP_pullback_eraseEmpty`);
* the truncation index of `Z` is the absorbing index of any irreducible component `D` of `Z`
  (`firstCenterIndex_eq_componentIndex`,
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.EqualAbsorbingIndex`), which after the deletion is the
  index `eraseIdx` of the absorbing index of `D` in `V := (BP TX).pullback g`
  (`firstCenterIndex_eraseEmpty`), and that is the absorbing index in `BP TX` of the component `C`
  of `X` into which `f` maps `D` (`firstCenterIndex_pullback_of_flat_of_le`: the generic point of
  `D` goes to the generic point of `C` because generalisations lift along flat maps), which is the
  truncation index of `X`;
* so `BR_affine TZ embZ` is the restriction to `Z` of the deletion of the truncation of `V` at the
  index of `X` (`eraseEmpty_take`, `take_pullback`), and the deletions agree
  (`eraseEmpty_pullback_eraseEmpty'`, `pullback_comp` with the square `embZ ≫ g = f ≫ embX`).

The empty `Z` is its own case: every blow-up sequence on the empty scheme deletes to `nil`
(`eraseEmpty_eq_nil_of_isEmpty`). The exact form for a flat surjective `f` with `BP TZ = g^* BP TX`
on the nose, which the change of fields needs, is
`Hironaka.Resolution.Algebraic.Kol07.Thm36.BaseChangeAffine`.

The file also records that the components of a member of the class `HasDisjointIntegralComponents`
are integral (`isIntegral_irreducibleComponentOpen`, `isIntegral_irreducibleComponent`), used by
Hironaka's Main Theorems (`Hironaka.Resolution.Algebraic.Hir64`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The components of a member of `HasDisjointIntegralComponents` are integral -/

/-- On the class the open component `X.irreducibleComponentOpen C` is the component itself
(`HasDisjointIntegralComponents.irreducibleComponentOpen_eq`), hence an integral scheme: reduced as
an open of the reduced `X`, irreducible as the component `C`. -/
theorem isIntegral_irreducibleComponentOpen {X : Scheme.{u}} [IsNoetherian X]
    (hX : HasDisjointIntegralComponents X) (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsIntegral (X.irreducibleComponentOpen C) := by
  have hred : IsReduced X := hX.1
  have hUred : IsReduced (X.irreducibleComponentOpen C) :=
    isReduced_of_isOpenImmersion (X.irreducibleComponentOpen C).ι
  have hirr : IsIrreducible ((X.irreducibleComponentOpen C : TopologicalSpace.Opens X) : Set X) :=
      by
    rw [hX.irreducibleComponentOpen_eq C hC]
    exact hC.1
  have : IrreducibleSpace (X.irreducibleComponentOpen C) := Subtype.irreducibleSpace hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- On the class the reduced closed subscheme of a component is integral: `irreducibleComponentOpen
C` is closed (it is `C`), so its inclusion is a closed immersion and the subscheme of its kernel is
isomorphic to it (`Scheme.Hom.toImage`). -/
theorem isIntegral_irreducibleComponent {X : Scheme.{u}} [IsNoetherian X]
    (hX : HasDisjointIntegralComponents X) (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsIntegral (X.irreducibleComponentIdeal C hC).subscheme := by
  have hint := isIntegral_irreducibleComponentOpen hX C hC
  have hcl : IsClosedImmersion (X.irreducibleComponentOpen C).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι, hX.irreducibleComponentOpen_eq C hC]
    exact isClosed_of_mem_irreducibleComponents C hC
  have := IsIntegral.of_isIso (X.irreducibleComponentOpen C).ι.toImage
  change IsIntegral (X.irreducibleComponentOpen C).ι.ker.subscheme at this
  rwa [Scheme.irreducibleComponentIdeal_def]

/-! ### The affine resolution along a smooth pullback of admissible pairs -/

/-- Kollár's "(34.1) is a local property" for the affine resolution on one smooth pullback pair
[Kol07, Theorem 36, proof; 34.1]: for admissible pairs `(TX, embX)` of `X` and `(TZ, embZ)` of `Z`,
reduced equidimensional, with `TZ` the pullback of `TX` along a smooth `g` and `f : Z ⟶ X` flat
with `embZ ≫ g = f ≫ embX`, `BRAffine Z` is the deletion of the pullback of `BRAffine X` along `f`.
The truncation indices agree through the components (`firstCenterIndex_eq_componentIndex`), the
transport of the first-centre index along the flat `g` (`firstCenterIndex_pullback_of_flat_of_le`)
and through the deletion (`firstCenterIndex_eraseEmpty`); the truncation commutes with the deletion
(`eraseEmpty_take`) and with the restriction (`take_pullback`). -/
theorem BRAffine_eq_eraseEmpty_pullback_of_admissible (X Z : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    (hX : X.IsReducedEquidimensional k) (hZ : Z.IsReducedEquidimensional k)
    (TX TZ : Triple k) (embX : X ⟶ TX.X.left) (embZ : Z ⟶ TZ.X.left)
    (hadmX : AdmissibleEmbedding k X TX embX) (hadmZ : AdmissibleEmbedding k Z TZ embZ)
    (g : TZ.X.left ⟶ TX.X.left) [Smooth g] (hpb : TZ.IsPullbackOf TX g)
    (f : Z ⟶ X) [Flat f] (hsq : embZ ≫ g = f ≫ embX) :
    BRAffine k Z = ((BRAffine k X).pullback f).eraseEmpty := by
  have hNX : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hNZ : IsNoetherian Z := (Z ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hNTX : IsNoetherian TX.X.left := (TX.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hNTZ : IsNoetherian TZ.X.left := (TZ.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hclX : IsClosedImmersion embX := hadmX.1
  have hclZ : IsClosedImmersion embZ := hadmZ.1
  have hredX : IsReduced X := hX.1
  have hredZ : IsReduced Z := hZ.1
  obtain ⟨dX, hdX⟩ := hX.2
  obtain ⟨dZ, hdZ⟩ := hZ.2
  rw [BRAffine_eq_eraseEmpty_BR_affine k X TX embX hadmX,
    BRAffine_eq_eraseEmpty_BR_affine k Z TZ embZ hadmZ, eraseEmpty_pullback_eraseEmpty']
  rcases isEmpty_or_nonempty Z with hZe | hZn
  · rw [eraseEmpty_eq_nil_of_isEmpty _ hZe, eraseEmpty_eq_nil_of_isEmpty _ hZe]
  · have hBPZ : BP TZ = ((BP TX).pullback g).eraseEmpty := BP_pullback_eraseEmpty TX TZ g hpb
    -- a component `D` of `Z` and the component `C` of `X` into which `f` maps it
    set D : Set Z := _root_.irreducibleComponent hZn.some with hDdef
    have hD : D ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents _
    obtain ⟨C, hC, hfC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible (f '' D)
      (hD.1.image f f.continuous.continuousOn)
    have hIC : IsIntegral ((X.irreducibleComponentIdeal C hC).map embX).subscheme :=
      isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced C hC embX
    have hID : IsIntegral ((Z.irreducibleComponentIdeal D hD).map embZ).subscheme :=
      isIntegral_subscheme_map_irreducibleComponentIdeal_of_isReduced D hD embZ
    have hηC : IsGenericPoint hC.1.genericPoint C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hηD : IsGenericPoint hD.1.genericPoint D :=
      hD.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hD)
    have hfη : f hD.1.genericPoint = hC.1.genericPoint :=
      map_genericPoint_eq_of_flat f hD hfC hηC hηD
    have hle : ((X.irreducibleComponentIdeal C hC).map embX).comap g ≤
        (Z.irreducibleComponentIdeal D hD).map embZ := by
      rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hsq,
        Scheme.IdealSheafData.comap_comp, comap_map_of_isClosedImmersion]
      exact comap_irreducibleComponentIdeal_le f C hC D hD hfC
    have hηη' : g (embZ hD.1.genericPoint) = embX hC.1.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hfη]
    -- the truncation indices
    have hidx : firstCenterIndex (BP TZ) TZ.I =
        eraseIdx ((BP TX).pullback g) (firstCenterIndex (BP TX) TX.I) := by
      rw [firstCenterIndex_eq_componentIndex (d := dZ) Z TZ embZ hadmZ D hD, componentIndex_def,
        hBPZ, firstCenterIndex_eraseEmpty,
        firstCenterIndex_eq_componentIndex (d := dX) X TX embX hadmX C hC, componentIndex_def]
      congr 1
      exact firstCenterIndex_pullback_of_flat_of_le (BP TX) g _
        (isGenericPoint_map_irreducibleComponentIdeal C hC embX hηC) _ hle
        (isGenericPoint_map_irreducibleComponentIdeal D hD embZ hηD) hηη'
    -- the two restrictions
    rw [BR_affine_eq, BR_affine_eq, hidx, hBPZ, eraseEmpty_take, eraseEmpty_pullback_eraseEmpty',
      ← take_pullback, ← pullback_comp, hsq, pullback_comp]

end Hironaka.Resolution
