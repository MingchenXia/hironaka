/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ContractionStein
import DeJongAlterations.StableModification.CurvesField.StableDownSchemeTop

/-!
# One exceptional blow-down (Temkin, Prop. 4.4.6 and Lemma 4.4.5)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3188–3229) and Lemma 4.4.5 (T:3178–3186). This file states the contraction
condition without fibre types, so that it can be transported along `b ≫ β'' = β`
(`ContractsExactlyAt`, `contractsExactly_iff_contractsExactlyAt`), and proves, for a blow-down
`b : X → Y` contracting exactly the component `Z` of the closed fibre (blueprint
`lem:sm-bdg-exceptional-blowdown`, `lem:sm-bdg-components`, `sm-blow-down-global.tex`):

* `isNodalCurve_of_contractsExactlyAt`: Temkin's Lemma 4.4.5 (nodal part) in this form;
* `ncard_genericPoints_closedFibre`: the closed fibre of `Y` has one irreducible component less
  than that of `X` (the components of `Y_{s₀}` are the images of those of `X_{s₀}` other than
  `Z`, since `b_{s₀}` is an isomorphism off `x = b(Z)`); this is the termination measure of the
  iteration (Temkin T:3192–3194: "we can perform at most `|Γ₀(C')|` contractions").
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus
open Geometry.ModificationCenter (isomorphismOpen center)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Absolute

variable {V : Type u} [CommRing V] [IsLocalRing V] {X Y : Scheme.{u}}

local notation "s₀" => IsLocalRing.closedPoint V

/-- **`b` contracts exactly the component `Z` of the closed fibre of `q`**, stated on `X`: a
generic point `w` of the closed fibre `X_{s₀}` of `q : X → Spec V` is mapped with its closure in
`X` to a single point of `Y` iff `w = Z`. -/
def ContractsExactlyAt (q : X ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y) (Z : q.fiber s₀) : Prop :=
  ∀ w ∈ genericPoints (q.fiber s₀), (b '' closure {q.fiberι s₀ w}).Subsingleton ↔ w = Z

/-- The closed fibre is a closed subspace. -/
theorem isClosedEmbedding_fiberι_closedPoint (q : X ⟶ Spec (CommRingCat.of V)) :
    Topology.IsClosedEmbedding (q.fiberι s₀) := by
  refine ⟨(q.fiberι s₀).isEmbedding, ?_⟩
  rw [Scheme.Hom.range_fiberι]
  exact (IsLocalRing.isClosed_singleton_closedPoint V).preimage q.continuous

/-- The closure of a point of the closed fibre is the image of its closure in the fibre. -/
theorem closure_fiberι_singleton (q : X ⟶ Spec (CommRingCat.of V)) (w : q.fiber s₀) :
    closure ({q.fiberι s₀ w} : Set X) = q.fiberι s₀ '' closure {w} := by
  rw [← Set.image_singleton, (isClosedEmbedding_fiberι_closedPoint q).closure_image_eq]

end Absolute

section Nodal

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  [Infinite (IsLocalRing.ResidueField V)] {X Y : Scheme.{u}}

local notation "s₀" => IsLocalRing.closedPoint V

omit [Finite (PrimeSpectrum V)] [Infinite (IsLocalRing.ResidueField V)] in
/-- **The two forms of the contraction condition agree** for `q = b ≫ p`. -/
theorem contractsExactly_iff_contractsExactlyAt (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y)
    (Z : (b ≫ p).fiber s₀) : ContractsExactly p b Z ↔ ContractsExactlyAt (b ≫ p) b Z := by
  have key : ∀ w : (b ≫ p).fiber s₀, (b '' closure {(b ≫ p).fiberι s₀ w}).Subsingleton ↔
      (Curves.fiberMap b p s₀ '' closure {w}).Subsingleton := by
    intro w
    rw [closure_fiberι_singleton, Set.image_image]
    have : (fun z => b ((b ≫ p).fiberι s₀ z)) = fun z => p.fiberι s₀ (Curves.fiberMap b p s₀ z) := by
      funext z
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι]
    rw [this, ← Set.image_image, (p.fiberι s₀).isEmbedding.injective.subsingleton_image_iff]
  exact ⟨fun h w hw => (key w).trans (h w hw), fun h w hw => (key w).symm.trans (h w hw)⟩


open scoped Classical in
/-- **Temkin's Lemma 4.4.5, nodal part, for a structure map `q = b ≫ p`** (blueprint
`lem:sm-bdg-exceptional-blowdown`): `isNodalCurve_of_contractsExactly` with the exceptional
component `Z` given as a point of the closed fibre of `q` and the contraction condition in the
form `ContractsExactlyAt`. -/
theorem isNodalCurve_of_contractsExactlyAt
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y) (q : X ⟶ Spec (CommRingCat.of V))
    (hq : b ≫ p = q) [IsIntegral Y] [IsIntegral X] [IsModification b] [IsProper p]
    [LocallyOfFinitePresentation p] [Flat p] [DeJong.IsNodalCurve q] [IsProper q]
    [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]
    (hp : IsProjectiveOver p) (hbp : DeJong.IsRelativelyProjective p b)
    (hnormal : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hη : Curves.IsEtaModification b p) {Z : q.fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactlyAt q b Z)
    (hgZ : 0 ≤ componentGenus
      (structureCoeff (A := ↑((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V)))
        (q.fiberToSpecResidueField s₀)) Z)
    (m : ℕ) [Fintype (nodesIn (q.fiberToSpecResidueField s₀) (closure {Z}))]
    (htree : (nodalGraph (q.fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal q s₀) (closure {Z})).IsP1Tree {Z})
    (hcard : ((nodalGraph (q.fiberToSpecResidueField s₀)
      (topologicalKrullDim_fiber_le_one_of_nodal q s₀)
      (closure {Z})).boundary {Z}).card + m ≤ 2) :
    DeJong.IsNodalCurve p ∧ m ≤ 1 ∧
      (m = 1 → ∀ y : p.fiber s₀, p.fiberι s₀ y = b (q.fiberι s₀ Z) →
        DeJong.IsSmoothAt (p.fiberToSpecResidueField s₀) y) := by
  subst hq
  obtain ⟨h1, h2, h3⟩ := isNodalCurve_of_contractsExactly p b hsep hp hbp hnormal hcurve hη hZ
    ((contractsExactly_iff_contractsExactlyAt p b Z).2 hc) hgZ m htree hcard
  refine ⟨h1, h2, fun hm y hy => ?_⟩
  have : y = Curves.fiberMap b p s₀ Z := by
    apply (p.fiberι s₀).isEmbedding.injective
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Curves.fiberMap_fiberι]
  rw [this]
  exact h3 hm

end Nodal

section Count

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X Y : Scheme.{u}}
  (p : Y ⟶ Spec (CommRingCat.of V)) (b : X ⟶ Y)

local notation "s₀" => IsLocalRing.closedPoint V

variable [IsIntegral Y] [IsIntegral X] [IsModification b] [IsProper p]
  [LocallyOfFinitePresentation p] [Flat p] [DeJong.IsNodalCurve (b ≫ p)]
  [IsAlgClosed ((Spec (CommRingCat.of V)).residueField (IsLocalRing.closedPoint V))]

/-- **The components of the closed fibre of the blow-down** (blueprint `lem:sm-bdg-components`):
`b_{s₀}` maps the generic points of `X_{s₀}` other than `Z` bijectively onto the generic points of
`Y_{s₀}`, so `Y_{s₀}` has one irreducible component less than `X_{s₀}`. -/
theorem ncard_genericPoints_closedFibre (hnormal : IsNormalScheme Y)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hpure : ∀ W ∈ irreducibleComponents (p.fiber s₀), topologicalKrullDim W = 1)
    {Z : (b ≫ p).fiber s₀} (hZ : Z ∈ genericPoints _) (hc : ContractsExactly p b Z) :
    (genericPoints (p.fiber s₀)).ncard + 1 = (genericPoints ((b ≫ p).fiber s₀)).ncard := by
  set F := Curves.fiberMap b p s₀ with hF
  set x := F Z with hx
  have hxc : IsClosed ({x} : Set (p.fiber s₀)) := isClosed_contractedPoint p b hZ hc
  let U : (p.fiber s₀).Opens := ⟨{x}ᶜ, hxc.isOpen_compl⟩
  have hiso : IsIso (F ∣_ U) :=
    isIso_fiberMap_restrict_of_center b p s₀ {x}
      (fun y => center_inter_closedFibre p b hnormal hcurve hZ hc y) U (fun y => Iff.rfl)
  have hxg : x ∉ genericPoints (p.fiber s₀) := not_mem_genericPoints_of_isClosed hpure hxc
  -- generic points other than `Z` map into `U`
  have hFw : ∀ w ∈ genericPoints ((b ≫ p).fiber s₀), w ≠ Z → F w ∈ U := by
    intro w hw hwZ hFwx
    refine hwZ ((hc w hw).1 ((Set.subsingleton_singleton (a := x)).anti ?_))
    exact image_closure_subset_singleton _ F.continuous hxc hFwx
  have himage : F '' (genericPoints ((b ≫ p).fiber s₀) \ {Z}) = genericPoints (p.fiber s₀) := by
    ext y
    constructor
    · rintro ⟨w, ⟨hw, hwZ⟩, rfl⟩
      exact (mem_genericPoints_iff_of_isIso_morphismRestrict F U (hFw w hw hwZ)).1 hw
    · intro hy
      have hyU : y ∈ U := fun h => hxg ((Set.mem_singleton_iff.1 h) ▸ hy)
      obtain ⟨w, rfl⟩ := exists_eq_of_isIso_morphismRestrict F U hyU
      refine ⟨w, ⟨(mem_genericPoints_iff_of_isIso_morphismRestrict F U hyU).2 hy, ?_⟩, rfl⟩
      rintro rfl
      exact hyU rfl
  have hinj : Set.InjOn F (genericPoints ((b ≫ p).fiber s₀) \ {Z}) := by
    rintro w ⟨hw, hwZ⟩ w' ⟨hw', hwZ'⟩ h
    exact injOn_of_isIso_morphismRestrict F U (hFw w hw hwZ) (hFw w' hw' hwZ') h
  have := noetherianSpace_fiber (b ≫ p) s₀
  have hfin : (genericPoints ((b ≫ p).fiber s₀)).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  rw [← himage, hinj.ncard_image, Set.ncard_sdiff_singleton_add_one hZ hfin]


omit [DeJong.IsNodalCurve (b ≫ p)] in
/-- **The component count for a structure map `q = b ≫ p`** (`ncard_genericPoints_closedFibre`
in the form of `ContractsExactlyAt`), with the pure dimension of the closed fibre of `Y` derived
from `b` (`hasPureFiberDimension_of_isNodalCurve_comp`). -/
theorem ncard_genericPoints_closedFibre_of_eq (q : X ⟶ Spec (CommRingCat.of V)) (hq : b ≫ p = q)
    [DeJong.IsNodalCurve q] (hnormal : IsNormalScheme Y)
    (hcurve : ValuationRing.fiberTrdeg p (genericPoint Y) ≤ 1)
    (hη : Curves.IsEtaModification b p) {Z : q.fiber s₀} (hZ : Z ∈ genericPoints _)
    (hc : ContractsExactlyAt q b Z) :
    (genericPoints (p.fiber s₀)).ncard + 1 = (genericPoints (q.fiber s₀)).ncard := by
  subst hq
  have hbir := (inferInstance : IsModification b).birational
  have : IsDominant b := isDominant_of_birationalOver_id b hbir
  have : IsDominant p := isDominant_of_flat p
  have : Nonempty ((b ≫ p).fiber (genericPoint (Spec (CommRingCat.of V)))) :=
    nonempty_fiber_genericPoint_of_flat (b ≫ p)
  have hpure : ∀ W ∈ irreducibleComponents (p.fiber s₀), topologicalKrullDim W = 1 :=
    hasPureFiberDimension_of_isNodalCurve_comp p b
      (one_le_fiberDimension_genericPoint p b hη.isIso_fiberMap) s₀
  exact ncard_genericPoints_closedFibre p b hnormal hcurve hpure hZ
    ((contractsExactly_iff_contractsExactlyAt p b Z).2 hc)

end Count

end

end DeJongAlterations.StableModification.BlowDown
