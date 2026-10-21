/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaActualFlatCoordinateIntrinsicHS
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Hironaka.Resolution.HironakaRelativeNormalIdeal

/-!
# Genuine native manifold charts at original regular subspace points

The whole-manifold quotient model is identified with the actual native
locally ringed manifold. Original regularity, the SAME true flattening and
actual projection/insertion then construct native manifold open charts,
without a supplied quotient-sheaf chart or stalk-isomorphism certificate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceManifoldCharts
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualFlatCoordinateIntrinsicHS HironakaRelativeNormalIdeal
  BlowupFlatCoordinates
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem whole_vanishing_univ_eq_bot (x : M) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (univ : Set M)) x = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro r hr
  change r = 0
  have him : r ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) (univ : Set M)) x := by
    rw [actualCentreIdealSectionGermImage_eq_whole]
    exact hr
  obtain ⟨U,hx,s,hs⟩ := him
  have hs0 : s.val = 0 := by
    apply Subtype.ext
    funext y
    exact (actualSectionIdeal_vanishing_iff (univ : Set M) U s.val).mp s.property
      y.val y.property (mem_univ _)
  calc
    _ = (actualComplexStructureSheaf (n := n) M).presheaf.germ U x hx s.val := hs.symm
    _ = 0 := by rw [hs0]; exact map_zero ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x hx).hom

private instance univInclusionStalkIso (x : (univ : Set M)) :
    IsIso ((actualSubspaceInclusion (n := n) (univ : Set M)).stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [actualSubspaceInclusion_stalk_kernel,whole_vanishing_univ_eq_bot]
  · exact actualSubspaceInclusionRingedHom_stalk_surjective (univ : Set M) x

private instance univInclusionOpen :
    LocallyRingedSpace.IsOpenImmersion (actualSubspaceInclusion (n := n) (univ : Set M)) :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ isOpen_univ.isOpenEmbedding_subtypeVal

/-- The ACTUAL whole-manifold quotient model is internally the genuine native manifold LRS. -/
def actualSubspaceUnivIso :
    actualSubspaceLocallyRingedSpace (n := n) (univ : Set M) ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M := by
  let I := actualSubspaceInclusion (n := n) (univ : Set M)
  have hr : range (LocallyRingedSpace.id (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M)).base ⊆ range I.base := by
    intro y _
    exact ⟨⟨y,mem_univ _⟩,rfl⟩
  let j := LocallyRingedSpace.IsOpenImmersion.lift I (𝟙 _) hr
  have hji : j ≫ I = 𝟙 _ := LocallyRingedSpace.IsOpenImmersion.lift_fac I (𝟙 _) hr
  refine ⟨I,j,?_,hji⟩
  apply (cancel_mono I).mp
  rw [Category.assoc,hji,Category.comp_id,Category.id_comp]

/-- The genuine forward isomorphism is the SAME actual original inclusion. -/
theorem actualSubspaceUnivIso_hom :
    (actualSubspaceUnivIso (n := n) (M := M)).hom =
      actualSubspaceInclusion (n := n) (univ : Set M) := rfl

/-- The constructed native inverse retains the original complex structure. -/
theorem actualSubspaceUnivIso_inv_point :
    (actualSubspaceUnivIso (n := n) (M := M)).inv ≫ subspacePointMap (n := n) (univ : Set M) =
      ambientPointMap n M := by
  change (actualSubspaceUnivIso (n := n) (M := M)).inv ≫
    ((actualSubspaceUnivIso (n := n) (M := M)).hom ≫ ambientPointMap n M) = _
  rw [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

/-- The actual base open cut out by inserting zero normal coordinates. -/
def planeBaseDomain (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) : Opens (ComplexModel d) :=
  ⟨(tangentInclusion d t) ⁻¹' Ω,Ω.isOpen.preimage (tangentInclusion d t).continuous⟩

/-- A genuine smaller actual open whose base-plane projection remains in the original target. -/
def planeStableDomain (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) : Opens (ComplexModel (d+t)) :=
  Ω ⊓ ⟨(tangentProjection d t) ⁻¹' planeBaseDomain d t Ω,
    (planeBaseDomain d t Ω).isOpen.preimage (tangentProjection d t).continuous⟩

/-- The whole actual coordinate-plane subset on that genuine projection-stable open. -/
def planeModelSubset (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) : Set (planeStableDomain d t Ω) :=
  (Subtype.val : planeStableDomain d t Ω → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d

/-- Literal actual projection into the true base open. -/
def planeProjection (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    planeStableDomain d t Ω → planeBaseDomain d t Ω :=
  fun z => ⟨tangentProjection d t z.val,z.property.2⟩

/-- Literal actual zero-normal insertion into the true stable open. -/
def planeInsertion (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    planeBaseDomain d t Ω → planeStableDomain d t Ω :=
  fun v => ⟨tangentInclusion d t v.val,⟨v.property,by
    change tangentProjection d t (tangentInclusion d t v.val) ∈ planeBaseDomain d t Ω
    rw [tangentProjection_tangentInclusion]
    exact v.property⟩⟩

private theorem planeProjection_smooth (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel d) ∞ (planeProjection d t Ω) :=
  (ContMDiff.subtypeVal_comp_iff (planeBaseDomain d t Ω) (planeProjection d t Ω)).mp
    ((tangentProjection d t).contMDiff.comp contMDiff_subtype_val)

private theorem planeInsertion_smooth (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ (planeInsertion d t Ω) :=
  (ContMDiff.subtypeVal_comp_iff (planeStableDomain d t Ω) (planeInsertion d t Ω)).mp
    ((tangentInclusion d t).contMDiff.comp contMDiff_subtype_val)

private theorem planeInsertion_mem (d t : ℕ) (Ω : Opens (ComplexModel (d+t)))
    (v : planeBaseDomain d t Ω) : planeInsertion d t Ω v ∈ planeModelSubset d t Ω :=
  tangentInclusion_mem_plane d t v.val

private def actualCoordinatePlaneModelIso (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    actualSubspaceLocallyRingedSpace (n := d+t) (planeModelSubset d t Ω) ≅
      actualSubspaceLocallyRingedSpace (n := d) (univ : Set (planeBaseDomain d t Ω)) :=
  actualSubspaceMutualRestrictionIso (planeProjection_smooth d t Ω) (planeInsertion_smooth d t Ω)
    (fun _ _ => mem_univ _) (fun v _ => planeInsertion_mem d t Ω v)
    (fun _z hz => Subtype.ext (tangentInclusion_projection_eq_of_mem_plane d t hz))
    (fun v _ => Subtype.ext (tangentProjection_tangentInclusion d t v.val))

/-- Genuine different-dimensional projection/insertion produces the native manifold model, with inverse only ON the plane. -/
def actualCoordinatePlaneManifoldIso (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    actualSubspaceLocallyRingedSpace (n := d+t) (planeModelSubset d t Ω) ≅
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) (planeBaseDomain d t Ω) :=
  (actualCoordinatePlaneModelIso d t Ω).trans
    (actualSubspaceUnivIso (n := d) (M := planeBaseDomain d t Ω))

/-- The constructed actual native plane-model chart retains the original complex structural triangle. -/
theorem actualCoordinatePlaneManifoldIso_inv_point (d t : ℕ) (Ω : Opens (ComplexModel (d+t))) :
    (actualCoordinatePlaneManifoldIso d t Ω).inv ≫ subspacePointMap (n := d+t) (planeModelSubset d t Ω) =
      ambientPointMap d (planeBaseDomain d t Ω) := by
  change (actualSubspaceUnivIso (n := d) (M := planeBaseDomain d t Ω)).inv ≫
    ((actualCoordinatePlaneModelIso d t Ω).inv ≫ subspacePointMap (n := d+t) (planeModelSubset d t Ω)) = _
  have hp : (actualCoordinatePlaneModelIso d t Ω).inv ≫
      subspacePointMap (n := d+t) (planeModelSubset d t Ω) =
      subspacePointMap (n := d) (univ : Set (planeBaseDomain d t Ω)) :=
    actualSubspaceMap_point (planeInsertion_smooth d t Ω) (fun v _ => planeInsertion_mem d t Ω v)
  rw [hp,actualSubspaceUnivIso_inv_point]

section Regular
variable {d t : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]

set_option backward.isDefEq.respectTransparency.types false in
/-- Original geometric regularity internally supplies a genuine native manifold open chart of the ACTUAL model. -/
theorem exists_actual_regular_subspace_manifold_chart (C : Set X) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d) :
    ∃ (V : Opens (ComplexModel d))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) V ⟶
        actualSubspaceLocallyRingedSpace (n := d+t) C),
      LocallyRingedSpace.IsOpenImmersion i ∧
      i ≫ subspacePointMap (n := d+t) C = ambientPointMap d V ∧
      (⟨x,hreg.2.1⟩ : C) ∈ range i.base := by
  obtain ⟨_hd,hxC,Φ,hsrc,h0,hflat⟩ := hreg
  let D₀ : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let Ω : Opens (ComplexModel (d+t)) := ⟨Φ.target,Φ.isOpen_target⟩
  let E := actualFlatCoordinateDiffeomorph Φ hsrc
  let R := planeStableDomain d t Ω
  let V := planeBaseDomain d t Ω
  let O : Opens D₀ := ⟨(fun z : D₀ => (E z).val) ⁻¹' R,
    R.isOpen.preimage (continuous_subtype_val.comp E.contMDiff.continuous)⟩
  let C₀ : Set D₀ := (Subtype.val : D₀ → X) ⁻¹' C
  let C₁ : Set O := (Subtype.val : O → D₀) ⁻¹' C₀
  let f : O → R := fun z => ⟨(E z.val).val,z.property⟩
  let g : R → O := fun r => ⟨E.symm ⟨r.val,r.property.1⟩,by
    change (E (E.symm ⟨r.val,r.property.1⟩)).val ∈ R
    rw [E.apply_symm_apply]
    exact r.property⟩
  have hEf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (fun z : O => E z.val) := E.contMDiff.comp contMDiff_subtype_val
  have hfAmbient : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (fun z : O => (E z.val).val) := (contMDiff_subtype_val (U := Ω)).comp hEf
  have hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff R f).mp hfAmbient
  have hg : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff O g).mp
      (E.symm.contMDiff.comp (contMDiff_inclusion (show R ≤ Ω from inf_le_left)))
  have hCD : ∀ z ∈ C₁, f z ∈ planeModelSubset d t Ω := by
    intro z hz
    exact (hflat z.val.property.1 z.val.property.2).mp hz
  have hDC : ∀ r ∈ planeModelSubset d t Ω, g r ∈ C₁ := by
    intro r hr
    apply (hflat (E.symm ⟨r.val,r.property.1⟩).property.1
      (E.symm ⟨r.val,r.property.1⟩).property.2).mpr
    change (E (E.symm (⟨r.val,r.property.1⟩ : Ω))).val ∈ complexCoordinatePlane (d+t) d
    have he := congrArg Subtype.val (E.apply_symm_apply (⟨r.val,r.property.1⟩ : Ω))
    exact (congrArg (fun z => z ∈ complexCoordinatePlane (d+t) d) he).mpr hr
  have hgf : ∀ z ∈ C₁,g (f z) = z := by
    intro z _
    apply Subtype.ext
    exact E.symm_apply_apply z.val
  have hfg : ∀ r ∈ planeModelSubset d t Ω,f (g r) = r := by
    intro r _
    apply Subtype.ext
    change (E (E.symm (⟨r.val,r.property.1⟩ : Ω))).val = r.val
    exact congrArg Subtype.val (E.apply_symm_apply (⟨r.val,r.property.1⟩ : Ω))
  let A := actualSubspaceMutualRestrictionIso hf hg hCD hDC hgf hfg
  let L := A.trans (actualCoordinatePlaneManifoldIso d t Ω)
  let r := actualOpenSubspaceMap (n := d+t) C₀ O ≫ actualOpenSubspaceMap (n := d+t) C D₀
  let i := L.inv ≫ r
  have hA : A.inv ≫ subspacePointMap (n := d+t) C₁ =
      subspacePointMap (n := d+t) (planeModelSubset d t Ω) := actualSubspaceMap_point hg hDC
  have hL : L.inv ≫ subspacePointMap (n := d+t) C₁ = ambientPointMap d V := by
    change (actualCoordinatePlaneManifoldIso d t Ω).inv ≫
      (A.inv ≫ subspacePointMap (n := d+t) C₁) = _
    rw [hA,actualCoordinatePlaneManifoldIso_inv_point]
  have hr₀ : actualOpenSubspaceMap (n := d+t) C D₀ ≫ subspacePointMap (n := d+t) C =
      subspacePointMap (n := d+t) C₀ :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  have hr₁ : actualOpenSubspaceMap (n := d+t) C₀ O ≫ subspacePointMap (n := d+t) C₀ =
      subspacePointMap (n := d+t) C₁ :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  have hpoint : i ≫ subspacePointMap (n := d+t) C = ambientPointMap d V := by
    change (L.inv ≫ (actualOpenSubspaceMap (n := d+t) C₀ O ≫
      actualOpenSubspaceMap (n := d+t) C D₀)) ≫ subspacePointMap (n := d+t) C = _
    rw [Category.assoc,Category.assoc,hr₀,hr₁]
    exact hL
  have hxD : x ∈ D₀ := mem_flatDomain_self Φ
  have hxE : (E ⟨x,hxD⟩).val = 0 := h0
  have h0Ω : (0 : ComplexModel (d+t)) ∈ Ω := by
    rw [← hxE]
    exact (E ⟨x,hxD⟩).property
  have h0V : (0 : ComplexModel d) ∈ V := by
    change tangentInclusion d t 0 ∈ Ω
    rw [map_zero]
    exact h0Ω
  have h0R : (0 : ComplexModel (d+t)) ∈ R := ⟨h0Ω,by
    change tangentProjection d t 0 ∈ V
    rw [map_zero]
    exact h0V⟩
  have hxO : (⟨x,hxD⟩ : D₀) ∈ O := by
    change (E ⟨x,hxD⟩).val ∈ R
    rw [hxE]
    exact h0R
  let c : C₁ := ⟨⟨⟨x,hxD⟩,hxO⟩,hxC⟩
  let v : V := L.hom.base c
  have hv : L.inv.base v = c := by
    have hh := congrArg (fun k => k.base c) L.hom_inv_id
    change L.inv.base (L.hom.base c) = c at hh
    exact hh
  refine ⟨V,i,inferInstance,hpoint,v,?_⟩
  change r.base (L.inv.base v) = ⟨x,hxC⟩
  rw [hv]
  rfl

end Regular

end
end Hironaka.HironakaActualAnalyticSubspaceManifoldCharts
