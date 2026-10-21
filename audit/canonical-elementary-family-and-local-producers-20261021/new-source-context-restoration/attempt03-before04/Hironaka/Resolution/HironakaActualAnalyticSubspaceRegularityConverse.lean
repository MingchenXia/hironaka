/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHolomorphicStalkSurjection
import Hironaka.Resolution.HironakaActualAnalyticSubspaceManifoldCharts
import Hironaka.Analytic.ConstantRankSubmanifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.RegularPointDimension

/-!
# Actual native manifold charts imply original ambient regularity

The derivative and actual image flattening are internally produced from
actual native stalk surjectivity. A genuine native model chart supplies
that surjectivity and, independently, the real ambient neighbourhood where
the same image equals the original subset. No rank or flattening certificate
is input at the original intrinsic-chart endpoint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceRegularityConverse
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualHolomorphicStalkSurjection
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts
  HironakaActualAnalyticSubspaceIntrinsicLifting
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk ConstantRankSubmanifold
variable {d n : ℕ} {O : Opens (ComplexModel d)} {V : Opens (ComplexModel n)}
  {f : O → V}

/-- Actual native stalk surjectivity internally yields true constant-rank image flattening. -/
theorem exists_regular_local_image_of_stalk_surjective
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f) (x : O)
    (hsurj : Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x)) :
    ∃ A : Set (ComplexModel d), IsOpen A ∧ x.val ∈ A ∧ A ⊆ O ∧
      ∀ z ∈ (actualOpenVectorExtension O (fun y : O => (f y).val)) '' A,
        RegularAtDim (n := n) ((actualOpenVectorExtension O (fun y : O => (f y).val)) '' A) z d := by
  let F := actualOpenVectorExtension O (fun y : O => (f y).val)
  have hfVec : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ (fun y : O => (f y).val) :=
    (contMDiff_subtype_val (U := V)).comp hf
  have hFd : DifferentiableOn ℂ F (O : Set (ComplexModel d)) := by
    intro y hy
    exact (mdifferentiableAt_iff_differentiableAt.mp
      ((actualOpenVectorExtension_contMDiffAt O _ ⟨y,hy⟩ hfVec.contMDiffAt).mdifferentiableAt (by simp))).differentiableWithinAt
  have hFs : ContDiffOn ℂ ∞ F (O : Set (ComplexModel d)) :=
    contDiffOn_of_differentiableOn_complex hFd O.isOpen
  let U : Set (ComplexModel d) := (O : Set (ComplexModel d)) ∩
    (fderiv ℂ F) ⁻¹' {L : ComplexModel d →L[ℂ] ComplexModel n | Function.Injective L}
  have hU : IsOpen U :=
    (hFs.continuousOn_fderiv_of_isOpen O.isOpen (by simp)).isOpen_inter_preimage
      O.isOpen ContinuousLinearMap.isOpen_injective
  have hxU : x.val ∈ U := ⟨x.property,injective_fderiv_of_native_stalk_surjective hf x hsurj⟩
  have hr : ∀ y ∈ U, Module.finrank ℂ (LinearMap.range
      ((fderiv ℂ F y) : ComplexModel d →ₗ[ℂ] ComplexModel n)) = d := by
    intro y hy
    rw [LinearMap.finrank_range_of_inj hy.2,finrank_euclideanSpace_fin]
  obtain ⟨A,W,g,hA,hxA,hAU,-,-,-,hreg⟩ :=
    exists_image_eq_graph hU (hFd.mono inter_subset_left) hr hxU
  exact ⟨A,hA,hxA,fun y hy => (hAU hy).1,hreg⟩

private theorem native_stalk_surjective_of_model_open_immersion
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f)
    {C : Set V} (hC : ∀ y ∈ (univ : Set O),f y ∈ C)
    [hopen : LocallyRingedSpace.IsOpenImmersion (actualSubspaceMap hf hC)] (x : O) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x) := by
  let u : (univ : Set O) := ⟨x,mem_univ _⟩
  let J := actualSubspaceMap hf hC
  let E := actualSubspaceUnivIso (n := d) (M := O)
  have hEinj : Function.Injective ((actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u) := by
    change Function.Injective (E.hom.stalkMap u)
    exact ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).1
  have hJsurj : Function.Surjective (J.stalkMap u) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)).2
  intro a
  obtain ⟨b,hb⟩ := hJsurj ((actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u a)
  obtain ⟨r,hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective C (J.base u) b
  refine ⟨r,hEinj ?_⟩
  have he := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hC u) r
  change J.stalkMap u ((actualSubspaceInclusion (n := n) C).stalkMap (J.base u) r) =
    (actualSubspaceInclusion (n := d) (univ : Set O)).stalkMap u
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x r) at he
  have hr' : (actualSubspaceInclusion (n := n) C).stalkMap (J.base u) r = b := hr
  exact he.symm.trans ((congrArg (J.stalkMap u) hr').trans hb)

/-- An ACTUAL holomorphic whole-model open immersion forces original regularity of the SAME subset. -/
theorem regularAtDim_of_holomorphic_model_open_immersion
    (hf : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ f)
    {C : Set V} (hC : ∀ y ∈ (univ : Set O),f y ∈ C)
    [hopen : LocallyRingedSpace.IsOpenImmersion (actualSubspaceMap hf hC)] (x : O) :
    RegularAtDim (n := n) C (f x) d := by
  let F := actualOpenVectorExtension O (fun y : O => (f y).val)
  obtain ⟨A,hA,hxA,hAO,hreg⟩ := exists_regular_local_image_of_stalk_surjective hf x
    (native_stalk_surjective_of_model_open_immersion hf hC x)
  let J := actualSubspaceMap hf hC
  let Q : Set (univ : Set O) := fun u => u.val.val ∈ A
  have hQ : IsOpen Q := hA.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hJQ : IsOpen (J.base '' Q) := hopen.base_open.isOpenMap _ hQ
  obtain ⟨W,hW,hWQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hJQ
  let B : Set (ComplexModel n) := (Subtype.val : V → ComplexModel n) '' C
  let T : Set (ComplexModel n) := (Subtype.val : V → ComplexModel n) '' W
  have hT : IsOpen T := V.isOpen.isOpenMap_subtype_val _ hW
  have himage : F '' A = B ∩ T := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      let v : O := ⟨y,hAO hy⟩
      let u : (univ : Set O) := ⟨v,mem_univ _⟩
      have hJu : J.base u ∈ J.base '' Q := ⟨u,hy,rfl⟩
      have hvW : f v ∈ W := by
        change J.base u ∈ (Subtype.val : C → V) ⁻¹' W
        rw [hWQ]
        exact hJu
      have hFy : F y = (f v).val := actualOpenVectorExtension_apply O _ v
      rw [hFy]
      exact ⟨⟨f v,hC v (mem_univ _),rfl⟩,⟨f v,hvW,rfl⟩⟩
    · rintro ⟨⟨v,hvC,hvz⟩,⟨w,hwW,hwz⟩⟩
      have hvw : v = w := Subtype.ext (hvz.trans hwz.symm)
      have hvW : v ∈ W := hvw ▸ hwW
      have hcQ : (⟨v,hvC⟩ : C) ∈ J.base '' Q := by
        rw [← hWQ]
        exact hvW
      obtain ⟨u,hu,heu⟩ := hcQ
      refine ⟨u.val.val,hu,?_⟩
      calc
        F u.val.val = (f u.val).val := actualOpenVectorExtension_apply O _ u.val
        _ = v.val := congrArg (fun c : C => c.val.val) heu
        _ = z := hvz
  have hfx : F x.val = (f x).val := actualOpenVectorExtension_apply O _ x
  have hximage : (f x).val ∈ F '' A := ⟨x.val,hxA,hfx⟩
  have hxT : (f x).val ∈ T := (himage ▸ hximage).2
  have hlocal : (F '' A) ∩ T = B ∩ T := by rw [himage,inter_assoc,inter_self]
  have hB : RegularAtDim (n := n) B (f x).val d :=
    RegularPointDimension.regularAtDim_of_inter_eq hT hxT hlocal (hreg _ hximage)
  exact AnalyticSubsetOpens.regularAtDim_image_val_iff.mp hB

private abbrev nestedOpenDomain (T : Opens O) : Opens (ComplexModel d) :=
  ⟨(Subtype.val : O → ComplexModel d) '' (T : Set O),O.isOpen.isOpenMap_subtype_val _ T.isOpen⟩

private def nestedOpenDiffeomorph (T : Opens O) :
    T ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ nestedOpenDomain T where
  toFun y := ⟨y.val.val,⟨y.val,y.property,rfl⟩⟩
  invFun z := ⟨Classical.choose z.property,(Classical.choose_spec z.property).1⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec (show y.val.val ∈ (nestedOpenDomain T : Set (ComplexModel d)) from
      ⟨y.val,y.property,rfl⟩)).2
  right_inv z := Subtype.ext (Classical.choose_spec z.property).2
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (nestedOpenDomain T) _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞ (fun y : T => y.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff T _).mp
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    have he : (fun z : nestedOpenDomain T => (Classical.choose z.property).val) =
        (Subtype.val : nestedOpenDomain T → ComplexModel d) := by
      funext z
      exact (Classical.choose_spec z.property).2
    change ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel d) ∞
      (fun z : nestedOpenDomain T => (Classical.choose z.property).val)
    rw [he]
    exact contMDiff_subtype_val

/-- ANY original over-point native manifold chart forces original regularity, without a rank or ambient-lift input. -/
theorem regularAtDim_of_native_manifold_chart {C : Set V}
    (j : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) O ⟶
      actualSubspaceLocallyRingedSpace (n := n) C)
    [hj : LocallyRingedSpace.IsOpenImmersion j]
    (hjp : j ≫ subspacePointMap (n := n) C = ambientPointMap d O) (x : O) :
    RegularAtDim (n := n) C (j.base x).val d := by
  let E := actualSubspaceUnivIso (n := d) (M := O)
  let J := E.hom ≫ j
  have hJp : J ≫ subspacePointMap (n := n) C = subspacePointMap (n := d) (univ : Set O) := by
    change (E.hom ≫ j) ≫ subspacePointMap (n := n) C = _
    rw [Category.assoc,hjp]
    rfl
  obtain ⟨T,hxT,g,hg,hgC,hgJ⟩ := exists_actualSubspaceMap_local_holomorphic_lift J hJp
    (⟨x,mem_univ _⟩ : (univ : Set O))
  have hgC' : ∀ y ∈ (univ : Set T),g y ∈ C := fun y _ => hgC y (mem_univ _)
  let K := actualSubspaceMap hg hgC'
  have hK : K = actualOpenSubspaceMap (n := d) (univ : Set O) T ≫ J := hgJ
  let : LocallyRingedSpace.IsOpenImmersion K := by
    rw [hK]
    infer_instance
  let S := nestedOpenDomain T
  let e := nestedOpenDiffeomorph T
  let g' : S → V := g ∘ e.symm
  have hg' : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ g' := hg.comp e.symm.contMDiff
  have hgC'' : ∀ y ∈ (univ : Set S),g' y ∈ C := fun y _ => hgC' (e.symm y) (mem_univ _)
  let B := actualSubspaceBiholomorphicIso e.symm (univ : Set S) (univ : Set T)
    (fun _ => iff_of_true (mem_univ _) (mem_univ _))
  have hcomp : actualSubspaceMap hg' hgC'' = B.hom ≫ K :=
    actualSubspaceMap_comp e.symm.contMDiff hg (fun _ _ => mem_univ _) hgC'
  let : LocallyRingedSpace.IsOpenImmersion (actualSubspaceMap hg' hgC'') := by
    rw [hcomp]
    infer_instance
  have hreg : RegularAtDim (n := n) C (g ⟨x,hxT⟩) d := by
    have hh := regularAtDim_of_holomorphic_model_open_immersion (f := g') hg' hgC'' (e ⟨x,hxT⟩)
    simpa only [g',Function.comp_apply,e.symm_apply_apply] using hh
  have hbase := congrArg (fun a => (a.base (⟨⟨x,hxT⟩,mem_univ _⟩ : (univ : Set T))).val) hK
  change g ⟨x,hxT⟩ = (j.base x).val at hbase
  rwa [hbase] at hreg

end
end Hironaka.HironakaActualAnalyticSubspaceRegularityConverse
