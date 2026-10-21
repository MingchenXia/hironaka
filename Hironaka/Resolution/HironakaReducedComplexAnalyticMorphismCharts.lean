/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting

/-!
# Genuine local holomorphic chart form of abstract reduced analytic morphisms

Actual source and target charts are chosen from the original local-model
property. A true ambient open restriction and the native universal property
of an open immersion produce an intrinsic model map. Genuine local ambient
lifting then supplies a holomorphic coordinate representative with the whole
locally ringed square. No chart transition or ambient lift is supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaReducedComplexAnalyticMorphismCharts
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceIntrinsicLifting
variable {n m : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual target chart range containment constructs a WHOLE intrinsic factor after ambient restriction. -/
theorem exists_actual_model_chart_factor {C : Set M}
    {V : Opens (ComplexModel m)} {D : Set V} (Z : Over complexPoint)
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ Z.left)
    (hF : F ≫ Z.hom = subspacePointMap (n := n) C)
    (j : actualSubspaceLocallyRingedSpace (n := m) D ⟶ Z.left)
    [hj : LocallyRingedSpace.IsOpenImmersion j]
    (hjp : j ≫ Z.hom = subspacePointMap (n := m) D)
    (x : C) (hx : F.base x ∈ range j.base) :
    ∃ (T : Opens M) (_hxT : x.val ∈ T)
      (H : actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : T → M) ⁻¹' C) ⟶
        actualSubspaceLocallyRingedSpace (n := m) D),
      H ≫ subspacePointMap (n := m) D =
          subspacePointMap (n := n) ((Subtype.val : T → M) ⁻¹' C) ∧
      H ≫ j = actualOpenSubspaceMap (n := n) C T ≫ F := by
  let Q : Opens (TopCat.of C) :=
    ⟨F.base ⁻¹' range j.base,hj.base_open.isOpen_range.preimage F.base.hom.continuous⟩
  obtain ⟨T,hT,hTQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let O : Opens M := ⟨T,hT⟩
  have hxO : x.val ∈ O := by
    change x ∈ Subtype.val ⁻¹' T
    rw [hTQ]
    exact hx
  let R := actualOpenSubspaceMap (n := n) C O ≫ F
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y,rfl⟩
    have hy : (⟨y.val.val,y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val,y.property⟩ : C) ∈ (Q : Set C)
      rw [← hTQ]
      exact y.val.property
    exact hy
  let H := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : H ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  refine ⟨O,hxO,H,?_,hfac⟩
  calc
    _ = H ≫ (j ≫ Z.hom) := congrArg (fun k => H ≫ k) hjp.symm
    _ = R ≫ Z.hom := by rw [← Category.assoc,hfac]
    _ = _ := by
      rw [Category.assoc,hF]
      exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every arbitrary morphism in the intrinsic analytic category has genuine local holomorphic chart form. -/
theorem exists_actual_holomorphic_morphism_charts (A B : ReducedComplexAnalyticSpace)
    (F : A ⟶ B) (x : A.obj.left) :
    ∃ (n m : ℕ) (U : Opens (ComplexModel n)) (V : Opens (ComplexModel m))
      (C : Set U) (D : Set V),
      IsComplexAnalyticSubset (n := n) C ∧ IsComplexAnalyticSubset (n := m) D ∧
      ∃ (i : actualSubspaceLocallyRingedSpace (n := n) C ⟶ A.obj.left)
        (j : actualSubspaceLocallyRingedSpace (n := m) D ⟶ B.obj.left) (c : C),
        LocallyRingedSpace.IsOpenImmersion i ∧ LocallyRingedSpace.IsOpenImmersion j ∧
        i ≫ A.obj.hom = subspacePointMap (n := n) C ∧
        j ≫ B.obj.hom = subspacePointMap (n := m) D ∧ i.base c = x ∧
        ∃ (T : Opens U) (hcT : c.val ∈ T) (W : Opens T)
          (_hcW : (⟨c.val,hcT⟩ : T) ∈ W)
          (f : W → V) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
          (hCD : ∀ y ∈ (Subtype.val : W → T) ⁻¹' ((Subtype.val : T → U) ⁻¹' C), f y ∈ D),
          let k := actualOpenSubspaceMap (n := n) ((Subtype.val : T → U) ⁻¹' C) W ≫
            actualOpenSubspaceMap (n := n) C T ≫ i
          LocallyRingedSpace.IsOpenImmersion k ∧ x ∈ range k.base ∧
            actualSubspaceMap hf hCD ≫ j = k ≫ F.hom.left := by
  obtain ⟨n,U,C,hC,i,hi,hip,c,hcx⟩ := A.property.2.2 x
  obtain ⟨m,V,D,hD,j,hj,hjp,d,hd⟩ := B.property.2.2 (F.hom.left.base x)
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  have hFi : (i ≫ F.hom.left) ≫ B.obj.hom = subspacePointMap (n := n) C := by
    rw [Category.assoc,Over.w F.hom]
    exact hip
  have hxj : (i ≫ F.hom.left).base c ∈ range j.base := by
    change F.hom.left.base (i.base c) ∈ range j.base
    rw [hcx]
    exact ⟨d,hd⟩
  obtain ⟨T,hcT,H,hHp,hHfac⟩ :=
    exists_actual_model_chart_factor B.obj (i ≫ F.hom.left) hFi j hjp c hxj
  let cT : ((Subtype.val : T → U) ⁻¹' C) := ⟨⟨c.val,hcT⟩,c.property⟩
  obtain ⟨W,hcW,f,hf,hCD,hfH⟩ := exists_actualSubspaceMap_local_holomorphic_lift H hHp cT
  refine ⟨n,m,U,V,C,D,hC,hD,i,j,c,hi,hj,hip,hjp,hcx,T,hcT,W,hcW,f,hf,hCD,?_,?_,?_⟩
  · infer_instance
  · refine ⟨⟨⟨⟨c.val,hcT⟩,hcW⟩,c.property⟩,?_⟩
    exact hcx
  · calc
      _ = (actualOpenSubspaceMap (n := n) ((Subtype.val : T → U) ⁻¹' C) W ≫ H) ≫ j :=
        congrArg (fun k => k ≫ j) hfH
      _ = actualOpenSubspaceMap (n := n) ((Subtype.val : T → U) ⁻¹' C) W ≫ (H ≫ j) :=
        Category.assoc _ _ _
      _ = actualOpenSubspaceMap (n := n) ((Subtype.val : T → U) ⁻¹' C) W ≫
          (actualOpenSubspaceMap (n := n) C T ≫ (i ≫ F.hom.left)) :=
        congrArg (fun k => actualOpenSubspaceMap (n := n) ((Subtype.val : T → U) ⁻¹' C) W ≫ k) hHfac
      _ = _ := by simp only [Category.assoc]

end
end Hironaka.HironakaReducedComplexAnalyticMorphismCharts
