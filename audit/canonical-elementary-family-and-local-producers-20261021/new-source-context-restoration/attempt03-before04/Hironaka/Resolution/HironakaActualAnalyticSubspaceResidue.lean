/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermMkSubPrimeOriginalExact
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces

/-!
# Actual complex residue fields and scalar-compatible point values

Every evaluation and constant map is constructed on the actual original
colimit stalk via its whole original quotient. Complex-point compatibility
of any genuine locally ringed map then derives point-value naturality,
without an ambient extension or stalk scalar certificate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceResidue
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaHilbertSamuelTangentValue
  HironakaActualWholeStalkHolomorphicPullback

private def pointGermEquiv : HolGerm (ComplexModel 0) ≃+* ℂ :=
  RingEquiv.ofBijective HolGerm.eval ⟨by
    intro a b hab
    induction a using HolGerm.induction_on with
    | h f hf =>
      induction b using HolGerm.induction_on with
      | h g hg =>
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Filter.Eventually.of_forall fun z => by
          simpa only [HolGerm.eval_mk,Subsingleton.elim z (0 : ComplexModel 0)] using hab,
    fun c => ⟨HolGerm.constHom c,HolGerm.eval_constHom c⟩⟩

/-- The actual complex-point colimit stalk is internally the literal complex field. -/
def actualComplexPointStalkEquiv : actualComplexStructureStalk (n := 0) (0 : ComplexModel 0) ≃+* ℂ :=
  (actualStalkChartEquiv (n := 0) (0 : ComplexModel 0)).trans pointGermEquiv

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

local instance actualStalkLocal (C : Set M) (x : C) :
    IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  actualSubspaceStalk_isLocalRing (n := n) C x

private def chartQuotientEval (C : Set M) (x : C) :
    HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal (vanishingIdeal (n := n) C)
      x.val x.val (mem_chart_source _ x.val) →+* ℂ :=
  Ideal.Quotient.lift _ HolGerm.eval (fun r hr =>
    (HolGerm.mem_maximalIdeal_iff r).mp (whole_vanishing_stalk_le_maximalIdeal (n := n) x.property hr))

/-- The genuine point evaluation of the entire actual quotient-subspace stalk. -/
def actualSubspaceStalkEval (C : Set M) (x : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier →+* ℂ :=
  (chartQuotientEval (n := n) C x).comp (actualSubspaceStalkChartEquiv (n := n) C x).toRingHom

/-- Actual original complex constants are transported through the entire quotient. -/
def actualSubspaceStalkConst (C : Set M) (x : C) :
    ℂ →+* ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  (actualSubspaceStalkChartEquiv (n := n) C x).symm.toRingHom.comp
    ((Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := n) C)
      x.val x.val (mem_chart_source _ x.val))).comp HolGerm.constHom)

/-- Genuine original constants split the actual point evaluation. -/
theorem actualSubspaceStalkEval_const (C : Set M) (x : C) (c : ℂ) :
    actualSubspaceStalkEval (n := n) C x (actualSubspaceStalkConst (n := n) C x c)=c := by
  simp [actualSubspaceStalkEval,actualSubspaceStalkConst,chartQuotientEval]

/-- The actual point residue evaluation is onto the original complex field. -/
theorem actualSubspaceStalkEval_surjective (C : Set M) (x : C) :
    Function.Surjective (actualSubspaceStalkEval (n := n) C x) :=
  fun c => ⟨actualSubspaceStalkConst (n := n) C x c,actualSubspaceStalkEval_const C x c⟩

/-- Its ENTIRE actual kernel is precisely the genuine local-ring maximal ideal. -/
theorem actualSubspaceStalkEval_ker (C : Set M) (x : C) :
    RingHom.ker (actualSubspaceStalkEval (n := n) C x)=
      IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
  IsLocalRing.ker_eq_maximalIdeal _ (actualSubspaceStalkEval_surjective C x)

/-- The genuine actual residue field is internally the original complex field. -/
def actualSubspaceResidueFieldEquiv (C : Set M) (x : C) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ⧸
        IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier ≃+* ℂ :=
  (Ideal.quotEquivOfEq (actualSubspaceStalkEval_ker (n := n) C x).symm).trans
    ((actualSubspaceStalkEval (n := n) C x).quotientKerEquivOfSurjective
      (actualSubspaceStalkEval_surjective C x))

/-- Every actual original residue numerator retains the constructed point evaluation. -/
theorem actualSubspaceResidueFieldEquiv_mk (C : Set M) (x : C)
    (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier) :
    actualSubspaceResidueFieldEquiv (n := n) C x (Ideal.Quotient.mk _ r)=
      actualSubspaceStalkEval (n := n) C x r := rfl

private theorem inclusion_stalk_chart (C : Set M) (x : C)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkChartEquiv (n := n) C x ((actualSubspaceInclusion (n := n) C).stalkMap x r) =
      Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val r) := by
  change (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val).symm)
    (actualSubspaceStalkWholeEquiv (n := n) C x ((actualSubspaceInclusion (n := n) C).stalkMap x r)) = _
  rw [actualSubspaceInclusion_stalk]
  rfl

/-- Every whole original ambient numerator retains its literal original point value. -/
theorem actualSubspaceStalkEval_inclusion (C : Set M) (x : C)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkEval (n := n) C x ((actualSubspaceInclusion (n := n) C).stalkMap x r)=
      HolGerm.eval (actualStalkChartEquiv (n := n) x.val r) := by
  exact congrArg (chartQuotientEval (n := n) C x) (inclusion_stalk_chart C x r)

private theorem point_germ_pullback (x : M) (r : HolGerm (ComplexModel 0)) :
    actualHolomorphicGermPullback (n := 0) (m := n)
        (f := fun _ : M => (0 : ComplexModel 0)) contMDiff_const x r =
      HolGerm.constHom (HolGerm.eval r) := by
  induction r using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk,HolGerm.constHom_apply,HolGerm.eval_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Filter.Eventually.of_forall fun z => congrArg F (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The ACTUAL complex structural map supplies the original scalar constants on every entire stalk. -/
theorem actualSubspacePointMap_stalk_const (C : Set M) (x : C) (c : ℂ) :
    (subspacePointMap (n := n) C).stalkMap x (actualComplexPointStalkEquiv.symm c)=
      actualSubspaceStalkConst (n := n) C x c := by
  apply (actualSubspaceStalkChartEquiv (n := n) C x).injective
  change actualSubspaceStalkChartEquiv (n := n) C x
    (((actualSubspaceInclusion (n := n) C ≫ ambientPointMap n M).stalkMap x)
      (actualComplexPointStalkEquiv.symm c)) = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change actualSubspaceStalkChartEquiv (n := n) C x
      ((actualSubspaceInclusion (n := n) C).stalkMap x
        ((ambientPointMap n M).stalkMap x.val (actualComplexPointStalkEquiv.symm c))) = _
  rw [inclusion_stalk_chart]
  change Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val
      ((ChartedSpace.locallyRingedSpaceMap (fun _ : M => (0 : ComplexModel 0)) contMDiff_const).stalkMap
        x.val (actualComplexPointStalkEquiv.symm c))) = _
  rw [actualNativeStalk_chart_pullback,point_germ_pullback]
  have hc : HolGerm.eval (actualStalkChartEquiv (n := 0) (0 : ComplexModel 0)
      (actualComplexPointStalkEquiv.symm c))=c := actualComplexPointStalkEquiv.apply_symm_apply c
  rw [hc]
  exact ((actualSubspaceStalkChartEquiv (n := n) C x).apply_symm_apply _).symm

private theorem subspacePointMap_base_apply (C : Set M) (x : C) :
    (subspacePointMap (n := n) C).base x=(0 : ComplexModel 0) := rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem point_compatible_stalk_const {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hpoint : F ≫ subspacePointMap (n := m) D=subspacePointMap (n := n) C)
    (x : C) (c : ℂ) :
    F.stalkMap x (actualSubspaceStalkConst (n := m) D (F.base x) c)=
      actualSubspaceStalkConst (n := n) C x c := by
  have h := LocallyRingedSpace.stalkMap_congr_hom
    (F ≫ subspacePointMap (n := m) D) (subspacePointMap (n := n) C) hpoint x
  have hs : (subspacePointMap (n := m) D).stalkMap (F.base x) ≫ F.stalkMap x =
      (subspacePointMap (n := n) C).stalkMap x := by
    calc
      _ = (F ≫ subspacePointMap (n := m) D).stalkMap x :=
        (LocallyRingedSpace.stalkMap_comp F (subspacePointMap (n := m) D) x).symm
      _ = _ := by
        simpa only [LocallyRingedSpace.comp_base,TopCat.comp_app,subspacePointMap_base_apply,
          TopCat.Presheaf.stalkSpecializes_refl,Category.id_comp] using h
  have hc := ConcreteCategory.congr_hom hs (actualComplexPointStalkEquiv.symm c)
  simp only [ConcreteCategory.comp_apply] at hc
  calc
    _ = F.stalkMap x ((subspacePointMap (n := m) D).stalkMap (F.base x)
        (actualComplexPointStalkEquiv.symm c)) :=
      congrArg (F.stalkMap x) (actualSubspacePointMap_stalk_const D (F.base x) c).symm
    _ = (subspacePointMap (n := n) C).stalkMap x (actualComplexPointStalkEquiv.symm c) := hc
    _ = _ := actualSubspacePointMap_stalk_const C x c

set_option backward.isDefEq.respectTransparency.types false in
/-- ANY genuine scalar-compatible locally ringed morphism preserves actual original point values. -/
theorem actualSubspaceMap_eval_of_point_compatible {C : Set M} {D : Set N}
    (F : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (hpoint : F ≫ subspacePointMap (n := m) D=subspacePointMap (n := n) C)
    (x : C) (a : ((actualSubspaceSheaf (n := m) D).presheaf.stalk (F.base x)).carrier) :
    actualSubspaceStalkEval (n := n) C x (F.stalkMap x a)=
      actualSubspaceStalkEval (n := m) D (F.base x) a := by
  let c := actualSubspaceStalkEval (n := m) D (F.base x) a
  have hz : a-actualSubspaceStalkConst (n := m) D (F.base x) c ∈
      IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := m) D).presheaf.stalk (F.base x)).carrier := by
    rw [← actualSubspaceStalkEval_ker,RingHom.mem_ker,map_sub,actualSubspaceStalkEval_const]
    exact sub_self c
  have hm := map_nonunit (F.stalkMap x).hom _ hz
  change (F.stalkMap x).hom _ ∈
    IsLocalRing.maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier at hm
  rw [← actualSubspaceStalkEval_ker,RingHom.mem_ker] at hm
  have hc := point_compatible_stalk_const F hpoint x c
  simp only [map_sub] at hm
  exact (sub_eq_zero.mp hm).trans
    ((congrArg (actualSubspaceStalkEval (n := n) C x) hc).trans (actualSubspaceStalkEval_const C x c))

end
end Hironaka.HironakaActualAnalyticSubspaceResidue
