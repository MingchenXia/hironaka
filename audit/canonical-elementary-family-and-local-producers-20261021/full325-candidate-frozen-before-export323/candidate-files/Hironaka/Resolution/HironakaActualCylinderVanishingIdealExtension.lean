/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermSubExact
import Hironaka.Resolution.HironakaActualCylinderRelativeHadamard
import Hironaka.Analytic.AnalyticGermDecomposition
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# The entire original singular cylinder ideal is the actual base extension

Actual relative Hadamard division retains every coefficient inside the SAME
original vanishing ideal. Genuine Noetherian holomorphic germs and Nakayama
then prove equality with the actual original base-ideal extension. No base
smoothness, analytic presentation, coherent-ideal or equality certificate is
assumed. Arbitrary-submersion sheaf transport remains a separate dictionary.
Blueprint: `hironaka-actual-cylinder-vanishing-ideal-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualCylinderVanishingIdealExtension
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualCylinderRelativeHadamard HironakaRelativeNormalIdeal HadamardBridgeAlong
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan

/-- The independently defined literal cylinder is the inverse image under the true original projection. -/
theorem mem_cylinderCarrier_iff (k t : ℕ) (W : Set (ComplexModel k)) (z : ComplexModel (k+t)) :
    z∈cylinderCarrier k t W ↔ tangentProjection k t z∈W := Iff.rfl

/-- The original projection extends the ENTIRE original base vanishing ideal into the true cylinder ideal. -/
theorem map_base_vanishingIdeal_le_cylinder (k t : ℕ) (W : Set (ComplexModel k)) :
    Ideal.map (tangentPullback k t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W)≤
      AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro g hg
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
  change tangentPullback k t (HolGerm.mk f hf)∈AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)
  unfold tangentPullback
  rw [compAlgHom_mk]
  apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
  have hp : Tendsto (tangentProjection k t) (𝓝 0) (𝓝 0) := by
    simpa using (tangentProjection k t).continuous.tendsto 0
  filter_upwards [hp.eventually (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg)] with z hz hzS
  exact hz hzS

/-- The actual zero section sends EVERY original cylinder germ back into the true base vanishing ideal. -/
theorem trace_cylinder_vanishingIdeal_le_base (k t : ℕ) (W : Set (ComplexModel k))
    (g : HolGerm (ComplexModel (k+t)))
    (hg : g∈AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)) :
    planeTrace k t g∈AnalyticGermDecomposition.vanishingIdeal W := by
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
  unfold planeTrace
  rw [compAlgHom_mk]
  apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
  have hs : Tendsto (tangentInclusion k t) (𝓝 0) (𝓝 0) := by
    simpa using (tangentInclusion k t).continuous.tendsto 0
  filter_upwards [hs.eventually (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg)] with z hz hzW
  apply hz
  rw [mem_cylinderCarrier_iff,tangentProjection_tangentInclusion]
  exact hzW

private theorem inclusion_projection_eq_planeRetract (k t : ℕ) (z : ComplexModel (k+t)) :
    tangentInclusion k t (tangentProjection k t z)=planeRetract k z := by
  ext i
  by_cases hi : i.val<k
  · let j : Fin k := ⟨i.val,hi⟩
    have he : i=j.castAdd t := Fin.ext rfl
    rw [he,tangentInclusion_tangent,tangentProjection_apply,planeRetract_apply,Fin.val_castAdd,if_pos j.isLt]
  · let j : Fin t := ⟨i.val-k,by have hin:=i.isLt; omega⟩
    have he : i=j.natAdd k := Fin.ext (by dsimp [j]; omega)
    rw [he,tangentInclusion_normal,planeRetract_apply,if_neg (by simp only [Fin.val_natAdd]; omega)]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Actual relative Hadamard gives the whole original ideal inclusion with self-multiples needed by Nakayama. -/
theorem cylinder_vanishingIdeal_le_extension_sup_normal_mul (k t : ℕ) (W : Set (ComplexModel k)) :
    AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)≤
      Ideal.map (tangentPullback k t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W)⊔
        normalIdeal k t*AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W) := by
  let J := AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)
  let K := Ideal.map (tangentPullback k t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W)
  intro g hg
  obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk g
  have hFmem : (vanishingIdeal (n := k+t) (cylinderCarrier k t W)).mem 0 F :=
    ⟨hF.mono fun _ hz => hz.mdifferentiableAt,AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg⟩
  obtain ⟨H,hH0,hHJ,heq⟩ := exists_cylinder_relative_difference k t W F hFmem
  let hH : ∀ i : Fin (k+t),∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),DifferentiableAt ℂ (H i) z :=
    fun i => (hHJ i).1.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mp hz
  have hHg (i : Fin (k+t)) : HolGerm.mk (H i) (hH i)∈J :=
    AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr (hHJ i).2
  let P := planeRetract (n := k+t) k
  have hp : Tendsto P (𝓝 0) (𝓝 0) := by simpa using P.continuous.tendsto 0
  have hFP : ∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),DifferentiableAt ℂ (F∘P) z := by
    filter_upwards [hp.eventually hF] with z hz
    exact hz.comp z P.differentiableAt
  have hret : HolGerm.mk (F∘P) hFP=tangentPullback k t (planeTrace k t (HolGerm.mk F hF)) := by
    unfold planeTrace tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (inclusion_projection_eq_planeRetract k t z).symm
  have hK : HolGerm.mk (F∘P) hFP∈K := by
    rw [hret]
    exact Ideal.mem_map_of_mem _ (trace_cylinder_vanishingIdeal_le_base k t W _ hg)
  let hterm : ∀ i : Fin (k+t),∀ᶠ z in 𝓝 (0 : ComplexModel (k+t)),
      DifferentiableAt ℂ (fun z => z i*H i z) z :=
    fun i => (hH i).mono fun z hz => (EuclideanSpace.proj i : ComplexModel (k+t) →L[ℂ] ℂ).differentiableAt.mul hz
  have hsum : HolGerm.mk F hF-HolGerm.mk (F∘P) hFP=
      ∑ i : Fin (k+t),coordinateGerm i*HolGerm.mk (H i) (hH i) := by
    calc
      _ = HolGerm.mk (fun z => ∑ i : Fin (k+t),z i*H i z)
          (eventually_differentiableAt_sum Finset.univ hterm) := by
        rw [← HolGerm.mk_sub]
        exact HolGerm.mk_eq_mk_iff.mpr heq
      _ = ∑ i : Fin (k+t),HolGerm.mk (fun z => z i*H i z) (hterm i) :=
        HolGerm.mk_sum Finset.univ _ hterm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact HolGerm.mk_mul (fun z : ComplexModel (k+t) => z i) (H i)
          (Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel (k+t) →L[ℂ] ℂ).differentiableAt) (hH i)
  have hdiff : HolGerm.mk F hF-HolGerm.mk (F∘P) hFP∈normalIdeal k t*J := by
    rw [hsum]
    apply Ideal.sum_mem
    intro i _
    by_cases hi : i.val<k
    · have hh : HolGerm.mk (H i) (hH i)=0 := by
        rw [← HolGerm.mk_zero]
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Eventually.of_forall fun z => congrFun (hH0 i hi) z
      simp only [hh,mul_zero]
      exact Ideal.zero_mem _
    · have hik : k≤ i.val := by omega
      let j : Fin t := ⟨i.val-k,by have hin:=i.isLt; omega⟩
      have he : i=j.natAdd k := Fin.ext (by dsimp [j]; omega)
      have hcoord : coordinateGerm i∈normalIdeal k t := by
        apply Ideal.subset_span
        exact ⟨j,congrArg coordinateGerm he.symm⟩
      exact Ideal.mul_mem_mul hcoord (hHg i)
  have hmem : HolGerm.mk (F∘P) hFP+(HolGerm.mk F hF-HolGerm.mk (F∘P) hFP)∈K⊔normalIdeal k t*J :=
    Ideal.add_mem _ (Ideal.mem_sup_left hK) (Ideal.mem_sup_right hdiff)
  have he : HolGerm.mk (F∘P) hFP+(HolGerm.mk F hF-HolGerm.mk (F∘P) hFP)=HolGerm.mk F hF := by ring
  rwa [he] at hmem

/-- The ENTIRE independently defined singular product ideal equals actual whole base extension, with no coherence certificate. -/
theorem cylinder_vanishingIdeal_eq_base_extension (k t : ℕ) (W : Set (ComplexModel k)) :
    AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)=
      Ideal.map (tangentPullback k t).toRingHom (AnalyticGermDecomposition.vanishingIdeal W) := by
  let : IsNoetherianRing (HolGerm (ComplexModel (k+t))) := isNoetherianRing_holGerm_euclidean (k+t)
  let J := AnalyticGermDecomposition.vanishingIdeal (cylinderCarrier k t W)
  have hN : normalIdeal k t≤Ideal.jacobson (⊥ : Ideal (HolGerm (ComplexModel (k+t)))) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply IsLocalRing.maximalIdeal_le_jacobson ⊥
    rw [HolGerm.mem_maximalIdeal_iff]
    simp [normalCoordinate,coordinateGerm,HolGerm.eval_mk]
  refine le_antisymm ?_ (map_base_vanishingIdeal_le_cylinder k t W)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Ideal.fg_of_isNoetherianRing J) hN
  rw [Ideal.smul_eq_mul]
  exact cylinder_vanishingIdeal_le_extension_sup_normal_mul k t W

end
end Hironaka.HironakaActualCylinderVanishingIdealExtension
