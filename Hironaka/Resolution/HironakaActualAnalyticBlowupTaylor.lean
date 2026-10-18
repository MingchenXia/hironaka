/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration

/-! Genuine polynomial blowup coordinate maps, whole original germ pullback and literal Taylor naturality. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticBlowupTaylor
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualAnalyticFormalNormalPowers HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalCoordinatePowerDivision HironakaHolomorphicJetChartInvariance
variable {n : ℕ}

/-- The actual complex polynomial coordinate of the exceptional chart. -/
def actualAnalyticBlowupCoordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) (z : ComplexModel n) : ℂ :=
  if i ∈ A then if i=e then z e else z e*(b i+z i) else z i

/-- The genuine vector-valued polynomial chart map, independently of all formal series. -/
def actualAnalyticBlowupMap (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ComplexModel n → ComplexModel n :=
  fun z => (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm
    (fun i => actualAnalyticBlowupCoordinate A e b i z)

/-- Each true coordinate has precisely its original polynomial expression. -/
theorem actualAnalyticBlowupMap_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (i : Fin n) :
    actualAnalyticBlowupMap A e b z i=actualAnalyticBlowupCoordinate A e b i z := rfl

/-- The actual map is holomorphic, by genuine complex linear projections and polynomial operations. -/
theorem differentiable_actualAnalyticBlowupMap (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Differentiable ℂ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : Differentiable ℂ (fun z : ComplexModel n => z i) :=
    ((ContinuousLinearMap.proj i).comp
      (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).toContinuousLinearMap).differentiable
  have hc (i : Fin n) : Differentiable ℂ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((differentiable_const (b i)).add (hp i))
    · exact hp i
  exact (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.differentiable.comp
    (differentiable_pi.mpr hc)

/-- The genuine chart map sends the actual origin to the actual origin. -/
theorem actualAnalyticBlowupMap_zero (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticBlowupMap A e b 0=0 := by
  ext i
  simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate]

/-- The actual original germ pullback uses genuine composition by the true polynomial map. -/
def actualAnalyticBlowupPullback (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (actualAnalyticBlowupMap A e b)
    (Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap A e b).differentiableAt)
    (actualAnalyticBlowupMap_zero A e b)

/-- The entire original coordinate germs have the literal actual polynomial pullbacks. -/
theorem actualAnalyticBlowupPullback_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) :
    actualAnalyticBlowupPullback A e b (coordinateGerm i)=
      if i ∈ A then if i=e then coordinateGerm e
        else coordinateGerm e*(HolGerm.constHom (b i)+coordinateGerm i)
      else coordinateGerm i := by
  split_ifs with hi hie
  · unfold actualAnalyticBlowupPullback coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hie]
  · unfold actualAnalyticBlowupPullback coordinateGerm
    rw [compAlgHom_mk]
    change HolGerm.mk _ _ = HolGerm.mk (fun z : ComplexModel n => z e*(b i+z i))
      (Eventually.of_forall fun z =>
        (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt.mul
          (differentiableAt_const (b i) |>.add (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt))
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hie]
  · unfold actualAnalyticBlowupPullback coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]

/-- The actual original coordinate dictionary agrees with the independently defined formal chart. -/
theorem actualTaylor_analyticBlowup_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b (coordinateGerm i))=
      actualFormalBlowupCoordinates A e b i := by
  have hc (c : ℂ) : actualUnshiftedTaylorAlgHom n (HolGerm.constHom c)=MvPowerSeries.C c :=
    (actualUnshiftedTaylorAlgHom n).commutes c
  rw [actualAnalyticBlowupPullback_coordinate]
  by_cases hi : i ∈ A <;> by_cases hie : i=e <;>
    simp [actualFormalBlowupCoordinates,hi,hie,actualUnshiftedTaylor_coordinate,hc]

/-- The WHOLE genuine original Taylor map commutes with genuine analytic chart pullback. -/
theorem actualTaylor_analyticBlowupPullback (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    (actualUnshiftedTaylorAlgHom n).comp (actualAnalyticBlowupPullback A e b)=
      (actualFormalBlowup A e b).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b (coordinateGerm i))=
      actualFormalBlowup A e b (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [actualTaylor_analyticBlowup_coordinate,actualUnshiftedTaylor_coordinate,actualFormalBlowup_X]
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b (coordinateGerm i)) ∈ _
    rw [actualTaylor_analyticBlowup_coordinate]
    unfold actualFormalBlowupCoordinates
    split_ifs
    · exact Ideal.subset_span ⟨e,mem_univ _,rfl⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e,mem_univ _,rfl⟩)
    · exact Ideal.subset_span ⟨i,mem_univ _,rfl⟩

/-- The actual original analytic coordinate-centre ideal, independently of its formal image. -/
def actualAnalyticCoordinateIdeal (A : Set (Fin n)) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (coordinateGerm '' A)

/-- The genuine Taylor map sends the whole analytic coordinate ideal to the whole formal coordinate ideal. -/
theorem map_actualAnalyticCoordinateIdeal_taylor (A : Set (Fin n)) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticCoordinateIdeal A)=
      actualFormalCoordinateIdeal n A := by
  rw [actualAnalyticCoordinateIdeal,Ideal.map_span,actualFormalCoordinateIdeal,← image_comp]
  congr 2
  funext i
  exact actualUnshiftedTaylor_coordinate n i

/-- Every actual analytic power member internally has the genuine formal centre-power membership. -/
theorem actualTaylor_mem_coordinateCentre_pow (A : Set (Fin n)) (q : ℕ)
    (g : HolGerm (ComplexModel n)) (hg : g ∈ actualAnalyticCoordinateIdeal A ^ q) :
    actualUnshiftedTaylorAlgHom n g ∈ actualFormalCoordinateIdeal n A ^ q := by
  have hm := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hg
  rwa [Ideal.map_pow,map_actualAnalyticCoordinateIdeal_taylor] at hm

/-- BOTH entire analytic centre-ideal image directions follow from actual polynomial coordinates. -/
theorem map_actualAnalyticCoordinateIdeal_blowup (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (actualAnalyticCoordinateIdeal A)=
      Ideal.span {coordinateGerm e} := by
  apply le_antisymm
  · rw [actualAnalyticCoordinateIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro F ⟨G,⟨i,hi,rfl⟩,rfl⟩
    change actualAnalyticBlowupPullback A e b (coordinateGerm i) ∈ _
    rw [actualAnalyticBlowupPullback_coordinate,if_pos hi]
    by_cases hie : i=e
    · simp [hie]
    · rw [if_neg hie]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro F rfl
    have h := Ideal.mem_map_of_mem (actualAnalyticBlowupPullback A e b).toRingHom
      (Ideal.subset_span (show coordinateGerm e ∈ coordinateGerm '' A from ⟨e,he,rfl⟩))
    change actualAnalyticBlowupPullback A e b (coordinateGerm e) ∈ _ at h
    rw [actualAnalyticBlowupPullback_coordinate,if_pos he,if_pos rfl] at h
    exact h

/-- Every true analytic centre power maps to the literal entire analytic exceptional power. -/
theorem map_actualAnalyticCoordinateIdeal_pow_blowup (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (q : ℕ) :
    Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (actualAnalyticCoordinateIdeal A ^ q)=
      Ideal.span {(coordinateGerm e)^q} := by
  rw [Ideal.map_pow,map_actualAnalyticCoordinateIdeal_blowup A e he b,Ideal.span_singleton_pow]

/-- Genuine analytic exceptional division constructs an actual holomorphic quotient, with its entire literal formal dictionary. -/
theorem exists_actualAnalyticBlowup_quotient (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (q : ℕ) (g : HolGerm (ComplexModel n))
    (hg : g ∈ actualAnalyticCoordinateIdeal A ^ q) :
    ∃ G : HolGerm (ComplexModel n), (coordinateGerm e)^q*G=actualAnalyticBlowupPullback A e b g ∧
      actualUnshiftedTaylorAlgHom n G=actualNormalizedFormalMember A e he b q
        (actualUnshiftedTaylorAlgHom n g) (actualTaylor_mem_coordinateCentre_pow A q g hg) := by
  have hm := Ideal.mem_map_of_mem (actualAnalyticBlowupPullback A e b).toRingHom hg
  rw [map_actualAnalyticCoordinateIdeal_pow_blowup A e he b q] at hm
  obtain ⟨G,hG⟩ := Ideal.mem_span_singleton'.mp hm
  change G*(coordinateGerm e)^q=actualAnalyticBlowupPullback A e b g at hG
  have hprod : (coordinateGerm e)^q*G=actualAnalyticBlowupPullback A e b g := by
    simpa only [mul_comm] using hG
  refine ⟨G,hprod,?_⟩
  apply actualNormalizedFormalMember_unique
  have ht := congrArg (actualUnshiftedTaylorAlgHom n) hprod
  rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at ht
  have hn := DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) g
  exact ht.trans hn

/-- Standard normal centres are literally the same original analytic coordinate ideals. -/
theorem actualAnalyticCoordinateIdeal_normal (d t : ℕ) :
    actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)=
      HironakaRelativeNormalIdeal.normalIdeal d t := by
  rw [actualAnalyticCoordinateIdeal,actualTangentCentreVariables,
    HironakaRelativeNormalIdeal.normalIdeal]
  congr 1
  ext g
  constructor
  · rintro ⟨i,⟨j,rfl⟩,rfl⟩
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨j.natAdd d,⟨j,rfl⟩,rfl⟩

/-- Formal normal-power membership alone internally recovers the genuine analytic exceptional quotient. -/
theorem exists_actualAnalyticBlowup_quotient_of_formal_normal_pow (d t q : ℕ)
    (e : Fin (d+t)) (he : e ∈ actualTangentCentreVariables d t) (b : Fin (d+t) → ℂ)
    (g : HolGerm (ComplexModel (d+t)))
    (hg : actualUnshiftedTaylorAlgHom (d+t) g ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^q) :
    ∃ G : HolGerm (ComplexModel (d+t)), (coordinateGerm e)^q*G=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b g ∧
      actualUnshiftedTaylorAlgHom (d+t) G=
        actualNormalizedFormalMember (actualTangentCentreVariables d t) e he b q
          (actualUnshiftedTaylorAlgHom (d+t) g) hg := by
  have ha : g ∈ actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^q := by
    rw [actualAnalyticCoordinateIdeal_normal]
    exact (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t q g).mpr hg
  exact exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables d t) e he b q g ha

end
end Hironaka.HironakaActualAnalyticBlowupTaylor
