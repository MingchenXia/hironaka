import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.DenseEmbedding

/-!
# Actual normalized blowup derivatives in legal block directions

Whole substitution differentiation is produced by actual polynomial density
and actual coefficientwise continuity. Source centre powers produce all lower
derivative powers. Neither a desired derivative identity nor a transformed
block membership certificate is an input.
-/

set_option autoImplicit false
open Set Classical
open scoped Topology MvPowerSeries.WithPiTopology

namespace Hironaka.HironakaActualNormalizedBlowupDerivative

noncomputable section

open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration

variable {n : ℕ}

/-- Genuine whole source centre-power membership produces the actual lower derivative power. -/
theorem pderiv_mem_actualCentrePower (A : Set (Fin n)) (j : Fin n) (hj : j ∈ A)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ (q+1)) :
    MvPowerSeries.pderiv ℂ j F ∈ actualFormalCoordinateIdeal n A ^ q := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff A q _).mpr
  intro a ha
  have hw : Finsupp.weight (actualCoordinateWeight A) (a + Finsupp.single j 1) =
      Finsupp.weight (actualCoordinateWeight A) a + 1 := by
    rw [map_add,Finsupp.weight_single]
    simp only [actualCoordinateWeight,if_pos hj,one_smul]
  rw [MvPowerSeries.coeff_pderiv,
    (mem_actualFormalCoordinateIdeal_pow_iff A (q+1) F).mp hF _ (by rw [hw]; omega),zero_mul]

private theorem pderiv_blowup_coordinate (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (j : Fin n) (hj : j ∈ A) (hje : j ≠ e) (i : Fin n) :
    MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b (MvPowerSeries.X i)) =
      MvPowerSeries.X e * actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ j (MvPowerSeries.X i)) := by
  have hXe : MvPowerSeries.pderiv ℂ j (MvPowerSeries.X e) = 0 :=
    MvPowerSeries.pderiv_X_of_ne (Ne.symm hje)
  by_cases hij : i = j
  · subst i
    rw [MvPowerSeries.pderiv_X_self,map_one,mul_one,actualFormalBlowup_X,
      actualFormalBlowupCoordinates,if_pos hj,if_neg hje,Derivation.leibniz,
      map_add,MvPowerSeries.pderiv_C,MvPowerSeries.pderiv_X_self,hXe]
    simp only [zero_add,smul_eq_mul,mul_one,mul_zero,add_zero]
  · have hXi : MvPowerSeries.pderiv ℂ j (MvPowerSeries.X i) = 0 :=
      MvPowerSeries.pderiv_X_of_ne hij
    rw [hXi,map_zero,mul_zero,actualFormalBlowup_X]
    by_cases hi : i ∈ A
    · by_cases hie : i = e
      · subst i
        rw [actualFormalBlowupCoordinates,if_pos hi,if_pos rfl]
        exact hXe
      · rw [actualFormalBlowupCoordinates,if_pos hi,if_neg hie,Derivation.leibniz,
          map_add,MvPowerSeries.pderiv_C,hXi,hXe]
        simp only [smul_zero,add_zero]
    · rw [actualFormalBlowupCoordinates,if_neg hi,hXi]

/-- The actual entire-series chain rule in a scaled nonexceptional centre direction.
The chart parameter is arbitrary; the polynomial-density argument is internal. -/
theorem pderiv_actualFormalBlowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (j : Fin n) (hj : j ∈ A) (hje : j ≠ e) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b F) =
      MvPowerSeries.X e * actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ j F) := by
  have hC (c : ℂ) : actualFormalBlowup A e b (MvPowerSeries.C c) = MvPowerSeries.C c :=
    (actualFormalBlowup A e b).commutes c
  have hcoord := pderiv_blowup_coordinate A e b j hj hje
  have hpoly (P : MvPolynomial (Fin n) ℂ) :
      MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b (P : MvPowerSeries (Fin n) ℂ)) =
        MvPowerSeries.X e * actualFormalBlowup A e b
          (MvPowerSeries.pderiv ℂ j (P : MvPowerSeries (Fin n) ℂ)) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp only [MvPolynomial.coe_C,hC,MvPowerSeries.pderiv_C,map_zero,mul_zero]
    | add P Q hP hQ => simp only [MvPolynomial.coe_add,map_add,hP,hQ,mul_add]
    | mul_X P i hP =>
      simp only [MvPolynomial.coe_mul,MvPolynomial.coe_X,map_mul,Derivation.leibniz,
        map_add,hP,hcoord,smul_eq_mul]
      ring
  let : UniformSpace ℂ := ⊥
  let : DiscreteUniformity ℂ := inferInstance
  let : DiscreteTopology ℂ := inferInstance
  have hD : Continuous (MvPowerSeries.pderiv ℂ j :
      MvPowerSeries (Fin n) ℂ → MvPowerSeries (Fin n) ℂ) := by
    apply continuous_pi
    intro a
    change Continuous (fun G : MvPowerSeries (Fin n) ℂ =>
      MvPowerSeries.coeff a (MvPowerSeries.pderiv ℂ j G))
    simpa only [MvPowerSeries.coeff_pderiv] using
      (MvPowerSeries.WithPiTopology.continuous_coeff ℂ (a + Finsupp.single j 1)).mul_const
        ((a j : ℂ) + 1)
  have hπ : Continuous (actualFormalBlowup A e b) := by
    change Continuous (fun G : MvPowerSeries (Fin n) ℂ => actualFormalBlowup A e b G)
    simp only [actualFormalBlowup,MvPowerSeries.substAlgHom_apply]
    exact MvPowerSeries.continuous_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero A e b))
  have heq : (fun G => MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b G)) =
      (fun G => MvPowerSeries.X e * actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ j G)) :=
    MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer
      (hD.comp hπ) (continuous_const.mul (hπ.comp hD)) (funext hpoly)
  exact congrFun heq F

/-- The SAME actual normalized member differentiates to the SAME actual lower-mark
member, whose genuine source-power premise is produced internally. -/
theorem pderiv_actualNormalizedFormalMember (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (j : Fin n) (hj : j ∈ A) (hje : j ≠ e)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ (q+1)) :
    MvPowerSeries.pderiv ℂ j (actualNormalizedFormalMember A e he b (q+1) F hF) =
      actualNormalizedFormalMember A e he b q (MvPowerSeries.pderiv ℂ j F)
        (pderiv_mem_actualCentrePower A j hj q F hF) := by
  apply actualNormalizedFormalMember_unique
  apply mul_left_cancel₀ (actualFormalExceptional_ne_zero e)
  have hs := congrArg (MvPowerSeries.pderiv ℂ j)
    (actualNormalizedFormalMember_spec A e he b (q+1) F hF)
  rw [Derivation.leibniz,MvPowerSeries.pderiv_pow,
    MvPowerSeries.pderiv_X_of_ne (Ne.symm hje)] at hs
  simp only [mul_zero,add_zero,smul_eq_mul] at hs
  rw [pderiv_actualFormalBlowup A e b j hj hje] at hs
  simpa only [pow_succ,mul_assoc,mul_comm (MvPowerSeries.X e ^ q) (MvPowerSeries.X e)] using hs

/-- The actual local blowup substitution preserves the genuine constant coefficient. -/
theorem constantCoeff_actualFormalBlowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.constantCoeff (actualFormalBlowup A e b F) = MvPowerSeries.constantCoeff F := by
  have hzero : MvPowerSeries.constantCoeff
      (F - MvPowerSeries.C (MvPowerSeries.constantCoeff F)) = 0 := by simp
  have hz := MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (actualFormalBlowupCoordinates_constant_zero A e b))
    (actualFormalBlowupCoordinates_constant_zero A e b) hzero
  have hC (c : ℂ) : actualFormalBlowup A e b (MvPowerSeries.C c) = MvPowerSeries.C c :=
    (actualFormalBlowup A e b).commutes c
  rw [← MvPowerSeries.substAlgHom_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e b))] at hz
  change MvPowerSeries.constantCoeff (actualFormalBlowup A e b
    (F - MvPowerSeries.C (MvPowerSeries.constantCoeff F))) = 0 at hz
  rw [map_sub,hC,map_sub,MvPowerSeries.constantCoeff_C,sub_eq_zero] at hz
  exact hz

/-- Every legal original Jacobian column of an actual mark-one member is
preserved at the actual chart origin, for arbitrary chart parameter b. -/
theorem normalized_mark_one_linear_coefficient (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (j : Fin n) (hj : j ∈ A) (hje : j ≠ e)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ 1) :
    MvPowerSeries.coeff (Finsupp.single j 1) (actualNormalizedFormalMember A e he b 1 F hF) =
      MvPowerSeries.coeff (Finsupp.single j 1) F := by
  have hD := pderiv_actualNormalizedFormalMember A e he b j hj hje 0 F hF
  have hz := actualNormalizedFormalMember_spec A e he b 0 (MvPowerSeries.pderiv ℂ j F)
    (pderiv_mem_actualCentrePower A j hj 0 F hF)
  rw [pow_zero,one_mul] at hz
  rw [hz] at hD
  have hc := congrArg MvPowerSeries.constantCoeff hD
  rw [constantCoeff_actualFormalBlowup] at hc
  simpa only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_pderiv,zero_add,Finsupp.zero_apply,Nat.cast_zero,zero_add,mul_one] using hc

/-- Source membership in a legitimate block internally gives actual centre-power one. -/
theorem block_mem_actualCentrePowerOne (A B : Set (Fin n)) (e : Fin n)
    (hB : B ⊆ A \ {e}) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n B) :
    F ∈ actualFormalCoordinateIdeal n A ^ 1 := by
  rw [pow_one]
  exact (Ideal.span_mono (Set.image_mono fun i hi => (hB hi).1)) hF

/-- Actual span induction produces the normalized SAME-block member internally;
the source-adapted condition b|B=0 is essential and explicit. -/
theorem normalized_mark_one_mem_actualBlock (A B : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (hB : B ⊆ A \ {e}) (b : Fin n → ℂ) (hb : ∀ j ∈ B, b j = 0)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n B) :
    actualNormalizedFormalMember A e he b 1 F (block_mem_actualCentrePowerOne A B e hB F hF) ∈
      actualFormalCoordinateIdeal n B := by
  have hfactor : ∀ G ∈ actualFormalCoordinateIdeal n B,
      ∃ Q ∈ actualFormalCoordinateIdeal n B, MvPowerSeries.X e * Q = actualFormalBlowup A e b G := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨j,hj,rfl⟩ := hG
      have hja : j ∈ A := (hB hj).1
      have hje : j ≠ e := by simpa only [Set.mem_singleton_iff] using (hB hj).2
      refine ⟨MvPowerSeries.X j,Ideal.subset_span ⟨j,hj,rfl⟩,?_⟩
      rw [actualFormalBlowup_X,actualFormalBlowupCoordinates,if_pos hja,if_neg hje,hb j hj,
        map_zero,zero_add]
    | zero => exact ⟨0,Ideal.zero_mem _,by simp⟩
    | add G H _ _ hG hH =>
      obtain ⟨Q,hQ,hQeq⟩ := hG
      obtain ⟨T,hT,hTeq⟩ := hH
      exact ⟨Q+T,Ideal.add_mem _ hQ hT,by rw [mul_add,hQeq,hTeq,map_add]⟩
    | smul C G _ hG =>
      obtain ⟨Q,hQ,hQeq⟩ := hG
      refine ⟨actualFormalBlowup A e b C * Q,(actualFormalCoordinateIdeal n B).mul_mem_left _ hQ,?_⟩
      change MvPowerSeries.X e * (actualFormalBlowup A e b C * Q) = actualFormalBlowup A e b (C * G)
      rw [map_mul,← hQeq]
      ring
  obtain ⟨Q,hQ,hQeq⟩ := hfactor F hF
  have heq := actualNormalizedFormalMember_unique A e he b 1 F
    (block_mem_actualCentrePowerOne A B e hB F hF) Q (by simpa only [pow_one] using hQeq)
  exact heq ▸ hQ

end

end Hironaka.HironakaActualNormalizedBlowupDerivative
