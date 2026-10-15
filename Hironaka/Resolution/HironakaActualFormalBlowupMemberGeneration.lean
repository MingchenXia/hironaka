/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalCoordinatePowerDivision
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! Genuine formal blowup substitution, exceptional division and generation of all normalized original members. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalBlowupMemberGeneration
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalCoordinatePowerDivision
variable {n : ℕ}

/-- Literal coordinates of the actual e-chart over the selected coordinate center. -/
def actualFormalBlowupCoordinates (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  if i ∈ A then if i=e then MvPowerSeries.X e
    else MvPowerSeries.X e*(MvPowerSeries.C (b i)+MvPowerSeries.X i)
  else MvPowerSeries.X i

/-- Actual coordinate factors internally supply true zero constant coefficients. -/
theorem actualFormalBlowupCoordinates_constant_zero (A : Set (Fin n)) (e : Fin n)
    (b : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualFormalBlowupCoordinates A e b i)=0 := by
  simp only [actualFormalBlowupCoordinates]
  split_ifs <;> simp

/-- The genuine formal complex algebra substitution defined by the actual blowup coordinates. -/
def actualFormalBlowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e b))

/-- Each true variable has exactly its literal blowup image. -/
theorem actualFormalBlowup_X (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    actualFormalBlowup A e b (MvPowerSeries.X i)=actualFormalBlowupCoordinates A e b i :=
  MvPowerSeries.substAlgHom_X _ i

/-- BOTH whole center-ideal image directions are internally supplied by actual chart coordinates. -/
theorem map_actualFormalCoordinateIdeal_blowup (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal.map (actualFormalBlowup A e b).toRingHom (actualFormalCoordinateIdeal n A)=
      Ideal.span {MvPowerSeries.X e} := by
  apply le_antisymm
  · rw [actualFormalCoordinateIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro F ⟨G,⟨i,hi,rfl⟩,rfl⟩
    change actualFormalBlowup A e b (MvPowerSeries.X i) ∈ _
    rw [actualFormalBlowup_X]
    by_cases hie : i=e
    · simp [actualFormalBlowupCoordinates,hie]
    · rw [actualFormalBlowupCoordinates,if_pos hi,if_neg hie]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · apply Ideal.span_le.mpr
    rintro F rfl
    have h := Ideal.mem_map_of_mem (actualFormalBlowup A e b).toRingHom
      (Ideal.subset_span (show (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ∈
        (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ) '' A from ⟨e,he,rfl⟩))
    change actualFormalBlowup A e b (MvPowerSeries.X e) ∈ _ at h
    rw [actualFormalBlowup_X,actualFormalBlowupCoordinates,if_pos he,if_pos rfl] at h
    change (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ∈
      Ideal.map (actualFormalBlowup A e b).toRingHom (actualFormalCoordinateIdeal n A)
    exact h

/-- EVERY actual center power has its literal whole exceptional principal-power image. -/
theorem map_actualFormalCoordinateIdeal_pow_blowup (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (d : ℕ) :
    Ideal.map (actualFormalBlowup A e b).toRingHom (actualFormalCoordinateIdeal n A ^ d)=
      Ideal.span {(MvPowerSeries.X e) ^ d} := by
  rw [Ideal.map_pow,map_actualFormalCoordinateIdeal_blowup A e he b,Ideal.span_singleton_pow]

/-- A true center-power member internally supplies genuine exceptional divisibility. -/
theorem actualFormalBlowup_divisible (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) :
    ∃ G : MvPowerSeries (Fin n) ℂ, (MvPowerSeries.X e)^d*G=actualFormalBlowup A e b F := by
  have h := Ideal.mem_map_of_mem (actualFormalBlowup A e b).toRingHom hF
  rw [map_actualFormalCoordinateIdeal_pow_blowup A e he b d] at h
  obtain ⟨G,hG⟩ := Ideal.mem_span_singleton'.mp h
  change G*(MvPowerSeries.X e)^d=actualFormalBlowup A e b F at hG
  exact ⟨G,by simpa only [mul_comm] using hG⟩

/-- The actual exceptional quotient is internally chosen from true center-power membership. -/
def actualNormalizedFormalMember (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) : MvPowerSeries (Fin n) ℂ :=
  Classical.choose (actualFormalBlowup_divisible A e he b d F hF)

/-- SAME actual numerator and true exceptional power define the internally constructed quotient. -/
theorem actualNormalizedFormalMember_spec (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) :
    (MvPowerSeries.X e)^d*actualNormalizedFormalMember A e he b d F hF=actualFormalBlowup A e b F :=
  Classical.choose_spec (actualFormalBlowup_divisible A e he b d F hF)

/-- The genuine exceptional variable is nonzero in the ACTUAL formal ring. -/
theorem actualFormalExceptional_ne_zero (e : Fin n) :
    (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single e 1)) h
  simp at hc

/-- Genuine formal-domain cancellation proves uniqueness, with no supplied exceptional quotient. -/
theorem actualNormalizedFormalMember_unique (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) (G : MvPowerSeries (Fin n) ℂ)
    (hG : (MvPowerSeries.X e)^d*G=actualFormalBlowup A e b F) :
    G=actualNormalizedFormalMember A e he b d F hF := by
  apply mul_left_cancel₀ (pow_ne_zero d (actualFormalExceptional_ne_zero e))
  exact hG.trans (actualNormalizedFormalMember_spec A e he b d F hF).symm

/-- Actual vertex normalized generators use the literal source vertex-power membership only. -/
def actualNormalizedFormalVertex (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, actualVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  actualNormalizedFormalMember A e he b _ (actualVertexSeries m I a) (hv a)

/-- EVERY normalized original member lies in the genuine finite normalized vertex ideal. -/
theorem actualNormalizedFormalMember_mem_vertex_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, actualVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d) :
    actualNormalizedFormalMember A e he b d F hF ∈
      Ideal.span (range (actualNormalizedFormalVertex m I A e he b hv)) := by
  let w (a : actualInitialVertices m I) := Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)
  have hd := actual_formal_centre_power_whole_division m I A d F hI hF hv
  let Q (a : actualInitialVertices m I) := actualFormalQuotient m I F a
  let Qb (a : actualInitialVertices m I) := actualNormalizedFormalMember A e he b (d-w a) (Q a) (hd.2 a)
  let fb := actualNormalizedFormalVertex m I A e he b hv
  have ht (a : actualInitialVertices m I) :
      actualFormalBlowup A e b (Q a*actualVertexSeries m I a)=
        (MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(w a-d)*Qb a*fb a) := by
    rw [map_mul,← actualNormalizedFormalMember_spec A e he b (d-w a) (Q a) (hd.2 a),
      ← actualNormalizedFormalMember_spec A e he b (w a) (actualVertexSeries m I a) (hv a)]
    change ((MvPowerSeries.X e)^(d-w a)*Qb a)*((MvPowerSeries.X e)^(w a)*fb a)=_
    calc
      _=(MvPowerSeries.X e)^((d-w a)+w a)*(Qb a*fb a) := by rw [pow_add]; ring
      _=(MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(w a-d)*Qb a*fb a) := by
        rw [show (d-w a)+w a=d+(w a-d) by omega,pow_add]
        ring
  have hs : actualNormalizedFormalMember A e he b d F hF=
      ∑ a : actualInitialVertices m I, (MvPowerSeries.X e)^(w a-d)*Qb a*fb a := by
    apply mul_left_cancel₀ (pow_ne_zero d (actualFormalExceptional_ne_zero e))
    calc
      _=actualFormalBlowup A e b F := actualNormalizedFormalMember_spec A e he b d F hF
      _=actualFormalBlowup A e b (∑ a : actualInitialVertices m I, Q a*actualVertexSeries m I a) :=
        congrArg (actualFormalBlowup A e b) hd.1
      _=∑ a : actualInitialVertices m I, actualFormalBlowup A e b (Q a*actualVertexSeries m I a) :=
        map_sum _ _ _
      _=_ := by simp_rw [ht]; exact (Finset.mul_sum _ _ _).symm
  rw [hs]
  apply Ideal.sum_mem
  intro a _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)

/-- The actual ideal of normalized images of EVERY original formal center-power member. -/
def actualNormalizedOriginalMemberIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span {G | ∃ (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (_hI : F ∈ I)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ d), G=actualNormalizedFormalMember A e he b d F hF}

/-- BOTH whole actual normalized-member ideals coincide; no all-power saturation bridge is assumed. -/
theorem actualNormalizedOriginalMemberIdeal_eq_vertex_span (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ)
    (hv : ∀ a : actualInitialVertices m I, actualVertexSeries m I a ∈ actualFormalCoordinateIdeal n A ^
      Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    actualNormalizedOriginalMemberIdeal I A e he b=
      Ideal.span (range (actualNormalizedFormalVertex m I A e he b hv)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro G ⟨d,F,hI,hF,rfl⟩
    exact actualNormalizedFormalMember_mem_vertex_span m I A e he b hv d F hI hF
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact Ideal.subset_span ⟨_,actualVertexSeries m I a,(actualVertexSeries_spec m I a).1,hv a,rfl⟩

end
end Hironaka.HironakaActualFormalBlowupMemberGeneration
