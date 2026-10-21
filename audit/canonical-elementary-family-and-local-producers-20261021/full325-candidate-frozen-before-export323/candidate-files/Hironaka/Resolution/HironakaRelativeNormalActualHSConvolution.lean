/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualBaseJetDimension
import Mathlib.LinearAlgebra.Quotient.Pi

/-! Evaluate genuine finite free quotient dimensions before the actual ambient HS convolution. -/
set_option autoImplicit false
open scoped BigOperators
namespace Hironaka.HironakaRelativeNormalActualHSConvolution
noncomputable section

section Coefficients
variable {B : Type*} [CommRing B] {A : Type*} [Fintype A]

/-- Actual ideal multiples of finite original coefficient families have exactly ideal-valued coordinates. -/
theorem actualCoefficientIdeal (K : Ideal B) :
    K • (⊤ : Submodule B (A → B)) = Submodule.pi Set.univ (fun _ : A => K) := by
  classical
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro b hb v _ a _
    exact K.mul_mem_right (v a) hb
  · intro v hv
    rw [← LinearMap.sum_single_apply (fun _ : A => B) v]
    apply Submodule.sum_mem
    intro a _
    have h : Pi.single a (v a) = (v a) • (Pi.single a 1 : A → B) := by
      ext c
      by_cases hc : c = a <;> simp [hc]
    rw [h]
    exact Submodule.smul_mem_smul (hv a (Set.mem_univ a)) (Submodule.mem_top)

end Coefficients

section ActualFreeQuotient
variable {B L : Type*} [CommRing B] [AddCommGroup L] [Module B L]
  [Module.Free B L] [Module.Finite B L]

/-- The genuine internally chosen finite basis preserves the WHOLE original ideal multiple. -/
theorem actualFreeCoefficientIdeal (K : Ideal B) :
    (K • (⊤ : Submodule B L)).map (Module.Free.chooseBasis B L).equivFun.toLinearMap =
      Submodule.pi Set.univ (fun _ : Module.Free.ChooseBasisIndex B L => K) := by
  rw [Submodule.map_smul'',Submodule.map_top,
    LinearEquiv.range,actualCoefficientIdeal]

/-- Whole genuine finite-free quotient coordinates use the SAME actual coefficient ideal. -/
def actualFreeQuotientEquiv (K : Ideal B) :
    (L ⧸ (K • (⊤ : Submodule B L))) ≃ₗ[B]
      (Module.Free.ChooseBasisIndex B L → B ⧸ K) := by
  classical
  exact (Submodule.Quotient.equiv _ _ (Module.Free.chooseBasis B L).equivFun
    (actualFreeCoefficientIdeal (L := L) K)).trans
      (Submodule.quotientPi (fun _ : Module.Free.ChooseBasisIndex B L => K))

end ActualFreeQuotient

section ActualComplexFreeQuotient
variable {B L : Type*} [CommRing B] [Algebra ℂ B] [AddCommGroup L]
  [Module B L] [Module ℂ L] [IsScalarTower ℂ B L]
  [Module.Free B L] [Module.Finite B L]

/-- The original scalar tower preserves the genuine complex action on EVERY original quotient class. -/
def actualFreeQuotientComplexEquiv (K : Ideal B) :
    (L ⧸ (K • (⊤ : Submodule B L))) ≃ₗ[ℂ]
      (Module.Free.ChooseBasisIndex B L → B ⧸ K) :=
  (actualFreeQuotientEquiv (L := L) K).restrictScalars ℂ

/-- The actual original quotient has its true finite-free rank times actual base-quotient dimension. -/
theorem actualFreeQuotientDimension [Nontrivial B] (K : Ideal B) [Module.Finite ℂ (B ⧸ K)] :
    Module.finrank ℂ (L ⧸ (K • (⊤ : Submodule B L))) =
      Module.finrank B L * Module.finrank ℂ (B ⧸ K) := by
  rw [(actualFreeQuotientComplexEquiv (L := L) K).finrank_eq,
    Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    ← Module.finrank_eq_card_basis (Module.Free.chooseBasis B L),nsmul_eq_mul]
  simp only [Nat.cast_id]

/-- True finite base quotient coordinates internally give finiteness of the original free-module quotient. -/
theorem actualFreeQuotientFinite (K : Ideal B) [Module.Finite ℂ (B ⧸ K)] :
    Module.Finite ℂ (L ⧸ (K • (⊤ : Submodule B L))) :=
  FiniteDimensional.of_injective (actualFreeQuotientComplexEquiv (L := L) K).toLinearMap
    (actualFreeQuotientComplexEquiv (L := L) K).injective

end ActualComplexFreeQuotient

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalIdeal
  HironakaRelativeNormalActualWeightedTruncations HironakaRelativeNormalActualBaseJetDimension
  HironakaHolomorphicPointJets HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalNearbyUniformRanks HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalFibreHilbertSamuel

open scoped Topology Manifold ContDiff

/-- The SAME genuine finite-free original module retains its actual base-jet binomial weight. -/
theorem actualOriginalFreeJetDimension (d k : ℕ) (L : Type*) [AddCommGroup L]
    [Module (HolGerm (ComplexModel d)) L] [Module ℂ L]
    [IsScalarTower ℂ (HolGerm (ComplexModel d)) L]
    [Module.Free (HolGerm (ComplexModel d)) L] [Module.Finite (HolGerm (ComplexModel d)) L] :
    Module.finrank ℂ
      (L ⧸ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (k+1) •
        (⊤ : Submodule (HolGerm (ComplexModel d)) L))) =
      Module.finrank (HolGerm (ComplexModel d)) L * (d+k).choose d := by
  let := finiteDimensional_quotient_maximalIdeal_pow d (k+1)
  rw [actualFreeQuotientDimension,actualBaseJetDimension]

section OriginalLayers
variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  IsScalarTower.of_algHom (tangentPullback d t)

/-- Each genuine positive weighted original normal layer is actually finite-dimensional over the original complex field. -/
theorem actualOriginalWeightedLayerFinite (I : Ideal (HolGerm (ComplexModel (d+t))))
    (ℓ q : ℕ) (hq : q ≤ ℓ)
    [Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q)]
    [Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q)] :
    Module.Finite ℂ (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d))
      I (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q) := by
  have hpositive : ℓ+1-q = (ℓ-q)+1 := by omega
  let := finiteDimensional_quotient_maximalIdeal_pow d (ℓ+1-q)
  exact actualFreeQuotientFinite (L := idealPowerLayer (HolGerm (ComplexModel d))
    I (normalIdeal d t) q) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (ℓ+1-q))

/-- Every SAME original weighted normal layer has the genuine rank times tangent binomial dimension. -/
theorem actualOriginalWeightedLayerDimension (I : Ideal (HolGerm (ComplexModel (d+t))))
    (ℓ q : ℕ) (hq : q ≤ ℓ)
    [Module.Free (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q)]
    [Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q)] :
    Module.finrank ℂ (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d))
      I (normalIdeal d t) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q) =
        Module.finrank (HolGerm (ComplexModel d))
          (idealPowerLayer (HolGerm (ComplexModel d)) I (normalIdeal d t) q) *
            (d+ℓ-q).choose d := by
  have hpositive : ℓ+1-q = (ℓ-q)+1 := by omega
  unfold actualWeightedLayerQuotient
  rw [hpositive,actualOriginalFreeJetDimension]
  have hsum : d+(ℓ-q) = d+ℓ-q := by omega
  rw [hsum]

end OriginalLayers

/-- ONLY original coherence gives the true AMBIENT HS convolution at EVERY order on the SAME one accumulating open. -/
theorem exists_original_nearby_actual_ambient_hs_convolution (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
      (∀ V ∈ nhds (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ ℓ : ℕ,
        let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
        hilbertSamuelValue Ia ℓ =
          ∑ q : Fin (ℓ+1), r q.val * (d+ℓ-q.val).choose d := by
  let := tangentAlgebra d t
  let : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
    IsScalarTower.of_algHom (tangentPullback d t)
  obtain ⟨U,r,hU,hmeet,hdecomp⟩ :=
    exists_original_nearby_ambient_weighted_layer_decomposition d t I hI
  refine ⟨U,r,hU,hmeet,?_⟩
  intro a ha ℓ
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))
  obtain ⟨hfree,hfinite,he⟩ := hdecomp a ha
  let := hfree
  let : ∀ q, Module.Finite (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q) :=
    fun q => (hfinite q).1
  let : ∀ q : Fin (ℓ+1), Module.Finite ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun q => actualOriginalWeightedLayerFinite d t Ia ℓ q.val (Nat.le_of_lt_succ q.isLt)
  let : ∀ q : Fin (ℓ+1), Module.Free ℂ
      (actualWeightedLayerQuotient (B := HolGerm (ComplexModel d)) Ia (normalIdeal d t)
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) (ℓ+1) q.val) :=
    fun _ => inferInstance
  let e := Classical.choice (he (ℓ+1))
  change Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
    (Ia ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1))) = _
  rw [e.finrank_eq,Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro q _
  rw [actualOriginalWeightedLayerDimension d t Ia ℓ q.val (Nat.le_of_lt_succ q.isLt)]
  have hr : Module.finrank (HolGerm (ComplexModel d))
      (idealPowerLayer (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q.val) = r q.val :=
    (hfinite q.val).2
  rw [hr]

/-- The genuine original ambient HS functions agree on the SAME open at ALL orders, without a caller constancy certificate. -/
theorem exists_original_nearby_actual_ambient_hs_constancy (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ nhds (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      ∀ a ∈ U, ∀ b ∈ U, ∀ ℓ : ℕ,
        hilbertSamuelValue
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) ℓ =
        hilbertSamuelValue
          (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t b))) ℓ := by
  obtain ⟨U,r,hU,hmeet,hvalue⟩ := exists_original_nearby_actual_ambient_hs_convolution d t I hI
  exact ⟨U,hU,hmeet,fun a ha b hb ℓ => (hvalue a ha ℓ).trans (hvalue b hb ℓ).symm⟩
end
end Hironaka.HironakaRelativeNormalActualHSConvolution
