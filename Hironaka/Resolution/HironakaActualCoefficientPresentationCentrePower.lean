/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalCoordinatePowerDivision
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Resolution.HironakaRelativeNormalAnalyticGraphQuotient

/-! Actual coefficient-series centre powers, before geometric transformed presentations. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCoefficientPresentationCentrePower
noncomputable section
open HironakaActualFormalCoordinatePowerDivision
variable {d t : ℕ}

/-- The actual exponent with the two literal coordinate blocks. -/
def actualJoinedExponent (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) : Fin (d+t) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.addCases β γ)

/-- The original tangent block of a genuine exponent. -/
def actualTangentExponent (a : Fin (d+t) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a (i.castAdd t))

/-- The original normal block of a genuine exponent. -/
def actualNormalExponent (a : Fin (d+t) →₀ ℕ) : Fin t →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a (i.natAdd d))

/-- Every literal exponent is reconstructed from its two actual blocks. -/
theorem actualJoinedExponent_split (a : Fin (d+t) →₀ ℕ) :
    actualJoinedExponent (actualTangentExponent a) (actualNormalExponent a) = a := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [actualJoinedExponent,actualTangentExponent,actualNormalExponent]

/-- The true total normal degree, including an empty normal block. -/
def actualNormalDegree (γ : Fin t →₀ ℕ) : ℕ := ∑ i, γ i

/-- The selected tangent centre variables and ALL original normal variables. -/
def actualPresentationCentreVariables (A : Set (Fin d)) : Set (Fin (d+t)) :=
  {i | Fin.addCases (fun j => j ∈ A) (fun _ => True) i}

/-- The actual centre weight is the selected tangent weight plus total normal degree. -/
theorem actualJoinedExponent_centre_weight (A : Set (Fin d))
    (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (actualPresentationCentreVariables (t := t) A))
        (actualJoinedExponent β γ) =
      Finsupp.weight (actualCoordinateWeight A) β + actualNormalDegree γ := by
  rw [Finsupp.weight_eq_sum,Fin.sum_univ_add,Finsupp.weight_eq_sum]
  simp [actualJoinedExponent,actualCoordinateWeight,actualPresentationCentreVariables,
    actualNormalDegree,smul_eq_mul]

/-- Literal normal coefficients retain the entire formal tangent series. -/
def actualFormalNormalCoefficient (F : MvPowerSeries (Fin (d+t)) ℂ)
    (γ : Fin t →₀ ℕ) : MvPowerSeries (Fin d) ℂ :=
  fun β => MvPowerSeries.coeff (actualJoinedExponent β γ) F

/-- The actual whole centre power is equivalent to all genuine low normal coefficient powers. -/
theorem mem_actualPresentationCentre_power_iff
    (A : Set (Fin d)) (q : ℕ) (F : MvPowerSeries (Fin (d+t)) ℂ) :
    F ∈ actualFormalCoordinateIdeal (d+t) (actualPresentationCentreVariables A) ^ q ↔
      ∀ γ : Fin t →₀ ℕ, actualNormalDegree γ < q →
        actualFormalNormalCoefficient F γ ∈
          actualFormalCoordinateIdeal d A ^ (q - actualNormalDegree γ) := by
  constructor
  · intro hF γ hγ
    apply (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mpr
    intro β hβ
    change MvPowerSeries.coeff (actualJoinedExponent β γ) F = 0
    apply (mem_actualFormalCoordinateIdeal_pow_iff _ q F).mp hF
    rw [actualJoinedExponent_centre_weight]
    omega
  · intro hcoeff
    apply (mem_actualFormalCoordinateIdeal_pow_iff _ q F).mpr
    intro a ha
    let β := actualTangentExponent a
    let γ := actualNormalExponent a
    have he : actualJoinedExponent β γ = a := actualJoinedExponent_split a
    have hs : Finsupp.weight (actualCoordinateWeight A) β + actualNormalDegree γ < q := by
      rw [← actualJoinedExponent_centre_weight A β γ,he]
      exact ha
    have hγ : actualNormalDegree γ < q := by omega
    have hβ : Finsupp.weight (actualCoordinateWeight A) β < q - actualNormalDegree γ := by omega
    have hz := (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mp (hcoeff γ hγ) β hβ
    change MvPowerSeries.coeff (actualJoinedExponent β γ) F = 0 at hz
    rwa [he] at hz

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalIdeal HironakaRelativeNormalAnalyticGraphQuotient
  HironakaActualOriginalFormalTaylor HironakaHolomorphicJetMonomialSpan
  HolGerm GermIdealOrder IdealWeightPowers OkaRelationSheaf

/-- Actual functional coordinate-plane powers give the genuine whole original germ powers. -/
theorem mk_mem_normalIdeal_pow_of_functional_power (k s q : ℕ)
    {f : ComplexModel (k+s) → ℂ} (hf : HolAt f 0)
    (hmem : (idealPow (vanishingIdeal (n := k+s) (complexCoordinatePlane (k+s) k)) q).mem 0 f) :
    HolGerm.mk f hf ∈ normalIdeal k s ^ q := by
  induction q generalizing f with
  | zero => simp only [pow_zero,Ideal.one_eq_top,Submodule.mem_top]
  | succ q ih =>
      let S := fun g : ComplexModel (k+s) → ℂ => ∃ a b,
        (idealPow (vanishingIdeal (n := k+s) (complexCoordinatePlane (k+s) k)) q).mem 0 a ∧
        (vanishingIdeal (n := k+s) (complexCoordinatePlane (k+s) k)).mem 0 b ∧ g = a*b
      have hS : ∀ g, S g → HolAt g 0 := by
        rintro g ⟨a,b,ha,hb,rfl⟩
        exact eventually_differentiableAt_mul
          ((holomorphicAt_of_mem_idealPow ha).mono (fun _ h => h.differentiableAt))
          (hb.1.mono (fun _ h => h.differentiableAt))
      apply whole_origin_span_mem _ S hS ?_ hf (mem_idealPow_succ_iff.mp hmem)
      rintro g ⟨a,b,ha,hb,rfl⟩
      let hah : HolAt a 0 := (holomorphicAt_of_mem_idealPow ha).mono (fun _ h => h.differentiableAt)
      let hbh : HolAt b 0 := hb.1.mono (fun _ h => h.differentiableAt)
      have he : HolGerm.mk (a*b) (hS (a*b) ⟨a,b,ha,hb,rfl⟩) =
          HolGerm.mk a hah * HolGerm.mk b hbh := rfl
      rw [he,pow_succ]
      exact Ideal.mul_mem_mul (ih hah ha) ((mk_mem_normalIdeal_iff k s b hbh).mpr hb.2)

/-- The tangent-centre variables are the same original normal-coordinate indices. -/
def actualTangentCentreVariables (k s : ℕ) : Set (Fin (k+s)) :=
  Set.range (Fin.natAdd k : Fin s → Fin (k+s))

/-- The original Taylor homomorphism after the literal dimension equality `0+n=n`. -/
def actualUnshiftedTaylorAlgHom (n : ℕ) :
    HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ := by
  have h := originalTaylorAlgHom n
  rw [Nat.zero_add] at h
  exact h

/-- Reassociating the dimension leaves the original coordinate Taylor dictionary intact. -/
theorem actualUnshiftedTaylor_coordinate (n : ℕ) (i : Fin n) :
    actualUnshiftedTaylorAlgHom n (coordinateGerm i) = MvPowerSeries.X i := by
  have hc (m : ℕ) (e : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) :
      (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) e) f) (coordinateGerm i) =
        f (coordinateGerm (Fin.cast e.symm i)) := by
    subst m
    rfl
  change (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
    MvPowerSeries (Fin n) ℂ) (Nat.zero_add n)) (originalTaylorAlgHom n))
      (coordinateGerm i) = _
  rw [hc (0+n) (Nat.zero_add n)]
  simpa [normalCoordinate] using originalTaylorAlgHom_coordinate n i

/-- Genuine Taylor expansion sends every original normal coordinate to its literal formal variable. -/
theorem originalTaylor_normalCoordinate (k s : ℕ) (i : Fin s) :
    actualUnshiftedTaylorAlgHom (k+s) (normalCoordinate k s i) = MvPowerSeries.X (i.natAdd k) :=
  actualUnshiftedTaylor_coordinate (k+s) (i.natAdd k)

/-- BOTH entire coordinate-ideal directions follow from the actual coordinate generator dictionary. -/
theorem map_normalIdeal_originalTaylor (k s : ℕ) :
    Ideal.map (actualUnshiftedTaylorAlgHom (k+s)).toRingHom (normalIdeal k s) =
      actualFormalCoordinateIdeal (k+s) (actualTangentCentreVariables k s) := by
  rw [normalIdeal,Ideal.map_span,actualFormalCoordinateIdeal,actualTangentCentreVariables,
    ← Set.range_comp,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact originalTaylor_normalCoordinate k s i

/-- Actual functional plane-power membership internally supplies the whole formal coordinate-power bound. -/
theorem originalTaylor_mem_coordinate_power_of_functional_power (k s q : ℕ)
    {f : ComplexModel (k+s) → ℂ} (hf : HolAt f 0)
    (hmem : (idealPow (vanishingIdeal (n := k+s) (complexCoordinatePlane (k+s) k)) q).mem 0 f) :
    actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk f hf) ∈
      actualFormalCoordinateIdeal (k+s) (actualTangentCentreVariables k s) ^ q := by
  have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (k+s)).toRingHom
    (mk_mem_normalIdeal_pow_of_functional_power k s q hf hmem)
  rwa [Ideal.map_pow,map_normalIdeal_originalTaylor] at h

/-- Only genuine original coherent coefficient cosupports supply the ENTIRE formal centre power. -/
theorem mem_actualPresentationCentre_power_of_original_coefficient_cosupport
    (k s t q : ℕ) (F : MvPowerSeries (Fin ((k+s)+t)) ℂ)
    (c : (Fin t →₀ ℕ) → ComplexModel (k+s) → ℂ)
    (hc : ∀ γ, HolAt (c γ) 0)
    (A : (Fin t →₀ ℕ) → GermIdeal (k+s) (ComplexModel (k+s)))
    (hA : ∀ γ, actualNormalDegree γ < q → (A γ).IsCoherent)
    (hmem : ∀ γ, actualNormalDegree γ < q → (A γ).mem 0 (c γ))
    (hC : IsClosedSubmanifold (k+s) (complexCoordinatePlane (k+s) k))
    (hcosupp : ∀ γ, actualNormalDegree γ < q →
      complexCoordinatePlane (k+s) k ⊆
        cosupport (k+s) univ (A γ) (q-actualNormalDegree γ))
    (hcoeff : ∀ γ, actualNormalDegree γ < q → actualFormalNormalCoefficient F γ =
      actualUnshiftedTaylorAlgHom (k+s) (HolGerm.mk (c γ) (hc γ))) :
    F ∈ actualFormalCoordinateIdeal ((k+s)+t)
      (actualPresentationCentreVariables (actualTangentCentreVariables k s)) ^ q := by
  apply (mem_actualPresentationCentre_power_iff _ q F).mpr
  intro γ hγ
  rw [hcoeff γ hγ]
  apply originalTaylor_mem_coordinate_power_of_functional_power k s _ (hc γ)
  exact (HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport
    (hA γ hγ) hC (hcosupp γ hγ)) 0 (c γ) (hmem γ hγ)

end
end Hironaka.HironakaActualCoefficientPresentationCentrePower
