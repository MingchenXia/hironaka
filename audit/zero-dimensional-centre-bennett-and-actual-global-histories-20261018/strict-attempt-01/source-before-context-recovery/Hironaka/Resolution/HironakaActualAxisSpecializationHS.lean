/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAxisContraction

/-! All-order intrinsic HS comparison for the genuine original one-coordinate contraction. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAxisSpecializationHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualHolomorphicFibreHS
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaActualAxisContraction
variable {n : ℕ}

/-- Genuine nonzero coordinate inverses preserve every intrinsic original whole-ideal HS value. -/
theorem hilbertSamuelValue_actual_axis_nonzero (e : Fin n) (c : ℂ) (hc : c ≠ 0)
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualAxisContractionGerm e c).toRingHom I) ℓ =
      hilbertSamuelValue I ℓ :=
  actualAmbientHS_eq_of_genuineAlgEquiv (actualAxisContractionGermEquiv e c hc) I ℓ

/-- The true joint domain is the preimage of the original common holomorphic neighbourhood. -/
def actualAxisContractionDomain (e : Fin n) (U : Set (ComplexModel n)) :
    Set (ComplexModel 1 × ComplexModel n) :=
  (fun u => actualAxisContraction e (u.1 0) u.2) ⁻¹' U

/-- Genuine joint holomorphicity supplies actual openness of the real domain. -/
theorem isOpen_actualAxisContractionDomain (e : Fin n) {U : Set (ComplexModel n)}
    (hU : IsOpen U) : IsOpen (actualAxisContractionDomain e U) :=
  hU.preimage (actualAxisContractionJoint_contDiff e).continuous

/-- Every true parameter-axis point belongs to the same actual joint domain. -/
theorem axis_mem_actualAxisContractionDomain (e : Fin n) {U : Set (ComplexModel n)}
    (h0 : (0 : ComplexModel n) ∈ U) (p : ComplexModel 1) :
    (p,0) ∈ actualAxisContractionDomain e U := by
  change actualAxisContraction e (p 0) 0 ∈ U
  rwa [map_zero]

/-- The actual original generators composed with the genuine varying coordinate map. -/
def actualAxisContractionFamily (e : Fin n) {s : ℕ} (G : Fin s → ComplexModel n → ℂ)
    (i : Fin s) (u : ComplexModel 1 × ComplexModel n) : ℂ :=
  G i (actualAxisContraction e (u.1 0) u.2)

/-- Holomorphicity on one original neighbourhood yields the real joint holomorphic family. -/
theorem differentiableOn_actualAxisContractionFamily (e : Fin n) {U : Set (ComplexModel n)}
    (hU : IsOpen U) {s : ℕ} (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (i : Fin s) :
    DifferentiableOn ℂ (actualAxisContractionFamily e G i) (actualAxisContractionDomain e U) := by
  intro u hu
  exact (((hG i).differentiableAt (hU.mem_nhds hu)).comp u
    ((actualAxisContractionJoint_contDiff e).differentiable (by simp)).differentiableAt).differentiableWithinAt

private theorem originalGenerator_holomorphic {U : Set (ComplexModel n)}
    (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U) {F : ComplexModel n → ℂ}
    (hF : DifferentiableOn ℂ F U) : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z := by
  filter_upwards [hU.mem_nhds h0] with z hz
  exact hF.differentiableAt (hU.mem_nhds hz)

/-- Both whole fibre-ideal directions identify exactly the original finite ideal span image. -/
theorem actualAxisContractionFibreIdeal_eq_map_original_span (e : Fin n)
    {U : Set (ComplexModel n)} (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U) {s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (p : ComplexModel 1) :
    actualFibreIdeal (isOpen_actualAxisContractionDomain e hU) (actualAxisContractionFamily e G)
      (differentiableOn_actualAxisContractionFamily e hU G hG) p (axis_mem_actualAxisContractionDomain e h0 p) =
      Ideal.map (actualAxisContractionGerm e (p 0)).toRingHom
        (Ideal.span (range fun i => HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))) := by
  rw [actualFibreIdeal_eq_original_span,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rfl

private theorem exists_original_axis_generators (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ (U : Set (ComplexModel n)) (hU : IsOpen U) (h0 : (0 : ComplexModel n) ∈ U)
      (s : ℕ) (G : Fin s → ComplexModel n → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U),
      Ideal.span (range fun i => HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))=I := by
  obtain ⟨s,G,hG,hI,_⟩ := exists_original_generators_jet_columns I
  choose V hV hVo h0V using fun i => eventually_nhds_iff.mp (hG i)
  let U : Set (ComplexModel n) := ⋂ i, V i
  have hU : IsOpen U := isOpen_iInter_of_finite hVo
  have h0 : (0 : ComplexModel n) ∈ U := mem_iInter.mpr h0V
  have hGon (i : Fin s) : DifferentiableOn ℂ (G i) U := fun z hz =>
    (hV i z (mem_iInter.mp hz i)).differentiableWithinAt
  exact ⟨U,hU,h0,s,G,hGon,hI⟩

private def axisParameterPoint (c : ℂ) : ComplexModel 1 :=
  c • (EuclideanSpace.basisFun (Fin 1) ℂ) 0

private theorem axisParameterPoint_coordinate (c : ℂ) : axisParameterPoint c 0=c := by
  simp [axisParameterPoint]

private theorem continuous_axisParameterPoint : Continuous axisParameterPoint :=
  continuous_id.smul continuous_const

/-- Every original ideal has every intrinsic HS value bounded by its actual axis-zero specialization. -/
theorem hilbertSamuelValue_actual_axis_specialization (e : Fin n)
    (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ ≤
      hilbertSamuelValue (Ideal.map (actualAxisContractionGerm e 0).toRingHom I) ℓ := by
  obtain ⟨U,hU,h0,s,G,hG,hI⟩ := exists_original_axis_generators I
  let D := actualAxisContractionDomain e U
  have hD : IsOpen D := isOpen_actualAxisContractionDomain e hU
  let F := actualAxisContractionFamily e G
  have hF : ∀ i, DifferentiableOn ℂ (F i) D := differentiableOn_actualAxisContractionFamily e hU G hG
  have haxis (p : ComplexModel 1) : (p,0) ∈ D := axis_mem_actualAxisContractionDomain e h0 p
  let J (c : ℂ) := actualFibreIdeal hD F hF (axisParameterPoint c) (haxis (axisParameterPoint c))
  have hdict (c : ℂ) : J c=Ideal.map (actualAxisContractionGerm e c).toRingHom I := by
    have h := actualAxisContractionFibreIdeal_eq_map_original_span e hU h0 G hG (axisParameterPoint c)
    rw [hI,axisParameterPoint_coordinate] at h
    exact h
  let P : ℂ → (⊤ : TopologicalSpace.Opens (ComplexModel 1)) :=
    fun c => ⟨axisParameterPoint c,mem_univ _⟩
  have hP : Continuous P := by
    apply Continuous.subtype_mk
    exact continuous_axisParameterPoint
  have hclosed : IsClosed {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    exact (isClosed_actualFibreHS_superlevel hD F hF ⊤ (fun p _ => haxis p) ℓ
      (hilbertSamuelValue I ℓ)).preimage hP
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ
    rw [hdict c,hilbertSamuelValue_actual_axis_nonzero e c hc0]
  have hz := closure_minimal hsub hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J 0) ℓ at hz
  rwa [hdict 0] at hz

end
end Hironaka.HironakaActualAxisSpecializationHS
