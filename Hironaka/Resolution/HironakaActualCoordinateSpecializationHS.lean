/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHolomorphicFibreHS
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback
import Hironaka.Support.GenuineAmbientJetAlgEquivExact

/-! Genuine original coordinate contraction, before nonprincipal HS specialization. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCoordinateSpecializationHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualHolomorphicFibreHS
  HironakaSmoothSubmersionMonomialChartPullback HironakaSmoothCentreRealDomainActualAmbientHS

/-- The actual original coordinate map, retaining the entire unscaled second block. -/
def actualBlockContraction (r n : ℕ) (c : ℂ) (z : ComplexModel (r+n)) : ComplexModel (r+n) :=
  (splitCoordinates r n).symm (c • (splitCoordinates r n z).1,(splitCoordinates r n z).2)

/-- Genuine continuous complex linearity of the SAME original coordinate contraction. -/
def actualBlockContractionLinear (r n : ℕ) (c : ℂ) :
    ComplexModel (r+n) →L[ℂ] ComplexModel (r+n) :=
  (splitCoordinates r n).symm.toContinuousLinearMap.comp
    (((c • ContinuousLinearMap.fst ℂ (ComplexModel r) (ComplexModel n)).prod
      (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel n))).comp
        (splitCoordinates r n).toContinuousLinearMap)

/-- The actual linear map has exactly the displayed original two-block values. -/
theorem actualBlockContractionLinear_apply (r n : ℕ) (c : ℂ) (z : ComplexModel (r+n)) :
    actualBlockContractionLinear r n c z=actualBlockContraction r n c z := rfl

/-- Every true original contraction fixes the actual germ centre. -/
theorem actualBlockContraction_zero (r n : ℕ) (c : ℂ) : actualBlockContraction r n c 0=0 :=
  (actualBlockContractionLinear r n c).map_zero

/-- The SAME original coordinate function is genuinely holomorphic near its original zero centre. -/
theorem actualBlockContraction_holomorphic (r n : ℕ) (c : ℂ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (r+n)), DifferentiableAt ℂ (actualBlockContraction r n c) z :=
  Eventually.of_forall fun _ => (actualBlockContractionLinear r n c).differentiableAt

/-- Actual original contraction composition is multiplication of its two original parameters. -/
theorem actualBlockContraction_comp (r n : ℕ) (c μ : ℂ) (z : ComplexModel (r+n)) :
    actualBlockContraction r n c (actualBlockContraction r n μ z) =
      actualBlockContraction r n (c*μ) z := by
  simp only [actualBlockContraction,ContinuousLinearEquiv.apply_symm_apply,smul_smul]

/-- Parameter one is the actual original identity map. -/
theorem actualBlockContraction_one (r n : ℕ) (z : ComplexModel (r+n)) :
    actualBlockContraction r n 1 z=z := by
  simp only [actualBlockContraction,one_smul,Prod.mk.eta,ContinuousLinearEquiv.symm_apply_apply]

/-- The actual entire original germ pullback by the true coordinate map. -/
def actualBlockContractionGerm (r n : ℕ) (c : ℂ) :
    HolGerm (ComplexModel (r+n)) →ₐ[ℂ] HolGerm (ComplexModel (r+n)) :=
  compAlgHom (actualBlockContraction r n c)
    (actualBlockContraction_holomorphic r n c)
    (actualBlockContraction_zero r n c)

/-- EVERY original representative retains its genuine composition with the original coordinate map. -/
theorem actualBlockContractionGerm_mk (r n : ℕ) (c : ℂ) (F : ComplexModel (r+n) → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (r+n)), DifferentiableAt ℂ F z) :
    actualBlockContractionGerm r n c (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ actualBlockContraction r n c)
        (holomorphic_comp _ (actualBlockContraction_holomorphic r n c)
          (actualBlockContraction_zero r n c) hF) := rfl

/-- Whole original germ-map composition retains the contravariant actual coordinate order. -/
theorem actualBlockContractionGerm_comp (r n : ℕ) (c μ : ℂ) :
    (actualBlockContractionGerm r n c).comp (actualBlockContractionGerm r n μ) =
      actualBlockContractionGerm r n (μ*c) := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    change actualBlockContractionGerm r n c (actualBlockContractionGerm r n μ (HolGerm.mk F hF)) =
      actualBlockContractionGerm r n (μ*c) (HolGerm.mk F hF)
    rw [actualBlockContractionGerm_mk,actualBlockContractionGerm_mk,
      actualBlockContractionGerm_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (actualBlockContraction_comp r n μ c z)

/-- Parameter one induces the genuine identity on ALL original germs. -/
theorem actualBlockContractionGerm_one (r n : ℕ) :
    actualBlockContractionGerm r n 1=AlgHom.id ℂ (HolGerm (ComplexModel (r+n))) := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    change actualBlockContractionGerm r n 1 (HolGerm.mk F hF)=HolGerm.mk F hF
    rw [actualBlockContractionGerm_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg F (actualBlockContraction_one r n z)

/-- Nonzero original parameters supply actual two-sided coordinate inverses before a whole algebra equivalence. -/
def actualBlockContractionGermEquiv (r n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    HolGerm (ComplexModel (r+n)) ≃ₐ[ℂ] HolGerm (ComplexModel (r+n)) := by
  apply AlgEquiv.ofAlgHom (actualBlockContractionGerm r n c) (actualBlockContractionGerm r n c⁻¹)
  · rw [actualBlockContractionGerm_comp,inv_mul_cancel₀ hc,actualBlockContractionGerm_one]
  · rw [actualBlockContractionGerm_comp,mul_inv_cancel₀ hc,actualBlockContractionGerm_one]

/-- The genuine inverse construction has the SAME actual original forward germ map. -/
theorem actualBlockContractionGermEquiv_apply (r n : ℕ) (c : ℂ) (hc : c ≠ 0)
    (g : HolGerm (ComplexModel (r+n))) :
    actualBlockContractionGermEquiv r n c hc g=actualBlockContractionGerm r n c g := rfl

/-- Every EXISTING original whole-ideal HS value is retained for each actual nonzero parameter. -/
theorem hilbertSamuelValue_actual_contraction_nonzero (r n : ℕ) (c : ℂ) (hc : c ≠ 0)
    (I : Ideal (HolGerm (ComplexModel (r+n)))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualBlockContractionGerm r n c).toRingHom I) ℓ =
      hilbertSamuelValue I ℓ :=
  actualAmbientHS_eq_of_genuineAlgEquiv (actualBlockContractionGermEquiv r n c hc) I ℓ

/-- Parameter zero sets exactly the FIRST original block to zero. -/
theorem actualBlockContraction_parameter_zero (r n : ℕ) (z : ComplexModel (r+n)) :
    actualBlockContraction r n 0 z=joinCoordinates r n 0 (blockProjection r n z) := by
  simp only [actualBlockContraction,zero_smul,joinCoordinates,blockProjection]

/-- The genuine jointly varying original contraction on the ACTUAL one-parameter model. -/
theorem actualContractionJoint_contDiff (r n : ℕ) :
    ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (r+n) =>
      actualBlockContraction r n (u.1 0) u.2) := by
  have hp : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (r+n) => u.1 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.comp contDiff_fst
  have hs : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (r+n) => splitCoordinates r n u.2) :=
    (splitCoordinates r n).contDiff.comp contDiff_snd
  exact (splitCoordinates r n).symm.contDiff.comp
    ((hp.smul (contDiff_fst.comp hs)).prodMk (contDiff_snd.comp hs))

/-- The REAL joint domain uses only the common original holomorphic neighbourhood. -/
def actualContractionDomain (r n : ℕ) (U : Set (ComplexModel (r+n))) :
    Set (ComplexModel 1 × ComplexModel (r+n)) :=
  (fun u => actualBlockContraction r n (u.1 0) u.2) ⁻¹' U

/-- The actual joint polynomial map gives true openness of that same original domain. -/
theorem isOpen_actualContractionDomain (r n : ℕ) {U : Set (ComplexModel (r+n))} (hU : IsOpen U) :
    IsOpen (actualContractionDomain r n U) := hU.preimage (actualContractionJoint_contDiff r n).continuous

/-- EVERY original parameter-axis point lies in the SAME genuine joint domain. -/
theorem axis_mem_actualContractionDomain (r n : ℕ) {U : Set (ComplexModel (r+n))}
    (h0 : (0 : ComplexModel (r+n)) ∈ U) (p : ComplexModel 1) :
    (p,0) ∈ actualContractionDomain r n U := by
  change actualBlockContraction r n (p 0) 0 ∈ U
  rwa [actualBlockContraction_zero]

/-- The actual original finite generators composed with the true jointly varying coordinate map. -/
def actualContractionFamily (r n : ℕ) {s : ℕ} (G : Fin s → ComplexModel (r+n) → ℂ)
    (i : Fin s) (u : ComplexModel 1 × ComplexModel (r+n)) : ℂ :=
  G i (actualBlockContraction r n (u.1 0) u.2)

/-- Original holomorphicity on ONE original neighbourhood gives the real joint holomorphic family. -/
theorem differentiableOn_actualContractionFamily (r n : ℕ) {U : Set (ComplexModel (r+n))}
    (hU : IsOpen U) {s : ℕ} (G : Fin s → ComplexModel (r+n) → ℂ)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (i : Fin s) :
    DifferentiableOn ℂ (actualContractionFamily r n G i) (actualContractionDomain r n U) := by
  intro u hu
  exact (((hG i).differentiableAt (hU.mem_nhds hu)).comp u
    ((actualContractionJoint_contDiff r n).differentiable (by simp)).differentiableAt).differentiableWithinAt

private theorem originalGenerator_holomorphic {a : ℕ} {U : Set (ComplexModel a)}
    (hU : IsOpen U) (h0 : (0 : ComplexModel a) ∈ U) {F : ComplexModel a → ℂ}
    (hF : DifferentiableOn ℂ F U) : ∀ᶠ z in 𝓝 (0 : ComplexModel a), DifferentiableAt ℂ F z := by
  filter_upwards [hU.mem_nhds h0] with z hz
  exact hF.differentiableAt (hU.mem_nhds hz)

/-- BOTH ENTIRE fibre-ideal directions retain the image of the SAME original finite ideal span. -/
theorem actualContractionFibreIdeal_eq_map_original_span (r n : ℕ) {U : Set (ComplexModel (r+n))}
    (hU : IsOpen U) (h0 : (0 : ComplexModel (r+n)) ∈ U) {s : ℕ}
    (G : Fin s → ComplexModel (r+n) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U) (p : ComplexModel 1) :
    actualFibreIdeal (isOpen_actualContractionDomain r n hU) (actualContractionFamily r n G)
      (differentiableOn_actualContractionFamily r n hU G hG) p (axis_mem_actualContractionDomain r n h0 p) =
      Ideal.map (actualBlockContractionGerm r n (p 0)).toRingHom
        (Ideal.span (range fun i => HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))) := by
  rw [actualFibreIdeal_eq_original_span,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [Function.comp_apply]
  change _ = actualBlockContractionGerm r n (p 0)
    (HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))
  rw [actualBlockContractionGerm_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => rfl

/-- ANY original ideal internally receives actual original representatives on ONE real neighbourhood. -/
theorem exists_original_contraction_generators (r n : ℕ) (I : Ideal (HolGerm (ComplexModel (r+n)))) :
    ∃ (U : Set (ComplexModel (r+n))) (hU : IsOpen U) (h0 : (0 : ComplexModel (r+n)) ∈ U)
      (s : ℕ) (G : Fin s → ComplexModel (r+n) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U),
      Ideal.span (range fun i => HolGerm.mk (G i) (originalGenerator_holomorphic hU h0 (hG i)))=I := by
  obtain ⟨s,G,hG,hI,_⟩ := exists_original_generators_jet_columns I
  choose V hV hVo h0V using fun i => eventually_nhds_iff.mp (hG i)
  let U : Set (ComplexModel (r+n)) := ⋂ i, V i
  have hU : IsOpen U := isOpen_iInter_of_finite hVo
  have h0 : (0 : ComplexModel (r+n)) ∈ U := mem_iInter.mpr h0V
  have hGon (i : Fin s) : DifferentiableOn ℂ (G i) U := fun z hz =>
    (hV i z (mem_iInter.mp hz i)).differentiableWithinAt
  exact ⟨U,hU,h0,s,G,hGon,hI⟩

private def contractionParameterPoint (c : ℂ) : ComplexModel 1 :=
  c • (EuclideanSpace.basisFun (Fin 1) ℂ) 0

private theorem contractionParameterPoint_coordinate (c : ℂ) : contractionParameterPoint c 0=c := by
  simp [contractionParameterPoint]

private theorem continuous_contractionParameterPoint : Continuous contractionParameterPoint :=
  continuous_id.smul continuous_const

/-- EVERY original ideal has every actual intrinsic HS value bounded by its TRUE zero-coordinate specialization. -/
theorem hilbertSamuelValue_actual_coordinate_specialization (r n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (r+n)))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ ≤
      hilbertSamuelValue (Ideal.map (actualBlockContractionGerm r n 0).toRingHom I) ℓ := by
  obtain ⟨U,hU,h0,s,G,hG,hI⟩ := exists_original_contraction_generators r n I
  let D := actualContractionDomain r n U
  have hD : IsOpen D := isOpen_actualContractionDomain r n hU
  let F := actualContractionFamily r n G
  have hF : ∀ i, DifferentiableOn ℂ (F i) D := differentiableOn_actualContractionFamily r n hU G hG
  have haxis (p : ComplexModel 1) : (p,0) ∈ D := axis_mem_actualContractionDomain r n h0 p
  let J (c : ℂ) := actualFibreIdeal hD F hF (contractionParameterPoint c) (haxis (contractionParameterPoint c))
  have hdict (c : ℂ) : J c=Ideal.map (actualBlockContractionGerm r n c).toRingHom I := by
    have h := actualContractionFibreIdeal_eq_map_original_span r n hU h0 G hG (contractionParameterPoint c)
    rw [hI,contractionParameterPoint_coordinate] at h
    exact h
  let P : ℂ → (⊤ : TopologicalSpace.Opens (ComplexModel 1)) :=
    fun c => ⟨contractionParameterPoint c,mem_univ _⟩
  have hP : Continuous P := by
    apply Continuous.subtype_mk
    exact continuous_contractionParameterPoint
  have hclosed : IsClosed {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    exact (isClosed_actualFibreHS_superlevel hD F hF ⊤ (fun p _ => haxis p) ℓ
      (hilbertSamuelValue I ℓ)).preimage hP
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {c : ℂ | hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J c) ℓ
    rw [hdict c,hilbertSamuelValue_actual_contraction_nonzero r n c hc0]
  have hz := closure_minimal hsub hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change hilbertSamuelValue I ℓ ≤ hilbertSamuelValue (J 0) ℓ at hz
  rwa [hdict 0] at hz
end
end Hironaka.HironakaActualCoordinateSpecializationHS
