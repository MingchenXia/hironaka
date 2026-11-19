/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualDualJetRaising
import Hironaka.Resolution.HironakaActualDualJetProlongationUnit
import Hironaka.Resolution.HironakaActualHolomorphicDualJetGeneration
import Hironaka.Resolution.HironakaActualDualJetProlongationHolomorphic

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualUnconditionalDualJetRaising
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreDualJetConnection
  HironakaActualHolomorphicDualJetGeneration HironakaActualDualJetProlongation
  HironakaActualDualJetProlongationHolomorphic HironakaActualHSZeroCentreVanishing

open HironakaActualDualJetRaising HironakaActualDualJetProlongationUnit

/-- A genuinely nonzero actual generator forces the ENTIRE SAME original translated ideal to be the unit ideal. -/
theorem actual_translatedIdeal_eq_top_of_generator_ne_zero {n : ℕ} {ι : Type*}
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n) (hGp : ∀ i, HolAt (G i) p)
    (i : ι) (hi : G i p ≠ 0) : translatedIdeal G p hGp = ⊤ := by
  by_contra hproper
  have hm : translatedGerm p (G i) (hGp i) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) :=
    IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span ⟨i, rfl⟩)
  have hz := (HolGerm.mem_maximalIdeal_iff _).mp hm
  exact hi (by simpa [translatedGerm, HolGerm.eval_mk] using hz)

/-- Genuine holomorphic continuity internally produces an OPEN unit-ideal neighborhood for the same original family. -/
theorem exists_actual_tangent_unit_ideal_neighborhood (d t : ℕ) {ι : Type*}
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    {V : Set (ComplexModel d)} (hV : IsOpen V)
    (hVU : ∀ c ∈ V, tangentInclusion d t c ∈ U)
    (c : ComplexModel d) (hc : c ∈ V) (i : ι) (hi : G i (tangentInclusion d t c) ≠ 0) :
    ∃ Z : Set (ComplexModel d), IsOpen Z ∧ c ∈ Z ∧ ∃ hZV : Z ⊆ V,
      ∀ b (hb : b ∈ Z), translatedIdeal G (tangentInclusion d t b)
        (actual_family_holomorphicAt hU G hG _ (hVU b (hZV hb))) = ⊤ := by
  let f : ComplexModel d → ℂ := fun b => G i (tangentInclusion d t b)
  let Z : Set (ComplexModel d) := V ∩ f ⁻¹' ({0} : Set ℂ)ᶜ
  have hF : DifferentiableOn ℂ f V :=
    (hG i).comp (tangentInclusion d t).differentiable.differentiableOn hVU
  have hZ : IsOpen Z := hF.continuousOn.isOpen_inter_preimage hV isClosed_singleton.isOpen_compl
  refine ⟨Z, hZ, ⟨hc, hi⟩, inter_subset_left, ?_⟩
  intro b hb
  exact actual_translatedIdeal_eq_top_of_generator_ne_zero G _
    (actual_family_holomorphicAt hU G hG _ (hVU b hb.1)) i hb.2

/-- No generator-vanishing or properness input: the ACTUAL constructed prolongation kills the ENTIRE original next ideal jet. -/
theorem actualDualJetProlongation_whole_ideal_zero_unconditional (d t q : ℕ) {ι : Type*} [Fintype ι]
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    {V : Set (ComplexModel d)} (hV : IsOpen V)
    (hVU : ∀ c ∈ V, tangentInclusion d t c ∈ U)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ)
    (hη : ∀ row, DifferentiableOn ℂ (η row) V)
    (hker : ∀ c ∈ V, ∀ col, ∑ row, η row c *
      originalMacaulayMatrix q G (tangentInclusion d t c) row col = 0)
    (c a : ComplexModel d) (hc : c ∈ V) (g : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ (hVU c hc))) :
    actualDualJetProlongation d t q η c a (finiteJet (q+1) g) = 0 := by
  by_cases hz : ∀ i, G i (tangentInclusion d t c) = 0
  · exact actualDualJetProlongation_whole_ideal_zero d t q hU G hG hV hVU η hη hker c a hc hz g hg
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    obtain ⟨Z, hZ, hcZ, hZV, htop⟩ :=
      exists_actual_tangent_unit_ideal_neighborhood d t hU G hG hV hVU c hc i hi
    exact actualDualJetProlongation_zero_of_translatedIdeal_eq_top d t q hU G hG hZ
      (fun b hb => hVU b (hZV hb)) η (fun row => (hη row).mono hZV)
      (fun b hb => hker b (hZV hb)) htop c a hcZ ⟨finiteJet (q+1) g, g, rfl⟩

/-- The genuine constructed next annihilator has explicit HOLOMORPHIC raising coefficients on the ENTIRE true next jet image. -/
theorem actual_dual_jet_holomorphic_raising_unconditional (d t q : ℕ) {ι : Type*} [Fintype ι]
    {U D : Set (ComplexModel (d+t))} (hU : IsOpen U) (hD : IsOpen D)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    (hDU : D ⊆ U) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) (q+1))
    (cols : Fin k → monomialIndex (d+t) (q+1) × ι)
    (hdet : ∀ p ∈ D, (pivotMatrix (q+1) G rows cols p).det ≠ 0)
    (hrank : ∀ c, tangentInclusion d t c ∈ D → Module.finrank ℂ
      (LinearMap.range (originalMacaulayLinearMap (q+1) G (tangentInclusion d t c))) = k)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ) (a : ComplexModel d)
    (hη : ∀ row, DifferentiableOn ℂ (η row) ((tangentInclusion d t) ⁻¹' D))
    (hDη : ∀ row, DifferentiableOn ℂ (fun c => fderiv ℂ (η row) c a) ((tangentInclusion d t) ⁻¹' D))
    (hker : ∀ c ∈ (tangentInclusion d t) ⁻¹' D, ∀ col,
      ∑ row, η row c * originalMacaulayMatrix q G (tangentInclusion d t c) row col = 0)
    :
    (∀ out, DifferentiableOn ℂ (actualDualJetRaisingCoefficient d t q η rows a out)
      ((tangentInclusion d t) ⁻¹' D)) ∧
    ∀ c, tangentInclusion d t c ∈ D → ∀ v : LinearMap.range (finiteJet (n := d+t) (q+1)),
      actualDualJetProlongation d t q η c a v.val =
        ∑ out, actualDualJetRaisingCoefficient d t q η rows a out c *
          (∑ row, actualProjectedDualRow d t (q+1) G rows cols out row c *
            finiteCoordinateArray (q+1) v.val row) := by
  let Λ : ComplexModel d → (LinearMap.range (finiteJet (n := d+t) (q+1)) →ₗ[ℂ] ℂ) :=
    fun c => (actualDualJetProlongation d t q η c a).comp
      (LinearMap.range (finiteJet (n := d+t) (q+1))).subtype
  have hΛhol : ∀ v, DifferentiableOn ℂ (fun c => Λ c v) ((tangentInclusion d t) ⁻¹' D) :=
    fun v => actualDualJetProlongation_holomorphic_fixed_jet d t q η a hη hDη v
  have hΛ : ∀ c (hc : tangentInclusion d t c ∈ D),
      ∀ g ∈ translatedIdeal G (tangentInclusion d t c)
        (actual_family_holomorphicAt hU G hG _ (hDU hc)),
        Λ c ((finiteJet (q+1)).rangeRestrict g) = 0 := by
    intro c hc g hg
    exact actualDualJetProlongation_whole_ideal_zero_unconditional d t q hU G hG
      (hD.preimage (tangentInclusion d t).continuous) (fun _ hc => hDU hc)
      η hη hker c a hc g hg
  exact actual_holomorphic_true_jet_annihilator_generation d t (q+1) G rows cols hdet hrank
    (fun p hp => actual_family_holomorphicAt hU G hG p (hDU hp)) Λ hΛhol hΛ

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original HS-constant centre geometry internally gives unconditional true holomorphic raising at ALL orders. -/
theorem exists_original_hs_constant_centre_unconditional_dual_jet_raising
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i, DifferentiableOn ℂ (H i) U) ∧
        ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
          (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
              translatedIdeal H p (hhol p hp)) ∧
          ∀ ℓ : ℕ, ∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) ((ℓ+1)+1))
            (cols : Fin k → monomialIndex (d+t) ((ℓ+1)+1) × Fin N)
            (D : Set (ComplexModel (d+t))), IsOpen D ∧ (0 : ComplexModel (d+t)) ∈ D ∧
            ∃ _hDU : D ⊆ U,
            (∀ p ∈ D, (pivotMatrix ((ℓ+1)+1) H rows cols p).det ≠ 0) ∧
            let V := (tangentInclusion d t) ⁻¹' D
            IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧
            ∀ (η : monomialIndex (d+t) (ℓ+1) → ComplexModel d → ℂ) (a : ComplexModel d),
              (∀ row, DifferentiableOn ℂ (η row) V) →
              (∀ row, DifferentiableOn ℂ (fun c => fderiv ℂ (η row) c a) V) →
              (∀ c ∈ V, ∀ col, ∑ row, η row c *
                originalMacaulayMatrix (ℓ+1) H (tangentInclusion d t c) row col = 0) →
              (∀ out, DifferentiableOn ℂ (actualDualJetRaisingCoefficient d t (ℓ+1) η rows a out) V) ∧
              ∀ c, c ∈ V → ∀ v : LinearMap.range (finiteJet (n := d+t) ((ℓ+1)+1)),
                actualDualJetProlongation d t (ℓ+1) η c a v.val =
                  ∑ out, actualDualJetRaisingCoefficient d t (ℓ+1) η rows a out c *
                    (∑ row, actualProjectedDualRow d t ((ℓ+1)+1) H rows cols out row c *
                      finiteCoordinateArray ((ℓ+1)+1) v.val row) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, hFrames⟩ :=
    exists_original_hs_constant_centre_holomorphic_dual_generation C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, hGen⟩ := hFrames (ℓ+1)
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, ?_⟩
  intro η a hη hDη hker
  let Λ : ComplexModel d → (LinearMap.range (finiteJet (n := d+t) ((ℓ+1)+1)) →ₗ[ℂ] ℂ) :=
    fun c => (actualDualJetProlongation d t (ℓ+1) η c a).comp
      (LinearMap.range (finiteJet (n := d+t) ((ℓ+1)+1))).subtype
  have hΛhol : ∀ v, DifferentiableOn ℂ (fun c => Λ c v) ((tangentInclusion d t) ⁻¹' D) :=
    fun v => actualDualJetProlongation_holomorphic_fixed_jet d t (ℓ+1) η a hη hDη v
  have hΛ : ∀ c (hc : tangentInclusion d t c ∈ D),
      ∀ g ∈ translatedIdeal H (tangentInclusion d t c) (hhol _ (hDU hc)),
        Λ c ((finiteJet ((ℓ+1)+1)).rangeRestrict g) = 0 := by
    intro c hc g hg
    exact actualDualJetProlongation_whole_ideal_zero_unconditional d t (ℓ+1) hU H hH hV
      (fun _ hc => hDU hc) η hη hker c a hc g hg
  exact hGen Λ hΛhol hΛ

end OriginalCentre
end
end Hironaka.HironakaActualUnconditionalDualJetRaising
