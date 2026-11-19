/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHolomorphicDualJetGeneration
import Hironaka.Resolution.HironakaActualDualJetProlongationHolomorphic

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualDualJetRaising
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

/-- Explicit next-frame coefficient FUNCTIONS evaluate the constructed prolongation on one fixed TRUE jet vector. -/
def actualDualJetRaisingCoefficient (d t q : ℕ)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) (q+1)) (a : ComplexModel d)
    (out : monomialIndex (d+t) (q+1)) (c : ComplexModel d) : ℂ :=
  actualDualGenerationCoefficient (d+t) (q+1) rows
    (fun c => (actualDualJetProlongation d t q η c a).comp
      (LinearMap.range (finiteJet (n := d+t) (q+1))).subtype) out c

/-- The genuine constructed next annihilator has explicit HOLOMORPHIC raising coefficients on the ENTIRE true next jet image. -/
theorem actual_dual_jet_holomorphic_raising (d t q : ℕ) {ι : Type*} [Fintype ι]
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
    (hzero : ∀ c ∈ (tangentInclusion d t) ⁻¹' D, ∀ i, G i (tangentInclusion d t c) = 0) :
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
    exact actualDualJetProlongation_whole_ideal_zero d t q hU G hG
      (hD.preimage (tangentInclusion d t).continuous) (fun _ hc => hDU hc)
      η hη hker c a hc (hzero c hc) g hg
  exact actual_holomorphic_true_jet_annihilator_generation d t (q+1) G rows cols hdet hrank
    (fun p hp => actual_family_holomorphicAt hU G hG p (hDU hp)) Λ hΛhol hΛ

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original proper HS-constant centre geometry internally gives generator vanishing, next pivots and true holomorphic raising at ALL orders. -/
theorem exists_original_hs_positive_centre_dual_jet_raising
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ)
    (hpos : 0 < hilbertSamuelAt A x 0) :
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
          (∀ c, tangentInclusion d t c ∈ U → ∀ i, H i (tangentInclusion d t c) = 0) ∧
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
    hMap, hH, hhol, hI, hHS, hRank, hFrames⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  have hpos0 : 0 < hilbertSamuelValue (translatedIdeal H 0 (hhol 0 h0U)) 0 := by
    rw [hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank,
      ← hHS 0 h0U 0, actualFlatteningInverseMap_zero x Φ h0]
    exact hpos
  have hproper : translatedIdeal H 0 (actual_family_holomorphicAt hU H hH 0 h0U) ≠ ⊤ :=
    (hilbertSamuelValue_zero_pos_iff_ne_top _).mp hpos0
  have hconstant : ∀ (c : ComplexModel d) (hc : tangentInclusion d t c ∈ U),
      hilbertSamuelValue (translatedIdeal H (tangentInclusion d t c)
        (actual_family_holomorphicAt hU H hH _ hc)) 0 =
      hilbertSamuelValue (translatedIdeal H 0 (actual_family_holomorphicAt hU H hH 0 h0U)) 0 := by
    intro c hc
    rw [hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank,
      hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank,
      hRank _ hc (tangentInclusion_mem_plane d t c) 0]
  have hzero := actual_hs_zero_constant_tangent_generators_vanish d t hU h0U H hH hproper hconstant
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, hzero, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, hk, D, hD, h0D, hDU, hV, h0V, hdet, _hP, _hK⟩ := hFrames (ℓ+1)
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, ?_⟩
  intro η a hη hDη hker
  have hr : ∀ c, tangentInclusion d t c ∈ D → Module.finrank ℂ (LinearMap.range
      (originalMacaulayLinearMap ((ℓ+1)+1) H (tangentInclusion d t c))) = k := by
    intro c hc
    exact (hRank _ (hDU hc) (tangentInclusion_mem_plane d t c) (ℓ+1)).trans hk.symm
  exact actual_dual_jet_holomorphic_raising d t (ℓ+1) hU hD H hH hDU rows cols hdet hr
    η a hη hDη hker (fun c hc => hzero c (hDU hc))

end OriginalCentre
end
end Hironaka.HironakaActualDualJetRaising
