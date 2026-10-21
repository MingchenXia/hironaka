/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantCentreJetFrames
import Hironaka.Resolution.HironakaActualMacaulayAnnihilatorConnection
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreDualJetConnection
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualMacaulayAnnihilatorConnection

/-- Specified actual coefficient functions of the unchanged original pivot projection. -/
def actualProjectedDualRow (d t q : ℕ) {ι : Type*}
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    (out row : monomialIndex (d+t) q) (c : ComplexModel d) : ℂ :=
  pivotProjection q G rows cols (tangentInclusion d t c) (Pi.single row 1) out

/-- Actual basis decomposition proves the whole-array dual pairing without word-coordinate independence. -/
theorem actualProjectedDualRow_pairing (d t q : ℕ) {ι : Type*}
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    (out : monomialIndex (d+t) q) (c : ComplexModel d)
    (v : monomialIndex (d+t) q → ℂ) :
    (∑ row, actualProjectedDualRow d t q G rows cols out row c * v row)=
      pivotProjection q G rows cols (tangentInclusion d t c) v out := by
  have hv := pi_eq_sum_univ' v
  have hp := congrArg (fun w => pivotProjection q G rows cols (tangentInclusion d t c) w out) hv
  rw [map_sum] at hp
  simpa [actualProjectedDualRow, map_smul, Finset.sum_apply, smul_eq_mul, mul_comm] using hp.symm

/-- The true projected dual coefficients are holomorphic on their actual tangent preimage domain. -/
theorem actualProjectedDualRow_holomorphic (d t q : ℕ) {ι : Type*}
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    {U D : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (hDU : D ⊆ U)
    (hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0)
    (out row : monomialIndex (d+t) q) :
    DifferentiableOn ℂ (actualProjectedDualRow d t q G rows cols out row)
      ((tangentInclusion d t) ⁻¹' D) := by
  have h := pivotProjection_holomorphic_entries q G rows cols hU hG hDU hdet (Pi.single row 1) out
  exact h.comp (tangentInclusion d t).differentiable.differentiableOn (fun _ hc => hc)

/-- Actual first derivatives of these specified coefficients are holomorphic on the SAME real tangent domain. -/
theorem actualProjectedDualRow_fderiv_holomorphic (d t q : ℕ) {ι : Type*}
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    {U D : Set (ComplexModel (d+t))} (hU : IsOpen U) (hD : IsOpen D)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (hDU : D ⊆ U)
    (hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0)
    (out row : monomialIndex (d+t) q) (a : ComplexModel d) :
    DifferentiableOn ℂ (fun c => fderiv ℂ
      (actualProjectedDualRow d t q G rows cols out row) c a)
      ((tangentInclusion d t) ⁻¹' D) := by
  have hhol := actualProjectedDualRow_holomorphic d t q G rows cols hU hG hDU hdet out row
  have hV := hD.preimage (tangentInclusion d t).continuous
  intro c hc
  have hAn := HolomorphicAnalytic.analyticAt_of_differentiableOn hV hhol hc
  exact (((ContinuousLinearMap.apply ℂ ℂ a).analyticAt _).comp hAn.fderiv).differentiableAt.differentiableWithinAt

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original geometry internally generates actual dual rows, their true derivative functions and their genuine successor connection. -/
theorem exists_original_hs_constant_centre_dual_jet_connection
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
          ∀ ℓ : ℕ, ∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) (ℓ+1))
            (cols : Fin k → monomialIndex (d+t) (ℓ+1) × Fin N)
            (D : Set (ComplexModel (d+t))), IsOpen D ∧ (0 : ComplexModel (d+t)) ∈ D ∧
            ∃ hDU : D ⊆ U, ∃ _hdet : ∀ p ∈ D, (pivotMatrix (ℓ+1) H rows cols p).det ≠ 0,
            let V := (tangentInclusion d t) ⁻¹' D
            let η := actualProjectedDualRow d t (ℓ+1) H rows cols
            IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧
            (∀ out row, DifferentiableOn ℂ (η out row) V) ∧
            (∀ out row a, DifferentiableOn ℂ (fun c => fderiv ℂ (η out row) c a) V) ∧
            (∀ c ∈ V, ∀ out col, ∑ row, η out row c *
              originalMacaulayMatrix (ℓ+1) H (tangentInclusion d t c) row col = 0) ∧
            (∀ c (hc : c ∈ V) (g : HolGerm (ComplexModel (d+t))),
              (∀ out, ∑ row, η out row c * scalarJet (ℓ+1) g row = 0) ↔
                g ∈ translatedIdeal H (tangentInclusion d t c) (hhol _ (hDU hc)) ⊔
                  IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1)) ∧
            ∀ out col c a, c ∈ V →
              ∑ row : monomialIndex (d+t) (ℓ+1),
                (fderiv ℂ (η out row) c a *
                    originalMacaulayMatrix (ℓ+1) H (tangentInclusion d t c) row col +
                  η out row c * iteratedFDeriv ℂ (row.1.val+1)
                    (fun z => wordFunction col.1 z * H col.2 (z+tangentInclusion d t c)) 0
                    (Fin.cons (tangentInclusion d t a)
                      (fun j => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 j)))) = 0 := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hHS, _hRank, hFrames⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, _hk, D, hD, h0D, hDU, hV, h0V, hdet, _hP, hK⟩ := hFrames ℓ
  let V := (tangentInclusion d t) ⁻¹' D
  let η := actualProjectedDualRow d t (ℓ+1) H rows cols
  have hη (out row : monomialIndex (d+t) (ℓ+1)) : DifferentiableOn ℂ (η out row) V :=
    actualProjectedDualRow_holomorphic d t (ℓ+1) H rows cols hU hH hDU hdet out row
  have hηker : ∀ c ∈ V, ∀ out col, ∑ row, η out row c *
      originalMacaulayMatrix (ℓ+1) H (tangentInclusion d t c) row col = 0 := by
    intro c hc out col
    have him : (fun row => originalMacaulayMatrix (ℓ+1) H (tangentInclusion d t c) row col) ∈
        LinearMap.range (originalMacaulayLinearMap (ℓ+1) H (tangentInclusion d t c)) := by
      rw [originalMacaulayLinearMap, Fintype.range_linearCombination]
      exact Submodule.subset_span ⟨col, rfl⟩
    rw [← (hK _ hc (tangentInclusion_mem_plane d t c)).1] at him
    have hz := LinearMap.mem_ker.mp him
    rw [actualProjectedDualRow_pairing]
    exact congrFun hz out
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, hη, ?_, hηker, ?_, ?_⟩
  · intro out row a
    exact actualProjectedDualRow_fderiv_holomorphic d t (ℓ+1) H rows cols hU hD hH hDU hdet out row a
  · intro c hc g
    have hker := (hK _ hc (tangentInclusion_mem_plane d t c)).2.1
    constructor
    · intro hz
      have hgzero : wholeQuotientCoordinates (ℓ+1) H rows cols (tangentInclusion d t c)
          (hdet _ hc) (hhol _ (hDU hc)) g = 0 := by
        apply Subtype.ext
        funext out
        exact (actualProjectedDualRow_pairing d t (ℓ+1) H rows cols out c (scalarJet (ℓ+1) g)).symm.trans (hz out)
      have hgker := LinearMap.mem_ker.mpr hgzero
      rw [hker] at hgker
      exact hgker
    · intro hg
      have hgker : g ∈ LinearMap.ker (wholeQuotientCoordinates (ℓ+1) H rows cols
          (tangentInclusion d t c) (hdet _ hc) (hhol _ (hDU hc))) := by
        rw [hker]
        exact hg
      have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hgker)
      intro out
      rw [actualProjectedDualRow_pairing]
      exact congrFun hz out
  · intro out col c a hc
    exact actual_moving_macaulay_annihilator_connection d t hU H hH (ℓ+1) hV
      (fun _ hc => hDU hc) (η out) (hη out) (fun c hc col => hηker c hc out col) col c a hc

end OriginalCentre
end
end Hironaka.HironakaActualCentreDualJetConnection
