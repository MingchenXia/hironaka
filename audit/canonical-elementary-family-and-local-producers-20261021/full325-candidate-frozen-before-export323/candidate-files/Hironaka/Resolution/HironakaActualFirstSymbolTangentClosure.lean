/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualDualJetProlongationUnit
import Hironaka.Resolution.HironakaActualCentreDualJetConnection

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFirstSymbolTangentClosure
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreDualJetConnection
  HironakaRelativeNormalTaylorCoefficients HironakaActualDualJetProlongation
  HironakaActualDualJetProlongationUnit HironakaActualHSZeroCentreVanishing

/-- A genuine zero old jet removes all derivative-coefficient terms and leaves the SAME canonical derivative-germ pairing. -/
theorem actualDualJetProlongation_eq_derivative_pairing_of_finiteJet_zero (d t q : ℕ)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ) (c a : ComplexModel d)
    (g : HolGerm (ComplexModel (d+t))) (hgzero : finiteJet q g = 0) :
    actualDualJetProlongation d t q η c a (finiteJet (q+1) g) =
      ∑ row, η row c * finiteCoordinateArray q
        (finiteJet q (iteratedDerivativeGerm [tangentInclusion d t a] g)) row := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  have hz (row : monomialIndex (d+t) q) : finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row = 0 := by
    rw [hgzero, map_zero]
    rfl
  have he (row : monomialIndex (d+t) q) :=
    actual_directional_derivative_germ_scalar_jet q (HolGerm.mk f hf) (tangentInclusion d t a) row
  simp only [he]
  change (∑ row : monomialIndex (d+t) q,
    (fderiv ℂ (η row) c a * finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row +
      η row c * finiteJet (q+1) (HolGerm.mk f hf) ⟨row.1.val+1, Nat.succ_lt_succ row.1.isLt⟩
        (Fin.cons (tangentInclusion d t a)
          (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))))) = _
  simp only [hz, mul_zero, zero_add]

/-- ACTUAL original constant-rank centre frames internally force genuine first-symbol tangent derivative closure, including the unit ideal. -/
theorem actual_projected_tangent_derivative_mem_ideal_sup_point_pow (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    {U D : Set (ComplexModel (d+t))} (hU : IsOpen U) (hD : IsOpen D)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) (hDU : D ⊆ U)
    (hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : ∀ c, tangentInclusion d t c ∈ D →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G (tangentInclusion d t c))) = k)
    (c a : ComplexModel d) (hc : tangentInclusion d t c ∈ D)
    (g : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ (hDU hc)))
    (hgpow : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q) :
    iteratedDerivativeGerm [tangentInclusion d t a] g ∈
      translatedIdeal G (tangentInclusion d t c) (actual_family_holomorphicAt hU G hG _ (hDU hc)) ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
  by_cases htop : translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ (hDU hc)) = ⊤
  · rw [htop, top_sup_eq]
    trivial
  have hzero (i : ι) : G i (tangentInclusion d t c) = 0 := by
    have hi : translatedGerm (tangentInclusion d t c) (G i)
        (actual_family_holomorphicAt hU G hG _ (hDU hc) i) ∈
        translatedIdeal G (tangentInclusion d t c) (actual_family_holomorphicAt hU G hG _ (hDU hc)) :=
      Ideal.subset_span ⟨i, rfl⟩
    have hz := (HolGerm.mem_maximalIdeal_iff _).mp (IsLocalRing.le_maximalIdeal htop hi)
    simpa [translatedGerm, HolGerm.eval_mk] using hz
  let η := actualProjectedDualRow d t q G rows cols
  let V := (tangentInclusion d t) ⁻¹' D
  have hV : IsOpen V := hD.preimage (tangentInclusion d t).continuous
  have hη out row : DifferentiableOn ℂ (η out row) V :=
    actualProjectedDualRow_holomorphic d t q G rows cols hU hG hDU hdet out row
  have hker : ∀ b ∈ V, ∀ out col, ∑ row, η out row b *
      originalMacaulayMatrix q G (tangentInclusion d t b) row col = 0 := by
    intro b hb out col
    have him : (fun row => originalMacaulayMatrix q G (tangentInclusion d t b) row col) ∈
        LinearMap.range (originalMacaulayLinearMap q G (tangentInclusion d t b)) := by
      rw [originalMacaulayLinearMap, Fintype.range_linearCombination]
      exact Submodule.subset_span ⟨col, rfl⟩
    rw [← ker_pivotProjection_eq_entire_image q G rows cols (tangentInclusion d t b)
      (hdet _ hb) (hrank b hb)] at him
    rw [actualProjectedDualRow_pairing]
    exact congrFun (LinearMap.mem_ker.mp him) out
  have hgj : finiteJet q g = 0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_finiteJet]
    exact hgpow
  have hpair (out : monomialIndex (d+t) q) : ∑ row, η out row c * finiteCoordinateArray q
      (finiteJet q (iteratedDerivativeGerm [tangentInclusion d t a] g)) row = 0 := by
    have hp := actualDualJetProlongation_whole_ideal_zero d t q hU G hG hV
      (fun _ hb => hDU hb) (η out) (hη out) (fun b hb col => hker b hb out col)
      c a hc hzero g hg
    rwa [actualDualJetProlongation_eq_derivative_pairing_of_finiteJet_zero d t q (η out) c a g hgj] at hp
  have hQzero : wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) (hdet _ hc)
      (actual_family_holomorphicAt hU G hG _ (hDU hc))
      (iteratedDerivativeGerm [tangentInclusion d t a] g) = 0 := by
    apply Subtype.ext
    funext out
    exact (actualProjectedDualRow_pairing d t q G rows cols out c
      (scalarJet q (iteratedDerivativeGerm [tangentInclusion d t a] g))).symm.trans (hpair out)
  have hQker := LinearMap.mem_ker.mpr hQzero
  rw [ker_wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) (hdet _ hc)
    (hrank c hc) (actual_family_holomorphicAt hU G hG _ (hDU hc))] at hQker
  exact hQker

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original HSconstant regular-centre geometry gives ALLpositive-order first-symbol tangent closure for the SAME original whole ideals. -/
theorem exists_original_hs_constant_centre_first_symbol_tangent_closure
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
            ∃ _hDU : D ⊆ U,
            (∀ p ∈ D, (pivotMatrix (ℓ+1) H rows cols p).det ≠ 0) ∧
            let V := (tangentInclusion d t) ⁻¹' D
            IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧
            ∀ c, c ∈ V → ∀ (a : ComplexModel d) (g : HolGerm (ComplexModel (d+t))),
              g ∈ originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
                (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c)) →
              g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1) →
              iteratedDerivativeGerm [tangentInclusion d t a] g ∈
                originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
                  (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c)) ⊔
                  IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hHS, hRank, hFrames⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, hk, D, hD, h0D, hDU, hV, h0V, hdet, _hP, _hK⟩ := hFrames ℓ
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, ?_⟩
  intro c hc a g hg hgpow
  have hr : ∀ b, tangentInclusion d t b ∈ D → Module.finrank ℂ (LinearMap.range
      (originalMacaulayLinearMap (ℓ+1) H (tangentInclusion d t b))) = k := by
    intro b hb
    exact (hRank _ (hDU hb) (tangentInclusion_mem_plane d t b) ℓ).trans hk.symm
  rw [hI _ (hDU hc)] at hg ⊢
  exact actual_projected_tangent_derivative_mem_ideal_sup_point_pow d t (ℓ+1) H rows cols
    hU hD hH hDU hdet hr c a hc g hg hgpow

end OriginalCentre
end
end Hironaka.HironakaActualFirstSymbolTangentClosure
