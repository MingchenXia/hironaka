/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentreDualJetConnection
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreDualJetSpan
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreDualJetConnection

section Point
variable (d t q : ℕ) {ι : Type*} [Fintype ι]
  (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
  (rows : Fin k → monomialIndex (d+t) q)
  (cols : Fin k → monomialIndex (d+t) q × ι) (c : ComplexModel d)
  (hdet : (pivotMatrix q G rows cols (tangentInclusion d t c)).det ≠ 0)
  (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G (tangentInclusion d t c))) = k)
  (hG : ∀ i, HolAt (G i) (tangentInclusion d t c))

include hdet hrank in
private theorem projected_pairings_zero_iff (g : HolGerm (ComplexModel (d+t))) :
    (∀ out, ∑ row, actualProjectedDualRow d t q G rows cols out row c * scalarJet q g row = 0) ↔
      g ∈ translatedIdeal G (tangentInclusion d t c) hG ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
  change _ ↔ g ∈ (translatedIdeal G (tangentInclusion d t c) hG ⊔
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q).restrictScalars ℂ
  rw [← ker_wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) hdet hrank hG,
    LinearMap.mem_ker]
  constructor
  · intro hz
    apply Subtype.ext
    funext out
    exact (actualProjectedDualRow_pairing d t q G rows cols out c (scalarJet q g)).symm.trans (hz out)
  · intro hz out
    rw [actualProjectedDualRow_pairing]
    exact congrFun (congrArg Subtype.val hz) out

include hdet hrank in
/-- The specified original projected rows separate exactly the ENTIRE ideal image in the TRUE finite-jet range. -/
theorem actualProjectedDualRow_separates_true_jet_image
    (v : LinearMap.range (finiteJet (n := d+t) q)) :
    (∀ out, ∑ row, actualProjectedDualRow d t q G rows cols out row c *
      finiteCoordinateArray q v.val row = 0) ↔
    v ∈ ((translatedIdeal G (tangentInclusion d t c) hG).restrictScalars ℂ).map (finiteJet q).rangeRestrict := by
  rcases v with ⟨v, g, rfl⟩
  rw [show finiteCoordinateArray q (finiteJet q g) = scalarJet q g from rfl,
    projected_pairings_zero_iff d t q G rows cols c hdet hrank hG]
  constructor
  · intro hg
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hg
    have hbzero : finiteJet q b = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_finiteJet]
      exact hb
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    change finiteJet q a = finiteJet q g
    rw [← hab, map_add, hbzero, add_zero]
  · rintro ⟨a, ha, hjet⟩
    have he := congrArg Subtype.val hjet
    change finiteJet q a = finiteJet q g at he
    have hrem : g-a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
      have hz : finiteJet q (g-a) = 0 := by rw [map_sub, ← he, sub_self]
      have hk := LinearMap.mem_ker.mpr hz
      rw [ker_finiteJet] at hk
      exact hk
    exact Submodule.mem_sup.mpr ⟨a, ha, g-a, hrem, by abel⟩

include hdet hrank in
/-- Every actual linear functional annihilating the ENTIRE original ideal jet is a finite combination of these true projected rows. -/
theorem actualProjectedDualRow_spans_true_jet_annihilator
    (Λ : LinearMap.range (finiteJet (n := d+t) q) →ₗ[ℂ] ℂ)
    (hΛ : ∀ g ∈ translatedIdeal G (tangentInclusion d t c) hG, Λ ((finiteJet q).rangeRestrict g) = 0) :
    ∃ b : monomialIndex (d+t) q → ℂ,
      ∀ v : LinearMap.range (finiteJet (n := d+t) q),
        Λ v = ∑ out, b out * (∑ row, actualProjectedDualRow d t q G rows cols out row c *
          finiteCoordinateArray q v.val row) := by
  let Q := wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) hdet hG
  let L := Λ.comp (finiteJet q).rangeRestrict
  have hker : LinearMap.ker Q ≤ LinearMap.ker L := by
    intro g hg
    rw [ker_wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) hdet hrank hG] at hg
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hg
    have hbzero : (finiteJet q).rangeRestrict b = 0 := by
      apply Subtype.ext
      apply LinearMap.mem_ker.mp
      rw [ker_finiteJet]
      exact hb
    rw [LinearMap.mem_ker]
    change Λ ((finiteJet q).rangeRestrict g) = 0
    rw [← hab, map_add, hbzero, add_zero]
    exact hΛ a ha
  let e := Q.quotKerEquivOfSurjective (wholeQuotientCoordinates_surjective q G rows cols
    (tangentInclusion d t c) hdet hG)
  let f : fixedQuotientModel q rows →ₗ[ℂ] ℂ := ((LinearMap.ker Q).liftQ L hker).comp e.symm.toLinearMap
  have hf (g : HolGerm (ComplexModel (d+t))) : f (Q g) = L g := by
    dsimp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  obtain ⟨F, hF⟩ := f.exists_extend
  refine ⟨fun out => F (Pi.single out 1), ?_⟩
  intro v
  rcases v with ⟨v, g, rfl⟩
  have hFg : F (Q g).val = Λ ((finiteJet q).rangeRestrict g) := by
    have he := LinearMap.congr_fun hF (Q g)
    exact he.trans (hf g)
  change Λ ((finiteJet q).rangeRestrict g) = ∑ out, F (Pi.single out 1) *
    (∑ row, actualProjectedDualRow d t q G rows cols out row c *
      finiteCoordinateArray q (finiteJet q g) row)
  rw [← hFg]
  have hsum := congrArg F (pi_eq_sum_univ' (Q g).val)
  rw [map_sum] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro out _
  rw [map_smul, smul_eq_mul, mul_comm]
  rw [actualProjectedDualRow_pairing]
  rfl

end Point
section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- SAME original geometry before ALL orders internally gives genuine dual spanning on each TRUE jet image. -/
theorem exists_original_hs_constant_centre_true_jet_dual_spanning
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
            ∃ hDU : D ⊆ U,
            (∀ p ∈ D, (pivotMatrix (ℓ+1) H rows cols p).det ≠ 0) ∧
            let V := (tangentInclusion d t) ⁻¹' D
            let η := actualProjectedDualRow d t (ℓ+1) H rows cols
            IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧
            (∀ out row, DifferentiableOn ℂ (η out row) V) ∧
            (∀ out row a, DifferentiableOn ℂ (fun c => fderiv ℂ (η out row) c a) V) ∧
            ∀ c (hc : c ∈ V),
              Module.finrank ℂ (LinearMap.range
                (originalMacaulayLinearMap (ℓ+1) H (tangentInclusion d t c))) = k ∧
              (∀ v : LinearMap.range (finiteJet (n := d+t) (ℓ+1)),
                (∀ out, ∑ row, η out row c * finiteCoordinateArray (ℓ+1) v.val row = 0) ↔
                v ∈ ((translatedIdeal H (tangentInclusion d t c) (hhol _ (hDU hc))).restrictScalars ℂ).map
                  (finiteJet (ℓ+1)).rangeRestrict) ∧
              ∀ Λ : LinearMap.range (finiteJet (n := d+t) (ℓ+1)) →ₗ[ℂ] ℂ,
                (∀ g ∈ translatedIdeal H (tangentInclusion d t c) (hhol _ (hDU hc)),
                  Λ ((finiteJet (ℓ+1)).rangeRestrict g) = 0) →
                ∃ b : monomialIndex (d+t) (ℓ+1) → ℂ,
                  ∀ v : LinearMap.range (finiteJet (n := d+t) (ℓ+1)),
                    Λ v = ∑ out, b out * (∑ row, η out row c * finiteCoordinateArray (ℓ+1) v.val row) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hHS, hRank, hFrames⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, hk, D, hD, h0D, hDU, hV, h0V, hdet, _hP, _hK⟩ := hFrames ℓ
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, ?_, ?_, ?_⟩
  · intro out row
    exact actualProjectedDualRow_holomorphic d t (ℓ+1) H rows cols hU hH hDU hdet out row
  · intro out row a
    exact actualProjectedDualRow_fderiv_holomorphic d t (ℓ+1) H rows cols hU hD hH hDU hdet out row a
  · intro c hc
    have hr : Module.finrank ℂ (LinearMap.range
        (originalMacaulayLinearMap (ℓ+1) H (tangentInclusion d t c))) = k :=
      (hRank _ (hDU hc) (tangentInclusion_mem_plane d t c) ℓ).trans hk.symm
    refine ⟨hr, ?_, ?_⟩
    · intro v
      exact actualProjectedDualRow_separates_true_jet_image d t (ℓ+1) H rows cols c
        (hdet _ hc) hr (hhol _ (hDU hc)) v
    · intro Λ hΛ
      exact actualProjectedDualRow_spans_true_jet_annihilator d t (ℓ+1) H rows cols c
        (hdet _ hc) hr (hhol _ (hDU hc)) Λ hΛ

end OriginalCentre
end
end Hironaka.HironakaActualCentreDualJetSpan
