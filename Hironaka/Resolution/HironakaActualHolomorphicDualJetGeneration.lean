/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentreDualJetConnection
import Hironaka.Resolution.HironakaActualCentreJetFrameTruncation
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHolomorphicDualJetGeneration
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreDualJetConnection
  HironakaActualCentreJetFrameTruncation

/-- One fixed actual linear retraction onto the TRUE fixed quotient model, independent of all points and functionals. -/
def actualFixedQuotientRetraction (n q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q) :
    (monomialIndex n q → ℂ) →ₗ[ℂ] fixedQuotientModel q rows :=
  (fixedQuotientModel q rows).subtype.leftInverse

/-- The fixed retraction is literally the identity on the genuine fixed-model subspace. -/
theorem actualFixedQuotientRetraction_apply (n q : ℕ) {k : ℕ}
    (rows : Fin k → monomialIndex n q) (v : fixedQuotientModel q rows) :
    actualFixedQuotientRetraction n q rows v.val = v :=
  LinearMap.leftInverse_apply_of_inj (fixedQuotientModel q rows).ker_subtype v

/-- A fixed TRUE-jet section is the ORIGINAL finite jet of the existing fixed whole scalar-jet representative. -/
def actualFixedTrueJetSection (n q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q) :
    fixedQuotientModel q rows →ₗ[ℂ] LinearMap.range (finiteJet (n := n) q) :=
  (finiteJet q).rangeRestrict.comp ((actualScalarJetRepresentative n q).comp
    (Submodule.inclusion (show fixedQuotientModel q rows ≤ scalarJetRange n q from inf_le_left)))

/-- Each coefficient evaluates the moving functional on this ONE fixed actual original jet vector. -/
def actualDualGenerationVector (n q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q)
    (out : monomialIndex n q) : LinearMap.range (finiteJet (n := n) q) :=
  actualFixedTrueJetSection n q rows (actualFixedQuotientRetraction n q rows (Pi.single out 1))

/-- The explicit genuine scalar coefficient FUNCTIONS are specified before the pointwise generation equality. -/
def actualDualGenerationCoefficient (n q : ℕ) {k : ℕ} (rows : Fin k → monomialIndex n q)
    {d : ℕ} (Λ : ComplexModel d → (LinearMap.range (finiteJet (n := n) q) →ₗ[ℂ] ℂ))
    (out : monomialIndex n q) (c : ComplexModel d) : ℂ :=
  Λ c (actualDualGenerationVector n q rows out)

/-- Fixed true-jet evaluation proves genuine holomorphic coefficient FUNCTIONS and generation on the ENTIRE actual jet image. -/
theorem actual_holomorphic_true_jet_annihilator_generation (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel (d+t) → ℂ) {k : ℕ}
    (rows : Fin k → monomialIndex (d+t) q)
    (cols : Fin k → monomialIndex (d+t) q × ι)
    {D : Set (ComplexModel (d+t))}
    (hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0)
    (hrank : ∀ c, tangentInclusion d t c ∈ D →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G (tangentInclusion d t c))) = k)
    (hG : ∀ p ∈ D, ∀ i, HolAt (G i) p)
    (Λ : ComplexModel d → (LinearMap.range (finiteJet (n := d+t) q) →ₗ[ℂ] ℂ))
    (hΛhol : ∀ v, DifferentiableOn ℂ (fun c => Λ c v) ((tangentInclusion d t) ⁻¹' D))
    (hΛ : ∀ c (hc : tangentInclusion d t c ∈ D),
      ∀ g ∈ translatedIdeal G (tangentInclusion d t c) (hG _ hc),
        Λ c ((finiteJet q).rangeRestrict g) = 0) :
    (∀ out, DifferentiableOn ℂ (actualDualGenerationCoefficient (d+t) q rows Λ out)
      ((tangentInclusion d t) ⁻¹' D)) ∧
    ∀ c, tangentInclusion d t c ∈ D → ∀ v : LinearMap.range (finiteJet (n := d+t) q),
      Λ c v = ∑ out, actualDualGenerationCoefficient (d+t) q rows Λ out c *
        (∑ row, actualProjectedDualRow d t q G rows cols out row c * finiteCoordinateArray q v.val row) := by
  refine ⟨fun out => hΛhol (actualDualGenerationVector (d+t) q rows out), ?_⟩
  intro c hc v
  rcases v with ⟨v, g, rfl⟩
  let Q := wholeQuotientCoordinates q G rows cols (tangentInclusion d t c) (hdet _ hc) (hG _ hc)
  let h := actualScalarJetRepresentative (d+t) q ⟨(Q g).val, (Q g).2.1⟩
  have hQh : Q h = Q g := wholeCoordinates_fixed_representative q G rows cols
    (tangentInclusion d t c) (hdet _ hc) (hG _ hc) (Q g)
  have hrem : g-h ∈ translatedIdeal G (tangentInclusion d t c) (hG _ hc) ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q := by
    have hz : Q (g-h) = 0 := by rw [map_sub, hQh, sub_self]
    have hk := LinearMap.mem_ker.mpr hz
    rw [ker_wholeQuotientCoordinates q G rows cols (tangentInclusion d t c)
      (hdet _ hc) (hrank c hc) (hG _ hc)] at hk
    exact hk
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hrem
  have hbzero : (finiteJet q).rangeRestrict b = 0 := by
    apply Subtype.ext
    apply LinearMap.mem_ker.mp
    rw [ker_finiteJet]
    exact hb
  have hdiff : Λ c ((finiteJet q).rangeRestrict (g-h)) = 0 := by
    rw [← hab, map_add, hbzero, add_zero]
    exact hΛ c hc a ha
  have hequal : Λ c ((finiteJet q).rangeRestrict g) =
      Λ c (actualFixedTrueJetSection (d+t) q rows (Q g)) := by
    change Λ c ((finiteJet q).rangeRestrict g) = Λ c ((finiteJet q).rangeRestrict h)
    exact sub_eq_zero.mp (by simpa only [map_sub] using hdiff)
  let F := (Λ c).comp ((actualFixedTrueJetSection (d+t) q rows).comp
    (actualFixedQuotientRetraction (d+t) q rows))
  have hF : F (Q g).val = Λ c ((finiteJet q).rangeRestrict g) := by
    dsimp only [F, LinearMap.comp_apply]
    rw [actualFixedQuotientRetraction_apply]
    exact hequal.symm
  change Λ c ((finiteJet q).rangeRestrict g) = ∑ out,
    actualDualGenerationCoefficient (d+t) q rows Λ out c *
      (∑ row, actualProjectedDualRow d t q G rows cols out row c *
        finiteCoordinateArray q (finiteJet q g) row)
  rw [← hF]
  have hsum := congrArg F (pi_eq_sum_univ' (Q g).val)
  rw [map_sum] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro out _
  rw [map_smul, smul_eq_mul, mul_comm]
  rw [actualProjectedDualRow_pairing]
  rfl

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Actual original geometry internally supplies explicit holomorphic generation on every TRUE jet image, with one family/open before ALL orders. -/
theorem exists_original_hs_constant_centre_holomorphic_dual_generation
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
            IsOpen V ∧ (0 : ComplexModel d) ∈ V ∧
            ∀ Λ : ComplexModel d → (LinearMap.range (finiteJet (n := d+t) (ℓ+1)) →ₗ[ℂ] ℂ),
              (∀ v, DifferentiableOn ℂ (fun c => Λ c v) V) →
              (∀ c (hc : c ∈ V),
                ∀ g ∈ translatedIdeal H (tangentInclusion d t c) (hhol _ (hDU hc)),
                  Λ c ((finiteJet (ℓ+1)).rangeRestrict g) = 0) →
              (∀ out, DifferentiableOn ℂ (actualDualGenerationCoefficient (d+t) (ℓ+1) rows Λ out) V) ∧
              ∀ c, c ∈ V → ∀ v : LinearMap.range (finiteJet (n := d+t) (ℓ+1)),
                Λ c v = ∑ out, actualDualGenerationCoefficient (d+t) (ℓ+1) rows Λ out c *
                  (∑ row, actualProjectedDualRow d t (ℓ+1) H rows cols out row c *
                    finiteCoordinateArray (ℓ+1) v.val row) := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hHS, hRank, hFrames⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, ?_⟩
  intro ℓ
  obtain ⟨k, rows, cols, hk, D, hD, h0D, hDU, hV, h0V, hdet, _hP, _hK⟩ := hFrames ℓ
  refine ⟨k, rows, cols, D, hD, h0D, hDU, hdet, hV, h0V, ?_⟩
  intro Λ hΛhol hΛ
  have hr : ∀ c, tangentInclusion d t c ∈ D → Module.finrank ℂ (LinearMap.range
      (originalMacaulayLinearMap (ℓ+1) H (tangentInclusion d t c))) = k := by
    intro c hc
    exact (hRank _ (hDU hc) (tangentInclusion_mem_plane d t c) ℓ).trans hk.symm
  exact actual_holomorphic_true_jet_annihilator_generation d t (ℓ+1) H rows cols hdet hr
    (fun p hp => hhol p (hDU hp)) Λ hΛhol hΛ

end OriginalCentre
end
end Hironaka.HironakaActualHolomorphicDualJetGeneration
