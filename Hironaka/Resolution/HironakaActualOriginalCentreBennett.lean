import Hironaka.Resolution.HironakaActualNormalTruncationRankConstancy
import Hironaka.Resolution.HironakaActualRelativeStandardnessAnalyticFamily
import Hironaka.Resolution.HironakaActualReducedCentreBennett

/-!
# The original constant-centre consumer for canonical normal powers and Bennett

One original normal-truncation producer supplies both tangent stability and
all normal truncations free for the same actual flattening and entire ideal.
The canonical reduced series and normalized-member ideals remain unchanged.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualOriginalCentreBennett

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalUniformTruncations
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaActualNormalTruncationRankConstancy
  HironakaActualRelativeStandardnessAnalyticFamily HironakaActualReducedCentreBennett
  HironakaActualFormalInitialDiagram HironakaActualOriginalFormalTaylor
  HironakaActualHomogeneousInitialHS HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualReducedFormalStandardBasis
  HironakaActualAnalyticStrictGenerators

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d + t)) M] [IsComplexManifold (d + t) M]

/-- Only original regularity, coherence and ambient HS constancy give the literal SAME canonical reduced normal powers. -/
theorem exists_original_hs_constant_centre_reduced_vertex_normal_powers
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d + t) C x d)
    (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
        chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
          complexCoordinatePlane (d + t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ a : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0),
        actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0) a ∈
            actualFormalCoordinateIdeal (d + t) (actualTangentCentreVariables d t) ^
              Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, U, _hU, h0U, _hUT, hProfiles, _hRank, hFree⟩ :=
    exists_original_hs_constant_centre_normal_truncations_free C x hreg A hA hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  have hc0 : tangentInclusion d t (0 : ComplexModel d) ∈ U := by
    simpa only [map_zero] using h0U
  have hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d + t)) ℂ),
      F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0) := by
    simpa only [map_zero] using (hProfiles (0 : ComplexModel d) hc0).1
  have hfree : ∀ q : ℕ, let := tangentAlgebra d t
      Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d + t)) ⧸ (I0 ⊔ normalIdeal d t ^ q)) :=
    fun q => (hFree q).1
  refine ⟨Φ, hsrc, h0, hflat, ?_⟩
  exact original_actualReducedVertexSeries_mem_normal_power d t I0 hD hfree

/-- The actual normalized-member Bennett inequality follows from ONLY original centre hypotheses, for the SAME flattening and whole original ideal. -/
theorem exists_original_hs_constant_centre_normalized_bennett
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d + t) C x d)
    (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
        chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
          complexCoordinatePlane (d + t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      (∀ a : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0),
        actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom I0) a ∈
            actualFormalCoordinateIdeal (d + t) (actualTangentCentreVariables d t) ^
              Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
      ∀ (j : Fin t) (b : Fin (d + t) → ℂ) (ℓ : ℕ),
        hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I0
          (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ ≤
            hilbertSamuelAt A x ℓ := by
  obtain ⟨Φ, hsrc, h0, hflat, hV⟩ :=
    exists_original_hs_constant_centre_reduced_vertex_normal_powers C x hreg A hA hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  have h0T : (0 : ComplexModel (d + t)) ∈ Φ.target :=
    actualFlattening_target_zero_mem x Φ h0
  refine ⟨Φ, hsrc, h0, hflat, hV, ?_⟩
  intro j b ℓ
  have hvalue : hilbertSamuelAt A x ℓ = hilbertSamuelValue I0 ℓ := by
    have hvalue0 : hilbertSamuelAt A (actualFlatteningInverseMap x Φ 0) ℓ =
        hilbertSamuelValue I0 ℓ := by
      rw [hilbertSamuelAt_eq_fixedChart A x _
        (actualNearbyPoint_mem_chart_source x Φ hsrc 0 h0T),
        fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc 0 h0T ℓ]
    simpa only [actualFlatteningInverseMap_zero x Φ h0] using hvalue0
  rw [hvalue]
  exact hilbertSamuelValue_actual_reduced_centre_normalized_le d t I0 hV j b ℓ

end

end Hironaka.HironakaActualOriginalCentreBennett
