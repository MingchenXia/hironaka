import Hironaka.Resolution.HironakaActualNearbyTangentClosure

/-!
# Whole initial tangent stability in a prescribed original flattening

The input flattening may already have been selected by the actual common
coefficient-domain construction. Original coherence is used only through
finite generators on its true holomorphic target.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualFixedFlatteningTangentClosure

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalTaylorCoefficients HironakaActualHomogeneousInitialTangentDerivatives
  HironakaActualHSConstantCentreJetFrames HironakaActualNearbyTangentClosure
  HironakaActualHSZeroCentreVanishing HironakaActualOriginalFormalTaylor
  HironakaActualHomogeneousInitialHS HironakaActualCoefficientPresentationCentrePower

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d + t)) M] [IsComplexManifold (d + t) M]

/-- Original HS constancy gives one common all-order rank domain in ANY prescribed actual flattening. -/
theorem fixed_flattening_original_hs_constant_centre_common_jet_ranks
    (C : Set M) (x : M) (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
      chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
        complexCoordinatePlane (d + t) d)) :
    ∃ (N : ℕ) (H : Fin N → ComplexModel (d + t) → ℂ)
      (U : Set (ComplexModel (d + t))), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
      (∀ i, DifferentiableOn ℂ (H i) U) ∧
      ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
        (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
          (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
            translatedIdeal H p (hhol p hp)) ∧
        ∀ p ∈ U, p ∈ complexCoordinatePlane (d + t) d → ∀ ℓ : ℕ,
          Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ + 1) H p)) =
            Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ + 1) H 0)) := by
  have h0T : (0 : ComplexModel (d + t)) ∈ Φ.target :=
    actualFlattening_target_zero_mem x Φ h0
  obtain ⟨_O, _hO, _hxO, N, G, _hG, _hgen, U, hU, h0U, hUT, _hMap, hH, hF⟩ :=
    exists_local_original_pullback_generators A hA Φ.target Φ.isOpen_target
      (actualFlatteningInverseMap_mdifferentiable x Φ hsrc) 0 h0T
  let H : Fin N → ComplexModel (d + t) → ℂ :=
    fun i => G i ∘ actualFlatteningInverseMap x Φ
  have hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p := by
    intro p hp i
    exact (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hH i) hp).mono
      (fun _ hz => hz.differentiableAt)
  have hdiff (i : Fin N) : DifferentiableOn ℂ (H i) U :=
    fun p hp => (hhol p hp i).self_of_nhds.differentiableWithinAt
  have hIt (p : ComplexModel (d + t)) (hp : p ∈ U) :
      originalCoherentOriginIdeal
        (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
          translatedIdeal H p (hhol p hp) := by
    have ht := translated_origin_ideal_eq_span_of_real_generators
      (actualFlattenedOriginalSheaf A x Φ) H hU hH hF hp
        (fun i => translated_function_holAt hU (hH i) hp)
    rw [ht, translatedIdeal]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    change H i (p + z) = H i (z + p)
    rw [add_comm]
  have hV (p : ComplexModel (d + t)) (hp : p ∈ U) (ℓ : ℕ) :
      hilbertSamuelAt A (actualFlatteningInverseMap x Φ p) ℓ =
        hilbertSamuelValue (translatedIdeal H p (hhol p hp)) ℓ := by
    rw [hilbertSamuelAt_eq_fixedChart A x _
      (actualNearbyPoint_mem_chart_source x Φ hsrc p (hUT hp)),
      fixed_real_original_whole_stalk_ambient_hs_dictionary A hA x Φ hsrc p (hUT hp) ℓ,
      hIt p hp]
  refine ⟨N, H, U, hU, h0U, hUT, hdiff, hhol, hIt, ?_⟩
  intro p hp hplane ℓ
  apply originalMacaulay_rank_eq_of_translated_hs_eq ℓ H p 0 (hhol p hp) (hhol 0 h0U)
  rw [← hV p hp ℓ, ← hV 0 h0U ℓ, actualFlatteningInverseMap_zero x Φ h0]
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc p (hUT hp)
  apply hhs _ ((hflat hdom.1 hdom.2).mpr ?_) ℓ
  rw [actualNearbyPoint_chart_value x Φ hsrc p (hUT hp), Φ.right_inv p (hUT hp)]
  exact hplane

/-- ANY prescribed flattening has all-order tangent closure for the actual whole original ideals at every nearby centre point. -/
theorem fixed_flattening_original_hs_constant_centre_tangent_closure
    (C : Set M) (x : M) (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
      chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
        complexCoordinatePlane (d + t) d)) :
    ∃ U : Set (ComplexModel (d + t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
      ∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
        let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
        ∀ q : ℕ, 0 < q → ∀ (a : ComplexModel d) (g : HolGerm (ComplexModel (d + t))),
          g ∈ Ic → g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q →
          iteratedDerivativeGerm [tangentInclusion d t a] g ∈ Ic ⊔
            IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q := by
  obtain ⟨N, H, U, hU, h0U, hUT, hH, hhol, hI, hRank⟩ :=
    fixed_flattening_original_hs_constant_centre_common_jet_ranks C x A hA hhs Φ hsrc h0 hflat
  refine ⟨U, hU, h0U, hUT, ?_⟩
  intro c hc
  dsimp only
  intro q hq a g hg hgpow
  cases q with
  | zero => omega
  | succ ℓ =>
    have hR : ∀ b, tangentInclusion d t b ∈ U →
        Module.finrank ℂ (LinearMap.range
          (originalMacaulayLinearMap (ℓ + 1) H (tangentInclusion d t b))) =
        Module.finrank ℂ (LinearMap.range
          (originalMacaulayLinearMap (ℓ + 1) H (tangentInclusion d t c))) := by
      intro b hb
      exact (hRank _ hb (tangentInclusion_mem_plane d t b) ℓ).trans
        (hRank _ hc (tangentInclusion_mem_plane d t c) ℓ).symm
    rw [hI _ hc] at hg ⊢
    exact actual_tangent_derivative_mem_of_constant_centre_rank d t (ℓ + 1) H
      hU hH c hc hR a g hg hgpow

/-- The given original flattening, without a replacement witness, has all-point whole-initial tangent stability. -/
theorem fixed_flattening_original_hs_constant_centre_initial_tangent_pderiv
    (C : Set M) (x : M) (A : GermIdeal (d + t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
      chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
        complexCoordinatePlane (d + t) d)) :
    ∃ U : Set (ComplexModel (d + t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
      ∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
        let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
        let Kc := Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom Ic
        ∀ (i : Fin d) (F : MvPowerSeries (Fin (d + t)) ℂ),
          F ∈ actualHomogeneousInitialIdeal Kc →
          MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal Kc := by
  obtain ⟨U, hU, h0U, hUT, hClosure⟩ :=
    fixed_flattening_original_hs_constant_centre_tangent_closure C x A hA hhs Φ hsrc h0 hflat
  refine ⟨U, hU, h0U, hUT, ?_⟩
  intro c hc
  dsimp only
  intro i F hF
  apply unshifted_initial_pderiv_of_closure (d + t) _ (i.castAdd t) ?_ F hF
  intro q hq g hg hgpow
  have h := hClosure c hc q hq (EuclideanSpace.single i 1) g hg hgpow
  rwa [tangentInclusion_coordinateVector] at h

end

end Hironaka.HironakaActualFixedFlatteningTangentClosure
