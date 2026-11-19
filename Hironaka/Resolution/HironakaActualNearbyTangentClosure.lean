import Hironaka.Resolution.HironakaActualHomogeneousInitialTangentDerivatives

/-!
# Tangent closure at every centre point in one fixed original flattening

The common original jet-rank domain is chosen before the point and order.
Maximal pivots are then selected locally at the actual chosen point.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualNearbyTangentClosure

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaSmoothCentreRealDomainOriginalStalkFreeness HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualHSConstantCentreJetFrames HironakaActualFirstSymbolTangentClosure
  HironakaActualHSZeroCentreVanishing
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualHomogeneousInitialHS
  HironakaActualHomogeneousInitialTangentDerivatives HironakaActualCoefficientPresentationCentrePower

/-- Constant ranks on a genuine centre domain supply a local maximal pivot at any point. -/
theorem actual_tangent_derivative_mem_of_constant_centre_rank
    (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel (d + t) → ℂ)
    {U : Set (ComplexModel (d + t))} (hU : IsOpen U)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    (c : ComplexModel d) (hc : tangentInclusion d t c ∈ U)
    (hRank : ∀ b, tangentInclusion d t b ∈ U →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G
        (tangentInclusion d t b))) =
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G
        (tangentInclusion d t c))))
    (a : ComplexModel d) (g : HolGerm (ComplexModel (d + t)))
    (hg : g ∈ translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ hc))
    (hgpow : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q) :
    iteratedDerivativeGerm [tangentInclusion d t a] g ∈
      translatedIdeal G (tangentInclusion d t c)
        (actual_family_holomorphicAt hU G hG _ hc) ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q := by
  let k := Module.finrank ℂ (LinearMap.range
    (originalMacaulayLinearMap q G (tangentInclusion d t c)))
  have hminor : ¬ ∀ (rows : Fin k → monomialIndex (d + t) q)
      (cols : Fin k → monomialIndex (d + t) q × ι),
      (Matrix.of fun i j => originalMacaulayMatrix q G
        (tangentInclusion d t c) (rows i) (cols j)).det = 0 := by
    intro hz
    have hlt := (finite_column_rank_lt_iff_minors_eq_zero
      (originalMacaulayMatrix q G (tangentInclusion d t c)) k).mpr hz
    change k < k at hlt
    exact (lt_irrefl k) hlt
  push Not at hminor
  obtain ⟨rows, cols, hdetc⟩ := hminor
  let f : ComplexModel (d + t) → ℂ := originalMacaulayMinor q G rows cols
  let D : Set (ComplexModel (d + t)) := U ∩ f ⁻¹' ({0} : Set ℂ)ᶜ
  have hD : IsOpen D :=
    (differentiableOn_originalMacaulayMinor q G hU hG rows cols).continuousOn.isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hcD : tangentInclusion d t c ∈ D := ⟨hc, hdetc⟩
  have hDU : D ⊆ U := inter_subset_left
  have hdet : ∀ p ∈ D, (pivotMatrix q G rows cols p).det ≠ 0 := fun _ hp => hp.2
  have hR : ∀ b, tangentInclusion d t b ∈ D →
      Module.finrank ℂ (LinearMap.range
        (originalMacaulayLinearMap q G (tangentInclusion d t b))) = k := by
    intro b hb
    exact hRank b (hDU hb)
  exact actual_projected_tangent_derivative_mem_ideal_sup_point_pow d t q G rows cols
    hU hD hG hDU hdet hR c a hcD g hg hgpow

private theorem unshiftedTaylor_directions_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) →
      (Fin n → ComplexModel m) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n) (normalVector 0 n)) :
    P n (actualUnshiftedTaylorAlgHom n) (fun i => EuclideanSpace.single i 1) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → ComplexModel m) (hf : P m f v) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f)
        (fun i => cast (congrArg ComplexModel hm) (v i)) := by
    subst m
    exact hf
  have ht := hc (Nat.zero_add n) (originalTaylorAlgHom n) (normalVector 0 n) h
  have hv : (fun i : Fin n => cast (congrArg ComplexModel (Nat.zero_add n))
      (normalVector 0 n i)) = (fun i => EuclideanSpace.single i (1 : ℂ)) := by
    funext i
    have hs {m : ℕ} (hm : m=n) (j : Fin m) :
        cast (congrArg ComplexModel hm) (EuclideanSpace.single j (1 : ℂ)) =
          EuclideanSpace.single (Fin.cast hm j) 1 := by
      subst m
      rfl
    rw [normalVector, hs (Nat.zero_add n)]
    congr 1
    apply Fin.ext
    simp
  change P n (actualUnshiftedTaylorAlgHom n) _ at ht
  rw [hv] at ht
  exact ht
/-- Positive-order first-symbol closure gives entire unshifted initial-ideal stability. -/
theorem unshifted_initial_pderiv_of_closure (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n)
    (hclosure : ∀ q : ℕ, 0 < q → ∀ g ∈ I,
      g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q →
      iteratedDerivativeGerm [EuclideanSpace.single i 1] g ∈
        I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) :
    MvPowerSeries.pderiv ℂ i F ∈
      actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (v : Fin n → ComplexModel m) : Prop :=
    ∀ (I : Ideal (HolGerm (ComplexModel m))) (i : Fin n),
      (∀ q : ℕ, 0 < q → ∀ g ∈ I,
        g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q →
        iteratedDerivativeGerm [v i] g ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q) →
      ∀ F : MvPowerSeries (Fin n) ℂ,
        F ∈ actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I) →
        MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal (Ideal.map f.toRingHom I)
  exact unshiftedTaylor_directions_property n P
    (actual_homogeneous_initial_ideal_pderiv_of_first_symbol_closure n) I i hclosure F hF


section OriginalCentre

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d + t)) M] [IsComplexManifold (d + t) M]

/-- One original flattening and domain give all-order tangent closure at every centre point. -/
theorem exists_original_hs_constant_centre_nearby_tangent_closure
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
      ∃ U : Set (ComplexModel (d + t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        ∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
          let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
          ∀ q : ℕ, 0 < q → ∀ (a : ComplexModel d) (g : HolGerm (ComplexModel (d + t))),
            g ∈ Ic → g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q →
            iteratedDerivativeGerm [tangentInclusion d t a] g ∈ Ic ⊔
              IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d + t))) ^ q := by
  obtain ⟨Φ, hsrc, h0, hflat, O, hO, hxO, N, G, hG, hgen, U, hU, h0U, hUT,
    hMap, hH, hhol, hI, _hDimension, hRank⟩ :=
    exists_original_hs_constant_centre_common_jet_ranks C x hreg A hA hhs
  let H : Fin N → ComplexModel (d + t) → ℂ :=
    fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, ?_⟩
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

/-- Original geometry supplies whole initial tangent stability at every point of one fixed domain. -/
theorem exists_original_hs_constant_centre_nearby_initial_tangent_pderiv
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
      ∃ U : Set (ComplexModel (d + t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        ∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
          let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
          let Kc := Ideal.map (actualUnshiftedTaylorAlgHom (d + t)).toRingHom Ic
          ∀ (i : Fin d) (F : MvPowerSeries (Fin (d + t)) ℂ),
            F ∈ actualHomogeneousInitialIdeal Kc →
            MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal Kc := by
  obtain ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hClosure⟩ :=
    exists_original_hs_constant_centre_nearby_tangent_closure C x hreg A hA hhs
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, ?_⟩
  intro c hc
  dsimp only
  intro i F hF
  apply unshifted_initial_pderiv_of_closure (d + t) _ (i.castAdd t) ?_ F hF
  intro q hq g hg hgpow
  have h := hClosure c hc q hq (EuclideanSpace.single i 1) g hg hgpow
  rwa [tangentInclusion_coordinateVector] at h

end OriginalCentre

end

end Hironaka.HironakaActualNearbyTangentClosure
