import Hironaka.Resolution.HironakaActualOriginalCentreBennett

/-!
# Actual local vanishing dictionaries and the original geometric Bennett bound

The coordinate set is the literal inverse image under the actual inverse
flattening map. All representative identities are used only on the genuine
source or target; the entire original zero-translate ideal is retained.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualOriginalGeometricCentreBennett

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  OkaRelationSheaf RelativePrincipalizationSpan InvertibleIdealQuotient BlowupFlatCoordinates
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualOriginalCentreBennett HironakaActualReducedCentreBennett
  HironakaActualPointGeometricBennett HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower

private theorem span_eventually_zero_on {n : ℕ}
    (S : (ComplexModel n → ℂ) → Prop) (Z : Set (ComplexModel n))
    (k : ComplexModel n → ℂ) (hk : IsInSpanAt (n := n) S 0 k)
    (hS : ∀ s, S s → ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Z → s z = 0) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Z → k z = 0 := by
  obtain ⟨_hhol, N, s, a, hs, _ha, he⟩ := hk
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i : Fin N, z ∈ Z → s i z = 0 :=
    eventually_all.mpr fun i => hS (s i) (hs i)
  filter_upwards [he, hall] with z hez hsz hz
  rw [hez]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [hsz i hz, mul_zero]

section LocalDictionary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual inverse/forward representatives prove the precise vanishing membership at the genuine origin. -/
theorem actual_flattened_vanishing_stalk_mem_iff
    (W : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (k : ComplexModel n → ℂ) :
    (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ).mem 0 k ↔
      (vanishingIdeal (n := n) ((actualFlatteningInverseMap x Φ) ⁻¹' W)).mem 0 k := by
  let f := actualFlatteningInverseMap x Φ
  have h0T : (0 : ComplexModel n) ∈ Φ.target := actualFlattening_target_zero_mem x Φ h0
  have ht : Tendsto f (𝓝 (0 : ComplexModel n)) (𝓝 (f 0)) :=
    (actualFlatteningInverseMap_mdifferentiable x Φ hsrc 0 h0T).continuousAt.tendsto
  constructor
  · intro hk
    change IsInSpanAt (n := n)
      (fun s => ∃ u, (vanishingIdeal (n := n) W).mem (f 0) u ∧ s = u ∘ f) 0 k at hk
    refine ⟨hk.1, span_eventually_zero_on _ _ k hk ?_⟩
    rintro s ⟨u, hu, rfl⟩
    exact ht.eventually hu.2
  · intro hk
    let u : M → ℂ := fun y => k (Φ.toFun (chartAt (ComplexModel n) x y))
    have hkdiff : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ k z :=
      hk.1.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mp hz
    have huHol : HolomorphicAt n u x :=
      holomorphicAt_comp_flat Φ (mem_flatDomain_self Φ) (by simpa only [h0] using hkdiff)
    have hforward : Tendsto (fun y : M => Φ.toFun (chartAt (ComplexModel n) x y))
        (𝓝 x) (𝓝 (0 : ComplexModel n)) := by
      have hc := (Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.comp
          ((chartAt (ComplexModel n) x).continuousAt (mem_chart_source _ x))
      simpa only [Function.comp_def, h0] using hc.tendsto
    have hu : (vanishingIdeal (n := n) W).mem x u := by
      refine ⟨huHol, ?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
        hforward.eventually hk.2] with y hy hyzero hyW
      apply hyzero
      change (chartAt (ComplexModel n) x).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) x y))) ∈ W
      rwa [flatInverse_flat Φ hy]
    have hu0 : (vanishingIdeal (n := n) W).mem (f 0) u := by
      change (vanishingIdeal (n := n) W).mem (actualFlatteningInverseMap x Φ 0) u
      rw [actualFlatteningInverseMap_zero x Φ h0]
      exact hu
    have heq : u ∘ f =ᶠ[𝓝 (0 : ComplexModel n)] k := by
      filter_upwards [Φ.isOpen_target.mem_nhds h0T] with z hz
      change k (Φ.toFun (chartAt (ComplexModel n) x
        ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))) = k z
      rw [(flatInverse_mem Φ hz hsrc).2]
    have hm : IsInSpanAt (n := n)
        (fun s => ∃ v, (vanishingIdeal (n := n) W).mem (f 0) v ∧ s = v ∘ f)
        0 (u ∘ f) :=
      isInSpanAt_self ⟨u, hu0, rfl⟩ (hk.1.congr heq.symm)
    exact InvertibleIdealQuotient.IsInSpanAt.congr' hm heq

/-- The unchanged actual zero translate has the same whole vanishing membership, by literal finite spans. -/
theorem actual_zero_translated_flattened_vanishing_stalk_mem_iff
    (W : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (k : ComplexModel n → ℂ) :
    (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0).mem 0 k ↔
      (vanishingIdeal (n := n) ((actualFlatteningInverseMap x Φ) ⁻¹' W)).mem 0 k := by
  have hid : actualAffineTranslation n (0 : ComplexModel n) = id := by
    funext z
    exact zero_add z
  change IsInSpanAt (n := n)
    (fun s => ∃ u, (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ).mem
      (actualAffineTranslation n 0 0) u ∧ s = u ∘ actualAffineTranslation n 0) 0 k ↔ _
  rw [hid]
  change IsInSpanAt (n := n)
    (fun s => ∃ u, (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ).mem 0 u ∧
      s = u) 0 k ↔ _
  constructor
  · intro hk
    refine ⟨hk.1, span_eventually_zero_on _ _ k hk ?_⟩
    rintro s ⟨u, hu, hsu⟩
    rw [hsu]
    exact ((actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 u).mp hu).2
  · intro hk
    exact isInSpanAt_self
      ⟨k, (actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 k).mpr hk, rfl⟩ hk.1

/-- The ENTIRE original zero-translated flattened vanishing ideal equals that of the literal actual inverse image set. -/
theorem actual_zero_translated_flattened_vanishing_origin_ideal
    (W : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0) =
      originalCoherentOriginIdeal
        (vanishingIdeal (n := n) ((actualFlatteningInverseMap x Φ) ⁻¹' W)) := by
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨k, hk, hmem, rfl⟩
    exact ⟨k, hk,
      (actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 k).mp hmem, rfl⟩
  · rintro ⟨k, hk, hmem, rfl⟩
    exact ⟨k, hk,
      (actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 k).mpr hmem, rfl⟩

end LocalDictionary

section OriginalCentre

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d + t)) M] [IsComplexManifold (d + t) M]

/-- Original regularity, original vanishing-ideal coherence and original HS constancy give the genuine local geometric strict-transform inequality. -/
theorem exists_original_hs_constant_centre_geometric_bennett
    (C W : Set M) (x : M) (hreg : RegularAtDim (n := d + t) C x d)
    (hW : (vanishingIdeal (n := d + t) W).IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := d + t) W) y ℓ =
        hilbertSamuelAt (vanishingIdeal (n := d + t) W) x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d + t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d + t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d + t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d + t)) x).source →
        chartAt (ComplexModel (d + t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d + t)) x y) ∈
          complexCoordinatePlane (d + t) d)) ∧
      let Wcoord := (actualFlatteningInverseMap x Φ) ⁻¹' W
      ∀ (j : Fin t) (b : Fin (d + t) → ℂ) (ℓ : ℕ),
        hilbertSamuelAt (vanishingIdeal (n := d + t)
          (strictTransform (d + t)
            (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
            Wcoord)) 0 ℓ ≤ hilbertSamuelAt (vanishingIdeal (n := d + t) W) x ℓ := by
  obtain ⟨Φ, hsrc, h0, hflat, hV⟩ :=
    exists_original_hs_constant_centre_reduced_vertex_normal_powers C x hreg
      (vanishingIdeal (n := d + t) W) hW hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf (vanishingIdeal (n := d + t) W) x Φ) 0)
  let Wcoord := (actualFlatteningInverseMap x Φ) ⁻¹' W
  have hI : I0 = originalCoherentOriginIdeal (vanishingIdeal (n := d + t) Wcoord) :=
    actual_zero_translated_flattened_vanishing_origin_ideal W x Φ hsrc h0
  dsimp only [I0] at hI
  dsimp only at hV
  rw [hI] at hV
  have h0T : (0 : ComplexModel (d + t)) ∈ Φ.target :=
    actualFlattening_target_zero_mem x Φ h0
  refine ⟨Φ, hsrc, h0, hflat, ?_⟩
  dsimp only
  intro j b ℓ
  have hvalue : hilbertSamuelAt (vanishingIdeal (n := d + t) Wcoord) 0 ℓ =
      hilbertSamuelAt (vanishingIdeal (n := d + t) W) x ℓ := by
    rw [hilbertSamuelAt_model_zero, ← hI]
    have hvalue0 : hilbertSamuelAt (vanishingIdeal (n := d + t) W)
        (actualFlatteningInverseMap x Φ 0) ℓ = hilbertSamuelValue I0 ℓ := by
      rw [hilbertSamuelAt_eq_fixedChart (vanishingIdeal (n := d + t) W) x _
        (actualNearbyPoint_mem_chart_source x Φ hsrc 0 h0T),
        fixed_real_original_whole_stalk_ambient_hs_dictionary
          (vanishingIdeal (n := d + t) W) hW x Φ hsrc 0 h0T ℓ]
    simpa only [actualFlatteningInverseMap_zero x Φ h0] using hvalue0.symm
  exact (hilbertSamuelAt_actual_reduced_centre_strict_le d t Wcoord hV j b ℓ).trans_eq hvalue

end OriginalCentre

end

end Hironaka.HironakaActualOriginalGeometricCentreBennett
