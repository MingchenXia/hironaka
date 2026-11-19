import Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS
import Hironaka.Resolution.HironakaAuxiliaryVariationDescent

set_option autoImplicit false

/-!
# Actual regularity and entire intrinsic HS at a locally finite history limit

The already constructed actual stable-window biholomorphism compares the
independent limit carrier with its actual finite centre-relative strict
transform. These are geometric dictionaries, not the existence of a resolving
history or transport of an evolving canonical invariant.

Blueprint: `hironaka-actual-limit-carrier-geometry.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaActualLimitCarrierGeometry

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MemberInterTowerAlong HomogenizedGlueingTower
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaBaseChange
  HironakaHolomorphicJetChartInvariance HironakaOriginalFullValueVariationLocus
  HironakaAuxiliaryVariationDescent HironakaActualOpenIntrinsicHS

attribute [local instance] limitChartedSpace

variable {n : ℕ} {X : CMfd.{u} n}

local instance (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) :=
  limitSpace_isComplexManifold s hLF

private theorem regularAtDim_diffeomorph_preimage_iff
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (e : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z)
    (A : Set Z) (y : Y) (q : ℕ) :
    RegularAtDim (n := n) (e ⁻¹' A) y q ↔ RegularAtDim (n := n) A (e y) q := by
  constructor
  · intro hy
    have h := RegularAtDimTransport.regularAtDim_of_preimage e.symm.contMDiff
      (MarkedIdealTowerTransport.notMem_exceptionalLocus e.symm (e y))
      isOpen_univ (mem_univ (e y)) (fun _ _ => Iff.rfl)
      (by simpa only [e.symm_apply_apply] using hy)
    have he : e.symm ⁻¹' (e ⁻¹' A) = A := by
      ext z
      simp only [mem_preimage, e.apply_symm_apply]
    change RegularAtDim (n := n) (e.symm ⁻¹' (e ⁻¹' A)) (e y) q at h
    rwa [he] at h
  · intro hy
    exact RegularAtDimTransport.regularAtDim_of_preimage e.contMDiff
      (MarkedIdealTowerTransport.notMem_exceptionalLocus e y)
      isOpen_univ (mem_univ y) (fun _ _ => Iff.rfl) hy

private theorem regularAtDim_openHoloEmbedding_preimage_iff
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {f : Y → Z} (hf : IsOpenHoloEmbedding n f) (A : Set Z) (y : Y) (q : ℕ) :
    RegularAtDim (n := n) (f ⁻¹' A) y q ↔ RegularAtDim (n := n) A (f y) q := by
  obtain ⟨U, e, he⟩ := hf
  have hfun : f = (Subtype.val : U → Z) ∘ e := funext he
  rw [hfun]
  change RegularAtDim (n := n) (e ⁻¹' ((Subtype.val : U → Z) ⁻¹' A)) y q ↔ _
  rw [regularAtDim_diffeomorph_preimage_iff]
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff

private theorem variation_preimage_openHoloEmbedding
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {Λ : Type v} {f : Y → Z} (hf : IsOpenHoloEmbedding n f)
    (g : Z → Λ) (A : Set Z) (q : ℕ) :
    f ⁻¹' actualValueVariationLocus (n := n) g A q =
      actualValueVariationLocus (n := n) (g ∘ f) (f ⁻¹' A) q := by
  ext y
  change (f y ∈ A ∧ ¬_) ↔ (f y ∈ A ∧ ¬_)
  apply and_congr_right
  intro _hyA
  apply not_congr
  apply and_congr (regularAtDim_openHoloEmbedding_preimage_iff hf A y q).symm
  constructor
  · rintro ⟨V, hV, hyV, hconst⟩
    exact ⟨f ⁻¹' V, hV.preimage hf.continuous, hyV,
      fun z hz => hconst (f z) ⟨hz.1, hz.2⟩⟩
  · rintro ⟨V, hV, hyV, hconst⟩
    refine ⟨f '' V, hf.isOpenMap _ hV, ⟨y, hyV, rfl⟩, ?_⟩
    rintro z ⟨hzA, w, hwV, hwz⟩
    rw [← hwz]
    have hwA : f w ∈ A := hwz.symm ▸ hzA
    exact hconst w ⟨hwA, hwV⟩

/-- The independently defined actual limit carrier has exactly the regular
dimension of the SAME finite centre-relative strict carrier on its true chart. -/
theorem regularAtDim_limitStrictTransform_local_iff
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    {B : Set X} (hB : IsClosed B) (x : X) (z : localEndpoint s hLF x) (q : ℕ) :
    RegularAtDim (n := n) (limitStrictTransform s hLF B)
        (actualHistoryLocalInclusion s hLF x z) q ↔
      RegularAtDim (n := n) (strictAlong (s.stage (stableIndex s hLF x)).2 B) z.val q := by
  have h := regularAtDim_openHoloEmbedding_preimage_iff
    (isOpenHoloEmbedding_localInclusion s hLF x) (limitStrictTransform s hLF B) z q
  rw [localInclusion_preimage_limitStrictTransform s hLF hB x] at h
  exact h.symm.trans AnalyticSubsetOpens.regularAtDim_preimage_val_iff

/-- Every intrinsic reduced HS order at the actual limit equals the SAME
order of the actual finite prefix carrier. Analyticity supplies coherence
internally in the native open and biholomorphic reduced-ideal comparisons. -/
theorem hilbertSamuelAt_vanishing_limitStrictTransform_local
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B)
    (x : X) (z : localEndpoint s hLF x) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (limitStrictTransform s hLF B))
        (actualHistoryLocalInclusion s hLF x z) ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n)
        (strictAlong (s.stage (stableIndex s hLF x)).2 B)) z.val ℓ := by
  let U := limitWindow s hLF (stableWindow s hLF x)
  let e := stableWindowDiffeomorph s hLF x
  let C := strictAlong (s.stage (stableIndex s hLF x)).2 B
  let D : Set U := (Subtype.val : U → limitManifold s hLF) ⁻¹' limitStrictTransform s hLF B
  have hLa := isComplexAnalyticSubset_limitStrictTransform s hLF hB
  have hCa := isComplexAnalyticSubset_strictAlong hB (s.stage (stableIndex s hLF x)).2
  have hDa : IsComplexAnalyticSubset (n := n) D :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hLa U
  have hpre : e ⁻¹' D =
      (Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹' C :=
    localInclusion_preimage_limitStrictTransform s hLF hB.isClosed x
  have hHS := HironakaActualBlowupOffCentreIntrinsicHS.hilbertSamuelAt_vanishing_actual_biholomorphic
    e hDa z ℓ
  rw [hpre] at hHS
  have hOpenLimit := hilbertSamuelAt_vanishing_actual_open hLa U (e z) ℓ
  have hOpenPrefix := hilbertSamuelAt_vanishing_actual_open hCa
    (openPreimage (s.stage (stableIndex s hLF x)).2 (stableWindow s hLF x)) z ℓ
  exact hOpenLimit.symm.trans (hHS.symm.trans hOpenPrefix)

/-- Exact literal bad-locus pullback for the entire family of reduced actual
limit carriers, along the actual auxiliary carrier. Every position and order
is retained; no finite-family assumption or evolving invariant is used. -/
theorem localInclusion_preimage_actual_whole_hs_variation
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    {A : Set X} (hA : IsClosed A) {ι : Type v} (B : ι → Set X)
    (hB : ∀ i, IsComplexAnalyticSubset (n := n) (B i)) (x : X) (q : ℕ) :
    (actualHistoryLocalInclusion s hLF x) ⁻¹' actualValueVariationLocus (n := n)
        (fun z i ℓ => hilbertSamuelAt (vanishingIdeal (n := n) (limitStrictTransform s hLF (B i))) z ℓ)
        (limitStrictTransform s hLF A) q =
      (Subtype.val : localEndpoint s hLF x → (s.stage (stableIndex s hLF x)).1) ⁻¹'
        actualValueVariationLocus (n := n)
          (fun z i ℓ => hilbertSamuelAt (vanishingIdeal (n := n)
            (strictAlong (s.stage (stableIndex s hLF x)).2 (B i))) z ℓ)
          (strictAlong (s.stage (stableIndex s hLF x)).2 A) q := by
  let Γ : localEndpoint s hLF x → limitManifold s hLF := actualHistoryLocalInclusion s hLF x
  let N := stableIndex s hLF x
  let gL : limitManifold s hLF → ι → ℕ → ℕ :=
    fun z i ℓ => hilbertSamuelAt (vanishingIdeal (n := n) (limitStrictTransform s hLF (B i))) z ℓ
  let gN : (s.stage N).1 → ι → ℕ → ℕ :=
    fun z i ℓ => hilbertSamuelAt (vanishingIdeal (n := n) (strictAlong (s.stage N).2 (B i))) z ℓ
  have hvalues : gL ∘ Γ =
      gN ∘ (Subtype.val : localEndpoint s hLF x → (s.stage N).1) := by
    funext z i ℓ
    exact hilbertSamuelAt_vanishing_limitStrictTransform_local s hLF (hB i) x z ℓ
  have hcarrier : Γ ⁻¹' limitStrictTransform s hLF A =
      (Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹' strictAlong (s.stage N).2 A :=
    localInclusion_preimage_limitStrictTransform s hLF hA x
  change Γ ⁻¹' actualValueVariationLocus (n := n) gL (limitStrictTransform s hLF A) q =
    (Subtype.val : localEndpoint s hLF x → (s.stage N).1) ⁻¹'
      actualValueVariationLocus (n := n) gN (strictAlong (s.stage N).2 A) q
  have hΓ : IsOpenHoloEmbedding n Γ := isOpenHoloEmbedding_localInclusion s hLF x
  rw [variation_preimage_openHoloEmbedding hΓ gL (limitStrictTransform s hLF A) q]
  rw [hvalues, hcarrier]
  exact (actualValueVariationLocus_preimage_val
    (openPreimage (s.stage N).2 (stableWindow s hLF x)) gN (strictAlong (s.stage N).2 A) q).symm

end

end Hironaka.HironakaActualLimitCarrierGeometry
