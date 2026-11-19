import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Resolution.HironakaResolutionSpaceLocal

/-!
# The Hilbert–Samuel presentation property (3a) of window records (goal G11)

Lane G11A's property `HSPresentation R w 𝔪 H` (step (3a) of the Hilbert–Samuel route, human
decision Option 1) follows from the TN form `HSTowerState 𝔪 w.carrier H`
(`HironakaG11PresTowerState`) for EVERY route invariant `R` whose domain contains the record:
canonical towers are multiple test blow-ups, and the Hilbert–Samuel functions and singular loci of
the reduced closed subspaces `(C, 𝒪/𝓘_C)` of complex manifolds are the embedded ones.

* `exists_ofChart_toPoint_eq`, **`originalStalkHS_ofClosedAnalytic`** (the intrinsic Hilbert–Samuel
  function of `(C, 𝒪_M/𝓘_C)` at `c` is `hilbertSamuelAt 𝓘_C c`),
  **`mem_intrinsicSingularLocus_ofClosedAnalytic_iff`** (its intrinsic singular locus is the
  embedded singular set);
* **`hsPresentation_of_hsTowerState`**: `HSTowerState` and `IsInvDomain k` give `HSPresentation`
  for every `R : ResolutionInvariant N k Λ`.

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-presentation.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11PresPresentation

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaResolutionSpaceComplex SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic HironakaG11VanishingWindows HironakaG11HSPhaseInduction
  HironakaG11PresTowerState BlowupTowers MarkedIdeals ResolutionInvariantSeq
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### Closed analytic subspaces: Hilbert–Samuel functions and singular loci -/

section Dictionary

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)

/-- Every point of `(A, 𝒪/𝓘_A)` is seen by its own chart embedding, at the chart image of the point. -/
theorem exists_ofChart_toPoint_eq (c : A) :
    ∃ d : (LocalEmbedding.ofChart A hA c.val).carrier,
      (LocalEmbedding.ofChart A hA c.val).toPoint d = c ∧
      (((chartDiffeo (n := n) c.val).symm d.val : chartDomain (n := n) c.val) : M) = c.val := by
  let p : chartDomain (n := n) c.val := ⟨c.val, mem_chartDomain (n := n) c.val⟩
  have hp : (chartDiffeo (n := n) c.val).symm (chartDiffeo (n := n) c.val p) = p :=
    (chartDiffeo (n := n) c.val).symm_apply_apply p
  have hmem : chartDiffeo (n := n) c.val p ∈ chartTrace (n := n) A c.val := by
    change (((chartDiffeo (n := n) c.val).symm (chartDiffeo (n := n) c.val p) :
      chartDomain (n := n) c.val) : M) ∈ A
    rw [hp]
    exact c.property
  refine ⟨⟨chartDiffeo (n := n) c.val p, hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (((chartDiffeo (n := n) c.val).symm (chartDiffeo (n := n) c.val p) :
      chartDomain (n := n) c.val) : M) = c.val
    rw [hp]
  · change (((chartDiffeo (n := n) c.val).symm (chartDiffeo (n := n) c.val p) :
      chartDomain (n := n) c.val) : M) = c.val
    rw [hp]

/-- **The intrinsic Hilbert–Samuel function of a closed analytic subspace** `(A, 𝒪_M/𝓘_A)` of a
complex manifold is the embedded one, `hilbertSamuelAt 𝓘_A`. -/
theorem originalStalkHS_ofClosedAnalytic (c : A) (ℓ : ℕ) :
    originalStalkHS (ofClosedAnalytic A hA) c ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) A) c.val ℓ := by
  obtain ⟨d, hd, hdc⟩ := exists_ofChart_toPoint_eq hA c
  let e := LocalEmbedding.ofChart A hA c.val
  have h1 := originalStalkHS_localEmbedding_eq (ofClosedAnalytic A hA) e d ℓ
  rw [hd] at h1
  rw [h1]
  change hilbertSamuelAt (vanishingIdeal (n := n)
      ((chartDiffeo (n := n) c.val).symm ⁻¹'
        ((Subtype.val : chartDomain (n := n) c.val → M) ⁻¹' A))) d.val ℓ = _
  rw [HironakaActualVanishingIntrinsicHSTransport.hilbertSamuelAt_vanishing_actual_biholomorphic_any,
    HironakaActualVanishingIntrinsicHSTransport.hilbertSamuelAt_vanishing_actual_open_any, hdc]

/-- **The intrinsic singular locus of a closed analytic subspace** `(A, 𝒪_M/𝓘_A)` of a complex
manifold is the embedded singular set of `A`. -/
theorem mem_intrinsicSingularLocus_ofClosedAnalytic_iff (c : A) :
    c ∈ intrinsicSingularLocus (ofClosedAnalytic A hA).obj ↔ c.val ∈ singularSet (n := n) A := by
  obtain ⟨d, hd, hdc⟩ := exists_ofChart_toPoint_eq hA c
  let e := LocalEmbedding.ofChart A hA c.val
  have h := Set.ext_iff.mp
    (OriginalIntrinsicSingularLocus.intrinsicSingularLocus_localEmbedding_preimage
      (ofClosedAnalytic A hA) e) d
  rw [mem_preimage, hd] at h
  rw [h]
  change d.val ∈ singularSet (n := n)
      ((chartDiffeo (n := n) c.val).symm ⁻¹'
        ((Subtype.val : chartDomain (n := n) c.val → M) ⁻¹' A)) ↔ _
  rw [HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq
      (X := CMfd.of (n := n) (chartDomain (n := n) c.val))
      (Y := CMfd.of (n := n) (chartImage (n := n) c.val))
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism
        (D := CMfd.of (n := n) (chartImage (n := n) c.val))
        (C := CMfd.of (n := n) (chartDomain (n := n) c.val)) (chartDiffeo (n := n) c.val).symm),
    HironakaResolutionSpaceLocal.singularSet_preimage_val, mem_preimage, mem_preimage, hdc]

end Dictionary

/-! ### The presentation property -/

section Presentation

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]

/-- **(3a) from the presentation along test towers.** A record `𝔪` in the domain of a route
invariant `R` which presents `H` on the window carrier along all multiple test blow-ups
(`HSTowerState`) has the presentation property `HSPresentation R w 𝔪 H` along the canonical towers
of `R`. -/
theorem hsPresentation_of_hsTowerState (R : ResolutionInvariant.{0} N k Λ) (w : DimEmbedding X N)
    (𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient)) (H : ℕ → ℕ) (hD : IsInvDomain k 𝔪)
    (hS : HSTowerState 𝔪 w.carrier H) : HSPresentation R w 𝔪 H := by
  intro Y T hcan
  have hT := R.isInvValue.isGeoTestTower_of_isCanonical hD T hcan
  obtain ⟨-, hsub, hle, hcut, hsing⟩ := hS T hT
  refine ⟨hsub, fun hA c => ⟨fun ℓ => ?_, ?_, fun hc => ?_⟩⟩
  · rw [originalStalkHS_ofClosedAnalytic hA c ℓ]
    exact hle c.val ℓ
  · rw [hcut c.val]
    constructor
    · intro h
      funext ℓ
      rw [originalStalkHS_ofClosedAnalytic hA c ℓ]
      exact h ℓ
    · intro h ℓ
      rw [← originalStalkHS_ofClosedAnalytic hA c ℓ, h]
  · exact (mem_intrinsicSingularLocus_ofClosedAnalytic_iff hA c).mpr (hsing hc)

end Presentation

end

end Hironaka.Analytic.Unibranch.HironakaG11PresPresentation
