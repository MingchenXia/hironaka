import Hironaka.Resolution.HironakaG8StableWindowTest
import Hironaka.Resolution.HironakaG8AmbientGrowingClip
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! A stable local TEST retains its initial data and its regular endpoint
when its base is viewed as an open subset of the ambient manifold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8AmbientStableTest

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8SingularFootprintExtension HironakaG8StableWindowTest HironakaG8AmbientGrowingClip
  HironakaNormalCrossingsSeparationChoiceComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport MarkedIdealBiholomorphism

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

private theorem pullback_comp_marked {A B C : CMfd.{0} n} (f : B → A) (g : C → B)
    (hf : ContMDiff 𝓘c 𝓘c ∞ f) (hg : ContMDiff 𝓘c 𝓘c ∞ g)
    (M : MarkedIdeal n A) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback g (MarkedIdeal.pullback f M) = MarkedIdeal.pullback (f ∘ g) M := by
  exact (HironakaSmoothSubmersionOrderedChoiceImageTrace.whole_markedPullback_comp hf hg M hI).symm

/-- The finite stable clip, transported to an ambient open, is a completed
original TEST with precisely the restricted marked ideal and carrier. -/
theorem ambient_stable_completed_test (U : Opens X)
    (s : GrowingSeq (CMfd.of (n := n) U)) (hLF : LocallyFinite (centreImage s)) (x : U)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ k, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (s.stage k).2)
    (W : Set X) (hW : IsClosed W)
    (hSing : ∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) (s.stage k).2)
    (hSmooth : IsClosedSubmanifold n
      (strictTransform n (gluedProjection s hLF) ((Subtype.val : U → X) ⁻¹' W))) :
    let O := stableWindow s hLF x
    let A := ambientWindow U O
    let Q := ambientGrowingClip U O s (stableIndex s hLF x)
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : A → X) M) Q.tower ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : A → X) ⁻¹' W))) Q.tower ∧
      IsClosedSubmanifold n (strictTransform n Q.tower.proj ((Subtype.val : A → X) ⁻¹' W)) := by
  let O := stableWindow s hLF x
  let A := ambientWindow U O
  let N := stableIndex s hLF x
  let E := ambientWindowBase U O
  let T := restrict O (s.stage N).2
  let Q := ambientGrowingClip U O s N
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let MO := MarkedIdeal.pullback (Subtype.val : O → U) MU
  let WO := (Subtype.val : O → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' W)
  let WA := (Subtype.val : A → X) ⁻¹' W
  have hMU : MU.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM U
  have hMO : MO.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hMU O
  obtain ⟨hT, hTS, hTR⟩ := stable_window_completed_test s hLF x MU hMU hTest
    ((Subtype.val : U → X) ⁻¹' W) hSing hSmooth
  have hRecord : MarkedIdeal.pullback E MO = MarkedIdeal.pullback (Subtype.val : A → X) M := by
    calc
      _ = MarkedIdeal.pullback ((Subtype.val : O → U) ∘ E) MU :=
        pullback_comp_marked (Subtype.val : O → U) E contMDiff_subtype_val E.contMDiff MU hMU.isCoherent
      _ = MarkedIdeal.pullback ((Subtype.val : U → X) ∘ ((Subtype.val : O → U) ∘ E)) M :=
        pullback_comp_marked (Subtype.val : U → X) ((Subtype.val : O → U) ∘ E)
          contMDiff_subtype_val (contMDiff_subtype_val.comp E.contMDiff) M hM.isCoherent
      _ = _ := rfl
  have hClosedO : IsClosed WO := (hW.preimage continuous_subtype_val).preimage continuous_subtype_val
  have hClosedA : IsClosed WA := hW.preimage continuous_subtype_val
  have hWback : E.symm ⁻¹' WA = WO := by
    ext z
    change (E.symm z).val ∈ W ↔ (z.val : X) ∈ W
    rw [← ambientWindowBase_val U O (E.symm z), E.apply_symm_apply]
  change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : A → X) M) Q.tower ∧
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj WA)) Q.tower ∧
    IsClosedSubmanifold n (strictTransform n Q.tower.proj WA)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hRecord]
    exact (isGeoTestTower_transport_iff E hMO.isCoherent T).mpr hT
  · apply singular_stages_of_tower_iso WA hClosedA E.symm (transport_isTowerIso E T).symm
    rw [hWback]
    exact hTS
  · have hWforward : E ⁻¹' WO = WA := rfl
    rw [← hWforward, strictTransform_preimage_of_square E Q.back Q.tower.contMDiff_proj
      T.contMDiff_proj WO hClosedO (fun z => (proj_transport E T z).symm)]
    exact (isClosedSubmanifold_preimage_iff Q.back).mpr hTR

end Hironaka.HironakaG8AmbientStableTest
