import Hironaka.Resolution.HironakaG8AmbientGrowingClip
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
import Hironaka.Resolution.HironakaG8StableGrowingClips

/-! Strict comparison of ambient finite clips of one growing history. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8AmbientStablePair

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail ResolutionInvariantSeq
  HironakaLocallyFiniteResolutionSequence HironakaG8AmbientGrowingClip
  HironakaG8StableGrowingClips MarkedIdealTowerTransport StepOneTangentChange
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveChosenOverlapCocycle
  HironakaSharpActualCurveCommonOpenCocycle HironakaSharpActualCurveEmptyPadding
  HironakaActualLocallyFiniteBoundary MaxLocusLocal

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- A genuine restricted ambient clip is the exact same original finite
history on the common local source, with the standard point-identity base. -/
theorem exists_ambient_clip_common_restriction (U : Opens X) (O : Opens U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (N : ℕ)
    (C : Opens X) (hC : C ≤ ambientWindow U O) :
    ∃ e : CMfd.of (n := n) (openPreimage (ambientGrowingClip U O s N).tower
          (nestedOpens (ambientWindow U O) C))
        ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (s.stage N).2 (nestedOpens U C)),
      IsTowerIso (commonOpenBase (ambientWindow U O) U C hC ((hC.trans (ambientWindow_le U O))))
        (restrict (nestedOpens (ambientWindow U O) C) (ambientGrowingClip U O s N).tower)
        (restrict (nestedOpens U C) (s.stage N).2) e := by
  let A := nestedOpens U C
  have hAO : A ≤ O := fun q hq => (mem_ambientWindow_iff U O q).mpr (hC hq)
  let V := nestedOpens (ambientWindow U O) C
  let B := nestedOpens O A
  have hMatch : ∀ q : ambientWindow U O, q ∈ V ↔ ambientWindowBase U O q ∈ B := fun _ => Iff.rfl
  have hTr := transport_isTowerIso (ambientWindowBase U O) (restrict O (s.stage N).2)
  have hRes := isTowerIso_restrictOpens hMatch hTr (isTowerIso_mem_openPreimage_iff hTr hMatch)
  have hNest := isTowerIso_restrict_nestedOpens hAO (s.stage N).2
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (hRes.trans hNest) ?_⟩
  intro z
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The same ambient flattening retains all true empty padding positions at
an arbitrary prescribed original clock. -/
theorem exists_ambient_clip_padded_common_restriction (U : Opens X) (O : Opens U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (N L : ℕ)
    (C : Opens X) (hC : C ≤ ambientWindow U O) :
    ∃ e : localEndpoint (ambientWindow U O) C .refl (ambientGrowingClip U O s N).tower
        ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (s.stage N).2 (nestedOpens U C)),
      IsTowerIso (commonOpenBase (ambientWindow U O) U C hC (hC.trans (ambientWindow_le U O)))
        (localPaddedHistory (ambientWindow U O) C .refl (ambientGrowingClip U O s N).tower L)
        ((restrict (nestedOpens U C) (s.stage N).2).append
          (identityEmptyTail (CMfd.of (n := n) (openPreimage (s.stage N).2 (nestedOpens U C))) (L-N))) e := by
  obtain ⟨e,he⟩ := exists_ambient_clip_common_restriction U O s N C hC
  have hLen : (ambientGrowingClip U O s N).tower.length = N := by
    simp only [ambientGrowingClip, length_transport, length_restrict, stage_length]
  have hPad := he.append (identityEmptyTail_isTowerIso e (L-N))
  refine ⟨e,?_⟩
  dsimp only [localPaddedHistory, paddedHistory]
  rw [length_restrict, hLen]
  change IsTowerIso _
    ((BlowupTower.refl : BlowupTower
      (CMfd.of (n := n) (nestedOpens (ambientWindow U O) C))
      (CMfd.of (n := n) (nestedOpens (ambientWindow U O) C))).append
      ((restrict (nestedOpens (ambientWindow U O) C) (ambientGrowingClip U O s N).tower).append
        (identityEmptyTail (CMfd.of (n := n) (openPreimage (ambientGrowingClip U O s N).tower
          (nestedOpens (ambientWindow U O) C))) (L-N)))) _ e
  rw [BlowupTower.refl_append]
  exact hPad

/-- Exact SAME-origin pair clause required by StrictPairwiseComparisons,
using each clip's original cutoff clock and the standard pairwise maximum. -/
theorem ambient_stable_pair_comparison (U : Opens X) (O P : Opens U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (N J : ℕ)
    (hO : ∀ k, N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (O : Set U)))
    (hP : ∀ k, J ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (P : Set U))) :
    let V := ambientWindow U O
    let W := ambientWindow U P
    let T := (ambientGrowingClip U O s N).tower
    let S := (ambientGrowingClip U P s J).tower
    ∃ e : localEndpoint V (V ⊓ W) .refl T ≃ₘ⟮𝓘c,𝓘c⟯ localEndpoint W (V ⊓ W) .refl S,
      IsTowerIso (commonOpenBase V W (V ⊓ W) inf_le_left inf_le_right)
        (localPaddedHistory V (V ⊓ W) .refl T (max T.length S.length))
        (localPaddedHistory W (V ⊓ W) .refl S (max T.length S.length)) e := by
  let V := ambientWindow U O
  let W := ambientWindow U P
  let C := V ⊓ W
  let A := nestedOpens U C
  have hAO : A ≤ O := fun q hq => (mem_ambientWindow_iff U O q).mpr hq.1
  have hAP : A ≤ P := fun q hq => (mem_ambientWindow_iff U P q).mpr hq.2
  have hN : ∀ k, N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (A : Set U)) :=
    fun k hk => (hO k hk).mono_right (preimage_mono hAO)
  have hJ : ∀ k, J ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (A : Set U)) :=
    fun k hk => (hP k hk).mono_right (preimage_mono hAP)
  let L := max (ambientGrowingClip U O s N).tower.length (ambientGrowingClip U P s J).tower.length
  have hLN : N ≤ L := by
    simpa only [L, ambientGrowingClip, length_transport, length_restrict, stage_length] using (le_max_left N J)
  have hLJ : J ≤ L := by
    simpa only [L, ambientGrowingClip, length_transport, length_restrict, stage_length] using (le_max_right N J)
  obtain ⟨eO,heO⟩ := exists_ambient_clip_padded_common_restriction U O s N L C inf_le_left
  obtain ⟨eP,heP⟩ := exists_ambient_clip_padded_common_restriction U P s J L C inf_le_right
  obtain ⟨eS,heS⟩ := exists_strict_stable_prefix_comparison s A N J L hN hJ hLN hLJ
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (heO.trans (heS.trans heP.symm)) ?_⟩
  intro z
  apply Subtype.ext
  apply Subtype.ext
  rfl

end Hironaka.HironakaG8AmbientStablePair
