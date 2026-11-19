import Hironaka.Resolution.HironakaG4ProcessedMaskNearCompact
import Hironaka.Resolution.HironakaOriginalTerminalWindowPhysicalComparison

/-! Physical comparison of one processed mask phase on arbitrary original
windows with the same literal incoming history and mask. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProcessedMaskWindowComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism CanonicalCentres NormalCrossings MaxLocusLocal
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskControlledSum
  HironakaG4ProcessedMaskRestriction HironakaG4ProcessedMaskNearCompact
  HironakaOriginalTerminalOverlapComparison HironakaOriginalTerminalWindowPhysicalComparison
  HironakaG3EmptyAwareHistory ResolutionInvariantSpec

variable {n : ℕ} {X Y Z Z' : CMfd.{u} n}

/-- A canonical resolving tail of the actual mask calculated on the
literal restricted original prefix. -/
def IsCanonicalProcessedMaskTail (hn : 0 < n) (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (U : Opens X)
    (S : BlowupTower (CMfd.of (n := n) (openPreimage T U)) Z) : Prop :=
  let v := (Subtype.val : U → X)
  let EU := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
  let M := processedMaskMarked (v ⁻¹' W) EU (restrict U T) (P.map e.toEmbedding)
  IsCanonical M ((invFamily hn (n+1)).inv M) S ∧ IsGeoResolution M S

/-- Physical independence of the two window choices for the same prepared
original prefix and the same selected mask. All real blowups are
compared after empty steps are allowed. -/
theorem processed_mask_windows_compare (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hAt : At W E P.card T)
    {U V O : Opens X} (hOU : O ≤ U) (hOV : O ≤ V)
    (S : BlowupTower (CMfd.of (n := n) (openPreimage T U)) Z)
    (R : BlowupTower (CMfd.of (n := n) (openPreimage T V)) Z')
    (hS : IsCanonicalProcessedMaskTail hn W E T P U S)
    (hR : IsCanonicalProcessedMaskTail hn W E T P V R) :
    let OU := nestedOpens (openPreimage T U) (openPreimage T O)
    let OV := nestedOpens (openPreimage T V) (openPreimage T O)
    let φ := overlapBaseEquiv (openPreimage_mono T hOU) (openPreimage_mono T hOV)
    ∃ χ : CMfd.of (n := n) (openPreimage S OU)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage R OV),
      EmptyAwareTowerIso φ (restrict OU S) (restrict OV R) χ := by
  let M := processedMaskMarked W E T P
  have hDom := (actual_processed_mask_controlled_record (Z := Y) hn hW hE hdense
    T hAt.1 hAt.2.1 hAt.2.2.2.1 hAt.2.2.2.2.1 hAt.2.2.2.2.2.1 P hP hAt.2.2.2.2.2.2.2).1
  have hU := (processed_mask_matrix_restrict hn hW hE hdense T hAt.1 hAt.2.1 U).1 P
  have hV := (processed_mask_matrix_restrict hn hW hE hdense T hAt.1 hAt.2.1 V).1 P
  dsimp only [IsCanonicalProcessedMaskTail] at hS hR
  rw [hU] at hS
  rw [hV] at hR
  exact original_family_terminal_windows_emptyAware hn M hDom (openPreimage_mono T hOU)
    (openPreimage_mono T hOV) S R hS.1 hR.1 hS.2 hR.2

end Hironaka.HironakaG4ProcessedMaskWindowComparison
