import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryOverlap
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport

/-! View a finite open clip of a growing history as a tower on the ambient manifold. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8AmbientGrowingClip

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MaxLocusLocal ResolutionInvariantSeq MarkedIdealTowerTransport

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The same points, as an open subset of the original ambient manifold. -/
def ambientWindow (U : Opens X) (O : Opens U) : Opens X :=
  ⟨(Subtype.val : U → X) '' (O : Set U), U.isOpen.isOpenMap_subtype_val _ O.isOpen⟩

theorem ambientWindow_le (U : Opens X) (O : Opens U) : ambientWindow U O ≤ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem mem_ambientWindow_iff (U : Opens X) (O : Opens U) (x : U) :
    x ∈ O ↔ x.val ∈ ambientWindow U O :=
  ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => (Subtype.ext he : y = x) ▸ hy⟩

/-- The identity on the underlying ambient points of an open window. -/
noncomputable def ambientWindowBase (U : Opens X) (O : Opens U) :
    CMfd.of (n := n) (ambientWindow U O) ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) O :=
  (nestedDiffeo (n := n) U O (ambientWindow U O) (mem_ambientWindow_iff U O)
    (ambientWindow_le U O)).symm

theorem ambientWindowBase_val (U : Opens X) (O : Opens U) (x : ambientWindow U O) :
    ((ambientWindowBase U O x).val : X) = x.val := rfl

/-- Transport the literal window restriction without removing any recorded steps. -/
noncomputable def ambientGrowingClip (U : Opens X) (O : Opens U)
    (s : GrowingSeq (CMfd.of (n := n) U)) (N : ℕ) :=
  transport (ambientWindowBase U O) (restrict O (s.stage N).2)

end Hironaka.HironakaG8AmbientGrowingClip
