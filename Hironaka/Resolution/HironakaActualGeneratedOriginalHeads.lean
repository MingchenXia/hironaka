import Hironaka.Resolution.HironakaActualGeneratedCurrentClocks

/-! Cutting a generated pair at its unchanged ORIGINAL chronological head
internally produces the corresponding generated pair of actual tails.
No independently supplied tail map or record/value matching is required. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedOriginalHeads
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan
open HironakaActualGeneratedCurrentHistories HironakaActualRawRecordPullbacks
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}
 {A : MarkedIdeal n X} {B : MarkedIdeal n X'}

/-- Every actual chronological cut generates a comparison of the real tails
based at the original head records, with exactly the same final current
comparison. Original head records are retained literally. -/
theorem generated_original_head_tails
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (j : ℕ) :
 Generated (geoTransformAlong A (head S j)) (geoTransformAlong B (head T j))
   (tail S j) (tail T j) U U' η := by
 induction H generalizing j with
 | initial U U' η hrec =>
   cases j with
   | zero => exact Generated.initial U U' η hrec
   | succ j => exact Generated.initial U U' η hrec
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   exact Generated.shrink (ih j) V V' hV hV' htr
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   cases j with
   | zero =>
     exact Generated.initial _ _ _ ((Generated.step H hAdm' hπ hπ' hC).whole_records hA hB)
   | succ j =>
     have hAdmTail : (geoTransformAlong (geoTransformAlong B (head T j)) (tail T j)).IsAdmissibleCentre C' := by
       rw [←geoTransformAlong_head_tail B T j]
       exact hAdm'
     exact Generated.step (ih j) hAdmTail hπ hπ' hC

end
end Hironaka.HironakaActualGeneratedOriginalHeads
