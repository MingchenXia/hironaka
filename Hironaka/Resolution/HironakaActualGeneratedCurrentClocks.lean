import Hironaka.Resolution.HironakaActualGeneratedCurrentHistories
import Hironaka.Resolution.HironakaActualRawOrderLocality

/-! Original nonmonomial-order clocks and ordered labels across generated
DIFFERENT actual histories, derived from raw geometry rather than supplied
matching certificates. Recursive family values remain a separate problem. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedCurrentClocks
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism
open RelativePrincipalizationSpan NonmonomialOrderLocal NonmonomialOrderRegime StepOneRegime
open HironakaActualRawRecordPullbacks HironakaActualRawOrderLocality HironakaActualGeneratedCurrentHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}
 {A : MarkedIdeal n X} {B : MarkedIdeal n X'}

theorem generated_order_and_cosupp
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (z : U) :
 nmOrd (geoTransformAlong A S) z.val=nmOrd (geoTransformAlong B T) (η z).val ∧
   (z.val∈(geoTransformAlong A S).cosupp ↔ (η z).val∈(geoTransformAlong B T).cosupp) := by
 have hBhol : ∀x g,B.ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg
 have hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g :=
   fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hB.isCoherent hg
 exact order_and_cosupp_from_records (geoTransformAlong A S) (geoTransformAlong B T)
   (holomorphic_geoTransformAlong A hA S) (span_closed_geoTransformAlong A hAc S)
   (holomorphic_geoTransformAlong B hBhol T) (span_closed_geoTransformAlong B hBc T)
   U U' η (H.whole_records hA hB) z

theorem generated_ordRegime_iff
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (o : ℕ) (z : U) :
 OrdRegime A o S z.val ↔ OrdRegime B o T (η z).val := by
 have h := generated_order_and_cosupp hA hAc hB H z
 exact and_congr h.2 (by rw [h.1])

/-- The entire trailing chronological order-regime clock is transported
through actual generated steps and arbitrary current-open shrinkings. -/
theorem generated_regimeRun_ordRegime
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed) (o : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) :
 ∀z : U,regimeRun (OrdRegime A o) S z.val=regimeRun (OrdRegime B o) T (η z).val := by
 classical
 induction H with
 | initial => intro z; rfl
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   intro z
   exact ih ⟨z.val,hV z.property⟩
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   intro z
   rw [regimeRun_step,regimeRun_step,nextComparison_square hπ hπ' U U' η hC z]
   have hreg := generated_ordRegime_iff hA hAc hB H o ⟨π z.val,z.property⟩
   by_cases hr : OrdRegime A o S (π z.val)
   · rw [if_pos hr,if_pos (hreg.mp hr),ih ⟨π z.val,z.property⟩]
   · rw [if_neg hr,if_neg (fun h => hr (hreg.mpr h))]

/-- Every ordered prefix of the original full boundary list, including any
cut between old and born labels, is retained at the same positions. -/
theorem generated_boundary_prefixes
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x) (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (m : ℕ) :
 ((geoTransformAlong A S).E.take m).map ((Subtype.val : U → Y) ⁻¹' ·) =
   (((geoTransformAlong B T).E.take m).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) := by
 have hE := congrArg MarkedIdeal.E (H.whole_records hA hB)
 have h := congrArg (List.take m) hE
 simpa only [MarkedIdeal.pullback,List.map_take] using h

end
end Hironaka.HironakaActualGeneratedCurrentClocks
