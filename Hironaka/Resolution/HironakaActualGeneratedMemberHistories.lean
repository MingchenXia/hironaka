import Hironaka.Resolution.HironakaActualGeneratedStepOneClocks
import Hironaka.Resolution.HironakaActualPointLocalMemberRestriction
import Hironaka.Resolution.HironakaActualAnchoredMaskedHistories

/-! Original positive-level reference records for different actual heads.
Chronological tail generation is added using anchored actual geometry. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedMemberHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
open StepOneValue StepOneLowerDomain InvDomainMemberRestriction InvDomainRebase
open HironakaActualGeneratedCurrentHistories HironakaActualGeneratedStepOneClocks
open HironakaActualRawRecordPullbacks HironakaActualPointLocalMemberRestriction
open HironakaActualAnchoredCurrentHistories HironakaActualAnchoredMaskedHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Any chosen original boundary prefix determines its actual whole member
reference record locally. Source SNC is needed only on the actual open
and is derived from the good target; born/old aliases are not erased. -/
theorem original_prefix_member_records_from_records
 (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : B.IsWellFormed) (hdB : 1≤B.d) (m : ℕ)
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B)) (p : U) :
 MarkedIdeal.pullback (Subtype.val : U → X)
     (memberRestrict A (membersThrough A.E (A.E.take m) p.val)) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X')
     (memberRestrict B (membersThrough B.E (B.E.take m) (η p).val))) := by
 have hE := congrArg MarkedIdeal.E hrec
 have hOld : (A.E.take m).map ((Subtype.val : U → X) ⁻¹' ·) =
     ((B.E.take m).map ((Subtype.val : U' → X') ⁻¹' ·)).map (η ⁻¹' ·) := by
   have h := congrArg (List.take m) hE
   simpa only [MarkedIdeal.pullback,List.map_take] using h
 exact current_member_records_from_whole_record A B hA hB hdB (A.E.take m) (B.E.take m)
   (fun _ h => List.mem_of_mem_take h) (fun _ h => List.mem_of_mem_take h) U U' η hrec hOld p

/-- At the ORIGINAL actual head, the positive-level unmasked reference
uses precisely the original members through that head point, with every
retained ordered boundary label preserved. -/
theorem generated_original_member_reference_records
 (A : MarkedIdeal n X) (B : MarkedIdeal n X') (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated (barMarked A) (barMarked B) S T U U' η) (p : U) :
 MarkedIdeal.pullback (Subtype.val : U → Y)
     (memberRestrict (geoTransformAlong (barMarked A) S)
       (membersThrough (geoTransformAlong (barMarked A) S).E (origMembers A S) p.val)) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y')
     (memberRestrict (geoTransformAlong (barMarked B) T)
       (membersThrough (geoTransformAlong (barMarked B) T).E (origMembers B T) (η p).val))) := by
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := isWellFormed_barMarked B hB
 have hBT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hBbar T H.target_test
 have hdBT : 1≤(geoTransformAlong (barMarked B) T).d := by
   rw [d_geoTransformAlong]
   exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
 have hOld := (generated_step_one_facts A B hB H).1
 exact current_member_records_from_whole_record
   (geoTransformAlong (barMarked A) S) (geoTransformAlong (barMarked B) T)
   (holomorphic_geoTransformAlong (barMarked A) hAbar S) hBT hdBT
   (origMembers A S) (origMembers B T)
   (fun _ h => List.mem_of_mem_take h) (fun _ h => List.mem_of_mem_take h)
   U U' η (H.whole_records hAbar hBbar) hOld p

/-- The complete original positive-level lower reference histories are
internally generated from ONE actual initial head comparison and its
anchored real-centre geometry. All original masks and tails are literal. -/
theorem exists_anchored_original_member_reference_histories
 {Y₀ Y₀' : CMfd.{u} n} (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (S₀ : BlowupTower X Y₀) (T₀ : BlowupTower X' Y₀')
 (hlen : A.E.length=B.E.length)
 (hBHead : (geoTransformAlong (barMarked B) T₀).IsWellFormed)
 {V₀ : Opens Y₀} {V₀' : Opens Y₀'}
 {φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀'}
 (hInitial : MarkedIdeal.pullback (Subtype.val : V₀ → Y₀) (geoTransformAlong (barMarked A) S₀)=
   MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → Y₀') (geoTransformAlong (barMarked B) T₀)))
 {S₁ : BlowupTower Y₀ Y} {T₁ : BlowupTower Y₀' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Anchored V₀ V₀' φ S₁ T₁ U U' η) (p : V₀) (s : ℕ)
 (hTarget : IsGeoTestTower (StepOneValueMasked.lowerMarkedM B (s+1) T₀ (φ p).val)
   (restrict (maskA B T₀ (φ p).val) T₁)) :
 let W := maskA A S₀ p.val
 let W' := maskA B T₀ (φ p).val
 ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens (openPreimage S₁ W) U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (MaxLocusLocal.nestedOpens (openPreimage T₁ W') U'),
   (∀z,(ν z).val.val=(η ⟨z.val.val,z.property⟩).val) ∧
   Generated (StepOneValueMasked.lowerMarkedM A (s+1) S₀ p.val)
     (StepOneValueMasked.lowerMarkedM B (s+1) T₀ (φ p).val)
     (restrict W S₁) (restrict W' T₁)
     (MaxLocusLocal.nestedOpens (openPreimage S₁ W) U)
     (MaxLocusLocal.nestedOpens (openPreimage T₁ W') U') ν := by
 let AS := geoTransformAlong (barMarked A) S₀
 let BT := geoTransformAlong (barMarked B) T₀
 let RA := memberRestrict AS (membersThrough AS.E (origMembers A S₀) p.val)
 let RB := memberRestrict BT (membersThrough BT.E (origMembers B T₀) (φ p).val)
 let W := maskA A S₀ p.val
 let W' := maskA B T₀ (φ p).val
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hAS := holomorphic_geoTransformAlong (barMarked A) hAbar S₀
 have hdBT : 1≤BT.d := by
   rw [d_geoTransformAlong]
   exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
 have hOld := (original_step_one_facts_from_records A B hlen hInitial).1
 have hMember := current_member_records_from_whole_record AS BT hAS hBHead hdBT
   (origMembers A S₀) (origMembers B T₀)
   (fun _ h => List.mem_of_mem_take h) (fun _ h => List.mem_of_mem_take h)
   V₀ V₀' φ hInitial hOld p
 have hMask := original_member_mask_traces_from_records A B hlen hInitial p
 have hRA : ∀x g,RA.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hRB : ∀x g,RB.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 obtain ⟨ψ,hψ,hRec⟩ :=
   HironakaActualCurrentMaskedReferenceValues.exists_actual_current_masked_reference_records
     RA RB hRA hRB W V₀ W' V₀' φ hMember hMask
 let φM := maskedComparison W V₀ W' V₀' φ hMask
 have hEq : ψ=φM := by
   apply Diffeomorph.ext
   intro z
   apply Subtype.ext
   apply Subtype.ext
   exact hψ z
 have hInitialM := hRec
 rw [hEq] at hInitialM
 obtain ⟨ν,hν,Hν⟩ := exists_anchored_original_masked_histories H W W' hMask
 have hGenerated := Hν.to_generated
   (StepOneValueMasked.lowerMarkedM A (s+1) S₀ p.val)
   (StepOneValueMasked.lowerMarkedM B (s+1) T₀ (φ p).val) hInitialM hTarget
 exact ⟨ν,hν,hGenerated⟩

end
end Hironaka.HironakaActualGeneratedMemberHistories
