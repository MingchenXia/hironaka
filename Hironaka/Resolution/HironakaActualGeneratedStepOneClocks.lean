import Hironaka.Resolution.HironakaActualGeneratedMaskedHistories
import Hironaka.Invariant.StepOneTowerIso

/-! Actual ORIGINAL StepOne levels, special loci and all regime clocks across
generated DIFFERENT histories. No numerical or locus comparisons are supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedStepOneClocks
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
open StepOneValue StepOneRegime StepOneLowerDomain CodimOneSupportAlong MemberInterLocusAlong
open BoundaryCount
open HironakaActualGeneratedCurrentHistories HironakaActualGeneratedCurrentClocks
open HironakaActualRawRecordPullbacks
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem generated_original_boundary_length {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) : A.E.length=B.E.length := by
 induction H with
 | initial _ _ _ hrec =>
   have h := congrArg (fun Q => Q.E.length) hrec
   simpa only [MarkedIdeal.pullback,List.length_map] using h
 | shrink _ _ _ _ _ _ ih => exact ih
 | step _ _ _ _ _ ih => exact ih

private theorem record_cosupp_traces (A : MarkedIdeal n Y) (B : MarkedIdeal n Y')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Y) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y') B)) :
 (Subtype.val : U → Y) ⁻¹' A.cosupp=η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' B.cosupp) := by
 have h := congrArg MarkedIdeal.cosupp hrec
 have hBU : ∀x g,(MarkedIdeal.pullback (Subtype.val : U' → Y') B).ideal.mem x g → HolomorphicAt n g x :=
   fun _ _ hg => hg.1
 rw [cosupp_pullback_val A hA U,MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
   η.contMDiff η.symm.contMDiff η.apply_symm_apply η.symm_apply_apply _ hBU,
   cosupp_pullback_val B hB U'] at h
 exact h

private theorem record_codim_one_traces (A : MarkedIdeal n Y) (B : MarkedIdeal n Y')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens Y) (U' : Opens Y')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Y) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y') B)) :
 (Subtype.val : U → Y) ⁻¹' codimOnePartAlong A.N A.ideal A.d=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' codimOnePartAlong B.N B.ideal B.d) := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → Y') B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hs := CodimOnePartCanonical.codimOnePartAlong_pullback_val U (N := A.N) hA A.d
 have hm := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => codimOnePartAlong Q.N Q.ideal Q.d) hrec
 have ht₁ := CodimOnePartCanonical.codimOnePartAlong_pullback η (N := BU.N) hBU BU.d
 have ht₂ := CodimOnePartCanonical.codimOnePartAlong_pullback_val U' (N := B.N) hB B.d
 exact hs.symm.trans (hm.trans (ht₁.trans (congrArg (η ⁻¹' ·) ht₂)))

/-- Whole StepOne records derive the original-member traces, original
levels, actual special loci and every level regime on the current window. -/
theorem original_step_one_facts_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'}
 {η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U'}
 (hlen : A.E.length=B.E.length)
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong (barMarked A) S)=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y') (geoTransformAlong (barMarked B) T))) :
 (origMembers A S).map ((Subtype.val : U → Y) ⁻¹' ·) =
   ((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) ∧
 ∀z : U,level A S z.val=level B T (η z).val ∧
   (IsSpecial A S z.val ↔ IsSpecial B T (η z).val) ∧
   ∀s,stepRegime A s S z.val ↔ stepRegime B s T (η z).val := by
 have hE := congrArg MarkedIdeal.E hrec
 have hOld' : ((geoTransformAlong (barMarked A) S).E.take A.E.length).map ((Subtype.val : U → Y) ⁻¹' ·) =
     (((geoTransformAlong (barMarked B) T).E.take A.E.length).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) := by
   have h := congrArg (List.take A.E.length) hE
   simpa only [MarkedIdeal.pullback,List.map_take] using h
 have hOld : (origMembers A S).map ((Subtype.val : U → Y) ⁻¹' ·) =
     ((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) := by
   simpa only [origMembers,←hlen] using hOld'
 let AS := geoTransformAlong (barMarked A) S
 let BT := geoTransformAlong (barMarked B) T
 have hsHol := holomorphic_geoTransformAlong (barMarked A) (fun _ _ hg => hg.1) S
 have htHol := holomorphic_geoTransformAlong (barMarked B) (fun _ _ hg => hg.1) T
 have hN : (Subtype.val : U → Y) ⁻¹' AS.N=η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' BT.N) :=
   congrArg MarkedIdeal.N hrec
 have hCos := record_cosupp_traces AS BT hsHol htHol U U' η hrec
 have hCod := record_codim_one_traces AS BT hsHol htHol U U' η hrec
 have hMs := memberInterLocus_preimage (Subtype.val : U → Y)
   (fun z => U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) AS.N (origMembers A S) AS.cosupp
 have hMt := memberInterLocus_preimage (Subtype.val : U' → Y')
   (fun z => U'.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z) BT.N (origMembers B T) BT.cosupp
 have hMe := memberInterLocus_preimage η (fun z => η.toHomeomorph.map_nhds_eq z)
   ((Subtype.val : U' → Y') ⁻¹' BT.N) ((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·))
   ((Subtype.val : U' → Y') ⁻¹' BT.cosupp)
 have hSets : memberInterLocus ((Subtype.val : U → Y) ⁻¹' AS.N)
     ((origMembers A S).map ((Subtype.val : U → Y) ⁻¹' ·)) ((Subtype.val : U → Y) ⁻¹' AS.cosupp)=
   memberInterLocus (η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' BT.N))
     (((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·))
     (η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' BT.cosupp)) := by rw [hN,hOld,hCos]
 have hMem := hMs.symm.trans (hSets.trans (hMe.trans (congrArg (η ⁻¹' ·) hMt)))
 refine ⟨hOld,fun z => ?_⟩
 have hl : level A S z.val=level B T (η z).val := by
   have hs := CodimOnePartCanonical.boundaryCount_map_preimage (Subtype.val : U → Y) (origMembers A S) z
   have hm := congrArg (fun E => boundaryCount E z) hOld
   have ht₁ := CodimOnePartCanonical.boundaryCount_map_preimage η
     ((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·)) z
   have ht₂ := CodimOnePartCanonical.boundaryCount_map_preimage (Subtype.val : U' → Y') (origMembers B T) (η z)
   exact hs.symm.trans (hm.trans (ht₁.trans ht₂))
 have hc : z.val∈codimOnePartAlong AS.N AS.ideal AS.d ↔
     (η z).val∈codimOnePartAlong BT.N BT.ideal BT.d :=
   Iff.of_eq (congrArg (fun E : Set U => z∈E) hCod)
 have hm : z.val∈memberInterLocus AS.N (origMembers A S) AS.cosupp ↔
     (η z).val∈memberInterLocus BT.N (origMembers B T) BT.cosupp :=
   Iff.of_eq (congrArg (fun E : Set U => z∈E) hMem)
 have hsp : IsSpecial A S z.val ↔ IsSpecial B T (η z).val := by
   unfold IsSpecial
   rw [hl]
   exact or_congr (and_congr Iff.rfl hc) (and_congr Iff.rfl hm)
 exact ⟨hl,hsp,fun s => by unfold stepRegime;rw [hl,hsp]⟩

theorem generated_step_one_facts (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated (barMarked A) (barMarked B) S T U U' η) :
 (origMembers A S).map ((Subtype.val : U → Y) ⁻¹' ·) =
   ((origMembers B T).map ((Subtype.val : U' → Y') ⁻¹' ·)).map (η ⁻¹' ·) ∧
 ∀z : U,level A S z.val=level B T (η z).val ∧
   (IsSpecial A S z.val ↔ IsSpecial B T (η z).val) ∧
   ∀s,stepRegime A s S z.val ↔ stepRegime B s T (η z).val := by
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := isWellFormed_barMarked B hB
 have hlen := generated_original_boundary_length (A := barMarked A) (B := barMarked B) H
 exact original_step_one_facts_from_records A B hlen (H.whole_records hAbar hBbar)

/-- Every original StepOne level/special regime clock is transported along
the full generated different histories, including all current shrinkings. -/
theorem generated_step_one_regime_clocks (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hB : B.IsWellFormed) (s : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated (barMarked A) (barMarked B) S T U U' η) :
 ∀z : U,regimeRun (stepRegime A s) S z.val=regimeRun (stepRegime B s) T (η z).val := by
 classical
 induction H with
 | initial => intro z;rfl
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   intro z
   exact ih ⟨z.val,hV z.property⟩
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   intro z
   rw [regimeRun_step,regimeRun_step,nextComparison_square hπ hπ' U U' η hC z]
   have hreg := ((generated_step_one_facts A B hB H).2 ⟨π z.val,z.property⟩).2.2 s
   by_cases hr : stepRegime A s S (π z.val)
   · rw [if_pos hr,if_pos (hreg.mp hr),ih ⟨π z.val,z.property⟩]
   · rw [if_neg hr,if_neg (fun h => hr (hreg.mpr h))]

/-- The positive-level ORIGINAL mask at an actual head point has matching
current traces. The interior in the raw source definition is preserved. -/
theorem original_member_mask_traces_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'}
 {η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U'}
 (hlen : A.E.length=B.E.length)
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong (barMarked A) S)=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Y') (geoTransformAlong (barMarked B) T))) (p : U) :
 (Subtype.val : U → Y) ⁻¹' (maskA A S p.val : Set Y)=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (maskA B T (η p).val : Set Y')) := by
 have hFacts := original_step_one_facts_from_records A B hlen hrec
 have hOld := hFacts.1
 have hK (w : U) :
     ((∀E∈origMembers A S,w.val∈E → p.val∈E) ∧
       ¬(level A S w.val=level A S p.val ∧ IsSpecial A S w.val)) ↔
     ((∀E∈origMembers B T,(η w).val∈E → (η p).val∈E) ∧
       ¬(level B T (η w).val=level B T (η p).val ∧ IsSpecial B T (η w).val)) := by
   have hlist := congrArg (fun E : List (Set U) => ∀K∈E,w∈K → p∈K) hOld
   have hlist' : (∀E∈origMembers A S,w.val∈E → p.val∈E) ↔
       (∀E∈origMembers B T,(η w).val∈E → (η p).val∈E) := by
     simpa only [List.forall_mem_map,mem_preimage] using Iff.of_eq hlist
   exact and_congr hlist' (not_congr (and_congr
     (by rw [(hFacts.2 w).1,(hFacts.2 p).1]) (hFacts.2 w).2.1))
 ext z
 change z.val∈interior {w | (∀E∈origMembers A S,w∈E → p.val∈E) ∧
       ¬(level A S w=level A S p.val ∧ IsSpecial A S w)} ↔
   (η z).val∈interior {w | (∀E∈origMembers B T,w∈E → (η p).val∈E) ∧
       ¬(level B T w=level B T (η p).val ∧ IsSpecial B T w)}
 rw [mem_interior_iff_mem_nhds,mem_interior_iff_mem_nhds]
 change (∀ᶠw : Y in 𝓝 z.val,(∀E∈origMembers A S,w∈E → p.val∈E) ∧
       ¬(level A S w=level A S p.val ∧ IsSpecial A S w)) ↔
   (∀ᶠw : Y' in 𝓝 (η z).val,(∀E∈origMembers B T,w∈E → (η p).val∈E) ∧
       ¬(level B T w=level B T (η p).val ∧ IsSpecial B T w))
 rw [eventually_nhds_val_iff U,eventually_nhds_val_iff U']
 have hηmap : Filter.map (η : U → U') (𝓝 z)=𝓝 (η z) := η.toHomeomorph.map_nhds_eq z
 rw [←hηmap,Filter.eventually_map]
 exact eventually_congr (Eventually.of_forall hK)

theorem generated_original_member_mask_traces (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hB : B.IsWellFormed)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated (barMarked A) (barMarked B) S T U U' η) (p : U) :
 (Subtype.val : U → Y) ⁻¹' (maskA A S p.val : Set Y)=
   η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (maskA B T (η p).val : Set Y')) := by
 have hAbar : ∀x g,(barMarked A).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBbar := isWellFormed_barMarked B hB
 have hlen := generated_original_boundary_length (A := barMarked A) (B := barMarked B) H
 exact original_member_mask_traces_from_records A B hlen (H.whole_records hAbar hBbar) p

end
end Hironaka.HironakaActualGeneratedStepOneClocks
