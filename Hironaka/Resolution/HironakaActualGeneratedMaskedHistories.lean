import Hironaka.Resolution.HironakaActualGeneratedCompanionHistories

/-! The paired histories on the UNCHANGED original masks are internally
generated from real centre traces. This carries chronological geometry,
not merely a terminal numerical or record matching certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedMaskedHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan NonmonomialOrderTail MarkedIdealRestrictOpen
open HironakaActualGeneratedCurrentHistories HironakaActualGeneratedOriginalOrderMasks
open HironakaActualGeneratedCompanionHistories CompanionRebase
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem exists_generated_original_masked_histories {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed) (o : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) :
 let Ws := openPreimage S (ordMask A o)
 let Wt := openPreimage T (ordMask B o)
 ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens Ws U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (MaxLocusLocal.nestedOpens Wt U'),
   (∀p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   Generated
     (MarkedIdeal.pullback (Subtype.val : ordMask A o → X) A)
     (MarkedIdeal.pullback (Subtype.val : ordMask B o → X') B)
     (restrict (ordMask A o) S) (restrict (ordMask B o) T)
     (MaxLocusLocal.nestedOpens Ws U) (MaxLocusLocal.nestedOpens Wt U') ν := by
 induction H with
 | initial U U' η hrec =>
   obtain ⟨ν,hν,hνrec⟩ := exists_generated_original_masked_whole_records hA hAc hB o
     (Generated.initial U U' η hrec)
   exact ⟨ν,hν,Generated.initial
     (X := CMfd.of (n := n) (ordMask A o)) (X' := CMfd.of (n := n) (ordMask B o))
     _ _ ν hνrec⟩
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   obtain ⟨ν,hν,Hν⟩ := ih
   let Ws := openPreimage S (ordMask A o)
   let Wt := openPreimage T (ordMask B o)
   let Vs := MaxLocusLocal.nestedOpens Ws V
   let Vt := MaxLocusLocal.nestedOpens Wt V'
   have hs : (Vs : Set Ws) ⊆ MaxLocusLocal.nestedOpens Ws U := fun p hp => hV hp
   have ht : (Vt : Set Wt) ⊆ MaxLocusLocal.nestedOpens Wt U' := fun p hp => hV' hp
   have htrace : ν ⁻¹' ((Subtype.val : MaxLocusLocal.nestedOpens Wt U' → Wt) ⁻¹' (Vt : Set Wt)) =
       (Subtype.val : MaxLocusLocal.nestedOpens Ws U → Ws) ⁻¹' (Vs : Set Ws) := by
     ext p
     change (ν p).val.val∈V' ↔ p.val.val∈V
     rw [hν p]
     exact Set.ext_iff.mp htr ⟨p.val.val,p.property⟩
   let ρ := restrictComparison (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     ν Vs Vt hs ht htrace
   have Hρ := Generated.shrink (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     Hν Vs Vt hs ht htrace
   obtain ⟨ψ,hψ,_hψrec⟩ := exists_generated_original_masked_whole_records hA hAc hB o
     (Generated.shrink H V V' hV hV' htr)
   have hEq : ψ=ρ := by
     apply Diffeomorph.ext
     intro p
     apply Subtype.ext
     apply Subtype.ext
     exact (hψ p).trans (hν ⟨p.val,hs p.property⟩).symm
   exact ⟨ψ,hψ,hEq.symm ▸ Hρ⟩
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   obtain ⟨ν,hν,Hν⟩ := ih
   let Ws := openPreimage S (ordMask A o)
   let Wt := openPreimage T (ordMask B o)
   let Ws₁ := openPreimage (.step S C π hπ) (ordMask A o)
   let Wt₁ := openPreimage (.step T C' π' hπ') (ordMask B o)
   let Us := MaxLocusLocal.nestedOpens Ws U
   let Ut := MaxLocusLocal.nestedOpens Wt U'
   let r : Ws₁ → Ws := fun p => ⟨π p.val,p.property⟩
   let r' : Wt₁ → Wt := fun p => ⟨π' p.val,p.property⟩
   have hs : IsBlowupAlong n ((Subtype.val : Ws → Y) ⁻¹' C) r :=
     BlowupRestrictOpen.isBlowupAlong_restrict hπ Ws Ws₁.isOpen
   have ht : IsBlowupAlong n ((Subtype.val : Wt → Y') ⁻¹' C') r' :=
     BlowupRestrictOpen.isBlowupAlong_restrict hπ' Wt Wt₁.isOpen
   have htrace : ν ⁻¹' ((Subtype.val : Ut → Wt) ⁻¹' ((Subtype.val : Wt → Y') ⁻¹' C')) =
       (Subtype.val : Us → Ws) ⁻¹' ((Subtype.val : Ws → Y) ⁻¹' C) := by
     ext p
     change (ν p).val.val∈C' ↔ p.val.val∈C
     rw [hν p]
     exact Set.ext_iff.mp hC ⟨p.val.val,p.property⟩
   have Hstep := Generated.step H hAdm' hπ hπ' hC
   have hTarget := isGeoTestTower_restrict (ordMask B o)
     hB.isClosedSubmanifold_N hB.isCoherent (.step T C' π' hπ') Hstep.target_test
   have Hnext := Generated.step
     (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
     (Z := CMfd.of (n := n) Ws₁) (Z' := CMfd.of (n := n) Wt₁)
     Hν hTarget.2 hs ht htrace
   obtain ⟨ψ,hψ,_hψrec⟩ := exists_generated_original_masked_whole_records hA hAc hB o Hstep
   have hψsq : ∀p,r' (ψ p).val=(ν ⟨r p.val,p.property⟩).val := by
     intro p
     apply Subtype.ext
     change π' (ψ p).val.val=(ν ⟨⟨π p.val.val,p.val.property⟩,p.property⟩).val.val
     rw [hψ p,nextComparison_square hπ hπ' U U' η hC]
     exact (hν ⟨⟨π p.val.val,p.val.property⟩,p.property⟩).symm
   have hEq : ψ=nextComparison
       (Y := CMfd.of (n := n) Ws) (Y' := CMfd.of (n := n) Wt)
       (Z := CMfd.of (n := n) Ws₁) (Z' := CMfd.of (n := n) Wt₁) hs ht Us Ut ν htrace :=
     (Classical.choose_spec
       (HironakaActualDifferentHistoryRecords.existsUnique_next_comparison
         (X := CMfd.of (n := n) Ws) (X' := CMfd.of (n := n) Wt)
         (Y := CMfd.of (n := n) Ws₁) (Y' := CMfd.of (n := n) Wt₁)
         hs ht Us Ut ν htrace)).2 ψ hψsq
   exact ⟨ψ,hψ,hEq.symm ▸ Hnext⟩

/-- The complete actual companion reference histories on unchanged original
head masks are generated internally. Canonical lower-tail data need supply
only actual target testness, never source testness or a value comparison. -/
theorem exists_generated_actual_companion_reference_histories {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : B.IsWellFormed) (o : ℕ)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η)
 (hTarget : IsGeoTestTower
   (companionOf n (MarkedIdeal.pullback (Subtype.val : ordMask B o → X') B) o)
   (restrict (ordMask B o) T)) :
 let Ws := openPreimage S (ordMask A o)
 let Wt := openPreimage T (ordMask B o)
 ∃ν : CMfd.of (n := n) (MaxLocusLocal.nestedOpens Ws U)
     ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
       CMfd.of (n := n) (MaxLocusLocal.nestedOpens Wt U'),
   (∀p,(ν p).val.val=(η ⟨p.val.val,p.property⟩).val) ∧
   Generated
     (companionOf n (MarkedIdeal.pullback (Subtype.val : ordMask A o → X) A) o)
     (companionOf n (MarkedIdeal.pullback (Subtype.val : ordMask B o → X') B) o)
     (restrict (ordMask A o) S) (restrict (ordMask B o) T)
     (MaxLocusLocal.nestedOpens Ws U) (MaxLocusLocal.nestedOpens Wt U') ν := by
 obtain ⟨ν,hν,Hν⟩ := exists_generated_original_masked_histories hA hAc hB o H
 let AM : MarkedIdeal n (CMfd.of (n := n) (ordMask A o)) :=
   MarkedIdeal.pullback (Subtype.val : ordMask A o → X) A
 let BM : MarkedIdeal n (CMfd.of (n := n) (ordMask B o)) :=
   MarkedIdeal.pullback (Subtype.val : ordMask B o → X') B
 have hAM : ∀x g,AM.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBM : ∀x g,BM.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hAMc : ∀x g,IsInSpanAt (n := n) (AM.ideal.mem x) x g → AM.ideal.mem x g := by
   intro x g hg
   dsimp only [AM,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 have hBMc : ∀x g,IsInSpanAt (n := n) (BM.ideal.mem x) x g → BM.ideal.mem x g := by
   intro x g hg
   dsimp only [BM,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 exact ⟨ν,hν,generated_original_companion_histories hAM hAMc hBM hBMc o Hν hTarget⟩

end
end Hironaka.HironakaActualGeneratedMaskedHistories
