import Hironaka.Resolution.HironakaActualGeneratedOriginalOrderMasks

/-! Transplanting actual generated histories to unchanged original companion
records. Only initial raw record naturality and actual TARGET testness are
used; no source companion testness or numerical equality is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedCompanionHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan CompanionRebase
open DerivativeIdealAlongEtale InvertibleIdealQuotient
open HironakaActualGeneratedCurrentHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

/-- Geometric history generation can be reused for new literal initial
records when their initial local identity is derived and the target is a
test history for them. No post-record identity is a successor premise. -/
theorem generated_change_initial_records {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (A' : MarkedIdeal n X) (B' : MarkedIdeal n X')
 (hInitial : ∀(V : Opens X) (V' : Opens X')
   (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V'),
   MarkedIdeal.pullback (Subtype.val : V → X) A =
     MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X') B) →
   MarkedIdeal.pullback (Subtype.val : V → X) A' =
     MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X') B'))
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (hT : IsGeoTestTower B' T) :
 Generated A' B' S T U U' η := by
 revert hT
 induction H with
 | initial V V' φ hrec =>
   intro _
   exact Generated.initial V V' φ (hInitial V V' φ hrec)
 | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
   intro ht
   exact Generated.shrink (ih ht) V V' hV hV' htr
 | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
   intro ht
   exact Generated.step (ih ht.1) ht.2 hπ hπ' hC

/-- Raw companion naturality derives the entire initial reference identity
between different original records, retaining all boundary labels. -/
theorem companion_records_from_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g)
 (o : ℕ) (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B)) :
 MarkedIdeal.pullback (Subtype.val : U → X) (companionOf n A o) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') (companionOf n B o)) := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → X') B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hBUc : ∀x g,IsInSpanAt (n := n) (BU.ideal.mem x) x g → BU.ideal.mem x g := by
   intro x g hg
   dsimp only [BU,MarkedIdeal.pullback,GermIdeal.pullback] at hg ⊢
   exact IsInSpanAt.trans (fun _ hs => hs) hg
 have hs := HironakaActualRawCompanionNaturality.pullback_companionOf
   (X := X) (Y := CMfd.of (n := n) U) contMDiff_subtype_val
   (fun p => ⟨openInv U p,isLocalInverseAt_val U p⟩) A hA hAc o
 have hm := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => companionOf n Q o) hrec
 have ht₁ := HironakaActualRawCompanionNaturality.pullback_companionOf
   η.contMDiff (fun p => ⟨η.symm,isLocalInverseAt_diffeo η p⟩) BU hBU hBUc o
 have ht₂ := HironakaActualRawCompanionNaturality.pullback_companionOf
   (X := X') (Y := CMfd.of (n := n) U') contMDiff_subtype_val
   (fun p => ⟨openInv U' p,isLocalInverseAt_val U' p⟩) B hB hBc o
 exact hs.trans (hm.trans (ht₁.symm.trans (congrArg (MarkedIdeal.pullback η) ht₂.symm)))

/-- Whole original companion histories are internally generated from the
original paired geometry and raw companion naturality. The target test
premise can be supplied by canonical lower-tail data. It is not a value
comparison, and no source companion admissibility is assumed. -/
theorem generated_original_companion_histories {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hAc : ∀x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (hBc : ∀x g,IsInSpanAt (n := n) (B.ideal.mem x) x g → B.ideal.mem x g)
 (o : ℕ) {S : BlowupTower X Y} {T : BlowupTower X' Y'}
 {U : Opens Y} {U' : Opens Y'} {η} (H : Generated A B S T U U' η)
 (ht : IsGeoTestTower (companionOf n B o) T) :
 Generated (companionOf n A o) (companionOf n B o) S T U U' η :=
 generated_change_initial_records (companionOf n A o) (companionOf n B o)
   (fun V V' φ hrec => companion_records_from_records A B hA hAc hB hBc o V V' φ hrec) H ht

end
end Hironaka.HironakaActualGeneratedCompanionHistories
