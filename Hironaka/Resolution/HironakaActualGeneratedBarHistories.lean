import Hironaka.Resolution.HironakaActualGeneratedCompanionHistories
import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality

/-! Derive actual StepOne BAR histories from original raw marked histories.
Raw and bar record identities are kept distinct throughout. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeneratedBarHistories
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism RelativePrincipalizationSpan StepOneValue
open DerivativeIdealAlongEtale CompanionRebase
open HironakaActualNonregularCoefficientNaturality HironakaActualGeneratedCurrentHistories
open HironakaActualGeneratedCompanionHistories
noncomputable section
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem bar_records_from_original_records (A : MarkedIdeal n X) (B : MarkedIdeal n X')
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 (U : Opens X) (U' : Opens X')
 (η : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → X) A =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') B)) :
 MarkedIdeal.pullback (Subtype.val : U → X) (barMarked A) =
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → X') (barMarked B)) := by
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → X') B
 have hBU : ∀x g,BU.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
 have hs := pullback_coeff_homMarkedAlong (X := X) (Z := CMfd.of (n := n) U)
   contMDiff_subtype_val (fun p => ⟨openInv U p,isLocalInverseAt_val U p⟩) A hA
 have hm := congrArg (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => barMarked Q) hrec
 have ht₁ := pullback_coeff_homMarkedAlong η.contMDiff
   (fun p => ⟨η.symm,isLocalInverseAt_diffeo η p⟩) BU hBU
 have ht₂ := pullback_coeff_homMarkedAlong (X := X') (Z := CMfd.of (n := n) U')
   contMDiff_subtype_val (fun p => ⟨openInv U' p,isLocalInverseAt_val U' p⟩) B hB
 exact hs.trans (hm.trans (ht₁.symm.trans (congrArg (MarkedIdeal.pullback η) ht₂.symm)))

/-- Original raw histories internally produce their bar histories. The
actual target bar testness is natural canonical StepOne data; no source
bar testness or desired bar-record comparison is supplied. -/
theorem generated_bar_histories {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
 (hA : ∀x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hB : ∀x g,B.ideal.mem x g → HolomorphicAt n g x)
 {S : BlowupTower X Y} {T : BlowupTower X' Y'} {U : Opens Y} {U' : Opens Y'} {η}
 (H : Generated A B S T U U' η) (hTarget : IsGeoTestTower (barMarked B) T) :
 Generated (barMarked A) (barMarked B) S T U U' η :=
 generated_change_initial_records (barMarked A) (barMarked B)
   (fun V V' φ hrec => bar_records_from_original_records A B hA hB V V' φ hrec) H hTarget

end
end Hironaka.HironakaActualGeneratedBarHistories
