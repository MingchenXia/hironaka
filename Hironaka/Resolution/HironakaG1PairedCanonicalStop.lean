import Hironaka.Resolution.HironakaG1LiteralSectionOrderEndpoint

/-! # Largest common canonical prefix on an actual padded history -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1PairedCanonicalStop
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials

universe u v w

section Towers

variable {n : ℕ} {X : CMfd.{u} n}
  {A B : Type*} [LinearOrder A] [LinearOrder B]
  (P S : MarkedIdeal n X)
  (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → A)
  (g : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → B)

/-- A rejected step is occupied, is the first clock's actual maximum
centre, and occurs where the two endpoint maximum loci disagree. -/
def RejectedCentre : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => False
  | _, .step R C _ _ =>
    C.Nonempty ∧ C = maxLocus (f R) (geoTransformAlong P R).cosupp ∧
      maxLocus (f R) (geoTransformAlong P R).cosupp ≠
        maxLocus (g R) (geoTransformAlong S R).cosupp

/-- At a shared canonical prefix, a genuine occupied step prescribed by
the first clock extends the second exactly when their actual maxima agree. -/
theorem canonical_extension_iff_maximum_agreement
    {Y Z : CMfd.{u} n} (R : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hC : C.Nonempty)
    (hf : IsCanonical P f (.step R C π hπ)) (hg : IsCanonical S g R) :
    IsCanonical S g (.step R C π hπ) ↔
      maxLocus (f R) (geoTransformAlong P R).cosupp =
        maxLocus (g R) (geoTransformAlong S R).cosupp := by
  have hF := hf.2.resolve_left hC.ne_empty
  constructor
  · intro hs
    exact hF.symm.trans (hs.2.resolve_left hC.ne_empty)
  · intro heq
    exact ⟨hg, Or.inr (hF.trans heq)⟩

/-- Either the actual canonical tower is canonical for both clocks, or
there is an exact first rejected occupied centre. If the rejection occurs
at the head omitting the last `j` steps, the largest shared canonical head
omits the last `j + 1` steps, and this bound decides all other prefixes. -/
theorem canonical_prefix_or_first_rejected_centre :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical P f T →
      IsCanonical S g T ∨
        ∃ j < T.length, RejectedCentre P S f g (head T j) ∧
          ∀ i, IsCanonical S g (head T i) ↔ j+1 ≤ i := by
  intro Y T
  induction T with
  | refl => exact fun _ => Or.inl trivial
  | @step Y Z R C π hπ ih =>
    intro hf
    rcases ih hf.1 with hg | ⟨j,hj,hBad,hCuts⟩
    · by_cases hNext : IsCanonical S g (.step R C π hπ)
      · exact Or.inl hNext
      · have hC : C.Nonempty := by
          by_contra h
          exact hNext ⟨hg,Or.inl (Set.not_nonempty_iff_eq_empty.mp h)⟩
        have hE := hf.2.resolve_left hC.ne_empty
        have hNe := mt ((canonical_extension_iff_maximum_agreement P S f g R C π hπ hC hf hg).mpr) hNext
        refine Or.inr ⟨0, by simp, ⟨hC,hE,hNe⟩, ?_⟩
        intro i
        cases i with
        | zero => exact iff_of_false hNext (by omega)
        | succ i => exact iff_of_true (isCanonical_head S g R i hg) (by omega)
    · refine Or.inr ⟨j+1, by simp only [BlowupTower.length_step]; omega, hBad, ?_⟩
      intro i
      cases i with
      | zero =>
        refine iff_of_false ?_ (by omega)
        intro hs
        have hR := (hCuts 0).mp (isCanonical_head S g R 0 hs.1)
        omega
      | succ i =>
        exact (hCuts i).trans (by omega)

end Towers

section Normal

variable {n k : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n+1)}
  (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)

local notation "P" => properNormalMarked Q
local notation "S" => sectionMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) P
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) S

set_option maxHeartbeats 1400000 in
/-- The normalized padded and literal section records have equal cosupport
on every actual prefix. Their canonical clocks share precisely the initial
prefix before the first occupied centre on which their maxima disagree. -/
theorem literal_section_paired_canonical_stop
    (hQ : IsInvDomain (k+1) Q) (hCan : IsCanonical P f T) :
    (∀ i, (geoTransformAlong P (head T i)).cosupp =
      (geoTransformAlong S (head T i)).cosupp) ∧
    (IsCanonical S g T ∨
      ∃ j < T.length, RejectedCentre P S f g (head T j) ∧
        ∀ i, (IsCanonical P f (head T i) ∧ IsCanonical S g (head T i)) ↔ j+1 ≤ i) := by
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := k+2)
    (invFamily (Nat.succ_pos n) (k+1)) P hP hMax (Nat.succ_pos n) T hCan).2.1
  constructor
  · intro i
    have hH := ((isGeoTestTower_iff_head_tail P T i).mp hTest).1
    exact ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 (head T i)).2 hH
  · rcases canonical_prefix_or_first_rejected_centre P S f g T hCan with hg | ⟨j,hj,hBad,hCuts⟩
    · exact Or.inl hg
    · refine Or.inr ⟨j,hj,hBad,?_⟩
      intro i
      exact ⟨fun h => (hCuts i).mp h.2,
        fun hi => ⟨isCanonical_head P f T i hCan,(hCuts i).mpr hi⟩⟩

end Normal

section Cartier
open HironakaG1CartierTwoAnchors HironakaG1LiteralSectionOrderEndpoint
local notation "Y₀" => HironakaG1LaterPositiveNormalExample.Y
local notation "B₀" => HironakaG1LaterPositiveNormalExample.B
local notation "pInv" => Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P
local notation "sInv" => Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S

/-- At the Cartier endpoint every genuine occupied padded canonical step
has the Cartier prefix as its largest common canonical head. -/
theorem cartier_exact_paired_stop
    {Z : CMfd.{0} 3} (D : Set Y₀) (hD : D.Nonempty) (π : Z → Y₀)
    (hπ : IsBlowupAlong 3 D π) (hCan : IsCanonical P pInv (.step B₀ D π hπ)) :
    RejectedCentre P S pInv sInv (.step B₀ D π hπ) ∧
      ∀ i, (IsCanonical P pInv (head (.step B₀ D π hπ) i) ∧
        IsCanonical S sInv (head (.step B₀ D π hπ) i)) ↔ 1 ≤ i := by
  have hn := cartier_no_shared_nonempty_canonical_step D hD π hπ
  refine ⟨⟨hD,hCan.2.resolve_left hD.ne_empty,cartier_common_prefix_maximum_discrepancy⟩,?_⟩
  intro i
  cases i with
  | zero => exact iff_of_false hn (by omega)
  | succ i =>
    exact iff_of_true ⟨isCanonical_head P pInv B₀ i cartier_common_first_canonical.1,
      isCanonical_head S sInv B₀ i cartier_common_first_canonical.2⟩ (by omega)

end Cartier
end
end Hironaka.HironakaG1PairedCanonicalStop
