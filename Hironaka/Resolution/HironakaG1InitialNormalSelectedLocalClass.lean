import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut
import Hironaka.Resolution.HironakaG1OriginalContactClassAtStage
import Hironaka.Resolution.HironakaG8PowerLowerMarks
import Hironaka.Resolution.HironakaG1InitialNormalSelectedSectionClass
import Hironaka.Resolution.HironakaG1InitialSelectedOrderPhase
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents
import Hironaka.Resolution.HironakaG1PositiveNormalRepairCentres

/-! Exact divisor exponents on the literal initial positive selected mask.
The ordered empty slots are retained on both actual records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1InitialNormalSelectedLocalClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked InvDomainMemberRestriction
  HironakaG1InitialNormalSelectedSectionClass HironakaG1InitialSelectedOrderPhase
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1PositiveNormalRepairCentres HironakaG8MixedBoundaryExponents
  HironakaActualPowerBoundaryExponents ContactStageKept BoundaryCount DivisorExponentAlong MarkedIdealOperationsAlong.MarkedIdeal

set_option maxHeartbeats 1000000 in
/-- On the actual initial positive mask the padded normal homogenized
contact and the genuine supported selected record have zero exponents in
every ordered boundary slot, including under crossed whole-power normalization. -/
theorem initial_normal_selected_mask_exponents_zero {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n+1) (productOpen U)) _) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n+1) (productOpen U)) _) p) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X)
    let O := maskA (properNormalMarked Q) H p
    let A := barMarked (X := X) (properNormalMarked Q)
    let B := barMarked (X := X) (supportedNormalMarked Q)
    let L := memberRestrict A (membersThrough A.E A.E p)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let K := contactMarkedKept (X := X) L (relativeNormalCoordinate U) H O
    let R := MarkedIdeal.pullback (Subtype.val : O → X) S
    K.E = R.E ∧
    (∀ H ∈ K.E, H = ∅) ∧
    ∀ (H : Set O), H ∈ K.E → ∀ (x : O) (e f : ℕ),
      divExpAlong (n+1) K.N
          (powerMarked (X := CMfd.of (n := n+1) O) K e).ideal H x = 0 ∧
      divExpAlong (n+1) R.N
          (powerMarked (X := CMfd.of (n := n+1) O) R f).ideal H x = 0 := by
  intro X H O A B L S K R
  let P := properNormalMarked Q
  have hOld : origMembers P H = A.E := List.take_length
  have hp : 0 < boundaryCount P.E p := by
    change boundaryCount (origMembers P H) p = s + 1 at hLevel
    rw [hOld] at hLevel
    change 0 < boundaryCount A.E p
    rw [hLevel]
    exact Nat.succ_pos s
  have hSame := initial_normal_selected_section_wEquiv Q hQ p hp O hpO
  have hOrdered : K.E = R.E := hSame.2.2.1
  have hLowerE := (original_initial_positive_lower_companion_eq Q hQ p (s := s) hLevel).1
  have hE : K.E = (lowerMarkedM P (s+1) H p).E := by
    change L.E.map ((Subtype.val : O → X) ⁻¹' ·) =
      (memberRestrict A (membersThrough A.E (origMembers P H) p)).E.map
        ((Subtype.val : O → X) ⁻¹' ·)
    rw [hOld]
  have hEmpty : ∀ D ∈ K.E, D = ∅ := fun D hD => hLowerE D (hE ▸ hD)
  refine ⟨hOrdered, hEmpty, ?_⟩
  intro D hD x e f
  rw [hEmpty D hD]
  exact ⟨divExpAlong_eq_zero_of_notMem (Y := CMfd.of (n := n+1) O)
      (N := K.N) (H := ∅) (I := (powerMarked (X := CMfd.of (n := n+1) O) K e).ideal)
      (x := x) (by simp) (by simp),
    divExpAlong_eq_zero_of_notMem (Y := CMfd.of (n := n+1) O)
      (N := R.N) (H := ∅) (I := (powerMarked (X := CMfd.of (n := n+1) O) R f).ideal)
      (x := x) (by simp) (by simp)⟩

private theorem coefficientMark_eq_factorial (d : ℕ) :
    HironakaG8PowerLowerMarks.coefficientMark d = Nat.factorial d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    unfold HironakaG8PowerLowerMarks.coefficientMark at *
    rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.sub_zero, ← ih, mul_comm]
    simp only [Nat.add_sub_add_right]

/-- The exact native marks are iterated factorial and linear, respectively. At selected
mark at least three, the two actual records cannot be restricted-equivalent
without changing a mark. -/
theorem initial_normal_selected_section_mark_obstruction {n k : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (p : productOpen U) (hp : 0 < boundaryCount (properNormalMarked Q).E p)
    (O : Opens (productOpen U)) (hpO : p ∈ O) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let A := barMarked (X := X) (properNormalMarked Q)
    let B := barMarked (X := X) (supportedNormalMarked Q)
    let L := memberRestrict A (membersThrough A.E A.E p)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let K := contactMarkedKept (X := X) L (relativeNormalCoordinate U) (.refl : BlowupTower X X) O
    let R := MarkedIdeal.pullback (Subtype.val : O → X) S
    K.d = Nat.factorial (Nat.factorial R.d) ∧
    (3 ≤ R.d → R.d < K.d ∧ ¬ RestrictEquiv (M := CMfd.of (n := n+1) O) K R) := by
  intro X A B L S K R
  have hSame := initial_normal_selected_section_wEquiv Q hQ p hp O hpO
  have hMark : K.d = Nat.factorial (Nat.factorial R.d) := by
    rw [hSame.2.2.2.2.1, HironakaG8PowerLowerMarks.coeffMarkedAlong_mark,
      coefficientMark_eq_factorial, hSame.2.2.2.1]
    rw [HironakaG8PowerLowerMarks.coeffMarkedAlong_mark, coefficientMark_eq_factorial]
    rfl
  refine ⟨hMark, fun hR => ?_⟩
  have hLt : R.d < K.d := hMark ▸ (Nat.lt_factorial_self hR).trans_le (Nat.self_le_factorial _)
  exact ⟨hLt, fun hEq => (Nat.ne_of_lt hLt) hEq.d_eq.symm⟩

set_option maxHeartbeats 1800000 in
/-- The two original initial selected records share the full weak product-test
class on every open of their common ambient space. -/
theorem initial_normal_selected_section_locWP {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : 0 < boundaryCount (properNormalMarked Q).E p)
    (O : Opens (productOpen U)) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let A := barMarked (X := X) (properNormalMarked Q)
    let B := barMarked (X := X) (supportedNormalMarked Q)
    let L := memberRestrict A (membersThrough A.E A.E p)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let K := contactMarkedKept (X := X) L (relativeNormalCoordinate U) (.refl : BlowupTower X X) O
    let R := MarkedIdeal.pullback (Subtype.val : O → X) S
    HironakaG8LocalHistory.LocWPEquiv (X := CMfd.of (n := n+1) O) K R := by
  intro X A B L S K R
  let P := properNormalMarked Q
  let M := supportedNormalMarked Q
  let T := BlowupTower.refl (X := X)
  have hP := properNormalMarked_isInvDomain Q hQ
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  obtain ⟨hL, _, _, hu, _⟩ := HironakaG1InitialSelectedNormalOrder.initial_selected_normal_data Q hQ p hp
  have hT : IsGeoTestTower P T := trivial
  have hTL : IsGeoTestTower L T := trivial
  have hOrigP : origMembers P T = A.E := List.take_length
  have hOrigM : origMembers M T = B.E := List.take_length
  have hCut := HironakaG1SeparateCarrierMemberCut.member_stage_local_of_local
    (Nat.succ_pos n) P M hP hM hPM T hT O p
  dsimp [T] at hCut
  rw [hOrigP, hOrigM] at hCut
  have hCt := HironakaG1OriginalContactClassAtStage.original_bar_local_to_reference_contact
    L L hL hL rfl (HironakaG8LocalHistory.LocEquiv.refl _ L)
    ⊤ (relativeNormalCoordinate U) hu T hTL O (by
      change (O : Set X) ⊆ Set.univ
      exact subset_univ _)
  have hBar := (HironakaG8HomStable.bar_local_any_boundary L hL).restrict O
  exact hCt.symm.trans (hBar.symm.trans hCut)

set_option maxHeartbeats 1500000 in
/-- On the actual initial positive mask the original canonical histories
agree as soon as both actual selected records lie in the family domain. -/
theorem initial_normal_selected_mask_original_can_iff {n k s l : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n+1) (productOpen U)) _) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n+1) (productOpen U)) _) p) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X)
    let O := maskA (properNormalMarked Q) H p
    let A := barMarked (X := X) (properNormalMarked Q)
    let B := barMarked (X := X) (supportedNormalMarked Q)
    let L := memberRestrict A (membersThrough A.E A.E p)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let K := contactMarkedKept (X := X) L (relativeNormalCoordinate U) H O
    let R := MarkedIdeal.pullback (Subtype.val : O → X) S
    ∀ {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) O) Y),
      IsInvDomain l K → IsInvDomain l R →
      (IsCanonical K ((invFamily (Nat.succ_pos n) l).inv K) T ↔
        IsCanonical R ((invFamily (Nat.succ_pos n) l).inv R) T) := by
  intro X H O A B L S K R Y T hK hR
  have hLevel' := hLevel
  change boundaryCount (origMembers (properNormalMarked Q) H) p = s + 1 at hLevel'
  have hOld : origMembers (properNormalMarked Q) H = (properNormalMarked Q).E :=
    List.take_length
  rw [hOld] at hLevel'
  have hp : 0 < boundaryCount (properNormalMarked Q).E p := hLevel' ▸ Nat.succ_pos s
  have hLoc := initial_normal_selected_section_locWP Q hQ p hp O
  have hSame := initial_normal_selected_section_wEquiv Q hQ p hp O hpO
  have hEmpty := (initial_normal_selected_mask_exponents_zero Q hQ p hLevel hpO).2.1
  have hInitial : ∀ D ∈ K.E, ∀ x ∈ K.cosupp, x ∈ D →
      R.d * divExpAlong (n+1) K.N K.ideal D x =
        K.d * divExpAlong (n+1) R.N R.ideal D x := by
    intro D hD x _ hx
    have hD0 : D = ∅ := hEmpty D hD
    rw [hD0] at hx
    exact False.elim hx
  exact HironakaG1OriginalUnequalMarkCanonical.invFamily_isCanonical_iff_of_local
    (Nat.succ_pos n) K R hK hR hLoc (HironakaG11InvBMClass.SameCarrierDim.of_N_eq hSame.2.1)
    hInitial T

end
end Hironaka.HironakaG1InitialNormalSelectedLocalClass
