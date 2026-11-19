import Hironaka.Resolution.HironakaG1InitialCompanionSectionComparison
import Hironaka.Resolution.HironakaG1LocalOffBoundary

/-! The raw first entry of the original invariant on the two literal initial records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSectionNumerics
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  StepOneValue StepOneValueMasked GeneralValue NonmonomialOrderLocal NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong InvDomainMemberRestriction CanonicalCentres
  ContactStageKept HomogenizedIdealAlong HironakaG8PowerLowerMarks
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialSelectedOrderPhase HironakaG1InitialCompanionSectionComparison
  HironakaG1LocalOffBoundary HironakaG8MixedOrderInvariance

private theorem coefficient_mark_factorial (d : ℕ) :
    coefficientMark d = Nat.factorial d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    unfold coefficientMark at *
    rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.sub_zero, ← ih, mul_comm]
    simp only [Nat.add_sub_add_right]

private theorem contact_refl_mark {n : ℕ} {X : CMfd.{0} n}
    (J : MarkedIdeal n X) (u : X → ℂ) (W : Opens X) :
    (contactMarkedKept J u (.refl (X := X)) W).d = Nat.factorial (Nat.factorial J.d) := by
  change (coeffMarkedAlong (barMarked J)).d = _
  rw [coeffMarkedAlong_mark, coefficient_mark_factorial, coeffMarkedAlong_mark,
    coefficient_mark_factorial]
  rfl

private theorem first_entry_factor {d e a b : ℕ}
    (hd : 0 < d) (hde : d ∣ e) (hScale : d * a = e * b) :
    a = (e / d) * b := by
  apply Nat.eq_of_mul_eq_mul_left hd
  rw [← Nat.mul_assoc, Nat.mul_div_cancel' hde]
  exact hScale

set_option maxHeartbeats 1100000 in
/-- The first entries on the literal initial companion contact and supported
section are proportional to their actual native marks. Their raw values
differ at a surviving point whenever the section mark is at least three. -/
theorem initial_companion_normal_section_first_entry {n k s l : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ W : Opens Y,
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      ∀ (x : W), IsInvDomain (l+1) K → x ∈ K.cosupp →
        let V := invFamily (Nat.succ_pos n) (l+1)
        let T := BlowupTower.refl (X := CMfd.of (n := n+1) W)
        let a := fstEntry (V.inv K T x)
        let b := fstEntry (V.inv R T x)
        K.d = Nat.factorial (Nat.factorial R.d) ∧
        R.d * a = K.d * b ∧ a = (K.d / R.d) * b ∧
        (3 ≤ R.d → b < a ∧ V.inv R T x ≠ V.inv K T x) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ W K R x hK hx V T a b
  obtain ⟨hLoc, hN, hEmpty⟩ := initial_companion_normal_section_contact Q hQ p hLevel hpO W
  have hR := (initial_companion_normal_section_can_iff Q hQ p hLevel hpO W hK).1
  have hJMark : J.d = L.d := by
    change (companionOf (n+1) (M := Y) (MarkedIdeal.pullback (Subtype.val : C → X) L) L.d).d = L.d
    unfold companionOf companionAlong
    split
    next hlt => exact False.elim ((Nat.lt_irrefl L.d) hlt)
    next => rfl
  have hMark : K.d = Nat.factorial (Nat.factorial R.d) := by
    have hContact : K.d = Nat.factorial (Nat.factorial J.d) := contact_refl_mark J u W
    have hLR : L.d = R.d := rfl
    rw [hContact, hJMark, hLR]
  have hOff (D : Set W) (hD : D ∈ K.E) : x ∉ D := by
    have hD0 : D = ∅ := hEmpty D hD
    rw [hD0]
    exact notMem_empty x
  have hScale : R.d * a = K.d * b :=
    nmOrd_along_local_off_boundary (X := CMfd.of (n := n+1) W)
      K R hK hR hN hLoc (.refl (X := CMfd.of (n := n+1) W)) trivial x hx hOff
  have hd : 0 < R.d := hR.one_le_d
  have hDiv : R.d ∣ K.d := by
    rw [hMark]
    exact Nat.dvd_factorial hd (Nat.self_le_factorial _)
  have hFactor : a = (K.d / R.d) * b := first_entry_factor hd hDiv hScale
  refine ⟨hMark, hScale, hFactor, fun hThree => ?_⟩
  have hLt : R.d < K.d :=
    hMark ▸ (Nat.lt_factorial_self hThree).trans_le (Nat.self_le_factorial _)
  have hPos : 0 < a := by
    change 0 < nmOrd (M := CMfd.of (n := n+1) W) K x
    rw [nmOrd_eq_ordinaryTraceOrder_of_notMem (X := CMfd.of (n := n+1) W) K (fun i => hOff _ (List.get_mem _ i))]
    exact Nat.lt_of_lt_of_le hK.one_le_d (mark_le_ordinaryTraceOrder (X := CMfd.of (n := n+1) W) K hK hx)
  have hOrder : b < a := by
    by_contra! hBA
    have hProd := Nat.mul_le_mul_left K.d hBA
    have hProdLt := Nat.mul_lt_mul_of_pos_right hLt hPos
    omega
  exact ⟨hOrder, fun hEq => (Nat.ne_of_lt hOrder) (congrArg fstEntry hEq)⟩

set_option maxHeartbeats 900000 in
/-- On the actual finite zero contact mask the recursive first entry has the
native factorial scaling, with both domains supplied by the finite branch. -/
theorem initial_companion_normal_section_finite_first_entry {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+2) Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ (y : O) (hyC : y ∈ C),
      let z : C := ⟨y, hyC⟩
      let W := maskB J (.refl (X := Y)) z
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      y ∈ L.cosupp → ¬ IsSpecial J (.refl (X := Y)) z →
      ∃ hz : z ∈ W,
        let r : W := ⟨z, hz⟩
        let V := invFamily (Nat.succ_pos n) (k+1)
        let T := BlowupTower.refl (X := CMfd.of (n := n+1) W)
        let a := fstEntry (V.inv K T r)
        let b := fstEntry (V.inv R T r)
        Seq.StepOneValueMasked.stepOneInvM V J (.refl (X := Y)) z =
          toLex (0, (V.inv K T r : WithTop (ValTy (k+1)))) ∧
        a = (K.d / R.d) * b ∧
        (3 ≤ R.d → b < a ∧
          Seq.StepOneValueMasked.stepOneInvM V J (.refl (X := Y)) z ≠
            toLex (0, (V.inv R T r : WithTop (ValTy (k+1))))) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hy hNS
  obtain ⟨hz, hK, _, hrR, _, hValue⟩ :=
    initial_companion_normal_section_finite_refl (k := k+1) Q hQ p hLevel hpO y hyC hy hNS
  let r : W := ⟨z, hz⟩
  have hLoc := (initial_companion_normal_section_contact Q hQ p hLevel hpO W).1
  have hW : HironakaG8LocalHistory.LocWPEquiv (X := CMfd.of (n := n+1) W) K R := hLoc
  have hrK : r ∈ K.cosupp := hW.cosupp_eq_base.symm ▸ hrR
  obtain ⟨_, _, hFactor, hStrict⟩ :=
    initial_companion_normal_section_first_entry (l := k) Q hQ p hLevel hpO W r hK hrK
  refine ⟨hz, hValue, hFactor, fun hThree => ⟨(hStrict hThree).1, ?_⟩⟩
  intro hEq
  have hRead := hEq.symm.trans hValue
  have hEntry := congrArg (fun w => (ofLex w).2) hRead
  exact (hStrict hThree).2 (WithTop.coe_injective hEntry)

end
end Hironaka.HironakaG1InitialCompanionSectionNumerics
