import Hironaka.Resolution.HironakaG1InitialCompanionSectionNumerics

/-! The exact original recursive value on the initial special-companion branch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSectionSpecialRead
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
  HironakaG1InitialCompanionSectionNumerics HironakaG8LocalHistory
  StepOneRegime BlowupTowerSplit BoundaryCount


/-- Specialness at the literal companion order mask of an initial point. -/
def InitialOrderSpecial {m : ℕ} {X : CMfd.{0} m} (A : MarkedIdeal m X) (x : X)
    (hx : x ∈ ordMask A (nmOrd A x)) : Prop :=
  IsSpecial (compAt A (nmOrd A x) (.refl (X := X)))
    (.refl (X := CMfd.of (n := m) (ordMask A (nmOrd A x))))
    (⟨x, hx⟩ : ordMask A (nmOrd A x))

set_option maxHeartbeats 800000 in
private theorem special_companion_refl_read {m j : ℕ} (hm : 0 < m) {X : CMfd.{0} m}
    (A : MarkedIdeal m X) (x : X) (hOrder : 0 < nmOrd A x)
    (hEmpty : ∀ D ∈ A.E, D = ∅)
    (hx : x ∈ ordMask A (nmOrd A x))
    (hSp : InitialOrderSpecial A x hx) :
    (invFamily hm (j+1)).inv A (.refl (X := X)) x =
      toLex (nmOrd A x, toLex (Sum.inr (↑(toLex (0, (⊤ : WithTop (ValTy j)))) :
        WithTop (ℕ ×ₗ WithTop (ValTy j)))) ) := by
  classical
  let C := ordMask A (nmOrd A x)
  let F := compAt A (nmOrd A x) (.refl (X := X))
  let z : C := ⟨x, hx⟩
  let V := invFamily hm j
  let M := fun {X : CMfd.{0} m} (B : MarkedIdeal m X) {Y : CMfd.{0} m}
    (T : BlowupTower X Y) (y : Y) => Seq.StepOneValueMasked.stepOneInvM V B T y
  have hFE : F.E = A.E.map ((Subtype.val : C → X) ⁻¹' ·) := by
    change (companionOf m (M := CMfd.of (n := m) C)
      (MarkedIdeal.pullback (Subtype.val : C → X) A) (nmOrd A x)).E = _
    exact companionAlong_E _ _ _ _ _ _
  have hLevel : level F .refl z = 0 := by
    change boundaryCount (F.E.take F.E.length) z = 0
    rw [List.take_length, boundaryCount, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    let D₀ := F.E.get i
    have hi : D₀ ∈ F.E := List.get_mem F.E i
    have hi' : D₀ ∈ A.E.map ((Subtype.val : C → X) ⁻¹' ·) := hFE ▸ hi
    obtain ⟨D, hD, hEq⟩ := List.mem_map.mp hi'
    change z ∉ D₀
    rw [← hEq, hEmpty D hD, preimage_empty]
    exact notMem_empty z
  have hStep : M F (.refl (X := CMfd.of (n := m) C)) z =
      toLex (0, (⊤ : WithTop (ValTy j))) := by
    have hSF : IsSpecial F (.refl (X := CMfd.of (n := m) C)) z := hSp
    simp only [M, Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
      if_pos hSF, hLevel]
  change genInv M A (.refl (X := X)) x = _
  rw [genInv_of_nmOrd_ne_zero M A (.refl (X := X)) rfl (Nat.ne_of_gt hOrder)]
  change toLex (nmOrd A x, toLex (Sum.inr
    (genLowerValue M A (nmOrd A x) (.refl (X := X)) (.refl (X := X)) x))) = _
  have hLower : genLowerValue M A (nmOrd A x) (.refl (X := X)) (.refl (X := X)) x =
      (M F (.refl (X := CMfd.of (n := m) C)) z : WithTop (ℕ ×ₗ WithTop (ValTy j))) :=
    genLowerValue_eq_of_mem M A (o := nmOrd A x) (T₀ := .refl (X := X))
      (T₁ := .refl (X := X)) (y := x) hx
  have hConst : genLowerValue M A (nmOrd A x) (.refl (X := X)) (.refl (X := X)) x =
      (toLex (0, (⊤ : WithTop (ValTy j))) : ℕ ×ₗ WithTop (ValTy j)) :=
    hLower.trans (congrArg (fun t : ℕ ×ₗ WithTop (ValTy j) => (↑t : WithTop (ℕ ×ₗ WithTop (ValTy j)))) hStep)
  exact congrArg (fun t : WithTop (ℕ ×ₗ WithTop (ValTy j)) =>
    (toLex (nmOrd A x, toLex (Sum.inr t)) : ValTy (j+1))) hConst

private theorem order_pos_refl_of_empty_slots {m q : ℕ} {X : CMfd.{0} m}
    (A : MarkedIdeal m X) (hA : IsInvDomain q A) (x : X) (hx : x ∈ A.cosupp)
    (hEmpty : ∀ D ∈ A.E, D = ∅) : 0 < nmOrd A x := by
  have hOff : ∀ i : Fin A.E.length, x ∉ A.E.get i := by
    intro i
    rw [hEmpty _ (List.get_mem _ i)]
    exact notMem_empty x
  rw [nmOrd_eq_ordinaryTraceOrder_of_notMem A hOff]
  exact Nat.lt_of_lt_of_le hA.one_le_d (mark_le_ordinaryTraceOrder A hA hx)

set_option maxHeartbeats 700000 in
/-- If the two literal initial order companions are special, each inner
Step One value is exactly `(0, ⊤)`. The recursive values on that branch use
the same right-hand entry, with the verified mark factor on the first entry. -/
theorem initial_companion_normal_section_special_reads {n k s l : ℕ} {U : Opens (ComplexModel n)}
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
        let Z := CMfd.of (n := n+1) W
        let T := BlowupTower.refl (X := Z)
        let a := nmOrd (M := Z) K x
        let b := nmOrd (M := Z) R x
        let topRead : ℕ → ValTy (l+1) := fun o =>
          toLex (o, toLex (Sum.inr (↑(toLex (0, (⊤ : WithTop (ValTy l)))) :
            WithTop (ℕ ×ₗ WithTop (ValTy l)))))
        ∃ (hxK : x ∈ ordMask (M := Z) K a) (hxR : x ∈ ordMask (M := Z) R b),
          InitialOrderSpecial (X := Z) K x hxK →
          InitialOrderSpecial (X := Z) R x hxR →
          (invFamily (Nat.succ_pos n) (l+1)).inv K T x = topRead ((K.d / R.d) * b) ∧
          (invFamily (Nat.succ_pos n) (l+1)).inv R T x = topRead b := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ W K R x hK hx Z T a b topRead
  obtain ⟨hLoc, _, hEmpty⟩ := initial_companion_normal_section_contact Q hQ p hLevel hpO W
  have hClass : LocWPEquiv (X := Z) K R := hLoc
  have hR := (initial_companion_normal_section_can_iff Q hQ p hLevel hpO W hK).1
  have hxR : x ∈ R.cosupp := hClass.cosupp_eq_base ▸ hx
  have hE : K.E = R.E := hClass.wEquiv.1
  have hREmpty : ∀ D ∈ R.E, D = ∅ := fun D hD => hEmpty D (hE.symm ▸ hD)
  have hmK : x ∈ ordMask (M := Z) K a :=
    (proj_tail_mem_ordMask (X := Z) (𝔪 := K) (Nat.succ_pos n) hK
      (.refl (X := Z)) trivial hx (o := a) rfl).2
  have hmR : x ∈ ordMask (M := Z) R b :=
    (proj_tail_mem_ordMask (X := Z) (𝔪 := R) (Nat.succ_pos n) hR
      (.refl (X := Z)) trivial hxR (o := b) rfl).2
  refine ⟨hmK, hmR, fun hSK hSR => ?_⟩
  have hKa : 0 < a := order_pos_refl_of_empty_slots (X := Z) K hK x hx hEmpty
  have hRb : 0 < b := order_pos_refl_of_empty_slots (X := Z) R hR x hxR hREmpty
  have hFactor : a = (K.d / R.d) * b :=
    (initial_companion_normal_section_first_entry (l := l) Q hQ p hLevel hpO W x hK hx).2.2.1
  have hReadK : (invFamily (Nat.succ_pos n) (l+1)).inv K T x = topRead a :=
    special_companion_refl_read (X := Z) (Nat.succ_pos n) K x hKa hEmpty hmK hSK
  have hReadR : (invFamily (Nat.succ_pos n) (l+1)).inv R T x = topRead b :=
    special_companion_refl_read (X := Z) (Nat.succ_pos n) R x hRb hREmpty hmR hSR
  exact ⟨hReadK.trans (congrArg topRead hFactor), hReadR⟩

set_option maxHeartbeats 900000 in
/-- The actual finite branch supplies its recursive domains on the zero mask.
If its next two order companions are special, the full recursive read has
the common special payload and differs only in the first order entry. -/
theorem initial_companion_normal_section_finite_special_reads {n k s : ℕ} {U : Opens (ComplexModel n)}
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
        let Z := CMfd.of (n := n+1) W
        let T := BlowupTower.refl (X := Z)
        let V := invFamily (Nat.succ_pos n) (k+1)
        let a := nmOrd (M := Z) K r
        let b := nmOrd (M := Z) R r
        let topRead : ℕ → ValTy (k+1) := fun o =>
          toLex (o, toLex (Sum.inr (↑(toLex (0, (⊤ : WithTop (ValTy k)))) :
            WithTop (ℕ ×ₗ WithTop (ValTy k)))))
        ∃ (hK : r ∈ ordMask (M := Z) K a) (hR : r ∈ ordMask (M := Z) R b),
          InitialOrderSpecial (X := Z) K r hK →
          InitialOrderSpecial (X := Z) R r hR →
          Seq.StepOneValueMasked.stepOneInvM V J (.refl (X := Y)) z =
            toLex (0, (topRead ((K.d / R.d) * b) : WithTop (ValTy (k+1)))) ∧
          V.inv R T r = topRead b := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hy hNS
  obtain ⟨hz, hK, _, hrR, _, hValue⟩ :=
    initial_companion_normal_section_finite_refl (k := k+1) Q hQ p hLevel hpO y hyC hy hNS
  let r : W := ⟨z, hz⟩
  let Z := CMfd.of (n := n+1) W
  have hClass : LocWPEquiv (X := Z) K R :=
    (initial_companion_normal_section_contact Q hQ p hLevel hpO W).1
  have hrK : r ∈ K.cosupp := hClass.cosupp_eq_base.symm ▸ hrR
  obtain ⟨hmK, hmR, hRead⟩ :=
    initial_companion_normal_section_special_reads (l := k) Q hQ p hLevel hpO W r hK hrK
  refine ⟨hz, hmK, hmR, fun hSK hSR => ?_⟩
  obtain ⟨hReadK, hReadR⟩ := hRead hSK hSR
  refine ⟨hValue.trans ?_, hReadR⟩
  exact congrArg (fun t : ValTy (k+1) => toLex (0, (↑t : WithTop (ValTy (k+1))))) hReadK

end
end Hironaka.HironakaG1InitialCompanionSectionSpecialRead
