import Hironaka.Resolution.HironakaG1ProperNormalZeroPhase
import Hironaka.Resolution.HironakaG1InitialSelectedNormalOrder
import Hironaka.Invariant.StepOneTangentChange

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NormalContactChoiceTransfer
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong TangentDirectionAlong
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain StepOneTangentChange ContactStageKept
  HironakaG1ProperNormalZeroPhase HironakaG1OriginalInvariantClassFunctorial
  HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1InitialSelectedNormalOrder HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials GeneralValue NonmonomialOrderTail NonmonomialOrderLocal
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical contact tail and finite value at a prescribed tangent. -/
abbrev ZeroContactTransfer {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (u : X → ℂ) (T : BlowupTower X Y) (y : Y) : Prop :=
    let R := invFamily hn k
    let r := regimeRun (stepRegime J 0) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskB J H p
    let A := lowerMarkedB J H p
    let B := contactMarkedKept J u H O
    ∃ hp : p ∈ O,
      IsInvDomain k A ∧ IsInvDomain k B ∧
      IsCanonical A (R.inv A) (restrict O S) ∧
      IsCanonical B (R.inv B) (restrict O S) ∧
      (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong B (restrict O S)).cosupp ∧
      R.inv A (restrict O S) (⟨y, hp⟩ : openPreimage S O) =
        R.inv B (restrict O S) (⟨y, hp⟩ : openPreimage S O) ∧
      Seq.StepOneValueMasked.stepOneInvM R J T y =
        toLex (0, (R.inv B (restrict O S) (⟨y, hp⟩ : openPreimage S O) : WithTop (ValTy k)))

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency false in
/-- At a nonspecial level-zero endpoint of an original canonical Step One
history, a prescribed global tangent uses the same restricted tail and
gives the same finite recursive value as the original choice. -/
theorem zero_step_one_prescribed_contact {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = 0) (hNS : ¬ IsSpecial J T y) :
    ZeroContactTransfer (k := k) hn J u T y := by
  let R := invFamily hn k
  let r := regimeRun (stepRegime J 0) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskB J H p
  let A := lowerMarkedB J H p
  let B := contactMarkedKept J u H O
  obtain ⟨hBarTest, hTest, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R J hJ hMax hn T hCan
  have hyBar := hCos.symm ▸ hy
  have hData := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (k := k + 1)
    J R hJ.isWellFormed hJ.one_le_d hn hMax hJ.dimLE T
    ((Seq.StepOneBridge.isCanonical_iff R J hJ hMax hn T).mp hCan) y hyBar hNS
  obtain ⟨hHeadReg, hHeadCos⟩ :=
    stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hData hHeadReg hHeadCos
  obtain ⟨hp, hDomA, hCanA, hCosA⟩ := hData
  have hHeadTest := ((isGeoTestTower_iff_head_tail J T r).mp hTest).1
  obtain ⟨_, _, hB, hClass, hDim, _, hE, hd, hExp⟩ :=
    global_prescribed_contact_data hn J hJ hMax u hu H hHeadTest p hHeadCos hHeadReg
  have hA' : IsInvDomain k A := by
    change IsInvDomain (k + 1 - 1) A at hDomA
    rw [Nat.add_sub_cancel] at hDomA
    exact hDomA
  have hB' : IsInvDomain k B := by simpa only [Nat.add_sub_cancel] using hB
  have hCanB := ((classFunctorialFor_invFamily hn k).canonical_iff
    (X := CMfd.of (n := n) O) A B hA' hB' hClass hd hE hDim hExp (restrict O S)).mp hCanA
  have hTestA := R.isInvValue.isGeoTestTower_of_isCanonical hA' (restrict O S) hCanA
  have hCosB : (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong B (restrict O S)).cosupp :=
    (hClass.wEquiv.2 (restrict O S)).2 hTestA ▸ hCosA
  let x := H.proj p
  let v := (tangentChoice J x).2
  let Uv := (tangentChoice J x).1
  obtain ⟨hxv, hv⟩ := tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMax H
      ((isGeoTestTower_iff_head_tail (barMarked J) T r).mp hBarTest).1 hHeadCos)
  have hx : x ∈ J.cosupp := by
    have hProj : T.proj y = H.proj (S.proj y) := congrFun (proj_eq_comp T r) y
    change H.proj (S.proj y) ∈ J.cosupp
    rw [← hProj]
    exact proj_mem_cosupp_of_mem_cosupp hJ.isWellFormed.isClosedSubmanifold_N
      hJ.isWellFormed.isCoherent T hTest hy
  obtain ⟨O₀, hxO, hCompare⟩ := Seq.StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens R J hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d hx hv hxv hu (mem_univ _)
  have hTO : IsGeoTestTower (barMarked J) (H.append S) := by
    rw [head_append_tail]
    exact hBarTest
  have hOld : ∀ D ∈ (geoTransformAlong (barMarked J) H).E.take J.E.length, ∀ q ∈ O, q ∉ D :=
    fun D hD _ hq => (interior_subset hq).2.1 D hD
  have hIn : ∀ q ∈ O, q ∈ H.proj ⁻¹' Uv := fun _ hq => (interior_subset hq).1
  let w : openPreimage S O := ⟨y, hp⟩
  have hwBar : w.val ∈ (geoTransformAlong (barMarked J) (H.append S)).cosupp := by
    rw [head_append_tail]
    exact hyBar
  have hValue : R.inv A (restrict O S) w = R.inv B (restrict O S) w :=
    hCompare H S hTO O O hIn (fun _ _ => mem_univ _) hOld hOld hA' hCanA hB' hCanB
      w w rfl hxO hwBar
  have hRead := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J (lowerMarkedM J) T hNS
  rw [hLevel, Seq.StepOneValueMasked.lowerValueL_eq_of_mem R J (lowerMarkedM J) hp] at hRead
  refine ⟨hp, hA', hB', hCanA, hCanB, hCosB, hValue, ?_⟩
  exact hRead.trans (congrArg (fun a : ValTy k => toLex (0, (a : WithTop (ValTy k)))) hValue)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual finite zero-level contact tail of the original initially
selected positive record's order companion can be read in the genuine
normal tangent. The companion's support, maximal order and Step One
canonicality are the hypotheses for the finite tail. -/
theorem initial_positive_companion_normal_contact {n k l s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := lowerMask P (s + 1) H p
    let X := CMfd.of (n := n + 1) O
    let L := lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) P (s + 1) H p
    let C : Opens X := ordMask (geoTransformAlong L (BlowupTower.refl (X := X))) L.d
    let J : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) C) := compAt (X := X) L L.d (BlowupTower.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    IsInvDomain (l + 1) J →
    IsMaximalOrderAlong J.N J.ideal J.d →
    IsTangentDirectionAlong J.N J.ideal J.d univ u →
    ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower X Y)
      (y : Y) (_hy : y ∈ (geoTransformAlong L T).cosupp),
      IsGeoTestTower L T →
      ∀ hp : T.proj y ∈ C,
        let S : BlowupTower (CMfd.of (n := n + 1) C)
          (CMfd.of (n := n + 1) (openPreimage T C)) := restrict C T
        let z : openPreimage T C := ⟨y, hp⟩
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) l) J) S →
        z ∈ (geoTransformAlong J S).cosupp →
        level J S z = 0 → ¬ IsSpecial J S z →
        nmOrd (geoTransformAlong L T) y = L.d ∧
          ZeroContactTransfer (k := l) (Nat.succ_pos n) J u S z := by
  intro P H O X L C J u hJ hMax hu Y T y hy hTest hp
  dsimp only
  intro hCan hz hZero hNS
  exact ⟨original_initial_positive_lower_test_order Q hQ p hLevel T hTest y hy,
    zero_step_one_prescribed_contact (Nat.succ_pos n) _ hJ hMax _ hu _ hCan _ hz hZero hNS⟩


end
end Hironaka.HironakaG1NormalContactChoiceTransfer
