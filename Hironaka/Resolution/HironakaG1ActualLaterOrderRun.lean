import Hironaka.Resolution.HironakaG1ActualLaterSuccessorRead
import Hironaka.Invariant.StepOneEmptyPrefix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1ActualLaterOrderRun
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime StepOneEmptyPrefix StepOneLowerDomain
  GeneralValue CompanionRebase CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  HironakaG3RRawRegimeLocality
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterSelectedActualOrder
  HironakaG1LaterPositiveSuccessorRead HironakaG1ActualLaterSuccessorRead
  HironakaG1PositiveNormalPhase HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount RelativePrincipalizationSpan

/-- Constant order on all tested continuations makes the order run
start at the source of each such tower. -/
theorem order_run_of_all_test_orders {n q : ℕ}
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain q L) (o : ℕ)
    (hOrder : ∀ {Z : CMfd.{0} n} (T : BlowupTower X Z), IsGeoTestTower L T →
      ∀ z ∈ (geoTransformAlong L T).cosupp, nmOrd (geoTransformAlong L T) z = o)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) (y : Y)
    (hy : y ∈ (geoTransformAlong L T).cosupp) :
    regimeRun (OrdRegime L o) T y = T.length := by
  apply le_antisymm (regimeRun_le_length (OrdRegime L o) T y)
  apply le_of_not_gt
  intro hlt
  let j := regimeRun (OrdRegime L o) T y + 1
  have hSplit := (isGeoTestTower_iff_head_tail L T j).mp hT
  have hCur := isInvDomain_geoTransformAlong hL (head T j) hSplit.1
  have hy' := hy
  rw [geoTransformAlong_head_tail L T j] at hy'
  have hp := proj_mem_cosupp_of_mem_cosupp hCur.isWellFormed.isClosedSubmanifold_N
    hCur.isWellFormed.isCoherent (tail T j) hSplit.2 hy'
  exact not_regime_head_regimeRun (OrdRegime L o) T y hlt ⟨hp, hOrder (head T j) hSplit.1 _ hp⟩

set_option maxHeartbeats 900000 in
/-- A single smaller window on which all tested continuations keep order
also determines the entire order run of the full-mask endpoint over it. -/
theorem full_order_run_of_canonical_restriction_on_test_window {n q : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : K.ideal.IsCoherent)
    {O W : Opens X} (hWO : W ≤ O) (S : BlowupTower X Y)
    (hL : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : O → X) K))
    (hCan : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) K)
      ((invFamily hn q).inv (MarkedIdeal.pullback (Subtype.val : O → X) K)) (restrict O S))
    (y : openPreimage S O) (hyW : S.proj y.val ∈ W)
    (hy : y ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) K) (restrict O S)).cosupp)
    (o : ℕ)
    (hOrder : ∀ {Z : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) W) Z),
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) K) T →
      ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) T).cosupp,
        nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) T) z = o) :
    regimeRun (OrdRegime (MarkedIdeal.pullback (Subtype.val : O → X) K) o) (restrict O S) y =
      (restrict O S).length := by
  let R := invFamily hn q
  obtain ⟨hW, hWCan, _⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hK hWO hL S hCan
  have hTestW := R.isInvValue.isGeoTestTower_of_isCanonical hW (restrict W S) hWCan
  have hHol : ∀ p f, K.ideal.mem p f → HolomorphicAt n f p :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK hf
  have hSpan : ∀ p f, IsInSpanAt (n := n) (K.ideal.mem p) p f → K.ideal.mem p f :=
    fun _ _ hf => GermIdealTotalTransform.mem_of_isInSpanAt_mem hK hf
  let z : openPreimage S W := ⟨y.val, hyW⟩
  rw [cosupp_restrict_raw K hHol O S] at hy
  have hz : z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W S)).cosupp := by
    rw [cosupp_restrict_raw K hHol W S]
    exact hy
  have hOrdW := order_run_of_all_test_orders _ hW o (fun T => hOrder T) (restrict W S) hTestW z hz
  have hRunO := regimeRun_ordRegime_restrict_raw K hHol hSpan O o S y
  have hRunW := regimeRun_ordRegime_restrict_raw K hHol hSpan W o S z
  exact hRunO.trans (hRunW.symm.trans (hOrdW.trans ((length_restrict W S).trans (length_restrict O S).symm)))

set_option maxHeartbeats 1700000 in
/-- The single actual subwindow at the split anchor controls every
surviving projection of the lower endpoint on the literal full-mask
tail. The original lower order clock therefore starts at that anchor. -/
theorem original_upper_positive_lower_full_order_run {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let Z := CMfd.of (n := n + 1) (openPreimage S O)
    let T' : BlowupTower A Z := restrict O S
    0 < L.d ∧ (∀ z : openPreimage S O, z.val = y →
      OrdRegime L L.d T' z ∧ regimeRun (OrdRegime L L.d) T' z = T'.length ∧
      ∀ i, i ≤ T'.length → OrdRegime L L.d (head T' i) ((tail T' i).proj z)) := by
  intro X P r H S p O A L Z T'
  let R := invFamily (Nat.succ_pos n) (k + 1)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarTest, hTest, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R P hP hMax (Nat.succ_pos n) T hCan
  have hyBar := hCos.symm ▸ hy
  obtain ⟨hReg, hpBar⟩ :=
    stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hReg hpBar
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨W, _, hpW, hWO, _, _, _, _, hOrderW⟩ :=
    exists_later_selected_actual_normal_order Q hQ H hHeadTest p hpBar hReg.1 hReg.2
  obtain ⟨_, _, _, _, hpO, _, hL, hLCan, hyL⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  let B := geoTransformAlong (barMarked P) H
  let K := memberRestrict B (membersThrough B.E (origMembers P H) p)
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H
      ((isGeoTestTower_iff_head_tail (barMarked P) T r).mp hBarTest).1
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB _
  let z : openPreimage S O := ⟨y, hpO⟩
  have hOrder : nmOrd (geoTransformAlong L T') z = L.d :=
    order_of_canonical_restriction_of_test_window (Nat.succ_pos n) K hK.isCoherent hWO S
      hL hLCan z hpW hyL L.d (hOrderW (restrict W S))
  have hRun : regimeRun (OrdRegime L L.d) T' z = T'.length :=
    full_order_run_of_canonical_restriction_on_test_window (Nat.succ_pos n) K hK.isCoherent hWO S
      hL hLCan z hpW hyL L.d (fun T => hOrderW T)
  refine ⟨hL.one_le_d, fun w hw => ?_⟩
  have heq : w = z := Subtype.ext hw
  subst w
  refine ⟨⟨hyL, hOrder⟩, hRun, fun i hi => ?_⟩
  rcases i with _ | i
  · simp only [head, tail]
    rw [split_zero T']
    exact ⟨hyL, hOrder⟩
  · exact regime_head_of_le_regimeRun (OrdRegime L L.d) T' z (i + 1) (Nat.succ_pos i) (hRun.symm ▸ hi)


/-- The actual order companion at the initial head of a tested lower
tail. The boundary is the literal ordered boundary of that companion. -/
abbrev InitialOrderCompanionWitness {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (L : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (Read : ValTy (k + 1) → Prop) : Prop :=
  let O := ordMask (geoTransformAlong L (.refl : BlowupTower X X)) o
  let J := compAt L o (.refl : BlowupTower X X)
  J.E = L.E.map ((Subtype.val : O → X) ⁻¹' ·) ∧
    ∃ hp : T.proj y ∈ O,
      let U := restrict O T
      let z : openPreimage T O := ⟨y, hp⟩
      IsInvDomain (k + 1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) U ∧
      z ∈ (geoTransformAlong J U).cosupp ∧
      Read (positiveSuccessorRead o (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J U z))

private theorem initial_companion_of_full_order_run {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (Read : ValTy (k + 1) → Prop) (hRun : regimeRun (OrdRegime L o) T y = T.length)
    (h : PositiveOrderCompanionWitness (k := k) hn L T y o Read) :
    InitialOrderCompanionWitness hn L T y o Read := by
  let Data (D : Σ V : CMfd.{0} n, BlowupTower X V × BlowupTower V Y) : Prop :=
    let O := ordMask (geoTransformAlong L D.2.1) o
    let J := compAt L o D.2.1
    ∃ hp : D.2.2.proj y ∈ O,
      let U := restrict O D.2.2
      let z : openPreimage D.2.2 O := ⟨y, hp⟩
      IsInvDomain (k + 1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) U ∧
      z ∈ (geoTransformAlong J U).cosupp ∧
      Read (positiveSuccessorRead o (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J U z))
  have hSplit : split T (regimeRun (OrdRegime L o) T y) = ⟨X, .refl, T⟩ :=
    (congrArg (split T) hRun).trans (split_of_length_le T T.length le_rfl)
  exact ⟨by simp [compAt, companionOf, MarkedIdeal.pullback], (congrArg Data hSplit).mp (show Data (split T (regimeRun (OrdRegime L o) T y)) from h)⟩

/-- A full positive order run reads its initial companion on the literal
initial order mask, with all ordered boundary slots retained. -/
theorem original_positive_initial_order_companion {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain (k + 1) L)
    (T : BlowupTower X Y) (hCan : IsCanonical L ((invFamily hn (k + 1)).inv L) T)
    (y : Y) (hy : y ∈ (geoTransformAlong L T).cosupp) (o : ℕ)
    (hOrder : nmOrd (geoTransformAlong L T) y = o) (ho : 0 < o)
    (hRun : regimeRun (OrdRegime L o) T y = T.length) :
    InitialOrderCompanionWitness (k := k) hn L T y o
      (fun v => (invFamily hn (k + 1)).inv L T y = v) :=
  initial_companion_of_full_order_run hn L T y o _ hRun
    (original_positive_order_successor_read hn L hL T hCan y hy o hOrder ho)

set_option maxHeartbeats 1500000 in
/-- At any actual positive nonspecial canonical cut, the original upper
finite value reads the initial order companion of its literal selected
lower tail. All its retained ordered slots remain part of the record. -/
theorem original_upper_positive_successor_at_initial_order_companion {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let Z := CMfd.of (n := n + 1) (openPreimage S O)
    let T' : BlowupTower A Z := restrict O S
    ∃ hp : p ∈ O,
      let z : openPreimage S O := ⟨y, hp⟩
      IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) T' ∧
      InitialOrderCompanionWitness (k := k) (Nat.succ_pos n) L T' z L.d
        (fun v => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
          toLex (s + 1, (v : WithTop (ValTy (k + 1))))) := by
  intro X P r H S p O A L Z T'
  obtain ⟨hp, hCanL, hRead⟩ := original_upper_positive_successor_at_true_mark Q hQ T hCan y hy hLevel hNS
  let z : openPreimage S O := ⟨y, hp⟩
  have hRuns := (original_upper_positive_lower_full_order_run Q hQ T hCan y hy hLevel hNS).2
  exact ⟨hp, hCanL, initial_companion_of_full_order_run (k := k) (Nat.succ_pos n)
    (X := A) (Y := Z) L T' z L.d _ (hRuns z rfl).2.1 hRead⟩

end
end Hironaka.HironakaG1ActualLaterOrderRun
