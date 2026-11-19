import Hironaka.Resolution.HironakaG1ActualChronologicalNext
import Hironaka.Resolution.HironakaG1TrueMarkZeroContactRead
import Hironaka.Resolution.HironakaG1AdvancingSupportedBornContact
import Hironaka.Resolution.HironakaG1LocalizedBornNormalOrder

/-! True-mark zero contact on the next chronologically selected positive suffix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Hironaka.HironakaG1ChronologicalTrueMarkZero

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong CoefficientIdealRestriction RestrictedIdealExtension ContactStageKept
  CompanionRebase GeneralValue NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  TangentDirectionAlong StepOneValue StepOneValueMasked StepOneRegime
  HironakaG1ActualLaterOrderRun HironakaG1InitialPositiveGeneralRead HironakaG1TrueMarkZeroContactRead
  HironakaG1AdvancingSupportedBornContact HironakaG8GapNormalizedExponent HironakaG8LocalHistory
  HironakaG1ProperNormalInitialRegime HironakaG1LaterSelectedNormalOrder
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  DivisorExponentAlong GermIdealOrder RestrictLeCalculus GiraudAlong DerivativeIdealAlong
  RelativePrincipalizationSpan MemberInterTowerAlong InvertibleIdealQuotient CompanionReductionAlong MonomialPartAlong
open HomogenizedGlueingTower (strictAlong)

private theorem tangent_true_order_bound {n k : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K) {u : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u) :
    IsMaximalOrderAlong K.N K.ideal K.d := by
  intro x hx
  let i := K.d - 1
  have hi : 1 + i = K.d := by dsimp [i]; have := hK.one_le_d; omega
  have hHol : ∀ y f, K.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf
  have hMem := hu.mem x (mem_univ x)
  have huH := holomorphicAt_of_mem_iterDerivIdealAlong hHol i x u hMem
  have hx1 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 i
    (by rw [hi]; exact cosupport_anti (Nat.le_succ K.d) hx)
  have hu0 := (vanishesToOrderOn_one_iff hx1.1 huH).mp (hx1.2 _ hMem)
  obtain ⟨e, ξ, hξ, hD⟩ := hu.multiplicity_one x (mem_univ x) hu0
  have hGen : DerivGenAlong K.N (iterDerivIdealAlong K.N K.ideal i) x (fieldDeriv e ξ u) :=
    Or.inr (Or.inr ⟨e, ξ, u, hξ, hMem, rfl⟩)
  have hDH := holomorphicAt_fieldDeriv hξ.mem_source hξ.holomorphicAt huH
  have hDMem : (iterDerivIdealAlong K.N K.ideal (i + 1)).mem x (fieldDeriv e ξ u) :=
    isInSpanAt_self hGen hDH
  have hNum : 1 + (i + 1) = K.d + 1 := by omega
  have hx2 := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 (i + 1)
    (by rw [hNum]; exact hx)
  exact hD ((vanishesToOrderOn_one_iff hx2.1 hDH).mp (hx2.2 _ hDMem))

/-- The tangent bounds ordinary order. Vanishing of the literal retained
boundary exponents then identifies the nonmonomial companion at the
actual selected mark, with the entire ordered divisor unchanged. -/
theorem true_mark_of_retained_boundary_zero {n k : ℕ} {X : CMfd.{0} n}
    (K : MarkedIdeal n X) (hK : IsInvDomain k K) {u : X → ℂ}
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0) :
    (∀ z ∈ K.cosupp, nmOrd K z = K.d) ∧
    companionOf n K K.d =
      (⟨K.N, K.E, restrictOn n K.N K.ideal, K.d⟩ : MarkedIdeal n X) := by
  have hNm := nonmonomial_eq_restrictOn_of_boundary_zero (X := X) K hExp
  have hMax := tangent_true_order_bound K hK hu
  have hOrder (z : X) (hz : z ∈ K.cosupp) : nmOrd (M := X) K z = K.d := by
    have hLow : z ∈ ordGe K K.d := by
      change z ∈ cosupport n K.N (nmPart K) K.d
      rw [hNm]
      exact cosupport_subset_of_restrictLe restrictLe_restrictOn K.d hz
    have hHigh : z ∉ ordGe K (K.d + 1) := by
      intro hh
      change z ∈ cosupport n K.N (nmPart K) (K.d + 1) at hh
      rw [hNm] at hh
      exact hMax z (cosupport_subset_of_restrictLe
        (restrictLe_self_restrictOn hK.isWellFormed.isCoherent) _ hh)
    have hd : K.d - 1 + 1 = K.d := by have := hK.one_le_d; omega
    have hLow' : z ∈ ordGe K (K.d - 1 + 1) := hd.symm ▸ hLow
    exact le_antisymm (nmOrd_le_of_notMem hHigh) (hd ▸ succ_le_nmOrd_of_mem ⟨K.d, hHigh⟩ hLow')
  refine ⟨hOrder, ?_⟩
  change companionAlong K.N K.E (nmPart K) (monomialPartAlong n K.N K.ideal K.E) K.d K.d = _
  rw [hNm]
  simp only [companionAlong, lt_self_iff_false, if_false]

set_option maxHeartbeats 2000000 in
/-- On the literal selected suffix, the true-mark, finite zero branch
advances its supported record along the same head. The old prefix and
the newly appended boundary slots both survive in their order. The
only extra premise for supported CAN on a nonempty zero head is a
cosupport gap of the actual advanced supported restriction. -/
theorem selected_suffix_true_mark_zero_contact {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k+1) K) (hR : IsInvDomain k R) (u : X → ℂ)
    (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {x | u x = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})) R)
    (hExp : ∀ F ∈ K.E, ∀ z, divExpAlong n K.N K.ideal F z = 0)
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k+1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    let C := ordMask K K.d
    let A := CMfd.of (n := n) C
    let J := compAt K K.d (.refl : BlowupTower X X)
    let Kc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) K
    let Rc := MarkedIdeal.pullback (M' := A) (Subtype.val : C → X) R
    let v : C → ℂ := u ∘ Subtype.val
    let V := restrict C T
    J.d = K.d ∧ J.E = K.E.map ((Subtype.val : C → X) ⁻¹' ·) ∧
    ∃ hp : T.proj y ∈ C,
      let z : openPreimage T C := ⟨y, hp⟩
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) V ∧
      z ∈ (geoTransformAlong J V).cosupp ∧
      (level J V z = 0 → (¬ IsSpecial J V z) →
        let r := regimeRun (stepRegime J 0) V z
        let H := head V r
        let S := tail V r
        let p := S.proj z
        let O := maskB J H p
        let B := CMfd.of (n := n) O
        let D := contactMarkedKept Kc v H O
        let R' := MarkedIdeal.pullback (M' := B) (Subtype.val : O → _) (geoTransformAlong Rc H)
        ∃ hq : p ∈ O,
          let w : openPreimage S O := ⟨z, hq⟩
          let G := restrict O S
          IsGeoTestTower Rc H ∧ IsInvDomain k D ∧ IsInvDomain k R' ∧
          D.N = R'.N ∧ D.E = R'.E ∧ R'.d = R.d ∧ LocWPEquiv D R' ∧
          D.N = (Subtype.val : O → _) ⁻¹' strictAlong H Rc.N ∧
          D.E = (J.E.map (strictAlong H) ++
            (geoTransformAlong (barMarked J) H).E.drop J.E.length).map
              ((Subtype.val : O → _) ⁻¹' ·) ∧
          IsCanonical D ((invFamily hn k).inv D) G ∧ IsGeoTestTower R' G ∧
          w ∈ (geoTransformAlong D G).cosupp ∧ w ∈ (geoTransformAlong R' G).cosupp ∧
          (HasCosupportGap (X := B) R' → IsCanonical R' ((invFamily hn k).inv R') G) ∧
          (invFamily hn (k+1)).inv K T y = positiveSuccessorRead K.d
            (toLex (0, ((invFamily hn k).inv D G w : WithTop (ValTy k))))) := by
  intro C A J Kc Rc v V
  obtain ⟨hOrder, hEq⟩ := true_mark_of_retained_boundary_zero K hK hu hExp
  have hMark : J.d = K.d := by simp [J, companionAlong, MarkedIdeal.pullback]
  have hE : J.E = K.E.map ((Subtype.val : C → X) ⁻¹' ·) := by
    simp [J, companionAlong, MarkedIdeal.pullback]
    intros
    rfl
  obtain ⟨hp, hCanJ, hz, hZero⟩ :=
    true_mark_original_advancing_zero_read hn K hK u hu hOrder hEq T hCan y hy
  refine ⟨hMark, hE, hp, hCanJ, hz, ?_⟩
  intro hLevel hNS r H S p O B D R'
  obtain ⟨hq, _, _, hw, hCarrier, hBoundary, hRead⟩ := hZero hLevel hNS
  obtain ⟨_, hHead, hD, hR', hN, hE', hd, hWP, hDC, hRT, hwR, hRC⟩ :=
    actual_zero_head_advances_supported_born hn K R hK hR u hu hTrace hClass hEq
      V hCanJ ⟨y, hp⟩ hz hLevel hNS
  have hTraceC : Kc.N ∩ {x : C | v x = 0} = Rc.N := by
    change (Subtype.val : C → X) ⁻¹' (K.N ∩ {x | u x = 0}) = (Subtype.val : C → X) ⁻¹' R.N
    rw [hTrace]
  rw [hTraceC] at hCarrier
  have hChron : (geoTransformAlong (barMarked J) H).E =
      J.E.map (strictAlong H) ++ (geoTransformAlong (barMarked J) H).E.drop J.E.length := by
    rw [← show (geoTransformAlong (barMarked J) H).E.take J.E.length = J.E.map (strictAlong H)
      from take_E_geoTransformAlong (barMarked J) H]
    exact (List.take_append_drop J.E.length _).symm
  exact ⟨hq, hHead, hD, hR', hN, hE', hd, hWP, hCarrier, hBoundary.trans (congrArg
    (fun E => E.map ((Subtype.val : O → _) ⁻¹' ·)) hChron), hDC, hRT, hw, hwR, hRC, hRead⟩

open NormalCrossings BoundaryCount HironakaG1LaterContactFieldExistence
  HironakaG8MixedBoundaryExponents DerivativeIdealAlongEtale HironakaMonomialBlowup

set_option maxHeartbeats 1300000 in
/-- Transversality of an actual supported zero trace to the whole retained
ordered list gives zero exponents after shrinking around that trace.
The full normal power is taken at the selected record's native mark. -/
theorem exists_retained_zero_window_of_normal_power {n k l : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain k K) (hR : IsInvDomain l R) (hE : K.E = R.E)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {x | u x = 0} = R.N)
    (hPow : ∀ x, K.ideal.mem x (fun z => u z ^ K.d))
    (p : X) (hp : p ∈ R.N) :
    ∃ W : Opens X, p ∈ W ∧
      let A := CMfd.of (n := n) W
      let Kw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) K
      ∀ F ∈ Kw.E, ∀ z, divExpAlong n Kw.N Kw.ideal F z = 0 := by
  classical
  have hp0 : u p = 0 := (hTrace ▸ hp).2
  obtain ⟨e, ξ, hξ, hD⟩ := hu.multiplicity_one p (mem_univ p) hp0
  have hHol (x : X) : HolomorphicAt n u x :=
    holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hh => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hh)
      (K.d - 1) x u (hu.mem x (mem_univ x))
  have hVan : (vanishingIdeal (n := n) R.N).mem p u :=
    ⟨hHol p, Eventually.of_forall fun _ hx => (hTrace ▸ hx).2⟩
  have hSub : R.N ⊆ K.N := fun _ hx => (hTrace ▸ hx).1
  have hTR : IsTransverse n R.N K.E := hE.symm ▸ hR.isWellFormed.isTransverse
  have hSlots (i : Fin K.E.length) :
      ∀ᶠ x in 𝓝 p, x ∈ K.E.get i →
        ∃ (q : ComplexChart n X) (η : Fin n → X → ℂ),
          IsTangentField (K.N ∩ K.E.get i) q η x ∧
          fieldDeriv q η u =ᶠ[𝓝 x] fun _ => 1 := by
    by_cases hi : p ∈ K.E.get i
    · have h := exists_normalized_tangent_field_of_transverse_boundary hn K.E {i}
          hK.isWellFormed.isSNCDivisor hK.isWellFormed.isTransverse hTR
          (by intro j hj; rwa [Finset.mem_singleton.mp hj]) hp hSub hVan hξ hD
      have hI : memberInter K.E {i} = K.E.get i := by
        ext x
        change (∀ j ∈ ({i} : Finset (Fin K.E.length)), x ∈ K.E.get j) ↔ x ∈ K.E.get i
        simp
      rw [hI] at h
      exact h.mono (fun _ h _ => h)
    · have hClosed := hK.isWellFormed.isSNCDivisor.1 _ (List.get_mem K.E i)
      filter_upwards [hClosed.isOpen_compl.mem_nhds hi] with x hx hxi
      exact (hx hxi).elim
  obtain ⟨S, hS, hOpen, hpS⟩ := mem_nhds_iff.mp (Filter.eventually_all.2 hSlots)
  let W : Opens X := ⟨S, hOpen⟩
  let A := CMfd.of (n := n) W
  let Kw : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) K
  have hX (x : W) (i : Fin K.E.length) : divExpAlong n K.N K.ideal (K.E.get i) x.val = 0 := by
    by_cases h : x.val ∈ K.N ∩ K.E.get i
    · obtain ⟨q, η, hη, hNorm⟩ := hS x.property i h.2
      exact divExpAlong_eq_zero_of_normal_power_field hK.isWellFormed.isCoherent h (hHol x.val)
        K.d (hPow x.val) hη (by rw [hNorm.self_of_nhds]; exact one_ne_zero)
    · exact divExpAlong_eq_zero_of_notMem (hK.isWellFormed.isClosedSubmanifold_N.1.inter
        (hK.isWellFormed.isSNCDivisor.1 _ (List.get_mem K.E i))) h
  refine ⟨W, hpS, ?_⟩
  change ∀ F ∈ Kw.E, ∀ z, divExpAlong n Kw.N Kw.ideal F z = 0
  intro F hF z
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hF
  have hLen : Kw.E.length = K.E.length := List.length_map _
  have hi : i.val < K.E.length := lt_of_lt_of_le i.isLt hLen.le
  exact (divExpAlong_pullback_val_get K hK.isWellFormed.isCoherent W z i.isLt hi).trans
    (hX z ⟨i.val, hi⟩)

open IdealWeightPowers HomogenizedGlueingLiftAlong InvDomainMemberRestriction CoefficientIdeal
  HironakaG1RecursiveMemberValueTransport ContactEquivalenceAlong

private theorem true_normal_power_in_member {n : ℕ} {X : CMfd.{0} n}
    (B : MarkedIdeal n X) (hB : B.IsWellFormed) (hd : 0 < B.d)
    (I : Finset (Fin B.E.length)) (W : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong B.N B.ideal B.d W u) {x : X} (hx : x ∈ W) :
    let K := memberRestrict B I
    HolomorphicAt n u x ∧ K.ideal.mem x (fun z => u z ^ K.d) := by
  let K := memberRestrict B I
  let i := B.d - 1
  let a := sumExp (fun j => B.d - j) B.d i
  have hMem := hu.mem x hx
  have hHol := holomorphicAt_of_mem_iterDerivIdealAlong
    (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hf) i x u hMem
  have hi : i < B.d := by dsimp [i]; omega
  have hOne : B.d - i = 1 := by dsimp [i]; omega
  have hMark : K.d = a := by
    change (Finset.range B.d).prod (fun j => B.d - j) = a
    simpa only [hOne, one_mul] using (mul_sumExp (fun j => B.d - j) hi).symm
  refine ⟨hHol, ?_⟩
  change IsInSpanAt (n := n) (fun f => ∃ j, j < B.d ∧
    (idealPow (iterDerivIdealAlong B.N B.ideal j) (sumExp (fun m => B.d - m) B.d j)).mem x f) x _
  rw [hMark]
  exact isInSpanAt_self ⟨i, hi, HomogenizedIdeal.pow_mem_idealPow hMem hHol a⟩
    (CompanionReduction.holomorphicAt_pow_of hHol a)

/-- The prescribed current bar tangent contributes its full normal
power to the literal historical selected member on every such window. -/
theorem historical_selected_full_normal_power {n : ℕ}
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (H : BlowupTower X Y) (a : Y)
    (V : Opens Y) (u : Y → ℂ)
    (hB : (geoTransformAlong (barMarked J) H).IsWellFormed)
    (hd : 0 < (geoTransformAlong (barMarked J) H).d)
    (hu : IsTangentDirectionAlong (geoTransformAlong (barMarked J) H).N
      (geoTransformAlong (barMarked J) H).ideal (geoTransformAlong (barMarked J) H).d V u) :
    let K := positiveMemberOn J H a V
    ∀ x : V, K.ideal.mem x (fun z => u z.val ^ K.d) := by
  intro K x
  let B := geoTransformAlong (barMarked J) H
  let I := membersThrough B.E (origMembers J H) a
  let K₀ := memberRestrict B I
  obtain ⟨hh, hm⟩ := true_normal_power_in_member B hB hd I V u hu x.property
  exact comp_mem_pullback (isLocalInverseAt_val (n := n) V x).mdiff hm
    (CompanionReduction.holomorphicAt_pow_of hh K₀.d)

open InvDomainTowerAlong StepOneLowerDomain MarkedIdealOpenBiholomorphism HironakaG3RRawRegimeLocality HironakaG1LocalizedBornWindowRestriction

set_option maxHeartbeats 1000000 in
/-- On the true-mark subwindow the literal selected suffix keeps its
original canonical value. The ordinary companion, supported contact
class, and all native marks on the subwindow are read by restriction. -/
theorem exists_selected_true_mark_canonical_window {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K R : MarkedIdeal n X)
    (hK : IsInvDomain (k+1) K) (hR : IsInvDomain k R)
    (u : X → ℂ) (hu : IsTangentDirectionAlong K.N K.ideal K.d univ u)
    (hTrace : K.N ∩ {x | u x = 0} = R.N)
    (hClass : LocWPEquiv (withN (coeffMarkedAlong K) (K.N ∩ {x | u x = 0})) R)
    (hPow : ∀ x, K.ideal.mem x (fun z => u z ^ K.d))
    (T : BlowupTower X Y) (hCan : IsCanonical K ((invFamily hn (k+1)).inv K) T)
    (y : Y) (hy : y ∈ (geoTransformAlong K T).cosupp) :
    ∃ (W : Opens X) (hp : T.proj y ∈ W),
      let A := CMfd.of (n := n) W
      let M : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) K
      let P : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) R
      let v : A → ℂ := u ∘ Subtype.val
      let S := restrict W T
      let z : openPreimage T W := ⟨y, hp⟩
      IsInvDomain (k+1) M ∧ IsInvDomain k P ∧
      IsTangentDirectionAlong M.N M.ideal M.d univ v ∧
      M.N ∩ {x | v x = 0} = P.N ∧
      LocWPEquiv (withN (coeffMarkedAlong M) (M.N ∩ {x | v x = 0})) P ∧
      (∀ F ∈ M.E, ∀ z, divExpAlong n M.N M.ideal F z = 0) ∧
      (∀ z ∈ M.cosupp, nmOrd M z = K.d) ∧
      companionOf n M K.d = (⟨M.N, M.E, restrictOn n M.N M.ideal, K.d⟩ : MarkedIdeal n A) ∧
      IsCanonical M ((invFamily hn (k+1)).inv M) S ∧
      z ∈ (geoTransformAlong M S).cosupp ∧
      (invFamily hn (k+1)).inv M S z = (invFamily hn (k+1)).inv K T y := by
  let I := invFamily hn (k+1)
  have hT := I.isInvValue.isGeoTestTower_of_isCanonical hK T hCan
  have hpK : T.proj y ∈ K.cosupp :=
    proj_mem_cosupp_of_mem_cosupp hK.isWellFormed.isClosedSubmanifold_N
      hK.isWellFormed.isCoherent T hT hy
  have hpR : T.proj y ∈ R.N := by
    let x := T.proj y
    have hHol : ∀ p f, K.ideal.mem p f → HolomorphicAt n f p :=
      fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf
    have hMem := hu.mem x (mem_univ x)
    have hU := holomorphicAt_of_mem_iterDerivIdealAlong hHol (K.d-1) x u hMem
    have hd : 1 + (K.d-1) = K.d := by have := hK.one_le_d; omega
    have hOne := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 (K.d-1)
      (by rw [hd]; exact hpK)
    have hZero := (vanishesToOrderOn_one_iff hOne.1 hU).mp (hOne.2 _ hMem)
    exact hTrace ▸ (show x ∈ K.N ∩ {x | u x = 0} from ⟨hOne.1,hZero⟩)
  have hE : K.E = R.E := hClass.wEquiv.1
  obtain ⟨W, hpW, hExp⟩ := exists_retained_zero_window_of_normal_power hn K R hK hR hE u hu hTrace
    hPow (T.proj y) hpR
  let A := CMfd.of (n := n) W
  let M : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) K
  let P : MarkedIdeal n A := MarkedIdeal.pullback (Subtype.val : W → X) R
  let v : A → ℂ := u ∘ Subtype.val
  let S := restrict W T
  let z : openPreimage T W := ⟨y, hpW⟩
  have hM : IsInvDomain (k+1) M := isInvDomain_pullback_val W hK
  have hP : IsInvDomain k P := isInvDomain_pullback_val W hR
  have hHol : ∀ x f, K.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hf
  have hv : IsTangentDirectionAlong M.N M.ideal M.d univ v :=
    isTangentDirectionAlong_pullback_val W hHol
      ⟨W.isOpen,fun x _ => hu.mem x (mem_univ _),fun x _ => hu.multiplicity_one x (mem_univ _)⟩
  have hTraceW : M.N ∩ {x | v x = 0} = P.N := by
    change (Subtype.val : W → X) ⁻¹' (K.N ∩ {x | u x = 0}) = _
    rw [hTrace]
    rfl
  have hWP := hClass.restrict W
  rw [selected_bare_contact_pullback_val K hK.isWellFormed hK.one_le_d u W] at hWP
  have hCanM := Seq.ResolutionInvariantExt.isCanonical_restrict I hK W T hCan
  have hz : z ∈ (geoTransformAlong M S).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W T)).cosupp
    rw [cosupp_restrict_raw K hHol W T]
    exact hy
  obtain ⟨hOrder, hEq⟩ := true_mark_of_retained_boundary_zero M hM hv hExp
  exact ⟨W, hpW, hM, hP, hv, hTraceW, hWP, hExp, hOrder, hEq, hCanM, hz,
    I.isInvValue.restrictOpen K hK W T hCan z hy⟩

open HironakaG1ChronologicalCompanionSuffix HironakaG8HomStable
  HironakaCoherentTransformExtension

set_option maxHeartbeats 1600000 in
/-- The chronological positive head produces a genuine true-mark window
for the literal selected canonical suffix. The supported-domain premise
is on the supported member cut of that same head, before shrinking. -/
theorem chronological_companion_true_mark_window {n k l b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y)
    (u : X → ℂ)
    (hu : IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d
      (⊤ : Opens X) u)
    (hTrace : (barMarked J).N ∩ {x | u x = 0} = R.N) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA J H p
    IsInvDomain k (positiveMemberOn R H p O) →
    ∃ (V : Opens (split T r).1) (v : (split T r).1 → ℂ) (hpV : p ∈ V),
      V ≤ O ∧
      let A := CMfd.of (n := n) V
      let K := positiveMemberOn J H p V
      let P := positiveMemberOn R H p V
      let T' := restrict V S
      let y' : openPreimage S V := ⟨y, hpV⟩
      ∃ (W : Opens A) (hpW : T'.proj y' ∈ W),
        let B := CMfd.of (n := n) W
        let M : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) K
        let N : MarkedIdeal n B := MarkedIdeal.pullback (Subtype.val : W → A) P
        let w : B → ℂ := fun x => v x.val.val
        let G := restrict W T'
        let z : openPreimage T' W := ⟨y', hpW⟩
        IsInvDomain (k+1) M ∧ IsInvDomain k N ∧
        IsTangentDirectionAlong M.N M.ideal M.d univ w ∧ M.N ∩ {x | w x = 0} = N.N ∧
        LocWPEquiv (withN (coeffMarkedAlong M) (M.N ∩ {x | w x = 0})) N ∧
        (∀ F ∈ M.E, ∀ z, divExpAlong n M.N M.ideal F z = 0) ∧
        companionOf n M M.d = (⟨M.N, M.E, restrictOn n M.N M.ideal, M.d⟩ : MarkedIdeal n B) ∧
        IsCanonical M ((invFamily hn (k+1)).inv M) G ∧
        z ∈ (geoTransformAlong M G).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J T y =
          toLex (b+1, ((invFamily hn (k+1)).inv M G z : WithTop (ValTy (k+1)))) := by
  intro r H S p O hRO
  obtain ⟨hHead, _, hB, _, _, _, _, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  obtain ⟨V, v, _, hVO, hBarTan, hTan, _, hContactN, _, _, _, hContactClass,
      hpV, hK, hCanK, _, hyK, hRead⟩ :=
    positive_companion_chronological_tangent (k := k+1) hn J R hJ hR hClass hMax
      T hCan y hy hLevel hNS u hu hTrace
  let A := CMfd.of (n := n) V
  let K : MarkedIdeal n A := positiveMemberOn J H p V
  let P : MarkedIdeal n A := positiveMemberOn R H p V
  let D := geoTransformAlong (barMarked R) H
  let P₀ := memberRestrict D (membersThrough D.E (origMembers R H) p)
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hHead
  have hRH := (hClass.wEquiv.2 H).1.mp hJH
  have hDH := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRH
  have hD : IsInvDomain l D := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hDH
  have hP₀ : P₀.IsWellFormed := isWellFormed_memberRestrict hn hD.isWellFormed _
  have hP : IsInvDomain k P := by
    have hRO' : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → _) P₀) := hRO
    have h0 := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens O V) hRO'
    have h1 := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hVO).symm h0
    rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hP₀.isCoherent hVO] at h1
  have hPow := historical_selected_full_normal_power J H p V v hB.isWellFormed hB.one_le_d hBarTan
  obtain ⟨W, hpW, hMW, hNW, hTanW, hTraceW, hWPW, hExpW, _, hEqW, hCanW, hzW, hValW⟩ :=
    exists_selected_true_mark_canonical_window hn K P hK hP (v ∘ Subtype.val) hTan hContactN
      hContactClass hPow (restrict V S) hCanK ⟨y,hpV⟩ hyK
  refine ⟨V, v, hpV, hVO, W, hpW, hMW, hNW, hTanW, hTraceW, hWPW, hExpW, hEqW, hCanW, hzW, ?_⟩
  exact hRead.trans (congrArg (fun q : ValTy (k+1) =>
    toLex (b+1, (q : WithTop (ValTy (k+1))))) hValW.symm)

#print axioms true_mark_of_retained_boundary_zero
#print axioms selected_suffix_true_mark_zero_contact
#print axioms exists_retained_zero_window_of_normal_power
#print axioms historical_selected_full_normal_power
#print axioms exists_selected_true_mark_canonical_window
#print axioms chronological_companion_true_mark_window

end Hironaka.HironakaG1ChronologicalTrueMarkZero
