import Hironaka.Resolution.HironakaG1RecursiveBornOrderTwoTangentExample
import Hironaka.Resolution.HironakaG1CanonicalNormalJointNativeExample

/-! The exact terminal curve value of the canonical recursive born example. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornNumericalPayloadExample
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  GeneralValue NonmonomialOrderTail NonmonomialOrderLocal ResolutionInvariantSpec CanonicalCentres
  GermIdealOrder RelativePrincipalizationSpan HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  HironakaG1CanonicalNormalJointNativeExample
  CompanionRebase CompanionReductionAlong RestrictedIdealExtension MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal HironakaSharpOriginalProductTraceOrder
  CodimOneSupport CodimOneSupportAlong AnalyticSubsetOpens BlowupFlatCoordinates

private theorem singleton_regular {M : CMfd.{0} 3} (x : M) :
    RegularAtDim (n := 3) ({x} : Set M) x 0 := by
  let e := complexChartAt (n := 3) x
  let q := e.val x
  let Φ : LocalHolomorphicEquivAt (n := 3) q := {
    source := e.val.target
    target := (fun w : ComplexModel 3 => w + q) ⁻¹' e.val.target
    isOpen_source := e.val.open_target
    isOpen_target := e.val.open_target.preimage (continuous_id.add_const q)
    center_mem_source := e.val.map_source (mem_complexChartAt_source x)
    toFun := fun z => z - q
    invFun := fun z => z + q
    toFun_holomorphic := (differentiable_id.sub_const q).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const q).differentiableOn
    mapsTo_toFun := by intro z hz; simpa only [mem_preimage, sub_add_cancel] using hz
    mapsTo_invFun := fun _ hw => hw
    left_inv := fun z _ => sub_add_cancel z q
    right_inv := fun z _ => add_sub_cancel_right z q }
  refine ⟨Nat.zero_le 3, mem_singleton _, Φ, Subset.rfl, sub_self q, ?_⟩
  intro y hy _
  constructor
  · intro hyx
    rw [mem_singleton_iff.mp hyx]
    change q - q ∈ complexCoordinatePlane 3 0
    rw [sub_self]
    intro i _
    rfl
  · intro hz
    have heq : e.val y - q = 0 := by
      ext i
      exact hz i (Nat.zero_le _)
    exact mem_singleton_iff.mpr (e.val.injOn hy (mem_complexChartAt_source x) (sub_eq_zero.mp heq))

set_option maxHeartbeats 700000 in
/-- The actual mark-two, empty-boundary curve with isolated cosupport at an
order-two point reads the order-two special value at the empty history. -/
theorem order_two_special_at_true_mark_two {X : CMfd.{0} 3} (M : MarkedIdeal 3 X)
    (hM : IsInvDomain 1 M) (hd : M.d = 2) (hE : M.E = []) (p : X)
    (hp : p ∈ M.cosupp) (hOrd : nmOrd M p = 2)
    (hReg : RegularAtDim (n := 3) M.N p 1)
    (hIso : ∀ᶠ y in 𝓝 p, y ∈ M.cosupp ↔ y = p) :
    (invFamily (by decide : 0 < 3) 1).inv M (BlowupTower.refl (X := X)) p = orderTwoSpecialValue := by
  let T := BlowupTower.refl (X := X)
  let W := ordMask (M := X) M 2
  let Y := CMfd.of (n := 3) W
  let C : MarkedIdeal 3 Y := compAt (X := X) M 2 T
  let M' : MarkedIdeal 3 Y := MarkedIdeal.pullback (Subtype.val : W → X) M
  let R := BlowupTower.refl (X := Y)
  let R₀ := invFamily (by decide : 0 < 3) 0
  obtain ⟨hpW, hC, _, _, hCos, hVal⟩ :=
    original_positive_order_successor_read (k := 0) (by decide : 0 < 3) (X := X)
      M hM T trivial p hp 2 hOrd (by decide)
  let q : W := ⟨p, hpW⟩
  have hE' : M'.E = [] := by
    change M.E.map _ = []
    rw [hE]
    rfl
  have hD' : M'.d = 2 := hd
  have hCeq : C = (⟨M'.N, [], restrictOn 3 M'.N M'.ideal, 2⟩ : MarkedIdeal 3 Y) := by
    change companionOf 3 (M := Y) M' 2 = _
    simp only [companionOf, companionAlong, hD', Nat.lt_irrefl, if_false, hE',
      nonmonomialPartAlong_nil_eq_restrictOn]
  have hMI : M'.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hM.isWellFormed.isCoherent
  have hCompCos : C.cosupp = M'.cosupp := by
    rw [hCeq]
    change cosupport 3 M'.N (restrictOn 3 M'.N M'.ideal) 2 = cosupport 3 M'.N M'.ideal M'.d
    rw [hD']
    exact Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hMI) 2)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn 2)
  have hBar : (barMarked C).cosupp = (Subtype.val : W → X) ⁻¹' M.cosupp := by
    rw [cosupp_barMarked C hC.isWellFormed hC.one_le_d, hCompCos]
    exact cosupp_pullback_val M
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) W
  have hNear : ∀ᶠ z : W in 𝓝 q, z ∈ ({q} : Set W) ↔ z ∈ (barMarked C).cosupp := by
    rw [hBar]
    filter_upwards [continuous_subtype_val.continuousAt.eventually hIso] with z hz
    change z ∈ ({q} : Set W) ↔ z.val ∈ M.cosupp
    exact ⟨fun h => hz.mpr (congrArg Subtype.val (mem_singleton_iff.mp h)),
      fun h => mem_singleton_iff.mpr (Subtype.ext (hz.mp h))⟩
  have hRegC : RegularAtDim (n := 3) C.N q 1 := by
    rw [hCeq]
    exact regularAtDim_preimage_val_iff.mpr hReg
  have hLev : level C R q = 0 := by
    change boundaryCount (C.E.take C.E.length) q = _
    have hc : C.E = [] := congrArg MarkedIdeal.E hCeq
    rw [hc]
    rfl
  have hSpec : IsSpecial C R q := Or.inl ⟨hLev, ⟨0, hRegC,
    regularAtDim_of_eventually_mem_iff hNear (singleton_regular (M := Y) q)⟩⟩
  have hStep : Seq.StepOneValueMasked.stepOneInvM R₀ C R q =
      toLex (0, (⊤ : WithTop (ValTy 0))) := by
    change Seq.StepOneValueMasked.stepOneInvL R₀ C (lowerMarkedM C) R q = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R₀ C _ R hSpec, hLev]
  exact hVal.trans (congrArg (positiveSuccessorRead 2) hStep)
open HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1RecursiveBornResidualExample HironakaG1RecursiveBornOrderTwoCompanionExample
  HironakaG1RecursiveBornOrderTwoBarExample HironakaG1RecursiveBornOrderTwoTangentExample
  ContactStageKept CoefficientIdealRestriction TangentDirectionAlong HomogenizedGlueingTower HomogenizedGlueing
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaRelativeNormalIdeal BlowupMonomialCharts
  NormalCrossings SNCGlobalPrimeComponents InvDomainTowerAlong RegularPointDimension
  MonomialPartAlong HironakaG1RecursiveBornOrderExample
  CoefficientIdealAlongRestrictionFull GermIdealPullbackCalculus InvertibleIdealQuotient

private abbrev A := geoTransformAlong record B
private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z
private abbrev X₀ := CMfd.of (n := 3) (productOpen (⊤ : Opens (ComplexModel 2)))
private abbrev p₀ : X₀ := zeroSection (⊤ : Opens (ComplexModel 2)) ⟨0, mem_univ _⟩
private abbrev F : Set Y := π ⁻¹' ({p₀} : Set X₀)

private theorem born_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ F ↔ yChart.toFun z (1 : Fin 3) = 0 := by
  have hp : p₀.val = 0 := map_zero (tangentInclusion 2 1)
  constructor
  · intro h
    have hi := congrArg (fun x : X₀ => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p₀.val (1 : Fin 3) at hi
    rw [chart_projection z hz, hp, monomial_apply] at hi
    simpa using hi
  · intro he
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz, hp]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using he
    · simp [monomial_apply, hi, he]

set_option maxHeartbeats 1900000 in
/-- The complete original successor value at the canonical middle-chart
survivor, including the terminal special curve letter. -/
theorem actual_recursive_born_numerical_payload :
    (invFamily (by decide : 0 < 3) 3).inv record B q =
      positiveSuccessorRead 1 (toLex (1, (positiveSuccessorRead 2
        (toLex (0, (orderTwoSpecialValue : WithTop (ValTy 1)))) : WithTop (ValTy 2)))) := by
  obtain ⟨hq, hz, hx, S, haS, hDom, _, hRead⟩ := actual_order_two_canonical_coordinate_read
  obtain ⟨hq', hz', hx', hQeq, hQ, _, _, _, _, _⟩ := selected_born_order_two_companion
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  obtain ⟨hq', hz', hx', V₀, _, haQ, haV, _, hTan⟩ := actual_order_two_coordinate_tangent
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  obtain ⟨hq', hz', hx', hd, hTwo, hThree⟩ := actual_recursive_born_coordinate_coefficient_exact_order
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  obtain ⟨hq', hz', hx', _, _, hSpan⟩ := actual_recursive_born_coordinate_coefficient_bounds
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  obtain ⟨hq', hz', _, _, hN, _, _⟩ := selected_born_trace_gens
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let M : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) M 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt M 2 (BlowupTower.refl (X := Z))
  let a : U := ⟨x, hx⟩
  let u : U → ℂ := fun y => yChart.toFun y.val.val.val (0 : Fin 3)
  let v : U → ℂ := fun y => yChart.toFun y.val.val.val (2 : Fin 3)
  let T := BlowupTower.refl (X := P)
  let E := CMfd.of (n := 3) S
  let R' : MarkedIdeal 3 E := contactMarkedKept Q u T S
  let b : S := ⟨a, haS⟩
  let C : Set U := Q.N ∩ {y | u y = 0}
  let D := coeffMarkedAlong (barMarked Q)
  let N : MarkedIdeal 3 P := withN D C
  have hR : R' = MarkedIdeal.pullback (Subtype.val : S → U) N := rfl
  have hDcoh : D.ideal.IsCoherent :=
    isCoherent_restrictedCoeff Q hQ.isWellFormed.isCoherent hQ.isWellFormed.isClosedSubmanifold_N u T trivial
  have hNcoh : N.ideal.IsCoherent := hDcoh
  have hd' : R'.d = 2 := hd
  have hE' : R'.E = [] := by
    have hQE : Q.E = [] := congrArg (fun G : MarkedIdeal 3 P => G.E) hQeq
    change Q.E.map _ = []
    rw [hQE]
    rfl
  have hCut (m : ℕ) : b ∈ cosupport 3 R'.N R'.ideal m ↔ a ∈ cosupport 3 C D.ideal m := by
    let N' : MarkedIdeal 3 P := ⟨C, [], D.ideal, m⟩
    have hEq := cosupp_pullback_val N'
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hDcoh hg) S
    exact Set.ext_iff.mp hEq b
  have hGood : b ∈ cosupport 3 R'.N R'.ideal 2 := (hCut 2).mpr hTwo
  have hBad : b ∉ cosupport 3 R'.N R'.ideal 3 := fun h => hThree ((hCut 3).mp h)
  have hb : b ∈ R'.cosupp := by
    change b ∈ cosupport 3 R'.N R'.ideal R'.d
    rw [hd']
    exact hGood
  have hSOrd : nmOrd (M := E) R' b = 2 := by
    have hO (m : ℕ) : ordGe (M := E) R' m = cosupport 3 R'.N R'.ideal m := by
      have hEq : ordGe (M := E) (ordinaryTraceMarked (X := E) R'.N R'.ideal) m = ordGe (M := E) R' m := by
        change cosupport 3 R'.N (nonmonomialPartAlong 3 R'.N R'.ideal []) m =
          cosupport 3 R'.N (nonmonomialPartAlong 3 R'.N R'.ideal R'.E) m
        rw [hE']
      exact hEq.symm.trans (ordGe_ordinaryTraceMarked_eq_cosupport R'.N R'.ideal hDom.isWellFormed.isCoherent m)
    have hLow : 2 ≤ nmOrd (M := E) R' b :=
      (mem_ordGe_iff hDom.isWellFormed hDom.isNonzeroAlongAt hGood.1 2).mp ((hO 2).symm ▸ hGood)
    have hHigh : ¬ 3 ≤ nmOrd (M := E) R' b := fun h =>
      hBad ((hO 3) ▸ (mem_ordGe_iff hDom.isWellFormed hDom.isNonzeroAlongAt hGood.1 3).mpr h)
    omega
  have hQN : Q.N = {y : U | y.val.val.val ∈ F} := by
    have hqN := congrArg (fun Q : MarkedIdeal 3 P => Q.N) hQeq
    exact hqN.trans (congrArg ((Subtype.val : U → O z) ⁻¹' ·) hN)
  have hQReg : RegularAtDim (n := 3) Q.N a 2 := by
    have hA := isInvDomain_geoTransformAlong domain B test
    have hS : IsSNCDivisor 3 [F] := (show A.E = [F] from stage_boundary) ▸ hA.isWellFormed.isSNCDivisor
    have hqF := (born_iff chart_q.1).mpr (by rw [chart_q.2]; rfl)
    have hr : RegularAtDim (n := 3) F q 2 := regularAtDim_member hS (0 : Fin 1) hqF
    have h₁ : RegularAtDim (n := 3) ((Subtype.val : W → Y) ⁻¹' F) z 2 :=
      regularAtDim_preimage_val_iff.mpr hr
    have h₂ : RegularAtDim (n := 3)
        ((Subtype.val : O z → W) ⁻¹' ((Subtype.val : W → Y) ⁻¹' F)) x 2 :=
      regularAtDim_preimage_val_iff.mpr h₁
    have h₃ : RegularAtDim (n := 3)
        ((Subtype.val : U → O z) ⁻¹' ((Subtype.val : O z → W) ⁻¹' ((Subtype.val : W → Y) ⁻¹' F))) a 2 :=
      regularAtDim_preimage_val_iff.mpr h₂
    rw [hQN]
    exact h₃
  have hau : u a = 0 := by change yChart.toFun q (0 : Fin 3) = 0; rw [chart_q.2]; rfl
  obtain ⟨k, hk, hReg⟩ := hTan.regularAtDim_contact
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg)
    hQ.isWellFormed.isClosedSubmanifold_N ⟨⟨haQ.1, hau⟩, haV⟩
  have hTwoDim : k = 2 := eq_of_regularAtDim hk hQReg
  have hCReg : RegularAtDim (n := 3) C a 1 := by
    rw [hTwoDim] at hReg
    refine regularAtDim_of_eventually_mem_iff ?_ hReg
    filter_upwards [V₀.isOpen.mem_nhds haV] with y hy
    exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  have hRReg : RegularAtDim (n := 3) R'.N b 1 := regularAtDim_preimage_val_iff.mpr hCReg
  have hIsoRaw : ∀ᶠ y : U in 𝓝 a, y ∈ N.cosupp ↔ y = a := by
    obtain ⟨k, s, c, hs, _, he⟩ := hSpan
    have hMem : ∀ᶠ y : U in 𝓝 a, ∀ i, D.ideal.mem y (s i) :=
      eventually_all.mpr fun i => eventually_mem hDcoh (hs i)
    have hCont : Continuous (fun y : U => y.val.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    filter_upwards [hMem, he, hCont.continuousAt.eventually (yChart.isOpen_source.mem_nhds chart_q.1)]
      with y hy hyEq hyChart
    constructor
    · intro hyC
      have hyN : y ∈ C := hyC.1
      have hy0 : u y = 0 := hyN.2
      have hyF : y.val.val.val ∈ F := by
        change y ∈ {u : U | u.val.val.val ∈ F}
        rw [← hQN]
        exact hyN.1
      have hy1 := (born_iff hyChart).mp hyF
      have hc : ∀ i, s i y = 0 := fun i =>
        (vanishesToOrderOn_one_iff hyC.1
          (GermIdeal.IsCoherent.holomorphicAt_mem hDcoh (hy i))).mp
          ((hyC.2 _ (hy i)).mono (hd.symm ▸ (by decide : 1 ≤ 2)))
      have hv2 : v y ^ 2 = 0 := by
        have h := hyEq hyN
        change v y ^ 2 = _ at h
        rw [h]
        simp [hc]
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply yChart.toPartialEquiv.injOn hyChart chart_q.1
      change yChart.toFun y.val.val.val = yChart.toFun q
      rw [chart_q.2]
      ext i
      fin_cases i
      · exact hy0
      · exact hy1
      · exact eq_zero_of_pow_eq_zero hv2
    · rintro rfl
      change a ∈ cosupport 3 C D.ideal D.d
      have hm : D.d = 2 := hd
      rw [hm]
      exact hTwo
  have hIso : ∀ᶠ y : S in 𝓝 b, y ∈ R'.cosupp ↔ y = b := by
    rw [hR, cosupp_pullback_val N
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hNcoh hg) S]
    filter_upwards [continuous_subtype_val.continuousAt.eventually hIsoRaw] with y hy
    exact ⟨fun h => Subtype.ext (hy.mp h), fun h => hy.mpr (congrArg Subtype.val h)⟩
  have hValue := order_two_special_at_true_mark_two R' hDom hd' hE' b hb hSOrd hRReg hIso
  exact hRead.trans (congrArg (fun w : ValTy 1 =>
    positiveSuccessorRead 1 (toLex (1, (positiveSuccessorRead 2
      (toLex (0, (w : WithTop (ValTy 1)))) : WithTop (ValTy 2))))) hValue)

end
end Hironaka.HironakaG1RecursiveBornNumericalPayloadExample
