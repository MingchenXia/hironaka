import Hironaka.Resolution.HironakaG1RecursiveBornResidualExample

/-! The next actual order-two companion of the selected born trace. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornOrderTwoCompanionExample
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  GeneralValue NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1RecursiveBornOrderExample HironakaG1InitialPositiveGeneralRead
  HironakaG1RecursiveBornResidualExample HironakaG1LaterPositiveSuccessorRead
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount MarkedIdealBiholomorphism
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension HomogenizedIdealAlong GermIdealOrder

private abbrev A := geoTransformAlong record B
private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z

private theorem read_injective {k : ℕ} {o : ℕ} :
    Function.Injective (positiveSuccessorRead (k := k) o) := by
  intro a b h
  have h₁ := congrArg (fun v : ValTy (k + 1) => (ofLex v).2) h
  have h₂ : Sum.inr (α := WithBot MonomialInvariant.Val)
      (a : WithTop (ℕ ×ₗ WithTop (ValTy k))) = Sum.inr
      (b : WithTop (ℕ ×ₗ WithTop (ValTy k))) := congrArg ofLex h₁
  exact WithTop.coe_inj.mp (Sum.inr.inj h₂)

set_option maxHeartbeats 900000 in
/-- At the actual selected born trace, the next original recursive letter uses
its literal order-two mask and companion, of mark two and level zero. -/
theorem selected_born_order_two_companion :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let K : MarkedIdeal 3 Z := L z
      let T := BlowupTower.refl (X := Z)
      let U := ordMask (M := Z) K 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 T
      let K' : MarkedIdeal 3 P := MarkedIdeal.pullback (Subtype.val : U → O z) K
      let S := BlowupTower.refl (X := P)
      ∃ hx : x ∈ U,
        let a : U := ⟨x, hx⟩
        Q = (⟨K'.N, [], restrictOn 3 K'.N K'.ideal, 2⟩ : MarkedIdeal 3 P) ∧
        IsInvDomain 2 Q ∧ IsMaximalOrderAlong Q.N Q.ideal Q.d ∧
        a ∈ Q.cosupp ∧ level Q S a = 0 ∧
        let v := Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) Q S a
        (invFamily (by decide : 0 < 3) 2).inv K T x = positiveSuccessorRead 2 v ∧
        (invFamily (by decide : 0 < 3) 3).inv record B q =
          positiveSuccessorRead 1 (toLex (1, (positiveSuccessorRead 2 v : WithTop (ValTy 2)))) := by
  obtain ⟨hq, hz, hE, hd, hN, hRead, hSpan⟩ := selected_born_trace_gens
  obtain ⟨v', hv', hRead'⟩ := selected_born_payload_first
  obtain ⟨_, hJ, _, hLev, _⟩ := actual_positive_companion_level
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let K : MarkedIdeal 3 Z := L z
  let T := BlowupTower.refl (X := Z)
  let U := ordMask (M := Z) K 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 T
  let K' : MarkedIdeal 3 P := MarkedIdeal.pullback (Subtype.val : U → O z) K
  let S := BlowupTower.refl (X := P)
  have hLevel : level J R z = 0 + 1 := hLev
  have hK : IsInvDomain 2 K := isInvDomain_lowerMarked_succ J hJ.isWellFormed hJ.one_le_d
    (by decide : 0 < 3) R trivial hJ.dimLE hLevel
  let v := (invFamily (by decide : 0 < 3) 2).inv K T x
  have hPair : toLex (1, (v : WithTop (ValTy 2))) = toLex (1, (v' : WithTop (ValTy 2))) :=
    read_injective (hRead.symm.trans hRead')
  have hValue : v = v' := by
    have h := congrArg (fun a : ℕ ×ₗ WithTop (ValTy 2) => (ofLex a).2) hPair
    exact WithTop.coe_inj.mp h
  have hOrd : NonmonomialOrderLocal.nmOrd (M := Z) K x = 2 := by
    change (ofLex v).1 = 2
    rw [hValue]
    exact hv'
  have hxN : x ∈ K.N := NonmonomialOrderLocal.ordGe_subset_N K 2
    (NonmonomialOrderLocal.mem_ordGe_of_succ_le (q := 1) hOrd.ge)
  have hCos : x ∈ K.cosupp := by
    have hCut := ordGe_ordinaryTraceMarked_eq_cosupport (X := Z) K.N K.ideal hK.isWellFormed.isCoherent 1
    have hEq : K = ordinaryTraceMarked (X := Z) K.N K.ideal :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of (𝔪 := K) rfl hE rfl hd
    have hMem := (NonmonomialOrderLocal.mem_ordGe_iff hK.isWellFormed hK.isNonzeroAlongAt hxN 1).mpr
      (by rw [hOrd]; decide)
    have hSet : NonmonomialOrderLocal.ordGe (M := Z) K 1 = K.cosupp :=
      (congrArg (fun M : MarkedIdeal 3 Z => NonmonomialOrderLocal.ordGe (M := Z) M 1) hEq).trans
        (hCut.trans (congrArg (cosupport 3 K.N K.ideal) hd.symm))
    exact hSet ▸ hMem
  have h := original_positive_order_successor_read (k := 1) (by decide : 0 < 3) (X := Z)
    K hK T trivial x hCos 2 hOrd (by decide)
  obtain ⟨hx, hQ, hMax, _, ha, hNext⟩ := h
  have hD' : K'.d = 1 := hd
  have hE' : K'.E = [] := by
    change K.E.map _ = []
    rw [show K.E = [] from hE]
    rfl
  have hQeq : Q = (⟨K'.N, [], restrictOn 3 K'.N K'.ideal, 2⟩ : MarkedIdeal 3 P) := by
    change companionOf 3 (M := P) K' 2 = _
    simp only [companionOf, companionAlong, hD', Nat.reduceLT, if_false, hE',
      nonmonomialPartAlong_nil_eq_restrictOn]
  have hZero : level Q S (⟨x, hx⟩ : U) = 0 := by
    change boundaryCount (Q.E.take Q.E.length) (⟨x, hx⟩ : U) = _
    have hQE : Q.E = [] := congrArg MarkedIdeal.E hQeq
    rw [hQE]
    rfl
  refine ⟨hq, hz, hx, hQeq, hQ, hMax, ha, hZero, hNext, ?_⟩
  exact hRead.trans (congrArg (fun w : ValTy 2 =>
    positiveSuccessorRead 1 (toLex (1, (w : WithTop (ValTy 2))))) hNext)

open RelativePrincipalizationSpan CoefficientIdealAlongRestrictionFull GermIdealPullbackCalculus
  InvertibleIdealQuotient MarkedIdealRestrictOpen HironakaG8LogClosureHistory

private abbrev firstCoord (y : Y) : ℂ := yChart.toFun y (0 : Fin 3)
private abbrev thirdCoord (y : Y) : ℂ := yChart.toFun y (2 : Fin 3)

set_option maxHeartbeats 1200000 in
/-- On the literal order-two mask, restricting the exact companion ideal
to the coordinate section (a=0) leaves precisely the restricted span of (c^2). -/
theorem selected_order_two_coordinate_trace :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let K : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) K 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
      ∃ hx : x ∈ U,
        let a : U := ⟨x, hx⟩
        let C := Q.N ∩ {u : U | firstCoord u.val.val.val = 0}
        a ∈ C ∧ Q.d = 2 ∧
        ∀ g : U → ℂ,
          IsInSpanOnAt (n := 3) C (Q.ideal.mem a) a g ↔
            IsInSpanOnAt (n := 3) C (fun b => b = (fun u => thirdCoord u.val.val.val ^ 2)) a g := by
  obtain ⟨hq, hz, hx, hQeq, hQ, _, ha, _, _, _⟩ := selected_born_order_two_companion
  obtain ⟨hq', hz', _, _, _, _, hSpan⟩ := selected_born_trace_gens
  have hq_same : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have hz_same : hz' = hz := Subsingleton.elim _ _
  subst hz'
  obtain ⟨_, hJ, _, hLev, _⟩ := actual_positive_companion_level
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let K : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) K 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
  let φ : U → O z := Subtype.val
  let K' : MarkedIdeal 3 P := MarkedIdeal.pullback φ K
  let a : U := ⟨x, hx⟩
  let C := Q.N ∩ {u : U | firstCoord u.val.val.val = 0}
  let f₀ (u : O z) := firstCoord u.val.val ^ 2
  let f₂ (u : O z) := thirdCoord u.val.val ^ 2
  let G (f : U → ℂ) : Prop := f = f₂ ∘ φ
  have hLevel : level J R z = 0 + 1 := hLev
  have hK : IsInvDomain 2 K := isInvDomain_lowerMarked_succ J hJ.isWellFormed hJ.one_le_d
    (by decide : 0 < 3) R trivial hJ.dimLE hLevel
  have hφD : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ φ := contMDiff_subtype_val
  have hExact : Q = (⟨K'.N, [], restrictOn 3 K'.N K'.ideal, 2⟩ : MarkedIdeal 3 P) := hQeq
  have hQN : Q.N = K'.N := by
    have h := congrArg (fun M : MarkedIdeal 3 P => M.N) hExact
    exact h
  have hNC : C ⊆ φ ⁻¹' K.N := fun u hu =>
    show u ∈ K'.N from hQN ▸ hu.1
  have hAt : a ∈ C := ⟨ha.1, by change yChart.toFun q (0 : Fin 3) = 0; rw [chart_q.2]; rfl⟩
  have hD : Q.d = 2 := congrArg MarkedIdeal.d hQeq
  have hF₂ : HolomorphicAt 3 f₂ x := by
    have hφ₀ : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞
        (fun u : O z => u.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
    have h0 := (yChart.holomorphicAt_coord chart_q.1 2).comp_contMDiff
      (f := fun u : O z => u.val.val) (y := x)
      (Eventually.of_forall fun _ => hφ₀.contMDiffAt)
    have he : HolomorphicAt 3 (fun u : O z => thirdCoord u.val.val * thirdCoord u.val.val) x :=
      h0.mul h0
    simpa only [f₂, pow_two] using he
  have hF₂p : HolomorphicAt 3 (f₂ ∘ φ) a :=
    hF₂.comp_contMDiff (f := φ) (y := a) (Eventually.of_forall fun _ => hφD.contMDiffAt)
  refine ⟨hq, hz, hx, hAt, hD, fun g => ?_⟩
  change IsInSpanOnAt (n := 3) C (Q.ideal.mem a) a g ↔ IsInSpanOnAt (n := 3) C G a g
  constructor
  · refine IsInSpanOnAt.trans ?_
    intro s hs
    have hs' : (restrictOn 3 K'.N K'.ideal).mem a s := by
      have hI : Q.ideal = restrictOn 3 K'.N K'.ideal := by
        have h := congrArg (fun M : MarkedIdeal 3 P => M.ideal) hExact
        exact h
      exact hI ▸ hs
    obtain ⟨k, b, c, hb, hc, he⟩ := hs'.2
    refine IsInSpanOnAt.trans ?_ (show IsInSpanOnAt (n := 3) C (K'.ideal.mem a) a s from
      ⟨k, b, c, hb, hc, he.mono (fun u hu huC => hu (hQN ▸ huC.1))⟩)
    intro t ht
    have hp : IsInSpanAt (n := 3) (fun r => ∃ v, K.ideal.mem x v ∧ r = v ∘ φ) a t :=
      GermIdeal.mem_pullback_iff.mp ht
    refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hp)
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (hSpan v).mp (IsInSpanAt.restrict (isInSpanAt_self hv
      (GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hv)))
    change IsInSpanOnAt (n := 3) K.N (fun b => b = f₀ ∨ b = f₂) x v at hv'
    have hComp := isInSpanOnAt_comp (z := a) hφD.continuous (hφD.mdifferentiable (by simp)) hNC hv'
    refine IsInSpanOnAt.trans ?_ hComp
    rintro _ ⟨f, rfl | rfl, rfl⟩
    · refine ⟨0, Fin.elim0, Fin.elim0, (fun i => i.elim0), (fun i => i.elim0), ?_⟩
      exact Eventually.of_forall fun u hu => by
        change firstCoord u.val.val.val ^ 2 = _
        have h0 : firstCoord u.val.val.val = 0 := hu.2
        simp [h0]
    · exact IsInSpanAt.restrict (isInSpanAt_self (show G (f₂ ∘ φ) from rfl) hF₂p)
  · refine IsInSpanOnAt.trans ?_
    intro s hs
    change s = f₂ ∘ φ at hs
    subst s
    have hG : IsInSpanOnAt (n := 3) K.N (fun b => b = f₀ ∨ b = f₂) x f₂ :=
      IsInSpanAt.restrict (isInSpanAt_self (Or.inr rfl) hF₂)
    have hv : (restrictOn 3 K.N K.ideal).mem x f₂ := ⟨hF₂, (hSpan f₂).mpr hG⟩
    have hComp := isInSpanOnAt_comp (z := a) hφD.continuous (hφD.mdifferentiable (by simp))
      (show K'.N ⊆ φ ⁻¹' K.N from subset_rfl) hv.2
    have hGen : Q.ideal.mem a (f₂ ∘ φ) := by
      have hI : Q.ideal = restrictOn 3 K'.N K'.ideal := by
        have h := congrArg (fun M : MarkedIdeal 3 P => M.ideal) hExact
        exact h
      rw [hI]
      refine ⟨hF₂p, IsInSpanOnAt.mono ?_ hComp⟩
      rintro _ ⟨t, ht, rfl⟩
      exact comp_val_mem_pullback_val U hK.isWellFormed.isCoherent ht
    exact IsInSpanAt.restrict (isInSpanAt_self hGen hF₂p)

end
end Hironaka.HironakaG1RecursiveBornOrderTwoCompanionExample
