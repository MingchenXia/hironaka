import Hironaka.Resolution.HironakaG8FinitePowerReductionLocalEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8FinitePowerReductionBoundary
noncomputable section

open scoped ProductComplexManifold

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings ProductComplexManifold HomogenizedGlueingTower GermIdealOrder IdealWeightPowers
  RelativePrincipalizationSpan OrderMultiplicativity GermOrderProduct OrderTaylor CompanionReduction IdealOrderArithmetic
  HironakaSharpOriginalProductTraceOrder ResolutionInvariantSpec HironakaG8LocalHistory
  HironakaG8LocalStable HironakaActualProjectionTestRecord HironakaG8MixedEquiv
  InvertibleIdealQuotient RestrictedIdealExtension ResolutionDriver DivisorExponentAlong
  HironakaG8FinitePowerReductionLocalEquiv HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression ResolutionDriver

/-- A finite-power reduction scales the exact ordinary order at every point. -/
theorem finite_power_reduction_arbitrary_cut {n : ℕ} {X : CMfd.{0} n}
    (I J : GermIdeal n X) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hn : ∀ x ∈ (univ : Set X), DivisorExponentAlong.IsNonzeroAlongAt univ I x)
    (r e : ℕ) (he : 0 < e) (hRed : (idealPow I r).mul J = idealPow I (r+e)) (d : ℕ) (x : X) :
    x ∈ cosupport n univ J d ↔ d ≤ (ordinaryTraceOrder (X := X) univ I x) * e := by
  let o := ordinaryTraceOrder (X := X) univ I x
  have hOrder := ordinaryTraceOrder_cosupport_iff (X := X) isClosedSubmanifold_univ hI hn (mem_univ x)
  have ho : x ∈ cosupport n univ I o := (hOrder o).mpr le_rfl
  have hno : x ∉ cosupport n univ I (o+1) := fun h => Nat.not_succ_le_self o ((hOrder (o+1)).mp h)
  have hHolI := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hI (x := x) (g := g) h
  have hHolJ := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hJ (x := x) (g := g) h
  have hHolPow := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem
    (GermIdealPullbackCalculus.isCoherent_idealPow hI r) (x := x) (g := g) h
  obtain ⟨g,hg,hNot⟩ : ∃ g, I.mem x g ∧ ¬ (idealPow (pointIdeal n x) (o+1)).mem x g := by
    by_contra! hAll
    exact hno ⟨mem_univ x,fun g hg => vanishesToOrderOn_of_mem (hAll g hg)⟩
  have hG := hHolI x g hg
  have hPowBound (j : ℕ) : x ∉ cosupport n univ (idealPow I j) (o*j+1) := by
    intro hx
    have hPow := mem_idealPow_of_vanishesToOrderOn_univ
      (hx.2 _ (MonomialPart.pow_mem_idealPow hg hG j))
    exact pow_notMem_idealPow hG hNot j (by simpa [Nat.mul_comm] using hPow)
  change x ∈ cosupport n univ J d ↔ d ≤ o*e
  have hAt : x ∈ cosupport n univ ((idealPow I r).mul J) (o*(r+e)) := by
    rw [hRed, cosupport_idealPow_mul_eq hHolI (by omega : 1 ≤ r+e)]
    exact ho
  have hMax := mem_cosupport_of_mem_cosupport_mul hHolPow hHolJ
    (Nat.mul_le_mul_left o (Nat.le_add_right r e)) hAt (hPowBound r)
  rw [Nat.mul_add, Nat.add_sub_cancel_left] at hMax
  constructor
  · intro hx
    by_contra hle
    have hlt : o*e < d := Nat.lt_of_not_ge hle
    have hc : x ∈ cosupport n univ ((idealPow I r).mul J) (o*r+d) :=
      inter_cosupport_subset_cosupport_mul (o*r) d
        ⟨cosupport_subset_cosupport_idealPow o r ho,hx⟩
    have hle' : o*(r+e)+1 ≤ o*r+d := by rw [Nat.mul_add]; omega
    have hc' := cosupport_anti hle' hc
    rw [hRed] at hc'
    exact hPowBound (r+e) hc'
  · exact fun h => cosupport_anti h hMax

/-- The normalized divisor exponent follows for any member, including at
points using the built-in default. The proof compares the entire nearby
divisibility predicates through their actual ordinary cuts. -/
theorem finite_power_reduction_divExpAlong
    {n : ℕ} {X : CMfd.{0} n}
    (I J : GermIdeal n X) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hn : ∀ x ∈ (univ : Set X), IsNonzeroAlongAt univ I x)
    (r e : ℕ) (he : 0 < e) (hRed : (idealPow I r).mul J = idealPow I (r+e))
    (H : Set X) (x : X) :
    divExpAlong n univ J H x = e * divExpAlong n univ I H x := by
  have hP := GermIdealPullbackCalculus.isCoherent_idealPow hI e
  have hOne : (idealPow I 0).mul (idealPow I e) = idealPow I (0+e) := by
    rw [idealPow_zero, Nat.zero_add, BlowupControlledTransform.unitIdeal_mul hP]
  have hCut (j : ℕ) : cosupport n univ J j = cosupport n univ (idealPow I e) j := by
    ext z
    exact (finite_power_reduction_arbitrary_cut I J hI hJ hn r e he hRed j z).trans
      (finite_power_reduction_arbitrary_cut I (idealPow I e) hI hP hn 0 e he hOne j z).symm
  have hNear : IsDivNearAlong n univ J H = IsDivNearAlong n univ (idealPow I e) H := by
    funext j z
    unfold IsDivNearAlong
    rw [hCut]
  calc
    divExpAlong n univ J H x = divExpAlong n univ (idealPow I e) H x := by
      unfold divExpAlong
      rw [hNear]
    _ = e * divExpAlong n univ I H x :=
      HironakaActualPowerBoundaryExponents.divExpAlong_idealPow isClosedSubmanifold_univ hI
        (Nat.succ_le_of_lt he) x

/-- Uniform raw coefficient compression supplies both the full local class
and the exact normalized exponent at every initial ordered member. -/
theorem equal_weight_native_functions_boundary_class
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι] [Nonempty ι]
    (f : ι → X → ℂ) (hf : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i))
    (d : ℕ) (hd : 0 < d) (E : List (Set X)) :
    let w : ι → ℕ := fun _ => d
    let P : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal f,d⟩
    let Q : MarkedIdeal n X := ⟨univ,E,weightedFunctionIdeal w f,weightedCommonMark w⟩
    IsInvDomain n P → IsInvDomain n Q →
      LocWPEquiv Q P ∧
      ∀ H x, P.d * divExpAlong n Q.N Q.ideal H x = Q.d * divExpAlong n P.N P.ideal H x := by
  intro w P Q hp hq
  refine ⟨(equal_weight_native_functions_locWPEquiv f hf d hd E hp hq).symm,fun H x => ?_⟩
  let e := weightedCommonMark w / d
  let i : ι := Classical.choice inferInstance
  have he : 0 < e := compressionExponent_pos w (fun _ => hd) i
  have hm : d*e = weightedCommonMark w := weight_mul_compressionExponent w i
  let r := Fintype.card ι * (e-1)
  have hRed : (idealPow P.ideal r).mul Q.ideal = idealPow P.ideal (r+e) :=
    finite_function_power_reduction f hf r e he (by dsimp [r]; omega)
  have hExp := finite_power_reduction_divExpAlong P.ideal Q.ideal hp.isWellFormed.isCoherent
    hq.isWellFormed.isCoherent hp.isNonzeroAlongAt r e he hRed H x
  change d * divExpAlong n univ Q.ideal H x = weightedCommonMark w * divExpAlong n univ P.ideal H x
  rw [hExp, ← hm, Nat.mul_assoc]

/-- The actual weighted stage certificate supplies low canonicality
on a chart whose finite equal-weight source functions generate the
unpowered residual reference. The full inherited ordered boundary is
carried by the class and normalized exponents of the reduction. -/
theorem native_equal_weight_chart_low_canonical_inherited
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I ι : Type} [Fintype ι] [Nonempty ι]
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (T : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)))
    (hp : IsInvDomain (n+1) P) (hPN : P.N = univ)
    (d : ℕ) (hd : 1 < d) (hPd : P.d ≤ d)
    (f : ι → A.openSet i → ℂ)
    (hf : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (f j)) :
    let weight : ι → ℕ := fun _ => d
    let R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) := ⟨univ,P.E,finiteFunctionIdeal f,d⟩
    IsInvDomain (n+1) R →
    A.record i = ⟨univ,P.E,weightedFunctionIdeal weight f,weightedCommonMark weight⟩ →
    NonmonomialOrderLocal.nmPart P = R.ideal →
    IsCanonical P ((CanonicalCentres.canonicalInvariant (n+1)).inv P)
      (BlowupTowerTransforms.restrict (A.openSet i) T) := by
  intro weight R hr hRaw hResid
  have hQN : (A.record i).N = univ := congrArg MarkedIdeal.N hRaw
  have hQd : 1 < (A.record i).d := by
    rw [hRaw]
    change 1 < weightedCommonMark weight
    let j : ι := Classical.choice inferInstance
    have hE := compressionExponent_pos weight (fun _ => Nat.zero_lt_of_lt hd) j
    have hm := weight_mul_compressionExponent weight j
    change d * (weightedCommonMark weight / d) = weightedCommonMark weight at hm
    change 0 < weightedCommonMark weight / d at hE
    have hLE := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hE)
    rw [Nat.mul_one,hm] at hLE
    exact hd.trans_le hLE
  have hQDom := A.domain i
  rw [hRaw] at hQDom
  have hCl : LocWPEquiv (A.record i) R ∧
      ∀ H x, R.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
        (A.record i).d * divExpAlong (n+1) R.N R.ideal H x := by
    rw [hRaw]
    exact equal_weight_native_functions_boundary_class (X := CMfd.of (n := n+1) (A.openSet i))
      f hf d (Nat.zero_lt_of_lt hd) P.E hr hQDom
  have hActive (x : A.openSet i) (hx : x ∈ (A.record i).cosupp) :
      ordinaryTraceOrder (A.record i).N (A.record i).ideal x = (A.record i).d := by
    obtain ⟨_, _, hN, hI, V, S, k, a, w, hw, _, _, hMark, _, _, hAt⟩ := A.native i
    have hv : V.Nonempty := by
      by_contra hNo
      have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
      have hOne : (A.record i).d = 1 := by
        rw [hMark]
        subst V
        simp [weightedCommonMark]
      omega
    have hOrd := (HironakaActualHistoricalNativeOrdinaryOrder.actual_native_point_ordinary_order
      S hv a w hw _ _ hN hI hMark x hx (hAt x hx)).1
    rwa [hN,hMark]
  exact HironakaG8EqualWeightNativeThresholds.native_simultaneous_canonical_via_residual_reference
    A.openSet A.record A.domain A.exponent A.positive T hSync i P R hp hr hPN rfl hQN
    rfl hPd hResid hCl.1 (fun H _ x _ _ => hCl.2 H x) hActive

end
end Hironaka.HironakaG8FinitePowerReductionBoundary
