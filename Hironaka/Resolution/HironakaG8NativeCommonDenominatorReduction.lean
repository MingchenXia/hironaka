import Hironaka.Resolution.HironakaG8FinitePowerReductionBoundary
import Mathlib.Algebra.GCDMonoid.Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeCommonDenominatorReduction
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  ResolutionInvariantSpec ResolutionDriver DivisorExponentAlong HironakaSharpOriginalProductTraceOrder HironakaG8LocalHistory
  HironakaG8FinitePowerReductionBoundary HironakaG8FinitePowerReductionLocalEquiv
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression

/-- Lowering the common mark to any divisor which is still a multiple of
all original weights gives literal uniformly powered normalized functions
at the native product mark. -/
theorem weightedFunctionIdeal_eq_common_denominator_power
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (f : ι → X → ℂ)
    (d : ℕ) (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w) :
    weightedFunctionIdeal (n := n) w f =
      finiteFunctionIdeal (fun i => (f i ^ (d/w i)) ^ (weightedCommonMark w / d)) := by
  unfold weightedFunctionIdeal
  apply congrArg (finiteFunctionIdeal (n := n))
  funext i x
  change f i x ^ (weightedCommonMark w / w i) = (f i x ^ (d / w i)) ^ (weightedCommonMark w / d)
  rw [← pow_mul]
  congr 1
  apply Nat.eq_of_mul_eq_mul_left (hw i)
  rw [weight_mul_compressionExponent, ← Nat.mul_assoc, Nat.mul_div_cancel' (hWeights i),
    Nat.mul_div_cancel' hDvd]

/-- The native product mark and a smaller valid common denominator give
all local weak projection tests and all scaled inherited boundary exponents. -/
theorem common_denominator_native_boundary_class
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (f : ι → X → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i))
    (d : ℕ) (hd : 0 < d) (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (E : List (Set X)) :
    let P : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal (fun i => f i ^ (d/w i)),d⟩
    let Q : MarkedIdeal n X := ⟨univ,E,weightedFunctionIdeal w f,weightedCommonMark w⟩
    IsInvDomain n P → IsInvDomain n Q →
    LocWPEquiv Q P ∧ ∀ H x, P.d * divExpAlong n Q.N Q.ideal H x = Q.d * divExpAlong n P.N P.ideal H x := by
  intro P Q hp hq
  let e := weightedCommonMark w / d
  let g := fun i => f i ^ (d/w i)
  have hm : d*e = weightedCommonMark w := Nat.mul_div_cancel' hDvd
  have hM := weightedCommonMark_pos w hw
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd hM hDvd) hd
  have hg (i : ι) : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) := (hf i).pow _
  have hQ : Q = ⟨univ,E,finiteFunctionIdeal (fun i => g i ^ e),d*e⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
      (weightedFunctionIdeal_eq_common_denominator_power w hw f d hWeights hDvd) hm.symm
  have hCl : LocWPEquiv P Q := by
    rw [hQ] at hq ⊢
    exact finite_function_power_locWPEquiv g hg d e he E hp hq
  refine ⟨hCl.symm,fun H x => ?_⟩
  let r := Fintype.card ι * (e-1)
  have hRed : (idealPow P.ideal r).mul Q.ideal = idealPow P.ideal (r+e) := by
    rw [hQ]
    exact finite_function_power_reduction g hg r e he (by dsimp [r]; omega)
  have hExp := finite_power_reduction_divExpAlong P.ideal Q.ideal hp.isWellFormed.isCoherent
    hq.isWellFormed.isCoherent hp.isNonzeroAlongAt r e he hRed H x
  change d * divExpAlong n univ Q.ideal H x = weightedCommonMark w * divExpAlong n univ P.ideal H x
  rw [hExp, ← hm, Nat.mul_assoc]

/-- The least common multiple of the original weights is an admissible
choice in the mixed-weight comparison with the native product mark. -/
theorem native_lcm_dvd_product {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    let d := Finset.univ.lcm w
    0 < d ∧ (∀ i, w i ∣ d) ∧ d ∣ weightedCommonMark w := by
  intro d
  have hDvd : d ∣ weightedCommonMark w :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem w hi
  have hPos : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_dvd_iff] at hDvd
    exact (Nat.ne_of_gt (weightedCommonMark_pos w hw)) hDvd
  exact ⟨hPos,fun i => Finset.dvd_lcm (Finset.mem_univ i),hDvd⟩

/-- The actual weighted stage certificate supplies low canonicality
on a chart whose source functions at a lower common denominator generate
the residual reference. All inherited ordered boundary exponents transfer. -/
theorem native_common_denominator_chart_low_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I ι : Type} [Fintype ι]
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (T : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)))
    (hp : IsInvDomain (n+1) P) (hPN : P.N = univ)
    (weight : ι → ℕ) (hPositive : ∀ j, 0 < weight j)
    (d : ℕ) (hd : 1 < d) (hPd : P.d ≤ d)
    (hWeights : ∀ j, weight j ∣ d) (hDvd : d ∣ weightedCommonMark weight)
    (f : ι → A.openSet i → ℂ)
    (hf : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (f j)) :
    let R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,P.E,finiteFunctionIdeal (fun j => f j ^ (d / weight j)),d⟩
    IsInvDomain (n+1) R →
    A.record i = ⟨univ,P.E,weightedFunctionIdeal weight f,weightedCommonMark weight⟩ →
    NonmonomialOrderLocal.nmPart P = R.ideal →
    IsCanonical P ((CanonicalCentres.canonicalInvariant (n+1)).inv P)
      (BlowupTowerTransforms.restrict (A.openSet i) T) := by
  intro R hr hRaw hResid
  have hQN : (A.record i).N = univ := congrArg MarkedIdeal.N hRaw
  have hQd : 1 < (A.record i).d := by
    rw [hRaw]
    change 1 < weightedCommonMark weight
    exact hd.trans_le (Nat.le_of_dvd (weightedCommonMark_pos weight hPositive) hDvd)
  have hQDom := A.domain i
  rw [hRaw] at hQDom
  have hCl : LocWPEquiv (A.record i) R ∧
      ∀ H x, R.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
        (A.record i).d * divExpAlong (n+1) R.N R.ideal H x := by
    rw [hRaw]
    exact common_denominator_native_boundary_class (X := CMfd.of (n := n+1) (A.openSet i))
      weight hPositive f hf d (Nat.zero_lt_of_lt hd) hWeights hDvd P.E hr hQDom
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
end Hironaka.HironakaG8NativeCommonDenominatorReduction
