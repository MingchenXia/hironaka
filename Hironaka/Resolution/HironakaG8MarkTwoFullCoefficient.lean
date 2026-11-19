import Hironaka.Resolution.HironakaActualWeightedNormalAmbientDerivatives
import Hironaka.Resolution.HironakaActualContactWeightedCoefficientThreshold

/-! Exact simplification of the actual double coefficient operation at mark two. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff ENat

namespace Hironaka.HironakaG8MarkTwoFullCoefficient

open Hironaka.HolomorphicIdealSheaves MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong HomogenizedIdeal HomogenizedGlueing HomogenizedEquivalence
  DerivativeIdeal DerivativeIdealAlong IdealWeightPowers CoefficientIdeal
  RestrictedIdealExtension GermIdealPullbackCalculus RelativePrincipalizationSpan
  FactorizationFromResolution RestrictLeCalculus BlowupDerivativeIdeal BlowupControlledTransform
  HironakaActualWeightedNormalAmbientDerivatives GermIdealOrder IdealOrderArithmetic

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

private theorem finite_two {J : ℕ → GermIdeal n X} (h0 : (J 0).IsCoherent)
    (h1 : (J 1).IsCoherent) :
    finSumIdeal J 2 = sumIdeal (J 0) (J 1) := by
  rw [finSumIdeal_succ (μ := 1) (fun i hi => by
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl
    · exact h0
    · exact h1), finSumIdeal_one h0]

private theorem coefficient_two (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent)
    (hN : M.N = univ) (hMark : M.d = 2) :
    (coeffMarkedAlong M).ideal = sumIdeal M.ideal (idealPow (derivIdeal M.ideal) 2) := by
  change finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
    (sumExp (fun j => M.d - j) M.d i)) M.d = _
  rw [hN,hMark]
  have ihol := fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hM (x := x) (g := g) hg
  simp only [iterDerivIdealAlong_univ ihol]
  have h0 : sumExp (fun j => 2 - j) 2 0 = 1 := by decide
  have h1 : sumExp (fun j => 2 - j) 2 1 = 2 := by decide
  rw [finite_two (J := fun i => idealPow (iterDerivIdeal M.ideal i) (sumExp (fun j => 2 - j) 2 i))
    (isCoherent_idealPow (isCoherent_iterDerivIdeal hM 0) _)
    (isCoherent_idealPow (isCoherent_iterDerivIdeal hM 1) _), h0, h1]
  change sumIdeal (idealPow M.ideal 1) (idealPow (derivIdeal M.ideal) 2) = _
  rw [idealPow_one_of_isCoherent hM]

private theorem homogenized_two (A : GermIdeal n X) (hA : A.IsCoherent) :
    homogenizedIdealAlong univ A 2 = sumIdeal A (idealPow (derivIdeal A) 2) := by
  unfold homogenizedIdealAlong tangentIdealAlong homSum
  have ihol := fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hA (x := x) (g := g) hg
  simp only [iterDerivIdealAlong_univ ihol]
  have hD : (derivIdeal A).IsCoherent := isCoherent_iterDerivIdeal hA 1
  rw [finite_two (isCoherent_mul hA (isCoherent_idealPow hD 0))
    (isCoherent_mul hD (isCoherent_idealPow hD 1))]
  change sumIdeal (A.mul (unitIdeal n X)) ((derivIdeal A).mul (idealPow (derivIdeal A) 1)) = _
  rw [mul_unitIdeal hA, idealPow_succ (p := 1), RestrictLeCalculus.mul_comm']

private theorem sum_absorb_right {A B : GermIdeal n X} (hA : A.IsCoherent) (h : B.Le A) :
    sumIdeal A B = A := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    change IsInSpanAt (n := n) (fun f => A.mem x f ∨ B.mem x f) x g at hg
    exact mem_of_isInSpanAt hA (hg.mono (fun f hf => hf.elim id (h x f)))
  · exact le_sumIdeal_left hA x g

private theorem deriv_homogenized_two (A : GermIdeal n X) (hA : A.IsCoherent) :
    derivIdeal (sumIdeal A (idealPow (derivIdeal A) 2)) = derivIdeal A := by
  let D := derivIdeal A
  have hD : D.IsCoherent := isCoherent_iterDerivIdeal hA 1
  have hD₂ : (idealPow D 2).IsCoherent := isCoherent_idealPow hD 2
  have hPow : (derivIdeal (idealPow D 2)).Le D := by
    have h := derivIdeal_le_idealPow (q := 1)
      (𝔞 := idealPow D 2) (𝔟 := D)
      (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hD (x := x) (g := g) hg)
      (fun _ _ hg => hg)
    rw [idealPow_one_of_isCoherent hD] at h
    exact h
  have h := iterDerivIdeal_sum hA hD₂ 1
  change derivIdeal (sumIdeal A (idealPow D 2)) = sumIdeal D (derivIdeal (idealPow D 2)) at h
  exact h.trans (sum_absorb_right hD hPow)

/-- The complete actual double coefficient ideal at mark two is the
original ideal plus the square of its first derivative ideal. -/
theorem mark_two_double_coefficient_ideal (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (hN : M.N = univ) (hMark : M.d = 2) :
    (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))).ideal =
      sumIdeal M.ideal (idealPow (derivIdeal M.ideal) 2) := by
  let H := homMarkedAlong M
  let B := coeffMarkedAlong H
  let J := sumIdeal M.ideal (idealPow (derivIdeal M.ideal) 2)
  have hD : (derivIdeal M.ideal).IsCoherent := isCoherent_iterDerivIdeal hM 1
  have hJ : J.IsCoherent := isCoherent_sumIdeal hM (isCoherent_idealPow hD 2)
  have hH : H.ideal = J := by
    change homogenizedIdealAlong M.N M.ideal M.d = J
    rw [hN,hMark]
    exact homogenized_two M.ideal hM
  have hHC : H.ideal.IsCoherent := hH.symm ▸ hJ
  have hHMark : H.d = 2 := hMark
  have hBMark : B.d = 2 := by
    change (coeffMarkedAlong H).d = _
    rw [coeffMarkedAlong_d (by rw [hHMark]; decide),hHMark]
    decide
  have hDerJ : derivIdeal J = derivIdeal M.ideal := deriv_homogenized_two M.ideal hM
  have hDuplicate : sumIdeal J (idealPow (derivIdeal M.ideal) 2) = J :=
    sum_absorb_right hJ (le_sumIdeal_right (isCoherent_idealPow hD 2))
  have hB : B.ideal = J := by
    change (coeffMarkedAlong H).ideal = _
    rw [coefficient_two H hHC hN hHMark, hH,hDerJ,hDuplicate]
  change (coeffMarkedAlong B).ideal = J
  rw [coefficient_two B (hB.symm ▸ hJ) hN hBMark,hB,hDerJ,hDuplicate]

/-- On a fixed contact trace, the raw order is the exact double-coefficient
order if twice the derivative trace order is at least the raw order. -/
theorem mark_two_double_coefficient_trace_order (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (hN : M.N = univ) (hMark : M.d = 2)
    (S : Set X) (x : X) (hx : x ∈ S) (p b : ℕ)
    (hRaw : order n S M.ideal x = (p : ℕ∞))
    (hDer : OrderGE n S (derivIdeal M.ideal) x b) (hBound : p ≤ b+b) :
    order n S (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))).ideal x = (p : ℕ∞) := by
  rw [mark_two_double_coefficient_ideal M hM hN hMark]
  let D := derivIdeal M.ideal
  let J := sumIdeal M.ideal (idealPow D 2)
  have hD : D.IsCoherent := isCoherent_iterDerivIdeal hM 1
  have h₁ := fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hM (x := z) (g := g) hg
  have h₂ := fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem
    (isCoherent_idealPow hD 2) (x := z) (g := g) hg
  have hJ := isCoherent_sumIdeal hM (isCoherent_idealPow hD 2)
  have hHol := fun z g hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ (x := z) (g := g) hg
  have hPow : OrderGE n S (idealPow D 2) x p := by
    rw [idealPow_succ (p := 1), idealPow_one_of_isCoherent hD]
    exact (orderGE_mul hDer hDer).mono hBound
  have hCos (k : ℕ) :
      cosupport n S J k = cosupport n S M.ideal k ∩ cosupport n S (idealPow D 2) k :=
    cosupport_sumIdeal h₁ h₂ k
  change order n S J x = (p : ℕ∞)
  apply le_antisymm
  · rw [← hRaw]
    apply iSup₂_le
    intro q hq
    have hqJ : x ∈ cosupport n S J q := ⟨hx,hq⟩
    exact (le_order_iff (h₁ x)).mpr ((hCos q ▸ hqJ).1).2
  · have hRawGe := (le_order_iff (h₁ x)).mp hRaw.ge
    have hP : x ∈ cosupport n S J p := (hCos p).symm ▸ ⟨⟨hx,hRawGe⟩,⟨hx,hPow⟩⟩
    exact (le_order_iff (hHol x)).mpr hP.2


end Hironaka.HironakaG8MarkTwoFullCoefficient
