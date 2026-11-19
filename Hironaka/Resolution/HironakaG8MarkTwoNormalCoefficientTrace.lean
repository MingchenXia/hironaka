import Hironaka.Resolution.HironakaG8MarkTwoFullCoefficient
import Hironaka.Resolution.HironakaActualWeightedNormalHomogenizedDerivatives

/-! Native weighting at degrees one and two, and the exact original double coefficient trace
for a mark-two normal padding. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8MarkTwoNormalCoefficientTrace

noncomputable section

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueing HomogenizedEquivalence HomogenizedIdealAlong CoefficientIdeal
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalPadding
  HironakaActualOpenZeroSectionDifferentials HironakaActualWeightedCoefficientCompression
  HironakaActualCoherentWeightedCoefficientMarked HironakaG8MarkTwoFullCoefficient
  GermIdealPullbackCalculus HironakaSmoothSubmersionCoefficientIdeals
  BlowupDerivativeIdeal DerivativeIdeal IdealWeightPowers
  HironakaSmoothSubmersionRelativeRestriction RestrictedIdealExtension

/-- Standard-basis functions with degrees one and two are cleared at mark two. -/
theorem degree_one_two_weighted_functions {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] (c : Fin 2 → X → ℂ) :
    let w : Fin 2 → ℕ := fun i => if i = 0 then 1 else 2
    weightedCommonMark w = 2 ∧
      weightedFunctionIdeal (n := n) w c =
        finiteFunctionIdeal (fun i x => if i = 0 then c i x ^ 2 else c i x) := by
  intro w
  have hw : weightedCommonMark w = 2 := by decide
  refine ⟨hw, ?_⟩
  unfold weightedFunctionIdeal
  rw [hw]
  congr 1
  funext i x
  fin_cases i <;> simp [w]

/-- Pullback of the entire original double coefficient operation for normal
padding agrees with that operation on the unpadded record at mark two. -/
theorem mark_two_normal_double_coefficient_trace {n : ℕ}
    {U : Opens (ComplexModel n)} {I : GermIdeal n U} (hI : I.IsCoherent)
    (hP : (normalPaddingIdeal I 2).IsCoherent) :
    let L : MarkedIdeal n U := ⟨univ, [], I, 2⟩
    let M : MarkedIdeal (n+1) (productOpen U) := ⟨univ, [], normalPaddingIdeal I 2, 2⟩
    GermIdeal.pullback (m := n) (zeroSection U)
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))).ideal =
        (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong L))).ideal := by
  intro L M
  rw [mark_two_double_coefficient_ideal M hP rfl rfl,
    mark_two_double_coefficient_ideal L hI rfl rfl]
  have hD : (derivIdeal M.ideal).IsCoherent := isCoherent_iterDerivIdeal hP 1
  have hZ := zeroSection_contMDiff U
  rw [pullback_sumIdeal_dimensions hZ hP (isCoherent_idealPow hD 2),
    pullback_idealPow hZ hD]
  have h0 := entire_ambient_derivative_trace hI (d := 2) (j := 0) (by decide)
  have h1 := entire_ambient_derivative_trace hI (d := 2) (j := 1) (by decide)
  exact congrArg₂ sumIdeal h0 (congrArg (fun A => idealPow A 2) h1)


/-- The actual weighted record formed from one degree-two function and the
normal degree-one function has the exact double coefficient trace of its
degree-two base record. -/
theorem degree_two_native_padding_double_coefficient_trace {n : ℕ}
    (U : Opens (ComplexModel n)) (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) f) :
    let w : Unit → ℕ := fun _ => 2
    let c : Unit → U → ℂ := fun _ => f
    let L : MarkedIdeal n U := ⟨univ, [], finiteFunctionIdeal c, 2⟩
    let M := paddingMarked U w c []
    M.d = 2 ∧ GermIdeal.pullback (m := n) (zeroSection U)
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))).ideal =
        (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong L))).ideal := by
  intro w c L M
  have hw : weightedCommonMark w = 2 := by decide
  have hI : weightedFunctionIdeal (n := n) w c = finiteFunctionIdeal c := by
    unfold weightedFunctionIdeal
    rw [hw]
    simp [w]
  have hM : M = (⟨univ, [], normalPaddingIdeal L.ideal 2, 2⟩ :
      MarkedIdeal (n+1) (productOpen U)) := by
    change paddingMarked U w c [] = _
    rw [entire_padding_record U w c (fun _ => hf), hw, hI]
    rfl
  have hCoherent := isCoherent_weightedFunctionIdeal (n := n) w c (fun _ => hf)
  rw [hI] at hCoherent
  have hPad := isCoherent_weightedFunctionIdeal (n := n+1) (paddingWeight w)
    (paddingFunction U c) (by
      intro i
      cases i with
      | inl i => exact hf.comp ((projection_contMDiff U).mdifferentiable (by simp))
      | inr i => exact normalCoordinate_mdifferentiable U)
  change M.ideal.IsCoherent at hPad
  rw [hM] at hPad
  rw [hM]
  exact ⟨rfl, mark_two_normal_double_coefficient_trace hCoherent hPad⟩

end
end Hironaka.HironakaG8MarkTwoNormalCoefficientTrace
