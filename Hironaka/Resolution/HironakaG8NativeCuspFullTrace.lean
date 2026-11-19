import Hironaka.Resolution.HironakaG8MarkTwoNormalCoefficientTrace
import Hironaka.Resolution.HironakaG8CuspDerivativeTrace

/-! The whole cleared coefficient ideal of the embedded cusp, evaluated on
the two fixed coordinate sections. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff ENat

namespace Hironaka.HironakaG8NativeCuspFullTrace
noncomputable section

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedIdealAlong GermIdealOrder
  HironakaActualWeightedNormalPadding HironakaActualOpenZeroSectionDifferentials
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaG8MarkTwoNormalCoefficientTrace HironakaG8CuspDerivativeTrace
  HironakaActualFiniteCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  GermIdealPullbackCalculus MarkedIdealBiholomorphism Hironaka.BlowupSequences HomogenizedGlueingTower

private abbrev U : Opens (ComplexModel 2) := ⊤
private def wholeOpen (x : ComplexModel 2) : U := ⟨x, trivial⟩
private theorem wholeOpen_smooth :
    ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞ wholeOpen := by
  exact (ContMDiff.subtypeVal_comp_iff U wholeOpen).mp contMDiff_id

private def weightTwo : Unit → ℕ := fun _ => 2
private def baseFunction (p : ℕ) : Unit → U → ℂ := fun _ z => cuspFunction p z.val

/-- The literal weighted embedded record on the product of the whole base
open with its normal line. -/
def nativeWeightedCusp (p : ℕ) : MarkedIdeal 3 (productOpen U) :=
  paddingMarked U weightTwo (baseFunction p) []

/-- On the ordinary cusp line following the normal section, the exact full
double coefficient order of the native weighted embedded record is p. -/
theorem native_weighted_cusp_double_coefficient_order (p : ℕ) (hp : 2 ≤ p) :
    order 2 {z : ComplexModel 2 | z.ofLp 1 = 0}
      (GermIdeal.pullback (m := 2) (zeroSection U ∘ wholeOpen)
        (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong (nativeWeightedCusp p)))).ideal)
      0 = (p : ℕ∞) := by
  let c : Unit → ComplexModel 2 → ℂ := fun _ => cuspFunction p
  let L : MarkedIdeal 2 (ComplexModel 2) := ⟨univ, [], cuspIdeal p, 2⟩
  let M := nativeWeightedCusp p
  let D := coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))
  have hDiff : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ℂ) (c i) :=
    fun _ => (((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiable.pow p)).mdifferentiable
  have hVal : ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞
      (Subtype.val : U → ComplexModel 2) := contMDiff_subtype_val
  have hBaseDiff : ∀ i, MDifferentiable 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ℂ) (baseFunction p i) :=
    fun i => (hDiff i).comp (hVal.mdifferentiable (by simp))
  have hCusp : finiteFunctionIdeal (n := 2) c = L.ideal := by
    apply GermIdeal.ext
    funext x g
    apply propext
    change IsInSpanAt (fun f => ∃ i, c i = f) x g ↔ IsInSpanAt (· = cuspFunction p) x g
    exact ⟨fun h => h.mono (fun f hf => by obtain ⟨i, hi⟩ := hf; exact hi.symm),
      fun h => h.mono (fun f hf => ⟨(), hf.symm⟩)⟩
  have hL : MarkedIdeal.pullback (Subtype.val : U → ComplexModel 2) L =
      (⟨univ, [], finiteFunctionIdeal (baseFunction p), 2⟩ : MarkedIdeal 2 U) := by
    have h := finiteFunctionIdeal_pullback c hDiff (Subtype.val : U → ComplexModel 2)
      contMDiff_subtype_val
    rw [hCusp] at h
    simp [MarkedIdeal.pullback, L, h, c, Function.comp_def]
    rfl
  have hM : M.ideal.IsCoherent := isCoherent_weightedFunctionIdeal
    (paddingWeight weightTwo) (paddingFunction U (baseFunction p)) (by
      intro i
      cases i with
      | inl i => exact (hBaseDiff i).comp ((projection_contMDiff U).mdifferentiable (by simp))
      | inr i => exact normalCoordinate_mdifferentiable U)
  have hSub : IsClosedSubmanifold 3 M.N := isClosedSubmanifold_univ
  have hD : D.ideal.IsCoherent := isCoherent_coeffMarkedAlong
    (isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hM hSub) hSub) hSub
  have hTrace := (degree_two_native_padding_double_coefficient_trace U
      (baseFunction p ()) (hBaseDiff ())).2
  change GermIdeal.pullback (m := 2) (zeroSection U) D.ideal = _ at hTrace
  rw [← hL] at hTrace
  have hLC : L.ideal.IsCoherent := cuspIdeal_coherent p
  have hN : IsClosedSubmanifold 2 L.N := isClosedSubmanifold_univ
  have hH := isCoherent_homMarkedAlong hLC hN
  have hB := isCoherent_coeffMarkedAlong hH hN
  rw [← pullback_val_homMarkedAlong U L hLC hN (show 1 ≤ 2 by decide),
    ← pullback_val_coeffMarkedAlong U _ hH hN (show 1 ≤ 2 by decide),
    ← pullback_val_coeffMarkedAlong U _ hB hN (show 1 ≤ 2 by decide)] at hTrace
  have hComp : (Subtype.val : U → ComplexModel 2) ∘ wholeOpen = id := rfl
  change order 2 _ (GermIdeal.pullback (m := 2) (zeroSection U ∘ wholeOpen) D.ideal) 0 = _
  rw [coherent_pullback_comp (zeroSection_contMDiff U) wholeOpen_smooth _ hD, hTrace]
  change order 2 _ (GermIdeal.pullback (m := 2) wholeOpen
    (GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2)
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong L))).ideal)) 0 = _
  rw [← coherent_pullback_comp contMDiff_subtype_val wholeOpen_smooth _
    (isCoherent_coeffMarkedAlong hB hN), hComp,
    BlowupControlledTransform.pullback_id (isCoherent_coeffMarkedAlong hB hN)]
  exact cusp_double_coefficient_trace_order p hp

end
end Hironaka.HironakaG8NativeCuspFullTrace
