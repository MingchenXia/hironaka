import Hironaka.Resolution.HironakaActualWeightedNormalPadding
import Hironaka.Resolution.HironakaActualSectionBoundaryGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionDerivativeEquality
import Hironaka.Blowup.BlowupDerivativeIdeal

/-! Entire ambient derivative traces of genuine weighted normal padding, only
at subcritical derivative orders. No canonical-history comparison is assumed.
Blueprint: hironaka-actual-weighted-normal-ambient-derivatives-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedNormalAmbientDerivatives
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient RestrictedIdealExtension
  DerivativeIdeal IdealOrderArithmetic IdealWeightPowers BlowupDerivativeIdeal
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualZeroCoordinateContactSeed
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionRelativeRestriction

private theorem derivIdeal_sum {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    derivIdeal (sumIdeal I J)=sumIdeal (derivIdeal I) (derivIdeal J) := by
  have hi := fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI (x := x) (g := g) hg
  have hj := fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ (x := x) (g := g) hg
  exact GermIdeal.ext (funext fun x => funext fun g => propext
    ⟨derivIdeal_sumIdeal_le hi hj x g,sumIdeal_le_derivIdeal_sumIdeal hi hj x g⟩)

/-- Entire ambient derivatives distribute over coherent ideal sums, at every order. -/
theorem iterDerivIdeal_sum {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    ∀ j,iterDerivIdeal (sumIdeal I J) j=sumIdeal (iterDerivIdeal I j) (iterDerivIdeal J j)
  | 0 => rfl
  | j+1 => by
    rw [iterDerivIdeal_succ,iterDerivIdeal_sum hI hJ j,
      derivIdeal_sum (isCoherent_iterDerivIdeal hI j) (isCoherent_iterDerivIdeal hJ j)]
    rfl

variable {n : ℕ}

private def normalIdeal (U : Opens (ComplexModel n)) : GermIdeal (n+1) (productOpen U) :=
  finiteFunctionIdeal (fun _ : Unit => relativeNormalCoordinate U)

private def normalPowerIdeal (U : Opens (ComplexModel n)) (d : ℕ) :
    GermIdeal (n+1) (productOpen U) :=
  finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z^d)

private theorem normal_holomorphic (U : Opens (ComplexModel n)) (z : productOpen U) :
    HolomorphicAt (n+1) (relativeNormalCoordinate U) z :=
  Eventually.of_forall fun y => normalCoordinate_mdifferentiable U y

private theorem normal_generator (U : Opens (ComplexModel n)) (z : productOpen U)
    (g : productOpen U → ℂ) :
    (normalIdeal U).mem z g ↔ IsInSpanAt (n := n+1) (· = relativeNormalCoordinate U) z g := by
  change IsInSpanAt (n := n+1) (· ∈ range (fun _ : Unit => relativeNormalCoordinate U)) z g ↔ _
  simp only [range_const,mem_singleton_iff]

private theorem normal_power_as_power (U : Opens (ComplexModel n)) (d : ℕ) :
    normalPowerIdeal U d=idealPow (normalIdeal U) d := by
  refine GermIdeal.ext (funext fun z => funext fun g => propext ?_)
  change IsInSpanAt (n := n+1) (· ∈ range
    (fun _ : Unit => fun z : productOpen U => relativeNormalCoordinate U z^d)) z g ↔ _
  simp only [range_const,mem_singleton_iff]
  exact (idealPow_mem_iff_of_generator (U := univ)
    (fun z _ => normal_holomorphic U z) (fun z _ g => normal_generator U z g)
    d z (mem_univ _) g).symm

private theorem normal_power_coherent (U : Opens (ComplexModel n)) (d : ℕ) :
    (normalPowerIdeal U d).IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun _ => (normalCoordinate_mdifferentiable U).pow d)

private theorem normal_section_zero (U : Opens (ComplexModel n)) (x : U) :
    relativeNormalCoordinate U (zeroSection U x)=0 := by
  change actualJointNormalProjection n 1 (tangentInclusion n 1 x.val) 0-0=0
  simp

/-- All subcritical ambient derivatives of the genuine normal power have zero
entire trace; the trace is contained in every coherent original ideal. -/
theorem normal_derivative_trace_le (U : Opens (ComplexModel n)) {I : GermIdeal n U}
    (hI : I.IsCoherent) {d j : ℕ} (hj : j<d) :
    (GermIdeal.pullback (m := n) (zeroSection U) (iterDerivIdeal (normalPowerIdeal U d) j)).Le I := by
  have hk : (normalIdeal U).IsCoherent :=
    isCoherent_finiteFunctionIdeal _ (fun _ => normalCoordinate_mdifferentiable U)
  have hle : (normalPowerIdeal U d).Le (idealPow (normalIdeal U) ((d-j)+j)) := by
    rw [Nat.sub_add_cancel (Nat.le_of_lt hj),←normal_power_as_power U d]
    exact fun _ _ hg => hg
  have hd := iterDerivIdeal_le_idealPow
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hk hg) j hle
  intro x g hg
  obtain ⟨hgh,K,s,a,hs,_ha,he⟩ := GermIdeal.mem_pullback_iff.mp hg
  have hz (i : Fin K) : s i =ᶠ[𝓝 x] 0 := by
    obtain ⟨b,hb,hsb⟩ := hs i
    have hp := hd (zeroSection U x) b hb
    have hspan := (idealPow_mem_iff_of_generator (U := univ)
      (fun z _ => normal_holomorphic U z) (fun z _ g => normal_generator U z g)
      (d-j) (zeroSection U x) (mem_univ _) b).mp hp
    obtain ⟨_hbhol,c,_hc,hbc⟩ := isInSpanAt_eq_iff.mp hspan
    have hevent := (zeroSection_contMDiff U).continuous.continuousAt.eventually hbc
    filter_upwards [hevent] with y hy
    rw [hsb]
    change b (zeroSection U y)=0
    rw [hy,normal_section_zero]
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hj)]
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine ⟨hgh,0,Fin.elim0,Fin.elim0,(fun i => i.elim0),(fun i => i.elim0),?_⟩
  filter_upwards [he,eventually_all.mpr hz] with y hy hy0
  rw [hy]
  simp only [Fin.sum_univ_zero]
  exact Finset.sum_eq_zero fun i _ => by simp only [hy0 i,Pi.zero_apply,mul_zero]

/-- The original coherent ideal extended by a genuine normal power on its actual product. -/
def normalPaddingIdeal {U : Opens (ComplexModel n)} (I : GermIdeal n U) (d : ℕ) :
    GermIdeal (n+1) (productOpen U) :=
  sumIdeal (GermIdeal.pullback (m := n+1) (projection U) I) (normalPowerIdeal U d)

/-- At every order below the original mark, the ENTIRE ambient derivative trace
is exactly the original ambient derivative ideal. -/
theorem entire_ambient_derivative_trace {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) {d j : ℕ} (hj : j<d) :
    GermIdeal.pullback (m := n) (zeroSection U) (iterDerivIdeal (normalPaddingIdeal I d) j)=
      iterDerivIdeal I j := by
  have hPI := isCoherent_pullback (projection_contMDiff U) hI
  have hN := normal_power_coherent U d
  have hDI := isCoherent_iterDerivIdeal hI j
  have hDN := isCoherent_iterDerivIdeal hN j
  have hproj := HironakaSmoothSubmersionDerivativeEquality.iterDerivIdeal_pullback_eq
    (fun y => (HironakaActualSectionBoundaryGeometry.projection_isSubmersion (U := U)).isSubmersionAt y)
    (fun y => (projection_contMDiff U).mdifferentiable (by simp) y)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) j
  have hsection : (projection U) ∘ (zeroSection U)=id := by
    funext x
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 x.val
  rw [normalPaddingIdeal,iterDerivIdeal_sum hPI hN j,hproj,
    pullback_sumIdeal_dimensions (zeroSection_contMDiff U)
      (isCoherent_pullback (projection_contMDiff U) hDI) hDN,
    ←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
      (iterDerivIdeal I j) hDI,hsection,BlowupControlledTransform.pullback_id hDI]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hDI
    exact IsInSpanAt.mono
      (fun b hb => hb.elim id (normal_derivative_trace_le U hDI hj x b))
      (mem_sumIdeal_iff.mp hg)
  · exact le_sumIdeal_left hDI x g

/-- The actual weighted family has exactly the same entire ambient derivative
trace below its SAME original common mark. -/
theorem weighted_padding_ambient_derivative_trace {ι : Type*} [Fintype ι]
    (U : Opens (ComplexModel n)) (w : ι → ℕ) (c : ι → U → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    {j : ℕ} (hj : j<HironakaActualWeightedCoefficientCompression.weightedCommonMark w) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (iterDerivIdeal (weightedFunctionIdeal (n := n+1) (paddingWeight w) (paddingFunction U c)) j)=
      iterDerivIdeal (weightedFunctionIdeal (n := n) w c) j := by
  rw [entire_padding_ideal U w c hc]
  exact entire_ambient_derivative_trace (isCoherent_weightedFunctionIdeal w c hc) hj

end
end Hironaka.HironakaActualWeightedNormalAmbientDerivatives
