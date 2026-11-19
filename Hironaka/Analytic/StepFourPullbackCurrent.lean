import Hironaka.Analytic.SubmanifoldCodRestrict
import Hironaka.Analytic.FormPullbackCompMixed
import Hironaka.Analytic.PolarBranchStepThree
import Hironaka.Analytic.StepFourOnStrictTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 4: the current `θ' + ddᶜφ'` on the strict transform

Source: Copy-4, `prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906`):

> the function `φ' := (π|_W)^* φ_{K,ℓ} + τ ψ_{E_rel}|_W` [...] Put
> `θ' := (π^*θ - ½δ₀ π^*ω)|_W`.  Since `(π|_W)^* K_ℓ ≥ δ₀ π^*ω|_W` by `eq:def-K-ell`,
> `θ' + ddᶜφ' = (π|_W)^* K_ℓ - ½δ₀ π^*ω|_W + τ([E_rel|_W] - Θ_{E_rel}|_W)
>   ≥ (½δ₀ - τ) π^*ω|_W + τ ω_Y|_W ≥ τ ω_Y|_W`.

This module proves that inequality, for an arbitrary potential `φ_K` on the submanifold `V`
with `θ|_V + ddᶜφ_K ≥ δ₀ ω|_V` (in Copy-4, `φ_{K,ℓ}` from `eq:def-K-ell`, which comes from the
quasi-equisingular approximation and stays an input), any holomorphic `π : Y → X`, any
metered divisor `E` and any closed complex submanifold `W ⊆ π⁻¹ V` of the same dimension:

* `thetaPlurisubharmonic_stepFourCurrent` — `φ' = φ_K ∘ π|_W + τ ψ_E|_W` is
  `(ι_W^*(π^*θ - δ π^*ω) - τ ι_W^*(π^*ω - Θ_E))`-psh whenever `0 < τ` and `δ + τ ≤ δ₀`
  (Copy-4: `δ = ½δ₀`, `τ < ½δ₀`).  With `ω_Y = π^*ω - Θ_E` Kähler this is the statement that
  `θ' + ddᶜφ' ≥ τ ω_Y|_W`.

Ingredients: `π|_W : W → V` is holomorphic (`SubmanifoldCodRestrict`), pullback of a `θ`-psh
function (`GlobalPotentialPullback.thetaPlurisubharmonic_comp`), the commutative square
`ι_V ∘ π|_W = π ∘ ι_W` for forms (`FormPullbackCompMixed`), `ψ_E` is `Θ_E`-psh
(`MeteredDivisorPositivity`), and the form arithmetic of Step 3 (`PolarBranchStepThree`).

* `locallyNondegenerate_stepFourCurrent` — on the strict transform `W` of `V`, `φ'` is finite
  somewhere in every open set (`π⁻¹ V \ Exc π` is dense in `W` and `π` is open off `Exc π`);
* `isKahlerCurrentPotential_stepFourCurrent` — for an exceptional metric `E` (`ω_Y = π^*ω - Θ_E`
  Kähler, support in `Exc π`) and `W` the strict transform: `φ'` is a Kähler-current potential of
  `θ' = (π^*θ - δ π^*ω)|_W`, with Kähler form `τ ω_Y|_W` (the inclusion `W → Y` is an immersion,
  `StepFourOnStrictTransform.fderiv_coordinateMap_val_injective`).  This is exactly the shape of
  the field `hφ'` of `PrincipalizationStepOneInterface.Copy4StepOneData`.

NOT here: the log singularities of `φ'` along `D|_W` (field `hlog`), and `φ_K` itself.
Sorry-free.
-/

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.StepFourPullbackCurrent

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.AnalyticGluingData SubmanifoldChartedSpace
  SubmanifoldCodRestrict FormPullbackCompMixed

noncomputable section

/-- **Pullback commutes with `a - ε b`**, coefficientwise on chart targets, for a holomorphic map
between manifolds of any dimensions. -/
theorem pullback_sub_smul_geometricallyEq {j n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel j) Z] [IsComplexManifold j Z] {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel j) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) (ε : ℝ) :
    (ClosedRealOneOneForm.pullback hf (a - ε • b)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hf a - ε • ClosedRealOneOneForm.pullback hf b).val := by
  intro e z hz
  have h1 := BlowupBigPullback.pullback_sub_geometricallyEq hf a (ε • b) e hz
  have h2 := BlowupPushforward.pullback_smul_geometricallyEq hf ε b e hz
  rw [h1, BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, h2]

/-- Geometric equality is compatible with `a - τ b`. -/
theorem geometricallyEq_sub_smul {j : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel j) Z] [IsComplexManifold j Z]
    {a a' b b' : ClosedRealOneOneForm j Z} (ha : a.val.GeometricallyEq a'.val)
    (hb : b.val.GeometricallyEq b'.val) (τ : ℝ) :
    (a - τ • b).val.GeometricallyEq (a' - τ • b').val := by
  intro e z hz
  rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_smul, ha e hz, hb e hz]

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Copy-4 Step 4, the current on `W`.**  Let `V ⊆ X` and `W ⊆ Y` be closed complex
submanifolds of dimension `k`, `π : Y → X` holomorphic with `π(W) ⊆ V`, `φ_K` a potential on `V`
with `θ|_V - δ₀ ω|_V + ddᶜφ_K ≥ 0`, `E` a metered divisor on `Y`, `0 < τ` and `δ + τ ≤ δ₀`.  Then
`φ' = φ_K ∘ π|_W + τ ψ_E|_W` satisfies
`ι_W^*(π^*θ - δ π^*ω) - τ ι_W^*(π^*ω - Θ_E) + ddᶜφ' ≥ 0` on `W`, i.e.
`θ' + ddᶜφ' ≥ τ ω_Y|_W` with `θ' = (π^*θ - δ π^*ω)|_W` and `ω_Y = π^*ω - Θ_E`. -/
theorem thetaPlurisubharmonic_stepFourCurrent (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {V : Set X} (hk : k ≤ n)
    (hV : ∀ x ∈ V, RegularAtDim (n := n) V x k) {δ₀ δ τ : ℝ} {φK : V → EReal}
    (hφK : letI := chartedSpace hk hV
      haveI := isComplexManifold_chartedSpace hk hV
      ThetaPlurisubharmonic
        (ClosedRealOneOneForm.pullback (contMDiff_val hk hV) (θ - δ₀ • omega.form)).val φK)
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (E : MeteredEffectiveQDivisor n Y) {W : Set Y}
    (hW : ∀ y ∈ W, RegularAtDim (n := n) W y k) (hWV : ∀ y ∈ W, π y ∈ V)
    (hτ : 0 < τ) (hδτ : δ + τ ≤ δ₀) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW)
          (ClosedRealOneOneForm.pullback hπ θ - δ • ClosedRealOneOneForm.pullback hπ omega.form)
        - τ • ClosedRealOneOneForm.pullback (contMDiff_val hk hW)
          (ClosedRealOneOneForm.pullback hπ omega.form - E.curvature)).val
      (fun w => φK ⟨π w.1, hWV w.1 w.2⟩ + (τ : EReal) * E.weight w.1) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have ιV := contMDiff_val hk hV
  have ιW := contMDiff_val hk hW
  have hres := contMDiff_restrictPreimage hk hV hk hW hπ hWV
  set A := ClosedRealOneOneForm.pullback ιW (ClosedRealOneOneForm.pullback hπ θ) with hA
  set Ω := ClosedRealOneOneForm.pullback ιW (ClosedRealOneOneForm.pullback hπ omega.form)
    with hΩ
  set T := ClosedRealOneOneForm.pullback ιW E.curvature with hT
  -- `φ_K ∘ π|_W` is `(A - δ₀ Ω)`-psh
  have h1 : ThetaPlurisubharmonic (A - δ₀ • Ω).val (fun w => φK ⟨π w.1, hWV w.1 w.2⟩) := by
    have hc := GlobalPotentialPullback.thetaPlurisubharmonic_comp hres hφK
    have hsq := pullback_pullback_geometricallyEq_of_comp_eq ιV hres hπ ιW
      (funext fun _ => rfl) (θ - δ₀ • omega.form).val
    have hπsub : (SmoothRealForm.pullback ιW
        (SmoothRealForm.pullback hπ (θ - δ₀ • omega.form).val)).GeometricallyEq
        (ClosedRealOneOneForm.pullback ιW (ClosedRealOneOneForm.pullback hπ θ -
          δ₀ • ClosedRealOneOneForm.pullback hπ omega.form)).val :=
      SmoothRealForm.GeometricallyEq.pullback ιW
        (pullback_sub_smul_geometricallyEq hπ θ omega.form δ₀)
    have hιsub := pullback_sub_smul_geometricallyEq ιW (ClosedRealOneOneForm.pullback hπ θ)
      (ClosedRealOneOneForm.pullback hπ omega.form) δ₀
    exact ((hsq.trans (hπsub.trans hιsub)).thetaPlurisubharmonic_iff _).mp hc
  -- `ψ_E|_W` is `T`-psh
  have h2 : ThetaPlurisubharmonic T.val (fun w : W => E.weight w.1) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp ιW
      (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
  have hsum := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos hτ h1 h2
  -- add the semipositive `(δ₀ - δ - τ) Ω`
  have hsemi : ((δ₀ - δ - τ) • Ω).val.IsSemipositive := by
    intro e z hz v
    rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith)
      (ClosedRealOneOneForm.pullback_isSemipositive ιW
        (ClosedRealOneOneForm.pullback_isSemipositive hπ omega.isSemipositive) e z hz v)
  have hall := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hsum hsemi
  -- the target form, geometrically
  have hgeom := geometricallyEq_sub_smul
    (pullback_sub_smul_geometricallyEq ιW (ClosedRealOneOneForm.pullback hπ θ)
      (ClosedRealOneOneForm.pullback hπ omega.form) δ)
    (BlowupBigPullback.pullback_sub_geometricallyEq ιW
      (ClosedRealOneOneForm.pullback hπ omega.form) E.curvature) τ
  refine (hgeom.thetaPlurisubharmonic_iff _).mpr ?_
  have hform : (1 : ℝ) • (A - δ₀ • Ω) + τ • T + (δ₀ - δ - τ) • Ω = A - δ • Ω - τ • (Ω - T) := by
    module
  have hfun : (fun p : W => ((1 : ℝ) : EReal) * φK ⟨π p.1, hWV p.1 p.2⟩
        + (τ : EReal) * E.weight p.1)
      = (fun w : W => φK ⟨π w.1, hWV w.1 w.2⟩ + (τ : EReal) * E.weight w.1) := by
    funext p
    rw [EReal.coe_one, one_mul]
  rw [← hform, ← hfun]
  exact hall

/-- **Local nondegeneracy of `φ' = φ_K ∘ π|_W + τ ψ`** on the strict transform `W` of `V`: if
`φ_K` is locally nondegenerate on `V` and `ψ` is finite off `Exc π`, then every open set of `W`
contains a point where `φ'` is finite.  Such an open set meets `π⁻¹ V \ Exc π` (dense in `W`),
off `Exc π` the map `π` sends neighbourhoods onto neighbourhoods, and `π⁻¹ V \ Exc π ⊆ W`. -/
theorem locallyNondegenerate_stepFourCurrent {V : Set X} {φK : V → EReal}
    (hφK : LocallyNondegenerate φK) {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {ψ : Y → EReal}
    (hψ : ∀ y, y ∉ BlowupSequences.exceptionalLocus n π → ψ y ≠ ⊥) {τ : ℝ} (hτ : 0 < τ)
    (hWV : ∀ y ∈ BlowupSequences.strictTransform n π V, π y ∈ V) :
    LocallyNondegenerate
      (fun w : BlowupSequences.strictTransform n π V =>
        φK ⟨π w.1, hWV w.1 w.2⟩ + (τ : EReal) * ψ w.1) := by
  intro w O hO hwO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.mp hO
  -- a point of `O'` on `π⁻¹ V \ Exc π`
  obtain ⟨z₀, hz₀O, hz₀V, hz₀E⟩ :
      (O' ∩ (π ⁻¹' V \ BlowupSequences.exceptionalLocus n π)).Nonempty :=
    mem_closure_iff.mp w.2 O' hO' hwO
  set N : Set Y := O' ∩ (BlowupSequences.exceptionalLocus n π)ᶜ with hNdef
  have hN : IsOpen N :=
    hO'.inter (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ)
  have himg : π '' N ∈ 𝓝 (π z₀) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hπ hz₀E]
    exact Filter.image_mem_map (hN.mem_nhds ⟨hz₀O, hz₀E⟩)
  -- `φ_K` is finite somewhere in the open set of `V` lying over `π '' N`
  obtain ⟨v, hvi, hv⟩ := hφK ⟨π z₀, hz₀V⟩ (Subtype.val ⁻¹' interior (π '' N))
    (isOpen_interior.preimage continuous_subtype_val)
    (mem_interior_iff_mem_nhds.mpr himg)
  obtain ⟨z, ⟨hzO, hzE⟩, hzv⟩ := interior_subset hvi
  have hzW : z ∈ BlowupSequences.strictTransform n π V :=
    subset_closure ⟨show π z ∈ V by rw [hzv]; exact v.2, hzE⟩
  refine ⟨⟨z, hzW⟩, hzO, EReal.add_ne_bot_iff.mpr ⟨?_, fun h => hψ z hzE ?_⟩⟩
  · have hpt : (⟨π z, hWV z hzW⟩ : V) = v := Subtype.ext hzv
    rw [hpt]
    exact hv
  · exact ThetaPshConvexCombination.eq_bot_of_coe_mul_eq_bot hτ h

/-- **Copy-4 Step 4: `θ' + ddᶜφ'` is a Kähler current on `W`.**  For the strict transform `W` of
`V` (a closed complex submanifold of dimension `k`, as is `V`), `φ_K` a potential on `V` with
`θ|_V - δ₀ ω|_V + ddᶜφ_K ≥ 0` and locally nondegenerate, an exceptional metric `E` (support in
`Exc π`, `ω_Y = π^*ω - Θ_E` Kähler), `0 < τ` and `δ + τ ≤ δ₀`:
`φ' = φ_K ∘ π|_W + τ ψ_E|_W` is a Kähler-current potential of `θ' = (π^*θ - δ π^*ω)|_W`, with
Kähler form `τ ω_Y|_W` (the inclusion `W → Y` is an immersion). -/
theorem isKahlerCurrentPotential_stepFourCurrent (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {V : Set X} (hk : k ≤ n)
    (hV : ∀ x ∈ V, RegularAtDim (n := n) V x k) {δ₀ δ τ : ℝ} {φK : V → EReal}
    (hφK : letI := chartedSpace hk hV
      haveI := isComplexManifold_chartedSpace hk hV
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback (contMDiff_val hk hV) (θ - δ₀ • omega.form)).val φK)
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (E : MeteredEffectiveQDivisor n Y)
    (hEexc : E.support ⊆ BlowupSequences.exceptionalLocus n π)
    (hEkahler : (ClosedRealOneOneForm.pullback hπ omega.form - E.curvature).val.IsKahler)
    (hW : ∀ y ∈ BlowupSequences.strictTransform n π V,
      RegularAtDim (n := n) (BlowupSequences.strictTransform n π V) y k)
    (hWV : ∀ y ∈ BlowupSequences.strictTransform n π V, π y ∈ V)
    (hτ : 0 < τ) (hδτ : δ + τ ≤ δ₀) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    IsKahlerCurrentPotential
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW)
        (ClosedRealOneOneForm.pullback hπ θ - δ • ClosedRealOneOneForm.pullback hπ omega.form))
      (fun w => φK ⟨π w.1, hWV w.1 w.2⟩ + (τ : EReal) * E.weight w.1) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hKW : (ClosedRealOneOneForm.pullback (contMDiff_val hk hW)
      (ClosedRealOneOneForm.pullback hπ omega.form - E.curvature)).val.IsKahler :=
    SmoothRealForm.IsKahler.pullback_of_injective (contMDiff_val hk hW)
      (StepFourOnStrictTransform.fderiv_coordinateMap_val_injective hk hW) hEkahler
  refine ⟨KahlerBackground.smul hτ ⟨_, hKW⟩, ?_, ?_⟩
  · rw [KahlerBackground.smul_form]
    exact thetaPlurisubharmonic_stepFourCurrent omega θ hk hV hφK.1 hπ E hW hWV hτ hδτ
  · exact locallyNondegenerate_stepFourCurrent hφK.2 hπ
      (fun y hy hbot => hy (hEexc (show y ∈ E.support from hbot))) hτ hWV

end

end Hironaka.StepFourPullbackCurrent
