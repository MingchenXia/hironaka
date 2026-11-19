import Hironaka.Analytic.StepFiveAssemblyOfStepOneCurrent
import Hironaka.Analytic.StrictTransformLocus
import Hironaka.Resolution.StrictTransformSubvarietySequence
import Hironaka.Blowup.ExceptionalImageAnalytic
import Hironaka.Blowup.BlowupSequenceIsomorphismOff

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The point `y` of Copy-4 Step 6

Source: Copy-4, `prop:principalization`, Steps 5--6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1908-1992`):

> [Step 5] `χ` is smooth on the open set `π⁻¹(X \ (Z' ∪ Z(𝔅_m)))`.  This open set meets
> `W`, since its complement on `V`, together with the locus over which `π` is not an
> isomorphism, is a proper analytic subset of `V`.  Hence `χ` is smooth on a neighborhood
> of some point of `W`.  [...]
> [Step 6] Since no component of `D` contains `W`, the set `Supp D ∩ W` is a proper analytic
> subset of `W`; as `χ` is smooth near some point of `W`, we may choose `y ∈ W` outside
> `Supp D` near which `χ` is smooth.

`StepFiveAssemblyOfStepOneCurrent.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent`
takes that point `y` as six hypotheses (`y ∈ W`, `y` off `Supp G̃_M`, `Supp P^mov`, `Supp P^F`,
off `Exc π`, and `Ψ` smooth near `π y`).  This module derives all six, for `W` the strict
transform of `V`, from

* a point `x₀ ∈ V` near which `Ψ` is smooth (what
  `IdealFunctionMaxGluing.exists_idealFunction` produces for `x₀ ∉ Z(𝔧 𝔅_m)`), and
* the hypothesis "no component of `D` contains `W`" that the assembly already carries.

## The argument

* `exists_mem_inter_notMem_image_exceptionalLocus` — for a blowup sequence `f` of a compact
  manifold and an irreducible `V ⊄ f(Exc f)`, every open set meeting `V` meets
  `V \ f(Exc f)`.  Copy-4 reads this off from `f(Exc f) ∩ V` being a proper analytic subset
  of `V`; analyticity of `f(Exc f)` for a *sequence* is a proper-mapping statement, so we
  argue by induction on the sequence instead: for one blowup `g` the exceptional image is
  analytic (`ExceptionalImageAnalytic`) and the identity principle for irreducible
  subvarieties (`StrictTransformLocus.subset_of_inter_isOpen_subset`) applies to the strict
  transform, which is irreducible (`StrictTransformSubvarietySequence`); the earlier stages
  are crossed over their isomorphism locus, where fibres are points.  No Remmert.
* `exists_mem_strictTransform_notMem_exceptionalLocus` — hence some `y ∈ W \ Exc π` has
  `π y` in any prescribed open set meeting `V`.
* `notMem_support_of_copy4Divisor_weight_ne_bot` — the coefficients of `eq:def-DLY` are
  positive, so a point where `ψ_D` is finite lies off `Supp G̃_M`, `Supp P^mov`, `Supp P^F`.
* `exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent_strictTransform` — the Step-5
  assembly with the point `y` derived.

Everything in this file is proved; the composite theorem inherits exactly the roots of
`StepFiveAssemblyOfStepOneCurrent` (`lem:residual-nef`'s two named inputs).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepSixGenericPoint

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NonKahlerLocus Hironaka.BlowupSequences Hironaka.NumericalRestrictedVolumeScaffold
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction MeteredDivisorScaling ResidualNefReduction
  ManifoldTubePositivity TubePositivityOneFlattening

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-! ### Off the exceptional image, on every open part of `V` -/

/-- **Every open set meeting `V` meets `V \ f(Exc f)`**, for a blowup sequence `f` of a
compact manifold and an irreducible subvariety `V ⊄ f(Exc f)`.  Induction on the sequence;
see the module docstring. -/
theorem exists_mem_inter_notMem_image_exceptionalLocus [CompactSpace X] {f : Y → X}
    (hf : IsBlowupSequence n X Y f) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : ¬ V.carrier ⊆ f '' exceptionalLocus n f) {O : Set X} (hO : IsOpen O)
    (hVO : (V.carrier ∩ O).Nonempty) :
    ∃ x ∈ V.carrier ∩ O, x ∉ f '' exceptionalLocus n f := by
  induction hf with
  | refl =>
      obtain ⟨x, hx⟩ := hVO
      exact ⟨x, hx, by simp⟩
  | step f C g hfs hg ih =>
      obtain ⟨hcompact, hsurjf⟩ :=
        StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hfs
      have := hcompact
      have hsurjg := StrictTransformComposition.surjective_of_isBlowupAlong hg
      have hfd : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f :=
        hfs.contMDiff.mdifferentiable (by simp)
      have hgd : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g :=
        hg.contMDiff.mdifferentiable (by simp)
      have hVf : ¬ V.carrier ⊆ f '' exceptionalLocus n f := fun h =>
        hV (h.trans (StrictTransformComposition.image_exceptionalLocus_subset_comp hfd hgd
          hsurjg))
      -- a point of `V ∩ O` over which `f` is an isomorphism, and its preimage `y₁`
      obtain ⟨x₁, ⟨hx₁V, hx₁O⟩, hx₁E⟩ := ih hVf
      obtain ⟨y₁, rfl⟩ := hsurjf x₁
      have hy₁exc : y₁ ∉ exceptionalLocus n f := fun h => hx₁E ⟨y₁, h, rfl⟩
      -- the strict transform `W` of `V` under `f` is irreducible and not `g`-exceptional
      obtain ⟨W, hWc, -⟩ :=
        StrictTransformSubvarietySequence.exists_strictTransform_subvariety_of_isBlowupSequence
          hfs V hVf
      have hWg : ¬ W.carrier ⊆ g '' exceptionalLocus n g := by
        rw [hWc]
        exact StrictTransformComposition.not_strictTransform_subset_image_exceptionalLocus
          hfs.contMDiff hg.contMDiff hsurjf hsurjg hV
      -- the open set `f⁻¹ O \ Exc f` meets `W` at `y₁`
      set O₁ := f ⁻¹' O ∩ (exceptionalLocus n f)ᶜ with hO₁
      have hO₁open : IsOpen O₁ :=
        (hO.preimage hfs.contMDiff.continuous).inter
          (StrictTransformComposition.isOpen_compl_exceptionalLocus hfs.contMDiff)
      have hy₁W : y₁ ∈ W.carrier := by
        rw [hWc]
        exact subset_closure ⟨hx₁V, hy₁exc⟩
      -- one blowup: `g(Exc g)` is analytic, so `W ∩ O₁ ⊄ g(Exc g)`
      have hA : IsComplexAnalyticSubset (n := n) (g '' exceptionalLocus n g) :=
        ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg
      have hWO₁ : ¬ W.carrier ∩ O₁ ⊆ g '' exceptionalLocus n g := fun h =>
        hWg (StrictTransformLocus.subset_of_inter_isOpen_subset W hA hO₁open
          ⟨y₁, hy₁W, hx₁O, hy₁exc⟩ h)
      obtain ⟨y₂, ⟨hy₂W, hy₂O, hy₂exc⟩, hy₂E⟩ := not_subset.mp hWO₁
      -- its image is the required point
      have hWsub : W.carrier ⊆ f ⁻¹' V.carrier := by
        rw [hWc, strictTransform]
        exact closure_minimal sdiff_subset (V.isClosed_carrier.preimage hfs.contMDiff.continuous)
      refine ⟨f y₂, ⟨hWsub hy₂W, hy₂O⟩, ?_⟩
      rintro ⟨z, hz, hfz⟩
      have hgz : g z = y₂ :=
        BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus hfs hy₂exc hfz
      rw [exceptionalLocus_comp hfd hgd] at hz
      rcases hz with hz | hz
      · exact hy₂E ⟨z, hz, hgz⟩
      · exact hy₂exc (hgz ▸ hz)

/-- A nonempty strict transform is not contained in the exceptional image. -/
theorem not_subset_image_exceptionalLocus_of_strictTransform_nonempty [CompactSpace X]
    {f : Y → X} (hf : IsBlowupSequence n X Y f) {V : Set X}
    (hne : (strictTransform n f V).Nonempty) :
    ¬ V ⊆ f '' exceptionalLocus n f := by
  have hraw : (f ⁻¹' V \ exceptionalLocus n f).Nonempty := by
    by_contra hraw
    rw [not_nonempty_iff_eq_empty] at hraw
    obtain ⟨y, hy⟩ := hne
    rw [strictTransform, hraw, closure_empty] at hy
    exact hy
  obtain ⟨y, hyV, hyexc⟩ := hraw
  intro hsub
  obtain ⟨z, hz, hfz⟩ := hsub hyV
  have hzy : z = y :=
    BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus hf hyexc hfz
  exact hyexc (hzy ▸ hz)

/-- **Copy-4 Step 5, "this open set meets `W`"**: for every open `O` meeting `V`, some point
of the strict transform `W` off `Exc π` lies over `O`. -/
theorem exists_mem_strictTransform_notMem_exceptionalLocus [CompactSpace X] {f : Y → X}
    (hf : IsBlowupSequence n X Y f) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hne : (strictTransform n f V.carrier).Nonempty) {O : Set X} (hO : IsOpen O)
    (hVO : (V.carrier ∩ O).Nonempty) :
    ∃ y ∈ strictTransform n f V.carrier, y ∉ exceptionalLocus n f ∧ f y ∈ O := by
  obtain ⟨-, hsurj⟩ := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf
  obtain ⟨x, ⟨hxV, hxO⟩, hxE⟩ := exists_mem_inter_notMem_image_exceptionalLocus hf V
    (not_subset_image_exceptionalLocus_of_strictTransform_nonempty hf hne) hO hVO
  obtain ⟨y, rfl⟩ := hsurj x
  have hyexc : y ∉ exceptionalLocus n f := fun h => hxE ⟨y, h, rfl⟩
  exact ⟨y, subset_closure ⟨hxV, hyexc⟩, hyexc, hxO⟩

/-! ### Off the supports of `D` -/

/-- Where a positive multiple of `ψ_E` is finite, the point lies off `Supp E`. -/
theorem notMem_support_of_smul_weight_ne_bot {c : ℚ} (hc : 0 < c)
    {E : MeteredEffectiveQDivisor n Y} {y : Y}
    (h : ((c : ℝ) : EReal) * E.weight y ≠ ⊥) : y ∉ E.support := by
  intro hy
  have hy' : E.weight y = ⊥ := hy
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  exact h (by rw [hy', EReal.coe_mul_bot_of_pos hcR])

/-- **The coefficients of `eq:def-DLY` are positive**: where `ψ_D` is finite, the point lies
off `Supp G̃_M`, `Supp P^mov` and `Supp P^F`. -/
theorem notMem_support_of_copy4Divisor_weight_ne_bot {levQ CQ τQ : ℚ} (hlev : 0 < levQ)
    (hC : 1 < CQ) (hτ : 0 ≤ τQ) (EGM EPmov EPF E : MeteredEffectiveQDivisor n Y) {y : Y}
    (hy : (copy4Divisor hlev hC.le hτ EGM EPmov EPF E).weight y ≠ ⊥) :
    y ∉ EGM.support ∧ y ∉ EPmov.support ∧ y ∉ EPF.support := by
  have hw := hy
  simp only [copy4Divisor, weight_qcomb4, ne_eq, EReal.add_eq_bot_iff, not_or] at hw
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, -⟩ := hw
  exact ⟨notMem_support_of_smul_weight_ne_bot (one_div_pos.mpr hlev) h₁,
    notMem_support_of_smul_weight_ne_bot (div_pos (sub_pos.mpr hC) hlev) h₂,
    notMem_support_of_smul_weight_ne_bot (div_pos (zero_lt_one.trans hC) hlev) h₃⟩

/-! ### The Step-5 assembly with the point derived -/

/-- **Copy-4 Steps 3--6 from Step 1 and the Step-4 current, with the point `y` derived.**
`StepFiveAssemblyOfStepOneCurrent.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent`
for `W` the strict transform of `V`, with its six hypotheses on `y` replaced by a point
`x₀ ∈ V` near which `Ψ` is smooth.  The point `y` is produced inside, from "no component of
`D` contains `W`" (`hnd`), as in Copy-4 Step 6. -/
theorem exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent_strictTransform
    [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k)
    -- Step 3: the exceptional metric
    (E : MeteredEffectiveQDivisor n Y) (hEexc : E.support ⊆ exceptionalLocus n π)
    (hEkahler :
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler)
    -- `sec:fixed-data`: `R = θ + ddᶜΦ_R ≥ δ_R ω` and `eq:PhiR-lower`
    {PhiR : X → EReal} {δR : ℝ}
    (hPhiR : IsThetaPshPotential (θ - δR • omega.form).val PhiR)
    {psiIV psij : X → EReal} {idealIV 𝔧 : GermIdeal n X}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV 1 idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij 1 𝔧)
    {A : ℝ} (hA : 0 ≤ A) (hPhiRsrc : AmbientPhiRLowerSource n X A PhiR psiIV psij)
    -- `eq:def-TM`: `lem:regularization` at the level `M`
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {levQ : ℚ} {UM psiBM : X → EReal} {𝔅M : GermIdeal n X}
    (hpsiBM : HasAnalyticSingularitiesOfType (n := n) psiBM 1 𝔅M)
    (hUM : IsThetaPshPotential (θ + (c₀ / (levQ : ℝ)) • omega.form).val UM)
    (hUMlower : MoreSingularOn (fun x => ((1 / (levQ : ℝ) : ℝ) : EReal) * psiBM x) UM univ)
    -- `eq:def-Psi`: the ideal function of `𝔧 𝔅_m`
    {Ψ psib : X → EReal} {𝔟 : GermIdeal n X} {cΨ δ : ℝ}
    (hΨpsh : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ)
    (hΨtype : HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟))
    (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    -- the constants
    (hlev : 0 < levQ) {L : ℝ} {CQ τQ : ℚ} (hL : 0 < L) (hLlev : L < (levQ : ℝ))
    (hconst : c₀ < L * δR)
    (hC : 1 < CQ) (hCA : L * A ≤ (CQ : ℝ) - 1)
    (hκδ : ((CQ : ℝ) - 1) / (levQ : ℝ) * cΨ ≤ δ)
    (hτ : 0 < τQ) (hτε : (τQ : ℝ) ≤ (L * δR - c₀) / (levQ : ℝ))
    -- Step 1, as weights
    (EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y)
    (hGM : HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
      (GermIdeal.pullback (m := n) π 𝔅M))
    {idealH : GermIdeal n Y}
    (hH : HasAnalyticSingularitiesOfType (n := n)
      (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1 idealH)
    (hfact : GermIdeal.pullback (m := n) π idealIV =
      idealH.mul (vanishingIdeal (n := n) (strictTransform n π V.carrier)))
    (hHfix : MoreSingularOn (fun y => psib (π y)) EHfix.weight univ)
    -- a point of `V` near which `Ψ` is smooth (Copy-4 Step 5)
    {x₀ : X} (hx₀V : x₀ ∈ V.carrier) (hΨx₀ : IsSmoothNear (n := n) Ψ x₀)
    -- Step 4's current on `W`, with its complex structure from the flattenings
    : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      ∀ (hnd : ∀ O : Set (strictTransform n π V.carrier), IsOpen O → O.Nonempty →
          ∃ p ∈ O, (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight (p : Y) ≠ ⊥)
        {φ' : strictTransform n π V.carrier → EReal},
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
          (ClosedRealOneOneForm.pullback hπ.contMDiff θ
            - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form)) φ' →
        HasLogSingularitiesAlong
          (restrictAlong k (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
            (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E) hnd) φ' →
        ∃ φG : Y → EReal,
          IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
          Nonempty (Copy4StepFiveExceptionalWeightData
            (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
            (strictTransform n π V.carrier) φG) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  intro hnd φ' hφ' hlog
  -- the smooth neighbourhood of `x₀`, and a point of `W \ Exc π` over it
  obtain ⟨U, hU, hx₀U, h, hh, hΨU⟩ := hΨx₀
  obtain ⟨y₁, hy₁W, hy₁exc, hy₁U⟩ :=
    exists_mem_strictTransform_notMem_exceptionalLocus hπ V hW.2.1.nonempty hU
      ⟨x₀, hx₀V, hx₀U⟩
  -- the open part of `W` over `U` and off `Exc π`, and a point of it off `Supp D`
  set O : Set (strictTransform n π V.carrier) :=
    Subtype.val ⁻¹' (π ⁻¹' U ∩ (exceptionalLocus n π)ᶜ) with hOdef
  have hOopen : IsOpen O :=
    ((hU.preimage hπ.contMDiff.continuous).inter
      (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.contMDiff)).preimage
      continuous_subtype_val
  obtain ⟨p, ⟨hpU, hpexc⟩, hpD⟩ := hnd O hOopen ⟨⟨y₁, hy₁W⟩, hy₁U, hy₁exc⟩
  obtain ⟨hpGM, hpPmov, hpPF⟩ :=
    notMem_support_of_copy4Divisor_weight_ne_bot hlev hC hτ.le EGM EPmov EPF E hpD
  exact StepFiveAssemblyOfStepOneCurrent.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent
    omega θ hπ hW E hEexc hEkahler hPhiR hIV hj hA hPhiRsrc hc₀ hpsiBM hUM hUMlower hΨpsh
    hΨtype hb hlev hL hLlev hconst hC hCA hκδ hτ hτε EGM EHfix EPmov EPF hGM hH hfact hHfix
    p.2 hpGM hpPmov hpPF hpexc ⟨U, hU, hpU, h, hh, hΨU⟩ hnd hφ' hlog

end

end Hironaka.StepSixGenericPoint
