import Hironaka.Analytic.PrincipalizationStepOneStages

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 1: the three-stage modification, from relative principalization

Source: Copy-4, `sec:fixed-principalization` and `prop:principalization`, Steps 1--2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1597-1622,
1774-1846`); blueprint `ana:copy4-steps-one-to-five`.

Copy-4 builds the modification of `prop:principalization` in three stages
`Y → Y₁ → Y_fix → X`, each an application of `lem:relative-principalization`
(`PrincipalizationStepOneStages.exists_principalizationStage`):

1. `π_fix : Y_fix → X` principalizes `𝔅_m` along `V`:
   `𝔅_m 𝒪_{Y_fix} = 𝒪(-G̃_m)`, `G̃_m = H^fix_m + H'` with `H'` disjoint from `W_m`
   (`eq:def-Gm-tilde`, clauses (i)--(ii));
2. `𝔅_M ⊆ 𝔅_m^{M/m}` gives `𝔅_M 𝒪_{Y_fix} = 𝒪(-(M/m) G̃_m) · 𝔠_M` with `𝔠_M` coherent
   (`eq:def-cM`), `𝔠_M ⊄ 𝓘_{W_m}` because `V ⊄ Z(𝔅_M)`, and `Y₁ → Y_fix` principalizes
   `𝔠_M` along `W_m`: `𝔠_M 𝒪_{Y₁} = 𝒪(-P^mov - P')` with `P'` disjoint from `W₁`;
3. `Y → Y₁` principalizes a further coherent ideal `𝔣 ⊄ 𝓘_{W₁}` along `W₁`:
   `𝔣 𝒪_Y = 𝒪(-P^F - P^F')` with `P^F'` disjoint from `W` (in Copy-4 `𝔣 = 𝔣̃_B`, built from
   the QEA ideal `𝔅`; here it is a parameter).

Step 2 (`eq:IV-H`) composes clause (i) along the stages:
`𝓘_V 𝒪_Y = 𝒪(-(H^fix_m + P^mov + P^F)) · 𝓘_W`.

All identities are kept AMBIENT, with the remainders `H'`, `P'`, `P^F'` disjoint from the strict
transform: on `W` they say `G_m = H^fix_m|_W`, `G_M = (M/m) G_m + P^mov|_W`
(`eq:Pmov-restriction`) and `div(𝔣 𝒪_W) = P^F|_W` (`eq:PF-restriction`), which is what Step 4
needs, without restricting divisors.

## Main results

* `exists_firstTwoStages` — stages 1--2 from `hRP`, for coherent `𝔅_m`, `𝔅_M` on `X` with
  `𝔅_M ⊆ 𝔅_m^q` and `V ⊄ Z(𝔅_m)`, `V ⊄ Z(𝔅_M)`;
* `exists_thirdStage` — stage 3 on top of any model carrying the output of stages 1--2;
* `stepOneFields` — the Step-1 fields of
  `PrincipalizationStepOneInterface.Copy4StepOneData` (`G̃_M`, `H^fix`, `P^mov`, `P^F` with
  `hGMideal`, `hBm`, `hfact` for `idealIV = 𝓘_V`, `hPmovexc`, `hPFexc`), from the same output.

Everything here is sorry-free and independent of the quasi-equisingular approximation; the
Hironaka content stays in the hypothesis `hRP` (I-0484).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PrincipalizationStepOneAssembly

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  PrincipalizationStepOneInterface PrincipalizationStepOneStages GermIdealTotalTransform
  BlowupSequenceTotalTransform GermIdealPullbackCalculus InvertibleIdealQuotient
  IdealWeightPowers RelativePrincipalizationSpan StepFourNoComponentContainsW

noncomputable section

/-! ### Ideal bookkeeping -/

section Ideals

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The unit ideal is invertible, with generator `1`. -/
theorem isInvertible_unitIdeal : (unitIdeal n M).IsInvertible := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, (1 : M → ℂ),
    (mdifferentiable_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ))
      (c := (1 : ℂ))).mdifferentiableOn,
    fun W _ _ hW => ?_, fun y _ g => ?_⟩
  · obtain ⟨y, hy⟩ := hW
    exact ⟨y, hy, by simp⟩
  · rw [mem_unitIdeal_iff]
    constructor
    · exact IsInSpanAt.mono fun s ⟨i, hi⟩ => hi.symm
    · exact IsInSpanAt.mono fun s hs => ⟨0, hs.symm⟩

/-- Powers of an invertible ideal are invertible. -/
theorem isInvertible_idealPow {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsInvertible) :
    ∀ q : ℕ, (idealPow 𝔞 q).IsInvertible
  | 0 => isInvertible_unitIdeal
  | q + 1 => isInvertible_mul (isInvertible_idealPow h𝔞 q) h𝔞

/-- **`W ⊄ Z(𝔞)` forces `𝔞 ⊄ 𝓘_W`**: a germ of `𝓘_W` at a point of `W` vanishes there. -/
theorem not_le_vanishingIdeal_of_not_subset_zeroLocus {𝔞 : GermIdeal n M} {W : Set M}
    (h : ¬ W ⊆ 𝔞.zeroLocus) : ¬ 𝔞.Le (vanishingIdeal (n := n) W) := by
  intro hle
  apply h
  intro x hx g hg
  exact (hle x g hg).2.self_of_nhds hx

/-- A closed connected submanifold of dimension `k < n` is a proper subset. -/
theorem ne_univ_of_isClosedConnectedSubmanifold {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (hk : k < n) : W ≠ univ := by
  intro hWu
  obtain ⟨x, hx⟩ := hW.2.1.nonempty
  have hreg := hW.2.2 x hx
  rw [hWu] at hreg
  exact (ne_of_lt hk) (AnalyticIrreducibleComponents.eq_of_regularAtDim_univ hreg)

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The pullback of the unit ideal is the unit ideal. -/
theorem pullback_unitIdeal {f : Y → M} :
    GermIdeal.pullback (m := n) f (unitIdeal n M) = unitIdeal n Y := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => hg.1, fun hg => ?_⟩)
  exact isInSpanAt_of_eq_mul (S := fun s => ∃ a, (unitIdeal n M).mem (f y) a ∧ s = a ∘ f)
    (s := fun _ => (1 : ℂ)) (a := g)
    ⟨fun _ => (1 : ℂ), holomorphicAt_const 1, rfl⟩ hg hg (Eventually.of_forall fun _ => by simp)

/-- **The pullback of a power is the power of the pullback**, for a coherent ideal. -/
theorem pullback_idealPow {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    ∀ q : ℕ, GermIdeal.pullback (m := n) f (idealPow 𝔞 q) =
      idealPow (GermIdeal.pullback (m := n) f 𝔞) q
  | 0 => pullback_unitIdeal
  | q + 1 => by
      rw [idealPow_succ, idealPow_succ, pullback_mul hf (isCoherent_idealPow h𝔞 q) h𝔞,
        pullback_idealPow hf h𝔞 q]

/-- The ideal of an effective divisor is coherent. -/
theorem isCoherent_ideal (D : EffectiveDivisor n M) : D.ideal.IsCoherent :=
  DivisorMetric.isCoherent_of_isInvertible D.isInvertible

end Ideals

/-! ### Strict transforms and total transforms -/

section Transforms

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The strict transform of a closed set lies in its preimage. -/
theorem strictTransform_subset_preimage {f : Y → X} (hf : Continuous f) {A : Set X}
    (hA : IsClosed A) : strictTransform n f A ⊆ f ⁻¹' A :=
  closure_minimal sdiff_subset (hA.preimage hf)

/-- **Disjointness from the strict transform survives a further stage**: if `D` is disjoint
from the strict transform `W` of `V` under `π`, its total transform under `g` is disjoint from
the strict transform of `V` under `π ∘ g`. -/
theorem disjoint_totalTransform_strictTransform {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) {V : Set X} {D : EffectiveDivisor n Y}
    (hD : Disjoint D.support (strictTransform n π V)) :
    Disjoint (EffectiveDivisor.totalTransform hg hint D).support
      (strictTransform n (π ∘ g) V) := by
  rw [support_totalTransform hg hint, StrictTransformComposition.strictTransform_comp hπ hg]
  exact (hD.preimage g).mono_right
    (strictTransform_subset_preimage hg.continuous isClosed_closure)

/-- The total transform of a `π`-exceptional divisor is `π ∘ g`-exceptional. -/
theorem support_totalTransform_subset_exceptionalLocus {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) {D : EffectiveDivisor n Y}
    (hD : D.support ⊆ exceptionalLocus n π) :
    (EffectiveDivisor.totalTransform hg hint D).support ⊆ exceptionalLocus n (π ∘ g) := by
  rw [support_totalTransform hg hint,
    exceptionalLocus_comp (hπ.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
  exact fun z hz => Or.inr (hD hz)

/-- A `g`-exceptional divisor is `π ∘ g`-exceptional. -/
theorem support_subset_exceptionalLocus_comp {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {D : EffectiveDivisor n Z}
    (hD : D.support ⊆ exceptionalLocus n g) : D.support ⊆ exceptionalLocus n (π ∘ g) := by
  rw [exceptionalLocus_comp (hπ.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
  exact fun z hz => Or.inl (hD hz)

end Transforms

/-! ### Stages 1 and 2 -/

variable {n : ℕ}

/-- **Copy-4 Step 1, stages 1--2** (`sec:fixed-principalization`, `eq:def-Gm-tilde`,
`eq:def-cM`, `eq:Pmov-restriction`).  Given `lem:relative-principalization` (`hRP`), a compact
connected `X`, an irreducible `V` that is a closed connected submanifold of dimension `k < n`,
and coherent ideals `𝔅_m`, `𝔅_M` with `𝔅_M ⊆ 𝔅_m^q`, `V ⊄ Z(𝔅_m)` and `V ⊄ Z(𝔅_M)`: a
sequence of blowups `π : Y₁ → X` adapted to `V`, with smooth strict transform `W₁`, and effective
divisors `H^fix`, `P^mov` (exceptional) and `H'`, `P'` (disjoint from `W₁`) with

* `𝓘_V 𝒪_{Y₁} = 𝒪(-(H^fix + P^mov)) · 𝓘_{W₁}` (`eq:IV-H` after two stages),
* `𝔅_m 𝒪_{Y₁} = 𝒪(-(H^fix + H'))` (`G̃_m = H^fix + H'`),
* `𝔅_M 𝒪_{Y₁} = 𝒪(-q G̃_m) · 𝒪(-(P^mov + P'))` (`eq:def-cM` principalized; on `W₁` this is
  `G_M = q G_m + P^mov|_{W₁}`, i.e. `eq:Pmov-restriction`). -/
theorem exists_firstTwoStages (hRP : RelativePrincipalizationHolds.{u} n)
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hV : IsClosedConnectedSubmanifold n V.carrier k) (hk : k < n)
    {𝔟m 𝔟M : GermIdeal n X} (h𝔟m : 𝔟m.IsCoherent) (h𝔟M : 𝔟M.IsCoherent) {q : ℕ}
    (hle : 𝔟M.Le (idealPow 𝔟m q)) (hVm : ¬ V.carrier ⊆ 𝔟m.zeroLocus)
    (hVM : ¬ V.carrier ⊆ 𝔟M.zeroLocus) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X),
      IsAdaptedBlowupSequence n X V.carrier Y π ∧ CompactSpace Y ∧ ConnectedSpace Y ∧
      IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k ∧
      ∃ Hfix Hm Pmov PM : EffectiveDivisor n Y,
        Hfix.support ⊆ exceptionalLocus n π ∧ Pmov.support ⊆ exceptionalLocus n π ∧
        Disjoint Hm.support (strictTransform n π V.carrier) ∧
        Disjoint PM.support (strictTransform n π V.carrier) ∧
        GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V.carrier) =
          (Hfix.ideal.mul Pmov.ideal).mul
            (vanishingIdeal (n := n) (strictTransform n π V.carrier)) ∧
        GermIdeal.pullback (m := n) π 𝔟m = Hfix.ideal.mul Hm.ideal ∧
        GermIdeal.pullback (m := n) π 𝔟M =
          (idealPow (Hfix.ideal.mul Hm.ideal) q).mul (Pmov.ideal.mul PM.ideal) := by
  classical
  have hVne : V.carrier ≠ univ := ne_univ_of_isClosedConnectedSubmanifold hV hk
  -- stage 1: principalize `𝔅_m` along `V`
  obtain ⟨Y₁, _t₁, _c₁, _m₁, f₁, hf₁, hY₁c, hY₁k, hW₁, -, H₁, H₁', hH₁exc, hH₁'disj, -,
    hvan₁, hid₁, -⟩ :=
    RelativePrincipalization.exists_relativePrincipalization_of_factorizationData V.carrier k
      𝔟m h𝔟m
      (hRP X V.carrier k hV hVne 𝔟m h𝔟m (not_le_vanishingIdeal_of_not_subset_zeroLocus hVm))
  have := hY₁c
  have := hY₁k
  have hf₁m := hf₁.contMDiff
  -- `eq:def-cM`: `𝔅_M 𝒪_{Y_fix} = 𝒪(-q G̃_m) · 𝔠_M`
  have hGm : (H₁.ideal.mul H₁'.ideal).IsInvertible :=
    isInvertible_mul H₁.isInvertible H₁'.isInvertible
  have hpow : (GermIdeal.pullback (m := n) f₁ 𝔟M).Le
      (idealPow (H₁.ideal.mul H₁'.ideal) q) := by
    have h1 := pullback_le_pullback (m := n) (f := f₁) hle
    have h2 := pullback_idealPow_le hf₁m h𝔟m q
    rw [hid₁] at h2
    exact fun y g hg => h2 y g (h1 y g hg)
  obtain ⟨c, hc, hcM⟩ := exists_isCoherent_eq_mul (isCoherent_pullback hf₁m h𝔟M)
    (isInvertible_idealPow hGm q) hpow
  -- `𝔠_M ⊄ 𝓘_{W_m}`, because `V ⊄ Z(𝔅_M)`
  have hW₁M : ¬ strictTransform n f₁ V.carrier ⊆
      (GermIdeal.pullback (m := n) f₁ 𝔟M).zeroLocus := by
    rw [zeroLocus_pullback hf₁m h𝔟M]
    intro hsub
    obtain ⟨y, hyW⟩ := hW₁.2.1.nonempty
    obtain ⟨p, -, hpV, hpexc, hpZ⟩ :=
      exists_mem_notMem_exceptionalLocus_notMem_of_inter_strictTransform hf₁.isBlowupSequence V
        (isComplexAnalyticSubset_zeroLocus h𝔟M) hVM isOpen_univ ⟨y, trivial, hyW⟩
    exact hpZ (hsub (subset_closure ⟨hpV, hpexc⟩))
  have hcres : ¬ c.Le (vanishingIdeal (n := n) (strictTransform n f₁ V.carrier)) := by
    refine not_le_right_of_not_le_mul_invertible (isInvertible_idealPow hGm q) hc ?_
    rw [← hcM]
    exact not_le_vanishingIdeal_of_not_subset_zeroLocus hW₁M
  -- stage 2: principalize `𝔠_M` along `W_m`
  obtain ⟨Y₂, _t₂, _c₂, _m₂, f₂, hf₂, hπ₂, hY₂c, hY₂k, hW₂, P, P', hPexc, hP'disj, hvan₂,
    hid₂, -⟩ :=
    exists_principalizationStage hRP hf₁ hW₁ (ne_univ_of_isClosedConnectedSubmanifold hW₁ hk)
      c hc hcres
  -- `eq:IV-H` across the two stages
  obtain ⟨Htot, hHtot, -, hvan⟩ :=
    exists_vanishingIdeal_stage hf₁ hf₂ hV hW₁ hW₂ H₁ hH₁exc hvan₁ P hPexc hvan₂
  have hf₂m := hf₂.contMDiff
  have hint₂ := interior_exceptionalLocus_eq_empty_of_isAdaptedBlowupSequence hf₂
  refine ⟨Y₂, _t₂, _c₂, _m₂, f₁ ∘ f₂, hπ₂, hY₂c, hY₂k, hW₂,
    EffectiveDivisor.totalTransform hf₂m hint₂ H₁,
    EffectiveDivisor.totalTransform hf₂m hint₂ H₁', P, P',
    support_totalTransform_subset_exceptionalLocus hf₁m hf₂m hint₂ hH₁exc,
    support_subset_exceptionalLocus_comp hf₁m hf₂m hPexc,
    disjoint_totalTransform_strictTransform hf₁m hf₂m hint₂ hH₁'disj, hP'disj, ?_, ?_, ?_⟩
  · rw [hvan, hHtot]
    rfl
  · rw [pullback_comp hf₁m hf₂m h𝔟m, hid₁,
      pullback_mul hf₂m (isCoherent_ideal H₁) (isCoherent_ideal H₁')]
    rfl
  · rw [pullback_comp hf₁m hf₂m h𝔟M, hcM,
      pullback_mul hf₂m (isCoherent_idealPow (DivisorMetric.isCoherent_of_isInvertible hGm) q) hc,
      pullback_idealPow hf₂m (DivisorMetric.isCoherent_of_isInvertible hGm) q,
      pullback_mul hf₂m (isCoherent_ideal H₁) (isCoherent_ideal H₁'), hid₂]
    rfl

/-! ### Stage 3 -/

/-- **Copy-4 Step 1, stage 3, and Step 2** (`eq:PF-restriction`, `eq:IV-H`).  On a model
`π : Y₁ → X` carrying the output of `exists_firstTwoStages`, `lem:relative-principalization`
applied to a coherent ideal `𝔣 ⊄ 𝓘_{W₁}` (in Copy-4 the ideal `𝔣̃_B` realizing `F_B`) gives
`g : Y → Y₁` adapted to `W₁` such that the identities of stages 1--2 hold for the total
transforms on `Y`, `𝔣 𝒪_Y = 𝒪(-(P^F + P^F'))` with `P^F` exceptional and `P^F'` disjoint from
`W`, and `𝓘_V 𝒪_Y = 𝒪(-(H^fix + P^mov + P^F)) · 𝓘_W`. -/
theorem exists_thirdStage (hRP : RelativePrincipalizationHolds.{u} n)
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {V : Set X} {k : ℕ} (hV : IsClosedConnectedSubmanifold n V k) (hk : k < n)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] [ConnectedSpace Y] {π : Y → X} (hπ : IsAdaptedBlowupSequence n X V Y π)
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V) k)
    {𝔟m 𝔟M : GermIdeal n X} (h𝔟m : 𝔟m.IsCoherent) (h𝔟M : 𝔟M.IsCoherent) {q : ℕ}
    {Hfix Hm Pmov PM : EffectiveDivisor n Y}
    (hHfix : Hfix.support ⊆ exceptionalLocus n π) (hPmov : Pmov.support ⊆ exceptionalLocus n π)
    (hHm : Disjoint Hm.support (strictTransform n π V))
    (hPM : Disjoint PM.support (strictTransform n π V))
    (hvan : GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V) =
      (Hfix.ideal.mul Pmov.ideal).mul (vanishingIdeal (n := n) (strictTransform n π V)))
    (hbm : GermIdeal.pullback (m := n) π 𝔟m = Hfix.ideal.mul Hm.ideal)
    (hbM : GermIdeal.pullback (m := n) π 𝔟M =
      (idealPow (Hfix.ideal.mul Hm.ideal) q).mul (Pmov.ideal.mul PM.ideal))
    (𝔣 : GermIdeal n Y) (h𝔣 : 𝔣.IsCoherent)
    (h𝔣W : ¬ 𝔣.Le (vanishingIdeal (n := n) (strictTransform n π V))) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (g : Y' → Y),
      IsAdaptedBlowupSequence n Y (strictTransform n π V) Y' g ∧
      IsAdaptedBlowupSequence n X V Y' (π ∘ g) ∧ CompactSpace Y' ∧ ConnectedSpace Y' ∧
      IsClosedConnectedSubmanifold n (strictTransform n (π ∘ g) V) k ∧
      ∃ Hfix' Hm' Pmov' PM' PF PF' : EffectiveDivisor n Y',
        Hfix'.support ⊆ exceptionalLocus n (π ∘ g) ∧
        Pmov'.support ⊆ exceptionalLocus n (π ∘ g) ∧
        PF.support ⊆ exceptionalLocus n (π ∘ g) ∧
        Disjoint Hm'.support (strictTransform n (π ∘ g) V) ∧
        Disjoint PM'.support (strictTransform n (π ∘ g) V) ∧
        Disjoint PF'.support (strictTransform n (π ∘ g) V) ∧
        GermIdeal.pullback (m := n) (π ∘ g) (vanishingIdeal (n := n) V) =
          ((Hfix'.ideal.mul Pmov'.ideal).mul PF.ideal).mul
            (vanishingIdeal (n := n) (strictTransform n (π ∘ g) V)) ∧
        GermIdeal.pullback (m := n) (π ∘ g) 𝔟m = Hfix'.ideal.mul Hm'.ideal ∧
        GermIdeal.pullback (m := n) (π ∘ g) 𝔟M =
          (idealPow (Hfix'.ideal.mul Hm'.ideal) q).mul (Pmov'.ideal.mul PM'.ideal) ∧
        GermIdeal.pullback (m := n) g 𝔣 = PF.ideal.mul PF'.ideal := by
  classical
  obtain ⟨Y', _t, _c, _m, g, hg, hπg, hY'c, hY'k, hW', PF, PF', hPFexc, hPF'disj, hvan₃,
    hid₃, -⟩ :=
    exists_principalizationStage hRP hπ hW (ne_univ_of_isClosedConnectedSubmanifold hW hk)
      𝔣 h𝔣 h𝔣W
  have hπm := hπ.contMDiff
  have hgm := hg.contMDiff
  have hint := interior_exceptionalLocus_eq_empty_of_isAdaptedBlowupSequence hg
  -- `eq:IV-H` across the third stage, with `H₀ = H^fix + P^mov`
  have hH₀exc : (EffectiveDivisor.add Hfix Pmov).support ⊆ exceptionalLocus n π :=
    (support_add_subset Hfix Pmov).trans (union_subset hHfix hPmov)
  obtain ⟨Htot, hHtot, -, hvanY⟩ :=
    exists_vanishingIdeal_stage hπ hg hV hW hW' (EffectiveDivisor.add Hfix Pmov) hH₀exc hvan
      PF hPFexc hvan₃
  have hHcoh : (Hfix.ideal.mul Hm.ideal).IsCoherent :=
    DivisorMetric.isCoherent_of_isInvertible (isInvertible_mul Hfix.isInvertible Hm.isInvertible)
  refine ⟨Y', _t, _c, _m, g, hg, hπg, hY'c, hY'k, hW',
    EffectiveDivisor.totalTransform hgm hint Hfix, EffectiveDivisor.totalTransform hgm hint Hm,
    EffectiveDivisor.totalTransform hgm hint Pmov, EffectiveDivisor.totalTransform hgm hint PM,
    PF, PF',
    support_totalTransform_subset_exceptionalLocus hπm hgm hint hHfix,
    support_totalTransform_subset_exceptionalLocus hπm hgm hint hPmov,
    support_subset_exceptionalLocus_comp hπm hgm hPFexc,
    disjoint_totalTransform_strictTransform hπm hgm hint hHm,
    disjoint_totalTransform_strictTransform hπm hgm hint hPM, hPF'disj, ?_, ?_, ?_, hid₃⟩
  · rw [hvanY, hHtot]
    change ((GermIdeal.pullback (m := n) g (Hfix.ideal.mul Pmov.ideal)).mul PF.ideal).mul _ = _
    rw [pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Pmov)]
    rfl
  · rw [pullback_comp hπm hgm h𝔟m, hbm, pullback_mul hgm (isCoherent_ideal Hfix)
      (isCoherent_ideal Hm)]
    rfl
  · rw [pullback_comp hπm hgm h𝔟M, hbM,
      pullback_mul hgm (isCoherent_idealPow hHcoh q)
        (IdealWeightPowers.isCoherent_mul (isCoherent_ideal Pmov) (isCoherent_ideal PM)),
      pullback_idealPow hgm hHcoh q,
      pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Hm),
      pullback_mul hgm (isCoherent_ideal Pmov) (isCoherent_ideal PM)]
    rfl

/-! ### The Step-1 fields of `Copy4StepOneData` -/

/-- **The Step-1 fields of `Copy4StepOneData`** from the output of the three stages:
`G̃_M` with `𝒪(-G̃_M) = 𝔅_M 𝒪_Y` (`hGMideal`), `𝔅_m 𝒪_Y ⊆ 𝒪(-H^fix)` (`hBm`),
`𝓘_V 𝒪_Y = 𝒪(-(H^fix + P^mov + P^F)) · 𝓘_W` (`hfact` with `idealIV = 𝓘_V`), and `P^mov`,
`P^F` exceptional. -/
theorem stepOneFields {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {V : Set X} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → X}
    {𝔟m 𝔟M : GermIdeal n X} {q : ℕ} {Hfix Hm Pmov PM PF : EffectiveDivisor n Y}
    (hvan : GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V) =
      ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal).mul
        (vanishingIdeal (n := n) (strictTransform n π V)))
    (hbm : GermIdeal.pullback (m := n) π 𝔟m = Hfix.ideal.mul Hm.ideal)
    (hbM : GermIdeal.pullback (m := n) π 𝔟M =
      (idealPow (Hfix.ideal.mul Hm.ideal) q).mul (Pmov.ideal.mul PM.ideal)) :
    ∃ GM : EffectiveDivisor n Y,
      GM.ideal = GermIdeal.pullback (m := n) π 𝔟M ∧
      (GermIdeal.pullback (m := n) π 𝔟m).Le Hfix.ideal ∧
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V) =
        ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal).mul
          (vanishingIdeal (n := n) (strictTransform n π V)) := by
  refine ⟨⟨GermIdeal.pullback (m := n) π 𝔟M, ?_⟩, rfl, ?_, hvan⟩
  · rw [hbM]
    exact isInvertible_mul
      (isInvertible_idealPow (isInvertible_mul Hfix.isInvertible Hm.isInvertible) q)
      (isInvertible_mul Pmov.isInvertible PM.isInvertible)
  · rw [hbm]
    exact mul_le_left (isCoherent_ideal Hfix)
      (fun hg => GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_ideal Hm) hg)

end

end Hironaka.PrincipalizationStepOneAssembly
