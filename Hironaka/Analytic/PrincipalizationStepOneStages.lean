import Hironaka.Blowup.BlowupSequenceTotalTransform
import Hironaka.Analytic.PrincipalizationStepOneData

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# One stage of Copy-4 Step 1: a relative principalization on top of a modification

Source: Copy-4, `prop:principalization`, Step 1 and Step 2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1774-1846`);
blueprint `ana:copy4-steps-one-to-five`.

Copy-4 builds the modification of `prop:principalization` in three stages
`Y → Y₁ → Y_fix → X`, each stage an application of `lem:relative-principalization` on the
current model, with the current strict transform of `V` as submanifold, to an ideal
(`𝔅_m`, then `𝔠_M`, then `𝔣̃_B`); Step 2 then reads off `H = H^fix_m + P^mov + P^F` with
`𝓘_V 𝒪_Y = 𝒪_Y(-H) · 𝓘_W` (`eq:IV-H`) by composing clause (i) of the lemma along the
stages.  This module provides the stage, independently of which ideal is principalized
(the three ideals of Copy-4 come from `sec:positive-current`; the QEA ideal waits):

* `isAdaptedBlowupSequence_comp` — a sequence of blowups adapted to `W` followed by one
  adapted to the strict transform of `W` is adapted to `W` (the definition is inductive in
  the LAST blowup, so this is an induction on the second sequence with
  `StrictTransformComposition.strictTransform_comp`);
* `zeroLocus_mul_subset` and `support_totalTransform` — supports of sums and total
  transforms of divisors;
* `exists_principalizationStage` — **one stage**: under `lem:relative-principalization`
  (`hRP`), a coherent ideal `𝔞` on the current model `Y` with nonzero restriction to the
  current strict transform `W` is principalized by an adapted `f : Y' → Y`, with the three
  clauses of the lemma for `f` and adaptedness of `π ∘ f` to `V`;
* `exists_vanishingIdeal_stage` — Step 2 across one more stage: if
  `𝓘_V 𝒪_Y = 𝒪_Y(-H₀) 𝓘_W` with `H₀` exceptional, then
  `𝓘_V 𝒪_{Y'} = 𝒪_{Y'}(-(f^*H₀ + H)) 𝓘_{W'}` with `f^*H₀ + H` exceptional for `π ∘ f`.

All sorry-free; the Hironaka content stays in the hypothesis `hRP`, discharged on the route
by `RelativePrincipalization.exists_factorizationData` (I-0484; proved in place from the canonical resolution invariant).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PrincipalizationStepOneStages

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  PrincipalizationStepOneInterface GermIdealTotalTransform BlowupSequenceTotalTransform

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-! ### Adapted sequences compose -/

/-- **Adapted sequences of blowups compose**: `f` adapted to `W`, followed by `g` adapted to
the strict transform of `W` under `f`, is adapted to `W`. -/
theorem isAdaptedBlowupSequence_comp {W : Set X} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    (hf : IsAdaptedBlowupSequence n X W Y f) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {g : Z → Y}
    (hg : IsAdaptedBlowupSequence n Y (strictTransform n f W) Z g) :
    IsAdaptedBlowupSequence n X W Z (f ∘ g) := by
  induction hg with
  | refl => exact hf
  | step g₁ C g₂ hg₁ hblow hcenter ih =>
      have hst : strictTransform n (f ∘ g₁) W = strictTransform n g₁ (strictTransform n f W) :=
        StrictTransformComposition.strictTransform_comp hf.contMDiff hg₁.contMDiff W
      exact IsAdaptedBlowupSequence.step (f ∘ g₁) C g₂ ih hblow (by rw [hst]; exact hcenter)

/-! ### Supports -/

section Supports

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`Z(𝔞 𝔟) ⊆ Z(𝔞) ∪ Z(𝔟)`** for coherent `𝔞`, `𝔟`: off both zero loci a product of two
germs nonvanishing at the point lies in `𝔞 𝔟`. -/
theorem zeroLocus_mul_subset {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent) :
    (𝔞.mul 𝔟).zeroLocus ⊆ 𝔞.zeroLocus ∪ 𝔟.zeroLocus := by
  intro x hx
  by_contra hnot
  rw [mem_union, not_or] at hnot
  obtain ⟨a, ha, hax⟩ : ∃ a, 𝔞.mem x a ∧ a x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnot.1 hcon
  obtain ⟨b, hb, hbx⟩ : ∃ b, 𝔟.mem x b ∧ b x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnot.2 hcon
  have hhol : HolomorphicAt n (a * b) x :=
    ((StepFourNoComponentContainsW.holomorphicAt_of_mem_of_isCoherent h𝔞 ha).mul
      (StepFourNoComponentContainsW.holomorphicAt_of_mem_of_isCoherent h𝔟 hb) :
        HolomorphicAt n (fun y => a y * b y) x)
  have hab : (𝔞.mul 𝔟).mem x (a * b) :=
    InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ a' b', 𝔞.mem x a' ∧ 𝔟.mem x b' ∧ s = a' * b') ⟨a, b, ha, hb, rfl⟩ hhol
  exact mul_ne_zero hax hbx (hx (a * b) hab)

/-- The support of a sum of effective divisors lies in the union of the supports. -/
theorem support_add_subset (D D' : EffectiveDivisor n M) :
    (EffectiveDivisor.add D D').support ⊆ D.support ∪ D'.support :=
  zeroLocus_mul_subset (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
    (DivisorMetric.isCoherent_of_isInvertible D'.isInvertible)

/-- **The support of a total transform is the preimage of the support.** -/
theorem support_totalTransform {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) (D : EffectiveDivisor n M) :
    (EffectiveDivisor.totalTransform hg hint D).support = g ⁻¹' D.support :=
  StepFourNoComponentContainsW.zeroLocus_pullback hg
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

end Supports

/-! ### One stage -/

/-- **One stage of Copy-4 Step 1.**  On a compact connected model `Y` reached from `X` by a
sequence of blowups `π` adapted to `V`, whose strict transform `W` of `V` is a proper closed
connected submanifold of dimension `k`, `lem:relative-principalization` (`hRP`) applied to a
coherent ideal `𝔞` on `Y` with nonzero restriction to `W` gives `f : Y' → Y` adapted to `W`
such that

* `π ∘ f` is adapted to `V`, `Y'` is compact and connected, and the strict transform `W'` of
  `V` under `π ∘ f` (the strict transform of `W` under `f`) is a closed connected submanifold
  of dimension `k`;
* clause (i): `𝓘_W 𝒪_{Y'} = 𝒪_{Y'}(-H) 𝓘_{W'}` with `H` supported on `Exc f`;
* clause (ii): `𝔞 𝒪_{Y'} = 𝒪_{Y'}(-H) 𝒪_{Y'}(-H')` with `H'` disjoint from `W'`;
* clause (iii): along `W'`, the restriction of `𝔞 𝒪_{Y'}` and that of `𝒪_{Y'}(-H)` have the
  same span. -/
theorem exists_principalizationStage (hRP : RelativePrincipalizationHolds.{u} n) {V : Set X}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] [ConnectedSpace Y] {π : Y → X} (hπ : IsAdaptedBlowupSequence n X V Y π)
    {k : ℕ} (hW : IsClosedConnectedSubmanifold n (strictTransform n π V) k)
    (hWY : strictTransform n π V ≠ univ) (𝔞 : GermIdeal n Y) (h𝔞 : 𝔞.IsCoherent)
    (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) (strictTransform n π V))) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y')
      (_ : IsComplexManifold n Y') (f : Y' → Y),
      IsAdaptedBlowupSequence n Y (strictTransform n π V) Y' f ∧
      IsAdaptedBlowupSequence n X V Y' (π ∘ f) ∧ CompactSpace Y' ∧ ConnectedSpace Y' ∧
      IsClosedConnectedSubmanifold n (strictTransform n (π ∘ f) V) k ∧
      ∃ H H' : EffectiveDivisor n Y',
        H.support ⊆ exceptionalLocus n f ∧
        Disjoint H'.support (strictTransform n (π ∘ f) V) ∧
        GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) (strictTransform n π V)) =
          H.ideal.mul (vanishingIdeal (n := n) (strictTransform n (π ∘ f) V)) ∧
        GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal ∧
        ∀ y ∈ strictTransform n (π ∘ f) V, ∀ g : Y' → ℂ, HolomorphicAt n g y →
          (IsInSpanOnAt (n := n) (strictTransform n (π ∘ f) V)
              (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g ↔
            IsInSpanOnAt (n := n) (strictTransform n (π ∘ f) V) (H.ideal.mem y) y g) := by
  obtain ⟨Y', _t, _c, _m, f, hf, hcompact, hconnected, hW', -, H, H', hHexc, hH'disj, -,
    hvanish, hideal, hspan⟩ :=
    RelativePrincipalization.exists_relativePrincipalization_of_factorizationData
      (strictTransform n π V) k 𝔞 h𝔞 (hRP Y (strictTransform n π V) k hW hWY 𝔞 h𝔞 hres)
  have hst : strictTransform n (π ∘ f) V = strictTransform n f (strictTransform n π V) :=
    StrictTransformComposition.strictTransform_comp hπ.contMDiff hf.contMDiff V
  refine ⟨Y', _t, _c, _m, f, hf, isAdaptedBlowupSequence_comp hπ hf, hcompact, hconnected,
    ?_, H, H', hHexc, ?_, ?_, hideal, ?_⟩
  · rw [hst]; exact hW'
  · rw [hst]; exact hH'disj
  · rw [hst]; exact hvanish
  · rw [hst]; exact hspan

/-- **Step 2 across one more stage** (`eq:IV-H`, composition remark after
`lem:relative-principalization`).  If `𝓘_V 𝒪_Y = 𝒪_Y(-H₀) 𝓘_W` with `H₀` supported on
`Exc π`, and `f` satisfies clause (i) for `W` with `H` supported on `Exc f`, then
`𝓘_V 𝒪_{Y'} = 𝒪_{Y'}(-(f^*H₀ + H)) 𝓘_{W'}` and `f^*H₀ + H` is supported on `Exc (π ∘ f)`. -/
theorem exists_vanishingIdeal_stage {V : Set X} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → X}
    (hπ : IsAdaptedBlowupSequence n X V Y π) {Y' : Type u} [TopologicalSpace Y']
    [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y'] {f : Y' → Y}
    (hf : IsAdaptedBlowupSequence n Y (strictTransform n π V) Y' f) {k j l : ℕ}
    (hV : IsClosedConnectedSubmanifold n V j)
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V) k)
    (hW' : IsClosedConnectedSubmanifold n (strictTransform n (π ∘ f) V) l)
    (H₀ : EffectiveDivisor n Y) (hH₀exc : H₀.support ⊆ exceptionalLocus n π)
    (h0 : GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V) =
      H₀.ideal.mul (vanishingIdeal (n := n) (strictTransform n π V)))
    (H : EffectiveDivisor n Y') (hHexc : H.support ⊆ exceptionalLocus n f)
    (h1 : GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) (strictTransform n π V)) =
      H.ideal.mul (vanishingIdeal (n := n) (strictTransform n (π ∘ f) V))) :
    ∃ Htot : EffectiveDivisor n Y',
      Htot.ideal = (GermIdeal.pullback (m := n) f H₀.ideal).mul H.ideal ∧
      Htot.support ⊆ exceptionalLocus n (π ∘ f) ∧
      GermIdeal.pullback (m := n) (π ∘ f) (vanishingIdeal (n := n) V) =
        Htot.ideal.mul (vanishingIdeal (n := n) (strictTransform n (π ∘ f) V)) := by
  have hst : strictTransform n (π ∘ f) V = strictTransform n f (strictTransform n π V) :=
    StrictTransformComposition.strictTransform_comp hπ.contMDiff hf.contMDiff V
  have hint := interior_exceptionalLocus_eq_empty_of_isBlowupSequence hf.isBlowupSequence
  have hexc : exceptionalLocus n (π ∘ f) =
      exceptionalLocus n f ∪ f ⁻¹' exceptionalLocus n π :=
    exceptionalLocus_comp (hπ.contMDiff.mdifferentiable (by simp))
      (hf.contMDiff.mdifferentiable (by simp))
  refine ⟨EffectiveDivisor.add (EffectiveDivisor.totalTransform hf.contMDiff hint H₀) H, rfl,
    ?_, ?_⟩
  · refine (support_add_subset _ _).trans ?_
    rw [support_totalTransform, hexc]
    exact union_subset (fun y hy => Or.inr (hH₀exc hy)) (fun y hy => Or.inl (hHexc hy))
  · have h1' := h1
    rw [hst] at h1'
    have := pullback_vanishingIdeal_comp_eq_mul hπ.contMDiff hf.contMDiff hint
      (RelativePrincipalizationVanishingWeight.isClosedSubmanifold_of_isClosedConnectedSubmanifold
        hV)
      (RelativePrincipalizationVanishingWeight.isClosedSubmanifold_of_isClosedConnectedSubmanifold
        hW)
      (by
        rw [← hst]
        exact RelativePrincipalizationVanishingWeight.isClosedSubmanifold_of_isClosedConnectedSubmanifold
          hW') H₀ H h0 h1'
    exact this

end

end Hironaka.PrincipalizationStepOneStages
