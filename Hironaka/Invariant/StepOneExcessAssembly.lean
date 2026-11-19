import Hironaka.Analytic.StepFourLogSingularities

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Steps 1--2 with the excess ideal, and `eq:DL-restriction` on the result

Source: Copy-4, `sec:fixed-principalization`, `prop:principalization` Steps 1, 2 and 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1598-1622,
1774-1892`).

This module composes the three stages of Copy-4 Step 1 with the excess ideal of
`ExcessIdealPrincipalization`:

1. `π_fix` principalizes `𝔅_m` and `Y₁ → Y_fix` the moving part of `𝔅_M`
   (`PrincipalizationStepOneAssembly.exists_firstTwoStages`, with `q = r + p`);
2. on `Y₁` the excess ideal `𝔣̃_B` is built from `𝔅̃` and `eq:ideal-comparison`
   (`ExcessIdealPrincipalization.excessIdeal_spec`);
3. `Y → Y₁` principalizes `𝔣̃_B` along `W₁` (`PrincipalizationStepOneStages.exists_principalizationStage`).

`exists_stepOneModel` returns the Step-1 fields of
`PrincipalizationStepOneInterface.Copy4StepOneData` (`G̃_M`, `H^fix`, `P^mov`, `P^F` with
`hGMideal`, `hBm`, `hfact` for `idealIV = 𝓘_V`, `hPmovexc`, `hPFexc`) TOGETHER with the
weight form of `eq:DL-restriction` on `W`
(`StepFourLogSingularities.sameSingularityTypeOn_stepFourWeights`), valid for every weight of
`𝔅̃` and all metrics of `G̃_M`, `P^mov`, `P^F`.  With
`StepFourLogSingularities.stepFourLogSingularities` this is the field `hlog` as soon as
`φ_{K,ℓ}` is given (the quasi-equisingular approximation, since proved).

The Hironaka content stays in the hypothesis `hRP` (I-0484), discharged on the route by
`RelativePrincipalization.exists_factorizationData` (proved in place from the canonical resolution invariant).  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepOneExcessAssembly

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  Hironaka.BlowupSequences RelativePrincipalizationSpan RestrictedIdealWeight
  RestrictedIdealQuotient IdealWeightPowers GermIdealTotalTransform GermIdealPullbackCalculus
  BlowupSequenceTotalTransform DivisorMetric PrincipalizationStepOneInterface
  PrincipalizationStepOneStages PrincipalizationStepOneAssembly ExcessIdealPrincipalization
  StepFourLogSingularities

noncomputable section

variable {n : ℕ}

/-- **Copy-4 Steps 1--2 with the excess ideal, and `eq:DL-restriction` on the model.**  Given
`lem:relative-principalization` (`hRP`), a compact connected `X`, an irreducible `V` that is a
closed connected submanifold of dimension `k < n`, coherent ideals `𝔅_m`, `𝔅_M`, `𝔅̃` with
`𝔅_M ⊆ 𝔅_m^{r+p}`, `eq:ideal-comparison` on `V` (`Res_V(𝔅̃ 𝔅_m^p) ⊆ Res_V 𝔅_M`), and `V`
contained in none of the three zero loci: a sequence of blowups `π : Y → X` adapted to `V` with
smooth strict transform `W` and effective divisors `G̃_M, H^fix, P^mov, P^F` such that

* `𝒪(-G̃_M) = 𝔅_M 𝒪_Y`, `𝔅_m 𝒪_Y ⊆ 𝒪(-H^fix)`, `𝓘_V 𝒪_Y = 𝒪(-(H^fix + P^mov + P^F)) 𝓘_W`,
  `P^mov`, `P^F` exceptional (the Step-1 fields of `Copy4StepOneData`);
* for every weight `ψ_𝔅` of `𝔅̃`, all metrics of `G̃_M`, `P^mov`, `P^F`, and `M > 0`,
  `C ≥ 1` with `r + p = C r` (Copy-4: `M/m = C ℓ/m`, `p = (C-1) ℓ/m`):
  `(C/M) ψ_𝔅 ∘ π = (1/M) ψ_{G̃_M} + ((C-1)/M) ψ_{P^mov} + (C/M) ψ_{P^F} + O(1)` on `W`. -/
theorem exists_stepOneModel (hRP : RelativePrincipalizationHolds.{u} n)
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hV : IsClosedConnectedSubmanifold n V.carrier k) (hk : k < n)
    {𝔟m 𝔟M 𝔅 : GermIdeal n X} (h𝔟m : 𝔟m.IsCoherent) (h𝔟M : 𝔟M.IsCoherent)
    (h𝔅 : 𝔅.IsCoherent) {r p : ℕ} (hle : 𝔟M.Le (idealPow 𝔟m (r + p)))
    (hcomp : RestrictLe V.carrier (𝔅.mul (idealPow 𝔟m p)) 𝔟M)
    (hVm : ¬ V.carrier ⊆ 𝔟m.zeroLocus) (hVM : ¬ V.carrier ⊆ 𝔟M.zeroLocus)
    (hVB : ¬ V.carrier ⊆ 𝔅.zeroLocus) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X),
      IsAdaptedBlowupSequence n X V.carrier Y π ∧ CompactSpace Y ∧ ConnectedSpace Y ∧
      IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k ∧
      ∃ GM Hfix Pmov PF : EffectiveDivisor n Y,
        GM.ideal = GermIdeal.pullback (m := n) π 𝔟M ∧
        (GermIdeal.pullback (m := n) π 𝔟m).Le Hfix.ideal ∧
        GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) V.carrier) =
          ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal).mul
            (vanishingIdeal (n := n) (strictTransform n π V.carrier)) ∧
        Pmov.support ⊆ exceptionalLocus n π ∧ PF.support ⊆ exceptionalLocus n π ∧
        ∀ ψB : X → EReal, HasAnalyticSingularitiesOfType (n := n) ψB 1 𝔅 →
        ∀ EGM EPmov EPF : MeteredEffectiveQDivisor n Y, IsDivisorMetric GM EGM →
          IsDivisorMetric Pmov EPmov → IsDivisorMetric PF EPF →
        ∀ C M : ℝ, 0 < M → 1 ≤ C → 0 < r → ((r + p : ℕ) : ℝ) = C * r →
          SameSingularityTypeOn (fun y => ((C / M : ℝ) : EReal) * ψB (π y))
            (fun y => ((1 / M : ℝ) : EReal) * EGM.weight y +
              (((C - 1) / M : ℝ) : EReal) * EPmov.weight y +
              ((C / M : ℝ) : EReal) * EPF.weight y)
            (strictTransform n π V.carrier) := by
  classical
  -- stages 1--2
  obtain ⟨Y₁, _t₁, _c₁, _m₁, π₁, hπ₁, hY₁c, hY₁k, hW₁, Hfix, Hm, Pmov, PM, hHfixexc,
    hPmovexc, hHmdisj, hPMdisj, hvan, hbm, hbM⟩ :=
    exists_firstTwoStages hRP V hV hk h𝔟m h𝔟M hle hVm hVM
  have := hY₁c
  have := hY₁k
  have hπ₁m := hπ₁.contMDiff
  have h𝔥 : (Hfix.ideal.mul Hm.ideal).IsInvertible :=
    GermIdealTotalTransform.isInvertible_mul Hfix.isInvertible Hm.isInvertible
  have h𝔓 : (Pmov.ideal.mul PM.ideal).IsInvertible :=
    GermIdealTotalTransform.isInvertible_mul Pmov.isInvertible PM.isInvertible
  have h𝔥c := DivisorMetric.isCoherent_of_isInvertible h𝔥
  have h𝔓c := DivisorMetric.isCoherent_of_isInvertible h𝔓
  have h𝔩c : ((idealPow (Hfix.ideal.mul Hm.ideal) r).mul (Pmov.ideal.mul PM.ideal)).IsCoherent :=
    IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔥c r) h𝔓c
  -- the excess ideal on `Y₁`
  obtain ⟨h𝔣c, h𝔣W, h1, h2⟩ :=
    excessIdeal_spec hπ₁.isBlowupSequence V hW₁ h𝔟m h𝔟M h𝔅 hcomp hVm hVM hVB h𝔥 h𝔓 hbm hbM
  -- stage 3: principalize the excess ideal along `W₁`
  obtain ⟨Y, _t, _c, _m, g, hg, hπg, hYc, hYconn, hW, PF, PF', hPFexc, hPF'disj, hvan₃,
    hid₃, -⟩ :=
    exists_principalizationStage hRP hπ₁ hW₁ (ne_univ_of_isClosedConnectedSubmanifold hW₁ hk)
      _ h𝔣c h𝔣W
  have hgm := hg.contMDiff
  have hint := interior_exceptionalLocus_eq_empty_of_isAdaptedBlowupSequence hg
  -- `eq:IV-H` across the third stage
  have hH₀exc : (EffectiveDivisor.add Hfix Pmov).support ⊆ exceptionalLocus n π₁ :=
    (support_add_subset Hfix Pmov).trans (union_subset hHfixexc hPmovexc)
  obtain ⟨Htot, hHtot, -, hvanY⟩ :=
    exists_vanishingIdeal_stage hπ₁ hg hV hW₁ hW (EffectiveDivisor.add Hfix Pmov) hH₀exc hvan
      PF hPFexc hvan₃
  set Hfix' := EffectiveDivisor.totalTransform hgm hint Hfix with hHfix'
  set Hm' := EffectiveDivisor.totalTransform hgm hint Hm with hHm'
  set Pmov' := EffectiveDivisor.totalTransform hgm hint Pmov with hPmov'
  set PM' := EffectiveDivisor.totalTransform hgm hint PM with hPM'
  have hvanY' : GermIdeal.pullback (m := n) (π₁ ∘ g) (vanishingIdeal (n := n) V.carrier) =
      ((Hfix'.ideal.mul Pmov'.ideal).mul PF.ideal).mul
        (vanishingIdeal (n := n) (strictTransform n (π₁ ∘ g) V.carrier)) := by
    rw [hvanY, hHtot]
    change ((GermIdeal.pullback (m := n) g (Hfix.ideal.mul Pmov.ideal)).mul PF.ideal).mul _ = _
    rw [pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Pmov)]
    rfl
  have hbmY : GermIdeal.pullback (m := n) (π₁ ∘ g) 𝔟m = Hfix'.ideal.mul Hm'.ideal := by
    rw [pullback_comp hπ₁m hgm h𝔟m, hbm,
      pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Hm)]
    rfl
  have hbMY : GermIdeal.pullback (m := n) (π₁ ∘ g) 𝔟M =
      (idealPow (Hfix'.ideal.mul Hm'.ideal) (r + p)).mul (Pmov'.ideal.mul PM'.ideal) := by
    rw [pullback_comp hπ₁m hgm h𝔟M, hbM,
      pullback_mul hgm (isCoherent_idealPow h𝔥c (r + p)) h𝔓c,
      pullback_idealPow hgm h𝔥c (r + p),
      pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Hm),
      pullback_mul hgm (isCoherent_ideal Pmov) (isCoherent_ideal PM)]
    rfl
  obtain ⟨GM, hGM, hBm, hfact⟩ := stepOneFields hvanY' hbmY hbMY
  -- `eq:PF-restriction` through `𝔅`, on `W`
  have hWW₁ : ∀ z ∈ strictTransform n (π₁ ∘ g) V.carrier, g z ∈ strictTransform n π₁ V.carrier := by
    intro z hz
    rw [StrictTransformComposition.strictTransform_comp hπ₁m hgm] at hz
    exact strictTransform_subset_preimage hgm.continuous hW₁.1 hz
  obtain ⟨e1, e2⟩ := restrictLe_pullback_excess hπ₁m hgm hWW₁ h𝔅 h𝔩c h𝔣c hid₃ h1 h2
  rw [pullback_mul hgm (isCoherent_idealPow h𝔥c r) h𝔓c, pullback_idealPow hgm h𝔥c r,
    pullback_mul hgm (isCoherent_ideal Hfix) (isCoherent_ideal Hm),
    pullback_mul hgm (isCoherent_ideal Pmov) (isCoherent_ideal PM)] at e1 e2
  refine ⟨Y, _t, _c, _m, π₁ ∘ g, hπg, hYc, hYconn, hW, GM, Hfix', Pmov', PF, hGM, hBm, hfact,
    support_totalTransform_subset_exceptionalLocus hπ₁m hgm hint hPmovexc,
    support_subset_exceptionalLocus_comp hπ₁m hgm hPFexc, ?_⟩
  intro ψB hψB EGM EPmov EPF hEGM hEPmov hEPF C M hM hC hr hq
  have := hYc
  exact sameSingularityTypeOn_stepFourWeights (hπ₁m.comp hgm) hW.1.isCompact h𝔅 hψB
    (Hfix := Hfix') (Hm := Hm') (Pmov := Pmov') (PM := PM') (PF := PF) (PF' := PF')
    (disjoint_totalTransform_strictTransform hπ₁m hgm hint hHmdisj)
    (disjoint_totalTransform_strictTransform hπ₁m hgm hint hPMdisj) hPF'disj
    (hGM.trans hbMY) e1 e2 hEGM hEPmov hEPF hM hC hr hq

end

end Hironaka.StepOneExcessAssembly
