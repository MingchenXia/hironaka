import Hironaka.Analytic.AdmissiblePrincipalizationAnalyticModification
import Hironaka.Analytic.AnalyticModificationComposition
import Hironaka.Analytic.AnalyticModificationStrongPullback
import Hironaka.Analytic.StepFourNoComponentContainsW
import Hironaka.MarkedIdeal.GermIdealTotalTransform

set_option autoImplicit false

/-! # Genuine domination of a prescribed single blowup

Complete statements and entire proofs precede this implementation in
`blueprint/src/prescribed-blowup-domination.tex`.
The centre ideal and its nonzero stalks are internally produced. The lift is
proved proper with genuine off-analytic holomorphic inverse data; it is not
assumed to be a finite blowup sequence.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PrescribedBlowupDomination

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaAdmissibleSequence AnalyticModificationLocalDiscrepancy DivisorExponentAlong

noncomputable section

variable {n : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

theorem isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent)
    (hint : interior 𝔞.zeroLocus = ∅) (x : X) :
    IsNonzeroAlongAt univ 𝔞 x := by
  obtain ⟨U, hU, hxU, N, g, hg, hgen⟩ := h𝔞 x
  apply isNonzeroAlongAt_univ_iff_exists.mpr
  by_contra hnone
  have hall : ∀ i, ∀ᶠ y in 𝓝 x, g i y = 0 := by
    intro i
    have hgm : 𝔞.mem x (g i) := (hgen x hxU (g i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩
        (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hg i) hxU))
    have hnot : ¬ ∃ᶠ y in 𝓝 x, g i y ≠ 0 := fun hfreq => hnone ⟨g i, hgm, hfreq⟩
    simpa only [not_frequently, not_not] using hnot
  have hZ : 𝔞.zeroLocus ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, eventually_all.mpr hall] with y hy hgy
    exact (StepFourNoComponentContainsW.mem_zeroLocus_iff_of_generators hU hg hgen hy).mpr hgy
  have hxZ := mem_interior_iff_mem_nhds.mpr hZ
  rw [hint] at hxZ
  exact hxZ

theorem isAnalyticModification_of_isBlowupAlong
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsAnalyticModification (n := n) π := by
  have hcoh := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hzero := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := n) hπ.1.1
  have hseq : IsAdmissibleBlowupSequence n X [] C Y π [π ⁻¹' C] := by
    simpa using IsAdmissibleBlowupSequence.step (id : X → X) [] C π
      IsAdmissibleBlowupSequence.refl hπ
      (NormalCrossings.hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1)
      (fun _ hx => hx)
  rw [← hzero] at hseq
  apply AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    hcoh hseq (BlowupExceptionalDivisor.exceptionalDivisor hπ)
  rw [BlowupExceptionalDivisor.support_exceptionalDivisor hπ, hzero]

private theorem interior_exceptional_eq_empty {c : Y → X}
    (hc : IsAnalyticModification (n := n) c) :
    interior (exceptionalLocus n c) = ∅ := by
  obtain ⟨A, _, _, hAi, _, hnon⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hc
  have hsub : exceptionalLocus n c ⊆ A := by
    intro y hy
    by_contra hyA
    exact hnon y hyA hy
  exact subset_empty_iff.mp ((interior_mono hsub).trans hAi.subset)

private theorem isAnalyticModification_of_commuting_lift
    {π : Y → X} {q : Z → X} {ℓ : Z → Y}
    (hπ : IsAnalyticModification (n := n) π)
    (hq : IsAnalyticModification (n := n) q)
    (hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hsquare : π ∘ ℓ = q) : IsAnalyticModification (n := n) ℓ := by
  obtain ⟨Aπ, Bπ, sπ, _, _, _, hBπc, hBπa, hBπi, hpreπ, _, _, hleftπ⟩ := hπ.2.2
  obtain ⟨Aq, Bq, sq, _, _, _, hBqc, hBqa, hBqi, hpreq, hsq, hrightq, hleftq⟩ := hq.2.2
  let T := Bπ ∪ Bq
  have hTc : IsClosed T := hBπc.union hBqc
  have hTa : IsComplexAnalyticSubset (n := n) T :=
    ConstantRankImage.IsComplexAnalyticSubset.union hBπa hBqa
  have hTi : interior T = ∅ := by
    change interior (Bπ ∪ Bq) = ∅
    rw [interior_union_isClosed_of_interior_empty hBπc hBqi]
    exact hBπi
  let AY := π ⁻¹' T
  let AW := q ⁻¹' T
  have hAYc : IsClosed AY := hTc.preimage hπ.1.continuous
  have hAWc : IsClosed AW := hTc.preimage hq.1.continuous
  have hAYa : IsComplexAnalyticSubset (n := n) AY :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.1 hTa
  have hAWa : IsComplexAnalyticSubset (n := n) AW :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hq.1 hTa
  have hAYi : interior AY = ∅ :=
    BlowupSequenceTotalTransform.interior_preimage_eq_empty hπ.1
      (interior_exceptional_eq_empty hπ) hTi
  have hAWi : interior AW = ∅ :=
    BlowupSequenceTotalTransform.interior_preimage_eq_empty hq.1
      (interior_exceptional_eq_empty hq) hTi
  have hproper : IsProperMap ℓ := isProperMap_of_comp_of_t2 hℓ.continuous
    hπ.1.continuous (hsquare.symm ▸ hq.2.1)
  have hpre : ℓ ⁻¹' AY = AW := by
    ext z
    change π (ℓ z) ∈ T ↔ q z ∈ T
    rw [show π (ℓ z) = q z from congrFun hsquare z]
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (sq ∘ π) AYᶜ := by
    apply hsq.comp hπ.1.contMDiffOn
    intro y hy h
    exact hy (Or.inr h)
  refine ⟨hℓ, hproper, AW, AY, sq ∘ π, hAWc, hAWa, hAWi,
    hAYc, hAYa, hAYi, hpre, hs, ?_, ?_⟩
  · intro y hy
    have hyq : π y ∉ Bq := fun h => hy (Or.inr h)
    have hyp : π y ∉ Bπ := fun h => hy (Or.inl h)
    have heq : π (ℓ (sq (π y))) = π y := by
      rw [show π (ℓ (sq (π y))) = q (sq (π y)) from congrFun hsquare (sq (π y)),
        hrightq (π y) hyq]
    have hya : y ∉ Aπ := by
      rw [← hpreπ]
      exact hyp
    have hla : ℓ (sq (π y)) ∉ Aπ := by
      rw [← hpreπ]
      change π (ℓ (sq (π y))) ∉ Bπ
      rwa [heq]
    exact (hleftπ _ hla).symm.trans ((congrArg sπ heq).trans (hleftπ y hya))
  · intro z hz
    have hzq : q z ∉ Bq := fun h => hz (Or.inr h)
    have hza : z ∉ Aq := by
      rw [← hpreq]
      exact hzq
    change sq (π (ℓ z)) = z
    rw [show π (ℓ z) = q z from congrFun hsquare z]
    exact hleftq z hza

/-- Public same-parameter interface to the existing genuine commuting-factor proof.
The original private producer and every prescribed-blowup consumer are unchanged. -/
theorem isAnalyticModification_of_commuting_factor
    {π : Y → X} {q : Z → X} {ℓ : Z → Y}
    (hπ : IsAnalyticModification (n := n) π)
    (hq : IsAnalyticModification (n := n) q)
    (hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hsquare : π ∘ ℓ = q) : IsAnalyticModification (n := n) ℓ :=
  isAnalyticModification_of_commuting_lift hπ hq hℓ hsquare

theorem exists_domination_of_isBlowupAlong [CompactSpace X]
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    {c : Z → X} (hc : IsAnalyticModification (n := n) c) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → Z) (ℓ : W → Y)
      (D : EffectiveDivisor n W) (E : List (Set W)),
      IsAdmissibleBlowupSequence n Z [] (c ⁻¹' C) W σ E ∧
      IsAnalyticModification (n := n) σ ∧ IsAnalyticModification (n := n) ℓ ∧
      π ∘ ℓ = c ∘ σ ∧
      GermIdeal.pullback (m := n) σ (GermIdeal.pullback (m := n) c
        (vanishingIdeal (n := n) C)) = D.ideal ∧
      NormalCrossings.IsSNCDivisor n E ∧ D.support = σ ⁻¹' (c ⁻¹' C) := by
  let 𝔞 := GermIdeal.pullback (m := n) c (vanishingIdeal (n := n) C)
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have ha : 𝔞.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hc.1 hIC
  have hZ : 𝔞.zeroLocus = c ⁻¹' C := by
    rw [show 𝔞 = GermIdeal.pullback (m := n) c (vanishingIdeal (n := n) C) from rfl,
      BlowupExceptionalDivisor.zeroLocus_pullback hc.1 hIC,
      BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hπ.1.1]
  have hthin : interior 𝔞.zeroLocus = ∅ := by
    rw [hZ]
    exact BlowupSequenceTotalTransform.interior_preimage_eq_empty hc.1
      (interior_exceptional_eq_empty hc) hπ.2.1
  let := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  obtain ⟨W, tW, chW, mW, σ, D, E, hσ, hpb, hE, _hsuppE, hsupp, _hiso⟩ :=
    exists_principalization_admissible ha
      (isNonzeroAlongAt_of_interior_zeroLocus_eq_empty ha hthin)
  let := tW
  let := chW
  let := mW
  have hσa := AdmissiblePrincipalizationAnalyticModification.isAnalyticModification_of_support_preimage
    ha hσ D hsupp
  have hq := AnalyticModificationComposition.isAnalyticModification_comp hc hσa
  have hinv : (GermIdeal.pullback (m := n) (c ∘ σ) (vanishingIdeal (n := n) C)).IsInvertible := by
    rw [GermIdealTotalTransform.pullback_comp hc.1 hσ.isBlowupSequence.contMDiff hIC, hpb]
    exact D.isInvertible
  obtain ⟨ℓ, ⟨hℓ, hsquare⟩, _⟩ :=
    hπ.2.2.2.2 n W (c ∘ σ) hq.1 hinv
  refine ⟨W, tW, chW, mW, σ, ℓ, D, E, ?_, hσa,
    isAnalyticModification_of_commuting_lift (isAnalyticModification_of_isBlowupAlong hπ)
      hq hℓ hsquare, hsquare, hpb, hE, ?_⟩
  · rwa [hZ] at hσ
  · rwa [hZ] at hsupp

end
end Hironaka.PrescribedBlowupDomination
