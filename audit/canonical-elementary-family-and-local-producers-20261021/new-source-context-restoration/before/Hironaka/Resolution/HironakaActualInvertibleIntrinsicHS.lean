/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPrincipalHSFormula
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Analytic.OrderInvariance

/-! Actual original invertible ideals retain their existing order and entire intrinsic HS. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualInvertibleIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaActualWholeStalkHolomorphicPullback HironakaActualPrincipalJetMultiplication
  HironakaActualPrincipalHSFormula RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers OrderTaylor HadamardBridge
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

private def centredChartForward (x : X) (y : X) : ComplexModel n :=
  (chartAt (ComplexModel n) x) y - (chartAt (ComplexModel n) x) x
private def centredChartInverse (x : X) (z : ComplexModel n) : X :=
  (chartAt (ComplexModel n) x).symm (z + (chartAt (ComplexModel n) x) x)

omit [IsComplexManifold n X] in
private theorem centredChartForward_zero (x : X) : centredChartForward (n := n) x x=0 := sub_self _
omit [IsComplexManifold n X] in
private theorem centredChartInverse_zero (x : X) : centredChartInverse (n := n) x 0=x := by
  simp only [centredChartInverse,zero_add,(chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x)]

private theorem centredChartForward_holomorphic (x : X) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (centredChartForward (n := n) x) y := by
  filter_upwards [(chartAt (ComplexModel n) x).open_source.mem_nhds (mem_chart_source _ x)] with y hy
  exact ((differentiableAt_id.sub_const ((chartAt (ComplexModel n) x) x)).mdifferentiableAt).comp y
    (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hy)

private theorem centredChartInverse_holomorphic (x : X) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (centredChartInverse (n := n) x) z := by
  have ht : Tendsto (fun z : ComplexModel n => z+(chartAt (ComplexModel n) x) x)
      (𝓝 0) (𝓝 ((chartAt (ComplexModel n) x) x)) := by
    have hc : ContinuousAt (fun z : ComplexModel n => z+(chartAt (ComplexModel n) x) x) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  filter_upwards [ht.eventually ((chartAt (ComplexModel n) x).open_target.mem_nhds
    ((chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)))] with z hz
  exact (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hz).comp z
    (differentiableAt_id.add_const ((chartAt (ComplexModel n) x) x)).mdifferentiableAt

omit [IsComplexManifold n X] in
private theorem centredChart_roundtrip (x : X) :
    ∀ᶠ y in 𝓝 x, centredChartInverse (n := n) x (centredChartForward (n := n) x y)=y := by
  filter_upwards [(chartAt (ComplexModel n) x).open_source.mem_nhds (mem_chart_source _ x)] with y hy
  simp only [centredChartInverse,centredChartForward,sub_add_cancel,
    (chartAt (ComplexModel n) x).left_inv hy]

/-- BOTH actual centred-chart maximal-power directions retain the original function and point ideal. -/
theorem chartTranslatedGerm_mem_maximal_pow_iff (x : X) (g : X → ℂ)
    (hg : HolomorphicAt n g x) (q : ℕ) :
    chartTranslatedGerm x x (mem_chart_source _ x) g hg ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
        (idealPow (pointIdeal n x) q).mem x g := by
  unfold chartTranslatedGerm translatedGerm
  rw [mem_maximalIdeal_pow_iff_point_power]
  change (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 (g ∘ centredChartInverse (n := n) x) ↔ _
  constructor
  · intro h
    have h' := comp_mem_idealPow_pointIdeal (n := n) (m := n)
      (φ := centredChartForward (n := n) x) (u := x) (centredChartForward_holomorphic (n := n) x) q
      (by simpa only [centredChartForward_zero (n := n) x] using h)
    apply mem_idealPow_congr h'
    exact (centredChart_roundtrip (n := n) x).mono fun y hy => congrArg g hy
  · intro h
    exact comp_mem_idealPow_pointIdeal (n := n) (m := n)
      (φ := centredChartInverse (n := n) x) (u := (0 : ComplexModel n))
      (centredChartInverse_holomorphic (n := n) x) q
      (by simpa only [centredChartInverse_zero (n := n) x] using h)

/-- The ENTIRE actual chart stalk has exactly the EXISTING original ambient order conditions. -/
theorem wholeChartStalkIdeal_le_maximal_pow_iff (A : GermIdeal n X) (x : X)
    (hA : ∀ g, A.mem x g → HolomorphicAt n g x) (q : ℕ) :
    wholeChartStalkIdeal A x x (mem_chart_source _ x) ≤
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔ OrderGE n univ A x q := by
  constructor
  · intro h g hg
    have hmem := (chartTranslatedGerm_mem_maximal_pow_iff x g (hA g hg) q).mp
      (h (Ideal.subset_span ⟨g,hA g hg,hg,rfl⟩))
    exact ⟨g,hmem,Eventually.of_forall fun _ _ => rfl⟩
  · intro h
    apply Ideal.span_le.mpr
    rintro f ⟨g,hg,hgA,rfl⟩
    exact (chartTranslatedGerm_mem_maximal_pow_iff x g hg q).mpr
      (mem_idealPow_of_vanishesToOrderOn_univ (h g hgA))

/-- ONLY original invertibility supplies a nonzero original principal whole chart stalk. -/
theorem exists_actual_nonzero_principal_whole_stalk (A : GermIdeal n X)
    (hA : A.IsInvertible) (x : X) :
    ∃ f : HolGerm (ComplexModel n), f ≠ 0 ∧
      wholeChartStalkIdeal A x x (mem_chart_source _ x)=Ideal.span ({f} : Set _) := by
  obtain ⟨U,hU,hxU,h,hh,hnon,hgen⟩ := hA x
  have hhol := InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hh hxU
  let f := chartTranslatedGerm x x (mem_chart_source _ x) h hhol
  have hspan := wholeChartStalkIdeal_eq_actual_generator_span A x
    (fun _ : Fin 1 => h) (fun _ => hhol) (by simpa using hgen x hxU)
  have hf : f ≠ 0 := by
    intro hf
    have heq : (h ∘ centredChartInverse (n := n) x) =ᶠ[𝓝 (0 : ComplexModel n)] fun _ => 0 := by
      have h0 : HolGerm.mk (fun z : ComplexModel n =>
          h ((chartAt (ComplexModel n) x).symm (z+(chartAt (ComplexModel n) x) x)))
          (translated_holomorphic _ (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hhol)) =
          HolGerm.mk (fun _ : ComplexModel n => 0) eventually_differentiableAt_zero := hf
      exact HolGerm.mk_eq_mk_iff.mp h0
    have ht : Tendsto (centredChartForward (n := n) x) (𝓝 x) (𝓝 0) := by
      simpa only [centredChartForward_zero (n := n) x] using
        (centredChartForward_holomorphic (n := n) x).self_of_nhds.continuousAt.tendsto
    have hz : ∀ᶠ y in 𝓝 x, h y=0 := by
      filter_upwards [ht.eventually heq,centredChart_roundtrip (n := n) x] with y hy hy'
      change h (centredChartInverse (n := n) x (centredChartForward (n := n) x y))=0 at hy
      rw [hy'] at hy
      exact hy
    obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hxU) hz)
    obtain ⟨y,hy,hyn⟩ := hnon V hV (fun y hy => (hVsub hy).1) ⟨x,hxV⟩
    exact hyn (hVsub hy).2
  refine ⟨f,hf,?_⟩
  simpa only [Set.range_const,Fin.isValue] using hspan

/-- Original invertibility internally supplies ONE actual finite original order and ALL intrinsic HS values. -/
theorem exists_actual_original_order_intrinsic_hs (A : GermIdeal n X)
    (hA : A.IsInvertible) (x : X) :
    ∃ μ : ℕ, order n univ A x=(μ : ℕ∞) ∧ ∀ ℓ,
      hilbertSamuelAt A x ℓ = Nat.choose (n+ℓ) n -
        (if μ ≤ ℓ then Nat.choose (n+(ℓ-μ)) n else 0) := by
  obtain ⟨f,hf,hI⟩ := exists_actual_nonzero_principal_whole_stalk A hA x
  let μ := actualGermOrder f hf
  obtain ⟨hm,hmn⟩ := actualGermOrder_spec f hf
  have hhol : ∀ g, A.mem x g → HolomorphicAt n g x :=
    fun g hg => GermIdeal.IsInvertible.holomorphicAt_mem hA hg
  have hge := (wholeChartStalkIdeal_le_maximal_pow_iff A x hhol μ).mp (by
    rw [hI]
    apply Ideal.span_le.mpr
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact hm)
  refine ⟨μ,le_antisymm ?_ ((le_order_iff hhol).mpr hge),?_⟩
  · apply iSup₂_le
    intro q hq
    have hqle : q ≤ μ := by
      by_contra hqle
      have hi := (wholeChartStalkIdeal_le_maximal_pow_iff A x hhol q).mpr hq
      rw [hI] at hi
      exact hmn (Ideal.pow_le_pow_right (by omega : μ+1 ≤ q)
        (hi (Ideal.subset_span (by simp))))
    exact_mod_cast hqle
  · intro ℓ
    unfold hilbertSamuelAt
    rw [hI]
    exact hilbertSamuelValue_actual_principal f μ hm hmn ℓ
end
end Hironaka.HironakaActualInvertibleIntrinsicHS
