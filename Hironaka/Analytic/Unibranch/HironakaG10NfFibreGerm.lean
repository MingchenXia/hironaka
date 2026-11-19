import Hironaka.Resolution.HironakaFiniteSectionProductGraph
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction

/-!
# H3 (3), generic part: function germs in the actual structure stalks

Lane G10FI, run 0081 (H3 item (3), the fibre identity).  Calculus of the actual original function germs
`actualOriginalFunctionGerm y f hf` of a complex manifold: every stalk element is one (`exists_germ_eq`); two are equal
iff the functions agree near `y` (`germ_eq_iff`); they form a ring map on functions (`germ_add`, `germ_mul`, …); the
stalk map of a holomorphic map acts by composition (`stalkMap_germ`); a germ lies in the maximal ideal iff its value
vanishes (`germ_mem_maximalIdeal_iff`); and **Hadamard's lemma in the normal variable of `M × ℂ^r` at any point**
(`exists_hadamard_normal`): `K q - K (q.1, λ₀) = ∑ (q.2 i - λ₀ i) H i q` near `(u₀, λ₀)` (from TN
`whole_product_zero_plane_ideal` and a translation).

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspaceOpenRestriction HironakaFiniteSectionProductGraph

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every stalk element is an original function germ. -/
theorem exists_germ_eq (y : M) (g : actualComplexStructureStalk (n := n) y) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f y), actualOriginalFunctionGerm y f hf = g := by
  obtain ⟨V, hy, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq g
  exact ⟨sectionExtension V s, sectionExtension_holomorphicAt V s y hy,
    actualOriginalFunctionGerm_eq_section V y hy s _ _ Filter.EventuallyEq.rfl⟩

theorem germ_congr (y : M) {f g : M → ℂ} (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y)
    (h : f =ᶠ[𝓝 y] g) : actualOriginalFunctionGerm y f hf = actualOriginalFunctionGerm y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original y f g hf hg h

theorem germ_eq_iff (y : M) {f g : M → ℂ} (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    actualOriginalFunctionGerm y f hf = actualOriginalFunctionGerm y g hg ↔ f =ᶠ[𝓝 y] g := by
  refine ⟨fun h => ?_, germ_congr y hf hg⟩
  have h1 := congrArg (actualStalkChartEquiv (n := n) y) h
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart] at h1
  dsimp only [chartTranslatedGerm, translatedGerm] at h1
  have h2 := HolGerm.mk_eq_mk_iff.mp h1
  let e := chartAt (ComplexModel n) y
  have ht : Tendsto (fun z : M => e z - e y) (𝓝 y) (𝓝 0) := by
    have hc : ContinuousAt (fun z : M => e z - e y) y :=
      ((chartAt (ComplexModel n) y).continuousAt (mem_chart_source _ y)).sub continuousAt_const
    simpa using hc.tendsto
  filter_upwards [ht.eventually h2, (chart_source_mem_nhds (ComplexModel n) y)] with z hz hzs
  change f (e.symm (e z - e y + e y)) = g (e.symm (e z - e y + e y)) at hz
  rwa [sub_add_cancel, e.left_inv hzs] at hz

theorem germ_add (y : M) {f g : M → ℂ} (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    actualOriginalFunctionGerm y (fun p => f p + g p) (hf.add hg) =
      actualOriginalFunctionGerm y f hf + actualOriginalFunctionGerm y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_add, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

theorem germ_mul (y : M) {f g : M → ℂ} (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) :
    actualOriginalFunctionGerm y (fun p => f p * g p) (hf.mul hg) =
      actualOriginalFunctionGerm y f hf * actualOriginalFunctionGerm y g hg := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

theorem germ_zero (y : M) :
    actualOriginalFunctionGerm y (fun _ => (0 : ℂ)) (holomorphicAt_const (n := n) (x := y) 0) = 0 := by
  apply (actualStalkChartEquiv (n := n) y).injective
  rw [map_zero, actualOriginalFunctionGerm_chart]
  exact HolGerm.mk_zero

theorem germ_sum (y : M) {ι : Type*} (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, HolomorphicAt n (f i) y) :
    actualOriginalFunctionGerm y (fun p => ∑ i ∈ s, f i p) (HolomorphicAt.sum s fun i _ => hf i) =
      ∑ i ∈ s, actualOriginalFunctionGerm y (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact germ_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, ← germ_add]
    exact germ_congr y _ _ (Eventually.of_forall fun p => by simp only [Finset.sum_insert ha])

/-- The stalk map of a holomorphic map acts on function germs by composition. -/
theorem stalkMap_germ {m : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (ComplexModel m) N]
    [IsComplexManifold m N] {F : M → N} (hF : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ F)
    (p : M) (f : N → ℂ) (hf : HolomorphicAt m f (F p)) :
    (ChartedSpace.locallyRingedSpaceMap F hF).stalkMap p (actualOriginalFunctionGerm (F p) f hf) =
      actualOriginalFunctionGerm p (f ∘ F) (hf.comp_contMDiff (Eventually.of_forall fun _ => hF.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualNativeStalk_chart_pullback, actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function, actualOriginalFunctionGerm_chart]

/-- A function germ is a nonunit iff the function vanishes at the point. -/
theorem germ_isUnit_iff (y : M) {f : M → ℂ} (hf : HolomorphicAt n f y) :
    IsUnit (actualOriginalFunctionGerm y f hf) ↔ f y ≠ 0 := by
  rw [← MulEquiv.isUnit_map (actualStalkChartEquiv (n := n) y).toMulEquiv]
  change IsUnit (actualStalkChartEquiv (n := n) y (actualOriginalFunctionGerm y f hf)) ↔ _
  rw [actualOriginalFunctionGerm_chart, HolGerm.isUnit_iff_eval_ne_zero]
  dsimp only [chartTranslatedGerm, translatedGerm]
  rw [HolGerm.eval_mk, zero_add, (chartAt (ComplexModel n) y).left_inv (mem_chart_source _ y)]

theorem germ_mem_maximalIdeal_iff (y : M) {f : M → ℂ} (hf : HolomorphicAt n f y) :
    actualOriginalFunctionGerm y f hf ∈
        IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).presheaf.stalk y) ↔
      f y = 0 := by
  show ¬ IsUnit (actualOriginalFunctionGerm y f hf) ↔ f y = 0
  rw [germ_isUnit_iff, not_not]

/-- A member function of a germ ideal has its germ in the whole stalk ideal. -/
theorem germ_mem_whole (A : GermIdeal n M) (y : M) {f : M → ℂ} (hf : HolomorphicAt n f y) (h : A.mem y f) :
    actualOriginalFunctionGerm y f hf ∈ actualWholeSheafStalkIdeal A y :=
  Ideal.subset_span ⟨f, hf, h, rfl⟩

/-- A germ in the span of finitely many function germs is a holomorphic combination of the functions. -/
theorem eventually_eq_sum_of_mem_span (y : M) {k : ℕ} (e : Fin k → M → ℂ) (he : ∀ i, HolomorphicAt n (e i) y)
    {F : M → ℂ} (hF : HolomorphicAt n F y)
    (h : actualOriginalFunctionGerm y F hF ∈
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm y (e i) (he i))) :
    ∃ H : Fin k → M → ℂ, (∀ i, HolomorphicAt n (H i) y) ∧ F =ᶠ[𝓝 y] fun p => ∑ i, H i p * e i p := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  choose H hH hHc using fun i => exists_germ_eq y (c i)
  refine ⟨H, hH, ?_⟩
  have hsum := HolomorphicAt.sum (Finset.univ : Finset (Fin k)) (fun i _ => (hH i).mul (he i))
  apply (germ_eq_iff y hF hsum).mp
  rw [← hc, germ_sum y Finset.univ (fun i p => H i p * e i p) (fun i => (hH i).mul (he i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [germ_mul y (hH i) (he i), hHc]

/-- **Hadamard's lemma in the normal variable of `M × ℂ^r` at any point.** -/
theorem exists_hadamard_normal {r : ℕ} (K : M × ComplexModel r → ℂ) (p : M × ComplexModel r)
    (hK : HolomorphicAt (n+r) K p) :
    ∃ H : Fin r → M × ComplexModel r → ℂ, (∀ i, HolomorphicAt (n+r) (H i) p) ∧
      ∀ᶠ q in 𝓝 p, K q - K (q.1, p.2) = ∑ i, H i q * (q.2 i - p.2 i) := by
  let Tm : M × ComplexModel r → M × ComplexModel r := fun q => (q.1, q.2 - p.2)
  let Tp : M × ComplexModel r → M × ComplexModel r := fun q => (q.1, q.2 + p.2)
  have hTm : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞ Tm :=
    ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst
      (ProductComplexManifold.contMDiff_snd.sub contMDiff_const)
  have hTp : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞ Tp :=
    ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst
      (ProductComplexManifold.contMDiff_snd.add contMDiff_const)
  let p₀ : M × ComplexModel r := (p.1, 0)
  have hTpp : Tp p₀ = p := by simp [Tp, p₀]
  let F : M × ComplexModel r → ℂ := fun q => K (Tp q) - K (q.1, p.2)
  have hS : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (fun q : M × ComplexModel r => ((q.1, p.2) : M × ComplexModel r)) :=
    ProductComplexManifold.contMDiff_prodMk ProductComplexManifold.contMDiff_fst contMDiff_const
  have hF : HolomorphicAt (n+r) F p₀ := by
    have h1 : HolomorphicAt (n+r) (K ∘ Tp) p₀ :=
      (hTpp.symm ▸ hK : HolomorphicAt (n+r) K (Tp p₀)).comp_contMDiff
        (Eventually.of_forall fun _ => hTp.contMDiffAt)
    have h2 : HolomorphicAt (n+r) (K ∘ fun q : M × ComplexModel r => ((q.1, p.2) : M × ComplexModel r)) p₀ :=
      (hK : HolomorphicAt (n+r) K ((p₀.1, p.2))).comp_contMDiff (Eventually.of_forall fun _ => hS.contMDiffAt)
    exact (h1.and h2).mono fun _ h => h.1.sub h.2
  have hvan : (vanishingIdeal (n := n+r) {q : M × ComplexModel r | q.2 = 0}).mem p₀ F := by
    refine ⟨hF, Eventually.of_forall fun q hq => ?_⟩
    change K (q.1, q.2 + p.2) - K (q.1, p.2) = 0
    rw [show q.2 = 0 from hq, zero_add, sub_self]
  have hmem := germ_mem_whole _ p₀ hF hvan
  rw [whole_product_zero_plane_ideal] at hmem
  obtain ⟨H, hH, hFH⟩ := eventually_eq_sum_of_mem_span p₀ _ _ hF hmem
  have hcont : Tendsto Tm (𝓝 p) (𝓝 p₀) := by
    have := hTm.continuous.tendsto p
    simpa [Tm, p₀] using this
  refine ⟨fun i => H i ∘ Tm, fun i => ?_, ?_⟩
  · have hi : HolomorphicAt (n+r) (H i) (Tm p) := by
      simpa [Tm, p₀] using hH i
    exact hi.comp_contMDiff (Eventually.of_forall fun _ => hTm.contMDiffAt)
  · filter_upwards [hcont.eventually hFH] with q hq
    simp only [F, Tp, Tm, Function.comp_apply, sub_add_cancel] at hq ⊢
    exact hq

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm
