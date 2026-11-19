import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile
import Hironaka.Resolution.HironakaActualWholeIdealJetDetection
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Resolution.HironakaActualFreshRecursiveValues
import Hironaka.Analytic.AnalyticJacobianCriterion

/-! Entire original HS equality retains intrinsic regularity and singularity
of the WHOLE analytic set, without purity or a supplied dimension equality. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualWholeHSSingularity
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaHilbertSamuelTangentValue
  HironakaCurrentEmbeddingDimension HironakaActualRegularIntrinsicHSProfile
  HironakaActualReferenceHSSingularCentre HironakaActualWholeIdealJetDetection
  HironakaActualWholeStalkHolomorphicPullback HironakaActualFreshRecursiveValues
  AnalyticJacobianCriterion StokesSingularLocusAnalytic AnalyticJacobianSingularCore
  InvertibleIdealQuotient HironakaEmbeddedAnalytic

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def zeroFamilyPresentation {r : ℕ} (g : Fin r → M → ℂ)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hg : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (g i) U) :
    ComplexAnalyticPresentationAt (n := n) {y | ∀ i,g i y=0} x := by
  let e := (complexChartAt (n := n) x).val
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  refine
    { generatorCount := r
      generator := fun i z => g i (e.symm z)
      coordinateNeighborhood := e.target ∩ e.symm ⁻¹' U
      isOpen_coordinateNeighborhood :=
        e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
      center_mem_coordinateNeighborhood := ⟨e.map_source hxe,?_⟩
      coordinateNeighborhood_subset_target := inter_subset_left
      generator_holomorphic := ?_
      zeroLocus := ?_ }
  · change e.symm (e x) ∈ U
    rwa [e.left_inv hxe]
  · intro i z hz
    have hAt := ((hg i).mdifferentiableAt (hU.mem_nhds hz.2)).comp z
      (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hz.1)
    exact (mdifferentiableAt_iff_differentiableAt.mp hAt).differentiableWithinAt
  · intro y hy _
    change (∀ i,g i y=0) ↔ ∀ i,g i (e.symm (e y))=0
    rw [e.left_inv hy]

/-- Local analyticity of the ACTUAL selected zero family gives actual
original generators near x; no global extension of the equations is used. -/
private theorem zeroFamily_local_generators {r : ℕ} (g : Fin r → M → ℂ)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hg : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (g i) U) :
    ∃ (s : ℕ) (G : Fin s → M → ℂ),
      (∀ i,HolomorphicAt n (G i) x) ∧
      ∀ f,(vanishingIdeal (n := n) {y | ∀ i,g i y=0}).mem x f ↔
        IsInSpanAt (n := n) (· ∈ range G) x f := by
  let V : Opens M := ⟨U,hU⟩
  let N : Set M := {y | ∀ i,g i y=0}
  let f : Fin r → V → ℂ := fun i y => g i y.val
  have hf : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i) univ := by
    have hval : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (Subtype.val : V → M) := contMDiff_subtype_val
    intro i y _
    exact (((hg i).mdifferentiableAt (hU.mem_nhds y.property)).comp y
      (hval.mdifferentiable (by simp)).mdifferentiableAt).mdifferentiableWithinAt
  have hNV : IsComplexAnalyticSubset (n := n) ((Subtype.val : V → M) ⁻¹' N) := by
    intro y
    exact ⟨zeroFamilyPresentation f isOpen_univ (mem_univ y) hf⟩
  have hcoh : (GermIdeal.pullback (m := n) (Subtype.val : V → M)
      (vanishingIdeal (n := n) N)).IsCoherent := by
    rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal V N]
    exact CartanIrreducible.cartanCoherence _ hNV
  obtain ⟨O,hO,hxO,s,G,hG,hgen⟩ := exists_local_generators_of_open_pullback
    (I := vanishingIdeal (n := n) N) (fun _ _ hf => hf.1)
    (fun _ _ hf => DerivativeIdealAlong.vanishingIdeal_mem_of_isInSpanAt hf)
    V hcoh (⟨x,hx⟩ : V)
  refine ⟨s,G,?_,hgen x hxO⟩
  intro i
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact (hG i y hy).mdifferentiableAt (hO.mem_nhds hy)

private theorem original_mem_of_whole_chart_germ_mem
    (A : GermIdeal n M) (x : M) {s : ℕ} (G : Fin s → M → ℂ)
    (hG : ∀ i,HolomorphicAt n (G i) x)
    (hgen : ∀ f,A.mem x f ↔ IsInSpanAt (n := n) (· ∈ range G) x f)
    (f : M → ℂ) (hf : HolomorphicAt n f x)
    (hmem : chartTranslatedGerm x x (mem_chart_source _ x) f hf ∈
      wholeChartStalkIdeal A x x (mem_chart_source _ x)) : A.mem x f := by
  rw [wholeChartStalkIdeal_eq_actual_generator_span A x G hG hgen] at hmem
  let H : Fin s → ComplexModel n → ℂ :=
    fun i z => G i ((chartAt (ComplexModel n) x).symm z)
  have hH (i : Fin s) := CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) (hG i)
  have hbridge : A.mem x f ↔ chartTranslatedGerm x x (mem_chart_source _ x) f hf ∈
      Ideal.span (range fun i => chartTranslatedGerm x x (mem_chart_source _ x) (G i) (hG i)) :=
    (hgen f).trans ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
      (mem_chart_source _ x) G f).trans (isInSpanAt_iff_translatedGerm_mem H _ hH
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hf)))
  exact hbridge.mpr hmem

private theorem regular_of_binomial {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (x : M) (d : ℕ)
    (hProfile : ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=(d+ℓ).choose d) :
    RegularAtDim (n := n) W x d := by
  have hzero : 1 ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) x 0 := by
    rw [hProfile 0]
    simp
  have hxW : x ∈ W := by
    have h := (one_le_hilbertSamuelAt_zero_iff (vanishingIdeal (n := n) W)
      (CartanIrreducible.cartanCoherence W hW) x).mp hzero
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed] at h
  have hOne := hProfile 1
  rw [hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one hW hxW,
    Nat.choose_succ_self_right] at hOne
  have hemb : embeddingDimension (n := n) W x=d := by omega
  have hd : d ≤ n := hemb ▸ embeddingDimension_le W x
  obtain ⟨U,hU,hxU,N,s,hs,hspan,hzeroU⟩ :=
    StokesSingularLocus.exists_cartanGenerators hW hW.isClosed x
  let e := (complexChartAt (n := n) x).val
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  have hrank := rank_add_embeddingDimension_of_cartanGenerators hU hs hspan hzeroU
    (complexChartAt (n := n) x) hxU hxe hxW
  have hge : n-d ≤ Module.finrank ℂ (Submodule.span ℂ
      (range fun i => fderiv ℂ (fun z => s i (e.symm z)) (e x))) := by
    rw [hemb] at hrank
    change Module.finrank ℂ (Submodule.span ℂ
      (range fun i => fderiv ℂ (fun z => s i (e.symm z)) (e x)))+d=n at hrank
    omega
  obtain ⟨rows,cols,hminor⟩ := exists_minor_ne_zero_of_le_finrank _ hge
  let A : Set M := {y | ∀ j : Fin (n-d),s (rows j) y=0}
  let P := zeroFamilyPresentation (fun j => s (rows j)) hU hxU (fun j => hs (rows j))
  have hxA : x ∈ A := fun j => (hzeroU x hxU).mp hxW (rows j)
  have hminor' : jacobianMinor P.generator (fun a => a) cols (e x) ≠ 0 := by
    change (Matrix.of fun a b =>
      fderiv ℂ (fun z => s (rows a) (e.symm z)) (e x) (coordinateDirection (cols b))).det ≠ 0
    exact hminor
  have hAreg0 : RegularAtDim (n := n) A x (n-(n-d)) :=
    regularAtDim_of_presentation_fullJacobianMinor_ne_zero P hxA cols hminor'
  have hAreg : RegularAtDim (n := n) A x d := by
    simpa only [Nat.sub_sub_self hd] using hAreg0
  let IA := wholeChartStalkIdeal (vanishingIdeal (n := n) A) x x (mem_chart_source _ x)
  let IW := wholeChartStalkIdeal (vanishingIdeal (n := n) W) x x (mem_chart_source _ x)
  have hle : IA ≤ IW := by
    apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hfA,rfl⟩
    apply Ideal.subset_span
    refine ⟨f,hf,⟨hf,?_⟩,rfl⟩
    filter_upwards [hU.mem_nhds hxU,hfA.2] with y hy hyA hyW
    exact hyA (fun j => (hzeroU y hy).mp hyW (rows j))
  have hEq : IA=IW := (original_ideal_eq_iff_entire_hs_eq_of_le IA IW hle).mpr (by
    intro ℓ
    exact (hilbertSamuelAt_actual_regular hd hAreg ℓ).trans (hProfile ℓ).symm)
  obtain ⟨r,G,hG,hgenA⟩ := zeroFamily_local_generators
    (fun j => s (rows j)) hU hxU (fun j => hs (rows j))
  have hsAt (i : Fin N) : HolomorphicAt n (s i) x := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hs i y hy).mdifferentiableAt (hU.mem_nhds hy)
  have hsA (i : Fin N) : (vanishingIdeal (n := n) A).mem x (s i) := by
    have hmem : (vanishingIdeal (n := n) W).mem x (s i) :=
      (hspan x hxU (s i)).mpr (CoherentIdealColon.isInSpanAt_range_self hsAt i)
    have hgerm : chartTranslatedGerm x x (mem_chart_source _ x) (s i) (hsAt i) ∈ IW :=
      Ideal.subset_span ⟨s i,hsAt i,hmem,rfl⟩
    rw [←hEq] at hgerm
    exact original_mem_of_whole_chart_germ_mem (vanishingIdeal (n := n) A) x
      G hG hgenA (s i) (hsAt i) hgerm
  have hnear : ∀ᶠ y in 𝓝 x,y ∈ A ↔ y ∈ W := by
    filter_upwards [hU.mem_nhds hxU,eventually_all.mpr (fun i => (hsA i).2)] with y hy hsy
    exact ⟨fun hyA => (hzeroU y hy).mpr (fun i => hsy i hyA),
      fun hyW j => (hzeroU y hy).mp hyW (rows j)⟩
  obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hnear
  have hsets : A ∩ V=W ∩ V := by
    ext y
    exact and_congr_left (fun hy => hVsub hy)
  exact RegularPointDimension.regularAtDim_of_inter_eq hV hxV hsets hAreg

/-- Original analytic geometry and the ENTIRE actual binomial profile detect
true regularity; support, ambient dimension and envelope are all derived. -/
theorem regularAtDim_iff_intrinsic_hs_binomial {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (x : M) (d : ℕ) :
    RegularAtDim (n := n) W x d ↔
      ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=(d+ℓ).choose d := by
  exact ⟨fun h ℓ => hilbertSamuelAt_actual_regular h.1 h ℓ,regular_of_binomial hW x d⟩

/-- Equality of ENTIRE original profiles reflects SAME-dimensional true
regularity without purity or a supplied source dimension equality. -/
theorem regularAtDim_of_entire_hs_eq {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {x y : M} {d : ℕ}
    (hy : RegularAtDim (n := n) W y d)
    (hHS : ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) y ℓ) :
    RegularAtDim (n := n) W x d := by
  apply (regularAtDim_iff_intrinsic_hs_binomial hW x d).mpr
  exact fun ℓ => (hHS ℓ).trans (hilbertSamuelAt_actual_regular hy.1 hy ℓ)

/-- The literal ENTIRE equality locus of an intrinsically singular reference
consists of singular points of the WHOLE actual analytic set, in all dimensions. -/
theorem entire_hs_equality_locus_subset_singularSet {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {a : M}
    (ha : a ∈ singularSet (n := n) W) :
    {x | ∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ} ⊆ singularSet (n := n) W := by
  intro x hx
  have ha' := mem_singularSet_iff.mp ha
  have hcoh := CartanIrreducible.cartanCoherence W hW
  have hz := BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (n := n) hW.isClosed
  have ha0 : 1 ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) a 0 :=
    (one_le_hilbertSamuelAt_zero_iff _ hcoh a).mpr (hz.symm ▸ ha'.1)
  have hx0 : 1 ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) x 0 := by
    rw [hx 0]
    exact ha0
  have hxW : x ∈ W := hz ▸ (one_le_hilbertSamuelAt_zero_iff _ hcoh x).mp hx0
  apply mem_singularSet_iff.mpr
  refine ⟨hxW,fun d hd => ?_⟩
  exact ha'.2 d (regularAtDim_of_entire_hs_eq hW hd (fun ℓ => (hx ℓ).symm))

/-- Actual whole-HS constancy at a singular reference gives the literal
centre containment needed for the WHOLE-set singular branch. -/
theorem centre_subset_singularSet_of_entire_hs_equal {W C : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {a : M}
    (ha : a ∈ singularSet (n := n) W)
    (hC : ∀ x ∈ C,∀ ℓ,hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) :
    C ⊆ singularSet (n := n) W :=
  fun x hx => entire_hs_equality_locus_subset_singularSet hW ha (hC x hx)

end
end Hironaka.HironakaActualWholeHSSingularity
