import Hironaka.Resolution.HironakaActualIntrinsicLogDerivativeFrame
import Hironaka.Resolution.HironakaActualExceptionalLogDerivativeIdeal
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces

/-! Actual original carrier quotient and geometric logarithmic germ dictionary.
BP FIRST: hironaka-actual-intrinsic-log-quotient-dictionary.tex.
No abstract intrinsic derivation lifting or transformation equivalence is assumed. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicLogQuotientDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm BlowupTowers
  HironakaActualIntrinsicLogDerivativeFrame HironakaActualExceptionalLogDerivativeIdeal
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualWholeStalkHolomorphicPullback
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactParameterCoefficientIdeals
  HironakaContactParameterIntrinsicOrder HironakaIntrinsicCarrierBoundaryCharts
  NormalCrossings BlowupFlatCoordinates GiraudAlong DerivativeIdealAlongCoherent
  DerivativeIdealAlong RelativePrincipalizationSpan HolomorphicGermCoordinateDerivation
  Hironaka.RegularLocusDense DerivativeIdealAlongEtale

section NativeStalks
variable {n m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) P] [IsComplexManifold m P]

private theorem exists_original_stalk_function (p : M)
    (r : actualComplexStructureStalk (n := n) p) :
    ∃ (g : M → ℂ) (hg : HolomorphicAt n g p), actualOriginalFunctionGerm p g hg = r := by
  obtain ⟨U,hp,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨sectionExtension U s,sectionExtension_holomorphicAt U s p hp,?_⟩
  exact actualOriginalFunctionGerm_eq_section U p hp s _ _ (Eventually.of_forall fun _ => rfl)

private theorem original_stalk_function_congr (p : M) {g h : M → ℂ}
    (hg : HolomorphicAt n g p) (hh : HolomorphicAt n h p) (he : g =ᶠ[𝓝 p] h) :
    actualOriginalFunctionGerm p g hg = actualOriginalFunctionGerm p h hh := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original p g h hg hh he

private theorem original_stalk_zero (p : M) :
    actualOriginalFunctionGerm p (fun _ => (0 : ℂ)) (holomorphicAt_const (n := n) 0) = 0 := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [actualOriginalFunctionGerm_chart,map_zero]
  rfl

private theorem original_stalk_zero_iff (p : M) {g : M → ℂ} (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p g hg = 0 ↔ g =ᶠ[𝓝 p] fun _ => 0 := by
  constructor
  · intro hz
    have h := congrArg (actualStalkChartEquiv (n := n) p)
      (hz.trans (original_stalk_zero p).symm)
    rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart] at h
    apply original_eventuallyEq_of_preferred_chart_eventuallyEq (n := n) p g (fun _ => 0)
    apply (HolGerm.mk_eq_mk_iff
      (hf := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p) hg))
      (hg := translated_holomorphic (chartAt (ComplexModel n) p p)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) p)
          (holomorphicAt_const (n := n) 0)))).mp
    exact h
  · intro he
    exact (original_stalk_function_congr p hg (holomorphicAt_const 0) he).trans (original_stalk_zero p)

private theorem native_stalk_original_function {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ) (z : P)
    (g : M → ℂ) (hg : HolomorphicAt n g (σ z)) :
    (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z (actualOriginalFunctionGerm (σ z) g hg) =
      actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := m) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem original_stalk_mul (p : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p (fun q => f q * g q) (hf.mul hg) =
      actualOriginalFunctionGerm p f hf * actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_mul _ _ _ _

private theorem original_stalk_sub (p : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p)
    (hsub : HolomorphicAt n (fun q => f q - g q) p) :
    actualOriginalFunctionGerm p (fun q => f q - g q) hsub =
      actualOriginalFunctionGerm p f hf - actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_sub,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sub _ _ _ _

private theorem original_stalk_sum (p : M) {r : ℕ} (s : Fin r → M → ℂ)
    (hs : ∀ i, HolomorphicAt n (s i) p) :
    actualOriginalFunctionGerm p (fun q => ∑ i, s i q)
      (HolomorphicAt.sum Finset.univ fun i _ => hs i) =
      ∑ i, actualOriginalFunctionGerm p (s i) (hs i) := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_sum]
  simp only [actualOriginalFunctionGerm_chart]
  unfold chartTranslatedGerm translatedGerm
  exact HolGerm.mk_sum _ _ _

private theorem span_image_mem {R : Type*} [CommRing R] (p : M)
    (φ : actualComplexStructureStalk (n := n) p →+* R) (L : Ideal R)
    (S : (M → ℂ) → Prop) (hS : ∀ g, S g → HolomorphicAt n g p)
    (hG : ∀ g hg, S g → φ (actualOriginalFunctionGerm p g hg) ∈ L)
    {f : M → ℂ} (hspan : IsInSpanAt (n := n) S p f) :
    φ (actualOriginalFunctionGerm p f hspan.1) ∈ L := by
  obtain ⟨hf,r,s,a,hs,ha,he⟩ := hspan
  have hsa (i) := (ha i).mul (hS (s i) (hs i))
  have hsum := HolomorphicAt.sum Finset.univ fun i _ => hsa i
  rw [original_stalk_function_congr p hf hsum he,
    original_stalk_sum p (fun i q => a i q * s i q) hsa,map_sum]
  apply L.sum_mem
  intro i _
  rw [original_stalk_mul _ _ _ (ha i) (hS (s i) (hs i)),map_mul]
  exact L.mul_mem_left _ (hG (s i) (hS (s i) (hs i)) (hs i))

private theorem native_whole_mono {A B : GermIdeal n M} (hAB : A.Le B) (p : M) :
    actualWholeSheafStalkIdeal A p ≤ actualWholeSheafStalkIdeal B p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨g,hg,hm,rfl⟩
  exact Ideal.subset_span ⟨g,hg,hAB p g hm,rfl⟩

private theorem native_whole_finite_span (A : GermIdeal n M) (p : M)
    {r : ℕ} (s : Fin r → M → ℂ) (hs : ∀ i, HolomorphicAt n (s i) p)
    (hgen : ∀ g, A.mem p g ↔ IsInSpanAt (n := n) (· ∈ Set.range s) p g) :
    actualWholeSheafStalkIdeal A p = Ideal.span (Set.range fun i => actualOriginalFunctionGerm p (s i) (hs i)) := by
  rw [actualWholeSheafStalkIdeal_eq_map_chart,
    wholeChartStalkIdeal_eq_actual_generator_span A p s hs hgen,Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  apply (actualStalkChartEquiv (n := n) p).injective
  change actualStalkChartEquiv (n := n) p
      ((actualStalkChartEquiv (n := n) p).symm (chartTranslatedGerm p p (mem_chart_source _ p) (s i) (hs i))) = _
  rw [RingEquiv.apply_symm_apply,actualOriginalFunctionGerm_chart]

private def sourceLogGen (N : Set M) (E : List (Set M)) (A : GermIdeal n M)
    (p : M) (s : M → ℂ) : Prop :=
  A.mem p s ∨ (vanishingIdeal (n := n) N).mem p s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsLogTangentField N E e ξ p ∧ A.mem p f ∧ s = fieldDeriv e ξ f

private theorem sourceLogGen_holomorphic {N : Set M} {E : List (Set M)}
    {A : GermIdeal n M} (hA : A.IsCoherent) (p : M) :
    ∀ g, sourceLogGen N E A p g → HolomorphicAt n g p := by
  rintro g (hg | hg | ⟨e,ξ,f,hξ,hf,rfl⟩)
  · exact GermIdeal.IsCoherent.holomorphicAt_mem hA hg
  · exact hg.1
  · exact holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
      (GermIdeal.IsCoherent.holomorphicAt_mem hA hf)

omit [IsComplexManifold n M] in
private theorem base_le_log {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : A.IsCoherent) : A.Le (logDerivIdealAlong N E A) := by
  intro p g hg
  change IsInSpanAt (sourceLogGen N E A p) p g
  exact isInSpanAt_of_eq_mul (Or.inl hg) (GermIdeal.IsCoherent.holomorphicAt_mem hA hg)
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

omit [IsComplexManifold n M] in
private theorem carrier_le_log {N : Set M} {E : List (Set M)} {A : GermIdeal n M} :
    (vanishingIdeal (n := n) N).Le (logDerivIdealAlong N E A) := by
  intro p g hg
  change IsInSpanAt (sourceLogGen N E A p) p g
  exact isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)

omit [IsComplexManifold n M] [IsComplexManifold m P] in
private theorem holomorphic_comp_local {r : M → P} {p : M}
    (hr : ∀ᶠ q in 𝓝 p, MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r q)
    {g : P → ℂ} (hg : HolomorphicAt m g (r p)) : HolomorphicAt n (g ∘ r) p := by
  filter_upwards [hr,hr.self_of_nhds.continuousAt.eventually hg] with q hq hgq
  exact hgq.comp q hq

/-- A true local geometric section lifts EVERY original native target stalk numerator. -/
private theorem native_stalk_surjective_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hsect : ∀ᶠ w in 𝓝 z, r (σ w) = w) :
    Function.Surjective ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z) := by
  intro q
  obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function z q
  have hgr : HolomorphicAt n (g ∘ r) (σ z) :=
    holomorphic_comp_local hr (hrz.symm ▸ hg)
  refine ⟨actualOriginalFunctionGerm (σ z) (g ∘ r) hgr,?_⟩
  rw [native_stalk_original_function]
  apply original_stalk_function_congr
  exact hsect.mono fun w hw => congrArg g hw

/-- Native kernel is the SAME whole vanishing ideal, derived by the actual on-carrier roundtrip. -/
private theorem native_stalk_kernel_of_local_retraction {σ : P → M}
    (hσ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ σ)
    (r : M → P) (N : Set M) (z : P)
    (hr : ∀ᶠ p in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) r p)
    (hrz : r (σ z) = z) (hσN : ∀ w, σ w ∈ N)
    (hround : ∀ᶠ p in 𝓝 (σ z), p ∈ N → σ (r p) = p) :
    RingHom.ker ((ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z).hom =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (σ z) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨g,hg,rfl⟩ := exists_original_stalk_function (σ z) q
    have hz : actualOriginalFunctionGerm z (g ∘ σ)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hσ.contMDiffAt)) = 0 := by
      rw [←native_stalk_original_function hσ z g hg]
      exact hq
    have hzero := (original_stalk_zero_iff z _).mp hz
    have hrt : Tendsto r (𝓝 (σ z)) (𝓝 z) := by
      simpa only [hrz] using hr.self_of_nhds.continuousAt.tendsto
    have hN : (vanishingIdeal (n := n) N).mem (σ z) g := by
      refine ⟨hg,?_⟩
      filter_upwards [hround,hrt.eventually hzero] with p hp hz hpN
      exact (congrArg g (hp hpN)).symm.trans hz
    exact Ideal.subset_span ⟨g,hg,hN,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨g,hg,hmem,rfl⟩
    change (ChartedSpace.locallyRingedSpaceMap σ hσ).stalkMap z
      (actualOriginalFunctionGerm (σ z) g hg) = 0
    rw [native_stalk_original_function]
    apply (original_stalk_zero_iff z _).mpr
    filter_upwards [hσ.continuous.continuousAt.eventually hmem.2] with w hw
    exact hw (hσN w)

end NativeStalks

section Parameter
variable {n : ℕ} {X : CMfd.{0} n} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (k : ℕ) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

/-- The literal actual ambient stalk map of the ORIGINAL parameter map. -/
def parameterStalkMap (v : parameterOpen Φ k) :
    actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) →+*
      actualComplexStructureStalk (n := k) v :=
  ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k)
    (parameterMapOn_contMDiff Φ k hΦsrc)).stalkMap v).hom

/-- The actual original native stalk map, followed by its genuine intrinsic chart equivalence. -/
def parameterGermPullback (v : parameterOpen Φ k) :
    actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) →+* HolGerm (ComplexModel k) :=
  (actualStalkChartEquiv (n := k) v).toRingHom.comp (parameterStalkMap Φ k hΦsrc v)

include hΦsrc in
private theorem parameter_function_holomorphic (v : parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMapOn Φ k v)) :
    ∀ᶠ w in 𝓝 v.val, DifferentiableAt ℂ (g ∘ parameterMap Φ k) w := by
  have hs := (parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
    ((parameterOpen Φ k).isOpen.mem_nhds v.property)
  filter_upwards [(parameterOpen Φ k).isOpen.mem_nhds v.property,
    hs.continuousAt.eventually hg.eventually_nhds] with w hw hgw
  apply mdifferentiableAt_iff_differentiableAt.mp
  exact hgw.self_of_nhds.comp w
    (((parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
      ((parameterOpen Φ k).isOpen.mem_nhds hw)).mdifferentiableAt (by simp))

private theorem parameter_function_germ (v : parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMapOn Φ k v)) :
    parameterGermPullback Φ k hΦsrc v (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg) =
      translatedGerm v.val (g ∘ parameterMap Φ k) (parameter_function_holomorphic Φ k hΦsrc v g hg) := by
  change actualStalkChartEquiv (n := k) v
    ((ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hΦsrc)).stalkMap v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg)) = _
  rw [native_stalk_original_function (parameterMapOn_contMDiff Φ k hΦsrc) v g hg,
    actualOriginalFunctionGerm_chart]
  have hF : HolomorphicAt k (g ∘ parameterMap Φ k) v.val := by
    filter_upwards [parameter_function_holomorphic Φ k hΦsrc v g hg] with w hw
    exact mdifferentiableAt_iff_differentiableAt.mpr hw
  have he := actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : parameterOpen Φ k → ComplexModel k)) contMDiff_subtype_val v
    (g ∘ parameterMap Φ k) hF
  rw [actualHolomorphicGermPullback_val] at he
  exact he.symm

private theorem coordinateInclusion_single (hk : k ≤ n) (j : Fin k) :
    coordinateInclusion n k (EuclideanSpace.single j 1) =
      EuclideanSpace.single (j.castLE hk) (1 : ℂ) := by
  ext i
  by_cases hij : i = j.castLE hk
  · subst i
    simp [coordinateInclusion_apply,j.isLt]
  · by_cases hi : i.val < k
    · have hne : (⟨i.val,hi⟩ : Fin k) ≠ j := by
        intro h
        apply hij
        exact Fin.ext (congrArg (fun a : Fin k => a.val) h)
      simp [coordinateInclusion_apply,hi,hij,hne]
    · simp [coordinateInclusion_apply,hi,hij]

include hΦsrc in
private theorem parameter_function_derivative (hk : k ≤ n) (j : Fin k)
    (w : ComplexModel k) (hw : w ∈ parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMap Φ k w)) :
    fderiv ℂ (g ∘ parameterMap Φ k) w (EuclideanSpace.single j 1) =
      flatPartial Φ (j.castLE hk) g (parameterMap Φ k w) := by
  have hd := differentiableAt_comp_flatInv hw hΦsrc hg
  change fderiv ℂ ((g ∘ flatInv Φ) ∘ coordinateInclusion n k) w _ = _
  rw [fderiv_comp w hd (coordinateInclusion n k).differentiableAt,
    ContinuousLinearMap.comp_apply,(coordinateInclusion n k).fderiv,
    coordinateInclusion_single k hk j]
  rw [flatPartial_eq (parameterMap_flat_dictionary Φ k hΦsrc w hw).1 hg,
    (parameterMap_flat_dictionary Φ k hΦsrc w hw).2]

private theorem parameter_partial_germ (hk : k ≤ n) (v : parameterOpen Φ k)
    (g : X → ℂ) (hg : HolomorphicAt n g (parameterMapOn Φ k v)) (j : Fin k) :
    parameterGermPullback Φ k hΦsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (flatPartial Φ (j.castLE hk) g)
        (holomorphicAt_flatPartial _ (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1 hg)) =
      coordinatePartial j (parameterGermPullback Φ k hΦsrc v
        (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg)) := by
  rw [parameter_function_germ,parameter_function_germ]
  unfold translatedGerm
  rw [coordinatePartial_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have ht : Tendsto (fun z : ComplexModel k => z + v.val) (𝓝 0) (𝓝 v.val) := by
    have hc : ContinuousAt (fun z : ComplexModel k => z + v.val) 0 := continuousAt_id.add_const v.val
    simpa only [zero_add] using hc.tendsto
  have hs := (parameterMap_contMDiffOn Φ k hΦsrc).contMDiffAt
    ((parameterOpen Φ k).isOpen.mem_nhds v.property)
  filter_upwards [ht.eventually ((parameterOpen Φ k).isOpen.mem_nhds v.property),
    ht.eventually (parameter_function_holomorphic Φ k hΦsrc v g hg),
    ht.eventually (hs.continuousAt.eventually hg.eventually_nhds)] with z hz hF hgz
  have he : fderiv ℂ (fun w => (g ∘ parameterMap Φ k) (w + v.val)) z =
      fderiv ℂ (g ∘ parameterMap Φ k) (z + v.val) := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using
      (hF.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const v.val)).fderiv
  rw [he,parameter_function_derivative Φ k hΦsrc hk j (z + v.val) hz g hgz]
  rfl

/-- Actual recentered full-slot coordinate coefficients, retaining units off each original trace. -/
def parameterWeight {l : ℕ} (κ : Fin l → Option (Fin n)) (hk : k ≤ n)
    (v : parameterOpen Φ k) (j : Fin k) : HolGerm (ComplexModel k) :=
  if ∃ i, κ i = some (j.castLE hk) then HolGerm.constHom (v.val j) + coordinateGerm j else 1

include hΦsrc in
private theorem weight_holomorphic {l : ℕ} (κ : Fin l → Option (Fin n)) (i : Fin n)
    (v : parameterOpen Φ k) :
    HolomorphicAt n (boundaryWeight Φ κ i) (parameterMapOn Φ k v) := by
  classical
  unfold boundaryWeight
  split
  · exact holomorphicAt_flatCoord Φ i (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1
  · exact holomorphicAt_const 1

private theorem parameter_weight_germ {l : ℕ} (κ : Fin l → Option (Fin n)) (hk : k ≤ n)
    (v : parameterOpen Φ k) (j : Fin k) :
    parameterGermPullback Φ k hΦsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (boundaryWeight Φ κ (j.castLE hk))
        (weight_holomorphic Φ k hΦsrc κ (j.castLE hk) v)) = parameterWeight Φ k κ hk v j := by
  classical
  rw [parameter_function_germ]
  by_cases ha : ∃ i, κ i = some (j.castLE hk)
  · simp only [parameterWeight,if_pos ha,boundaryWeight]
    change HolGerm.mk (fun z => flatCoord Φ (j.castLE hk) (parameterMap Φ k (z + v.val))) _ =
      HolGerm.constHom (v.val j) + coordinateGerm j
    rw [coordinateGerm,HolGerm.constHom_apply,←HolGerm.mk_add]
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (fun z : ComplexModel k => z + v.val) (𝓝 0) (𝓝 v.val) := by
      have hc : ContinuousAt (fun z : ComplexModel k => z + v.val) 0 := continuousAt_id.add_const v.val
      simpa only [zero_add] using hc.tendsto
    filter_upwards [ht.eventually ((parameterOpen Φ k).isOpen.mem_nhds v.property)] with z hz
    have h := congrArg (fun w : ComplexModel n => w (j.castLE hk))
      (parameterMap_flat_dictionary Φ k hΦsrc (z + v.val) hz).2
    calc
      _ = coordinateInclusion n k (z + v.val) (j.castLE hk) := h
      _ = (z + v.val) j := by simp [coordinateInclusion_apply,j.isLt]
      _ = v.val j + z j := by simp [add_comm]
  · simp [parameterWeight,ha,boundaryWeight,translatedGerm,HolGerm.mk_const]

/-- EVERY original numerator obeys the actual native weighted geometric-field germ formula. -/
theorem actual_weighted_field_pullback_germ {l : ℕ} (κ : Fin l → Option (Fin n))
    (hk : k ≤ n) (v : parameterOpen Φ k) (g : X → ℂ)
    (hg : HolomorphicAt n g (parameterMapOn Φ k v)) (j : Fin k) :
    parameterGermPullback Φ k hΦsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v)
        (fun p => boundaryWeight Φ κ (j.castLE hk) p * flatPartial Φ (j.castLE hk) g p)
        ((weight_holomorphic Φ k hΦsrc κ (j.castLE hk) v).mul
          (holomorphicAt_flatPartial _ (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1 hg))) =
      logDirection (parameterWeight Φ k κ hk v) j
        (parameterGermPullback Φ k hΦsrc v
          (actualOriginalFunctionGerm (parameterMapOn Φ k v) g hg)) := by
  have hw := weight_holomorphic Φ k hΦsrc κ (j.castLE hk) v
  have hp := holomorphicAt_flatPartial (j.castLE hk)
    (parameterMap_flat_dictionary Φ k hΦsrc v.val v.property).1 hg
  rw [original_stalk_mul _ _ _ hw hp,map_mul,parameter_weight_germ,parameter_partial_germ]
  rfl

include hΦsrc in
private theorem parameter_retraction_section (hk : k ≤ n) (v w : parameterOpen Φ k) :
    actualParameterRetraction Φ k v (parameterMapOn Φ k w) = w := by
  change openInv (parameterOpen Φ k) v
    (coordinateProjection n k (flatMap Φ (parameterMap Φ k w.val))) = w
  rw [(parameterMap_roundtrip Φ k hk hΦsrc).1 w.val w.property]
  simp [openInv,w.property]

private theorem parameter_whole_kernel {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    Function.Surjective (parameterStalkMap Φ k hΦsrc v) ∧
      RingHom.ker (parameterStalkMap Φ k hΦsrc v) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) := by
  have hg := actual_parameter_retraction_geometry Φ hk hΦsrc N hN v
  constructor
  · exact native_stalk_surjective_of_local_retraction (parameterMapOn_contMDiff Φ k hΦsrc)
      (actualParameterRetraction Φ k v) v hg.2.1 hg.2.2.1
      (Eventually.of_forall fun w => parameter_retraction_section Φ k hΦsrc hk v w)
  · exact native_stalk_kernel_of_local_retraction (parameterMapOn_contMDiff Φ k hΦsrc)
      (actualParameterRetraction Φ k v) N v hg.2.1 hg.2.2.1 hg.1 hg.2.2.2

private theorem parameter_germ_kernel {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    RingHom.ker (parameterGermPullback Φ k hΦsrc v) =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) := by
  rw [←(parameter_whole_kernel Φ k hΦsrc hk hN v).2]
  ext r
  change actualStalkChartEquiv (n := k) v (parameterStalkMap Φ k hΦsrc v r) = 0 ↔
    parameterStalkMap Φ k hΦsrc v r = 0
  constructor
  · intro h
    apply (actualStalkChartEquiv (n := k) v).injective
    simpa only [map_zero] using h
  · intro h
    simp only [h,map_zero]

private theorem parameter_germ_surjective {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) : Function.Surjective (parameterGermPullback Φ k hΦsrc v) :=
  (actualStalkChartEquiv (n := k) v).surjective.comp (parameter_whole_kernel Φ k hΦsrc hk hN v).1

private def carrierQuotientEquiv {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) :
    (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v)) ≃+*
      actualComplexStructureStalk (n := k) v :=
  (Ideal.quotEquivOfEq (parameter_whole_kernel Φ k hΦsrc hk hN v).2.symm).trans
    (RingHom.quotientKerEquivOfSurjective (parameter_whole_kernel Φ k hΦsrc hk hN v).1)

private theorem carrierQuotientEquiv_mk {N : Set X} (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k)
    (r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v)) :
    carrierQuotientEquiv Φ k hΦsrc hk hN v (Ideal.Quotient.mk _ r) =
      parameterStalkMap Φ k hΦsrc v r := by
  rfl

private theorem parameter_complex_square :
    ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hΦsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k) := by
  exact (ChartedSpace.locallyRingedSpace_comp 𝓘(ℂ,ComplexModel 0) (parameterMapOn_contMDiff Φ k hΦsrc)
    (contMDiff_const : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel 0) ∞
      (fun _ : X => (0 : ComplexModel 0)))).symm

end Parameter

section WholeLogarithmicImage
variable {k : ℕ}

/-- Held Leibniz/span engine specialized to ALL analytic coefficients of a whole finite ideal.
This generic plumbing receives no repeated independent engine credit. -/
private theorem derivative_of_span_mem
    (D : Derivation ℂ (HolGerm (ComplexModel k)) (HolGerm (ComplexModel k)))
    {r : ℕ} (G : Fin r → HolGerm (ComplexModel k))
    (J L : Ideal (HolGerm (ComplexModel k))) (hJ : J = Ideal.span (Set.range G))
    (hJL : J ≤ L) (hD : ∀ i, D (G i) ∈ L) : ∀ f ∈ J, D f ∈ L := by
  let K : Ideal (HolGerm (ComplexModel k)) :=
    { carrier := {f | f ∈ J ∧ D f ∈ L}
      zero_mem' := ⟨J.zero_mem,by rw [map_zero];exact L.zero_mem⟩
      add_mem' := by
        intro f g hf hg
        exact ⟨J.add_mem hf.1 hg.1,by rw [map_add];exact L.add_mem hf.2 hg.2⟩
      smul_mem' := by
        intro c f hf
        refine ⟨J.mul_mem_left c hf.1,?_⟩
        rw [smul_eq_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul]
        exact L.add_mem (L.mul_mem_left c hf.2) (hJL (J.mul_mem_right _ hf.1)) }
  have hJK : J ≤ K := by
    rw [hJ]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨hJ.symm ▸ Ideal.subset_span ⟨i,rfl⟩,hD i⟩
  intro f hf
  exact (hJK hf).2

/-- Whole ideal equality covers EVERY member and coefficient, not selected generator values. -/
private theorem logIdeal_eq_finite_span (a : Fin k → HolGerm (ComplexModel k))
    {r : ℕ} (G : Fin r → HolGerm (ComplexModel k))
    (J : Ideal (HolGerm (ComplexModel k))) (hJ : J = Ideal.span (Set.range G)) :
    logIdeal a J = J ⊔ Ideal.span {h | ∃ (j : Fin k) (i : Fin r), h = logDirection a j (G i)} := by
  let L := J ⊔ Ideal.span {h | ∃ (j : Fin k) (i : Fin r), h = logDirection a j (G i)}
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,f,hf,rfl⟩
    exact derivative_of_span_mem (logDirection a j) G J L hJ le_sup_left
      (fun i => (show Ideal.span _ ≤ L from le_sup_right) (Ideal.subset_span ⟨j,i,rfl⟩)) f hf
  · refine sup_le le_sup_left ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,i,rfl⟩
    exact (show Ideal.span _ ≤ logIdeal a J from le_sup_right)
      (Ideal.subset_span ⟨j,G i,hJ.symm ▸ Ideal.subset_span ⟨i,rfl⟩,rfl⟩)

end WholeLogarithmicImage

section LogImage
variable {n : ℕ} {X : CMfd.{0} n} {x : X}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
  (k : ℕ) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)

private theorem frame_derivative_image_mem {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (κ : Fin E.length → Option (Fin n)) (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k) (e : ComplexChart n X) (ξ : Fin n → X → ℂ)
    (hξ : IsLogTangentField N E e ξ (parameterMapOn Φ k v)) (f : X → ℂ)
    (hf : A.mem (parameterMapOn Φ k v) f) (c : Fin n → X → ℂ)
    (hc : ∀ j, HolomorphicAt n (c j) (parameterMapOn Φ k v))
    (hr : (vanishingIdeal (n := n) N).mem (parameterMapOn Φ k v)
      (fun p => fieldDeriv e ξ f p - ∑ j : Fin n, if j.val < k then
        c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0)) :
    parameterGermPullback Φ k hsrc v
      (actualOriginalFunctionGerm (parameterMapOn Φ k v) (fieldDeriv e ξ f)
        (holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt
          (GermIdeal.IsCoherent.holomorphicAt_mem hA hf))) ∈
      logIdeal (parameterWeight Φ k κ hk v)
        (Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))) := by
  classical
  let p := parameterMapOn Φ k v
  let φ := parameterGermPullback Φ k hsrc v
  let a := parameterWeight Φ k κ hk v
  let J := Ideal.map φ (actualWholeSheafStalkIdeal A p)
  let L := logIdeal a J
  have hpΦ : p ∈ flatDomain Φ := (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1
  have hfhol := GermIdeal.IsCoherent.holomorphicAt_mem hA hf
  have hD := holomorphicAt_fieldDeriv hξ.1.mem_source hξ.1.holomorphicAt hfhol
  let B : Fin n → X → ℂ := fun j q => if j.val < k then
    c j q * (boundaryWeight Φ κ j q * flatPartial Φ j f q) else 0
  have hB (j) : HolomorphicAt n (B j) p := by
    by_cases hj : j.val < k
    · simpa only [B,if_pos hj] using (hc j).mul
        ((weight_holomorphic Φ k hsrc κ j v).mul (holomorphicAt_flatPartial j hpΦ hfhol))
    · simpa only [B,if_neg hj] using holomorphicAt_const (n := n) (x := p) (0 : ℂ)
  have hsum := HolomorphicAt.sum Finset.univ fun j _ => hB j
  have hR0 : φ (actualOriginalFunctionGerm p
      (fun q => fieldDeriv e ξ f q - ∑ j, B j q) hr.1) = 0 := by
    change actualOriginalFunctionGerm p _ _ ∈ RingHom.ker (parameterGermPullback Φ k hsrc v)
    rw [parameter_germ_kernel Φ k hsrc hk hN v]
    exact Ideal.subset_span ⟨_,hr.1,hr,rfl⟩
  rw [original_stalk_sub _ _ _ hD hsum hr.1,map_sub,original_stalk_sum p B hB,map_sum] at hR0
  rw [sub_eq_zero.mp hR0]
  apply L.sum_mem
  intro j _
  by_cases hj : j.val < k
  · simp only [B,if_pos hj]
    have hw := weight_holomorphic Φ k hsrc κ j v
    have hP := holomorphicAt_flatPartial j hpΦ hfhol
    rw [original_stalk_mul _ _ _ (hc j) (hw.mul hP),map_mul]
    apply L.mul_mem_left
    let jj : Fin k := ⟨j.val,hj⟩
    have hcast : jj.castLE hk = j := Fin.ext rfl
    have he := actual_weighted_field_pullback_germ Φ k hsrc κ hk v f hfhol jj
    rw [hcast] at he
    rw [he]
    exact (show Ideal.span _ ≤ L from le_sup_right)
      (Ideal.subset_span ⟨jj,φ (actualOriginalFunctionGerm p f hfhol),
        Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨f,hfhol,hf,rfl⟩),rfl⟩)
  · simp only [B,if_neg hj,original_stalk_zero (n := n) p,map_zero]
    exact L.zero_mem

private theorem whole_log_image_eq {N : Set X} {E : List (Set X)}
    (A : GermIdeal n X) (hA : A.IsCoherent) (κ : Fin E.length → Option (Fin n)) (hk : k ≤ n)
    (hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k)
    (v : parameterOpen Φ k)
    (hfields : ∀ j : Fin k, IsLogTangentField N E (complexChartAt (n := n) x)
      (fun m p => boundaryWeight Φ κ (j.castLE hk) p *
        flatField Φ (EuclideanSpace.single (j.castLE hk) 1) m p) (parameterMapOn Φ k v))
    (hcoeff : ∀ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsLogTangentField N E e ξ (parameterMapOn Φ k v) →
      ∃ c : Fin n → X → ℂ, (∀ j, HolomorphicAt n (c j) (parameterMapOn Φ k v)) ∧
        ∀ f, HolomorphicAt n f (parameterMapOn Φ k v) →
          (vanishingIdeal (n := n) N).mem (parameterMapOn Φ k v)
            (fun p => fieldDeriv e ξ f p - ∑ j : Fin n, if j.val < k then
              c j p * (boundaryWeight Φ κ j p * flatPartial Φ j f p) else 0)) :
    Ideal.map (parameterGermPullback Φ k hsrc v)
      (actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) (parameterMapOn Φ k v)) =
      logIdeal (parameterWeight Φ k κ hk v)
        (Ideal.map (parameterGermPullback Φ k hsrc v)
          (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))) := by
  classical
  let p := parameterMapOn Φ k v
  let φ := parameterGermPullback Φ k hsrc v
  let a := parameterWeight Φ k κ hk v
  let J := Ideal.map φ (actualWholeSheafStalkIdeal A p)
  let K := Ideal.map φ (actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) p)
  have hpΦ : p ∈ flatDomain Φ := (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1
  have hbase : J ≤ K := Ideal.map_mono (native_whole_mono (base_le_log (N := N) (E := E) hA) p)
  apply le_antisymm
  · rw [actualWholeSheafStalkIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨r,⟨f,hf,hm,rfl⟩,rfl⟩
    change IsInSpanAt (sourceLogGen N E A p) p f at hm
    apply span_image_mem p φ (logIdeal a J) (sourceLogGen N E A p)
      (sourceLogGen_holomorphic hA p) ?_ hm
    rintro g hg (hmem | hmem | ⟨e,ξ,f,hξ,hf,rfl⟩)
    · exact (show J ≤ logIdeal a J from le_sup_left)
        (Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨g,hg,hmem,rfl⟩))
    · have hz : φ (actualOriginalFunctionGerm p g hg) = 0 := by
        change actualOriginalFunctionGerm p g hg ∈ RingHom.ker (parameterGermPullback Φ k hsrc v)
        rw [parameter_germ_kernel Φ k hsrc hk hN v]
        exact Ideal.subset_span ⟨g,hg,hmem,rfl⟩
      rw [hz]
      exact Ideal.zero_mem _
    · obtain ⟨c,hc,hr⟩ := hcoeff e ξ hξ
      exact frame_derivative_image_mem Φ k hsrc A hA κ hk hN v e ξ hξ f hf c hc
        (hr f (GermIdeal.IsCoherent.holomorphicAt_mem hA hf))
  · obtain ⟨U,hU,hp,r,s,hs,hgen⟩ := hA p
    have hhol (i : Fin r) : HolomorphicAt n (s i) p :=
      eventually_of_mem (hU.mem_nhds hp) fun q hq =>
        (hs i q hq).mdifferentiableAt (hU.mem_nhds hq)
    let G : Fin r → HolGerm (ComplexModel k) := fun i => φ (actualOriginalFunctionGerm p (s i) (hhol i))
    have hJ : J = Ideal.span (Set.range G) := by
      change Ideal.map φ (actualWholeSheafStalkIdeal A p) = _
      rw [native_whole_finite_span A p s hhol (hgen p hp),Ideal.map_span,←Set.range_comp]
      rfl
    rw [logIdeal_eq_finite_span a G J hJ]
    refine sup_le hbase ?_
    apply Ideal.span_le.mpr
    rintro _ ⟨j,i,rfl⟩
    have hsi : A.mem p (s i) := (hgen p hp _).mpr
      (isInSpanAt_of_eq_mul ⟨i,rfl⟩ (hhol i) (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm))
    let jj := j.castLE hk
    let w : X → ℂ := fun q => boundaryWeight Φ κ jj q * flatPartial Φ jj (s i) q
    have hw : HolomorphicAt n w p := (weight_holomorphic Φ k hsrc κ jj v).mul
      (holomorphicAt_flatPartial jj hpΦ (hhol i))
    have he : w = fieldDeriv (complexChartAt (n := n) x)
        (fun m q => boundaryWeight Φ κ jj q * flatField Φ (EuclideanSpace.single jj 1) m q) (s i) := by
      funext q
      simp only [w,flatPartial,fieldDeriv,Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hGen : sourceLogGen N E A p w :=
      Or.inr (Or.inr ⟨_,_,s i,hfields j,hsi,he⟩)
    have hLog : (logDerivIdealAlong N E A).mem p w := by
      change IsInSpanAt (sourceLogGen N E A p) p w
      exact isInSpanAt_of_eq_mul hGen hw (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => (one_mul _).symm)
    have himage : φ (actualOriginalFunctionGerm p w hw) ∈ K :=
      Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨w,hw,hLog,rfl⟩)
    exact (actual_weighted_field_pullback_germ Φ k hsrc κ hk v (s i) (hhol i) j) ▸ himage

end LogImage

/-- Reused full-slot restriction: the index type stays the ENTIRE original boundary list. -/
private def intrinsicSlot {n k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) : Option (Fin k) :=
  match s with
  | none => none
  | some j => some ⟨j.val,hs j rfl⟩

private theorem intrinsicSlot_value {n k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) :
    Option.map Fin.val (intrinsicSlot s hs) = Option.map Fin.val s := by
  cases s <;> rfl

private theorem intrinsicSlot_some_iff {n k : ℕ} (s : Option (Fin n))
    (hs : ∀ j, s = some j → j.val < k) (hk : k ≤ n) (j : Fin k) :
    intrinsicSlot s hs = some j ↔ s = some (j.castLE hk) := by
  cases s with
  | none => simp [intrinsicSlot]
  | some i =>
    constructor
    · intro h
      exact congrArg some (Fin.ext (congrArg (fun a : Fin k => a.val) (Option.some.inj h)))
    · intro h
      apply congrArg some
      apply Fin.ext
      exact congrArg (fun a : Fin n => a.val) (Option.some.inj h)

/-- Only ordinary original geometry produces the native carrier quotient on ONE parameter open,
before ALL its points and ALL original numerator germs. -/
theorem exists_actual_carrier_quotient_dictionary {n : ℕ} {X : CMfd.{0} n}
    {N : Set X} {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x ∈ N) :
    ∃ k ≤ n, ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n)) (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ p ∈ flatDomain Φ,
        (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
        ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
      (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
        ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
      ∀ v : parameterOpen Φ k,
        Function.Surjective (parameterStalkMap Φ k hsrc v) ∧
        RingHom.ker (parameterStalkMap Φ k hsrc v) =
          actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) ∧
        ∃ e : (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸
            actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v)) ≃+*
            actualComplexStructureStalk (n := k) v,
          ∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
            e (Ideal.Quotient.mk _ r) = parameterStalkMap Φ k hsrc v r := by
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,_hfields,_hcoeff⟩ :=
    exists_actual_full_boundary_log_frame hE hT x hx
  refine ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,parameter_complex_square Φ k hsrc,?_⟩
  intro v
  have hN : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k :=
    fun p hp => (hcharts p hp).1
  have hg := parameter_whole_kernel Φ k hsrc hk hN v
  exact ⟨hg.1,hg.2,carrierQuotientEquiv Φ k hsrc hk hN v,
    carrierQuotientEquiv_mk Φ k hsrc hk hN v⟩

/-- An ordinary original coherent ideal and full transverse boundary produce the WHOLE
geometric log-ideal dictionary and original quotient, with every numerator and scalar. -/
theorem exists_actual_intrinsic_log_quotient_dictionary {n : ℕ} {X : CMfd.{0} n}
    {N : Set X} {E : List (Set X)} (A : GermIdeal n X) (hA : A.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (x : X) (hx : x ∈ N) :
    ∃ (k : ℕ) (hk : k ≤ n),
      ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
        (κ : Fin E.length → Option (Fin n)) (τ : Fin E.length → Option (Fin k))
        (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
        Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
        (∀ i j, κ i = some j → j.val < k) ∧ Set.InjOn κ {i | x ∈ E.get i} ∧
        (∀ i, Option.map Fin.val (τ i) = Option.map Fin.val (κ i)) ∧
        (∀ v : parameterOpen Φ k, ∀ i, parameterMapOn Φ k v ∈ E.get i ↔
          ∃ j : Fin k, τ i = some j ∧ v.val j = 0) ∧
        (∀ p ∈ flatDomain Φ,
          (p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k) ∧
          ∀ i, p ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j p = 0) ∧
        (ChartedSpace.locallyRingedSpaceMap (parameterMapOn Φ k) (parameterMapOn_contMDiff Φ k hsrc) ≫
          ambientPointMap n X = ambientPointMap k (parameterOpen Φ k)) ∧
        (logDerivIdealAlong N E A).IsCoherent ∧
        ∀ v : parameterOpen Φ k,
          let φ := parameterGermPullback Φ k hsrc v
          let a := parameterWeight Φ k κ hk v
          let J := Ideal.map φ (actualWholeSheafStalkIdeal A (parameterMapOn Φ k v))
          let D := actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) (parameterMapOn Φ k v)
          Function.Surjective φ ∧
          RingHom.ker φ = actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) (parameterMapOn Φ k v) ∧
          Ideal.map φ D = logIdeal a J ∧ Ideal.comap φ (logIdeal a J) = D ∧
          ∃ e : (actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸ D) ≃+*
              (HolGerm (ComplexModel k) ⧸ logIdeal a J),
            (∀ r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v),
              e (Ideal.Quotient.mk D r) = Ideal.Quotient.mk (logIdeal a J) (φ r)) ∧
            ∀ (r : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v))
              (q : actualComplexStructureStalk (n := n) (parameterMapOn Φ k v) ⧸ D),
              e (Ideal.Quotient.mk D r * q) = Ideal.Quotient.mk (logIdeal a J) (φ r) * e q := by
  classical
  obtain ⟨k,hk,Φ,κ,hsrc,h0,hκ,hinj,hcharts,hfields,hcoeff⟩ :=
    exists_actual_full_boundary_log_frame hE hT x hx
  let τ : Fin E.length → Option (Fin k) := fun i => intrinsicSlot (κ i) (hκ i)
  have hslots (i) : Option.map Fin.val (τ i) = Option.map Fin.val (κ i) :=
    intrinsicSlot_value (κ i) (hκ i)
  have htrace (v : parameterOpen Φ k) (i : Fin E.length) :
      parameterMapOn Φ k v ∈ E.get i ↔ ∃ j : Fin k, τ i = some j ∧ v.val j = 0 := by
    have hp := parameterMap_flat_dictionary Φ k hsrc v.val v.property
    have he := (hcharts (parameterMapOn Φ k v) hp.1).2 i
    constructor
    · intro hv
      obtain ⟨a,ha,hzero⟩ := he.mp hv
      let j : Fin k := ⟨a.val,hκ i a ha⟩
      have hj : j.castLE hk = a := Fin.ext rfl
      refine ⟨j,(intrinsicSlot_some_iff (κ i) (hκ i) hk j).mpr (hj.symm ▸ ha),?_⟩
      have hval : flatCoord Φ a (parameterMapOn Φ k v) = v.val j := by
        change flatMap Φ (parameterMap Φ k v.val) a = _
        rw [hp.2]
        simp [coordinateInclusion_apply,hκ i a ha,j]
      exact hval.symm.trans hzero
    · rintro ⟨j,hj,hzero⟩
      apply he.mpr
      refine ⟨j.castLE hk,(intrinsicSlot_some_iff (κ i) (hκ i) hk j).mp hj,?_⟩
      change flatMap Φ (parameterMap Φ k v.val) (j.castLE hk) = 0
      rw [hp.2]
      simpa [coordinateInclusion_apply,j.isLt] using hzero
  refine ⟨k,hk,Φ,κ,τ,hsrc,h0,hκ,hinj,hslots,htrace,hcharts,
    parameter_complex_square Φ k hsrc,isCoherent_logDerivIdealAlong hA hN hE hT,?_⟩
  intro v
  let p := parameterMapOn Φ k v
  let φ := parameterGermPullback Φ k hsrc v
  let a := parameterWeight Φ k κ hk v
  let J := Ideal.map φ (actualWholeSheafStalkIdeal A p)
  let D := actualWholeSheafStalkIdeal (logDerivIdealAlong N E A) p
  have hpΦ : p ∈ flatDomain Φ := (parameterMap_flat_dictionary Φ k hsrc v.val v.property).1
  have hNgeo : ∀ p ∈ flatDomain Φ, p ∈ N ↔ flatMap Φ p ∈ complexCoordinatePlane n k :=
    fun p hp => (hcharts p hp).1
  have hSurj : Function.Surjective φ := parameter_germ_surjective Φ k hsrc hk hNgeo v
  have hKer : RingHom.ker φ = actualWholeSheafStalkIdeal (vanishingIdeal (n := n) N) p :=
    parameter_germ_kernel Φ k hsrc hk hNgeo v
  have hMap : Ideal.map φ D = logIdeal a J := whole_log_image_eq Φ k hsrc A hA κ hk hNgeo v
    (fun j => hfields p hpΦ (j.castLE hk) j.isLt) (hcoeff p hpΦ)
  have hKD : RingHom.ker φ ≤ D := by
    rw [hKer]
    exact native_whole_mono (carrier_le_log (E := E) (A := A)) p
  have hInv : Ideal.comap φ (logIdeal a J) = D := by
    rw [←hMap,Ideal.comap_map_of_surjective φ hSurj,←RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hKD
  let qmap := (Ideal.Quotient.mk (logIdeal a J)).comp φ
  have hqSurj : Function.Surjective qmap := Ideal.Quotient.mk_surjective.comp hSurj
  have hqKer : RingHom.ker qmap = D := by
    ext r
    change Ideal.Quotient.mk (logIdeal a J) (φ r) = 0 ↔ r ∈ D
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ Ideal.comap φ (logIdeal a J) ↔ r ∈ D
    rw [hInv]
  let e := (Ideal.quotEquivOfEq hqKer.symm).trans (RingHom.quotientKerEquivOfSurjective hqSurj)
  refine ⟨hSurj,hKer,hMap,hInv,e,?_,?_⟩
  · intro r
    rfl
  · intro r q
    rw [map_mul]
    rfl

end
end Hironaka.HironakaActualIntrinsicLogQuotientDictionary
