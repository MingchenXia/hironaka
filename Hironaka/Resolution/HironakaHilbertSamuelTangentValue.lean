/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance
import Hironaka.Resolution.HironakaCurrentEmbeddingDimension

/-! # The genuine whole reduced first Hilbert--Samuel value

Actual original affine representatives internally fill the entire first jet.
The complete original ideal image is the faithful span of all original
Cartan differentials, proved from actual coordinate-product point powers.
Original analyticity internally constructs all reduced stalk, properness,
zero-value and complete tangent dictionaries. The same intrinsic literal
Hilbert--Samuel function then detects the actual current pure singular locus.
Normal-flat smooth centres, higher HS transformation and general G8 descent
remain subsequent geometry obligations.
-/

set_option autoImplicit false
open Set Filter Module
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaHilbertSamuelTangentValue
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
open Hironaka

noncomputable section
variable {n : ℕ}

/-- The actual empty original coordinate word in the genuine first-jet index. -/
def zeroWord (n : ℕ) : monomialIndex n 2 := ⟨0, Fin.elim0⟩

/-- The actual singleton original coordinate word in the genuine first-jet index. -/
def coordinateWord {n : ℕ} (i : Fin n) : monomialIndex n 2 := ⟨1, fun _ => i⟩

/-- The actual complete first-word index consists of one genuine empty word and n singleton words. -/
def firstWordEquiv (n : ℕ) : monomialIndex n 2 ≃ (Unit ⊕ Fin n) where
  toFun w := if h : w.1.val = 0 then Sum.inl () else
    Sum.inr (w.2 ⟨0, by have := w.1.isLt; omega⟩)
  invFun a := a.elim (fun _ => zeroWord n) coordinateWord
  left_inv w := by
    rcases w with ⟨⟨j, hj⟩, v⟩
    interval_cases j
    · simp only [dite_true, Sum.elim_inl]
      unfold zeroWord
      congr 1
      funext k
      exact Fin.elim0 k
    · simp only [Nat.one_ne_zero, dite_false, Sum.elim_inr]
      unfold coordinateWord
      congr 1
      funext k
      have hk : k = ⟨0, by omega⟩ := Fin.ext (by have := k.isLt; omega)
      rw [hk]
  right_inv a := by
    cases a with
    | inl u => cases u; rfl
    | inr i => rfl

/-- The complete actual first scalar coordinate jet on the ENTIRE original germ ring. -/
def firstScalarJet : HolGerm (ComplexModel n) →ₗ[ℂ] (monomialIndex n 2 → ℂ) :=
  (finiteCoordinateArray 2).comp (finiteJet 2)

/-- The genuine whole first scalar jet records the unmodified original function value. -/
theorem firstScalarJet_zeroWord {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z) :
    firstScalarJet (HolGerm.mk f hf) (zeroWord n) = f 0 := by
  have hg : translatedGerm 0 f hf = HolGerm.mk f hf := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp only [add_zero]
  change finiteCoordinateArray 2 (finiteJet 2 (HolGerm.mk f hf)) (zeroWord n) = _
  rw [← hg]
  have hh := finiteCoordinateArray_translatedGerm 2 0 hf (zeroWord n)
  change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm 0 f hf)) (zeroWord n) =
      iteratedFDeriv ℂ 0 f 0 (fun k : Fin 0 => EuclideanSpace.single (Fin.elim0 k) 1) at hh
  rw [iteratedFDeriv_zero_apply] at hh
  exact hh

/-- The genuine whole first scalar jet records the original coordinate derivative. -/
theorem firstScalarJet_coordinateWord {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z) (i : Fin n) :
    firstScalarJet (HolGerm.mk f hf) (coordinateWord i) =
      fderiv ℂ f 0 (AnalyticJacobianSingularCore.coordinateDirection i) := by
  have hg : translatedGerm 0 f hf = HolGerm.mk f hf := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp only [add_zero]
  change finiteCoordinateArray 2 (finiteJet 2 (HolGerm.mk f hf)) (coordinateWord i) = _
  rw [← hg]
  have hh := finiteCoordinateArray_translatedGerm 2 0 hf (coordinateWord i)
  change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm 0 f hf)) (coordinateWord i) =
      iteratedFDeriv ℂ 1 f 0 (fun _ : Fin 1 => EuclideanSpace.basisFun (Fin n) ℂ i) at hh
  rw [iteratedFDeriv_one_apply] at hh
  simpa only [EuclideanSpace.basisFun_apply, AnalyticJacobianSingularCore.coordinateDirection] using hh

/-- Genuine original affine functions internally realize every entire first-jet scalar array. -/
theorem firstScalarJet_surjective : Function.Surjective (firstScalarJet (n := n)) := by
  classical
  intro c
  let L : ComplexModel n →L[ℂ] ℂ := ∑ i : Fin n, c (coordinateWord i) • EuclideanSpace.proj i
  let F : ComplexModel n → ℂ := fun z => c (zeroWord n) + L z
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z :=
    Eventually.of_forall fun z => L.differentiableAt.const_add _
  refine ⟨HolGerm.mk F hF, ?_⟩
  funext w
  obtain ⟨a, ha⟩ := (firstWordEquiv n).symm.surjective w
  rw [← ha]
  cases a with
  | inl u =>
    cases u
    change firstScalarJet (HolGerm.mk F hF) (zeroWord n) = _
    rw [firstScalarJet_zeroWord]
    simp only [F, map_zero, add_zero]
    rfl
  | inr i =>
    change firstScalarJet (HolGerm.mk F hF) (coordinateWord i) = _
    rw [firstScalarJet_coordinateWord]
    have hd : fderiv ℂ F 0 = L := by
      simpa only [F, fderiv_const_add] using L.fderiv
    rw [hd]
    simp [L, AnalyticJacobianSingularCore.coordinateDirection, PiLp.single_apply]
    rfl

/-- The actual entire first-jet range has dimension one plus the true ambient dimension. -/
theorem finrank_range_finiteJet_two :
    Module.finrank ℂ (LinearMap.range (finiteJet (n := n) 2)) = 1 + n := by
  let V := LinearMap.range (finiteJet (n := n) 2)
  have hmap : V.map (finiteCoordinateArray 2) = ⊤ := by
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr firstScalarJet_surjective
  have hd := (V.equivMapOfInjective (finiteCoordinateArray 2) (finiteCoordinateArray_injective 2)).finrank_eq
  rw [hmap, finrank_top, finrank_pi] at hd
  calc
    Module.finrank ℂ V = Fintype.card (monomialIndex n 2) := hd
    _ = Fintype.card (Unit ⊕ Fin n) := Fintype.card_congr (firstWordEquiv n)
    _ = 1 + n := by simp

/-- The genuine differential array, with its actual empty-word entry zero. -/
def firstDerivativeEmbedding : (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] (monomialIndex n 2 → ℂ) where
  toFun L w := (firstWordEquiv n w).elim (fun _ => 0)
    (fun i => L (AnalyticJacobianSingularCore.coordinateDirection i))
  map_add' L K := by
    funext w
    cases h : firstWordEquiv n w <;> simp [h]
  map_smul' c L := by
    funext w
    cases h : firstWordEquiv n w <;> simp [h]

/-- Actual original coordinate directions make the complete differential array faithful. -/
theorem firstDerivativeEmbedding_injective : Function.Injective (firstDerivativeEmbedding (n := n)) := by
  intro L K h
  apply StokesSingularLocusAnalytic.evalBasis_injective
  funext i
  have hi := congrFun h (coordinateWord i)
  simpa [firstDerivativeEmbedding, firstWordEquiv, coordinateWord,
    StokesSingularLocusAnalytic.evalBasis] using hi

/-- Vanishing actual original generators have exactly their original differential as first jet. -/
theorem firstScalarJet_translated_eq_derivative (p : ComplexModel n) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) (hf0 : f p = 0) :
    firstScalarJet (translatedGerm p f hf) = firstDerivativeEmbedding (fderiv ℂ f p) := by
  funext w
  obtain ⟨a, ha⟩ := (firstWordEquiv n).symm.surjective w
  rw [← ha]
  cases a with
  | inl u =>
    cases u
    change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm p f hf)) (zeroWord n) = 0
    have hh := finiteCoordinateArray_translatedGerm 2 p hf (zeroWord n)
    change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm p f hf)) (zeroWord n) =
      iteratedFDeriv ℂ 0 f p (fun k : Fin 0 => EuclideanSpace.single (Fin.elim0 k) 1) at hh
    rw [iteratedFDeriv_zero_apply, hf0] at hh
    exact hh
  | inr i =>
    change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm p f hf)) (coordinateWord i) =
      fderiv ℂ f p (AnalyticJacobianSingularCore.coordinateDirection i)
    have hh := finiteCoordinateArray_translatedGerm 2 p hf (coordinateWord i)
    change finiteCoordinateArray 2 (finiteJet 2 (translatedGerm p f hf)) (coordinateWord i) =
      iteratedFDeriv ℂ 1 f p (fun _ : Fin 1 => EuclideanSpace.basisFun (Fin n) ℂ i) at hh
    rw [iteratedFDeriv_one_apply] at hh
    simpa only [EuclideanSpace.basisFun_apply, AnalyticJacobianSingularCore.coordinateDirection] using hh

/-- A genuine singleton original coordinate times a vanishing generator is killed by the entire first jet. -/
theorem firstScalarJet_coordinate_mul_translated_eq_zero (p : ComplexModel n)
    {f : ComplexModel n → ℂ} (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z)
    (hf0 : f p = 0) (i : Fin n) :
    firstScalarJet (coordinateGerm i * translatedGerm p f hf) = 0 := by
  have hc : coordinateGerm i ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    simp [coordinateGerm, HolGerm.eval_mk]
  have hg : translatedGerm p f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    simpa [translatedGerm, HolGerm.eval_mk] using hf0
  have hm : coordinateGerm i * translatedGerm p f hf ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hc hg
  have hz : finiteJet 2 (coordinateGerm i * translatedGerm p f hf) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_finiteJet]
    exact hm
  change finiteCoordinateArray 2 (finiteJet 2 _) = 0
  rw [hz, map_zero]

/-- Every literal original Macaulay column is internally its true differential or zero. -/
theorem firstScalarJet_word_mul_translated (p : ComplexModel n) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) (hf0 : f p = 0)
    (w : monomialIndex n 2) :
    firstScalarJet (wordMonomial w * translatedGerm p f hf) =
      (firstWordEquiv n w).elim (fun _ => firstDerivativeEmbedding (fderiv ℂ f p)) (fun _ => 0) := by
  obtain ⟨a, ha⟩ := (firstWordEquiv n).symm.surjective w
  rw [← ha, Equiv.apply_symm_apply]
  cases a with
  | inl u =>
    cases u
    change firstScalarJet (wordMonomial (zeroWord n) * translatedGerm p f hf) = _
    have hw : wordMonomial (zeroWord n) = 1 := by
      change (∏ k : Fin 0, coordinateGerm (Fin.elim0 k)) = 1
      simp
    rw [hw, one_mul]
    exact firstScalarJet_translated_eq_derivative p hf hf0
  | inr i =>
    change firstScalarJet (wordMonomial (coordinateWord i) * translatedGerm p f hf) = 0
    have hw : wordMonomial (coordinateWord i) = coordinateGerm i := by
      change (∏ _ : Fin 1, coordinateGerm i) = coordinateGerm i
      simp
    rw [hw]
    exact firstScalarJet_coordinate_mul_translated_eq_zero p hf hf0 i

/-- The complete original Macaulay range is the faithful image of ALL original differentials. -/
theorem range_first_originalMacaulay_eq_differentials {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) (hzero : ∀ i, G i p = 0) :
    LinearMap.range (originalMacaulayLinearMap 2 G p) =
      (Submodule.span ℂ (range fun i => fderiv ℂ (G i) p)).map firstDerivativeEmbedding := by
  classical
  rw [originalMacaulayLinearMap_eq 2 G p hG, LinearMap.range_comp, range_macaulayMap,
    map_span_ideal_finiteJet_eq_monomial_columns, Submodule.map_span, ← Set.range_comp']
  rw [Submodule.map_span, ← Set.range_comp']
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨w, i⟩, rfl⟩
    change firstScalarJet (wordMonomial w * translatedGerm p (G i) (hG i)) ∈ _
    rw [firstScalarJet_word_mul_translated p (hG i) (hzero i)]
    cases a : firstWordEquiv n w with
    | inl u =>
      simp only [Sum.elim_inl]
      exact Submodule.subset_span ⟨i, rfl⟩
    | inr j =>
      simp only [Sum.elim_inr]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have he : firstScalarJet (wordMonomial (zeroWord n) * translatedGerm p (G i) (hG i)) =
        firstDerivativeEmbedding (fderiv ℂ (G i) p) := by
      rw [firstScalarJet_word_mul_translated p (hG i) (hzero i)]
      rfl
    change firstDerivativeEmbedding (fderiv ℂ (G i) p) ∈ _
    rw [← he]
    exact Submodule.subset_span ⟨(zeroWord n, i), rfl⟩

/-- The dimension of the ENTIRE actual ideal first image is the full original cotangent rank. -/
theorem finrank_first_originalMacaulay_eq_differentials {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) (hzero : ∀ i, G i p = 0) :
    Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap 2 G p)) =
      Module.finrank ℂ (Submodule.span ℂ (range fun i => fderiv ℂ (G i) p)) := by
  rw [range_first_originalMacaulay_eq_differentials G p hG hzero]
  exact ((Submodule.span ℂ (range fun i => fderiv ℂ (G i) p)).equivMapOfInjective
    firstDerivativeEmbedding firstDerivativeEmbedding_injective).finrank_eq.symm

/-- The literal first Hilbert--Samuel value of the entire original vanishing family ideal. -/
theorem hilbertSamuelValue_translatedIdeal_one_eq {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) (hzero : ∀ i, G i p = 0) :
    hilbertSamuelValue (translatedIdeal G p hG) 1 =
      (1 + n) - Module.finrank ℂ (Submodule.span ℂ (range fun i => fderiv ℂ (G i) p)) := by
  rw [hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank,
    finrank_range_finiteJet_two, finrank_first_originalMacaulay_eq_differentials G p hG hzero]

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
open HolomorphicIdealSheaves HironakaCurrentEmbeddingDimension AnalyticDimensionBasics

/-- EVERY actual reduced membership germ lies in the actual maximal ideal at a genuine set point. -/
theorem whole_vanishing_stalk_le_maximalIdeal {A : Set M} {x : M} (hxA : x ∈ A) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) A) x x (mem_chart_source _ x) ≤
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, hmem, rfl⟩
  apply (HolGerm.mem_maximalIdeal_iff _).mpr
  have hf0 : f x = 0 := hmem.2.self_of_nhds hxA
  simpa [chartTranslatedGerm, translatedGerm, HolGerm.eval_mk,
    (chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x)] using hf0

/-- The genuine whole reduced stalk is proper at every actual original point. -/
theorem whole_vanishing_stalk_ne_top {A : Set M} {x : M} (hxA : x ∈ A) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) A) x x (mem_chart_source _ x) ≠ ⊤ := by
  intro he
  have hle := whole_vanishing_stalk_le_maximalIdeal (n := n) hxA
  rw [he] at hle
  have hm := top_le_iff.mp hle
  exact (IsLocalRing.maximalIdeal.isMaximal (HolGerm (ComplexModel n))).ne_top hm

/-- Original analyticity internally produces the COMPLETE reduced first HS/tangent identity. -/
theorem hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {x : M} (hxA : x ∈ A) :
    hilbertSamuelAt (vanishingIdeal (n := n) A) x 1 = embeddingDimension (n := n) A x + 1 := by
  classical
  obtain ⟨U, hU, hxU, N, s, hs, hspan, hzero⟩ :=
    StokesSingularLocus.exists_cartanGenerators hA hA.isClosed x
  let e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hshol (i : Fin N) : HolomorphicAt n (s i) x :=
    (show ∀ᶠ z in 𝓝 x, z ∈ U from hU.mem_nhds hxU).mono
      fun z hz => (hs i).mdifferentiableAt (hU.mem_nhds hz)
  let G : Fin N → ComplexModel n → ℂ := fun i z => s i (e.val.symm z)
  have hG (i : Fin N) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (G i) z :=
    CartanLocalReduction.holAt_comp_chart_symm hxe (hshol i)
  have hbridge (f : M → ℂ) (hf : HolomorphicAt n f x) :
      (vanishingIdeal (n := n) A).mem x f ↔ chartTranslatedGerm x x hxe f hf ∈
        translatedIdeal G (e.val x) hG :=
    (hspan x hxU f).trans
      ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff hxe s f).trans
        (isInSpanAt_iff_translatedGerm_mem G _ hG
          (CartanLocalReduction.holAt_comp_chart_symm hxe hf)))
  have hwhole : wholeChartStalkIdeal (vanishingIdeal (n := n) A) x x hxe =
      translatedIdeal G (e.val x) hG := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨f, hf, hmem, rfl⟩
      exact (hbridge f hf).mp hmem
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Ideal.subset_span
      refine ⟨s i, hshol i, ?_, rfl⟩
      exact (hspan x hxU (s i)).mpr (CoherentIdealColon.isInSpanAt_range_self hshol i)
  have hGzero (i : Fin N) : G i (e.val x) = 0 := by
    change s i (e.val.symm (e.val x)) = 0
    rw [e.val.left_inv hxe]
    exact (hzero x hxU).mp hxA i
  have hvalue := hilbertSamuelValue_translatedIdeal_one_eq G (e.val x) hG hGzero
  have hrank := rank_add_embeddingDimension_of_cartanGenerators hU hs hspan hzero e hxU hxe hxA
  rw [hilbertSamuelAt_eq_fixedChart (vanishingIdeal (n := n) A) x x hxe 1, hwhole, hvalue]
  change Module.finrank ℂ (Submodule.span ℂ (range fun i => fderiv ℂ (G i) (e.val x))) +
    embeddingDimension (n := n) A x = n at hrank
  omega

/-- The actual CURRENT pure singular locus is exactly the same intrinsic first-HS threshold. -/
theorem singularLocus_eq_first_hilbertSamuel_superlevel {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) A d) :
    A \ regularLocus (n := n) A d =
      {x | x ∈ A ∧ d + 2 ≤ hilbertSamuelAt (vanishingIdeal (n := n) A) x 1} := by
  rw [diff_regularLocus_eq_embeddingDimension_superlevel hA hd hpure]
  ext x
  by_cases hx : x ∈ A
  · simp only [Set.mem_ofPred_eq, hx, true_and]
    rw [hilbertSamuelAt_vanishing_one_eq_embeddingDimension_add_one hA hx]
    omega
  · simp [hx]

end Manifold

end
end Hironaka.HironakaHilbertSamuelTangentValue
