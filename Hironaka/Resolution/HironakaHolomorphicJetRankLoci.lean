/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Hironaka.Analytic.RankDegeneracy
import Hironaka.Analytic.ManifoldFiniteSpanChartTransport

/-! # Actual holomorphic Macaulay matrices and whole point-value minor loci

The genuine whole-ring finite Macaulay columns are read in their actual finite
coordinate array. Joint original holomorphic functions produce holomorphic entries;
actual finite minors produce every literal finite Hilbert--Samuel superlevel.
Coherence internally produces original Cartan generators and the full nearby
chart-stalk ideal dictionary, including all original membership germs.

The final producers assume original holomorphicity or original coherence only.
They do not take a matrix, rank formula, point-value identity, stalk equality or
minor-locus equality as an input certificate. Nearby values here are measured in
one fixed original chart. Intrinsic nonlinear chart comparison, normally flat
smooth centres, actual HS transformation, higher-entry descent and general G8
termination are subsequent obligations.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaHolomorphicJetRankLoci
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
open Hironaka
noncomputable section
variable {n : ℕ}

/-- Evaluate the true degree-wise multilinear jets on every original coordinate-basis tuple. -/
def finiteCoordinateArray (q : ℕ) :
    (∀ j : Fin q, MultilinearMap ℂ (fun _ : Fin j.val => ComplexModel n) ℂ) →ₗ[ℂ]
      (monomialIndex n q → ℂ) where
  toFun J w := J w.1 (fun k => EuclideanSpace.basisFun (Fin n) ℂ (w.2 k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual entire derivative tuple is faithfully detected by finite genuine coordinate evaluations. -/
theorem finiteCoordinateArray_injective (q : ℕ) :
    Function.Injective (finiteCoordinateArray (n := n) q) := by
  intro J K heq
  funext j
  apply Module.Basis.ext_multilinear (fun _ : Fin j.val => (EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
  intro v
  exact congrFun heq (⟨j, v⟩ : monomialIndex n q)

/-- Actual holomorphic translation to the original point, with no translated-germ certificate. -/
theorem translated_holomorphic (p : ComplexModel n) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun w => f (w + p)) z := by
  have htp : Tendsto (fun z : ComplexModel n => z + p) (𝓝 0) (𝓝 p) := by
    have hc : ContinuousAt (fun z : ComplexModel n => z + p) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  filter_upwards [htp.eventually hf] with z hz
  exact hz.comp z (differentiableAt_id.add_const p)

/-- The actual whole germ of the unmodified original function translated at p. -/
def translatedGerm (p : ComplexModel n) (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) : HolGerm (ComplexModel n) :=
  HolGerm.mk (fun z => f (z + p)) (translated_holomorphic p hf)

/-- Every genuine original coordinate jet entry is exactly the original derivative at p. -/
theorem finiteCoordinateArray_translatedGerm (q : ℕ) (p : ComplexModel n)
    {f : ComplexModel n → ℂ} (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z)
    (w : monomialIndex n q) :
    finiteCoordinateArray q (finiteJet q (translatedGerm p f hf)) w =
      iteratedFDeriv ℂ w.1.val f p
        (fun k => EuclideanSpace.basisFun (Fin n) ℂ (w.2 k)) := by
  change iteratedFDeriv ℂ w.1.val (fun z => f (z + p)) 0 _ = _
  rw [iteratedFDeriv_comp_add_right, zero_add]

/-- The genuine iterated chain rule along the actual affine second-variable slice,
using only holomorphicity on the real open joint domain. -/
theorem iteratedFDeriv_affine_slice {D : Set (ComplexModel n × ComplexModel n)}
    (hD : IsOpen D) {F : ComplexModel n × ComplexModel n → ℂ}
    (hF : DifferentiableOn ℂ F D) {p : ComplexModel n} (hp : (p, 0) ∈ D) (j : ℕ) :
    iteratedFDeriv ℂ j (fun z => F (p, z)) 0 =
      (iteratedFDeriv ℂ j F (p, 0)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℂ (ComplexModel n) (ComplexModel n)) := by
  let b : ComplexModel n × ComplexModel n := (p, 0)
  let L := ContinuousLinearMap.inr ℂ (ComplexModel n) (ComplexModel n)
  let Fs : ComplexModel n × ComplexModel n → ℂ := fun u => F (u + b)
  let S : Set (ComplexModel n × ComplexModel n) := (fun u => u + b) ⁻¹' D
  have hS : IsOpen S := hD.preimage (continuous_id.add continuous_const)
  have h0 : (0 : ComplexModel n × ComplexModel n) ∈ S := by simpa [S, b] using hp
  have hAn : AnalyticOnNhd ℂ Fs S := by
    intro u hu
    exact (HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hu).comp
      (f := fun w : ComplexModel n × ComplexModel n => w + b) (x := u)
      (analyticAt_id.add analyticAt_const)
  have hpre : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hL0 : L (0 : ComplexModel n) ∈ S := by simpa only [map_zero] using h0
  have hEq := L.iteratedFDerivWithin_comp_right
    (hAn.contDiffOn hS.uniqueDiffOn (n := (⊤ : ℕ∞ω))) hS.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := j) (by exact le_top)
  have hLeft : ContDiffAt ℂ j (Fs ∘ L) (0 : ComplexModel n) :=
    ((hAn (L 0) hL0).comp (L.analyticAt 0)).contDiffAt.of_le le_top
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hLeft hL0,
    show L (0 : ComplexModel n) = 0 from map_zero L,
    iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn
      ((hAn 0 h0).contDiffAt.of_le le_top) h0] at hEq
  have hslice : Fs ∘ L = fun z => F (p, z) := by
    funext z
    change F ((0, z) + (p, 0)) = F (p, z)
    congr 1
    ext <;> simp
  rw [hslice] at hEq
  simpa only [Fs, iteratedFDeriv_comp_add_right, zero_add, b] using hEq

private def fixedMultilinearEvaluation (j : ℕ)
    (v : Fin j → (ComplexModel n × ComplexModel n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin j => ComplexModel n × ComplexModel n) ℂ →L[ℂ] ℂ where
  toFun A := A v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

/-- True partial derivatives of an original joint holomorphic function vary holomorphically. -/
theorem analyticOnNhd_partial_derivative {U : Set (ComplexModel n)}
    {D : Set (ComplexModel n × ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel n × ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D)
    (hU : ∀ p ∈ U, (p, 0) ∈ D) (j : ℕ) (v : Fin j → ComplexModel n) :
    AnalyticOnNhd ℂ (fun p => iteratedFDeriv ℂ j (fun z => F (p, z)) 0 v) U := by
  have hAn : AnalyticOnNhd ℂ F D := fun _ hx =>
    HolomorphicAnalytic.analyticAt_of_differentiableOn hD hF hx
  intro p hp
  have hDer := (hAn.iteratedFDeriv j) (p, 0) (hU p hp)
  have hSlice : AnalyticAt ℂ (fun p : ComplexModel n => (p, (0 : ComplexModel n))) p :=
    (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel n)).analyticAt p
  have hDerSlice := hDer.comp (f := fun x : ComplexModel n => (x, (0 : ComplexModel n))) (x := p) hSlice
  have hEv := ((fixedMultilinearEvaluation j (fun k => (0, v k))).analyticAt _).comp hDerSlice
  apply hEv.congr
  filter_upwards [hSlice.continuousAt.eventually (hD.mem_nhds (hU p hp))] with x hx
  exact congrArg (fun A : ContinuousMultilinearMap ℂ (fun _ : Fin j => ComplexModel n) ℂ => A v)
    (iteratedFDeriv_affine_slice hD hF hx j).symm

/-- The actual original polynomial of the same finite coordinate word. -/
def wordFunction {q : ℕ} (w : monomialIndex n q) (z : ComplexModel n) : ℂ :=
  ∏ k : Fin w.1.val, z (w.2 k)

theorem differentiable_wordFunction {q : ℕ} (w : monomialIndex n q) :
    Differentiable ℂ (wordFunction w) := by
  unfold wordFunction
  fun_prop

/-- Original coordinate products represent exactly the previously proved whole word germs. -/
theorem wordMonomial_eq_mk {q : ℕ} (w : monomialIndex n q) :
    wordMonomial w = HolGerm.mk (wordFunction w)
      (Eventually.of_forall (differentiable_wordFunction w)) := by
  apply Subtype.ext
  rw [wordMonomial, HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [coordinateGerm, HolGerm.coe_mk]
  have h := map_prod (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) :
    (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ)
    (fun k : Fin w.1.val => fun z : ComplexModel n => z (w.2 k)) Finset.univ
  rw [show wordFunction w = (fun z : ComplexModel n => ∏ k : Fin w.1.val, z (w.2 k)) from rfl]
  simpa only [Germ.coe_coeRingHom, Finset.prod_fn] using h.symm

/-- The genuine original joint word-times-translated-generator function. -/
def jointColumn {q : ℕ} (w : monomialIndex n q) (f : ComplexModel n → ℂ)
    (u : ComplexModel n × ComplexModel n) : ℂ := wordFunction w u.2 * f (u.2 + u.1)

/-- Every actual original joint column is holomorphic on its true open sum domain. -/
theorem differentiableOn_jointColumn {q : ℕ} (w : monomialIndex n q)
    {U : Set (ComplexModel n)} (hU : IsOpen U) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (jointColumn w f) {u : ComplexModel n × ComplexModel n | u.2 + u.1 ∈ U} := by
  intro u hu
  exact ((differentiable_wordFunction w).differentiableAt.comp u differentiableAt_snd).mul
    ((hf.differentiableAt (hU.mem_nhds hu)).comp u (differentiableAt_snd.add differentiableAt_fst))
      |>.differentiableWithinAt

/-- Actual finite Macaulay coordinate columns vary holomorphically on the original open domain. -/
theorem analyticOnNhd_original_macaulay_column {q : ℕ} (w : monomialIndex n q)
    {U : Set (ComplexModel n)} (hU : IsOpen U) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f U) (j : ℕ) (v : Fin j → ComplexModel n) :
    AnalyticOnNhd ℂ (fun p =>
      iteratedFDeriv ℂ j (fun z => wordFunction w z * f (z + p)) 0 v) U := by
  exact analyticOnNhd_partial_derivative
    (hU.preimage (continuous_snd.add continuous_fst))
    (differentiableOn_jointColumn w hU hf) (fun p hp => by
      change (0 : ComplexModel n) + p ∈ U
      simpa only [zero_add] using hp) j v

/-- The same original joint function represents each whole-ring word-times-generator column. -/
theorem finiteCoordinateArray_original_macaulay_column {q : ℕ}
    (w a : monomialIndex n q) (p : ComplexModel n) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) :
    finiteCoordinateArray q (finiteJet q (wordMonomial w * translatedGerm p f hf)) a =
      iteratedFDeriv ℂ a.1.val (fun z => wordFunction w z * f (z + p)) 0
        (fun k => EuclideanSpace.basisFun (Fin n) ℂ (a.2 k)) := by
  rw [wordMonomial_eq_mk, translatedGerm, ← HolGerm.mk_mul]
  rfl

/-- The finite actual scalar matrix of original word-times-generator derivative columns. -/
def originalMacaulayMatrix (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ)
    (p : ComplexModel n) : Matrix (monomialIndex n q) (monomialIndex n q × ι) ℂ :=
  fun a b => iteratedFDeriv ℂ a.1.val (fun z => wordFunction b.1 z * G b.2 (z + p)) 0
    (fun k => EuclideanSpace.basisFun (Fin n) ℂ (a.2 k))

/-- Each genuine original finite matrix entry is holomorphic on the same original open domain. -/
theorem differentiableOn_originalMacaulayMatrix_entry (q : ℕ) {ι : Type*}
    (G : ι → ComplexModel n → ℂ) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    (a : monomialIndex n q) (b : monomialIndex n q × ι) :
    DifferentiableOn ℂ (fun p => originalMacaulayMatrix q G p a b) U :=
  (analyticOnNhd_original_macaulay_column b.1 hU (hG b.2) a.1.val
    (fun k => EuclideanSpace.basisFun (Fin n) ℂ (a.2 k))).differentiableOn

/-- The actual finite scalar Macaulay matrix as a genuine complex linear map. -/
def originalMacaulayLinearMap (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n) :
    ((monomialIndex n q × ι) → ℂ) →ₗ[ℂ] (monomialIndex n q → ℂ) :=
  Fintype.linearCombination ℂ (fun b a => originalMacaulayMatrix q G p a b)

/-- The original holomorphic matrix is exactly the finite coordinate evaluation
of the true whole-germ Macaulay map. -/
theorem originalMacaulayLinearMap_eq (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    originalMacaulayLinearMap q G p = (finiteCoordinateArray q).comp
      (macaulayMap q (fun i => translatedGerm p (G i) (hG i))) := by
  ext c a
  change (∑ b : monomialIndex n q × ι, c b • (fun a => originalMacaulayMatrix q G p a b)) a =
    finiteCoordinateArray q (∑ b : monomialIndex n q × ι,
      c b • finiteJet q (wordMonomial b.1 * translatedGerm p (G b.2) (hG b.2))) a
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteCoordinateArray_original_macaulay_column]
  rfl

/-- The entire genuine ideal of the original functions translated at the original point. -/
def translatedIdeal {ι : Type*} (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (range fun i => translatedGerm p (G i) (hG i))

/-- The literal entire original point quotient is given by the genuine original holomorphic matrix rank. -/
theorem hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    hilbertSamuelValue (translatedIdeal G p hG) ℓ =
      Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) -
        Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ + 1) G p)) := by
  rw [translatedIdeal, hilbertSamuelValue_eq_macaulay_rank]
  congr 1
  rw [originalMacaulayLinearMap_eq (ℓ + 1) G p hG, LinearMap.range_comp]
  exact ((LinearMap.range (macaulayMap (ℓ + 1) (fun i => translatedGerm p (G i) (hG i)))).equivMapOfInjective
    (finiteCoordinateArray (ℓ + 1)) (finiteCoordinateArray_injective (ℓ + 1))).finrank_eq


/-- The actual complex-bilinear coordinate functional of a finite scalar array. -/
def scalarArrayToDual {A : Type*} [Fintype A] :
    (A → ℂ) →ₗ[ℂ] (ComplexModel (Fintype.card A) →L[ℂ] ℂ) where
  toFun v := ∑ a, v a • EuclideanSpace.proj ((Fintype.equivFin A) a)
  map_add' v w := by
    classical
    ext z
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    classical
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Actual coordinate evaluation recovers each original array entry. -/
theorem scalarArrayToDual_coordinateDirection {A : Type*} [Fintype A]
    (v : A → ℂ) (a : A) :
    scalarArrayToDual v
      (AnalyticJacobianSingularCore.coordinateDirection ((Fintype.equivFin A) a)) = v a := by
  classical
  simp [scalarArrayToDual, AnalyticJacobianSingularCore.coordinateDirection,
    PiLp.single_apply, (Fintype.equivFin A).injective.eq_iff]

/-- The true coordinate-functional map is injective, including the empty array. -/
theorem scalarArrayToDual_injective {A : Type*} [Fintype A] :
    Function.Injective (scalarArrayToDual (A := A)) := by
  intro v w h
  funext a
  simpa only [scalarArrayToDual_coordinateDirection] using
    congrArg (fun L => L (AnalyticJacobianSingularCore.coordinateDirection
      ((Fintype.equivFin A) a))) h

/-- The actual range rank of a finite scalar column matrix is detected exactly by all square minors. -/
theorem finite_column_rank_lt_iff_minors_eq_zero {A B : Type*} [Fintype A] [Fintype B]
    (M : Matrix A B ℂ) (r : ℕ) :
    Module.finrank ℂ (LinearMap.range (Fintype.linearCombination ℂ (fun b a => M a b))) < r ↔
      ∀ (rows : Fin r → A) (cols : Fin r → B),
        (Matrix.of fun i j => M (rows i) (cols j)).det = 0 := by
  let C : B → (A → ℂ) := fun b a => M a b
  let L : Fin (Fintype.card B) → (ComplexModel (Fintype.card A) →L[ℂ] ℂ) :=
    fun k => scalarArrayToDual (C ((Fintype.equivFin B).symm k))
  have hrange : range L = scalarArrayToDual '' range C := by
    ext K
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨(Fintype.equivFin B).symm k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨(Fintype.equivFin B) b, by simp [L]⟩
  have hspan : Submodule.span ℂ (range L) = (Submodule.span ℂ (range C)).map scalarArrayToDual := by
    rw [Submodule.map_span, hrange]
  have hdim : Module.finrank ℂ (Submodule.span ℂ (range L)) =
      Module.finrank ℂ (Submodule.span ℂ (range C)) := by
    rw [hspan]
    exact ((Submodule.span ℂ (range C)).equivMapOfInjective scalarArrayToDual
      scalarArrayToDual_injective).finrank_eq.symm
  rw [Fintype.range_linearCombination]
  change Module.finrank ℂ (Submodule.span ℂ (range C)) < r ↔ _
  rw [← hdim, RankDegeneracy.finrank_span_lt_iff_minors_eq_zero]
  constructor
  · intro h rows cols
    have hh := h (fun i => (Fintype.equivFin B) (cols i))
      (fun j => (Fintype.equivFin A) (rows j))
    have heq : (Matrix.of fun i j =>
        L ((Fintype.equivFin B) (cols i))
          (AnalyticJacobianSingularCore.coordinateDirection ((Fintype.equivFin A) (rows j)))) =
        (Matrix.of fun i j => M (rows i) (cols j)).transpose := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, L, Equiv.symm_apply_apply,
        scalarArrayToDual_coordinateDirection, C]
    rw [heq, Matrix.det_transpose] at hh
    exact hh
  · intro h rows cols
    have hh := h (fun j => (Fintype.equivFin A).symm (cols j))
      (fun i => (Fintype.equivFin B).symm (rows i))
    have heq : (Matrix.of fun i j => L (rows i)
        (AnalyticJacobianSingularCore.coordinateDirection (cols j))) =
        (Matrix.of fun i j => M ((Fintype.equivFin A).symm (cols i))
          ((Fintype.equivFin B).symm (rows j))).transpose := by
      ext i j
      have hcoord := scalarArrayToDual_coordinateDirection
        (C ((Fintype.equivFin B).symm (rows i))) ((Fintype.equivFin A).symm (cols j))
      simpa only [Matrix.of_apply, Matrix.transpose_apply, L, C, Equiv.apply_symm_apply]
        using hcoord
    rw [heq, Matrix.det_transpose]
    exact hh


/-- The true finite original Macaulay minor, formed from its actual holomorphic entries. -/
def originalMacaulayMinor (q : ℕ) {ι : Type*} (G : ι → ComplexModel n → ℂ)
    {s : ℕ} (rows : Fin s → monomialIndex n q)
    (cols : Fin s → monomialIndex n q × ι) (p : ComplexModel n) : ℂ :=
  (Matrix.of fun i j => originalMacaulayMatrix q G p (rows i) (cols j)).det

/-- Every actual original finite Macaulay minor is holomorphic on the same original domain. -/
theorem differentiableOn_originalMacaulayMinor (q : ℕ) {ι : Type*}
    (G : ι → ComplexModel n → ℂ) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) {s : ℕ}
    (rows : Fin s → monomialIndex n q) (cols : Fin s → monomialIndex n q × ι) :
    DifferentiableOn ℂ (originalMacaulayMinor q G rows cols) U := by
  have hdet : originalMacaulayMinor q G rows cols = fun p =>
      ∑ σ : Equiv.Perm (Fin s), Equiv.Perm.sign σ •
        ∏ a : Fin s, originalMacaulayMatrix q G p (rows (σ a)) (cols a) := by
    funext p
    simp only [originalMacaulayMinor, Matrix.det_apply, Matrix.of_apply]
  rw [hdet]
  have hsum : DifferentiableOn ℂ
      (∑ σ : Equiv.Perm (Fin s), fun p => Equiv.Perm.sign σ •
        ∏ a : Fin s, originalMacaulayMatrix q G p (rows (σ a)) (cols a)) U := by
    refine DifferentiableOn.sum (𝕜 := ℂ) (E := ComplexModel n) (F := ℂ)
      (u := (Finset.univ : Finset (Equiv.Perm (Fin s))))
      (A := fun σ p => Equiv.Perm.sign σ •
        ∏ a : Fin s, originalMacaulayMatrix q G p (rows (σ a)) (cols a)) fun σ _ => ?_
    refine (PureDimension.differentiableOn_finset_prod Finset.univ
      (fun a p => originalMacaulayMatrix q G p (rows (σ a)) (cols a)) U ?_).const_smul _
    intro a _
    exact differentiableOn_originalMacaulayMatrix_entry q G hU hG _ _
  refine hsum.congr fun p _ => ?_
  exact (Finset.sum_apply p Finset.univ (fun σ : Equiv.Perm (Fin s) => fun p =>
    Equiv.Perm.sign σ • ∏ a : Fin s,
      originalMacaulayMatrix q G p (rows (σ a)) (cols a))).symm

/-- The actual whole-ideal matrix rank is bounded by the entire finite-jet image dimension. -/
theorem finrank_originalMacaulayLinearMap_le (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q G p)) ≤
      Module.finrank ℂ (LinearMap.range (finiteJet (n := n) q)) := by
  rw [originalMacaulayLinearMap_eq q G p hG, LinearMap.range_comp]
  have he := ((LinearMap.range (macaulayMap q (fun i => translatedGerm p (G i) (hG i)))).equivMapOfInjective
    (finiteCoordinateArray q) (finiteCoordinateArray_injective q)).finrank_eq
  rw [← he, range_macaulayMap]
  apply Submodule.finrank_mono
  rintro v ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

/-- A genuine literal whole-ideal point-value threshold is exactly the vanishing of the actual minors. -/
theorem hilbertSamuelValue_translatedIdeal_ge_iff_minors (ℓ r : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z)
    (hr : r ≤ Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1)))) :
    r ≤ hilbertSamuelValue (translatedIdeal G p hG) ℓ ↔
      ∀ (rows : Fin (Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) - r + 1) →
          monomialIndex n (ℓ + 1))
        (cols : Fin (Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) - r + 1) →
          monomialIndex n (ℓ + 1) × ι),
        originalMacaulayMinor (ℓ + 1) G rows cols p = 0 := by
  have hle := finrank_originalMacaulayLinearMap_le (ℓ + 1) G p hG
  rw [hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank]
  have hnat : (r ≤ Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) -
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ + 1) G p))) ↔
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ + 1) G p)) <
        Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) - r + 1 := by omega
  rw [hnat]
  exact finite_column_rank_lt_iff_minors_eq_zero (originalMacaulayMatrix (ℓ + 1) G p) _

/-- Actual finite holomorphic equations for every literal whole-ideal point-value superlevel. -/
theorem exists_hilbertSamuelValue_superlevel_equations (ℓ r : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → ComplexModel n → ℂ) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hG : ∀ i, DifferentiableOn ℂ (G i) U) :
    ∃ (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
      (∀ i, DifferentiableOn ℂ (F i) U) ∧
      ∀ (p : ComplexModel n) (hp : p ∈ U),
        r ≤ hilbertSamuelValue (translatedIdeal G p
          (fun i => (show ∀ᶠ z in 𝓝 p, z ∈ U from hU.mem_nhds hp).mono fun _z hz =>
            (hG i).differentiableAt (hU.mem_nhds hz))) ℓ ↔ ∀ i, F i p = 0 := by
  classical
  let d := Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1)))
  by_cases hr : r ≤ d
  · let S := (Fin (d - r + 1) → monomialIndex n (ℓ + 1)) ×
      (Fin (d - r + 1) → monomialIndex n (ℓ + 1) × ι)
    let F : Fin (Fintype.card S) → ComplexModel n → ℂ := fun i =>
      originalMacaulayMinor (ℓ + 1) G ((Fintype.equivFin S).symm i).1
        ((Fintype.equivFin S).symm i).2
    refine ⟨Fintype.card S, F, fun i => differentiableOn_originalMacaulayMinor
      (ℓ + 1) G hU hG _ _, ?_⟩
    intro p hp
    rw [hilbertSamuelValue_translatedIdeal_ge_iff_minors ℓ r G p _ hr]
    constructor
    · intro h i
      exact h _ _
    · intro h rows cols
      simpa only [F, Equiv.symm_apply_apply] using h ((Fintype.equivFin S) (rows, cols))
  · refine ⟨1, fun _ _ => 1, fun _ => differentiableOn_const (1 : ℂ), ?_⟩
    intro p hp
    rw [hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank]
    constructor
    · intro h
      have hh : r ≤ d := h.trans (Nat.sub_le _ _)
      exact (hr hh).elim
    · intro h
      exact (one_ne_zero (h 0)).elim


/-- The genuine coordinate translation at the original point. -/
def translationEquiv (p : ComplexModel n) : LocalHolomorphicEquivAt (n := n) p where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ p
  toFun := fun z => z - p
  invFun := fun z => z + p
  toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun z _ => sub_add_cancel z p
  right_inv := fun z _ => add_sub_cancel_right z p

/-- Full finite original span is exactly full whole-ring span after the actual translation. -/
theorem isInSpanAt_iff_translatedGerm_mem {s : ℕ} (G : Fin s → ComplexModel n → ℂ)
    (p : ComplexModel n) (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z)
    {F : ComplexModel n → ℂ} (hF : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ F z) :
    HolomorphicIdealSheaves.IsInSpanAt (n := n) (· ∈ range G) p F ↔
      translatedGerm p F hF ∈ translatedIdeal G p hG := by
  have h := LocalHolomorphicFiniteSpanTransport.isInSpanAt_comp_inv_iff (translationEquiv p) G F
  have ht : (translationEquiv p).toFun p = 0 := sub_self p
  rw [ht] at h
  exact h.trans (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
    (fun i z => G i (z + p)) (fun i => translated_holomorphic p (hG i))
    (translated_holomorphic p hF))

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
open HolomorphicIdealSheaves

/-- The entire original holomorphic function read in the actual chart and translated at the nearby point. -/
def chartTranslatedGerm (x y : M) (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (f : M → ℂ) (hf : HolomorphicAt n f y) : HolGerm (ComplexModel n) :=
  translatedGerm ((chartAt (ComplexModel n) x) y)
    (fun z => f ((chartAt (ComplexModel n) x).symm z))
    (CartanLocalReduction.holAt_comp_chart_symm hy hf)

/-- The actual complete original stalk ideal in this fixed genuine chart,
formed from all literal original membership germs. -/
def wholeChartStalkIdeal (𝔞 : GermIdeal n M) (x y : M)
    (hy : y ∈ (chartAt (ComplexModel n) x).source) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span {g | ∃ (f : M → ℂ) (hf : HolomorphicAt n f y),
    𝔞.mem y f ∧ g = chartTranslatedGerm x y hy f hf}

/-- Coherence internally produces one actual original family and the exact entire stalk
ideal dictionary at every nearby point of one original chart. -/
theorem exists_coherent_whole_stalk_original_columns (𝔞 : GermIdeal n M) (h𝔞 : 𝔞.IsCoherent)
    (x : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hx : x ∈ U) (s : ℕ) (G : Fin s → M → ℂ),
      ∃ hsource : U ⊆ (chartAt (ComplexModel n) x).source,
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) U) ∧
      ∀ (y : M) (hy : y ∈ U),
        let hchart : y ∈ (chartAt (ComplexModel n) x).source := hsource hy
        ∃ hG : ∀ i, ∀ᶠ z in 𝓝 ((chartAt (ComplexModel n) x) y),
          DifferentiableAt ℂ (fun w => G i ((chartAt (ComplexModel n) x).symm w)) z,
          (∀ (f : M → ℂ) (hf : HolomorphicAt n f y),
            𝔞.mem y f ↔ chartTranslatedGerm x y hchart f hf ∈
              translatedIdeal (fun i z => G i ((chartAt (ComplexModel n) x).symm z))
                ((chartAt (ComplexModel n) x) y) hG) ∧
          wholeChartStalkIdeal 𝔞 x y hchart =
            translatedIdeal (fun i z => G i ((chartAt (ComplexModel n) x).symm z))
              ((chartAt (ComplexModel n) x) y) hG := by
  classical
  obtain ⟨U₀, hU₀, hxU₀, s, G, hG, hspan⟩ := h𝔞 x
  let U := U₀ ∩ (chartAt (ComplexModel n) x).source
  have hU : IsOpen U := hU₀.inter (chartAt (ComplexModel n) x).open_source
  have hx : x ∈ U := ⟨hxU₀, mem_chart_source (ComplexModel n) x⟩
  refine ⟨U, hU, hx, s, G, inter_subset_right, fun i => (hG i).mono inter_subset_left, ?_⟩
  intro y hy
  have hyc : y ∈ (chartAt (ComplexModel n) x).source := hy.2
  have hGhol (i : Fin s) : HolomorphicAt n (G i) y :=
    (show ∀ᶠ z in 𝓝 y, z ∈ U₀ from hU₀.mem_nhds hy.1).mono fun _z hz =>
      (hG i).mdifferentiableAt (hU₀.mem_nhds hz)
  let H : Fin s → ComplexModel n → ℂ := fun i z => G i ((chartAt (ComplexModel n) x).symm z)
  have hH (i : Fin s) : ∀ᶠ z in 𝓝 ((chartAt (ComplexModel n) x) y), DifferentiableAt ℂ (H i) z :=
    CartanLocalReduction.holAt_comp_chart_symm hyc (hGhol i)
  have hbridge (f : M → ℂ) (hf : HolomorphicAt n f y) :
      𝔞.mem y f ↔ chartTranslatedGerm x y hyc f hf ∈
        translatedIdeal H ((chartAt (ComplexModel n) x) y) hH :=
    (hspan y hy.1 f).trans
      ((ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff hyc G f).trans
        (isInSpanAt_iff_translatedGerm_mem H _ hH
          (CartanLocalReduction.holAt_comp_chart_symm hyc hf)))
  refine ⟨hH, hbridge, ?_⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨f, hf, hmem, rfl⟩
    exact (hbridge f hf).mp hmem
  · apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    apply Ideal.subset_span
    refine ⟨G i, hGhol i, ?_, rfl⟩
    exact (hspan y hy.1 (G i)).mpr (CoherentIdealColon.isInSpanAt_range_self hGhol i)


/-- An original coherent ideal internally receives actual finite holomorphic equations
for its literal entire nearby stalk-quotient superlevel in one genuine original chart. -/
theorem exists_coherent_whole_stalk_superlevel_equations (𝔞 : GermIdeal n M)
    (h𝔞 : 𝔞.IsCoherent) (x : M) (ℓ r : ℕ) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hx : x ∈ U)
      (hsource : U ⊆ (chartAt (ComplexModel n) x).source)
      (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
      (∀ i, DifferentiableOn ℂ (F i)
        ((chartAt (ComplexModel n) x).target ∩ (chartAt (ComplexModel n) x).symm ⁻¹' U)) ∧
      ∀ (y : M) (hy : y ∈ U),
        r ≤ hilbertSamuelValue (wholeChartStalkIdeal 𝔞 x y (hsource hy)) ℓ ↔
          ∀ i, F i ((chartAt (ComplexModel n) x) y) = 0 := by
  obtain ⟨U, hU, hx, s, G, hsource, hGM, hdict⟩ :=
    exists_coherent_whole_stalk_original_columns 𝔞 h𝔞 x
  let e := chartAt (ComplexModel n) x
  let V := e.target ∩ e.symm ⁻¹' U
  let H : Fin s → ComplexModel n → ℂ := fun i z => G i (e.symm z)
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hH : ∀ i, DifferentiableOn ℂ (H i) V := fun i z hz =>
    (StokesSingularLocusAnalytic.differentiableAt_chart (complexChartAt (n := n) x) hz.1
      ((hGM i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  obtain ⟨N, F, hF, hEq⟩ := exists_hilbertSamuelValue_superlevel_equations ℓ r H hV hH
  refine ⟨U, hU, hx, hsource, N, F, hF, ?_⟩
  intro y hy
  have hyV : e y ∈ V := by
    refine ⟨e.map_source (hsource hy), ?_⟩
    change e.symm (e y) ∈ U
    simpa only [e.left_inv (hsource hy)] using hy
  obtain ⟨hHpoint, _, hwhole⟩ := hdict y hy
  rw [hwhole]
  exact hEq (e y) hyV

end Manifold
end
end Hironaka.HironakaHolomorphicJetRankLoci
