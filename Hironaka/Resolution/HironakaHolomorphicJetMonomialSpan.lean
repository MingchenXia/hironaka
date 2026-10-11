/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicGermDifferentiableSubtraction
import Hironaka.Resolution.HironakaHolomorphicPointJets
import Hironaka.Analytic.CoordinatePlaneDivision
import Hironaka.Analytic.HolomorphicGermNoetherian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-! # Actual finite monomial representatives and whole-ideal Macaulay jets

Every entire original holomorphic germ receives an internally constructed
finite original coordinate-word representative modulo the actual maximal-ideal
power. Whole generated ideals have exactly the finite real word-times-generator
jet columns. Genuine Noetherianity produces original generators for every ideal,
and the literal whole quotient Hilbert--Samuel value equals actual Macaulay rank.
Normal-flat centres, HS transformation and higher-entry finite descent remain open.
Blueprint: `hironaka-holomorphic-jet-monomial-span-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaHolomorphicJetMonomialSpan
open Hironaka.HolomorphicIdealSheaves HolGerm
open HironakaHolomorphicPointJets
open Hironaka
noncomputable section
variable {n : ℕ}

private theorem coordinate_holomorphic (i : Fin n) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun w : ComplexModel n => w i) z :=
  Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt

/-- Actual original coordinate germ. -/
def coordinateGerm (i : Fin n) : HolGerm (ComplexModel n) :=
  HolGerm.mk (fun z : ComplexModel n => z i) (coordinate_holomorphic i)

/-- A finite word of coordinates of degree strictly below q. -/
def monomialIndex (n q : ℕ) := Σ j : Fin q, (Fin j.val → Fin n)

instance fintypeMonomialIndex (n q : ℕ) : Fintype (monomialIndex n q) := inferInstanceAs (Fintype (Σ j : Fin q, Fin j.val → Fin n))

/-- The genuine whole-ring product of original coordinate germs. -/
def wordMonomial {q : ℕ} (w : monomialIndex n q) : HolGerm (ComplexModel n) :=
  ∏ k : Fin w.1.val, coordinateGerm (w.2 k)

/-- Actual complex span of all finite original words below q. -/
def monomialSpan (n q : ℕ) : Submodule ℂ (HolGerm (ComplexModel n)) :=
  Submodule.span ℂ (range (wordMonomial (n := n) (q := q)))

/-- Original holomorphic Hadamard coefficients, internally passed to whole germs. -/
theorem exists_coordinate_decomposition (g : HolGerm (ComplexModel n)) :
    ∃ h : Fin n → HolGerm (ComplexModel n),
      g = HolGerm.constHom (HolGerm.eval g) + ∑ i : Fin n, coordinateGerm i * h i := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  let F : ComplexModel n → ℂ := fun z => f z - f 0
  have hF := eventually_differentiableAt_sub hf (eventually_differentiableAt_const (f 0))
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ complexCoordinatePlane n 0 → F z = 0 := by
    filter_upwards [] with z hz
    have hz0 : z = 0 := by
      ext i
      exact hz i (Nat.zero_le _)
    simp [F, hz0]
  obtain ⟨H, -, hH, heq⟩ := CoordinatePlaneDivision.exists_eq_sum_coord_mul
    n 0 (by omega) (fun _ _ => rfl) hF hvan
  refine ⟨fun i => HolGerm.mk (H i) (hH i), ?_⟩
  have hsum := eventually_differentiableAt_sum Finset.univ fun i =>
    eventually_differentiableAt_mul (coordinate_holomorphic i) (hH i)
  have he : HolGerm.mk F hF = ∑ i : Fin n, coordinateGerm i * HolGerm.mk (H i) (hH i) := by
    calc
      HolGerm.mk F hF = HolGerm.mk (fun z => ∑ i : Fin n, z i * H i z) hsum :=
        HolGerm.mk_eq_mk_iff.mpr heq
      _ = _ := by
        rw [HolGerm.mk_sum Finset.univ (fun i z => z i * H i z)
          (fun i => eventually_differentiableAt_mul
            (coordinate_holomorphic i) (hH i))]
        exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  change HolGerm.mk f hf = HolGerm.constHom (f 0) + _
  have hsub : HolGerm.mk F hF = HolGerm.mk f hf - HolGerm.constHom (f 0) := rfl
  rw [hsub] at he
  rw [← he]
  ring

/-- The actual degree-zero word is the genuine unit. -/
theorem one_mem_monomialSpan (q : ℕ) : (1 : HolGerm (ComplexModel n)) ∈ monomialSpan n (q + 1) := by
  apply Submodule.subset_span
  refine ⟨⟨⟨0, by omega⟩, Fin.elim0⟩, ?_⟩
  simp [wordMonomial]

/-- Prefixing the actual original word produces the coordinate-span step. -/
theorem coordinate_mul_mem_monomialSpan {q : ℕ} (i : Fin n)
    {p : HolGerm (ComplexModel n)} (hp : p ∈ monomialSpan n q) :
    coordinateGerm i * p ∈ monomialSpan n (q + 1) := by
  apply Submodule.span_induction (p := fun p _ => coordinateGerm i * p ∈ monomialSpan n (q + 1))
    ?_ ?_ ?_ ?_ hp
  · rintro p ⟨⟨j, w⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨⟨j.val + 1, by omega⟩, Fin.cons i w⟩, ?_⟩
    simp [wordMonomial, Fin.prod_univ_succ]
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro c p _ hp
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hp

section
attribute [local instance 1001] SubsemiringClass.toAddSubmonoidClass

/-- Internally constructed finite original coordinate representative of every germ. -/
theorem exists_monomial_representative (q : ℕ) (g : HolGerm (ComplexModel n)) :
    ∃ p ∈ monomialSpan n q,
      g - p ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  induction q generalizing g with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ q ih =>
    obtain ⟨h, hg⟩ := exists_coordinate_decomposition g
    choose p hp hrem using fun i => ih (h i)
    let P : HolGerm (ComplexModel n) := HolGerm.constHom (HolGerm.eval g) + ∑ i : Fin n, coordinateGerm i * p i
    refine ⟨P, ?_, ?_⟩
    · apply Submodule.add_mem
      · have hconst : HolGerm.constHom (HolGerm.eval g) = HolGerm.eval g • (1 : HolGerm (ComplexModel n)) := by
          rw [Algebra.smul_def]
          simp only [mul_one]
          rfl
        rw [hconst]
        exact Submodule.smul_mem _ _ (one_mem_monomialSpan q)
      · exact Submodule.sum_mem _ fun i _ => coordinate_mul_mem_monomialSpan i (hp i)
    · have he : g - P = ∑ i : Fin n, coordinateGerm i * (h i - p i) := by
        rw [hg]
        dsimp [P]
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
      rw [he, pow_succ']
      apply Ideal.sum_mem
      intro i _
      apply Ideal.mul_mem_mul
      · apply (HolGerm.mem_maximalIdeal_iff _).mpr
        rfl
      · exact hrem i

end

/-- The genuine entire jet image is the finite actual coordinate-word span. -/
theorem range_finiteJet_eq_span_monomials (q : ℕ) :
    LinearMap.range (finiteJet (n := n) q) = Submodule.span ℂ
      (range fun w : monomialIndex n q => finiteJet q (wordMonomial w)) := by
  let J := finiteJet (n := n) q
  have hmap : (monomialSpan n q).map J = Submodule.span ℂ
      (range fun w : monomialIndex n q => J (wordMonomial w)) := by
    rw [monomialSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  apply le_antisymm
  · rintro v ⟨g, rfl⟩
    obtain ⟨p, hp, hrem⟩ := exists_monomial_representative q g
    have hker : g - p ∈ LinearMap.ker J := by
      rw [ker_finiteJet]
      exact hrem
    have he : J g = J p := by
      have h0 := LinearMap.mem_ker.mp hker
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [he, ← hmap]
    exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact LinearMap.mem_range_self _ _

private theorem finiteJet_mul_mem_monomial_columns (q : ℕ)
    (a h : HolGerm (ComplexModel n)) :
    finiteJet q (a * h) ∈ Submodule.span ℂ
      (range fun w : monomialIndex n q => finiteJet q (wordMonomial w * h)) := by
  let J := finiteJet (n := n) q
  let C := Submodule.span ℂ (range fun w : monomialIndex n q => J (wordMonomial w * h))
  obtain ⟨p, hp, hrem⟩ := exists_monomial_representative q a
  have hzer : J ((a - p) * h) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_finiteJet]
    exact Ideal.mul_mem_right h _ hrem
  have heq : J (a * h) = J (p * h) := by
    rw [sub_mul, map_sub, sub_eq_zero] at hzer
    exact hzer
  rw [heq]
  change J (p * h) ∈ C
  apply Submodule.span_induction (p := fun p _ => J (p * h) ∈ C) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [add_mul, map_add]
    exact Submodule.add_mem _ hx hy
  · intro c p _ hp
    rw [smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ _ hp

/-- True entire ring-ideal image equals the finite actual word-times-generator columns. -/
theorem map_span_ideal_finiteJet_eq_monomial_columns (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel n)) :
    ((Ideal.span (range G)).restrictScalars ℂ).map (finiteJet q) = Submodule.span ℂ
      (range fun b : monomialIndex n q × ι => finiteJet q (wordMonomial b.1 * G b.2)) := by
  classical
  let J := finiteJet (n := n) q
  let C := Submodule.span ℂ
    (range fun b : monomialIndex n q × ι => J (wordMonomial b.1 * G b.2))
  apply le_antisymm
  · rintro v ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    rw [← ha, map_sum]
    apply Submodule.sum_mem
    intro i _
    have hle : Submodule.span ℂ
        (range fun w : monomialIndex n q => J (wordMonomial w * G i)) ≤ C := by
      apply Submodule.span_le.mpr
      rintro v ⟨w, rfl⟩
      exact Submodule.subset_span ⟨(w, i), rfl⟩
    exact hle (finiteJet_mul_mem_monomial_columns q (a i) (G i))
  · apply Submodule.span_le.mpr
    rintro v ⟨b, rfl⟩
    exact Submodule.mem_map.mpr ⟨wordMonomial b.1 * G b.2,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := b.2)), rfl⟩

/-- Internally selected original holomorphic generators give exact finite columns
for every actual ideal, simultaneously at every jet degree. -/
theorem exists_original_generators_jet_columns (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ (r : ℕ) (G : Fin r → ComplexModel n → ℂ)
      (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z),
      Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I ∧
      ∀ q : ℕ, (I.restrictScalars ℂ).map (finiteJet q) = Submodule.span ℂ
        (range fun b : monomialIndex n q × Fin r =>
          finiteJet q (wordMonomial b.1 * HolGerm.mk (G b.2) (hG b.2))) := by
  let := isNoetherianRing_holGerm_euclidean n
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  choose G hG hrep using fun i => HolGerm.exists_eq_mk (g i)
  have heq : (fun i => HolGerm.mk (G i) (hG i)) = g := funext fun i => (hrep i).symm
  have hspan : Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I := by
    rw [heq]
    exact hg
  refine ⟨r, G, hG, hspan, ?_⟩
  intro q
  rw [← hspan]
  exact map_span_ideal_finiteJet_eq_monomial_columns q _

/-- Actual second quotient of the whole finite-jet map gives the literal dimension. -/
theorem finrank_quotient_eq_jet_rank_sub_ideal_image_rank (q : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) =
      Module.finrank ℂ (LinearMap.range (finiteJet (n := n) q)) -
        Module.finrank ℂ ((I.restrictScalars ℂ).map (finiteJet q)) := by
  let J := finiteJet (n := n) q
  let V := LinearMap.range J
  let W := (I.restrictScalars ℂ).map J.rangeRestrict
  let F := W.mkQ.comp J.rangeRestrict
  have hsurj : Function.Surjective F := W.mkQ_surjective.comp J.surjective_rangeRestrict
  have hker : LinearMap.ker F =
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).restrictScalars ℂ := by
    ext g
    rw [LinearMap.mem_ker]
    change W.mkQ (J.rangeRestrict g) = 0 ↔ g ∈ I ⊔ _
    change J.rangeRestrict g ∈ LinearMap.ker W.mkQ ↔ _
    rw [Submodule.ker_mkQ]
    constructor
    · intro hg
      obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp hg
      have hzero : J (g - a) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr (congrArg Subtype.val he).symm
      have hrem : g - a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
        have hz := LinearMap.mem_ker.mpr hzero
        rw [ker_finiteJet] at hz
        exact hz
      have ha' : a ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q :=
        (show I ≤ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q from le_sup_left) ha
      have hr' : g - a ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q :=
        (show IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≤
          I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q from le_sup_right) hrem
      have := Ideal.add_mem _ ha' hr'
      simpa only [add_sub_cancel] using this
    · intro hg
      obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hg
      have hz : J b = 0 := by
        apply LinearMap.mem_ker.mp
        rw [ker_finiteJet]
        exact hb
      apply Submodule.mem_map.mpr
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      change J a = J g
      rw [← he, map_add, hz, add_zero]
  have hdim : Module.finrank ℂ (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) =
      Module.finrank ℂ (V ⧸ W) := by
    have he := (F.quotKerEquivOfSurjective hsurj).finrank_eq
    rw [hker] at he
    exact he
  have hmap : W.map V.subtype = (I.restrictScalars ℂ).map J := by
    change ((I.restrictScalars ℂ).map J.rangeRestrict).map V.subtype = _
    rw [← Submodule.map_comp]
    rfl
  have hw : Module.finrank ℂ W = Module.finrank ℂ ((I.restrictScalars ℂ).map J) := by
    rw [← hmap]
    exact (W.equivMapOfInjective V.subtype Subtype.val_injective).finrank_eq
  have hsum : Module.finrank ℂ (V ⧸ W) + Module.finrank ℂ W = Module.finrank ℂ V :=
    Submodule.finrank_quotient_add_finrank W
  rw [hdim, ← hw]
  change Module.finrank ℂ (V ⧸ W) = Module.finrank ℂ V - Module.finrank ℂ W
  omega

/-- The genuine finite matrix-column linear map on actual complex coefficient vectors. -/
def macaulayMap (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel n)) :
    ((monomialIndex n q × ι) → ℂ) →ₗ[ℂ]
      (∀ j : Fin q, MultilinearMap ℂ (fun _ : Fin j.val => ComplexModel n) ℂ) :=
  Fintype.linearCombination ℂ (fun b : monomialIndex n q × ι =>
    finiteJet q (wordMonomial b.1 * G b.2))

/-- Actual Macaulay range equals the jet image of the entire original ring ideal. -/
theorem range_macaulayMap (q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel n)) :
    LinearMap.range (macaulayMap q G) =
      ((Ideal.span (range G)).restrictScalars ℂ).map (finiteJet q) := by
  rw [macaulayMap, Fintype.range_linearCombination,
    map_span_ideal_finiteJet_eq_monomial_columns]

/-- Literal whole-ring Hilbert--Samuel value is obtained from actual finite Macaulay rank. -/
theorem hilbertSamuelValue_eq_macaulay_rank (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel n)) :
    hilbertSamuelValue (Ideal.span (range G)) ℓ =
      Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) -
        Module.finrank ℂ (LinearMap.range (macaulayMap (ℓ + 1) G)) := by
  rw [hilbertSamuelValue, finrank_quotient_eq_jet_rank_sub_ideal_image_rank,
    range_macaulayMap]

/-- Every given whole ideal internally receives one original generator family
and the actual Macaulay rank formula for all its Hilbert--Samuel point values. -/
theorem exists_original_generators_macaulay_rank (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ (r : ℕ) (G : Fin r → ComplexModel n → ℂ)
      (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z),
      Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I ∧
      ∀ ℓ : ℕ, hilbertSamuelValue I ℓ =
        Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ + 1))) -
          Module.finrank ℂ (LinearMap.range
            (macaulayMap (ℓ + 1) (fun i => HolGerm.mk (G i) (hG i)))) := by
  obtain ⟨r, G, hG, hI, -⟩ := exists_original_generators_jet_columns I
  refine ⟨r, G, hG, hI, ?_⟩
  intro ℓ
  rw [← hI]
  exact hilbertSamuelValue_eq_macaulay_rank ℓ _

end
end Hironaka.HironakaHolomorphicJetMonomialSpan
