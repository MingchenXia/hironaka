/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.IntegralPositivePrescription
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Actual finite-order vanishing from zeros on an ideal sheaf's support

The coefficients are restrictions through the original affine chart maps. A native Noetherian
radical-power bound makes one positive power of every supportwise-zero section belong to the
actual affine ideals, on an internally constructed finite affine trivializing cover. The full
nonvanishing locus is preserved. The ideal may be an actual conductor; descent through a finite
morphism is a separate assertion.

Blueprint: `ideal-power-vanishing.tex`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.IdealPowerVanishing

noncomputable section

open Projectivity.LineBundleData

variable {X : Scheme.{u}} {L : LineBundleData X} {m : ℤ}

/-- The actual original coefficient restricted to an affine open inside its original chart. -/
def coefficientOnAffine (s : L.Sections m ⊤) (U : X.affineOpens) {i : L.ι}
    (hU : U.1 ≤ L.U i) : Γ(X, U.1) :=
  X.presheaf.map (homOfLE (le_inf le_top hU)).op (s.coeff i)

lemma basicOpen_coefficientOnAffine (s : L.Sections m ⊤) (U : X.affineOpens) {i : L.ι}
    (hU : U.1 ≤ L.U i) :
    X.basicOpen (coefficientOnAffine s U hU) = U.1 ⊓ s.nonvanishingLocus := by
  rw [coefficientOnAffine, Scheme.basicOpen_res, ← s.nonvanishingLocus_inf i]
  ext x
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hU h.1⟩⟩

lemma coefficientOnAffine_npow (s : L.Sections m ⊤) (U : X.affineOpens) {i : L.ι}
    (hU : U.1 ≤ L.U i) (e : ℕ) :
    coefficientOnAffine (s.npow e) U hU = coefficientOnAffine s U hU ^ e := by
  unfold coefficientOnAffine
  rw [Sections.coeff_npow, map_pow]

/-- Supportwise zeros imply radical membership in the original affine ideal, without a field
extension, a replacement coefficient ring, or an ideal-membership certificate as input. -/
lemma coefficient_mem_radical_of_zero_on_support (I : X.IdealSheafData)
    (s : L.Sections m ⊤) (hzero : ∀ x ∈ I.support, x ∉ s.nonvanishingLocus)
    (U : X.affineOpens) {i : L.ι} (hU : U.1 ≤ L.U i) :
    coefficientOnAffine s U hU ∈ (I.ideal U).radical := by
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  apply (PrimeSpectrum.mem_vanishingIdeal _ _).mpr
  intro q hq
  have hx : U.2.fromSpec q ∈ X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus]
    exact ⟨q, hq, rfl⟩
  have hsupp : U.2.fromSpec q ∈ I.support :=
    (I.mem_support_iff_of_mem hx.2).mpr hx.1
  have hnot : q ∉ PrimeSpectrum.basicOpen (coefficientOnAffine s U hU) := by
    intro hqf
    have hxf : U.2.fromSpec q ∈ X.basicOpen (coefficientOnAffine s U hU) := by
      change q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen (coefficientOnAffine s U hU)
      rw [U.2.fromSpec_preimage_basicOpen]
      exact hqf
    rw [basicOpen_coefficientOnAffine] at hxf
    exact hzero _ hsupp hxf.2
  simpa only [PrimeSpectrum.mem_basicOpen, not_not] using hnot

/-- On a finite family of original affine trivializations, one positive power works for every
section of every power of the line bundle that vanishes on the actual ideal support. -/
theorem exists_uniform_power_on_affine_frames [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {J : Type u} [Fintype J] (U : J → X.affineOpens)
    (chart : J → L.ι) (hU : ∀ j, (U j).1 ≤ L.U (chart j)) :
    ∃ e : ℕ, 0 < e ∧ ∀ (m : ℤ) (s : L.Sections m ⊤),
      (∀ x ∈ I.support, x ∉ s.nonvanishingLocus) →
      (s.npow e).nonvanishingLocus = s.nonvanishingLocus ∧
        ∀ j, coefficientOnAffine (s.npow e) (U j) (hU j) ∈ I.ideal (U j) := by
  classical
  have hbound : ∀ j, ∃ n : ℕ, (I.ideal (U j)).radical ^ n ≤ I.ideal (U j) := by
    intro j
    have : IsNoetherianRing Γ(X, (U j).1) := IsLocallyNoetherian.component_noetherian (U j)
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose n hn using hbound
  let e : ℕ := Finset.univ.sup n + 1
  have he : 0 < e := Nat.succ_pos _
  refine ⟨e, he, fun m s hzero => ⟨Sections.nonvanishingLocus_npow s he, ?_⟩⟩
  intro j
  rw [coefficientOnAffine_npow]
  have hr := coefficient_mem_radical_of_zero_on_support I s hzero (U j) (hU j)
  have hle : n j ≤ e := (Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _)
  exact hn j (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hr e))

/-- A finite affine cover refining the original trivializing opens is constructed internally. -/
theorem exists_finite_affine_trivializations [CompactSpace X] (L : LineBundleData X) :
    ∃ (S : Finset X) (U : S → X.affineOpens) (chart : S → L.ι),
      (∀ j, (U j).1 ≤ L.U (chart j)) ∧ ∀ x : X, ∃ j, x ∈ (U j).1 := by
  classical
  have hnear : ∀ x : X, ∃ (i : L.ι) (U : X.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ U ≤ L.U i := by
    intro x
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    obtain ⟨U, hU, hx, hle⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨i, U, hU, hx, hle⟩
  choose chart U haff hx hle using hnear
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨S, (fun j => ⟨U j, haff j⟩), (fun j => chart j), (fun j => hle j), fun x => ?_⟩
  have h := hS (Set.mem_univ x)
  simp only [Set.mem_iUnion] at h
  obtain ⟨j, hj, hxj⟩ := h
  exact ⟨⟨j, hj⟩, hxj⟩

/-- An actual finite affine trivializing cover and uniform positive power, with membership in
every actual ideal on that cover, are produced from quasi-compactness and local Noetherianity. -/
theorem exists_uniform_power_on_actual_cover [CompactSpace X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (L : LineBundleData X) :
    ∃ (S : Finset X) (U : S → X.affineOpens) (chart : S → L.ι)
      (hU : ∀ j, (U j).1 ≤ L.U (chart j)) (e : ℕ),
      0 < e ∧ (∀ x : X, ∃ j, x ∈ (U j).1) ∧
        ∀ (m : ℤ) (s : L.Sections m ⊤),
          (∀ x ∈ I.support, x ∉ s.nonvanishingLocus) →
          (s.npow e).nonvanishingLocus = s.nonvanishingLocus ∧
            ∀ j, coefficientOnAffine (s.npow e) (U j) (hU j) ∈ I.ideal (U j) := by
  obtain ⟨S, U, chart, hU, hcov⟩ := exists_finite_affine_trivializations L
  obtain ⟨e, he, h⟩ := exists_uniform_power_on_affine_frames I U chart hU
  exact ⟨S, U, chart, hU, e, he, hcov, h⟩

/-- Positive degree constructs an actual positive-power section with prescribed finite nonzeros
and membership in every original ideal on an internally constructed affine trivializing cover.
The ideal's finite support is a geometric input; neither a section nor ideal membership is. -/
theorem exists_section_prescribing_ideal_of_degree_pos
    {K : Type u} [Field K] [Infinite K] [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundleData X) (hdeg : 0 < CurvesField.Positive.degree L (Cohomology.structureCoeff p))
    (I : X.IdealSheafData) (T₀ T₁ : Finset X)
    (hcl : ∀ z, z ∈ T₀ ∨ z ∈ T₁ → IsClosed ({z} : Set X)) (hdisj : Disjoint T₀ T₁)
    (hsupp : ∀ x ∈ I.support, x ∈ T₀) :
    ∃ (n : ℕ) (s : L.Sections n ⊤) (S : Finset X) (U : S → X.affineOpens)
      (chart : S → L.ι) (hU : ∀ j, (U j).1 ≤ L.U (chart j)),
      0 < n ∧ (∀ x : X, ∃ j, x ∈ (U j).1) ∧
        (∀ z ∈ T₀, z ∉ s.nonvanishingLocus) ∧ (∀ z ∈ T₁, z ∈ s.nonvanishingLocus) ∧
          ∀ j, coefficientOnAffine s (U j) (hU j) ∈ I.ideal (U j) := by
  have : IsProper p := hp.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨N, hN, k₀, hk₀⟩ := IntegralPositivePrescription.exists_sections_prescribing_of_degree_pos
    hp hdim L hdeg T₀ T₁ hcl hdisj
  obtain ⟨t, ht₀, ht₁⟩ := hk₀ k₀ le_rfl
  let n₀ : ℕ := N * (k₀ + 1)
  have hn₀ : 0 < n₀ := Nat.mul_pos hN (Nat.succ_pos k₀)
  have hcast₀ : (N : ℤ) * (k₀ + 1 : ℕ) = (n₀ : ℤ) := by simp [n₀]
  let w : L.Sections n₀ ⊤ := t.cast hcast₀
  have hwt : w.nonvanishingLocus = t.nonvanishingLocus := by
    exact Sections.nonvanishingLocus_cast hcast₀ t
  obtain ⟨S, U, chart, hU, e, he, hcov, hpower⟩ := exists_uniform_power_on_actual_cover I L
  have hzero : ∀ x ∈ I.support, x ∉ w.nonvanishingLocus := by
    intro x hx
    rw [hwt]
    exact ht₀ x (hsupp x hx)
  obtain ⟨hpowerD, hcoeff⟩ := hpower n₀ w hzero
  have hcast : (n₀ : ℤ) * e = ((n₀ * e : ℕ) : ℤ) := by simp
  let s : L.Sections (n₀ * e) ⊤ := (w.npow e).cast hcast
  have hsw : s.nonvanishingLocus = w.nonvanishingLocus := by
    exact (Sections.nonvanishingLocus_cast hcast (w.npow e)).trans hpowerD
  refine ⟨n₀ * e, s, S, U, chart, hU, Nat.mul_pos hn₀ he, hcov, ?_, ?_, ?_⟩
  · intro z hz
    rw [hsw, hwt]
    exact ht₀ z hz
  · intro z hz
    rw [hsw, hwt]
    exact ht₁ z hz
  · intro j
    simpa only [s, coefficientOnAffine, Sections.coeff_cast] using hcoeff j

end

end DeJongAlterations.StableModificationBridge.IdealPowerVanishing
