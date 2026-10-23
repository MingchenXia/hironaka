/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.IdealPowerVanishing

/-!
# One intrinsic ideal-power bound on every original affine trivialization

The bound is an inequality of entire native ideal sheaves. Hence no coefficient-cover transport
certificate is needed to use the actual section on arbitrary original affine charts.

Blueprint: `global-ideal-power-vanishing.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification

namespace DeJongAlterations.StableModificationBridge.GlobalIdealPowerVanishing

open LineBundleData IdealPowerVanishing

variable {X : Scheme.{u}}

theorem exists_positive_radical_power_le [CompactSpace X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : ∃ e : ℕ, 0 < e ∧ I.radical ^ e ≤ I := by
  classical
  have hnear : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 := by
    intro x
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
    exact ⟨⟨U, hU⟩, hx⟩
  choose U hx using hnear
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => ((U x).1 : Set X))
    (fun x => (U x).1.isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have hcov : ⨆ j : S, (U j).1 = ⊤ := by
    apply top_unique
    intro x _
    have h := hS (Set.mem_univ x)
    simp only [Set.mem_iUnion] at h
    obtain ⟨j, hj, hxj⟩ := h
    exact Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hxj⟩
  have hbound : ∀ j : S, ∃ n : ℕ, (I.ideal (U j)).radical ^ n ≤ I.ideal (U j) := by
    intro j
    let : IsNoetherianRing Γ(X, (U j).1) := IsLocallyNoetherian.component_noetherian (U j)
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose n hn using hbound
  let e := Finset.univ.sup n + 1
  refine ⟨e, Nat.succ_pos _, Scheme.IdealSheafData.le_of_iSup_eq_top (fun j : S => U j) hcov ?_⟩
  intro j
  change (I.ideal (U j)).radical ^ e ≤ I.ideal (U j)
  exact (Ideal.pow_le_pow_right ((Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_succ _))).trans
    (hn j)

theorem exists_uniform_power_on_every_affine [CompactSpace X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    ∃ e : ℕ, 0 < e ∧ ∀ (L : LineBundleData X) (m : ℤ) (s : L.Sections m ⊤),
      (∀ x ∈ I.support, x ∉ s.nonvanishingLocus) →
      (s.npow e).nonvanishingLocus = s.nonvanishingLocus ∧
        ∀ (U : X.affineOpens) (i : L.ι) (hU : U.1 ≤ L.U i),
          coefficientOnAffine (s.npow e) U hU ∈ I.ideal U := by
  obtain ⟨e, he, hle⟩ := exists_positive_radical_power_le I
  refine ⟨e, he, fun L m s hzero => ⟨Sections.nonvanishingLocus_npow s he, ?_⟩⟩
  intro U i hU
  rw [coefficientOnAffine_npow]
  have hr := coefficient_mem_radical_of_zero_on_support I s hzero U hU
  exact hle U (Ideal.pow_mem_pow hr e)

theorem exists_section_prescribing_ideal_on_every_affine_of_degree_pos
    {K : Type u} [Field K] [Infinite K] [IsIntegral X] [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundleData X) (hdeg : 0 < CurvesField.Positive.degree L (Cohomology.structureCoeff p))
    (I : X.IdealSheafData) (T₀ T₁ : Finset X)
    (hcl : ∀ z, z ∈ T₀ ∨ z ∈ T₁ → IsClosed ({z} : Set X)) (hdisj : Disjoint T₀ T₁)
    (hsupp : ∀ x ∈ I.support, x ∈ T₀) :
    ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
      (∀ z ∈ T₀, z ∉ s.nonvanishingLocus) ∧ (∀ z ∈ T₁, z ∈ s.nonvanishingLocus) ∧
        ∀ (U : X.affineOpens) (i : L.ι) (hU : U.1 ≤ L.U i),
          coefficientOnAffine s U hU ∈ I.ideal U := by
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨N, hN, k₀, hk₀⟩ := IntegralPositivePrescription.exists_sections_prescribing_of_degree_pos
    hp hdim L hdeg T₀ T₁ hcl hdisj
  obtain ⟨t, ht₀, ht₁⟩ := hk₀ k₀ le_rfl
  let n₀ : ℕ := N * (k₀ + 1)
  have hn₀ : 0 < n₀ := Nat.mul_pos hN (Nat.succ_pos k₀)
  have hcast₀ : (N : ℤ) * (k₀ + 1 : ℕ) = (n₀ : ℤ) := by simp [n₀]
  let w : L.Sections n₀ ⊤ := t.cast hcast₀
  have hwt : w.nonvanishingLocus = t.nonvanishingLocus :=
    Sections.nonvanishingLocus_cast hcast₀ t
  obtain ⟨e, he, hpower⟩ := exists_uniform_power_on_every_affine I
  have hzero : ∀ x ∈ I.support, x ∉ w.nonvanishingLocus := by
    intro x hx
    rw [hwt]
    exact ht₀ x (hsupp x hx)
  obtain ⟨hpowerD, hcoeff⟩ := hpower L n₀ w hzero
  have hcast : (n₀ : ℤ) * e = ((n₀ * e : ℕ) : ℤ) := by simp
  let s : L.Sections (n₀ * e) ⊤ := (w.npow e).cast hcast
  have hsw : s.nonvanishingLocus = w.nonvanishingLocus :=
    (Sections.nonvanishingLocus_cast hcast (w.npow e)).trans hpowerD
  refine ⟨n₀ * e, s, Nat.mul_pos hn₀ he, ?_, ?_, ?_⟩
  · intro z hz
    rw [hsw, hwt]
    exact ht₀ z hz
  · intro z hz
    rw [hsw, hwt]
    exact ht₁ z hz
  · intro U i hU
    simpa only [s, coefficientOnAffine, Sections.coeff_cast] using hcoeff U i hU

end DeJongAlterations.StableModificationBridge.GlobalIdealPowerVanishing
