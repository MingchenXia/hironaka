/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.FinitePointPrescription

/-!
# Actual finite-point prescription from positive degree on an integral curve

The original Euler degree supplies the initial global section, the second-section and affine
nonvanishing-locus producers construct an actual two-section affine cover of the original curve,
and finite-point prescription produces actual sections over the original coefficient field.
No initial good section, two-section cover, or cohomology-vanishing certificate is an input.

Blueprint: `integral-positive-prescription.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.IntegralPositivePrescription

noncomputable section

open CurvesField CurvesField.Ample CurvesField.Positive Projectivity.LineBundleData

variable {K : Type u} [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
  {p : X ⟶ Spec (.of K)} [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- The original positive Euler degree constructs actual sections with affine nonvanishing loci
covering the original integral curve, in one positive power of the original line bundle. -/
theorem exists_twoAffineSectionCover_of_degree_pos (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) (L : LineBundleData X)
    (hdeg : 0 < degree L (structureCoeff p)) :
    ∃ N : ℕ, 0 < N ∧ ∃ s₀ s₁ : L.Sections N ⊤,
      s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
        IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus := by
  have : IsProper p := hp.isProper
  obtain ⟨n, hn, s, hgen, hzero⟩ := exists_section_of_degree_pos_of_isIntegral hp hdim L hdeg
  have hdim' := eq_or_eq_of_topologicalKrullDim_le_one hdim
  obtain ⟨m, t, ht⟩ := exists_section_sup_eq_top hp hdim' s hgen
  let N : ℕ := n * (m + 1)
  have hN : 0 < N := Nat.mul_pos hn (Nat.succ_pos m)
  have hcast : (n : ℤ) * ((m + 1 : ℕ) : ℤ) = (N : ℤ) := by
    simp [N]
  let s₀ : L.Sections (N : ℤ) ⊤ := (s.npow (m + 1)).cast hcast
  let s₁ : L.Sections (N : ℤ) ⊤ := t.cast hcast
  have hs₀ : s₀.nonvanishingLocus = s.nonvanishingLocus := by
    rw [Sections.nonvanishingLocus_cast, Sections.nonvanishingLocus_npow _ (Nat.succ_pos m)]
  have hs₁ : s₁.nonvanishingLocus = t.nonvanishingLocus := Sections.nonvanishingLocus_cast _ _
  have hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ := by rw [hs₀, hs₁, ht]
  obtain ⟨h₀, h₁⟩ := isAffineOpen_nonvanishingLocus p hdim' s₀ s₁ hcov
    (fun x hx => hs₀ ▸ hgen x hx) (fun x hx => hs₀ ▸ hzero x hx)
  exact ⟨N, hN, s₀, s₁, hcov, h₀, h₁⟩

/-- Positive degree alone supplies actual sections in positive, arbitrarily high multiples,
with prescribed zeros and nonzeros at finite sets of original closed points. -/
theorem exists_sections_prescribing_of_degree_pos (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) (L : LineBundleData X)
    (hdeg : 0 < degree L (structureCoeff p)) (T₀ T₁ : Finset X)
    (hcl : ∀ z, z ∈ T₀ ∨ z ∈ T₁ → IsClosed ({z} : Set X)) (hdisj : Disjoint T₀ T₁) :
    ∃ N : ℕ, 0 < N ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ t : L.Sections ((N : ℤ) * (k + 1 : ℕ)) ⊤,
        (∀ z ∈ T₀, z ∉ t.nonvanishingLocus) ∧ (∀ z ∈ T₁, z ∈ t.nonvanishingLocus) := by
  obtain ⟨N, hN, s₀, s₁, hcov, h₀, h₁⟩ :=
    exists_twoAffineSectionCover_of_degree_pos hp hdim L hdeg
  obtain ⟨k₀, hk₀⟩ := FinitePointPrescription.exists_sections_prescribing_finite_closed_points
    s₀ s₁ hcov h₀ h₁ T₀ T₁ hcl hdisj
  exact ⟨N, hN, k₀, hk₀⟩

end

end DeJongAlterations.StableModificationBridge.IntegralPositivePrescription
