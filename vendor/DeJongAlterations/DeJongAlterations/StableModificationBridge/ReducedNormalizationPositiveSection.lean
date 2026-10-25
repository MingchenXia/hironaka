/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.PositiveIntegralClopenAssembly
import DeJongAlterations.StableModificationBridge.NormalizationConductorSupport
import DeJongAlterations.StableModificationBridge.SourceConductorPowerDescent
import DeJongAlterations.Geometry.ProjectiveSecantIntegralDimension
import DeJongAlterations.StableModification.CurvesField.AmpleFiber

/-!
# Reduced positive sections from the actual canonical normalization component cover

Every section, finite conductor support, coefficient membership, descended original section,
second covering section and coherent Serre ampleness conclusion is internally constructed.
Identification of the natural integral clopen normalization pieces with particular canonical
component normalizations is an explicit separate geometric input.

Blueprint: `reduced-normalization-positive-section.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField

namespace DeJongAlterations.StableModificationBridge.ReducedNormalizationPositiveSection

noncomputable section

open LineBundleData Ample Genus
open NormalizationConductorSupport

variable {X : Scheme.{u}}

theorem exists_twoAffineSectionCover_of_good_section
    {K : Type u} [Field K] [Infinite K] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1) {L : LineBundleData X}
    {n : ℕ} (hn : 0 < n) (s : L.Sections n ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    ∃ N : ℕ, 0 < N ∧ ∃ s₀ s₁ : L.Sections N ⊤,
      s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
        IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus := by
  let : IsProper p := hp.isProper
  have hdim' := eq_or_eq_of_topologicalKrullDim_le_one hdim
  obtain ⟨m, t, ht⟩ := exists_section_sup_eq_top hp hdim' s hgen
  let N : ℕ := n * (m + 1)
  have hN : 0 < N := Nat.mul_pos hn (Nat.succ_pos m)
  have hcast : (n : ℤ) * ((m + 1 : ℕ) : ℤ) = (N : ℤ) := by simp [N]
  let s₀ : L.Sections (N : ℤ) ⊤ := (s.npow (m + 1)).cast hcast
  let s₁ : L.Sections (N : ℤ) ⊤ := t.cast hcast
  have hs₀ : s₀.nonvanishingLocus = s.nonvanishingLocus :=
    (Sections.nonvanishingLocus_cast hcast _).trans
      (Sections.nonvanishingLocus_npow s (Nat.succ_pos m))
  have hs₁ : s₁.nonvanishingLocus = t.nonvanishingLocus := Sections.nonvanishingLocus_cast _ _
  have hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ := by rw [hs₀, hs₁, ht]
  obtain ⟨h₀, h₁⟩ := isAffineOpen_nonvanishingLocus p hdim' s₀ s₁ hcov
    (fun x hx => hs₀ ▸ hgen x hx) (fun x hx => hs₀ ▸ hzero x hx)
  exact ⟨N, hN, s₀, s₁, hcov, h₀, h₁⟩

theorem exists_good_section_and_affine_cover_of_normalization_components
    {K : Type u} [Field K] [Infinite K] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsReduced X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] (S : Set X) [Finite S]
    (hS : S = genericPoints X) (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundleData X) :
    letI : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
    letI : CompactSpace (normalizationPoints S) := compactSpace_of_isAffineHom (normalizationPointsMap S)
    letI : IsAffineHom (pullback.diagonal (terminal.from (normalizationPoints S))) :=
      isAffineHom_diagonal_of_isAffineHom (normalizationPointsMap S)
    ∀ {J : Type u} [Fintype J] (Z : J → Scheme.{u})
      (j : ∀ i, Z i ⟶ normalizationPoints S)
      [∀ i, IsIntegral (Z i)] [∀ i, IsFinite (j i)] [∀ i, IsOpenImmersion (j i)],
      Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange) →
      (⨆ i, (j i).opensRange) = ⊤ →
      (∀ i, (∃ z : Z i, ¬ IsClosed ({z} : Set (Z i))) →
        haveI : CompactSpace (Z i) := compactSpace_of_isAffineHom (j i)
        haveI : IsAffineHom (pullback.diagonal (terminal.from (Z i))) :=
          isAffineHom_diagonal_of_isAffineHom (j i)
        0 < Positive.degree ((L.pullback (normalizationPointsMap S)).pullback (j i))
          (Cohomology.structureCoeff (j i ≫ (normalizationPointsMap S ≫ p)))) →
      ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) ∧
        L.SerreAmple ∧ ∃ N : ℕ, 0 < N ∧ ∃ s₀ s₁ : L.Sections N ⊤,
          s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
            IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus := by
  let : IsFinite (normalizationPointsMap S) := isFinite_normalizationPointsMap p
  let : CompactSpace (normalizationPoints S) := compactSpace_of_isAffineHom (normalizationPointsMap S)
  let : IsAffineHom (pullback.diagonal (terminal.from (normalizationPoints S))) :=
    isAffineHom_diagonal_of_isAffineHom (normalizationPointsMap S)
  intro J _ Z j _ _ _ hdisj hcov hdeg
  let : IsLocallyNoetherian (normalizationPoints S) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationPointsMap S ≫ p)
  let : IsSchemeTheoreticallyDominant (normalizationPointsMap S) :=
    NormalizationConductorDescent.isSchemeTheoreticallyDominant_normalizationPoints p S hS
  let T : Finset (normalizationPoints S) := (finite_source_support_normalizationPoints p S hS hdim hp).toFinset
  have hcl : ∀ z ∈ T, IsClosed ({z} : Set (normalizationPoints S)) := by
    intro z hz
    exact isClosed_source_support_points_normalizationPoints p S hS hdim hp z
      ((Set.Finite.mem_toFinset _).mp hz)
  have hpN := Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp (normalizationPointsMap S)
  have hdimN : topologicalKrullDim (normalizationPoints S) ≤ 1 :=
    (Geometry.ProjectiveSecant.topologicalKrullDim_le_of_isIntegralHom (normalizationPointsMap S)).trans hdim
  obtain ⟨n, t, hn, htzero, htgen, htspec⟩ :=
    PositiveIntegralClopenAssembly.exists_good_section_zero_of_positive_integral_clopen_cover
      hpN hdimN Z j hdisj hcov (L.pullback (normalizationPointsMap S)) hdeg T hcl
  obtain ⟨N, s, hN, hsgen, hszero⟩ :=
    SourceConductorPowerDescent.exists_good_power_descent_of_zero_on_conductor
      (normalizationPointsMap S) L n hn t
      (fun z hz => htzero z ((Set.Finite.mem_toFinset _).mpr hz)) htgen htspec
  exact ⟨N, s, hN, hsgen, hszero, serreAmple_of_section hp hdim hN s hsgen hszero,
    exists_twoAffineSectionCover_of_good_section hp hdim hN s hsgen hszero⟩

end

end DeJongAlterations.StableModificationBridge.ReducedNormalizationPositiveSection
