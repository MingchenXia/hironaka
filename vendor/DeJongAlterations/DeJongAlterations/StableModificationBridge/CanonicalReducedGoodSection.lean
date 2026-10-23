/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.ReductionCanonicalDegree
import DeJongAlterations.StableModificationBridge.ReducedNormalizationPositiveSection
import DeJongAlterations.Geometry.CanonicalNormalizationComponentDegree

/-!
# Original canonical positivity produces the actual reduced good affine cover

Canonical normalization component geometry and all intrinsic conductor descent are internal.
The final output has original good-section conditions on the FIRST actual affine-cover section,
matching the genuine nilradical lifting consumer. Nilpotent lifting itself remains separate.

Blueprint: `canonical-reduced-good-section.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField

namespace DeJongAlterations.StableModificationBridge.CanonicalReducedGoodSection

noncomputable section

open LineBundleData Ample Genus

variable {X : Scheme.{u}}

theorem exists_good_affine_cover_of_good_section
    {K : Type u} [Field K] [Infinite K] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1) {L : LineBundleData X}
    {n : ℕ} (hn : 0 < n) (s : L.Sections n ⊤)
    (hgen : ∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus)
    (hzero : ∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) :
    ∃ N : ℕ, 0 < N ∧ ∃ s₀ s₁ : L.Sections N ⊤,
      s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
        IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s₀.nonvanishingLocus) ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s₀.nonvanishingLocus) := by
  let : IsProper p := hp.isProper
  have hdim' := eq_or_eq_of_topologicalKrullDim_le_one hdim
  obtain ⟨m, t, ht⟩ := exists_section_sup_eq_top hp hdim' s hgen
  let N : ℕ := n * (m + 1)
  have hcast : (n : ℤ) * ((m + 1 : ℕ) : ℤ) = (N : ℤ) := by simp [N]
  let s₀ : L.Sections N ⊤ := (s.npow (m + 1)).cast hcast
  let s₁ : L.Sections N ⊤ := t.cast hcast
  have hs₀ : s₀.nonvanishingLocus = s.nonvanishingLocus :=
    (Sections.nonvanishingLocus_cast hcast _).trans
      (Sections.nonvanishingLocus_npow s (Nat.succ_pos m))
  have hs₁ : s₁.nonvanishingLocus = t.nonvanishingLocus := Sections.nonvanishingLocus_cast _ _
  have hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ := by rw [hs₀, hs₁, ht]
  obtain ⟨h₀, h₁⟩ := isAffineOpen_nonvanishingLocus p hdim' s₀ s₁ hcov
    (fun x hx => hs₀ ▸ hgen x hx) (fun x hx => hs₀ ▸ hzero x hx)
  exact ⟨N, Nat.mul_pos hn (Nat.succ_pos m), s₀, s₁, hcov, h₀, h₁,
    fun x hx => hs₀ ▸ hgen x hx, fun x hx => hs₀ ▸ hzero x hx⟩

theorem exists_good_affine_cover_of_positiveCanonicalComponents
    {K : Type u} [Field K] [Infinite K] [IsReduced X]
    (p : X ⟶ Spec (.of K)) (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundleData X) (hpos : StableProjectivityClosedFibres.PositiveCanonicalComponents p hp L) :
    L.SerreAmple ∧ ∃ N : ℕ, 0 < N ∧ ∃ s₀ s₁ : L.Sections N ⊤,
      s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
        IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s₀.nonvanishingLocus) ∧
        (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s₀.nonvanishingLocus) := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := compactSpace_of_quasiCompact p
  let : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  let : Finite (genericPoints X) := finite_genericPoints p
  let : Fintype (genericPoints X) := Fintype.ofFinite _
  obtain ⟨n, s, hn, hsgen, hszero, hample, -⟩ :=
    ReducedNormalizationPositiveSection.exists_good_section_and_affine_cover_of_normalization_components
      p (genericPoints X) rfl hp hdim L Geometry.CanonicalNormalization.component
      Geometry.CanonicalNormalization.componentIncl
      Geometry.CanonicalNormalization.pairwise_disjoint_componentIncl
      Geometry.CanonicalNormalization.iSup_componentIncl_opensRange
      (fun η hz => Geometry.CanonicalNormalization.positive_componentIncl_degree p hp L hpos η hz)
  exact ⟨hample, exists_good_affine_cover_of_good_section hp hdim hn s hsgen hszero⟩

theorem exists_good_reduced_affine_cover_of_positiveCanonicalComponents
    {K : Type u} [Field K] [Infinite K] (p : X ⟶ Spec (.of K))
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1) (L : LineBundleData X)
    (hpos : StableProjectivityClosedFibres.PositiveCanonicalComponents p hp L) :
    (L.pullback X.nilradical.subschemeι).SerreAmple ∧ ∃ N : ℕ, 0 < N ∧
      ∃ s₀ s₁ : (L.pullback X.nilradical.subschemeι).Sections N ⊤,
        s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤ ∧
          IsAffineOpen s₀.nonvanishingLocus ∧ IsAffineOpen s₁.nonvanishingLocus ∧
          (∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
            x ∈ s₀.nonvanishingLocus) ∧
          (∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
            ∃ z, x ⤳ z ∧ z ∉ s₀.nonvanishingLocus) := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := compactSpace_of_quasiCompact p
  let : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  let : IsReduced X.nilradical.subscheme := ReductionCanonicalGeometry.isReduced_reduction X
  exact exists_good_affine_cover_of_positiveCanonicalComponents (X.nilradical.subschemeι ≫ p)
    (Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp X.nilradical.subschemeι)
    (X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
    (L.pullback X.nilradical.subschemeι)
    (ReductionCanonicalDegree.positiveCanonicalComponents_reduction p hp L hpos)

end

end DeJongAlterations.StableModificationBridge.CanonicalReducedGoodSection
