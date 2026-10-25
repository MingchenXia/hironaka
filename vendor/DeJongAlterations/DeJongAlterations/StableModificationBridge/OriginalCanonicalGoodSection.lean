/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.CanonicalReducedGoodSection
import DeJongAlterations.StableModificationBridge.ReductionOpenComparison
import DeJongAlterations.StableModificationBridge.NilradicalAffineness
import DeJongAlterations.StableModificationBridge.NilradicalGoodSection

/-!
# Unconditional good sections on the actual original projective curve

Original canonical-component positivity internally produces the actual reduced good pair,
actual original affine opens, and an actual positive-power original good section.

Blueprint: `original-canonical-good-section.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField

namespace DeJongAlterations.StableModificationBridge.OriginalCanonicalGoodSection

noncomputable section

open LineBundleData Ample

variable {X : Scheme.{u}}

theorem isAffineOpen_liftOpen {K : Type u} [Field K] (p : X ⟶ Spec (.of K))
    [IsSeparated p] [IsLocallyNoetherian X] (W : X.nilradical.subscheme.Opens)
    (hW : IsAffineOpen W) : IsAffineOpen (ReductionOpenComparison.liftOpen W) := by
  let U := ReductionOpenComparison.liftOpen W
  let : IsAffine U.toScheme.nilradical.subscheme :=
    ReductionOpenComparison.isAffine_reduction_of_preimage U (by
      rw [ReductionOpenComparison.preimage_liftOpen]
      exact hW)
  have hUc : IsCompact (U : Set X) :=
    hW.isCompact.image (ReductionCanonicalGeometry.homeomorph X).continuous
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  let : IsAffineHom (pullback.diagonal (terminal.from U.toScheme)) :=
    isAffineHom_diagonal_of_isSeparated (U.ι ≫ p)
  exact NilradicalAffineness.isAffine_of_affine_reduction U.toScheme

theorem exists_good_section_of_positiveCanonicalComponents
    {K : Type u} [Field K] [Infinite K] (p : X ⟶ Spec (.of K))
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1) (L : LineBundleData X)
    (hpos : StableProjectivityClosedFibres.PositiveCanonicalComponents p hp L) :
    ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  let : IsProper p := hp.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  obtain ⟨-, N, hN, s₀, s₁, hcov, haff₀, haff₁, hgen, hzero⟩ :=
    CanonicalReducedGoodSection.exists_good_reduced_affine_cover_of_positiveCanonicalComponents
      p hp hdim L hpos
  let U := ReductionOpenComparison.liftOpen s₀.nonvanishingLocus
  let V := ReductionOpenComparison.liftOpen s₁.nonvanishingLocus
  have hU : IsAffineOpen U := isAffineOpen_liftOpen p _ haff₀
  have hV : IsAffineOpen V := isAffineOpen_liftOpen p _ haff₁
  obtain ⟨n, s, hn, -, hsgen, hszero⟩ := NilradicalGoodSection.exists_good_section_of_affine_cover
    hN hU hV (hU.inf hV) s₀ s₁
    (ReductionOpenComparison.preimage_liftOpen _).symm
    (ReductionOpenComparison.preimage_liftOpen _).symm
    (X.nilradical.subschemeι ≫ p)
    (Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp X.nilradical.subschemeι)
    hcov haff₀ haff₁ hgen hzero
  exact ⟨n, s, hn, hsgen, hszero⟩

theorem algClosedCurveGoodSection : StableProjectivityClosedFibres.AlgClosedCurveGoodSection.{u} := by
  intro K _ _ X p hp hdim L hpos
  exact exists_good_section_of_positiveCanonicalComponents p hp hdim L hpos

end

end DeJongAlterations.StableModificationBridge.OriginalCanonicalGoodSection
