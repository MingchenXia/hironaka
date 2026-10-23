/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import DeJongAlterations.StableModificationBridge.NilradicalCoverEngine

/-!
# Affineness after lifting the original global functions

The actual global-section surjectivity remains an explicit cohomological input.
The principal refinement, unit ideal and affine criterion are proved internally.
Blueprint: `affine-reduction-global-sections.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.AffineReductionGlobalSections

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual affine source, surjective on points and on whole original global
functions, forces a quasi-compact target to be affine. -/
theorem isAffine_of_surjective_appTop {X Y : Scheme.{u}} [CompactSpace X] [IsAffine Y]
    (f : Y ⟶ X) (hpoints : Function.Surjective f)
    (hΓ : Function.Surjective f.appTop) : IsAffine X := by
  classical
  let S : Set Γ(Y, ⊤) := {b | ∃ U : X.Opens, IsAffineOpen U ∧
    Y.basicOpen b ≤ f ⁻¹ᵁ U}
  have hS : Ideal.span S = ⊤ := by
    apply (isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mp
    apply le_antisymm (iSup_le fun _ => Y.basicOpen_le _)
    intro y _
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := f y) (U := (⊤ : X.Opens)) trivial
    obtain ⟨b, hbU, hyb⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (V := f ⁻¹ᵁ U) ⟨y, hyU⟩ trivial
    exact Opens.mem_iSup.mpr ⟨⟨b, U, hU, hbU⟩, hyb⟩
  let T : Set Γ(X, ⊤) := f.appTop ⁻¹' S
  have himage : f.appTop '' T = S := Set.image_preimage_eq S hΓ
  have hmap : (Ideal.span T).map f.appTop.hom = ⊤ := by
    rw [Ideal.map_span, himage, hS]
  have hker : RingHom.ker f.appTop.hom ≤ (Ideal.span T).radical := by
    intro a ha
    have hpre : f ⁻¹ᵁ X.basicOpen a = ⊥ := by
      rw [Scheme.preimage_basicOpen_top, RingHom.mem_ker.mp ha]
      exact Y.basicOpen_zero _
    have hempty : X.basicOpen a = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨y, rfl⟩ := hpoints x
      have hy : y ∈ f ⁻¹ᵁ X.basicOpen a := hx
      rw [hpre] at hy
      exact hy.elim
    obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot a).mpr hempty
    exact Ideal.mem_radical_iff.mpr ⟨n, hn.symm ▸ (Ideal.span T).zero_mem⟩
  have hspan : Ideal.span T = ⊤ := by
    have hsup : Ideal.span T ⊔ RingHom.ker f.appTop.hom = ⊤ := by
      have h := congrArg (Ideal.comap f.appTop.hom) hmap
      simpa only [Ideal.comap_map_of_surjective _ hΓ, Ideal.comap_top,
        RingHom.ker_eq_comap_bot] using h
    apply Ideal.radical_eq_top.mp
    apply top_unique
    rw [← hsup]
    exact sup_le Ideal.le_radical hker
  apply isAffine_of_isAffineOpen_basicOpen T hspan
  intro a ha
  obtain ⟨U, hU, hle⟩ := ha
  have hle' : X.basicOpen a ≤ U := by
    intro x hx
    obtain ⟨y, rfl⟩ := hpoints x
    apply hle
    change y ∈ Y.basicOpen (f.appTop a)
    rw [← Scheme.preimage_basicOpen_top]
    exact hx
  have h := hU.basicOpen (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hle'] at h

/-- The only remaining input here is surjectivity of the actual original
reduction map on whole global functions; affine-cover geometry is internal. -/
theorem isAffine_of_reduction_appTop_surjective (X : Scheme.{u}) [CompactSpace X]
    [IsAffine X.nilradical.subscheme]
    (hΓ : Function.Surjective X.nilradical.subschemeι.appTop) : IsAffine X :=
  isAffine_of_surjective_appTop X.nilradical.subschemeι
    (StableModificationBridge.NilradicalCoverEngine.reduction_surjective X) hΓ

end DeJongAlterations.Geometry.AffineReductionGlobalSections
