/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.IntegralPositivePrescription
import DeJongAlterations.StableModification.CurvesField.AmplePositiveNormalization

/-!
# Actual positive-degree good sections with arbitrary finite original closed zeros

Both the extra zero specialization and the prescribed nonzero closed point are internally
constructed on the same original curve and over the original field.

Blueprint: `integral-positive-finite-zero.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.IntegralPositiveFiniteZero

noncomputable section

open LineBundleData CurvesField.Positive CurvesField.Ample

variable {X : Scheme.{u}}

theorem exists_good_section_zero_on_finite_closed_points_of_degree_pos
    {K : Type u} [Field K] [Infinite K] [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundleData X) (hdeg : 0 < degree L (Cohomology.structureCoeff p))
    (T : Finset X) (hcl : ∀ z ∈ T, IsClosed ({z} : Set X)) :
    ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
      (∀ z ∈ T, z ∉ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  classical
  by_cases hnc : ∃ x : X, ¬ IsClosed ({x} : Set X)
  · obtain ⟨x, hx⟩ := hnc
    obtain ⟨n₀, -, s₀, hs₀gen, hs₀zero⟩ :=
      exists_section_of_degree_pos_of_isIntegral hp hdim L hdeg
    obtain ⟨z₀, -, hz₀⟩ := hs₀zero x hx
    have hz₀cl : IsClosed ({z₀} : Set X) := by
      by_contra h
      exact hz₀ (hs₀gen z₀ h)
    let T' := insert z₀ T
    have hTcl : ∀ z ∈ T', IsClosed ({z} : Set X) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hz₀cl
      · exact hcl z hz
    have hTclosed : IsClosed (T' : Set X) := by
      simpa only [Set.biUnion_of_singleton] using
        T'.finite_toSet.isClosed_biUnion (fun z hz => hTcl z hz)
    let : IsProper p := hp.isProper
    let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    have hxT : x ∈ (T' : Set X)ᶜ := fun h => hx (hTcl x h)
    obtain ⟨z₁, hz₁T, hz₁cl⟩ := nonempty_inter_closedPoints ⟨x, hxT⟩ hTclosed.isOpen_compl.isLocallyClosed
    have hz₁cl' : IsClosed ({z₁} : Set X) := hz₁cl
    have hdisj : Disjoint T' ({z₁} : Finset X) := by
      rw [Finset.disjoint_singleton_right]
      exact hz₁T
    obtain ⟨N, hN, k₀, hk₀⟩ := IntegralPositivePrescription.exists_sections_prescribing_of_degree_pos
      hp hdim L hdeg T' {z₁} (by
        intro z hz
        rcases hz with hz | hz
        · exact hTcl z hz
        · simpa only [Finset.mem_singleton.mp hz] using hz₁cl') hdisj
    obtain ⟨t, ht₀, ht₁⟩ := hk₀ k₀ le_rfl
    have hcast : (N : ℤ) * (k₀ + 1 : ℕ) = ((N * (k₀ + 1) : ℕ) : ℤ) := by simp
    let s : L.Sections (N * (k₀ + 1)) ⊤ := t.cast hcast
    have hD : s.nonvanishingLocus = t.nonvanishingLocus := Sections.nonvanishingLocus_cast hcast t
    have hz₁D : z₁ ∈ s.nonvanishingLocus := by rw [hD]; exact ht₁ z₁ (Finset.mem_singleton_self _)
    have hz₀D : z₀ ∉ s.nonvanishingLocus := by rw [hD]; exact ht₀ z₀ (Finset.mem_insert_self _ _)
    refine ⟨N * (k₀ + 1), s, Nat.mul_pos hN (Nat.succ_pos _), ?_, ?_, ?_⟩
    · intro z hz
      rw [hD]
      exact ht₀ z (Finset.mem_insert_of_mem hz)
    · intro y hy
      rw [eq_genericPoint_of_not_isClosed hdim hy]
      exact genericPoint_mem_of_nonempty ⟨z₁, hz₁D⟩
    · intro y hy
      refine ⟨z₀, ?_, hz₀D⟩
      rw [eq_genericPoint_of_not_isClosed hdim hy]
      exact (genericPoint_spec X).specializes (Set.mem_univ _)
  · refine ⟨1, 0, Nat.one_pos, ?_, ?_, ?_⟩
    · intro z _ hz
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
      change z ∈ X.basicOpen (0 : Γ(X, ⊤ ⊓ L.U i)) at hi
      simp only [Scheme.basicOpen_zero, Opens.mem_bot] at hi
    · intro x hx
      exact False.elim (hnc ⟨x, hx⟩)
    · intro x hx
      exact False.elim (hnc ⟨x, hx⟩)

open Geometry.NormalizationGluing in
theorem exists_good_section_zero_on_finite_closed_points_of_normalization_degree_pos
    {K : Type u} [Field K] [Infinite K] [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {p : X ⟶ Spec (.of K)} [LocallyOfFiniteType p] (hp : IsProjectiveOver p)
    (hdim : topologicalKrullDim X ≤ 1) (L : LineBundleData X)
    (hdeg :
      haveI := CurvesField.Genus.normalization_isAffineHom p
      haveI := CurvesField.Genus.compactSpace_of_isAffineHom (normalizationStructure X)
      haveI := CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (normalizationStructure X)
      0 < degree (L.pullback (normalizationStructure X))
        ((normalizationStructure X).appTop.hom.comp (Cohomology.structureCoeff p)))
    (T : Finset X) (hcl : ∀ z ∈ T, IsClosed ({z} : Set X)) :
    ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
      (∀ z ∈ T, z ∉ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  let := CurvesField.Genus.normalization_isAffineHom p
  let := CurvesField.Genus.compactSpace_of_isAffineHom (normalizationStructure X)
  let := CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (normalizationStructure X)
  obtain ⟨P, -⟩ := exists_presentation_of_isIntegral hp hdim L
  rw [degree_pullback_eq (normalizationStructure X) hp P CurvesField.Genus.normalization_app_injective
    (fun W hW => CurvesField.Genus.normalization_isFiniteCoker p hdim W hW)] at hdeg
  exact exists_good_section_zero_on_finite_closed_points_of_degree_pos hp hdim L hdeg T hcl

end

end DeJongAlterations.StableModificationBridge.IntegralPositiveFiniteZero
