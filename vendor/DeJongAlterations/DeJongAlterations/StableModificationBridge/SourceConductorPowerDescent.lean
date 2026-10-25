/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.GlobalIdealPowerVanishing
import DeJongAlterations.StableModificationBridge.AffineConductorSectionDescent

/-!
# Actual conductor zeros yield original whole-section descent after a power

Original source supportwise zeros internally produce every intrinsic affine ideal membership,
then actual coefficient gluing supplies the original section. Good-section properties descend
along the same actual finite surjection, with unchanged inverse-image nonvanishing locus.

Blueprint: `source-conductor-power-descent.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.SourceConductorPowerDescent

noncomputable section

open LineBundleData

variable {X Y : Scheme.{u}} (ν : Y ⟶ X) [IsFinite ν] [IsSchemeTheoreticallyDominant ν]
  [CompactSpace Y] [IsLocallyNoetherian Y] (L : LineBundleData X)

theorem exists_power_descent_of_zero_on_conductor (m : ℤ) (t : (L.pullback ν).Sections m ⊤)
    (hzero : ∀ y ∈ (SchemeConductor.sourceIdealSheaf ν).support, y ∉ t.nonvanishingLocus) :
    ∃ (e : ℕ) (s : L.Sections (m * e) ⊤), 0 < e ∧ s.pullback ν = t.npow e ∧
      ν ⁻¹ᵁ s.nonvanishingLocus = t.nonvanishingLocus := by
  obtain ⟨e, he, hpower⟩ := GlobalIdealPowerVanishing.exists_uniform_power_on_every_affine
    (SchemeConductor.sourceIdealSheaf ν)
  obtain ⟨hD, hcoeff⟩ := hpower (L.pullback ν) m t hzero
  obtain ⟨s, hs, -⟩ := AffineConductorSectionDescent.existsUnique_descent_of_source_ideal ν L
    (m * e) (t.npow e) (fun U i hU => hcoeff ⟨ν ⁻¹ᵁ U.1, U.2.preimage ν⟩ i (ν.preimage_mono hU))
  refine ⟨e, s, he, hs, ?_⟩
  have hsD := congrArg (fun z : (L.pullback ν).Sections (m * e) ⊤ => z.nonvanishingLocus) hs
  exact (Sections.nonvanishingLocus_pullback ν s).symm.trans (hsD.trans hD)

theorem exists_good_power_descent_of_zero_on_conductor (n : ℕ) (hn : 0 < n)
    (t : (L.pullback ν).Sections n ⊤)
    (hzero : ∀ y ∈ (SchemeConductor.sourceIdealSheaf ν).support, y ∉ t.nonvanishingLocus)
    (hgen : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → y ∈ t.nonvanishingLocus)
    (hspec : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → ∃ z, y ⤳ z ∧ z ∉ t.nonvanishingLocus) :
    ∃ (N : ℕ) (s : L.Sections N ⊤), 0 < N ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  obtain ⟨e, s, he, -, hD⟩ := exists_power_descent_of_zero_on_conductor ν L n t hzero
  have hcast : (n : ℤ) * e = ((n * e : ℕ) : ℤ) := by simp
  let s' : L.Sections (n * e) ⊤ := s.cast hcast
  have hD' : ν ⁻¹ᵁ s'.nonvanishingLocus = t.nonvanishingLocus := by
    rw [Sections.nonvanishingLocus_cast]
    exact hD
  have hnonclosed : ∀ {y : Y}, ¬ IsClosed ({ν y} : Set X) → ¬ IsClosed ({y} : Set Y) := by
    intro y hy hy'
    apply hy
    simpa only [Set.image_singleton] using ν.isClosedMap _ hy'
  refine ⟨n * e, s', Nat.mul_pos hn he, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := ν.surjective x
    have hy := hgen y (hnonclosed hx)
    rw [← hD'] at hy
    exact hy
  · intro x hx
    obtain ⟨y, rfl⟩ := ν.surjective x
    obtain ⟨z, hyz, hz⟩ := hspec y (hnonclosed hx)
    refine ⟨ν z, hyz.map ν.continuous, ?_⟩
    intro hνz
    apply hz
    rw [← hD']
    exact hνz

end

end DeJongAlterations.StableModificationBridge.SourceConductorPowerDescent
