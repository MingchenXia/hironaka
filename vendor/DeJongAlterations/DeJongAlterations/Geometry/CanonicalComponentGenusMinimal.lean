/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.CanonicalComponentDegreeMinimal

/-! # Nonnegative original component genus from projectivity only of its normalization -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal

universe u

open ComponentDegree Cohomology CurvesField CurvesField.Genus ComponentNormalization

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{u}} (f : X ⟶ S) {K : Type u} [Field K] [IsAlgClosed K]
  (a : Spec (.of K) ⟶ S)
  [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
  [DeJong.IsNodalCurve f] [CompactSpace (pullback (C := Scheme.{u}) f a)]
  {η : pullback (C := Scheme.{u}) f a} (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a))

include hη in
/-- The SAME actual component genus is nonnegative using only its own projective normalization. -/
theorem componentGenus_nonneg (hN : IsProjectiveOver (componentStructure f a η)) :
    0 ≤ componentGenus (structureCoeff (pullback.snd f a)) η := by
  have : IsProper (componentStructure f a η) := hN.isProper
  obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
  obtain ⟨P, -⟩ := DualityScheme.exists_isSeparable_chartPair
    (componentStructure f a η) hN
    (topologicalKrullDim_normalizationPoints_le η (pullback.snd f a)
      (topologicalKrullDim_fibre_le_one f a))
    (exists_ne_genericPoint η hz hzη)
  rw [← arithmeticGenus_componentNormalization f a η]
  have hχ := DualityScheme.eulerCharOf_eq_of_pair
    (SheafOfModules.unit (componentNormalization f a η).ringCatSheaf)
    (structureCoeff (componentStructure f a η)) P.sup_eq_top
    P.isAffineOpen₀ P.isAffineOpen₁ P.isAffineOpen_inf
  rw [DualityScheme.eulerCharOf_unit] at hχ
  have h0 := BlowDown.ExcSpecialize.finrank_cohomology_zero_of_isIntegral (componentStructure f a η)
  rw [arithmeticGenus, hχ, h0]
  omega

end DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal
