/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Geometry.FiniteHyperplanePositiveDegree
import Hironaka.Geometry.FiniteProjectivePreservation
import Hironaka.Geometry.StableModification.Omega.ComponentNormalization

/-! # Actual canonical-normalization applicability of finite hyperplane positivity -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace Hironaka.Geometry.CurveLineBundle

universe u

open StableModification StableModification.Projectivity StableModification.Cohomology
open CurvesField CurvesField.Genus CurvesField.Positive
open Projectivity.LineBundleData

set_option backward.isDefEq.respectTransparency false

/-- A finite original map to the actual projective target internally supplies all
canonical curve inputs, preserving the same singleton normalization and coefficients. -/
theorem degree_normalization_pos_of_finite_hyperplane_power_iso
    {K : Type u} [Field K] [Infinite K] {F Y : Scheme.{u}} [CompactSpace F]
    [IsAffineHom (pullback.diagonal (terminal.from F))]
    (pF : F ⟶ Spec (.of K)) [LocallyOfFiniteType pF]
    (hdim : topologicalKrullDim F ≤ 1) (η : F) (hη : ¬ IsClosed ({η} : Set F))
    (pY : Y ⟶ Spec (.of K)) (hpY : IsProjectiveOver pY)
    {A : Type u} [CommRing A] {c : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A c) (h : F ⟶ Y) [IsFinite h] (hover : h ≫ pY = pF)
    (L : LineBundleData F) (m : ℕ) (hm : 0 < m)
    (e : (L.pullback (normalizationPointsMap ({η} : Set F))).twist
        (unitModule (normalizationPoints ({η} : Set F))) m ≅
      ((hyperplane D).pullback (normalizationPointsMap ({η} : Set F) ≫ h)).twist
        (unitModule (normalizationPoints ({η} : Set F))) 1) :
    0 < Positive.degree (L.pullback (normalizationPointsMap ({η} : Set F)))
      (structureCoeff (normalizationPointsMap ({η} : Set F) ≫ pF)) := by
  let ν := normalizationPointsMap ({η} : Set F)
  let : IsFinite ν := Omega.ComponentNormalization.isFinite_normalizationPointsMap_singleton η pF
  have hpN : IsProjectiveOver (ν ≫ pF) := by
    rw [← hover, ← Category.assoc]
    exact Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite pY hpY (ν ≫ h)
  let : IsProper (ν ≫ pF) := hpN.isProper
  let : CompactSpace (normalizationPoints ({η} : Set F)) :=
    Ample.compactSpace_of_quasiCompact (ν ≫ pF)
  let : IsAffineHom (pullback.diagonal (terminal.from (normalizationPoints ({η} : Set F)))) :=
    Ample.isAffineHom_diagonal_of_isSeparated (ν ≫ pF)
  have hdimN : topologicalKrullDim (normalizationPoints ({η} : Set F)) ≤ 1 :=
    Omega.ComponentNormalization.topologicalKrullDim_normalizationPoints_le η pF hdim
  have hηN : ¬ IsClosed ({genericPoint (normalizationPoints ({η} : Set F))} :
      Set (normalizationPoints ({η} : Set F))) := by
    intro hc
    have hi := ν.isClosedMap _ hc
    rw [Set.image_singleton, Omega.ComponentNormalization.normalizationPointsMap_genericPoint] at hi
    exact hη hi
  exact degree_pos_of_finite_hyperplane_power_iso hpN hdimN hηN (L.pullback ν) m hm D (ν ≫ h) e

end Hironaka.Geometry.CurveLineBundle
