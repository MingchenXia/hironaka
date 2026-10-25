/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ClosedFibreCanonicalNormalization
import DeJongAlterations.Geometry.CanonicalComponentGenusMinimal
import DeJongAlterations.Geometry.ProjectiveIdentity

/-! # Actual closed-fibre projectivity gives projectivity of the same canonical component -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.ClosedFibreComponent

universe u

open StableModification StableModification.CurvesField StableModification.Omega

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (β : X ⟶ Y) (q : Y ⟶ S) (y : Y) [IsSeparated q]
  [LocallyOfFiniteType (pullback.snd (β ≫ q) (basePoint q y))]
  [IsAffineHom (pullback.diagonal (terminal.from (β.fiber y)))]
  [IsAffineHom (pullback.diagonal
    (terminal.from (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))))]

/-- The literal original projective `β`-fibre produces the actual projectivity needed by the
canonical-component degree theorem, over the SAME residue field. -/
theorem isProjectiveOver_canonicalNormalization
    (hpT : IsProjectiveOver (β.fiberToSpecResidueField y)) (η : β.fiber y) :
    IsProjectiveOver
      (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
          pullback.snd (β ≫ q) (basePoint q y)) := by
  have : IsProper (β.fiberToSpecResidueField y) := hpT.isProper
  have hNT := ComponentNormalization.isProjectiveOver_normalizationPoints η
    (β.fiberToSpecResidueField y) hpT
  let e := canonicalNormalizationIso β q y η
  have H := hNT.precomp_isIso e.inv
  have he : e.inv ≫ (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
      β.fiberToSpecResidueField y) =
      Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
          pullback.snd (β ≫ q) (basePoint q y) := by
    apply (cancel_epi e.hom).mp
    rw [e.hom_inv_id_assoc]
    exact (canonicalNormalizationIso_snd β q y η).symm
  rwa [he] at H

end DeJongAlterations.Geometry.ClosedFibreComponent
