/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ClosedFibreCanonicalNormalization
import DeJongAlterations.Geometry.LineBundleIsoEuler

/-! # Actual degree transport on the same canonical singleton normalization -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.ClosedFibreComponent

universe u

open StableModification StableModification.CurvesField StableModification.Cohomology
open StableModification.Projectivity

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (β : X ⟶ Y) (q : Y ⟶ S) (y : Y) [IsSeparated q]
  [LocallyOfFiniteType (pullback.snd (β ≫ q) (basePoint q y))]
  [IsAffineHom (pullback.diagonal (terminal.from (β.fiber y)))]
  [IsAffineHom (pullback.diagonal
    (terminal.from (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))))]
  [CompactSpace (β.fiber y)]
  [CompactSpace (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))]

/-- The degree equality is derived from the actual canonical normalization iso, with unchanged
original maps, coefficients, and original line-bundle transition data. -/
theorem canonicalNormalization_degree_eq (L : LineBundleData X) (η : β.fiber y) :
    DualityScheme.eulerCharOf
        ((L.pullback (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
          β.fiberι y)).twist (unitModule (Genus.normalizationPoints ({η} : Set (β.fiber y)))) 1)
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
          β.fiberToSpecResidueField y)) -
      Genus.eulerChar (Genus.normalizationPoints ({η} : Set (β.fiber y)))
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
          β.fiberToSpecResidueField y)) =
    DualityScheme.eulerCharOf
        ((L.pullback (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
          Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
            pullback.fst (β ≫ q) (basePoint q y))).twist
              (unitModule (Genus.normalizationPoints ({fibreInTotalCurve β q y η} :
                Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))))) 1)
        (structureCoeff (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
          Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
            pullback.snd (β ≫ q) (basePoint q y))) -
      Genus.eulerChar (Genus.normalizationPoints ({fibreInTotalCurve β q y η} :
          Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))))
        (structureCoeff (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
          Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
            pullback.snd (β ≫ q) (basePoint q y))) := by
  have hL := LineBundleData.eulerCharOf_twist_pullback_iso
    (L.pullback (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
      Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
        pullback.fst (β ≫ q) (basePoint q y))) 1 (canonicalNormalizationIso β q y η)
    (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ β.fiberToSpecResidueField y)
    (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
      Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
        pullback.snd (β ≫ q) (basePoint q y)) (canonicalNormalizationIso_snd β q y η)
  rw [LineBundleData.pullback_comp_eq, canonicalNormalizationIso_fst] at hL
  rw [hL, BlowDown.eulerChar_eq_of_iso _ _ (canonicalNormalizationIso β q y η)
    (canonicalNormalizationIso_snd β q y η)]

end DeJongAlterations.Geometry.ClosedFibreComponent
