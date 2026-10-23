/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ClosedFibreCanonicalComponent

/-! # The same canonical singleton normalizations and the whole original projections -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.ClosedFibreComponent

universe u

open StableModification StableModification.CurvesField StableModification.Cohomology

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (β : X ⟶ Y) (q : Y ⟶ S) (y : Y) [IsSeparated q]
  [LocallyOfFiniteType (pullback.snd (β ≫ q) (basePoint q y))]
  [IsAffineHom (pullback.diagonal (terminal.from (β.fiber y)))]
  [IsAffineHom (pullback.diagonal
    (terminal.from (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))))]

/-- Reuse the native canonical normalization isomorphism of the actual closed immersion. -/
abbrev canonicalNormalizationIso (η : β.fiber y) :
    Genus.normalizationPoints ({η} : Set (β.fiber y)) ≅
      Genus.normalizationPoints ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) :=
  BlowDown.ExcSpecialize.normalizationPointsIso
    (pullback.snd (β ≫ q) (basePoint q y)) (fibreInTotalCurve β q y) η

@[reassoc]
theorem canonicalNormalizationIso_map (η : β.fiber y) :
    (canonicalNormalizationIso β q y η).hom ≫
      Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) =
      Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ fibreInTotalCurve β q y :=
  BlowDown.ExcSpecialize.normalizationPointsIso_hom_comp _ _ _

/-- The entire original map from the canonical component normalization to `X` agrees. -/
@[reassoc]
theorem canonicalNormalizationIso_fst (η : β.fiber y) :
    (canonicalNormalizationIso β q y η).hom ≫
      Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
          pullback.fst (β ≫ q) (basePoint q y) =
      Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ β.fiberι y := by
  rw [canonicalNormalizationIso_map_assoc, fibreInTotalCurve_fst]

/-- The entire original structure morphism to the same residue field agrees. -/
@[reassoc]
theorem canonicalNormalizationIso_snd (η : β.fiber y) :
    (canonicalNormalizationIso β q y η).hom ≫
      Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
          pullback.snd (β ≫ q) (basePoint q y) =
      Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
        β.fiberToSpecResidueField y := by
  rw [canonicalNormalizationIso_map_assoc, fibreInTotalCurve_snd]

/-- The coefficient action is the original residue-field action transported by that same iso. -/
theorem canonicalNormalizationIso_coeff (η : β.fiber y) :
    (canonicalNormalizationIso β q y η).hom.appTop.hom.comp
      (structureCoeff (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
          pullback.snd (β ≫ q) (basePoint q y))) =
      structureCoeff (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫
        β.fiberToSpecResidueField y) := by
  rw [← canonicalNormalizationIso_snd β q y η]
  ext a
  simp [structureCoeff]

/-- Every original sheaf on `X` has the native pullback comparison along the same whole map. -/
def canonicalNormalizationPullbackIso (η : β.fiber y) (M : X.Modules) :
    (Scheme.Modules.pullback (canonicalNormalizationIso β q y η).hom).obj
      ((Scheme.Modules.pullback
        (Genus.normalizationPointsMap ({fibreInTotalCurve β q y η} :
          Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ≫
            pullback.fst (β ≫ q) (basePoint q y))).obj M) ≅
      (Scheme.Modules.pullback
        (Genus.normalizationPointsMap ({η} : Set (β.fiber y)) ≫ β.fiberι y)).obj M :=
  (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (canonicalNormalizationIso_fst β q y η)).app M

end DeJongAlterations.Geometry.ClosedFibreComponent
