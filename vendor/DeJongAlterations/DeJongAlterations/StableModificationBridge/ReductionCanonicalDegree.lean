/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.ReductionCanonicalGeometry
import DeJongAlterations.StableModificationBridge.StableProjectivityClosedFibres
import DeJongAlterations.StableModification.BlowDown.ExcSpecializeGenus
import DeJongAlterations.Geometry.LineBundleIsoEuler
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-!
# Canonical singleton normalization degrees across the original nilradical reduction

The native closed-immersion comparison and original whole-map triangle internally transport
the original line bundle and its entire original coefficient-field Euler degree. Actual generic
points and nonclosedness are derived by the same original reduction homeomorphism.

Blueprint: `reduction-canonical-degree.tex`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModificationBridge.ReductionCanonicalDegree

noncomputable section

variable {X : Scheme.{u}}
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from X.nilradical.subscheme))]
  {K : Type u} [Field K] (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]

abbrev normalizationIso (η : X.nilradical.subscheme) :
    Genus.normalizationPoints ({η} : Set X.nilradical.subscheme) ≅
      Genus.normalizationPoints ({X.nilradical.subschemeι η} : Set X) :=
  BlowDown.ExcSpecialize.normalizationPointsIso p X.nilradical.subschemeι η

@[reassoc]
theorem normalizationIso_map (η : X.nilradical.subscheme) :
    (normalizationIso p η).hom ≫
      Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) =
      Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫ X.nilradical.subschemeι :=
  BlowDown.ExcSpecialize.normalizationPointsIso_hom_comp p X.nilradical.subschemeι η

@[reassoc]
theorem normalizationIso_structure (η : X.nilradical.subscheme) :
    (normalizationIso p η).hom ≫
      (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) ≫ p) =
      Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫
        (X.nilradical.subschemeι ≫ p) := by
  rw [← Category.assoc, normalizationIso_map, Category.assoc]

theorem normalizationIso_coeff (η : X.nilradical.subscheme) :
    (normalizationIso p η).hom.appTop.hom.comp
        (structureCoeff (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) ≫ p)) =
      structureCoeff (Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫
        (X.nilradical.subschemeι ≫ p)) := by
  rw [← normalizationIso_structure p η]
  ext a
  simp only [structureCoeff, Scheme.Hom.comp_appTop, RingHom.comp_apply]
  rfl

variable [CompactSpace X] [CompactSpace X.nilradical.subscheme]

theorem normalization_degree_eq (L : LineBundleData X) (η : X.nilradical.subscheme) :
    DualityScheme.eulerCharOf
        (((L.pullback X.nilradical.subschemeι).pullback
          (Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme))).twist
            (unitModule (Genus.normalizationPoints ({η} : Set X.nilradical.subscheme))) 1)
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫
          (X.nilradical.subschemeι ≫ p))) -
      Genus.eulerChar (Genus.normalizationPoints ({η} : Set X.nilradical.subscheme))
        (structureCoeff (Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫
          (X.nilradical.subschemeι ≫ p))) =
    DualityScheme.eulerCharOf
        ((L.pullback (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X))).twist
          (unitModule (Genus.normalizationPoints ({X.nilradical.subschemeι η} : Set X))) 1)
        (structureCoeff (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) ≫ p)) -
      Genus.eulerChar (Genus.normalizationPoints ({X.nilradical.subschemeι η} : Set X))
        (structureCoeff (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) ≫ p)) := by
  have hL := LineBundleData.eulerCharOf_twist_pullback_iso
    (L.pullback (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X))) 1
    (normalizationIso p η)
    (Genus.normalizationPointsMap ({η} : Set X.nilradical.subscheme) ≫ (X.nilradical.subschemeι ≫ p))
    (Genus.normalizationPointsMap ({X.nilradical.subschemeι η} : Set X) ≫ p)
    (normalizationIso_structure p η)
  rw [LineBundleData.pullback_comp_eq, normalizationIso_map,
    ← LineBundleData.pullback_comp_eq] at hL
  rw [hL, BlowDown.eulerChar_eq_of_iso _ _ (normalizationIso p η) (normalizationIso_structure p η)]

omit [CompactSpace X.nilradical.subscheme]
    [IsAffineHom (pullback.diagonal (terminal.from X.nilradical.subscheme))] in
theorem positiveCanonicalComponents_reduction (hp : IsProjectiveOver p) (L : LineBundleData X)
    (hpos : StableProjectivityClosedFibres.PositiveCanonicalComponents p hp L) :
    StableProjectivityClosedFibres.PositiveCanonicalComponents (X.nilradical.subschemeι ≫ p)
      (Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp X.nilradical.subschemeι)
      (L.pullback X.nilradical.subschemeι) := by
  let : CompactSpace X.nilradical.subscheme :=
    Genus.compactSpace_of_isAffineHom X.nilradical.subschemeι
  let : IsAffineHom (pullback.diagonal (terminal.from X.nilradical.subscheme)) :=
    Genus.isAffineHom_diagonal_of_isAffineHom X.nilradical.subschemeι
  intro η hη hηnc
  have hηg := (ReductionCanonicalGeometry.mem_genericPoints_iff X η).mp hη
  have hηnc' : ¬ IsClosed ({X.nilradical.subschemeι η} : Set X) :=
    fun h => hηnc ((ReductionCanonicalGeometry.isClosed_singleton_iff X η).mpr h)
  have h := hpos (X.nilradical.subschemeι η) hηg hηnc'
  exact lt_of_lt_of_eq h (normalization_degree_eq p L η).symm

end

end DeJongAlterations.StableModificationBridge.ReductionCanonicalDegree
