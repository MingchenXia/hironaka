/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.ComponentDegree
import DeJongAlterations.StableModification.BlowDown.ExcSpecializeGenus

/-! # Actual closed-fibre components inside the original total-curve fibre -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.ClosedFibreComponent

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (β : X ⟶ Y) (q : Y ⟶ S) (y : Y)

/-- The actual original residue-field point, viewed over the original base. -/
abbrev basePoint : Spec (Y.residueField y) ⟶ S := Y.fromSpecResidueField y ≫ q

/-- The native map from the original `β`-fibre into the original total-curve fibre. -/
abbrev fibreInTotalCurve : β.fiber y ⟶ pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y) :=
  pullback.mapDesc β (Y.fromSpecResidueField y) q

instance [IsSeparated q] : IsClosedImmersion (fibreInTotalCurve β q y) := by
  change IsClosedImmersion (pullback.mapDesc β (Y.fromSpecResidueField y) q)
  infer_instance

@[reassoc (attr := simp)]
theorem fibreInTotalCurve_fst :
    fibreInTotalCurve β q y ≫ pullback.fst (β ≫ q) (basePoint q y) = β.fiberι y := by
  simp [fibreInTotalCurve, pullback.mapDesc, pullback.map, basePoint, Scheme.Hom.fiberι]

@[reassoc (attr := simp)]
theorem fibreInTotalCurve_snd :
    fibreInTotalCurve β q y ≫ pullback.snd (β ≫ q) (basePoint q y) =
      β.fiberToSpecResidueField y := by
  simp [fibreInTotalCurve, pullback.mapDesc, pullback.map, basePoint,
    Scheme.Hom.fiberToSpecResidueField]

/-- The original residue-field point determines a section of the base-changed `q`. -/
def residueSection : Spec (Y.residueField y) ⟶ pullback q (basePoint q y) :=
  pullback.lift (Y.fromSpecResidueField y) (𝟙 _) (by simp)

/-- The whole original map of curve fibres is constant on the original `β`-fibre. -/
theorem fibreInTotalCurve_comp :
    fibreInTotalCurve β q y ≫ StableModification.Curves.pullbackCompMap β q (basePoint q y) =
      β.fiberToSpecResidueField y ≫ residueSection q y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, StableModification.Curves.pullbackCompMap_fst,
      fibreInTotalCurve_fst_assoc, residueSection, pullback.lift_fst]
    exact pullback.condition
  · simp only [Category.assoc, StableModification.Curves.pullbackCompMap_snd,
      residueSection, pullback.lift_snd, Category.comp_id]
    rfl

variable [IsSeparated q]

/-- A nonclosed point of the actual fibre remains nonclosed in the total-curve fibre. -/
theorem image_nonclosed (η : β.fiber y) (hη : ¬ IsClosed ({η} : Set (β.fiber y))) :
    ¬ IsClosed ({fibreInTotalCurve β q y η} :
      Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) := by
  intro hc
  apply hη
  have he : (fibreInTotalCurve β q y) ⁻¹' {fibreInTotalCurve β q y η} = {η} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => (fibreInTotalCurve β q y).isClosedEmbedding.injective h, congrArg _⟩
  rw [← he]
  exact hc.preimage (fibreInTotalCurve β q y).continuous

/-- A positive-dimensional actual fibre component is a component of the total curve fibre. -/
theorem image_mem_genericPoints [CompactSpace (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))]
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y)) ≤ 1)
    (η : β.fiber y) (hη : ¬ IsClosed ({η} : Set (β.fiber y))) :
    fibreInTotalCurve β q y η ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y)) := by
  by_contra h
  exact image_nonclosed β q y η hη
    (StableModification.CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints hdim h)

/-- The original fibre map contracts the entire closure of each point in the original fibre. -/
theorem contracted_closure (η : β.fiber y) :
    (StableModification.Curves.pullbackCompMap β q (basePoint q y) ''
      closure ({fibreInTotalCurve β q y η} :
        Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y)))).Subsingleton := by
  have hsub : closure ({fibreInTotalCurve β q y η} :
      Set (pullback (C := Scheme.{u}) (β ≫ q) (basePoint q y))) ⊆ Set.range (fibreInTotalCurve β q y) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨η, rfl⟩)
      (fibreInTotalCurve β q y).isClosedMap.isClosed_range
  rintro z₁ ⟨t₁, ht₁, rfl⟩ z₂ ⟨t₂, ht₂, rfl⟩
  obtain ⟨w₁, rfl⟩ := hsub ht₁
  obtain ⟨w₂, rfl⟩ := hsub ht₂
  change (fibreInTotalCurve β q y ≫
      StableModification.Curves.pullbackCompMap β q (basePoint q y)) w₁ =
    (fibreInTotalCurve β q y ≫
      StableModification.Curves.pullbackCompMap β q (basePoint q y)) w₂
  rw [fibreInTotalCurve_comp]
  exact congrArg (residueSection q y) (Subsingleton.elim _ _)

end DeJongAlterations.Geometry.ClosedFibreComponent
