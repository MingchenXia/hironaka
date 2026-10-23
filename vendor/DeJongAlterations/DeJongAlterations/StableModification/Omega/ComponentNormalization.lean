/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusReduced
import DeJongAlterations.StableModification.BlowDown.Normalization
import DeJongAlterations.Geometry.CurveCompactificationRestriction
import DeJongAlterations.Geometry.CurveBoundaryBasic
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension
import DeJongAlterations.Geometry.FiberDimensionGenericFinite
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-!
# The normalization of an irreducible component of a curve

For a point `η` of a scheme `C` with affine diagonal, `C̃_η = normalizationPoints {η}` is the
relative normalization of `C` in `Spec κ(η)` (Codex's `CurvesField.Genus.normalizationPoints`,
the scheme whose genus is `componentGenus`); for a generic point `η` of a curve this is the
normalization of the irreducible component with generic point `η`
(Temkin, `semi-stable.tex` App. B, l. 4384–4433, the `C̃_η` of `lastlem`).

This file records the general properties of `π : C̃_η → C` which the degree formula for `ν^* ω`
on a component (`cor:sm-omega-bcf-restriction-component`, blueprint
`sm-omega-component-degree.tex`) needs:

* `C̃_η` is integral (`isIntegral_normalizationPoints`) and normal
  (`isNormalScheme_normalizationPoints`);
* `π` maps into `closure {η}`, onto it, and sends the generic point to `η`
  (`range_normalizationPointsMap`, `normalizationPointsMap_genericPoint`);
* over a field, `C̃_η` is locally Noetherian, of dimension at most that of `C`, projective when `C`
  is (`topologicalKrullDim_normalizationPoints_le`, `isProjectiveOver_normalizationPoints`).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.StableModification.Omega.ComponentNormalization

open CurvesField.Genus

section Points

variable {C : Scheme.{u}} (η : C)

/-- The scheme `∐_{η' ∈ {η}} Spec κ(η')` is `Spec κ(η)`. -/
def pointsSchemeIso : pointsScheme C ({η} : Set C) ≅ Spec (C.residueField η) :=
  letI := Set.uniqueSingleton η
  coproductUniqueIso (fun η' : ({η} : Set C) => Spec (C.residueField η'.1))

instance nonempty_pointsScheme_singleton : Nonempty (pointsScheme C ({η} : Set C)) :=
  ⟨(pointsSchemeIso η).inv (Nonempty.some inferInstance)⟩

instance isIntegral_pointsScheme_singleton : IsIntegral (pointsScheme C ({η} : Set C)) :=
  isIntegral_of_isOpenImmersion (pointsSchemeIso η).hom

theorem isNormalScheme_pointsScheme_singleton :
    IsNormalScheme (pointsScheme C ({η} : Set C)) :=
  Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion (pointsSchemeIso η).hom
    (isNormalScheme_spec (C.residueField η))

theorem pointsMap_singleton_apply (z : pointsScheme C ({η} : Set C)) :
    pointsMap C ({η} : Set C) z = η :=
  pointsMap_mem z

end Points

section Normalization

variable {C : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from C))] (η : C)

instance isIntegral_normalizationPoints : IsIntegral (normalizationPoints ({η} : Set C)) :=
  inferInstanceAs (IsIntegral (pointsMap C ({η} : Set C)).normalization)

/-- **The normalization of a component is normal** (it is the relative normalization of `C` in the
normal integral scheme `Spec κ(η)`; `BlowDown.isNormalScheme_normalization`). -/
theorem isNormalScheme_normalizationPoints : IsNormalScheme (normalizationPoints ({η} : Set C)) :=
  BlowDown.isNormalScheme_normalization (pointsMap C ({η} : Set C))
    (isNormalScheme_pointsScheme_singleton η)

/-- `π : C̃_η → C` maps into the closure of `η`. -/
theorem normalizationPointsMap_mem_closure (y : normalizationPoints ({η} : Set C)) :
    normalizationPointsMap ({η} : Set C) y ∈ closure ({η} : Set C) := by
  have hd := (pointsMap C ({η} : Set C)).toNormalization.denseRange
  refine map_mem_closure (normalizationPointsMap ({η} : Set C)).continuous (hd y) ?_
  rintro _ ⟨w, rfl⟩
  change ((pointsMap C ({η} : Set C)).toNormalization ≫
    (pointsMap C ({η} : Set C)).fromNormalization) w ∈ ({η} : Set C)
  rw [Scheme.Hom.toNormalization_fromNormalization]
  exact pointsMap_singleton_apply η w

/-- `π : C̃_η → C` maps onto the closure of `η`. -/
theorem range_normalizationPointsMap :
    Set.range (normalizationPointsMap ({η} : Set C)) = closure ({η} : Set C) := by
  refine (Set.range_subset_iff.mpr (normalizationPointsMap_mem_closure η)).antisymm ?_
  have hcl : IsClosed (Set.range (normalizationPointsMap ({η} : Set C))) :=
    (normalizationPointsMap ({η} : Set C)).isClosedMap.isClosed_range
  refine hcl.closure_subset_iff.mpr ?_
  rw [Set.singleton_subset_iff]
  obtain ⟨w⟩ := nonempty_pointsScheme_singleton η
  refine ⟨(pointsMap C ({η} : Set C)).toNormalization w, ?_⟩
  change ((pointsMap C ({η} : Set C)).toNormalization ≫
    (pointsMap C ({η} : Set C)).fromNormalization) w = η
  rw [Scheme.Hom.toNormalization_fromNormalization]
  exact pointsMap_singleton_apply η w

/-- `π` sends the generic point of `C̃_η` to `η`. -/
theorem normalizationPointsMap_genericPoint :
    normalizationPointsMap ({η} : Set C) (genericPoint (normalizationPoints ({η} : Set C))) = η := by
  obtain ⟨y, hy⟩ : η ∈ Set.range (normalizationPointsMap ({η} : Set C)) := by
    rw [range_normalizationPointsMap]; exact subset_closure rfl
  have h1 : normalizationPointsMap ({η} : Set C) (genericPoint _) ⤳ η := by
    have := (genericPoint_specializes y).map (normalizationPointsMap ({η} : Set C)).continuous
    rwa [hy] at this
  have h2 : η ⤳ normalizationPointsMap ({η} : Set C) (genericPoint _) :=
    specializes_iff_mem_closure.mpr (normalizationPointsMap_mem_closure η _)
  exact (h1.antisymm h2).eq

/-- If the closure of `η` has a point other than `η`, then `C̃_η` has a point other than its
generic point. -/
theorem exists_ne_genericPoint {z : C} (hz : z ∈ closure ({η} : Set C)) (hzη : z ≠ η) :
    ∃ y : normalizationPoints ({η} : Set C), y ≠ genericPoint _ := by
  rw [← range_normalizationPointsMap] at hz
  obtain ⟨y, rfl⟩ := hz
  refine ⟨y, fun h => hzη ?_⟩
  rw [h, normalizationPointsMap_genericPoint]

section Field

variable {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
theorem isFinite_normalizationPointsMap_singleton :
    IsFinite (normalizationPointsMap ({η} : Set C)) :=
  isFinite_normalizationPointsMap (S := ({η} : Set C)) p

instance locallyOfFiniteType_normalizationPointsMap_comp :
    LocallyOfFiniteType (normalizationPointsMap ({η} : Set C) ≫ p) := by
  have := isFinite_normalizationPointsMap_singleton η p
  infer_instance

include p in
theorem isLocallyNoetherian_normalizationPoints :
    IsLocallyNoetherian (normalizationPoints ({η} : Set C)) :=
  LocallyOfFiniteType.isLocallyNoetherian (normalizationPointsMap ({η} : Set C) ≫ p)

include p in
/-- **The normalization of a component has dimension at most that of `C`** (it is finite over
`C`: on the affine cover by the `π⁻¹ V`, `Γ(π⁻¹ V, 𝒪)` is integral over `Γ(V, 𝒪_C)`). -/
theorem topologicalKrullDim_normalizationPoints_le {n : ℕ} (hdim : topologicalKrullDim C ≤ n) :
    topologicalKrullDim (normalizationPoints ({η} : Set C)) ≤ n := by
  have := isFinite_normalizationPointsMap_singleton η p
  set π := normalizationPointsMap ({η} : Set C)
  have hcov : IsOpenCover fun V : C.affineOpens => π ⁻¹ᵁ V.1 := by
    rw [IsOpenCover, eq_top_iff]
    intro y _
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hyV⟩
  refine Geometry.FunctionFieldDimension.topologicalKrullDim_le_of_openCover _ n
    ((normalizationPoints ({η} : Set C)).openCoverOfIsOpenCover _ hcov) fun V => ?_
  change topologicalKrullDim (π ⁻¹ᵁ V.1).toScheme ≤ n
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine (π ⁻¹ᵁ V.1).toScheme := V.2.preimage π
  rw [Geometry.FiberDimensionGenericFinite.topologicalKrullDim_eq_ringKrullDim_of_isAffine]
  refine (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral _
    (π ∣_ V.1).finite_appTop.to_isIntegral).trans ?_
  rw [← Geometry.FiberDimensionGenericFinite.topologicalKrullDim_eq_ringKrullDim_of_isAffine]
  exact (topologicalKrullDim_subspace_le C (V.1 : Set C)).trans hdim

/-- **The normalization of a component of a projective scheme is projective** (`π` is finite). -/
theorem isProjectiveOver_normalizationPoints (hp : IsProjectiveOver p) :
    IsProjectiveOver (normalizationPointsMap ({η} : Set C) ≫ p) := by
  have := isFinite_normalizationPointsMap_singleton η p
  exact Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp _

end Field

end Normalization

end DeJongAlterations.StableModification.Omega.ComponentNormalization
