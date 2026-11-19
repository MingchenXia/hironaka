import Hironaka.Geometry.StableModificationBridge.StableOpenSpecialBoundary
import Hironaka.Geometry.StableModification.Omega.ComponentDegree

/-! Actual nonempty native pole sets and actual positive dualizing degree in positive normalized genus. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace Hironaka.StableModificationBridge.StableOpenNormalizedBoundary

open StableModification
open Omega.ComponentDegree Omega.ComponentNormalization CurvesField.Genus Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X C S : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ S)
    [hNodal : DeJong.IsNodalCurve (β ≫ g)] [hProper : IsProper (β ≫ g)]
    [hIntegral : IsIntegral S] [hNoeth : IsLocallyNoetherian S]
    {K : Type u} [Field K] [hAlgClosed : IsAlgClosed K]
    (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (hp : IsProjectiveOver (pullback.snd (β ≫ g) a))
    (hS : IsNormalScheme S)
    (hgen : ∀ x : X, (β ≫ g) x = genericPoint S → DeJong.IsSmoothAt (β ≫ g) x)
    (hno : Global.NoContractedClopen β g a)
    (η : pullback (C := Scheme.{u}) (β ≫ g) a)
    (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (Curves.pullbackCompMap β g a '' closure {η}).Subsingleton)

include hNodal hProper hIntegral hNoeth hAlgClosed hp hS hgen hno hη hcon

/-- ONLY the original corrected geometry internally produces a NONEMPTY ACTUAL native pole set
in the actual normalization's existing dualizing-degree formula. -/
theorem exists_nonempty_pole_degree :
    ∃ E : Finset (componentNormalization (β ≫ g) a η),
      (∀ y, y ∈ E ↔ componentMap (β ≫ g) a η y ∉ (β ≫ g).smoothLocus) ∧ E.Nonempty ∧
      (∀ y ∈ E, IsClosed ({y} : Set (componentNormalization (β ≫ g) a η))) ∧
      (∀ i, FiniteDimensional K (cohomology
        ((Scheme.Modules.pullback (componentMap (β ≫ g) a η)).obj (Omega.dualizingSheaf (β ≫ g)))
        (structureCoeff (componentStructure (β ≫ g) a η)) i)) ∧
      CurvesField.DualityScheme.eulerCharOf
          ((Scheme.Modules.pullback (componentMap (β ≫ g) a η)).obj (Omega.dualizingSheaf (β ≫ g)))
          (structureCoeff (componentStructure (β ≫ g) a η)) -
        eulerChar (componentNormalization (β ≫ g) a η) (structureCoeff (componentStructure (β ≫ g) a η)) =
        2 * componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) η - 2 + E.card := by
  obtain ⟨W, hW, hne, x, hx, hxW⟩ :=
    StableOpenComponentBoundary.contracted_geometric_component_meets_another β g a hno
      (closure {η}) hη hcon
  have hns := StableOpenSpecialBoundary.component_intersection_not_smooth
    (pullback.snd (β ≫ g) a) (closure {η}) W hη hW hne x hx hxW
  have hsm : pullback.fst (β ≫ g) a x ∈ (β ≫ g).smoothLocus ↔
      x ∈ (pullback.snd (β ≫ g) a).smoothLocus := by
    rw [← Omega.preimage_smoothLocus_eq_of_isNodalCurve (β ≫ g) K a]
    rfl
  have hxns : pullback.fst (β ≫ g) a x ∉ (β ≫ g).smoothLocus := fun h => hns (hsm.mp h)
  have hxrange : x ∈ Set.range (normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) (β ≫ g) a))) := by
    rw [range_normalizationPointsMap]
    exact hx
  obtain ⟨y, hy⟩ := hxrange
  obtain ⟨E, hE, hEc, hfd, hdeg⟩ :=
    degree_pullback_dualizingSheaf_component (β ≫ g) a hp hη hS hgen
  have hyE : y ∈ E := (hE y).mpr (by
    change pullback.fst (β ≫ g) a (normalizationPointsMap ({η} : Set _) y) ∉ (β ≫ g).smoothLocus
    rw [hy]
    exact hxns)
  exact ⟨E, hE, ⟨y, hyE⟩, hEc, hfd, hdeg⟩

/-- The ACTUAL dualizing degree is positive on contracted components of positive normalized genus;
the needed pole point is internally constructed, not supplied as a cardinality certificate. -/
theorem positive_dualizing_degree_of_positive_normalized_genus
    (hg : 1 ≤ componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) η) :
    0 < CurvesField.DualityScheme.eulerCharOf
          ((Scheme.Modules.pullback (componentMap (β ≫ g) a η)).obj (Omega.dualizingSheaf (β ≫ g)))
          (structureCoeff (componentStructure (β ≫ g) a η)) -
        eulerChar (componentNormalization (β ≫ g) a η) (structureCoeff (componentStructure (β ≫ g) a η)) := by
  obtain ⟨E, _, hne, _, _, hdeg⟩ := exists_nonempty_pole_degree β g a hp hS hgen hno η hη hcon
  rw [hdeg]
  have hcard : 0 < E.card := Finset.card_pos.mpr hne
  omega

end Hironaka.StableModificationBridge.StableOpenNormalizedBoundary
