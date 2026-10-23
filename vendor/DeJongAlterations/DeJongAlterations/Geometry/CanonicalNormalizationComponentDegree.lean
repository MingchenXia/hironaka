/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.CanonicalNormalizationComponentCover
import DeJongAlterations.Geometry.LineBundleIsoEuler
import DeJongAlterations.StableModificationBridge.StableProjectivityClosedFibres

/-! # Original coefficients, original line-bundle degrees and nonclosed canonical labels -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CanonicalNormalization

universe u

open StableModification StableModification.CurvesField StableModification.CurvesField.Genus
open StableModification.Projectivity StableModification.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from T))]
  [Finite (genericPoints T)] {K : Type u} [Field K] (p : T ⟶ Spec (.of K))

/-- The whole original structure map is retained by each actual canonical piece. -/
@[reassoc]
theorem componentIncl_structure (η : genericPoints T) :
    componentIncl η ≫ (normalizationPointsMap (genericPoints T) ≫ p) =
      normalizationPointsMap ({η.1} : Set T) ≫ p := by
  rw [componentIncl_fromNormalization_assoc]

/-- This is the SAME original coefficient action, without identifying or replacing the field. -/
theorem componentIncl_coeff (η : genericPoints T) :
    (componentIncl η).appTop.hom.comp
        (structureCoeff (normalizationPointsMap (genericPoints T) ≫ p)) =
      structureCoeff (normalizationPointsMap ({η.1} : Set T) ≫ p) := by
  rw [← componentIncl_structure p η]
  ext a
  simp only [structureCoeff, Scheme.Hom.comp_appTop, RingHom.comp_apply]
  rfl

variable [CompactSpace T]

/-- Both actual Euler terms agree on the SAME original canonical singleton normalization. -/
theorem degree_componentIncl_eq (L : LineBundleData T) (η : genericPoints T) :
    DualityScheme.eulerCharOf
        (((L.pullback (normalizationPointsMap (genericPoints T))).pullback
          (componentIncl η)).twist (unitModule (component η)) 1)
        (structureCoeff (componentIncl η ≫ (normalizationPointsMap (genericPoints T) ≫ p))) -
      eulerChar (component η)
        (structureCoeff (componentIncl η ≫ (normalizationPointsMap (genericPoints T) ≫ p))) =
    DualityScheme.eulerCharOf ((L.pullback (normalizationPointsMap ({η.1} : Set T))).twist
        (unitModule (normalizationPoints ({η.1} : Set T))) 1)
        (structureCoeff (normalizationPointsMap ({η.1} : Set T) ≫ p)) -
      eulerChar (normalizationPoints ({η.1} : Set T))
        (structureCoeff (normalizationPointsMap ({η.1} : Set T) ≫ p)) := by
  rw [LineBundleData.pullback_comp_eq, componentIncl_fromNormalization, componentIncl_structure]

variable [LocallyOfFiniteType p]

omit [Finite (genericPoints T)] [CompactSpace T] in
include p in
/-- A closed original label would make the WHOLE canonical piece a discrete finite-map fibre. -/
theorem nonclosed_label_of_nonclosed_componentPoint (η : genericPoints T) (z : component η)
    (hz : ¬ IsClosed ({z} : Set (component η))) : ¬ IsClosed ({η.1} : Set T) := by
  intro hc
  have : IsFinite (normalizationPointsMap ({η.1} : Set T)) :=
    Omega.ComponentNormalization.isFinite_normalizationPointsMap_singleton η.1 p
  have he : (normalizationPointsMap ({η.1} : Set T)) ⁻¹' {η.1} =
      (Set.univ : Set (component η)) := by
    apply Set.eq_univ_of_forall
    intro w
    have hw := Omega.ComponentNormalization.normalizationPointsMap_mem_closure η.1 w
    rw [hc.closure_eq] at hw
    exact hw
  have hd := (normalizationPointsMap ({η.1} : Set T)).isDiscrete_preimage_singleton η.1
  rw [he] at hd
  have : DiscreteTopology (component η) := isDiscrete_univ_iff.mp hd
  exact hz (isClosed_discrete _)

/-- Original canonical positivity internally supplies the exact natural clopen-assembly inputs. -/
theorem positive_componentIncl_degree (hp : IsProjectiveOver p) (L : LineBundleData T)
    (hpos : StableModificationBridge.StableProjectivityClosedFibres.PositiveCanonicalComponents p hp L)
    (η : genericPoints T) (hz : ∃ z : component η, ¬ IsClosed ({z} : Set (component η))) :
    0 < DualityScheme.eulerCharOf
        (((L.pullback (normalizationPointsMap (genericPoints T))).pullback
          (componentIncl η)).twist (unitModule (component η)) 1)
        (structureCoeff (componentIncl η ≫ (normalizationPointsMap (genericPoints T) ≫ p))) -
      eulerChar (component η)
        (structureCoeff (componentIncl η ≫ (normalizationPointsMap (genericPoints T) ≫ p))) := by
  rw [degree_componentIncl_eq]
  obtain ⟨z, hz⟩ := hz
  exact hpos η.1 η.2 (nonclosed_label_of_nonclosed_componentPoint p η z hz)

end DeJongAlterations.Geometry.CanonicalNormalization
