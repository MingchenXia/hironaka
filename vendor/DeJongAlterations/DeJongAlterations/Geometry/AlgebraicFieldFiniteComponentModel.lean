import DeJongAlterations.Geometry.AlgebraicFieldOriginalScalarModel
import DeJongAlterations.Geometry.AlgebraicFieldFiniteIntegralModel
import DeJongAlterations.Geometry.FiniteBirationalNormalReducedComponents
import DeJongAlterations.StableModification.Limits.SpreadModificationProjective

/-! Actual reduced scalar components descend inside the SAME original finite-field scalar scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteComponentModel

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldOriginalScalarModel
  FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The canonical actual scalar map for ANY original intermediate field. -/
def scalarMap (E : IntermediateField k L) :
    pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom)) (by
      rw [Category.assoc, ← Spec.map_comp]
      exact pullback.condition)

/-- The actual further original model retains the WHOLE original scalar projection. -/
theorem original_baseChange_comparison {i j : Index k L} (h : j ⟶ i) :
    ((originalModel k L p i).baseChange h).g ≫
      (originalModel_baseChange_isPullback k L p h).isoPullback.hom = scalarLift k L p j := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, scalarLift_fst]
    simp [Model.baseChange, originalModel, scalarLift]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, scalarLift_snd]
    have H := ((originalModel k L p i).baseChange h).isPullback.w
    rw [scalarCone_π] at H
    exact H

/-- An actual reduced scalar component INTERNALLY produces a finite dominant alteration of
ORIGINAL X, inside the SAME literal finite-field scalar scheme, retaining ALL original maps. -/
theorem exists_finite_component_model [IsVariety p]
    (C : irreducibleComponents (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u})) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of E))
        (g : reducedComponent (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) C ⟶ Y)
        (ι : Y ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap k E)))),
        IsVariety q ∧ IsClosedImmersion ι ∧
        ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k E))) = q ∧
        IsPullback g
          (reducedComponentInclusion _ C ≫ pullback.snd p
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))) q
          (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        IsPullback g (reducedComponentInclusion _ C) ι (scalarMap k L p E) ∧
        g ≫ ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E))) =
          reducedComponentInclusion _ C ≫ pullback.fst p
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
        IsFinite (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) ∧
        IsAlteration (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) := by
  let : LocallyOfFinitePresentation p :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType p
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let XL := pullback p b
  let a : reducedComponent XL C ⟶ XL := reducedComponentInclusion XL C
  let qL := a ≫ pullback.snd p b
  let : LocallyOfFinitePresentation qL :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType qL
  let i : Index k L := Opposite.op ⊥
  let r := originalModel k L p i
  obtain ⟨j, h, m, t, hm, ht, htf, hgt⟩ :=
    exists_closedImmersion_model (isLimitScalarCone k L) r
      (originalModel_isFP k L p i) qL a rfl
  let E := levelField k L j
  let : FiniteDimensional k E := levelField_finiteDimensional k L j
  let e := (originalModel_baseChange_isPullback k L p h).isoPullback
  let ι := t ≫ e.hom
  have H := m.isPullback
  rw [scalarCone_π] at H
  let : IsIntegral m.Y :=
    AlgebraicFieldFiniteIntegralModel.isIntegral_of_scalar_pullback E.val.toRingHom m.fY H
  let : IsClosedImmersion t := ht
  let : IsClosedImmersion ι := inferInstance
  have hιf : ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k E))) = m.fY := by
    rw [Category.assoc, IsPullback.isoPullback_hom_snd]
    exact htf
  let : IsSeparated m.fY := by rw [← hιf]; infer_instance
  let : LocallyOfFinitePresentation m.fY := hm.1
  let : QuasiCompact m.fY := hm.2.1
  let : IsVariety (k := E) m.fY := ⟨⟩
  have hwhole : m.g ≫ ι = a ≫ scalarLift k L p j := by
    rw [← Category.assoc, hgt, Category.assoc, original_baseChange_comparison]
  have Hι : IsPullback m.g a ι (scalarLift k L p j) := by
    have Houter : IsPullback m.g (a ≫ pullback.snd p b)
        (ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k E))))
        (Spec.map (CommRingCat.ofHom E.val.toRingHom)) := by
      rw [hιf]
      exact H
    have Hambient := (originalModel k L p j).isPullback
    rw [scalarCone_π] at Hambient
    exact IsPullback.of_bot Houter hwhole Hambient
  have hX : m.g ≫ ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E))) =
      a ≫ pullback.fst p b := by
    rw [reassoc_of% hwhole, scalarLift_fst]
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : IsFinite (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
    inferInstance
  let : IsDominant (a ≫ pullback.fst p b) := inferInstance
  let : IsDominant (m.g ≫ ι ≫ pullback.fst p
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))) := by rw [hX]; infer_instance
  let : IsDominant (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
    IsDominant.of_comp m.g _
  refine ⟨E, inferInstance, m.Y, m.fY, m.g, ι, inferInstance, inferInstance,
    hιf, H, ?_, hX, inferInstance, isAlteration_of_isFinite _⟩
  exact Hι

/-- EVERY original variety INTERNALLY produces a component and its whole finite alteration
and scalar closed-immersion diagram, without supplied component or descent data. -/
theorem exists_original_finite_component_alteration [IsVariety p] :
    ∃ C : irreducibleComponents (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of E))
        (g : reducedComponent (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) C ⟶ Y)
        (ι : Y ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap k E)))),
        IsVariety q ∧ IsClosedImmersion ι ∧
        ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k E))) = q ∧
        IsPullback g
          (reducedComponentInclusion _ C ≫ pullback.snd p
            (Spec.map (CommRingCat.ofHom (algebraMap k L)))) q
          (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        IsPullback g (reducedComponentInclusion _ C) ι (scalarMap k L p E) ∧
        g ≫ ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E))) =
          reducedComponentInclusion _ C ≫ pullback.fst p
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
        IsFinite (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) ∧
        IsAlteration (ι ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : Surjective c := ⟨fun y => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ y⟩⟩
  let : Surjective (pullback.fst p c) := inferInstance
  obtain ⟨x, _⟩ := (pullback.fst p c).surjective (genericPoint X)
  let C : irreducibleComponents (pullback p c : Scheme.{u}) :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨C, exists_finite_component_model k L p C⟩

end DeJongAlterations.Geometry.AlgebraicFieldFiniteComponentModel
