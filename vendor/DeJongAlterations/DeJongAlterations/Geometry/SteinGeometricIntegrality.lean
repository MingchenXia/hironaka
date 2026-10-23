import DeJongAlterations.Algebra.SteinTensorDomain
import DeJongAlterations.Algebra.SteinSeparatingTower
import DeJongAlterations.Geometry.SteinGeometricConnectedness
import DeJongAlterations.Geometry.SteinFactorSeparability
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Actual generic geometric integrality of the same constant-field factor

The endpoint uses the original canonical separating basis and internally
derives its extension to the same finite normalization's function field.
All-fibre proper connectedness is a separate theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

namespace DeJongAlterations.Geometry.SteinGeometricIntegrality

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance isIntegral_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
  ⟨fun {X Y} e h => by
    let := h
    let : Nonempty Y := Nonempty.map e.hom inferInstance
    exact isIntegral_of_isOpenImmersion (f := e.inv)⟩

/-- The actual regular field spectrum is geometrically integral, for arbitrary scalar fields. -/
theorem spec_geometricallyIntegral {K F : Type u} [Field K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] {ι : Type u} {v : ι → F}
    (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F]
    (h : integralClosure K F = ⊥) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap K F))) := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro E _ _
  let : IsDomain (E ⊗[K] F) := Algebra.SteinTensorDomain.isDomain_tensorProduct hv h
  let : IsDomain (F ⊗[K] E) := (Algebra.TensorProduct.comm K F E).injective.isDomain
  let : IsIntegral (Spec (.of (F ⊗[K] E))) := inferInstance
  exact isIntegral_of_isOpenImmersion (f := (pullbackSpecIso K F E).hom)

/-- Actual schematic dominance transfers geometric integrality over a field. -/
theorem geometricallyIntegral_of_schemeTheoreticallyDominant {K : Type u} [Field K]
    {Z T : Scheme.{u}} (j : Z ⟶ T) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (p : T ⟶ Spec (.of K)) (h : GeometricallyIntegral (j ≫ p)) :
    GeometricallyIntegral p := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro E _ e
  let := h
  let b := pullback.map (j ≫ p) e p e j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hb : IsPullback (pullback.fst (j ≫ p) e) b j (pullback.fst p e) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd p e) (v₂₂ := p)
    · simpa [b] using (IsPullback.of_hasPullback (j ≫ p) e)
    · simp [b]
    · exact IsPullback.of_hasPullback p e
  let : IsSchemeTheoreticallyDominant b := IsSchemeTheoreticallyDominant.of_isPullback hb
  let : QuasiCompact b := by rw [← hb.isoPullback_hom_snd]; infer_instance
  let : IsIntegral (pullback (j ≫ p) e : Scheme.{u}) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  let : IsReduced (pullback p e : Scheme.{u}) := IsSchemeTheoreticallyDominant.isReduced b
  have hr : Set.range b = (pullback.fst p e) ⁻¹' Set.range j := by
    simpa using Scheme.Pullback.range_map (j ≫ p) e p e j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hd : DenseRange b := by
    change Dense (Set.range b)
    rw [hr]
    exact j.denseRange.preimage (pullback.fst p e).isOpenMap
  let : IrreducibleSpace (pullback p e : Scheme.{u}) := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set (pullback p e : Scheme.{u}))
    rw [← hd.closure_eq]
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ _).image b b.continuous.continuousOn).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The actual generic-point scheme map discharges schematic dominance and quasi-compactness. -/
theorem geometricallyIntegral_of_genericField {K : Type u} [Field K]
    {T : Scheme.{u}} [IsIntegral T] (p : T ⟶ Spec (.of K))
    (h : GeometricallyIntegral (T.fromSpecStalk (genericPoint T) ≫ p)) :
    GeometricallyIntegral p := by
  let : IsDominant (T.fromSpecStalk (genericPoint T)) :=
    SteinFiniteFactor.genericMap_isDominant (X := T)
  let : IsSchemeTheoreticallyDominant (T.fromSpecStalk (genericPoint T)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  let : QuasiCompact (T.fromSpecStalk (genericPoint T)) :=
    ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  exact geometricallyIntegral_of_schemeTheoreticallyDominant _ p h

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

attribute [local instance] GenericFiberIntegral.genericFiber_isIntegral
  GenericFiberFunctionField.genericFiberι_isDominant

/-- The actual two field isomorphisms transport the canonical field property to the native fibre. -/
theorem genericFiber_geometricallyIntegral_of_field
    (h : GeometricallyIntegral (Spec.map (NormalizationInExtension.functionFieldMap f))) :
    GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)) := by
  let T := f.fiber (genericPoint S)
  let K := S.residueField (genericPoint S)
  let p := f.fiberToSpecResidueField (genericPoint S)
  let : Algebra K T.functionField := SeparableGenericSmoothness.functionFieldAlgebra p
  let : IsIso (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))) :=
    GenericFiberFunctionField.functionFieldMap_isIso f
  let : IsIso (S.residue (genericPoint S)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(S.residue (genericPoint S)).hom.injective, IsLocalRing.residue_surjective⟩
  have hc : Spec.map (CommRingCat.ofHom (algebraMap K T.functionField)) ≫
      Spec.map (S.residue (genericPoint S)) =
      Spec.map (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))) ≫
        Spec.map (NormalizationInExtension.functionFieldMap f) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (SteinGenericFiber.coefficient_triangle f))
  have hpre : GeometricallyIntegral
      (Spec.map (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))) ≫
        Spec.map (NormalizationInExtension.functionFieldMap f)) :=
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral _ _).mpr h
  rw [← hc] at hpre
  have hfield : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap K T.functionField))) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral _ _).mp hpre
  apply geometricallyIntegral_of_genericField p
  rw [← SteinGenericFiber.structureFieldMap_generic p]
  exact hfield

/-- The original canonical separating basis gives geometric integrality of the same factor's generic fibre. -/
theorem factor_genericFiber_geometricallyIntegral [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
    [AlgebraicGeometry.IsNoetherian X] {k : Type u} [Field k]
    (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hnormal : IsNormalScheme X)
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    GeometricallyIntegral ((SteinCurveFactor.factor f hdim p hnormal).fiberToSpecResidueField
      (genericPoint (SteinCurveFactor.base f))) := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.baseMap_isDominant f hdim
  let := SteinCurveFactor.factor_isDominant f hdim p hnormal
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := FiniteBirationalNormal.functionFieldAlgebra (SteinCurveFactor.baseMap f)
  let := FiniteBirationalNormal.functionFieldAlgebra (SteinCurveFactor.factor f hdim p hnormal)
  have hc : NormalizationInExtension.functionFieldMap f =
      NormalizationInExtension.functionFieldMap (SteinCurveFactor.baseMap f) ≫
        NormalizationInExtension.functionFieldMap (SteinCurveFactor.factor f hdim p hnormal) := by
    simpa only [SteinCurveFactor.factor_structure] using
      (NormalizationInExtension.functionFieldMap_comp
        (SteinCurveFactor.factor f hdim p hnormal) (SteinCurveFactor.baseMap f))
  let : IsScalarTower S.functionField (SteinCurveFactor.base f).functionField X.functionField :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hc)
  let : Algebra.IsSeparable S.functionField (SteinCurveFactor.base f).functionField :=
    SteinFactorSeparability.baseFunctionField_isSeparable f hdim p hsep
  let : Algebra.EssFiniteType S.functionField X.functionField :=
    FiniteBirationalNormal.functionFieldMap_essFiniteType f
  let : Algebra.EssFiniteType (SteinCurveFactor.base f).functionField X.functionField :=
    Algebra.EssFiniteType.of_comp S.functionField (SteinCurveFactor.base f).functionField
      X.functionField
  obtain ⟨s, hs, hsep⟩ := hsep
  let : Algebra.IsSeparable
      (IntermediateField.adjoin S.functionField (Set.range ((↑) : s → X.functionField)))
      X.functionField := by convert! hsep <;> simp
  have hL := Algebra.SteinSeparatingTower.separatingBasis_of_algebraic
    (L := (SteinCurveFactor.base f).functionField) ((↑) : s → X.functionField) hs
  let := hL.2
  apply genericFiber_geometricallyIntegral_of_field (SteinCurveFactor.factor f hdim p hnormal)
  apply spec_geometricallyIntegral hL.1.1
  rw [← algebraicClosure_toSubalgebra,
    SteinCurveFactor.factor_algebraicClosure_eq_bot f hdim p hnormal]
  rfl

end DeJongAlterations.Geometry.SteinGeometricIntegrality
