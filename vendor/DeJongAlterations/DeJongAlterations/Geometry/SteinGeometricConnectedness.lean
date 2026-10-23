import DeJongAlterations.Algebra.SteinTensorConnected
import DeJongAlterations.Geometry.SteinCurveFactor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual generic geometric connectedness of the same constant-field factor

No proper connectedness theorem is presumed.  The native generic fibre
is handled through the exact original generic-stalk scalar triangle,
the actual function-field isomorphism, and a dense generic-point map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

namespace DeJongAlterations.Geometry.SteinGeometricConnectedness

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual spectrum of a field with relatively closed constants is geometrically connected. -/
theorem spec_geometricallyConnected {K F : Type u} [Field K] [Field F] [Algebra K F]
    (h : integralClosure K F = ⊥) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap K F))) := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro E _ _
  let : ConnectedSpace (PrimeSpectrum (E ⊗[K] F)) :=
    Algebra.SteinTensorConnected.connectedSpace_tensorSpectrum h
  let : ConnectedSpace (PrimeSpectrum (F ⊗[K] E)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm K F E).toRingEquiv).connectedSpace_iff.mpr inferInstance
  let : ConnectedSpace (Spec (.of (F ⊗[K] E))) := by
    change ConnectedSpace (PrimeSpectrum (F ⊗[K] E))
    infer_instance
  exact (pullbackSpecIso K F E).hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Over a field, any actual dominant source controls geometric connectedness of the target. -/
theorem geometricallyConnected_of_dominant {K : Type u} [Field K]
    {Z T : Scheme.{u}} (j : Z ⟶ T) [IsDominant j] (p : T ⟶ Spec (.of K))
    (h : GeometricallyConnected (j ≫ p)) : GeometricallyConnected p := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro E _ e
  let := h
  let b := pullback.map (j ≫ p) e p e j (𝟙 _) (𝟙 _)
    (by simp) (by simp)
  have hb : Set.range b =
      (pullback.fst p e) ⁻¹' Set.range j := by
    simpa using
      Scheme.Pullback.range_map (j ≫ p) e p e j (𝟙 _) (𝟙 _)
        (by simp) (by simp)
  have hd : DenseRange b := by
    change Dense (Set.range b)
    rw [hb]
    exact j.denseRange.preimage (pullback.fst p e).isOpenMap
  let : PreconnectedSpace (pullback p e : Scheme.{u}) := hd.preconnectedSpace b.continuous
  let : Nonempty (pullback p e : Scheme.{u}) := Nonempty.map b inferInstance
  exact ⟨inferInstance⟩

/-- Actual canonical constants of an integral scheme suffice, with no presentation or properness. -/
theorem geometricallyConnected_of_integralClosure_eq_bot {K : Type u} [Field K]
    {T : Scheme.{u}} [IsIntegral T] (p : T ⟶ Spec (.of K))
    (h : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      integralClosure K T.functionField = ⊥) : GeometricallyConnected p := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let : IsDominant (T.fromSpecStalk (genericPoint T)) :=
    SteinFiniteFactor.genericMap_isDominant (X := T)
  apply geometricallyConnected_of_dominant (T.fromSpecStalk (genericPoint T)) p
  rw [← SteinGenericFiber.structureFieldMap_generic p]
  exact spec_geometricallyConnected h

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

attribute [local instance] GenericFiberIntegral.genericFiber_isIntegral
  GenericFiberFunctionField.genericFiberι_isDominant

/-- Closed constants transport to the native generic fibre through the literal scalar triangle. -/
theorem genericFiber_integralClosure_eq_bot
    (h : letI := FiniteBirationalNormal.functionFieldAlgebra f
      integralClosure S.functionField X.functionField = ⊥) :
    letI : Algebra (S.residueField (genericPoint S))
        (f.fiber (genericPoint S)).functionField :=
      SeparableGenericSmoothness.functionFieldAlgebra
        (f.fiberToSpecResidueField (genericPoint S))
    integralClosure (S.residueField (genericPoint S))
      (f.fiber (genericPoint S)).functionField = ⊥ := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let T := f.fiber (genericPoint S)
  let K := S.residueField (genericPoint S)
  let p := f.fiberToSpecResidueField (genericPoint S)
  let : Algebra K T.functionField := SeparableGenericSmoothness.functionFieldAlgebra p
  let : Algebra S.functionField K := (S.residue (genericPoint S)).hom.toAlgebra
  let : Module.Finite S.functionField K :=
    RingHom.Finite.of_surjective (S.residue (genericPoint S)).hom
      IsLocalRing.residue_surjective
  let : Algebra S.functionField T.functionField :=
    ((NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))).hom.comp
      (NormalizationInExtension.functionFieldMap f).hom).toAlgebra
  let : IsScalarTower S.functionField K T.functionField :=
    .of_algebraMap_eq' (SteinGenericFiber.coefficient_triangle f).symm
  let e : X.functionField ≃ₐ[S.functionField] T.functionField :=
    { (GenericFiberFunctionField.functionFieldIso f).commRingCatIsoToRingEquiv with
      commutes' := fun r => rfl }
  apply le_antisymm ?_ bot_le
  intro a ha
  have haK : IsIntegral S.functionField a := isIntegral_trans a ha
  have hm : e.symm a ∈ integralClosure S.functionField X.functionField := haK.map e.symm
  rw [h] at hm
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hm
  apply Algebra.mem_bot.mpr
  refine ⟨algebraMap S.functionField K r, ?_⟩
  rw [← IsScalarTower.algebraMap_apply S.functionField K T.functionField]
  exact (e.commutes r).symm.trans
    ((congrArg e hr).trans (e.apply_symm_apply a))

/-- Closed actual relative constants give genuine geometric connectedness of the native generic fibre. -/
theorem genericFiber_geometricallyConnected
    (h : letI := FiniteBirationalNormal.functionFieldAlgebra f
      integralClosure S.functionField X.functionField = ⊥) :
    GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S)) :=
  geometricallyConnected_of_integralClosure_eq_bot _ (genericFiber_integralClosure_eq_bot f h)

/-- The original constructed factor's native generic fibre is genuinely geometrically connected. -/
theorem factor_genericFiber_geometricallyConnected [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
    [AlgebraicGeometry.IsNoetherian X] {k : Type u} [Field k]
    (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hnormal : IsNormalScheme X) :
    GeometricallyConnected ((SteinCurveFactor.factor f hdim p hnormal).fiberToSpecResidueField
      (genericPoint (SteinCurveFactor.base f))) := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.factor_isDominant f hdim p hnormal
  apply genericFiber_geometricallyConnected (SteinCurveFactor.factor f hdim p hnormal)
  let := FiniteBirationalNormal.functionFieldAlgebra (SteinCurveFactor.factor f hdim p hnormal)
  rw [← algebraicClosure_toSubalgebra,
    SteinCurveFactor.factor_algebraicClosure_eq_bot f hdim p hnormal]
  rfl

end DeJongAlterations.Geometry.SteinGeometricConnectedness
