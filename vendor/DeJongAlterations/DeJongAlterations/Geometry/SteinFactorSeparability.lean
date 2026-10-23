import DeJongAlterations.Algebra.SteinSeparability
import DeJongAlterations.Geometry.SteinCurveFactor
import DeJongAlterations.Geometry.RelativeGenericSmoothness

/-!
# Separable constants and genuine generic smoothness of the same finite factor

The input is the original canonical relative separating-basis property.
The native constant field, the original finite base normalization and the
original constructed source factor remain exactly the released objects.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SteinFactorSeparability

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

/-- Separability is derived for the actual intrinsic constant field from the original separating basis. -/
theorem constantField_isSeparable
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    Algebra.IsSeparable S.functionField (SteinCurveFactor.constantField f) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  obtain ⟨s, hs, hsep⟩ := hsep
  let : Algebra.IsSeparable
      (IntermediateField.adjoin S.functionField (Set.range ((↑) : s → X.functionField)))
      X.functionField := by
    convert! hsep <;> simp
  exact Algebra.SteinSeparability.algebraicClosure_isSeparable hs.1

variable [LocallyOfFiniteType f]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include hdim p in
/-- The very same actual finite normalization structure map is generically etale. -/
theorem baseMap_isGenericallyEtale
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    IsGenericallyEtale (SteinCurveFactor.baseMap f) := by
  let := SteinCurveFactor.constantField_finite f hdim
  let := constantField_isSeparable f hsep
  exact NormalizationInExtension.normalizationStructure_isGenericallyEtale
    (SteinCurveFactor.constantField f) p

include p in
/-- Separability of the actual canonical field embedding of the actual finite base map. -/
theorem baseFunctionField_isSeparable
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    letI := SteinCurveFactor.base_isIntegral f hdim
    letI := SteinCurveFactor.baseMap_isDominant f hdim
    letI := FiniteBirationalNormal.functionFieldAlgebra (SteinCurveFactor.baseMap f)
    Algebra.IsSeparable S.functionField (SteinCurveFactor.base f).functionField := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.baseMap_isDominant f hdim
  let : IsFinite (SteinCurveFactor.baseMap f) := SteinCurveFactor.baseMap_isFinite f hdim p
  exact (FiniteBirationalNormal.functionField_finite_separable
    (SteinCurveFactor.baseMap f) (baseMap_isGenericallyEtale f hdim p hsep)).2

variable [AlgebraicGeometry.IsNoetherian X] (hnormal : IsNormalScheme X)

/-- The actual constructed factor's canonical generic-stalk map is formally smooth. -/
theorem factor_formallySmooth_functionField
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    letI := SteinCurveFactor.base_isIntegral f hdim
    letI := SteinCurveFactor.factor_isDominant f hdim p hnormal
    (NormalizationInExtension.functionFieldMap
      (SteinCurveFactor.factor f hdim p hnormal)).hom.FormallySmooth := by
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
    baseFunctionField_isSeparable f hdim p hsep
  let : Algebra.FormallyEtale S.functionField (SteinCurveFactor.base f).functionField :=
    Algebra.FormallyEtale.of_isSeparable _ _
  let : Algebra.FormallySmooth S.functionField X.functionField :=
    RelativeGenericSmoothness.formallySmooth_functionField f hsep
  exact Algebra.FormallySmooth.of_restrictScalars S.functionField
    (SteinCurveFactor.base f).functionField X.functionField

/-- The constructed factor is locally of finite presentation, derived from the original finite type. -/
theorem factor_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (SteinCurveFactor.factor f hdim p hnormal) := by
  let : IsFinite (SteinCurveFactor.baseMap f) := SteinCurveFactor.baseMap_isFinite f hdim p
  let : IsLocallyNoetherian (SteinCurveFactor.base f) :=
    LocallyOfFiniteType.isLocallyNoetherian (SteinCurveFactor.baseMap f ≫ p)
  let : LocallyOfFiniteType
      (SteinCurveFactor.factor f hdim p hnormal ≫ SteinCurveFactor.baseMap f) := by
    rw [SteinCurveFactor.factor_structure]
    infer_instance
  let : LocallyOfFiniteType (SteinCurveFactor.factor f hdim p hnormal) :=
    locallyOfFiniteType_of_comp _ (SteinCurveFactor.baseMap f)
  infer_instance

include hdim p hnormal in
/-- The generic point lies in the actual smooth locus of the same factor. -/
theorem genericPoint_mem_factor_smoothLocus
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    letI := factor_locallyOfFinitePresentation f hdim p hnormal
    genericPoint X ∈ (SteinCurveFactor.factor f hdim p hnormal).smoothLocus := by
  let := SteinCurveFactor.base_isIntegral f hdim
  let := SteinCurveFactor.factor_isDominant f hdim p hnormal
  let := factor_locallyOfFinitePresentation f hdim p hnormal
  rw [Scheme.Hom.mem_smoothLocus]
  let e := (SteinCurveFactor.base f).presheaf.stalkCongr
    (.of_eq (genericPoint_map_of_isDominant
      (SteinCurveFactor.factor f hdim p hnormal)).symm)
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso e.hom
    ((SteinCurveFactor.factor f hdim p hnormal).stalkMap (genericPoint X))).mp
  exact factor_formallySmooth_functionField f hdim p hnormal hsep

/-- An actual nonempty dense source open on which the original factor is smooth. -/
theorem exists_dense_factor_smooth_open
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    ∃ U : X.Opens, Nonempty U ∧ Dense (U : Set X) ∧
      Smooth (U.ι ≫ SteinCurveFactor.factor f hdim p hnormal) := by
  let := factor_locallyOfFinitePresentation f hdim p hnormal
  let U := (SteinCurveFactor.factor f hdim p hnormal).smoothLocus
  have hη : genericPoint X ∈ U := genericPoint_mem_factor_smoothLocus f hdim p hnormal hsep
  exact ⟨U, ⟨⟨genericPoint X, hη⟩⟩, U.isOpen.dense ⟨genericPoint X, hη⟩,
    GenericSmoothness.smooth_smoothLocus _⟩

end DeJongAlterations.Geometry.SteinFactorSeparability
