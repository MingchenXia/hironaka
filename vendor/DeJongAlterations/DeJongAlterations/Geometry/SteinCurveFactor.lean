import DeJongAlterations.Algebra.SteinCurveConstants
import DeJongAlterations.Geometry.SteinGenericFiber
import DeJongAlterations.Geometry.SteinNormalizationFactor

/-!
# The actual finite constant-field factor of a generic curve

The intermediate field is the native relative algebraic closure in the
original canonical function field. Its finiteness is derived from the
dimension of the actual generic fibre. The finite base normalization
and the normal-source factor morphism are constructed internally.

Geometric connectedness and the smooth-case separability conclusion of
source 4.12 are separate obligations, not hypotheses or conclusions here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.SteinCurveFactor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

/-- The actual constants inside the original canonical source function field. -/
abbrev constantField : Type u :=
  letI := FiniteBirationalNormal.functionFieldAlgebra f
  algebraicClosure S.functionField X.functionField

instance constantField_algebra : Algebra S.functionField (constantField f) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  infer_instance

/-- The original subfield inclusion, over the original generic-stalk embedding. -/
def constantEmbedding :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    constantField f →ₐ[S.functionField] X.functionField := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  exact (algebraicClosure S.functionField X.functionField).val

/-- The actual generic curve produces a genuinely finite constant field. -/
theorem constantField_finite [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1) :
    FiniteDimensional S.functionField (constantField f) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let : Algebra.EssFiniteType S.functionField X.functionField :=
    FiniteBirationalNormal.functionFieldMap_essFiniteType f
  exact Algebra.SteinCurveConstants.finite_constants_of_trdeg_le_one
    S.functionField X.functionField (SteinGenericFiber.trdeg_le_one f hdim)

/-- There are no further algebraic constants in the original ambient field. -/
theorem algebraicClosure_constants_eq_bot :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    algebraicClosure (constantField f) X.functionField = ⊥ := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  exact algebraicClosure.algebraicClosure_eq_bot S.functionField X.functionField

/-- The actual normalization of the original base in its actual constant field. -/
abbrev base : Scheme.{u} := NormalizationInExtension.normalization S (constantField f)

/-- The original finite normalization structure map. -/
abbrev baseMap : base f ⟶ S :=
  NormalizationInExtension.normalizationStructure S (constantField f)

variable [LocallyOfFiniteType f]
  (hdim : topologicalKrullDim (f.fiber (genericPoint S)) ≤ 1)

include hdim in
theorem base_isIntegral : IsIntegral (base f) := by
  let := constantField_finite f hdim
  exact NormalizationInExtension.isIntegral_normalization (constantField f)

include hdim in
theorem base_isNormalScheme : IsNormalScheme (base f) := by
  let := constantField_finite f hdim
  exact NormalizationInExtension.normalization_isNormalScheme (constantField f)

include hdim in
theorem baseMap_isDominant : IsDominant (baseMap f) := by
  let := constantField_finite f hdim
  infer_instance

/-- The actual comparison retains the originally constructed normalization, with no field model input. -/
def baseFunctionFieldEquiv :
    letI := base_isIntegral f hdim
    (base f).functionField ≃+* constantField f := by
  let := constantField_finite f hdim
  exact NormalizationInExtension.normalizationFunctionFieldEquiv (constantField f)

variable [AlgebraicGeometry.IsNoetherian X]
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]

omit [AlgebraicGeometry.IsNoetherian X] in
include hdim p in
theorem baseMap_isFinite : IsFinite (baseMap f) := by
  let := constantField_finite f hdim
  exact NormalizationInExtension.normalizationStructure_isFinite (constantField f) p

/-- The actual source-to-normalized-base morphism, constructed from its intrinsic constants. -/
def factor (hnormal : IsNormalScheme X) : X ⟶ base f := by
  let := constantField_finite f hdim
  exact SteinNormalizationFactor.factor f (constantField f) (constantEmbedding f) p hnormal

@[reassoc]
theorem factor_structure (hnormal : IsNormalScheme X) :
    factor f hdim p hnormal ≫ baseMap f = f := by
  let := constantField_finite f hdim
  exact SteinNormalizationFactor.factor_structure f
    (constantField f) (constantEmbedding f) p hnormal

theorem factor_isDominant (hnormal : IsNormalScheme X) :
    IsDominant (factor f hdim p hnormal) := by
  let := constantField_finite f hdim
  exact SteinNormalizationFactor.factor_isDominant f
    (constantField f) (constantEmbedding f) p hnormal

/-- The literal native generic-stalk map is the original inclusion of the intrinsic constant field. -/
theorem factor_functionFieldMap (hnormal : IsNormalScheme X) :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    letI := base_isIntegral f hdim
    letI := factor_isDominant f hdim p hnormal
    (NormalizationInExtension.functionFieldMap (factor f hdim p hnormal)).hom =
      (constantEmbedding f).toRingHom.comp (baseFunctionFieldEquiv f hdim).toRingHom := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := constantField_finite f hdim
  exact SteinNormalizationFactor.factor_functionFieldMap f
    (constantField f) (constantEmbedding f) p hnormal

theorem factor_isProper (hf : IsProper f) (hnormal : IsNormalScheme X) :
    IsProper (factor f hdim p hnormal) := by
  let := hf
  let := constantField_finite f hdim
  exact SteinNormalizationFactor.factor_isProper f
    (constantField f) (constantEmbedding f) p hnormal

/-- The finite normal base and its actual dominant source factor are all derived from the original curve. -/
theorem finite_normal_factor (hnormal : IsNormalScheme X) :
    IsIntegral (base f) ∧ IsNormalScheme (base f) ∧
      IsFinite (baseMap f) ∧ IsDominant (baseMap f) ∧
      IsDominant (factor f hdim p hnormal) ∧
      factor f hdim p hnormal ≫ baseMap f = f :=
  ⟨base_isIntegral f hdim, base_isNormalScheme f hdim, baseMap_isFinite f hdim p,
    baseMap_isDominant f hdim, factor_isDominant f hdim p hnormal,
    factor_structure f hdim p hnormal⟩

/-- The actual canonical relative field of the constructed factor has no further algebraic constants. -/
theorem factor_algebraicClosure_eq_bot (hnormal : IsNormalScheme X) :
    letI := base_isIntegral f hdim
    letI := factor_isDominant f hdim p hnormal
    letI := FiniteBirationalNormal.functionFieldAlgebra (factor f hdim p hnormal)
    algebraicClosure (base f).functionField X.functionField = ⊥ := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := base_isIntegral f hdim
  let := factor_isDominant f hdim p hnormal
  let : Algebra (base f).functionField X.functionField :=
    FiniteBirationalNormal.functionFieldAlgebra (factor f hdim p hnormal)
  let e := baseFunctionFieldEquiv f hdim
  let : Algebra (base f).functionField (constantField f) := e.toRingHom.toAlgebra
  let : IsScalarTower (base f).functionField (constantField f) X.functionField :=
    .of_algebraMap_eq' (factor_functionFieldMap f hdim p hnormal)
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxC : IsAlgebraic (constantField f) x :=
    (mem_algebraicClosure_iff.mp hx).tower_top (constantField f)
  have hm : x ∈ algebraicClosure (constantField f) X.functionField :=
    mem_algebraicClosure_iff.mpr hxC
  rw [algebraicClosure_constants_eq_bot f] at hm
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hm
  obtain ⟨a, ha⟩ := e.surjective c
  apply IntermediateField.mem_bot.mpr
  refine ⟨a, ?_⟩
  exact (IsScalarTower.algebraMap_apply (base f).functionField (constantField f)
    X.functionField a).trans ((congrArg (algebraMap (constantField f) X.functionField)
      ha).trans hc)

end DeJongAlterations.Geometry.SteinCurveFactor
