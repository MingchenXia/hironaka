import DeJongAlterations.Geometry.SteinFiniteFactor
import DeJongAlterations.Geometry.NormalizationInExtension
import DeJongAlterations.Geometry.FiniteBirationalNormalLiftGeneric

/-!
# Actual finite normalization factors of a dominant morphism

A specified finite subfield of the original canonical function field gives
an actual finite normal base scheme and an actual morphism factoring the
original map. The generic field embedding is retained literally. The
relative constant field and geometric connectedness are not assumed outputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.SteinNormalizationFactor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]
  (L : Type u) [Field L] [Algebra S.functionField L]
  [FiniteDimensional S.functionField L]
  (σ : letI := FiniteBirationalNormal.functionFieldAlgebra f;
    L →ₐ[S.functionField] X.functionField)

/-- The given field embedding defines the actual generic map into the actual normalization. -/
def genericFactor : Spec X.functionField ⟶ NormalizationInExtension.normalization S L := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  exact Spec.map (CommRingCat.ofHom (σ.toRingHom.comp
    (NormalizationInExtension.normalizationFunctionFieldEquiv (X := S) L).toRingHom)) ≫
    (NormalizationInExtension.normalization S L).fromSpecStalk
      (genericPoint (NormalizationInExtension.normalization S L))

/-- The generic factor uses the original morphism's actual canonical field map. -/
@[reassoc]
theorem genericFactor_structure :
    genericFactor f L σ ≫ NormalizationInExtension.normalizationStructure S L =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  rw [genericFactor, Category.assoc,
    ← FiniteBirationalNormal.functionFieldMap_fromSpecStalk,
    ← Spec.map_comp_assoc]
  have h :
      (σ.toRingHom.comp
        (NormalizationInExtension.normalizationFunctionFieldEquiv (X := S) L).toRingHom).comp
          (NormalizationInExtension.functionFieldMap
            (NormalizationInExtension.normalizationStructure S L)).hom =
        (NormalizationInExtension.functionFieldMap f).hom := by
    rw [RingHom.comp_assoc,
      NormalizationInExtension.normalizationFunctionFieldEquiv_comp]
    exact σ.comp_algebraMap
  rw [show NormalizationInExtension.functionFieldMap
      (NormalizationInExtension.normalizationStructure S L) ≫
      CommRingCat.ofHom (σ.toRingHom.comp
        (NormalizationInExtension.normalizationFunctionFieldEquiv (X := S) L).toRingHom) =
      NormalizationInExtension.functionFieldMap f from CommRingCat.hom_ext h]
  exact FiniteBirationalNormal.functionFieldMap_fromSpecStalk f

theorem genericFactor_isDominant : IsDominant (genericFactor f L σ) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let q := σ.toRingHom.comp
    (NormalizationInExtension.normalizationFunctionFieldEquiv (X := S) L).toRingHom
  let : IsDominant (Spec.map (CommRingCat.ofHom q)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical q).mpr
    intro a ha
    have ha0 : a = 0 := q.injective (by simpa using ha)
    simp [ha0]
  let := SteinFiniteFactor.genericMap_isDominant
    (X := NormalizationInExtension.normalization S L)
  dsimp only [genericFactor]
  infer_instance

variable [AlgebraicGeometry.IsNoetherian X]
  {k : Type u} [Field k] (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- The actual finite normalization factor, constructed from the specified intermediate field. -/
def factor (hnormal : IsNormalScheme X) :
    X ⟶ NormalizationInExtension.normalization S L := by
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  exact SteinFiniteFactor.lift f (NormalizationInExtension.normalizationStructure S L)
    (genericFactor f L σ) (genericFactor_structure f L σ) hnormal

@[reassoc]
theorem factor_structure (hnormal : IsNormalScheme X) :
    factor f L σ p hnormal ≫ NormalizationInExtension.normalizationStructure S L = f := by
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  exact SteinFiniteFactor.lift_structure f _ _ _ hnormal

/-- The full actual generic morphism agrees with the originally supplied field embedding. -/
@[reassoc]
theorem factor_generic (hnormal : IsNormalScheme X) :
    X.fromSpecStalk (genericPoint X) ≫ factor f L σ p hnormal = genericFactor f L σ := by
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  exact SteinFiniteFactor.lift_generic f _ _ _ hnormal

theorem factor_isDominant (hnormal : IsNormalScheme X) :
    IsDominant (factor f L σ p hnormal) := by
  let : IsDominant (X.fromSpecStalk (genericPoint X) ≫ factor f L σ p hnormal) := by
    rw [factor_generic]
    exact genericFactor_isDominant f L σ
  exact IsDominant.of_comp (X.fromSpecStalk (genericPoint X)) _

/-- The factor's actual canonical generic-stalk homomorphism is the specified field embedding. -/
theorem factor_functionFieldMap (hnormal : IsNormalScheme X) :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    letI := factor_isDominant f L σ p hnormal
    (NormalizationInExtension.functionFieldMap (factor f L σ p hnormal)).hom =
      σ.toRingHom.comp
        (NormalizationInExtension.normalizationFunctionFieldEquiv (X := S) L).toRingHom := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  let := factor_isDominant f L σ p hnormal
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono ((NormalizationInExtension.normalization S L).fromSpecStalk
    (genericPoint (NormalizationInExtension.normalization S L)))).mp
  rw [FiniteBirationalNormal.functionFieldMap_fromSpecStalk, factor_generic]
  rfl

/-- The normalization factor is determined by its actual original generic embedding. -/
theorem factor_unique (hnormal : IsNormalScheme X)
    (a : X ⟶ NormalizationInExtension.normalization S L)
    (ha : a ≫ NormalizationInExtension.normalizationStructure S L = f)
    (hgen : X.fromSpecStalk (genericPoint X) ≫ a = genericFactor f L σ) :
    a = factor f L σ p hnormal := by
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  exact SteinFiniteFactor.generic_lift_unique f _ a (factor f L σ p hnormal)
    ha (factor_structure f L σ p hnormal)
    (hgen.trans (factor_generic f L σ p hnormal).symm)

theorem factor_isProper [IsProper f] (hnormal : IsNormalScheme X) :
    IsProper (factor f L σ p hnormal) := by
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  let : IsProper (factor f L σ p hnormal ≫
      NormalizationInExtension.normalizationStructure S L) := by
    rw [factor_structure]
    infer_instance
  exact IsProper.of_comp _ (NormalizationInExtension.normalizationStructure S L)

end DeJongAlterations.Geometry.SteinNormalizationFactor
