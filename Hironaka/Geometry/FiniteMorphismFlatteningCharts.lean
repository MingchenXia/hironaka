import Hironaka.Algebra.FiniteMorphismFlattening
import Hironaka.Geometry.ModuleFlattening
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual finite flat closed affine chart transforms

Every chart uses the native algebra image of the original coefficient
tensor map. The closed immersion into the literal original tensor spectrum
and its coefficient triangle are constructed from the actual range
surjection. The minor ideal and all flat chart transforms are internally
produced from the original finite algebra.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka.Geometry.FiniteMorphismFlattening

open Algebra.FiniteMorphismFlattening Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual closed chart transform inside the original coefficient tensor spectrum. -/
def chartTransformInclusion (S : Subalgebra R (FractionRing R)) :
    Spec (.of (pureTransformAlgebra R A S)) ⟶ Spec (.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (tensorAlgMap R A S).rangeRestrict.toRingHom)

instance chartTransformInclusion_isClosedImmersion (S : Subalgebra R (FractionRing R)) :
    IsClosedImmersion (chartTransformInclusion R A S) :=
  IsClosedImmersion.spec_of_surjective _ (tensorAlgMap_rangeRestrict_surjective R A S)

/-- The literal structure map from the actual chart transform to its original blowup chart. -/
abbrev chartTransformMap (S : Subalgebra R (FractionRing R)) :
    Spec (.of (pureTransformAlgebra R A S)) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (pureTransformAlgebra R A S)))

/-- The actual closed immersion preserves the original coefficient structure map. -/
@[reassoc (attr := simp)]
theorem chartTransformInclusion_structure (S : Subalgebra R (FractionRing R)) :
    chartTransformInclusion R A S ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      chartTransformMap R A S := by
  rw [chartTransformInclusion, ← Spec.map_comp]
  congr 1

/-- The original generic algebra maps into its actual chart algebra image through the original inclusion. -/
def genericToChartTransform (S : Subalgebra R (FractionRing R)) :
    Spec (.of (FractionRing R ⊗[R] A)) ⟶ Spec (.of (pureTransformAlgebra R A S)) :=
  Spec.map (CommRingCat.ofHom (pureTransformAlgebra R A S).val.toRingHom)

/-- The actual generic map factors exactly through the actual closed chart transform. -/
@[reassoc (attr := simp)]
theorem genericToChartTransform_inclusion (S : Subalgebra R (FractionRing R)) :
    genericToChartTransform R A S ≫ chartTransformInclusion R A S =
      Spec.map (CommRingCat.ofHom (tensorAlgMap R A S).toRingHom) := by
  rw [genericToChartTransform, chartTransformInclusion, ← Spec.map_comp]
  rfl

/-- Native finiteness of the chart structure follows from actual module finiteness. -/
theorem chartTransformMap_isFinite (S : Subalgebra R (FractionRing R))
    [Module.Finite S (pureTransformAlgebra R A S)] : IsFinite (chartTransformMap R A S) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Native flatness of the chart structure follows from actual module flatness. -/
theorem chartTransformMap_flat (S : Subalgebra R (FractionRing R))
    [Module.Flat S (pureTransformAlgebra R A S)] : Flat (chartTransformMap R A S) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The actual original coefficient tensor spectrum is the native affine base change. -/
theorem chartTensor_isPullback (S : Subalgebra R (FractionRing R)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] A)))
      (Spec.map (CommRingCat.ofHom (S := S ⊗[R] A)
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S A)

/-- The original finite algebra internally chooses the actual projective modification
and literal finite minor cover on which the actual closed algebra-image chart transforms
have native finite flat structure maps. -/
theorem exists_projective_modification_finite_flat_chartTransforms [IsDomain R] [Module.Finite R A] :
    ∃ (n r : ℕ) (m : Fin n → A) (V : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧ (minorIdeal V).FG ∧ minorIdeal V ≠ ⊥ ∧
      IsProjectiveOver (affineBlowupStructure (minorIdeal V)) ∧
      IsModification (affineBlowupStructure (minorIdeal V)) ∧
      ∀ s : (ModuleFlattening.minorFractionOpenCover V).I₀,
        let S := affineBlowupFractionChart (minorIdeal V) (columnMinor V s.val)
        IsFinite (chartTransformMap R A S) ∧ Flat (chartTransformMap R A S) := by
  obtain ⟨n, r, m, V, hm, hfg, hI, hfree⟩ :=
    exists_nonzero_minorIdeal_free_finite_flat_algebra R A
  refine ⟨n, r, m, V, hm, hfg, hI, affineBlowupStructure_isProjective _ hfg,
    ModuleFlattening.minorBlowup_isModification V hI hfg, fun s ↦ ?_⟩
  obtain ⟨hf, hfin, hflat, hrank⟩ := hfree s.val s.property
  let S := affineBlowupFractionChart (minorIdeal V) (columnMinor V s.val)
  let : Module.Finite S (pureTransformAlgebra R A S) := hfin
  let : Module.Flat S (pureTransformAlgebra R A S) := hflat
  exact ⟨chartTransformMap_isFinite R A S, chartTransformMap_flat R A S⟩

end Hironaka.Geometry.FiniteMorphismFlattening
