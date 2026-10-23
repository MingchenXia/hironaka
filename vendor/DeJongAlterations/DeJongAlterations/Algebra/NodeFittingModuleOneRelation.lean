import DeJongAlterations.Algebra.NodeFittingModuleBaseChange
import Mathlib.Tactic.FinCases

/-!
# Actual two-generator one-relation modules and their intrinsic first Fitting ideal

The original basis, actual native surjection and its entire proved kernel
internally construct the native finite matrix presentation. No wanted
Fitting ideal or finite-presentation certificate is an input.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open NodeFittingMatrix Matrix

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {R : Type u} [CommRing R] {V : Type v} {U : Type w}
  [AddCommGroup V] [Module R V] [AddCommGroup U] [Module R U]

/-- Any actual finite matrix presentation internally proves native finite presentation. -/
theorem FiniteMatrixPresentation.finitePresentation (P : FiniteMatrixPresentation (R := R) U) :
    Module.FinitePresentation R U := by
  apply Module.finitePresentation_of_free_of_surjective P.toModule P.surjective
  rw [LinearMap.exact_iff.mp P.exact, relationMap_range]
  exact Submodule.fg_span (Set.finite_range _)

/-- The actual one-coordinate relation map into the original free module. -/
def scalarRelationMap (v : V) : (Fin 1 → R) →ₗ[R] V where
  toFun x := x 0 • v
  map_add' x y := by simp [add_smul]
  map_smul' r x := by simp [smul_smul]

/-- Its entire native image is the actual original vector span. -/
theorem scalarRelationMap_range (v : V) :
    LinearMap.range (scalarRelationMap (R := R) v) = Submodule.span R {v} := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  · intro x hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨fun _ => a, ha⟩

/-- The actual single relation column in the original two-coordinate basis. -/
def oneRelationMatrix (b : Module.Basis (Fin 2) R V) (v : V) : Matrix (Fin 2) (Fin 1) R :=
  LinearMap.toMatrix (Pi.basisFun R (Fin 1)) b (scalarRelationMap v)

/-- Every actual original relation entry is its original native basis coefficient. -/
@[simp]
theorem oneRelationMatrix_entry (b : Module.Basis (Fin 2) R V) (v : V) (i : Fin 2) (j : Fin 1) :
    oneRelationMatrix b v i j = b.repr v i := by
  fin_cases j
  rw [oneRelationMatrix, LinearMap.toMatrix_apply]
  simp [Pi.basisFun_apply, scalarRelationMap]

/-- The original entire kernel and original basis internally give the actual finite presentation. -/
def oneRelationPresentation (b : Module.Basis (Fin 2) R V) (v : V) (d : V →ₗ[R] U)
    (hs : Function.Surjective d) (hk : LinearMap.ker d = Submodule.span R {v}) :
    FiniteMatrixPresentation (R := R) U where
  generatorCount := 2
  relationCount := 1
  matrix := oneRelationMatrix b v
  toModule := d.comp b.equivFun.symm.toLinearMap
  surjective := hs.comp b.equivFun.symm.surjective
  exact := exact_in_coordinates (Pi.basisFun R (Fin 1)) b (scalarRelationMap v) d
    (LinearMap.exact_iff.mpr (hk.trans (scalarRelationMap_range v).symm))

/-- The entire intrinsic first Fitting ideal is the actual original two-entry ideal. -/
theorem fittingIdeal_oneRelation [Module.FinitePresentation R U]
    (b : Module.Basis (Fin 2) R V) (v : V) (d : V →ₗ[R] U)
    (hs : Function.Surjective d) (hk : LinearMap.ker d = Submodule.span R {v}) :
    fittingIdeal (R := R) (M := U) 1 = Ideal.span {b.repr v 0, b.repr v 1} := by
  rw [fittingIdeal_eq_presentationIdeal (oneRelationPresentation b v d hs hk) 1]
  change determinantalIdeal 1 (oneRelationMatrix b v) = _
  rw [determinantalIdeal_one]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    change oneRelationMatrix b v i j ∈ {b.repr v 0, b.repr v 1}
    rw [oneRelationMatrix_entry]
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨⟨0, 0⟩, oneRelationMatrix_entry b v 0 0⟩
    · exact ⟨⟨1, 0⟩, oneRelationMatrix_entry b v 1 0⟩

end DeJongAlterations.Algebra.NodeFittingModule
