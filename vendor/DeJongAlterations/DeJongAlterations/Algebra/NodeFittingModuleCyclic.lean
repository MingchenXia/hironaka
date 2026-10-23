import DeJongAlterations.Algebra.NodeFittingModuleInvariance
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Nakayama

/-! # Actual original finite generators and cyclic Fitting unit ideals -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open NodeFittingMatrix

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M]

/-- The actual given finite free surjection internally produces its full native kernel presentation. -/
def presentationFromSurjection {n : ℕ} (p : (Fin n → R) →ₗ[R] M)
    (hp : Function.Surjective p) : FiniteMatrixPresentation (R := R) M := by
  let h := (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp
    (Module.FinitePresentation.fg_ker p hp)
  let m := Classical.choose h
  let g := Classical.choose (Classical.choose_spec h)
  have hg := Classical.choose_spec (Classical.choose_spec h)
  refine {
    generatorCount := n
    relationCount := m
    matrix := LinearMap.toMatrix' g
    toModule := p
    surjective := hp
    exact := ?_ }
  apply LinearMap.exact_iff.mpr
  rw [relationMap_eq_toLin, Matrix.toLin'_toMatrix']
  exact hg.symm

/-- Actual at-most-i generators imply the entire original i-th intrinsic Fitting ideal is the unit ideal. -/
theorem fittingIdeal_eq_top_of_surjective {n : ℕ} (p : (Fin n → R) →ₗ[R] M)
    (hp : Function.Surjective p) (i : ℕ) (hi : n ≤ i) :
    fittingIdeal (R := R) (M := M) i = ⊤ := by
  rw [fittingIdeal_eq_presentationIdeal (presentationFromSurjection p hp) i]
  change determinantalIdeal (n - i) (presentationFromSurjection p hp).matrix = ⊤
  rw [Nat.sub_eq_zero_of_le hi, determinantalIdeal_zero]

/-- The actual single-coordinate evaluation, retaining the original coefficient ring. -/
def singleCoordinateEvaluation : (Fin 1 → R) →ₗ[R] R where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every actual original coefficient is attained by the actual single-coordinate vector. -/
theorem singleCoordinateEvaluation_surjective :
    Function.Surjective (singleCoordinateEvaluation (R := R)) :=
  fun r => ⟨fun _ => r, rfl⟩

/-- Every actual cyclic original module has the ENTIRE original first Fitting ideal equal to one. -/
theorem fittingIdeal_one_eq_top_of_cyclic (p : R →ₗ[R] M) (hp : Function.Surjective p) :
    fittingIdeal (R := R) (M := M) 1 = ⊤ :=
  fittingIdeal_eq_top_of_surjective (p.comp singleCoordinateEvaluation)
    (hp.comp singleCoordinateEvaluation_surjective) 1 le_rfl

/-- Native Nakayama lifts the SAME actual map from the actual quotient, then gives the full unit ideal. -/
theorem fittingIdeal_one_eq_top_of_residue_surjective (p : R →ₗ[R] M)
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hp : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ.comp p)) :
    fittingIdeal (R := R) (M := M) 1 = ⊤ :=
  fittingIdeal_one_eq_top_of_cyclic p (p.surjective_of_surjective_comp_mkQ I hI hp)

end DeJongAlterations.Algebra.NodeFittingModule
