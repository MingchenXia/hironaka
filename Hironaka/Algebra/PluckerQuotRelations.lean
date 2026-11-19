import Hironaka.Algebra.PluckerQuotMinors
import Hironaka.Algebra.PluckerQuotHomogeneous

/-!
# Actual homogeneous Cramer–Plücker equations in the original relation ideal

The concrete degree-r replacement-minor equations belong to the actual
homogeneous relation ideal. No homogeneous-equation or Grassmannian
representability certificate is supplied.
-/

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι κ : Type u} [Fintype ι] [DecidableEq ι]

/- Reused determinant-degree proof from EnvelopeProperty/Berkovich/
ProjectiveNormHomogeneous.lean, SHA256 78455a9e790a354264739d587ba4b9af4b6b08d14593cf8f65e8190a4bf4062a. -/
private theorem homogeneous_det {σ : Type u}
    (M : Matrix ι ι (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous d) :
    M.det.IsHomogeneous (d * Fintype.card ι) := by
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp := IsHomogeneous.prod Finset.univ (fun i ↦ M (s i) i) (fun _ ↦ d)
    (fun i _ ↦ hM (s i) i)
  have hpc : (∏ i, M (s i) i).IsHomogeneous (d * Fintype.card ι) := by
    simpa [Nat.mul_comm] using hp
  simpa using hpc.C_mul (s.sign : R)

/-- The actual original homogeneous replacement-minor equation. -/
def cramerRelation (s t : ι → κ) : MvPolynomial (ι → κ) R :=
  Matrix.det (fun i j ↦ MvPolynomial.X (Function.update s i (t j))) -
    MvPolynomial.X s ^ (Fintype.card ι - 1) * MvPolynomial.X t

/-- The actual replacement-minor polynomial has exactly the required homogeneous degree. -/
theorem cramerRelation_isHomogeneous [Nonempty ι] (s t : ι → κ) :
    (cramerRelation (R := R) s t).IsHomogeneous (Fintype.card ι) := by
  have hd : (Matrix.det (fun i j ↦ (MvPolynomial.X (Function.update s i (t j)) :
      MvPolynomial (ι → κ) R))).IsHomogeneous (Fintype.card ι) := by
    simpa only [one_mul] using homogeneous_det _ 1 (fun _ _ ↦ MvPolynomial.isHomogeneous_X R _)
  have hp := (MvPolynomial.isHomogeneous_X_pow (R := R) s (Fintype.card ι - 1)).mul
    (MvPolynomial.isHomogeneous_X R t)
  have hcard : 1 ≤ Fintype.card ι := Nat.succ_le_of_lt Fintype.card_pos
  rw [Nat.sub_add_cancel hcard] at hp
  exact hd.sub hp

/-- The entire actual Cramer polynomial lies in the original homogeneous minor-relation ideal. -/
theorem cramerRelation_mem_minorRelationIdeal [Nonempty ι] (s t : ι → κ) :
    cramerRelation (R := R) s t ∈ (minorRelationIdeal R ι κ (ι → κ) id).toIdeal := by
  apply mem_minorRelationIdeal R ι κ (ι → κ) id
    ⟨Fintype.card ι, cramerRelation_isHomogeneous s t⟩
  let E := genericMinorEval R ι κ (ι → κ) id
  let C : Matrix ι ι (MvPolynomial (ι → κ) R) :=
    fun i j ↦ MvPolynomial.X (Function.update s i (t j))
  have he : E.mapMatrix C =
      (fun i j ↦ columnMinor (Matrix.mvPolynomialX ι κ R) (Function.update s i (t j))) := by
    ext i j
    simp [E, C, genericMinorEval]
  have hd : E C.det =
      columnMinor (Matrix.mvPolynomialX ι κ R) s ^ (Fintype.card ι - 1) *
        columnMinor (Matrix.mvPolynomialX ι κ R) t :=
    (E.map_det C).trans ((congrArg Matrix.det he).trans (det_replacementMinorMatrix _ s t))
  change E (C.det - MvPolynomial.X s ^ (Fintype.card ι - 1) * MvPolynomial.X t) = 0
  rw [map_sub, map_mul, map_pow, hd]
  simp [E, genericMinorEval]

end Hironaka.Algebra.PluckerQuot
