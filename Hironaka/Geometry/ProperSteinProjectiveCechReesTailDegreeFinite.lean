/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesLinear
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite original Rees tails prove finite actual original degree components

The closed native linear-locus proof is adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsFixedTarget.lean`,
SHA256 1c3ec98dbf68a5df2334783b0718495a6e4a4c71ce7b80beb8785d4ce790a6f7.
The original constant-coefficient tail quotient argument is constructed here.
This is an algebraic producer; actual geometric homogeneous action is a
separate proof obligation, never replaced by an output-finiteness certificate.
-/
open scoped Polynomial DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesTailDegreeFinite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual original polynomial constant coefficient of an actual original Rees element. -/
def constantCoefficient : reesAlgebra I →+* R :=
  Polynomial.constantCoeff.comp (reesAlgebra I).val.toRingHom

/-- Every ORIGINAL coefficient is retained by the actual original constant map. -/
theorem constantCoefficient_algebraMap (r : R) :
    constantCoefficient I (algebraMap R (reesAlgebra I) r) = r := by
  change (Polynomial.C r).coeff 0 = r
  exact Polynomial.coeff_C_zero

/-- Every actual original positive monomial has precisely zero original constant coefficient. -/
theorem constantCoefficient_monomial_pos {e : ℕ} (he : 0<e) (a : ↥(I^e)) :
    constantCoefficient I (ReesMultiplication.monomial I e a) = 0 := by
  change (Polynomial.monomial e a.val).coeff 0 = 0
  simp only [Polynomial.coeff_monomial, if_neg (Nat.ne_of_gt he)]

variable (M : ℕ → Type u) [∀ d, AddCommGroup (M d)] [∀ d, Module R (M d)]
  [Module (reesAlgebra I) (⨁ d : ℕ, M d)] [IsScalarTower R (reesAlgebra I) (⨁ d : ℕ, M d)]

/-- The GENUINE original Rees span of ALL unchanged original summands at or above d. -/
def tailSpan (d : ℕ) : Submodule (reesAlgebra I) (⨁ j : ℕ, M j) :=
  Submodule.span (reesAlgebra I) {x | ∃ j, d≤j ∧ ∃ y : M j, DirectSum.lof R ℕ M j y=x}

/-- The actual target coefficient action retains the original R-module M_d unchanged. -/
@[instance_reducible]
def coefficientAction (d : ℕ) : Module (reesAlgebra I) (M d) :=
  Module.compHom (M d) (constantCoefficient I)

private def linearLocus {A V W : Type u} [Semiring A]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (L : V →+ W) : Submodule A V where
  carrier := {x | ∀ a : A, L (a • x)=a • L x}
  zero_mem' a := by simp only [smul_zero, map_zero]
  add_mem' hx hy a := by rw [smul_add, map_add, hx a, hy a, map_add, smul_add]
  smul_mem' b x hx a := by rw [smul_smul, hx (a*b), mul_smul, hx b]

variable (hmono : ∀ e (a : ↥(I^e)) j (y : M j), ∃ z : M (e+j),
  ReesMultiplication.monomial I e a • DirectSum.lof R ℕ M j y = DirectSum.lof R ℕ M (e+j) z)
include hmono

private theorem tailSpan_le_linearLocus (d : ℕ) :
    letI := coefficientAction I M d
    tailSpan I M d ≤ linearLocus (DirectSum.component R ℕ M d).toAddMonoidHom := by
  let := coefficientAction I M d
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hdj, y, rfl⟩
  intro p
  change DirectSum.component R ℕ M d (p • DirectSum.lof R ℕ M j y) =
    constantCoefficient I p • DirectSum.component R ℕ M d (DirectSum.lof R ℕ M j y)
  induction p using ReesLinear.rees_induction_on I with
  | hzero => simp only [zero_smul, map_zero]
  | hadd p q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | hmonomial e a =>
    by_cases he : e=0
    · subst e
      have hm : ReesMultiplication.monomial I 0 a = algebraMap R (reesAlgebra I) a.val := by
        apply Subtype.ext
        change (Polynomial.monomial 0 a.val : R[X]) = Polynomial.C a.val
        rfl
      have hR (r : R) (x : ⨁ k : ℕ, M k) : algebraMap R (reesAlgebra I) r • x = r • x := by
        calc
          _ = (r • (1 : reesAlgebra I)) • x := by rw [Algebra.smul_def, mul_one]
          _ = r • ((1 : reesAlgebra I) • x) := smul_assoc _ _ _
          _ = r • x := by rw [one_smul]
      rw [hm, hR, (DirectSum.component R ℕ M d).map_smul,
        constantCoefficient_algebraMap]
    · obtain ⟨z, hz⟩ := hmono e a j y
      rw [hz, constantCoefficient_monomial_pos I (Nat.pos_of_ne_zero he), zero_smul]
      change (DirectSum.lof R ℕ M (e+j) z) d = 0
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (show d≠e+j by omega)]

/-- The SAME original degree projection is genuinely Rees-linear on the ENTIRE actual original tail. -/
def tailProjection (d : ℕ) :
    letI := coefficientAction I M d
    tailSpan I M d →ₗ[reesAlgebra I] M d := by
  letI := coefficientAction I M d
  exact {
    toFun := fun x => DirectSum.component R ℕ M d x.val
    map_add' := fun x y => (DirectSum.component R ℕ M d).map_add x.val y.val
    map_smul' := fun p x => tailSpan_le_linearLocus I M hmono d x.property p }

/-- Every original class in degree d is retained by the SAME actual original tail projection. -/
theorem tailProjection_surjective (d : ℕ) :
    letI := coefficientAction I M d
    Function.Surjective (tailProjection I M hmono d) := by
  let := coefficientAction I M d
  intro y
  refine ⟨⟨DirectSum.lof R ℕ M d y, Submodule.subset_span ⟨d, le_rfl, y, rfl⟩⟩, ?_⟩
  exact DirectSum.component.lof_self R d y

/-- Finite ENTIRE original Rees modules and genuine homogeneous action prove finite EVERY original component. -/
theorem degree_finite [IsNoetherianRing (reesAlgebra I)] [Module.Finite (reesAlgebra I) (⨁ j : ℕ, M j)]
    (d : ℕ) : Module.Finite R (M d) := by
  let := coefficientAction I M d
  let : Module.Finite (reesAlgebra I) (tailSpan I M d) := inferInstance
  let : Module.Finite (reesAlgebra I) (M d) := Module.Finite.of_surjective
    (tailProjection I M hmono d) (tailProjection_surjective I M hmono d)
  let : Algebra (reesAlgebra I) R := (constantCoefficient I).toAlgebra
  let : IsScalarTower (reesAlgebra I) R (M d) := by
    constructor
    intro p r x
    change (constantCoefficient I p * r) • x = constantCoefficient I p • (r • x)
    exact mul_smul _ _ _
  exact Module.Finite.of_restrictScalars_finite (reesAlgebra I) R (M d)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesTailDegreeFinite
