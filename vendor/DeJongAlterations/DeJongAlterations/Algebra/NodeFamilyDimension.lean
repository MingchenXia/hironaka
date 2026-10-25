import DeJongAlterations.Algebra.NodeFamilyBaseChange
import DeJongAlterations.Algebra.FunctionFieldDimension

/-! Dimension one of every actual field-valued node, including the crossing parameter. -/

noncomputable section

open Polynomial

namespace DeJongAlterations.Algebra.NodeFamilyDimension

open NodeBlowupChart NodeFamilyQuadratic FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K]

/-- The actual monic presentation has degree two over every field. -/
theorem quadratic_degree (t : K) : (quadratic t).degree = 2 := by
  unfold quadratic
  compute_degree!

/-- Every literal field node has whole-ring Krull dimension exactly one. -/
theorem node_ringKrullDim (t : K) : ringKrullDim (Node K t) = 1 := by
  let Q := QuadraticAlgebra t
  let : Module.Finite K[X] Q := (quadratic_monic t).finite_adjoinRoot
  let : Algebra.IsIntegral K[X] Q := Algebra.IsIntegral.of_finite K[X] Q
  have hI : (algebraMap K[X] Q).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have hi : Function.Injective (algebraMap K[X] Q) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by rw [quadratic_degree K t]; norm_num)
  have hQ : ringKrullDim Q = ringKrullDim K[X] := le_antisymm
    (ringKrullDim_le_of_isIntegral _ hI)
    (ringKrullDim_le_of_isIntegral_of_injective _ hI hi)
  rw [ringKrullDim_eq_of_ringEquiv (quadraticEquiv t).toRingEquiv, hQ]
  simp

end DeJongAlterations.Algebra.NodeFamilyDimension
