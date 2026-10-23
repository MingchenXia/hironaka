import DeJongAlterations.Algebra.NodeFamilyQuadratic
import Mathlib.RingTheory.Flat.Stability

/-! Genuine coefficient flatness and finite presentation of every actual node algebra. -/

noncomputable section

open Polynomial

namespace DeJongAlterations.Algebra.NodeFamilyFlat

open NodeBlowupChart NodeFamilyQuadratic

universe u

variable {A : Type u} [CommRing A]

/-- The actual monic quotient has its native coefficient-module basis. -/
def quadraticBasis (t : A) :
    Module.Basis (Fin (quadratic t).natDegree) A[X] (QuadraticAlgebra t) :=
  AdjoinRoot.powerBasisAux' (quadratic_monic t)

/-- The original coefficient module of the literal node quotient is flat over every base ring. -/
theorem node_flat (t : A) : Module.Flat A (Node A t) := by
  let : Module.Free A[X] (QuadraticAlgebra t) := (quadratic_monic t).free_adjoinRoot
  let : Module.Flat A[X] (QuadraticAlgebra t) := inferInstance
  let : Module.Flat A (QuadraticAlgebra t) := Module.Flat.trans A A[X] (QuadraticAlgebra t)
  exact Module.Flat.of_linearEquiv (quadraticEquiv t).toLinearEquiv

/-- One literal polynomial relation gives genuine finite presentation, with no Noetherian input. -/
theorem node_finitePresentation (t : A) : Algebra.FinitePresentation A (Node A t) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

end DeJongAlterations.Algebra.NodeFamilyFlat
