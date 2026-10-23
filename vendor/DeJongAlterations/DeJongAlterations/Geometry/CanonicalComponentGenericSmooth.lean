/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.ComponentDegree

/-! # Original reduced generic stalks are smooth over the same perfect field -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every original generic component point is smooth over the same original perfect field,
without assuming projectivity of the actual whole source. -/
theorem genericPoint_mem_smoothLocus {K : Type u} [Field K] [PerfectField K]
    {F : Scheme.{u}} [IsReduced F] (p : F ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (η : F) (hη : η ∈ genericPoints F) : η ∈ p.smoothLocus := by
  let : Field (F.presheaf.stalk η) :=
    (isField_stalk_of_closure_mem_irreducibleComponents F η hη).toField
  have := LocallyOfFiniteType.stalkMap p η
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(p.stalkMap η).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (p η)
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (p η).asIdeal.primeCompl
    (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (p η)) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (p η)) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (p η))
  exact Algebra.FormallySmooth.of_perfectField

end DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal
