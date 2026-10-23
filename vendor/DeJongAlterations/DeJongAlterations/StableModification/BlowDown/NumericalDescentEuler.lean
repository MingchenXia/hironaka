/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentScheme
import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# The Euler characteristic is invariant under extension of the base field

For a quasi-compact scheme `Y` with affine diagonal over a field `k` and a field extension
`ψ : k → K`, `χ(Y_K, 𝒪) = χ(Y, 𝒪)` (`eulerChar_baseChange_field`): the Čech complex of the base
change for the preimage of a finite affine cover is the base change of the Čech complex
(lane COH2's `Cohomology.cechComplexBaseChangeIso`), `K ⊗_k -` is exact, so it commutes with
cohomology, and `dim_K (K ⊗_k M) = dim_k M`. No finiteness of the cohomology is needed (both sides
use `Module.finrank`). This is the "flat base change of cohomology" step of
`BlowDown.NoClosedExc.NumericalDescent` (the arithmetic genus of a component does not change under
`K / κ(t)`).

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-euler-base-change`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

universe u

open Cohomology CurvesField.Genus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Homology

variable {k K : Type u} [Field k] [Field K] (ψ : k →+* K)

instance : (ModuleCat.extendScalars.{u, u, u} ψ).PreservesHomology := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ψ) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by
      let _ := ψ.toAlgebra
      exact (RingHom.flat_algebraMap_iff).mpr inferInstance)
  infer_instance

/-- **Cohomology commutes with the extension of scalars along a field extension.** -/
theorem finrank_homology_baseChange (C : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Module.finrank K (((baseChange ψ).obj C).homology i) = Module.finrank k (C.homology i) := by
  let e : ((baseChange ψ).obj C).homology i ≅ (ModuleCat.extendScalars.{u, u, u} ψ).obj
      (C.homology i) := (C.sc i).mapHomologyIso (ModuleCat.extendScalars.{u, u, u} ψ)
  rw [e.toLinearEquiv.finrank_eq]
  let _ := ψ.toAlgebra
  exact Module.finrank_baseChange

end Homology

section Euler

variable {k K : Type u} [Field k] [Field K] (ψ : k →+* K) {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of k)) [CompactSpace Y]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]

/-- **`χ(Y_K, 𝒪) = χ(Y, 𝒪)` for a field extension `K / k`** (blueprint
`lem:sm-bdu-euler-base-change`). -/
theorem eulerChar_baseChange_field :
    eulerChar (pullback q (Spec.map (CommRingCat.ofHom ψ))) (structureCoeff (bcSnd ψ q)) =
      eulerChar Y (structureCoeff q) := by
  set D := FiniteAffineCover.choose Y
  have : Fintype D.ι := Fintype.ofFinite _
  rw [BlowDown.eulerChar_baseChange_eq_sum q ψ D.U D.iSup_eq_top D.isAffineOpen
    (Fintype.card D.ι) le_rfl]
  have hY : eulerChar Y (structureCoeff q) = ∑ i ∈ Finset.range (Fintype.card D.ι),
      (-1 : ℤ) ^ i * (Module.finrank k
        (cechCohomology (SheafOfModules.unit Y.ringCatSheaf) D.U (structureCoeff q) i) : ℤ) := by
    unfold eulerChar
    exact homologyEulerChar_eq_sum _ _ fun i hi =>
      ModuleCat.subsingleton_of_isZero (isZero_cechCohomology_of_card_le _ _ _ i hi)
  rw [hY]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  let e := cechComplexBaseChangeIso ψ q (SheafOfModules.unit Y.ringCatSheaf) D.U
    D.isAffineOpen_inf
  have he := ((HomologicalComplex.homologyFunctor _ _ i).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank K (((baseChange ψ).obj
      (cechComplex (SheafOfModules.unit Y.ringCatSheaf) D.U (structureCoeff q))).homology i) =
    Module.finrank K (cechCohomology ((Scheme.Modules.pullback (bcFst ψ q)).obj
      (SheafOfModules.unit Y.ringCatSheaf)) (fun j => bcFst ψ q ⁻¹ᵁ D.U j)
      (structureCoeff (bcSnd ψ q)) i) at he
  rw [← he, finrank_homology_baseChange]

end Euler

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
