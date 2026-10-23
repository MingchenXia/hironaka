import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Actual flat integral morphisms send original components onto original components

The two pure native generic-point arguments are adapted from:
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean,
SHA256 226e89b8c2e43653935be3150f8eb1cab569f5caadfbeff4de25f1ea476adfb5;
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Resolution/Algebraic/Kol07/Thm36/ReducedComponents.lean,
SHA256 e0a1c9c89a0b25514f734ba30f5dc0e4f293616610aeb40e510850ef677c8b11.
No whole-source reduction or Noetherian hypothesis is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.ProjectiveSecant

universe u

/-- The actual original component generic point has no proper original generalization. -/
theorem eq_of_specializes_component_generic {X : Scheme.{u}} {D : Set X}
    (hD : D ∈ irreducibleComponents X) {η ξ : X} (hη : IsGenericPoint η D) (hξ : ξ ⤳ η) :
    ξ = η := by
  have hsub : D ⊆ closure {ξ} := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξ))
      isClosed_closure
  have hgen : IsGenericPoint ξ D := hD.eq_of_ge isIrreducible_singleton.closure hsub
  exact hgen.eq hη

/-- Native flat generalization lifting internally preserves the actual original component generic point. -/
theorem map_component_genericPoint_eq_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {C : Set Y} {D : Set X} (hD : D ∈ irreducibleComponents X)
    (hfD : f '' D ⊆ C) {ηC : Y} (hηC : IsGenericPoint ηC C) {ηD : X}
    (hηD : IsGenericPoint ηD D) : f ηD = ηC := by
  have hspec : ηC ⤳ f ηD := hηC.specializes (hfD ⟨ηD, hηD.mem, rfl⟩)
  obtain ⟨ξ, hξ, hfξ⟩ := Flat.generalizingMap f hspec
  rw [← hfξ, eq_of_specializes_component_generic hD hηD hξ]

/-- The exact original image is itself an actual original target component; no target-component certificate is supplied. -/
theorem image_component_mem_irreducibleComponents_of_flat_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegralHom f]
    (D : Set X) (hD : D ∈ irreducibleComponents X) :
    f '' D ∈ irreducibleComponents Y := by
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f '' D) (hD.1.image f f.continuous.continuousOn)
  let ηD := (genericPoints.ofComponent ⟨D, hD⟩).val
  let ηC := (genericPoints.ofComponent ⟨C, hC⟩).val
  have hηD : IsGenericPoint ηD D := genericPoints.isGenericPoint_ofComponent ⟨D, hD⟩
  have hηC : IsGenericPoint ηC C := genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
  have hmap := map_component_genericPoint_eq_of_flat f hD hsub hηC hηD
  have hCsub : C ⊆ f '' D := by
    rw [← hηC.def, ← hmap]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨ηD, hηD.mem, rfl⟩)
      (f.isClosedMap D (isClosed_of_mem_irreducibleComponents D hD))
  rwa [hsub.antisymm hCsub]

end DeJongAlterations.Geometry.ProjectiveSecant
