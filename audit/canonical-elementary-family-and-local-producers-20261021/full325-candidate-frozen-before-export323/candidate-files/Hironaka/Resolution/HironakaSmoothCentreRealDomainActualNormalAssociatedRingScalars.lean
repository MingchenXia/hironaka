/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf

/-! Independent actual ambient/centre scalars on the original ring sheaf.
Actual ring-sheaf stalk functoriality defines the action before comparison.
Centre annihilation is proved before quotient descent; one original open then
supplies free and flat whole ring stalks through the existing module producer. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars
noncomputable section

open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra
  HironakaRelativeNormalCentreScalars
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original ambient ring-sheaf morphism gives its genuine stalk ring map. -/
def actualNormalAssociatedRingSheafStalkAmbientHom (A : GermIdeal n M) (C : Set M) (y : M) :
    actualComplexStructureStalk (n := n) y →+* actualNormalAssociatedRingSheafStalk A C y :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (actualNormalAssociatedAmbientRingSheafMap A C).hom).hom

/-- Actual multiplication with the genuine ambient stalk image, before every scalar dictionary. -/
instance actualNormalAssociatedRingSheafStalkAlgebra (A : GermIdeal n M) (C : Set M) (y : M) :
    Algebra (actualComplexStructureStalk (n := n) y) (actualNormalAssociatedRingSheafStalk A C y) :=
  (actualNormalAssociatedRingSheafStalkAmbientHom A C y).toAlgebra

/-- The whole original ring retains its intrinsic degree-zero representative algebra. -/
instance actualWholeNormalAssociatedRingAlgebra (A : GermIdeal n M) (C : Set M) (y : M) :
    Algebra (actualComplexStructureStalk (n := n) y) (actualWholeNormalAssociatedRing A C y) :=
  idealPowerAssociatedAlgebra (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)

/-- Every original ambient section keeps the same whole degree-zero germ under the existing ring map. -/
theorem actualNormalAssociatedRingSectionGermHom_algebraMap (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U) :
    actualNormalAssociatedRingSectionGermHom A C U y hy
      (algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) s) =
    algebraMap (actualComplexStructureStalk (n := n) y) (actualWholeNormalAssociatedRing A C y)
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) := by
  rw [idealPowerAssociated_algebraMap, actualNormalAssociatedRingSectionGermHom_of,
    idealPowerAssociated_algebraMap]
  apply congrArg (DirectSum.of (fun q => actualWholeNormalLayer A C q y) 0)
  apply Subtype.ext
  exact actualRemainderQuotientSectionGermHom_mk A C 1 U y hy s

/-- The SAME whole ring dictionary preserves every genuine original ambient stalk scalar. -/
theorem actualNormalAssociatedRingSheafStalkWholeEquiv_algebraMap (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y) :
    actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y
      (algebraMap (actualComplexStructureStalk (n := n) y) (actualNormalAssociatedRingSheafStalk A C y) r) =
    algebraMap (actualComplexStructureStalk (n := n) y) (actualWholeNormalAssociatedRing A C y) r := by
  obtain ⟨U, hy, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  change actualComplexSection (n := n) U at s
  change actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y
      (actualNormalAssociatedRingSheafStalkAmbientHom A C y
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s)) = _
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    (actualNormalAssociatedAmbientRingSheafMap A C).hom s
  change actualNormalAssociatedRingSheafStalkAmbientHom A C y
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) = _ at he
  rw [he, actualNormalAssociatedAmbientRingSheafMap_app,
    actualNormalAssociatedRingSheafStalkWholeEquiv_germ,
    actualNormalAssociatedRingSectionGermHom_algebraMap]

/-- The preexisting ring equivalence is an algebra equivalence for both independent original actions. -/
def actualNormalAssociatedRingSheafStalkWholeAlgEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    actualNormalAssociatedRingSheafStalk A C y ≃ₐ[actualComplexStructureStalk (n := n) y]
      actualWholeNormalAssociatedRing A C y :=
  { actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y with
    commutes' := actualNormalAssociatedRingSheafStalkWholeEquiv_algebraMap A hA C y }

/-- The actual centre ideal annihilates the genuine ambient ring-sheaf stalk action before descent. -/
theorem actualNormalAssociatedRingSheafStalk_isTorsionByCentre (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    Module.IsTorsionBySet (actualComplexStructureStalk (n := n) y)
      (actualNormalAssociatedRingSheafStalk A C y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) := by
  intro v r
  let E := (actualNormalAssociatedRingSheafStalkWholeAlgEquiv A hA C y).toLinearEquiv
  apply E.injective
  rw [E.map_smul, E.map_zero]
  exact idealPowerAssociated_isTorsionBySet (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    (x := E v) (a := r)

/-- The actual centre action descends canonically only after its annihilation proof. -/
@[instance_reducible] def actualNormalAssociatedRingSheafStalkCentreModule (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    Module (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (actualNormalAssociatedRingSheafStalk A C y) :=
  (actualNormalAssociatedRingSheafStalk_isTorsionByCentre A hA C y).module

/-- Both canonical centre actions retain every original ambient scalar product. -/
theorem actualNormalAssociatedRingSheafStalkCentre_mk_smul (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y)
    (v : actualNormalAssociatedRingSheafStalk A C y) :
    letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
    Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r • v = r • v := rfl

/-- Actual centre annihilation at the genuine ring unit proves the ambient ring map kills the whole centre ideal. -/
theorem actualNormalAssociatedRingSheafStalkAmbientHom_centre_zero (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y)
    (hr : r ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) :
    actualNormalAssociatedRingSheafStalkAmbientHom A C y r = 0 := by
  have he := actualNormalAssociatedRingSheafStalk_isTorsionByCentre A hA C y
    (x := (1 : actualNormalAssociatedRingSheafStalk A C y)) (a := ⟨r, hr⟩)
  change actualNormalAssociatedRingSheafStalkAmbientHom A C y r * 1 = 0 at he
  simpa only [mul_one] using he

/-- Genuine quotient-ring descent constructs the whole actual centre ring homomorphism. -/
def actualNormalAssociatedRingSheafStalkCentreHom (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) →+*
      actualNormalAssociatedRingSheafStalk A C y :=
  Ideal.Quotient.lift (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    (actualNormalAssociatedRingSheafStalkAmbientHom A C y)
    (fun r hr => actualNormalAssociatedRingSheafStalkAmbientHom_centre_zero A hA C y r hr)

/-- The true centre ring map retains every original ambient numerator. -/
theorem actualNormalAssociatedRingSheafStalkCentreHom_mk (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y) :
    actualNormalAssociatedRingSheafStalkCentreHom A hA C y
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r) =
      actualNormalAssociatedRingSheafStalkAmbientHom A C y r := rfl

/-- The independently constructed actual centre ring map induces its genuine algebra. -/
@[instance_reducible] def actualNormalAssociatedRingSheafStalkCentreAlgebra (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    Algebra (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (actualNormalAssociatedRingSheafStalk A C y) :=
  (actualNormalAssociatedRingSheafStalkCentreHom A hA C y).toAlgebra

/-- Every genuine quotient-ring algebra scalar uses the SAME original ambient product. -/
theorem actualNormalAssociatedRingSheafStalkCentreAlgebra_mk_smul (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y)
    (v : actualNormalAssociatedRingSheafStalk A C y) :
    letI := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
    Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r • v = r • v := by
  let := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
  change actualNormalAssociatedRingSheafStalkCentreHom A hA C y
    (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r) * v =
    actualNormalAssociatedRingSheafStalkAmbientHom A C y r * v
  rw [actualNormalAssociatedRingSheafStalkCentreHom_mk]

/-- The SAME whole original ring dictionary is centre linear for independently descended actions. -/
def actualNormalAssociatedRingSheafStalkWholeCentreLinearEquiv (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
    letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    actualNormalAssociatedRingSheafStalk A C y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualWholeNormalAssociatedRing A C y := by
  letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
  letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
  let E := (actualNormalAssociatedRingSheafStalkWholeAlgEquiv A hA C y).toLinearEquiv
  refine { E.toAddEquiv with map_smul' := ?_ }
  intro r v
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact E.map_smul s v

/-- The actual ring-sheaf and prior actual associated module-sheaf stalks agree with their own centre actions. -/
def actualNormalAssociatedRingModuleSheafStalkCentreLinearEquiv (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
    letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
    actualNormalAssociatedRingSheafStalk A C y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualNormalAssociatedSheafStalk A C y := by
  letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
  letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
  letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
  exact (actualNormalAssociatedRingSheafStalkWholeCentreLinearEquiv A hA C y).trans
    (actualNormalAssociatedSheafStalkWholeCentreLinearEquiv A hA C y).symm

/-- The genuine quotient-ring algebra action keeps the SAME whole original centre-linear dictionary. -/
def actualNormalAssociatedRingSheafCentreAlgebraWholeLinearEquiv (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M) :
    letI := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
    letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    actualNormalAssociatedRingSheafStalk A C y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualWholeNormalAssociatedRing A C y := by
  letI := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
  letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
  let E := (actualNormalAssociatedRingSheafStalkWholeAlgEquiv A hA C y).toLinearEquiv
  refine { E.toAddEquiv with map_smul' := ?_ }
  intro r v
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [actualNormalAssociatedRingSheafStalkCentreAlgebra_mk_smul]
  exact E.map_smul s v

/-- Original inputs supply one accumulating original centre open with genuine whole ring-sheaf stalks free and flat. -/
theorem exists_original_regular_actual_associated_ring_sheaf_free_open
    {d t : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O),
        letI := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
        Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) ∧
        Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) := by
  obtain ⟨O, hO, hcl, hfree⟩ :=
    exists_original_regular_all_actual_associated_sheaf_degrees_free_open C x hreg A hA hAC
  refine ⟨O, hO, hcl, ?_⟩
  intro y hyCO
  let := actualNormalAssociatedRingSheafStalkCentreModule A hA C y
  let := actualNormalAssociatedSheafStalkCentreModule A hA C y
  let := (hfree y hyCO).1.1
  let E := actualNormalAssociatedRingModuleSheafStalkCentreLinearEquiv A hA C y
  have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) :=
    Module.Free.of_equiv E.symm
  let := hf
  exact ⟨hf, inferInstance⟩

/-- The SAME original accumulating centre open is free and flat for the genuine quotient-ring algebra action. -/
theorem exists_original_regular_actual_associated_ring_sheaf_algebra_free_open
    {d t : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O),
        letI := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
        Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) ∧
        Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) := by
  obtain ⟨O, hO, hcl, hfree⟩ :=
    exists_original_regular_all_actual_associated_sheaf_degrees_free_open C x hreg A hA hAC
  refine ⟨O, hO, hcl, ?_⟩
  intro y hyCO
  let := actualNormalAssociatedRingSheafStalkCentreAlgebra A hA C y
  let := actualNormalAssociatedSheafStalkCentreModule A hA C y
  let := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := d+t) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y)
  let := (hfree y hyCO).1.1
  let E := (actualNormalAssociatedRingSheafCentreAlgebraWholeLinearEquiv A hA C y).trans
    (actualNormalAssociatedSheafStalkWholeCentreLinearEquiv A hA C y).symm
  have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedRingSheafStalk A C y) :=
    Module.Free.of_equiv E.symm
  let := hf
  exact ⟨hf, inferInstance⟩

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars
