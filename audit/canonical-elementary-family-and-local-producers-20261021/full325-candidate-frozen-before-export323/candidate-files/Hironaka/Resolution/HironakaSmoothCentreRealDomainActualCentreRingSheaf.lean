/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars

/-! The true original centre quotient ring sheaf and its global associated-ring
morphism. Literal section quotients and their actual restrictions precede
sheafification; the global map retains every original numerator and factors the
existing ambient map before any whole-stalk dictionary. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualCentreRingSheaf
noncomputable section

open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualNormalLayerStalk
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The whole literal centre section quotient on a true original open. -/
abbrev actualCentreRingSection (C : Set M) (U : Opens M) : Type :=
  actualComplexSection (n := n) U ⧸ actualSectionIdeal (vanishingIdeal (n := n) C) U

/-- Actual original holomorphic restrictions descend through the whole centre ideal. -/
def actualCentreRingRestrict (C : Set M) (U V : Opens M) (hUV : U ≤ V) :
    actualCentreRingSection (n := n) C V →+* actualCentreRingSection (n := n) C U :=
  Ideal.Quotient.lift (actualSectionIdeal (vanishingIdeal (n := n) C) V)
    ((Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U)).comp
      ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom)
    (fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr
      (actualSectionIdeal_restrict (vanishingIdeal (n := n) C) U V hUV s hs))

/-- Every original centre quotient numerator keeps its actual restricted section. -/
theorem actualCentreRingRestrict_mk (C : Set M) (U V : Opens M) (hUV : U ≤ V)
    (s : actualComplexSection (n := n) V) :
    actualCentreRingRestrict (n := n) C U V hUV
      (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) V) s) =
    Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U)
      ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s) := rfl

/-- The genuine original centre quotient ring presheaf uses every literal original open. -/
def actualCentreRingPresheaf (C : Set M) : (TopCat.of M).Presheaf CommRingCat where
  obj U := CommRingCat.of (actualCentreRingSection (n := n) C (unop U))
  map i := CommRingCat.ofHom (actualCentreRingRestrict (n := n) C _ _ (leOfHom i.unop))
  map_id := by
    intro U
    ext a
    rfl
  map_comp := by
    intro U V W i j
    ext a
    rfl

/-- The actual original centre quotient ring sheaf is constructed before its action. -/
def actualCentreRingSheaf (C : Set M) : (TopCat.of M).Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of M)) CommRingCat).obj
    (actualCentreRingPresheaf (n := n) C)

/-- The actual centre ring presheaf has its genuine sheafification unit. -/
def actualCentreRingSheafUnit (C : Set M) :
    actualCentreRingPresheaf (n := n) C ⟶ (actualCentreRingSheaf (n := n) C).presheaf :=
  toSheafify (Opens.grothendieckTopology (TopCat.of M)) (actualCentreRingPresheaf (n := n) C)

/-- The original structure-ring presheaf has its actual numerator quotient map. -/
def actualCentreAmbientRingMap (C : Set M) :
    (actualComplexStructureSheaf (n := n) M).presheaf ⟶ actualCentreRingPresheaf (n := n) C where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) (unop U)))
  naturality U V i := by
    ext r
    rfl

/-- The true original ambient ring sheaf maps globally to the true centre quotient ring sheaf. -/
def actualCentreAmbientRingSheafMap (C : Set M) :
    actualComplexStructureSheaf (n := n) M ⟶ actualCentreRingSheaf (n := n) C :=
  ⟨actualCentreAmbientRingMap (n := n) C ≫ actualCentreRingSheafUnit (n := n) C⟩

/-- All original ambient sections retain their actual centre quotient numerator. -/
theorem actualCentreAmbientRingSheafMap_app (C : Set M) (U : Opens M)
    (s : actualComplexSection (n := n) U) :
    (actualCentreAmbientRingSheafMap (n := n) C).hom.app (op U) s =
      (actualCentreRingSheafUnit (n := n) C).app (op U)
        (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s) := rfl

/-- The actual degree-zero section map kills the whole actual centre section ideal. -/
theorem actualNormalAssociatedSection_algebraMap_centre_zero (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (s : actualComplexSection (n := n) U)
    (hs : s ∈ actualSectionIdeal (vanishingIdeal (n := n) C) U) :
    algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) s = 0 := by
  rw [idealPowerAssociated_algebraMap]
  simp only [Algebra.algebraMap_self_apply]
  have hz : idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
      (actualSectionIdeal (vanishingIdeal (n := n) C) U) 0 ⟨s, by simp⟩ = 0 := by
    apply Subtype.ext
    change Ideal.Quotient.mk (actualSectionIdeal A U ⊔
      actualSectionIdeal (vanishingIdeal (n := n) C) U ^ (0+1)) s = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [zero_add, pow_one] using
      (show s ∈ actualSectionIdeal A U ⊔ actualSectionIdeal (vanishingIdeal (n := n) C) U from
        (show actualSectionIdeal (vanishingIdeal (n := n) C) U ≤
          actualSectionIdeal A U ⊔ actualSectionIdeal (vanishingIdeal (n := n) C) U from le_sup_right) hs)
  rw [hz, map_zero]

/-- A genuine quotient ring map acts on the original associated section ring. -/
def actualCentreRingAssociatedSectionHom (A : GermIdeal n M) (C : Set M) (U : Opens M) :
    actualCentreRingSection (n := n) C U →+* actualNormalAssociatedRingSection A C U :=
  Ideal.Quotient.lift (actualSectionIdeal (vanishingIdeal (n := n) C) U)
    (algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U))
    (fun s hs => actualNormalAssociatedSection_algebraMap_centre_zero A C U s hs)

/-- Every actual centre section numerator acts by the same original ambient algebra image. -/
theorem actualCentreRingAssociatedSectionHom_mk (A : GermIdeal n M) (C : Set M) (U : Opens M)
    (s : actualComplexSection (n := n) U) :
    actualCentreRingAssociatedSectionHom A C U
      (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s) =
    algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) s := rfl

/-- The true centre section ring action is natural for actual original holomorphic restrictions. -/
def actualCentreRingAssociatedPresheafMap (A : GermIdeal n M) (C : Set M) :
    actualCentreRingPresheaf (n := n) C ⟶ actualNormalAssociatedRingPresheaf A C where
  app U := CommRingCat.ofHom (actualCentreRingAssociatedSectionHom A C (unop U))
  naturality U V i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact (actualNormalAssociatedRingRestrict_algebraMap A C (unop V) (unop U)
      (leOfHom i.unop) r).symm

/-- The original centre quotient ring SHEAF acts through a genuine global ring-sheaf morphism. -/
def actualCentreRingAssociatedSheafMap (A : GermIdeal n M) (C : Set M) :
    actualCentreRingSheaf (n := n) C ⟶ actualNormalAssociatedRingSheaf A C :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of M))
    (actualCentreRingAssociatedPresheafMap A C ≫ actualNormalAssociatedRingSheafUnit A C)
    (actualNormalAssociatedRingSheaf A C).property⟩

/-- The genuine global centre morphism retains every original section quotient before sheafification. -/
theorem actualCentreRingAssociatedSheafMap_unit (A : GermIdeal n M) (C : Set M) :
    actualCentreRingSheafUnit (n := n) C ≫ (actualCentreRingAssociatedSheafMap A C).hom =
      actualCentreRingAssociatedPresheafMap A C ≫ actualNormalAssociatedRingSheafUnit A C :=
  toSheafify_sheafifyLift _ _ _

/-- Every original numerator keeps its old original degree-zero associated-ring section class. -/
theorem actualCentreRingAssociatedSheafMap_unit_mk (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (s : actualComplexSection (n := n) U) :
    (actualCentreRingAssociatedSheafMap A C).hom.app (op U)
      ((actualCentreRingSheafUnit (n := n) C).app (op U)
        (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s)) =
    (actualNormalAssociatedRingSheafUnit A C).app (op U)
      (algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) s) := by
  have he := congrArg (fun f => f.app (op U)) (actualCentreRingAssociatedSheafMap_unit A C)
  exact ConcreteCategory.congr_hom he
    (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s)

/-- The SAME existing ambient ring SHEAF morphism factors through the actual global centre quotient. -/
theorem actualCentreRingAssociatedSheafMap_factorization (A : GermIdeal n M) (C : Set M) :
    actualCentreAmbientRingSheafMap (n := n) C ≫ actualCentreRingAssociatedSheafMap A C =
      actualNormalAssociatedAmbientRingSheafMap A C := by
  apply Sheaf.hom_ext
  ext U s
  exact actualCentreRingAssociatedSheafMap_unit_mk A C (unop U) s

/-- Genuine stalk functoriality supplies the true global centre quotient stalk map. -/
def actualCentreAmbientRingSheafStalkHom (C : Set M) (y : M) :
    actualComplexStructureStalk (n := n) y →+*
      ((actualCentreRingSheaf (n := n) C).presheaf.stalk y).carrier :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (actualCentreAmbientRingSheafMap (n := n) C).hom).hom

/-- Genuine stalk functoriality supplies the true global centre action on the associated ring stalk. -/
def actualCentreRingAssociatedSheafStalkHom (A : GermIdeal n M) (C : Set M) (y : M) :
    ((actualCentreRingSheaf (n := n) C).presheaf.stalk y).carrier →+*
      actualNormalAssociatedRingSheafStalk A C y :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (actualCentreRingAssociatedSheafMap A C).hom).hom

/-- The actual global centre action preserves the SAME original ambient stalk homomorphism. -/
theorem actualCentreRingAssociatedSheafStalkHom_factorization (A : GermIdeal n M) (C : Set M)
    (y : M) (r : actualComplexStructureStalk (n := n) y) :
    actualCentreRingAssociatedSheafStalkHom A C y (actualCentreAmbientRingSheafStalkHom (n := n) C y r) =
      actualNormalAssociatedRingSheafStalkAmbientHom A C y r := by
  have he := congrArg (fun f => (TopCat.Presheaf.stalkFunctor
    (X := TopCat.of M) CommRingCat y).map f.hom)
    (actualCentreRingAssociatedSheafMap_factorization A C)
  change (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
      ((actualCentreAmbientRingSheafMap (n := n) C).hom ≫
        (actualCentreRingAssociatedSheafMap A C).hom) = _ at he
  rw [Functor.map_comp] at he
  exact ConcreteCategory.congr_hom he r

end
end Hironaka.HironakaSmoothCentreRealDomainActualCentreRingSheaf
