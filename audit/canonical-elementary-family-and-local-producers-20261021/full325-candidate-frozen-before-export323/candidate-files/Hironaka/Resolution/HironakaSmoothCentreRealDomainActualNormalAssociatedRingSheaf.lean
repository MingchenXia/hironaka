/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk

/-! Genuine ring sheafification of the original associated-ring presheaf.
The ring sheaf and original ambient morphism precede the whole stalk dictionary.
The sheafification unit is internally an actual ring-stalk isomorphism. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingStalk

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual ring-valued sheafification gives genuine section ring operations. -/
def actualNormalAssociatedRingSheaf (A : GermIdeal n M) (C : Set M) :
    (TopCat.of M).Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of M)) CommRingCat).obj
    (actualNormalAssociatedRingPresheaf A C)

/-- The actual ring presheaf unit, before every whole ring-stalk comparison. -/
def actualNormalAssociatedRingSheafUnit (A : GermIdeal n M) (C : Set M) :
    actualNormalAssociatedRingPresheaf A C ⟶ (actualNormalAssociatedRingSheaf A C).presheaf :=
  toSheafify (Opens.grothendieckTopology (TopCat.of M)) (actualNormalAssociatedRingPresheaf A C)

/-- The true original structure-ring sheaf acts through its original degree-zero unit image. -/
def actualNormalAssociatedAmbientRingSheafMap (A : GermIdeal n M) (C : Set M) :
    actualComplexStructureSheaf (n := n) M ⟶ actualNormalAssociatedRingSheaf A C :=
  ⟨actualNormalAssociatedAmbientRingMap A C ≫ actualNormalAssociatedRingSheafUnit A C⟩

/-- Every genuine ambient section acts by the unit of its original degree-zero class. -/
theorem actualNormalAssociatedAmbientRingSheafMap_app (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (s : actualComplexSection (n := n) U) :
    (actualNormalAssociatedAmbientRingSheafMap A C).hom.app (op U) s =
      (actualNormalAssociatedRingSheafUnit A C).app (op U)
        (algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) s) := rfl

/-- The independently constructed actual ring sheaf has its true neighbourhood-colimit stalk. -/
abbrev actualNormalAssociatedRingSheafStalk (A : GermIdeal n M) (C : Set M) (y : M) : Type :=
  ((actualNormalAssociatedRingSheaf A C).presheaf.stalk y).carrier

/-- Every genuine sheafification unit induces a true ring-stalk isomorphism internally. -/
def actualNormalAssociatedRingUnitStalkIso (A : GermIdeal n M) (C : Set M) (y : M) :
    (actualNormalAssociatedRingPresheaf A C).stalk y ≅
      (actualNormalAssociatedRingSheaf A C).presheaf.stalk y := by
  let f := (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (actualNormalAssociatedRingSheafUnit A C)
  have hf : IsIso f :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      (X := TopCat.of M) y CommRingCat (actualNormalAssociatedRingPresheaf A C)
  exact @asIso _ _ _ _ f hf

/-- Only original coherence identifies the SAME genuine ring sheaf stalk with the whole original ring. -/
def actualNormalAssociatedRingSheafStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    actualNormalAssociatedRingSheafStalk A C y ≃+* actualWholeNormalAssociatedRing A C y :=
  (actualNormalAssociatedRingUnitStalkIso A C y).symm.commRingCatIsoToRingEquiv.trans
    (actualNormalAssociatedRingStalkWholeEquiv A hA C y)

/-- The genuine whole unit stalk image keeps the original whole ring-colimit class. -/
theorem actualNormalAssociatedRingSheafStalkWholeEquiv_unit (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (y : M)
    (v : ((actualNormalAssociatedRingPresheaf A C).stalk y).carrier) :
    actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y
      ((actualNormalAssociatedRingUnitStalkIso A C y).hom v) =
      actualNormalAssociatedRingStalkWholeEquiv A hA C y v := by
  let E := (actualNormalAssociatedRingUnitStalkIso A C y).commRingCatIsoToRingEquiv
  change actualNormalAssociatedRingStalkWholeEquiv A hA C y (E.symm (E v)) = _
  rw [RingEquiv.symm_apply_apply]

/-- Every actual whole original section germ keeps its original ring class in the true ring sheaf. -/
theorem actualNormalAssociatedRingSheafStalkWholeEquiv_germ (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualNormalAssociatedRingSection A C U) :
    actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y
      ((actualNormalAssociatedRingSheaf A C).presheaf.germ U y hy
        ((actualNormalAssociatedRingSheafUnit A C).app (op U) s)) =
      actualNormalAssociatedRingSectionGermHom A C U y hy s := by
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    (actualNormalAssociatedRingSheafUnit A C) s
  change (actualNormalAssociatedRingUnitStalkIso A C y).hom
    ((actualNormalAssociatedRingPresheaf A C).germ U y hy s) = _ at he
  rw [← he, actualNormalAssociatedRingSheafStalkWholeEquiv_unit,
    actualNormalAssociatedRingStalkWholeEquiv_germ]

/-- Every actual homogeneous original layer keeps its degree and literal original germ class. -/
theorem actualNormalAssociatedRingSheafStalkWholeEquiv_germ_of (A : GermIdeal n M)
    (hA : A.IsCoherent) (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (q : ℕ) (s : actualNormalLayerSection A C q U) :
    actualNormalAssociatedRingSheafStalkWholeEquiv A hA C y
      ((actualNormalAssociatedRingSheaf A C).presheaf.germ U y hy
        ((actualNormalAssociatedRingSheafUnit A C).app (op U)
          (DirectSum.of (fun k => actualNormalLayerSection A C k U) q s))) =
      DirectSum.of (fun k => actualWholeNormalLayer A C k y) q
        (actualNormalLayerSectionGermHom A C q U y hy s) := by
  rw [actualNormalAssociatedRingSheafStalkWholeEquiv_germ,
    actualNormalAssociatedRingSectionGermHom_of]

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
