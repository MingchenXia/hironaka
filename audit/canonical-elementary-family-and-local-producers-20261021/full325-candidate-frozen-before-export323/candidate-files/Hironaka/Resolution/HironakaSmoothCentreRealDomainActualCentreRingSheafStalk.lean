/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentreRingSheaf

/-! Whole original centre quotient ring-sheaf stalks and their actual action.
The actual original quotient germ cocone precedes the dictionary. Genuine
smaller-open numerator equalities construct injectivity; no coherent centre
certificate is supplied. The genuine sheaf action keeps the old quotient map. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualCentreRingSheafStalk
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingScalars
  HironakaSmoothCentreRealDomainActualCentreRingSheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual quotient sections retain their whole original centre quotient germ. -/
def actualCentreRingSectionGermHom (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U) :
    actualCentreRingSection (n := n) C U →+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  Ideal.Quotient.lift (actualSectionIdeal (vanishingIdeal (n := n) C) U)
    ((Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)).comp
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom)
    (fun _s hs => Ideal.Quotient.eq_zero_iff_mem.mpr (hs y hy))

/-- Every true original quotient numerator keeps its exact original germ class. -/
theorem actualCentreRingSectionGermHom_mk (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualComplexSection (n := n) U) :
    actualCentreRingSectionGermHom (n := n) C U y hy
      (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) := rfl

/-- The original quotient germ maps form the genuine ring-valued neighbourhood cocone. -/
def actualCentreRingGermCocone (C : Set M) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualCentreRingPresheaf (n := n) C) where
  pt := CommRingCat.of (actualComplexStructureStalk (n := n) y ⧸
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
  ι := {
    app := fun U => CommRingCat.ofHom
      (actualCentreRingSectionGermHom (n := n) C (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext a
      obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective a
      change Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop V).val y (unop V).property
            ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE (leOfHom i.unop)).op s)) =
        Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop U).val y (unop U).property s)
      exact congrArg (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y))
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
          (homOfLE (leOfHom i.unop)) y (unop V).property s) }

/-- The genuine ring colimit supplies the actual whole original centre quotient stalk map. -/
def actualCentreRingStalkToWholeHom (C : Set M) (y : M) :
    ((actualCentreRingPresheaf (n := n) C).stalk y).carrier →+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  (colimit.desc _ (actualCentreRingGermCocone (n := n) C y)).hom

/-- Every actual quotient-presheaf germ retains its original quotient germ formula. -/
theorem actualCentreRingStalkToWholeHom_germ (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualCentreRingSection (n := n) C U) :
    actualCentreRingStalkToWholeHom (n := n) C y ((actualCentreRingPresheaf (n := n) C).germ U y hy s) =
      actualCentreRingSectionGermHom (n := n) C U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualCentreRingPresheaf (n := n) C
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualCentreRingGermCocone (n := n) C y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- Every whole original quotient germ has a true original quotient-section representative. -/
theorem actualCentreRingStalkToWholeHom_surjective (C : Set M) (y : M) :
    Function.Surjective (actualCentreRingStalkToWholeHom (n := n) C y) := by
  intro g
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨U,hyU,s,heq⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨(actualCentreRingPresheaf (n := n) C).germ U y hyU
    (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) U) s),?_⟩
  rw [actualCentreRingStalkToWholeHom_germ,actualCentreRingSectionGermHom_mk,heq]

/-- Actual centre membership and true smaller-open equality prove whole quotient-stalk injectivity. -/
theorem actualCentreRingStalkToWholeHom_injective (C : Set M) (y : M) :
    Function.Injective (actualCentreRingStalkToWholeHom (n := n) C y) := by
  intro a b hab
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let Q := actualCentreRingPresheaf (n := n) C
  obtain ⟨U,hyU,s,rfl⟩ := Q.exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := Q.exists_germ_eq b
  change actualCentreRingSection (n := n) C U at s
  change actualCentreRingSection (n := n) C V at t
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [actualCentreRingStalkToWholeHom_germ,actualCentreRingStalkToWholeHom_germ,
    actualCentreRingSectionGermHom_mk,actualCentreRingSectionGermHom_mk] at hab
  let W : Opens M := U ⊓ V
  have hyW : y ∈ W := ⟨hyU,hyV⟩
  let fu := F.map (homOfLE (show W ≤ U from inf_le_left)).op f
  let gv := F.map (homOfLE (show W ≤ V from inf_le_right)).op g
  have hfu : F.germ W y hyW fu = F.germ U y hyU f :=
    F.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) y hyW f
  have hgv : F.germ W y hyW gv = F.germ V y hyV g :=
    F.germ_res_apply (homOfLE (show W ≤ V from inf_le_right)) y hyW g
  have hj : F.germ W y hyW (fu-gv) ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y := by
    change (F.germ W y hyW).hom (fu-gv) ∈ _
    rw [map_sub,hfu,hgv]
    exact Ideal.Quotient.eq.mp hab
  have him : F.germ W y hyW (fu-gv) ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) y := by
    rw [actualCentreIdealSectionGermImage_eq_whole C y]
    exact hj
  obtain ⟨R,hyR,k,hk⟩ := him
  obtain ⟨Z,hyZ,iW,iR,heq⟩ := F.germ_eq y hyW hyR (fu-gv) k.val hk.symm
  have hdiff : F.map iW.op (fu-gv) ∈ actualSectionIdeal (vanishingIdeal (n := n) C) Z := by
    rw [heq]
    exact actualSectionIdeal_restrict (vanishingIdeal (n := n) C) Z R (leOfHom iR) k.val k.property
  have heqQ : Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) Z) (F.map iW.op fu) =
      Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) Z) (F.map iW.op gv) := by
    apply Ideal.Quotient.eq.mpr
    change (F.map iW.op).hom fu - (F.map iW.op).hom gv ∈ _
    rw [← map_sub]
    exact hdiff
  apply Q.germ_ext Z hyZ (iW ≫ homOfLE (show W ≤ U from inf_le_left))
    (iW ≫ homOfLE (show W ≤ V from inf_le_right))
  change Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) Z) (F.map iW.op fu) =
    Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C) Z) (F.map iW.op gv)
  exact heqQ

/-- The independently constructed actual centre quotient-presheaf stalk map is a whole ring equivalence. -/
def actualCentreRingStalkWholeEquiv (C : Set M) (y : M) :
    ((actualCentreRingPresheaf (n := n) C).stalk y).carrier ≃+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  RingEquiv.ofBijective (actualCentreRingStalkToWholeHom (n := n) C y)
    ⟨actualCentreRingStalkToWholeHom_injective (n := n) C y,
      actualCentreRingStalkToWholeHom_surjective (n := n) C y⟩

/-- The genuine centre ring-sheafification unit is internally an actual ring-stalk isomorphism. -/
def actualCentreRingUnitStalkIso (C : Set M) (y : M) :
    (actualCentreRingPresheaf (n := n) C).stalk y ≅ (actualCentreRingSheaf (n := n) C).presheaf.stalk y := by
  let f := (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
    (actualCentreRingSheafUnit (n := n) C)
  have hf : IsIso f := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := TopCat.of M) y CommRingCat (actualCentreRingPresheaf (n := n) C)
  exact @asIso _ _ _ _ f hf

/-- The SAME actual centre ring sheaf has its whole original quotient ring stalk. -/
def actualCentreRingSheafStalkWholeEquiv (C : Set M) (y : M) :
    ((actualCentreRingSheaf (n := n) C).presheaf.stalk y).carrier ≃+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  (actualCentreRingUnitStalkIso (n := n) C y).symm.commRingCatIsoToRingEquiv.trans
    (actualCentreRingStalkWholeEquiv (n := n) C y)

/-- Every original centre quotient germ keeps its whole class under the actual sheafification unit. -/
theorem actualCentreRingSheafStalkWholeEquiv_unit (C : Set M) (y : M)
    (r : ((actualCentreRingPresheaf (n := n) C).stalk y).carrier) :
    actualCentreRingSheafStalkWholeEquiv (n := n) C y
      (((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
        (actualCentreRingSheafUnit (n := n) C)) r) = actualCentreRingStalkToWholeHom (n := n) C y r := by
  change actualCentreRingStalkToWholeHom (n := n) C y
    ((actualCentreRingUnitStalkIso (n := n) C y).inv ((actualCentreRingUnitStalkIso (n := n) C y).hom r)) = _
  rw [CategoryTheory.Iso.hom_inv_id_apply]

/-- Actual sheaf germs of every original quotient section keep their original whole quotient germ. -/
theorem actualCentreRingSheafStalkWholeEquiv_germ (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualCentreRingSection (n := n) C U) :
    actualCentreRingSheafStalkWholeEquiv (n := n) C y
      ((actualCentreRingSheaf (n := n) C).presheaf.germ U y hy
        ((actualCentreRingSheafUnit (n := n) C).app (op U) s)) =
      actualCentreRingSectionGermHom (n := n) C U y hy s := by
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    (actualCentreRingSheafUnit (n := n) C) s
  calc
    _ = actualCentreRingSheafStalkWholeEquiv (n := n) C y
        (((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) CommRingCat y).map
          (actualCentreRingSheafUnit (n := n) C))
          ((actualCentreRingPresheaf (n := n) C).germ U y hy s)) := congrArg _ he.symm
    _ = _ := (actualCentreRingSheafStalkWholeEquiv_unit (n := n) C y _).trans
      (actualCentreRingStalkToWholeHom_germ (n := n) C U y hy s)

/-- The genuine centre quotient sheaf morphism induces the SAME whole original quotient stalk map. -/
theorem actualCentreRingSheafStalkWholeEquiv_ambientHom (C : Set M) (y : M)
    (r : actualComplexStructureStalk (n := n) y) :
    actualCentreRingSheafStalkWholeEquiv (n := n) C y (actualCentreAmbientRingSheafStalkHom (n := n) C y r) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r := by
  obtain ⟨U,hy,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    (actualCentreAmbientRingSheafMap (n := n) C).hom s
  change actualCentreAmbientRingSheafStalkHom (n := n) C y
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) = _ at he
  rw [he,actualCentreAmbientRingSheafMap_app,actualCentreRingSheafStalkWholeEquiv_germ,
    actualCentreRingSectionGermHom_mk]

/-- The independently constructed genuine global ring-sheaf action is exactly the whole original quotient action. -/
theorem actualCentreRingAssociatedSheafStalkHom_whole (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M)
    (q : actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) :
    actualCentreRingAssociatedSheafStalkHom A C y ((actualCentreRingSheafStalkWholeEquiv (n := n) C y).symm q) =
      actualNormalAssociatedRingSheafStalkCentreHom A hA C y q := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  have he : (actualCentreRingSheafStalkWholeEquiv (n := n) C y).symm
      (Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r) =
      actualCentreAmbientRingSheafStalkHom (n := n) C y r := by
    apply (actualCentreRingSheafStalkWholeEquiv (n := n) C y).injective
    rw [RingEquiv.apply_symm_apply,actualCentreRingSheafStalkWholeEquiv_ambientHom]
  rw [he,actualCentreRingAssociatedSheafStalkHom_factorization,actualNormalAssociatedRingSheafStalkCentreHom_mk]

end
end Hironaka.HironakaSmoothCentreRealDomainActualCentreRingSheafStalk
