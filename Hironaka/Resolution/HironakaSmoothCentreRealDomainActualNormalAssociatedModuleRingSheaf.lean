/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingPresheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! Genuine whole sheaf comparison, using the original ambient ring-sheaf
morphism and the independent module coproduct. No coherence is required. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingSheaf
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualNormalLayerSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedRingSheaf
  HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingPresheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal original ring-sheaf sections, retaining their genuine ring operations. -/
abbrev actualNormalAssociatedRingSheafSection (A : GermIdeal n M) (C : Set M)
    (U : Opens M) : Type :=
  ((actualNormalAssociatedRingSheaf A C).presheaf.obj (op U)).carrier

/-- Original ambient sections act through the already constructed actual ring-sheaf morphism. -/
instance actualNormalAssociatedRingSheafSectionAlgebra (A : GermIdeal n M) (C : Set M)
    (U : Opens M) :
    Algebra (actualComplexSection (n := n) U) (actualNormalAssociatedRingSheafSection A C U) :=
  ((actualNormalAssociatedAmbientRingSheafMap A C).hom.app (op U)).hom.toAlgebra

/-- The SAME genuine ring-sheaf sections are modules through the independent ambient ring map. -/
def actualNormalAssociatedRingSheafModulePresheaf (A : GermIdeal n M) (C : Set M) :
    ActualModulePresheaf n M := by
  let G := (actualNormalAssociatedRingSheaf A C).presheaf ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  letI (U : (Opens M)ᵒᵖ) :
      Module (((actualComplexStructureSheaf (n := n) M).presheaf ⋙
        forget₂ CommRingCat RingCat).obj U) (G.obj U) := by
    change Module (actualComplexSection (n := n) (unop U))
      (actualNormalAssociatedRingSheafSection A C (unop U))
    infer_instance
  apply PresheafOfModules.ofPresheaf G
  intro U V i r s
  change actualComplexSection (n := n) (unop U) at r
  change actualNormalAssociatedRingSheafSection A C (unop U) at s
  change ((actualNormalAssociatedRingSheaf A C).presheaf.map i).hom
      (((actualNormalAssociatedAmbientRingSheafMap A C).hom.app U).hom r * s) =
    ((actualNormalAssociatedAmbientRingSheafMap A C).hom.app V).hom
      ((actualComplexStructureSheaf (n := n) M).presheaf.map i r) *
      ((actualNormalAssociatedRingSheaf A C).presheaf.map i).hom s
  rw [map_mul]
  have h := ConcreteCategory.congr_hom
    ((actualNormalAssociatedAmbientRingSheafMap A C).hom.naturality i) r
  exact congrArg (fun t => t * ((actualNormalAssociatedRingSheaf A C).presheaf.map i).hom s) h.symm

/-- The actual ring sheaf with its genuine ambient section action, before all stalk dictionaries. -/
def actualNormalAssociatedRingAmbientModuleSheaf (A : GermIdeal n M) (C : Set M) :
    SheafOfModules (actualComplexStructureRingSheaf n M) where
  val := actualNormalAssociatedRingSheafModulePresheaf A C
  isSheaf := Presheaf.isSheaf_comp_of_isSheaf
    (Opens.grothendieckTopology (TopCat.of M))
    (actualNormalAssociatedRingSheaf A C).presheaf
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (actualNormalAssociatedRingSheaf A C).property

/-- The actual ring unit is ambient linear for the SAME independently defined action. -/
def actualNormalAssociatedRingModuleSheafUnit (A : GermIdeal n M) (C : Set M) :
    actualNormalAssociatedRingModulePresheaf A C ⟶
      (PresheafOfModules.restrictScalars (𝟙 (actualComplexStructureRingSheaf n M).obj)).obj
        (actualNormalAssociatedRingAmbientModuleSheaf A C).val :=
  PresheafOfModules.homMk
    (whiskerRight (actualNormalAssociatedRingSheafUnit A C)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
    intro U r s
    change actualComplexSection (n := n) (unop U) at r
    change actualNormalAssociatedRingSection A C (unop U) at s
    change ((actualNormalAssociatedRingSheafUnit A C).app U).hom (r • s) =
      ((actualNormalAssociatedAmbientRingSheafMap A C).hom.app U).hom r *
        ((actualNormalAssociatedRingSheafUnit A C).app U).hom s
    rw [Algebra.smul_def]
    erw [map_mul]
    rfl)

/-- The true linear ring unit extends uniquely through genuine MODULE sheafification. -/
def actualNormalAssociatedRingModuleSheafLift (A : GermIdeal n M) (C : Set M) :
    (PresheafOfModules.sheafification (R := actualComplexStructureRingSheaf n M)
      (𝟙 (actualComplexStructureRingSheaf n M).obj)).obj
        (actualNormalAssociatedRingModulePresheaf A C) ⟶
      actualNormalAssociatedRingAmbientModuleSheaf A C :=
  (PresheafOfModules.sheafificationHomEquiv
    (R := actualComplexStructureRingSheaf n M)
      (𝟙 (actualComplexStructureRingSheaf n M).obj)).symm
        (actualNormalAssociatedRingModuleSheafUnit A C)

/-- Forgetting the extension is precisely the genuine ring/additive sheafification comparison. -/
theorem actualNormalAssociatedRingModuleSheafLift_toSheaf (A : GermIdeal n M) (C : Set M) :
    (SheafOfModules.toSheaf (actualComplexStructureRingSheaf n M)).map
      (actualNormalAssociatedRingModuleSheafLift A C) =
    (sheafComposeNatTrans (Opens.grothendieckTopology (TopCat.of M))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of M)) CommRingCat)
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat)).app
        (actualNormalAssociatedRingPresheaf A C) := by
  rw [actualNormalAssociatedRingModuleSheafLift]
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  rfl

/-- Compatible ring/additive sheafification proves the true WHOLE module extension is an isomorphism. -/
instance actualNormalAssociatedRingModuleSheafLiftIsIso (A : GermIdeal n M) (C : Set M) :
    IsIso (actualNormalAssociatedRingModuleSheafLift A C) := by
  let : (Opens.grothendieckTopology (TopCat.of M)).PreservesSheafification
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) := inferInstance
  have : IsIso (sheafComposeNatTrans (Opens.grothendieckTopology (TopCat.of M))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of M)) CommRingCat)
      (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat)) :=
    inferInstance
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (actualComplexStructureRingSheaf n M)),
    actualNormalAssociatedRingModuleSheafLift_toSheaf]
  exact NatIso.isIso_app_of_isIso _ (actualNormalAssociatedRingPresheaf A C)

/-- The actual WHOLE associated module sheaf agrees with the independently defined ambient ring module sheaf. -/
def actualNormalAssociatedModuleRingSheafIso (A : GermIdeal n M) (C : Set M) :
    actualNormalAssociatedModuleSheaf A C ≅ actualNormalAssociatedRingAmbientModuleSheaf A C :=
  (PresheafOfModules.sheafification (R := actualComplexStructureRingSheaf n M)
    (𝟙 (actualComplexStructureRingSheaf n M).obj)).mapIso
      (actualNormalAssociatedModuleRingPresheafIso A C) ≪≫
    asIso (actualNormalAssociatedRingModuleSheafLift A C)

set_option backward.isDefEq.respectTransparency false in
/-- The true whole linear extension retains the SAME original ring unit on all sections. -/
theorem actualNormalAssociatedRingModuleSheafLift_unit (A : GermIdeal n M) (C : Set M) :
    toSheafify (Opens.grothendieckTopology (TopCat.of M))
        (actualNormalAssociatedRingModulePresheaf A C).presheaf ≫
      (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (actualNormalAssociatedRingModuleSheafLift A C).val =
      whiskerRight (actualNormalAssociatedRingSheafUnit A C)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (R := actualComplexStructureRingSheaf n M)
    (P := actualNormalAssociatedRingModulePresheaf A C)
    (F := actualNormalAssociatedRingAmbientModuleSheaf A C)
      (𝟙 (actualComplexStructureRingSheaf n M).obj)).apply_symm_apply
        (actualNormalAssociatedRingModuleSheafUnit A C)
  have h' := congrArg
    (fun f => (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map f) h
  exact h'

set_option backward.isDefEq.respectTransparency false in
/-- The actual WHOLE module sheaf comparison extends the same original whole presheaf map. -/
theorem actualNormalAssociatedModuleRingSheafIso_unit (A : GermIdeal n M) (C : Set M) :
    toSheafify (Opens.grothendieckTopology (TopCat.of M))
        (actualNormalAssociatedModulePresheaf A C).presheaf ≫
      (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (actualNormalAssociatedModuleRingSheafIso A C).hom.val =
      (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (actualNormalAssociatedModuleRingPresheafIso A C).hom ≫
      whiskerRight (actualNormalAssociatedRingSheafUnit A C)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) := by
  change toSheafify (Opens.grothendieckTopology (TopCat.of M))
      (actualNormalAssociatedModulePresheaf A C).presheaf ≫
      (sheafifyMap (Opens.grothendieckTopology (TopCat.of M))
        ((PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
          (actualNormalAssociatedModuleRingPresheafIso A C).hom) ≫
        (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
          (actualNormalAssociatedRingModuleSheafLift A C).val) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg
    (fun f => (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
      (actualNormalAssociatedModuleRingPresheafIso A C).hom ≫ f)
    (actualNormalAssociatedRingModuleSheafLift_unit A C)

set_option backward.isDefEq.respectTransparency false in
/-- Every true degree-module inclusion keeps its literal section inclusion under the whole sheaf isomorphism. -/
theorem actualNormalAssociatedModuleRingSheafIso_degree (A : GermIdeal n M) (C : Set M)
    (q : ℕ) :
    (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (Sigma.ι (fun k : ℕ => HironakaSmoothCentreRealDomainActualNormalLayerScalars.actualNormalLayerModulePresheaf A C k) q) ≫
      toSheafify (Opens.grothendieckTopology (TopCat.of M))
        (actualNormalAssociatedModulePresheaf A C).presheaf ≫
      (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (actualNormalAssociatedModuleRingSheafIso A C).hom.val =
    (PresheafOfModules.toPresheaf (actualComplexStructureRingSheaf n M).obj).map
        (actualNormalAssociatedRingModuleDegreeMap A C q) ≫
      whiskerRight (actualNormalAssociatedRingSheafUnit A C)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) := by
  rw [actualNormalAssociatedModuleRingSheafIso_unit,
    ← Category.assoc, ← Functor.map_comp, actualNormalAssociatedModuleRingPresheafIso_degree]

/-- On EVERY original open, every original homogeneous section retains its literal ring-sheaf unit image. -/
theorem actualNormalAssociatedModuleRingSheafIso_degree_apply (A : GermIdeal n M) (C : Set M)
    (q : ℕ) (U : Opens M)
    (s : HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C q U) :
    ((actualNormalAssociatedModuleRingSheafIso A C).hom.val.app (op U))
      ((toSheafify (Opens.grothendieckTopology (TopCat.of M))
        (actualNormalAssociatedModulePresheaf A C).presheaf).app (op U)
          ((Sigma.ι (fun k : ℕ => HironakaSmoothCentreRealDomainActualNormalLayerScalars.actualNormalLayerModulePresheaf A C k) q).app (op U) s)) =
    (actualNormalAssociatedRingSheafUnit A C).app (op U)
      (DirectSum.of (fun k => HironakaSmoothCentreRealDomainActualNormalLayerStalk.actualNormalLayerSection A C k U) q s) := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (actualNormalAssociatedModuleRingSheafIso_degree A C q) (op U)) s

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedModuleRingSheaf
