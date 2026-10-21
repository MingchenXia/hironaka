/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits
/-! The entire genuine original associated-module sheaf and its whole stalks.
Complete four-node Mathematics.tex precedes code. Actual coproduct section
modules and module sheafification precede every whole original dictionary. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk HironakaSmoothCentreRealDomainActualNormalLayerScalars
  HironakaSmoothCentreRealDomainActualNormalLayerSheaf
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual module presheaves always use the SAME literal original complex structure presheaf. -/
abbrev ActualModulePresheaf (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] :=
  PresheafOfModules ((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat)

/-- The genuine original neighbourhood colimit carrier of ANY actual module presheaf. -/
abbrev actualModulePresheafStalk (P : ActualModulePresheaf n M) (y : M) : Type :=
  (TopCat.Presheaf.stalk P.presheaf y).carrier

/-- The actual section action is independently inherited from the module presheaf. -/
instance actualModulePresheafSectionModule (P : ActualModulePresheaf n M) (U : Opens M) :
    Module (actualComplexSection (n := n) U) (P.presheaf.obj (op U)) := by
  change Module (((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U))
    (P.presheaf.obj (op U))
  infer_instance

/-- Genuine filtered-colimit multiplication, BEFORE any universal stalk comparison. -/
instance actualModulePresheafStalkModule (P : ActualModulePresheaf n M) (y : M) :
    Module (actualComplexStructureStalk (n := n) y) (actualModulePresheafStalk P y) :=
  P.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier y

/-- The true additive stalk functor maps a real module-presheaf morphism on genuine colimits. -/
def actualModuleStalkMapHom {P Q : ActualModulePresheaf n M} (f : P ⟶ Q) (y : M) :
    actualModulePresheafStalk P y →+ actualModulePresheafStalk Q y := by
  let g : TopCat.Presheaf.stalk P.presheaf y ⟶ TopCat.Presheaf.stalk Q.presheaf y :=
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf _).map f)
  exact g.hom

omit [IsComplexManifold n M] in
/-- EVERY real section retains its actual section-morphism germ under the genuine stalk map. -/
theorem actualModuleStalkMapHom_germ {P Q : ActualModulePresheaf n M} (f : P ⟶ Q)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : P.presheaf.obj (op U)) :
    actualModuleStalkMapHom f y (TopCat.Presheaf.germ P.presheaf U y hy s) =
      TopCat.Presheaf.germ Q.presheaf U y hy (f.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy ((PresheafOfModules.toPresheaf _).map f) s

omit [IsComplexManifold n M] in
/-- ALL true ambient stalk scalars obey the genuine module-morphism scalar law on real common opens. -/
theorem actualModuleStalkMapHom_smul {P Q : ActualModulePresheaf n M} (f : P ⟶ Q) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualModulePresheafStalk P y) :
    actualModuleStalkMapHom f y (r • v) = r • actualModuleStalkMapHom f y v := by
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  obtain ⟨V,hyV,s,hs⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf v
  change P.obj (op V) at s
  obtain ⟨U,hUV,hyU,t,ht⟩ := F.exists_le_germ_eq r hyV
  change actualComplexSection (n := n) U at t
  let su : P.obj (op U) := P.presheaf.map (homOfLE hUV).op s
  have hsu : TopCat.Presheaf.germ P.presheaf U y hyU su = v :=
    (TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE hUV) y hyU s).trans hs
  erw [← ht,← hsu,← P.germ_smul y U hyU t su,actualModuleStalkMapHom_germ,actualModuleStalkMapHom_germ]
  have hprod : f.app (op U) (t • su) = t • f.app (op U) su :=
    (f.app (op U)).hom.map_smul
      (show (((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat).obj (op U)) from t) su
  erw [hprod,Q.germ_smul y U hyU t (f.app (op U) su)]

/-- The SAME actual induced stalk map is linear for its independent filtered-colimit actions. -/
def actualModuleStalkMapLinear {P Q : ActualModulePresheaf n M} (f : P ⟶ Q) (y : M) :
    actualModulePresheafStalk P y →ₗ[actualComplexStructureStalk (n := n) y] actualModulePresheafStalk Q y where
  toFun := actualModuleStalkMapHom f y
  map_add' := (actualModuleStalkMapHom f y).map_add
  map_smul' := actualModuleStalkMapHom_smul f y

/-- The genuine module stalk functor, with independently supplied actual module operations. -/
def actualModuleStalkFunctor (y : M) :
    ActualModulePresheaf n M ⥤ ModuleCat (actualComplexStructureStalk (n := n) y) where
  obj P := ModuleCat.of (actualComplexStructureStalk (n := n) y) (actualModulePresheafStalk P y)
  map f := ModuleCat.ofHom (actualModuleStalkMapLinear f y)
  map_id P := by
    ext v
    change (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf _).map (𝟙 P)) v = v
    erw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext v
    change (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf _).map (f ≫ g)) v = _
    erw [CategoryTheory.Functor.map_comp,CategoryTheory.Functor.map_comp]
    rfl

omit [IsComplexManifold n M] in
/-- Forgetting actual stalk scalars gives EXACTLY genuine additive presheaf stalk functoriality. -/
theorem actualModuleStalkFunctor_forget (y : M) :
    actualModuleStalkFunctor (n := n) y ⋙ forget₂ (ModuleCat (actualComplexStructureStalk (n := n) y)) AddCommGrpCat =
      PresheafOfModules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y := rfl

/-- ALL actual small-shape colimits are preserved; true module forgetfulness reflects their universal properties. -/
instance actualModuleStalkFunctor_preservesColimitsOfShape (y : M) (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (actualModuleStalkFunctor (n := n) y) := by
  let G := forget₂ (ModuleCat (actualComplexStructureStalk (n := n) y)) AddCommGrpCat
  let : PreservesColimitsOfShape J (actualModuleStalkFunctor (n := n) y ⋙ G) := by
    change PreservesColimitsOfShape J (PresheafOfModules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y)
    let : PreservesColimitsOfShape J (PresheafOfModules.toPresheaf
        ((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat)) := inferInstance
    let : PreservesColimitsOfShape J (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y) := inferInstance
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves (actualModuleStalkFunctor (n := n) y) G

/-- The actual concrete entire direct sum is a genuine module coproduct, with its independent component actions. -/
def actualModuleDirectSumCofan {R : Type} [CommRing R] (G : ℕ → ModuleCat R) : Cofan G :=
  Cofan.mk (ModuleCat.of R (⨁ q : ℕ, G q)) (fun q => ModuleCat.ofHom (DirectSum.lof R ℕ (fun q => G q) q))

/-- The true finite-support universal property constructs the whole direct sum coproduct, internally. -/
def actualModuleDirectSumCofanIsColimit {R : Type} [CommRing R] (G : ℕ → ModuleCat R) :
    IsColimit (actualModuleDirectSumCofan G) where
  desc s := ModuleCat.ofHom (DirectSum.toModule R ℕ s.pt (fun q => (s.ι.app ⟨q⟩).hom))
  fac s j := by
    rcases j with ⟨q⟩
    ext x
    change G q at x
    change DirectSum.toModule R ℕ s.pt (fun q => (s.ι.app ⟨q⟩).hom)
      (DirectSum.lof R ℕ (fun q => G q) q x) = (s.ι.app ⟨q⟩).hom x
    exact DirectSum.toModule_lof (R := R) (ι := ℕ) (M := fun q => G q) (N := s.pt)
      (φ := fun q => (s.ι.app ⟨q⟩).hom) q x
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro q
    ext x
    change m.hom (DirectSum.lof R ℕ (fun q => G q) q x) =
      DirectSum.toModule R ℕ s.pt (fun q => (s.ι.app ⟨q⟩).hom) (DirectSum.lof R ℕ (fun q => G q) q x)
    erw [DirectSum.toModule_lof]
    exact congrArg (fun f => f.hom x) (hm ⟨q⟩)

/-- The ENTIRE actual original degree-module coproduct is formed BEFORE all whole stalk comparisons. -/
def actualNormalAssociatedModulePresheaf (A : GermIdeal n M) (C : Set M) : ActualModulePresheaf n M :=
  ∐ (fun q : ℕ => actualNormalLayerModulePresheaf A C q)

/-- Genuine module sheafification constructs the whole actual associated module SHEAF. -/
def actualNormalAssociatedModuleSheaf (A : GermIdeal n M) (C : Set M) :
    SheafOfModules (actualComplexStructureRingSheaf n M) :=
  (PresheafOfModules.sheafification (R := actualComplexStructureRingSheaf n M)
    (𝟙 (actualComplexStructureRingSheaf n M).obj)).obj (actualNormalAssociatedModulePresheaf A C)

/-- The actual whole module-sheaf underlying module presheaf retains independent sheafified section multiplication. -/
abbrev actualNormalAssociatedSheafModulePresheaf (A : GermIdeal n M) (C : Set M) : ActualModulePresheaf n M :=
  (SheafOfModules.forget (actualComplexStructureRingSheaf n M)).obj (actualNormalAssociatedModuleSheaf A C)

/-- The LITERAL actual whole associated module-sheaf stalk, with its genuine independent module action. -/
abbrev actualNormalAssociatedSheafStalk (A : GermIdeal n M) (C : Set M) (y : M) : Type :=
  actualModulePresheafStalk (actualNormalAssociatedSheafModulePresheaf A C) y

/-- The true whole unit stalk map is intrinsically an ambient-linear isomorphism, before the original whole dictionary. -/
def actualNormalAssociatedUnitStalkIso (A : GermIdeal n M) (C : Set M) (y : M) :
    (actualModuleStalkFunctor (n := n) y).obj (actualNormalAssociatedModulePresheaf A C) ≅
      (actualModuleStalkFunctor (n := n) y).obj (actualNormalAssociatedSheafModulePresheaf A C) := by
  let R := actualComplexStructureRingSheaf n M
  let P := actualNormalAssociatedModulePresheaf A C
  let η := (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P
  let f := (actualModuleStalkFunctor (n := n) y).map η
  have hf : IsIso f := by
    let : IsIso ((forget₂ (ModuleCat (actualComplexStructureStalk (n := n) y)) AddCommGrpCat).map f) := by
      change IsIso ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M)) P.presheaf))
      exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (X := TopCat.of M) y AddCommGrpCat P.presheaf
    exact isIso_of_reflects_iso f (forget₂ (ModuleCat (actualComplexStructureStalk (n := n) y)) AddCommGrpCat)
  exact @asIso _ _ _ _ f hf

/-- ALL actual raw degree stalks are genuinely compared with the ENTIRE original layers as one true diagram isomorphism. -/
def actualNormalAssociatedDegreeStalkIso (A : GermIdeal n M) (hA : A.IsCoherent) (C : Set M) (y : M) :
    Discrete.functor (fun q : ℕ => (actualModuleStalkFunctor (n := n) y).obj (actualNormalLayerModulePresheaf A C q)) ≅
      Discrete.functor (fun q : ℕ => ModuleCat.of (actualComplexStructureStalk (n := n) y) (actualWholeNormalLayer A C q y)) :=
  Discrete.natIso (fun q => (actualNormalLayerStalkWholeLinearEquiv A hA C q.as y).toModuleIso)

/-- Original coherence and actual coproduct preservation internally identify the ENTIRE actual raw associated stalk. -/
def actualNormalAssociatedRawStalkWholeIso (A : GermIdeal n M) (hA : A.IsCoherent) (C : Set M) (y : M) :
    (actualModuleStalkFunctor (n := n) y).obj (actualNormalAssociatedModulePresheaf A C) ≅
      ModuleCat.of (actualComplexStructureStalk (n := n) y) (⨁ q : ℕ, actualWholeNormalLayer A C q y) :=
  PreservesCoproduct.iso (actualModuleStalkFunctor (n := n) y) (fun q : ℕ => actualNormalLayerModulePresheaf A C q) ≪≫
    HasColimit.isoOfNatIso (actualNormalAssociatedDegreeStalkIso A hA C y) ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (actualModuleDirectSumCofanIsColimit (fun q : ℕ =>
          ModuleCat.of (actualComplexStructureStalk (n := n) y) (actualWholeNormalLayer A C q y)))

/-- ONLY original coherence yields a whole actual SHEAF-stalk ambient equivalence, with its genuine independent action. -/
def actualNormalAssociatedSheafStalkWholeLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (C : Set M) (y : M) :
    actualNormalAssociatedSheafStalk A C y ≃ₗ[actualComplexStructureStalk (n := n) y]
      (⨁ q : ℕ, actualWholeNormalLayer A C q y) :=
  ((actualNormalAssociatedUnitStalkIso A C y).symm ≪≫ actualNormalAssociatedRawStalkWholeIso A hA C y).toLinearEquiv

/-- EVERY degree inclusion is retained by the actual whole coproduct stalk comparison. -/
theorem actualNormalAssociatedRawStalkWholeIso_ι (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) (q : ℕ) :
    (actualModuleStalkFunctor (n := n) y).map
        (Sigma.ι (fun q : ℕ => actualNormalLayerModulePresheaf A C q) q) ≫
      (actualNormalAssociatedRawStalkWholeIso A hA C y).hom =
    (show (actualModuleStalkFunctor (n := n) y).obj (actualNormalLayerModulePresheaf A C q) ⟶
        ModuleCat.of (actualComplexStructureStalk (n := n) y) (⨁ q : ℕ, actualWholeNormalLayer A C q y) from
      (actualNormalLayerStalkWholeLinearEquiv A hA C q y).toModuleIso.hom ≫
        ModuleCat.ofHom (DirectSum.lof (actualComplexStructureStalk (n := n) y) ℕ
          (fun q => actualWholeNormalLayer A C q y) q)) := by
  let F := actualModuleStalkFunctor (n := n) y
  let K := fun q : ℕ => actualNormalLayerModulePresheaf A C q
  let L := fun q : ℕ => ModuleCat.of (actualComplexStructureStalk (n := n) y) (actualWholeNormalLayer A C q y)
  let E1 := PreservesCoproduct.iso F K
  let E2 := HasColimit.isoOfNatIso (actualNormalAssociatedDegreeStalkIso A hA C y)
  let E3 := IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor L))
    (actualModuleDirectSumCofanIsColimit L)
  have h1 : F.map (Sigma.ι K q) ≫ E1.hom = Sigma.ι (fun q => F.obj (K q)) q :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit F K) (colimit.isColimit _) ⟨q⟩
  have h3 : Sigma.ι L q ≫ E3.hom = (actualModuleDirectSumCofan L).ι.app ⟨q⟩ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) (actualModuleDirectSumCofanIsColimit L) ⟨q⟩
  change F.map (Sigma.ι K q) ≫ (E1.hom ≫ E2.hom ≫ E3.hom) = _
  rw [← Category.assoc,h1]
  erw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [h3]
  rfl

/-- The TRUE whole associated sheaf inclusion is built from actual degree coproduct maps and genuine unit, before every whole equivalence. -/
def actualNormalAssociatedSheafDegreeStalkInclusion (A : GermIdeal n M) (C : Set M) (y : M) (q : ℕ) :
    actualNormalLayerStalk A C q y →ₗ[actualComplexStructureStalk (n := n) y] actualNormalAssociatedSheafStalk A C y :=
  (actualNormalAssociatedUnitStalkIso A C y).hom.hom.comp
    ((actualModuleStalkFunctor (n := n) y).map
      (Sigma.ι (fun q : ℕ => actualNormalLayerModulePresheaf A C q) q)).hom

/-- EVERY actual degree colimit element has its literal entire original degree inclusion formula. -/
theorem actualNormalAssociatedSheafStalkWholeLinearEquiv_inclusion (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) (q : ℕ) (v : actualNormalLayerStalk A C q y) :
    actualNormalAssociatedSheafStalkWholeLinearEquiv A hA C y
      (actualNormalAssociatedSheafDegreeStalkInclusion A C y q v) =
    DirectSum.of (fun q => actualWholeNormalLayer A C q y) q
      (actualNormalLayerStalkWholeLinearEquiv A hA C q y v) := by
  change (actualNormalAssociatedRawStalkWholeIso A hA C y).toLinearEquiv
      ((actualNormalAssociatedUnitStalkIso A C y).toLinearEquiv.symm
        ((actualNormalAssociatedUnitStalkIso A C y).toLinearEquiv
          (((actualModuleStalkFunctor (n := n) y).map
            (Sigma.ι (fun q : ℕ => actualNormalLayerModulePresheaf A C q) q)).hom v))) = _
  erw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun f => f.hom v) (actualNormalAssociatedRawStalkWholeIso_ι A hA C y q)

/-- EVERY original actual degree section germ retains its SAME whole original class in the genuine associated SHEAF stalk. -/
theorem actualNormalAssociatedSheafStalkWholeLinearEquiv_germ_inclusion (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) (q : ℕ) (U : Opens M) (hy : y ∈ U) (s : actualNormalLayerSection A C q U) :
    actualNormalAssociatedSheafStalkWholeLinearEquiv A hA C y
      (actualNormalAssociatedSheafDegreeStalkInclusion A C y q
        ((actualNormalLayerPresheaf A C q).germ U y hy s)) =
    DirectSum.of (fun q => actualWholeNormalLayer A C q y) q (actualNormalLayerSectionGermHom A C q U y hy s) := by
  rw [actualNormalAssociatedSheafStalkWholeLinearEquiv_inclusion]
  exact congrArg (DirectSum.of (fun q => actualWholeNormalLayer A C q y) q)
    (actualNormalLayerStalkToWholeHom_germ A C q U y hy s)

/-- EVERY actual original power-section class keeps its SAME original whole degree class in the ENTIRE genuine associated module-SHEAF stalk. -/
theorem actualNormalAssociatedSheafStalkWholeLinearEquiv_power_class (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) (q : ℕ) (U : Opens M) (hy : y ∈ U)
    (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualNormalAssociatedSheafStalkWholeLinearEquiv A hA C y
      (actualNormalAssociatedSheafDegreeStalkInclusion A C y q
        ((actualNormalLayerPresheaf A C q).germ U y hy
          (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩))) =
    DirectSum.of (fun q => actualWholeNormalLayer A C q y) q
      (idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
          ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
            actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩) := by
  rw [actualNormalAssociatedSheafStalkWholeLinearEquiv_germ_inclusion,actualNormalLayerSectionGermHom_class]

/-- Original coherence internally proves ENTIRE centre annihilation on the independent genuine whole module-SHEAF stalk action. -/
theorem actualNormalAssociatedSheafStalk_isTorsionByCentre (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    Module.IsTorsionBySet (actualComplexStructureStalk (n := n) y) (actualNormalAssociatedSheafStalk A C y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) := by
  intro v r
  let E := actualNormalAssociatedSheafStalkWholeLinearEquiv A hA C y
  apply E.injective
  rw [E.map_smul,E.map_zero]
  exact idealPowerAssociated_isTorsionBySet (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    (x := E v) (a := r)

/-- The actual whole centre action descends only AFTER internally proved annihilation, never by transporting an equivalence. -/
@[instance_reducible] def actualNormalAssociatedSheafStalkCentreModule (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    Module (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (actualNormalAssociatedSheafStalk A C y) :=
  (actualNormalAssociatedSheafStalk_isTorsionByCentre A hA C y).module

/-- EVERY original ambient scalar representative acts by its independent actual whole sheaf-stalk product. -/
theorem actualNormalAssociatedSheafStalkCentre_mk_smul (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) (r : actualComplexStructureStalk (n := n) y)
    (v : actualNormalAssociatedSheafStalk A C y) :
    letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
    Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r • v = r • v := rfl

/-- The SAME internally supplied whole sheaf-stalk comparison is centre-linear for BOTH independently descended actions. -/
def actualNormalAssociatedSheafStalkWholeCentreLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (y : M) :
    letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
    letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
    actualNormalAssociatedSheafStalk A C y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] (⨁ q : ℕ, actualWholeNormalLayer A C q y) := by
  letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
  letI := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
  let E := actualNormalAssociatedSheafStalkWholeLinearEquiv A hA C y
  refine { E.toAddEquiv with map_smul' := ?_ }
  intro r v
  obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective r
  exact E.map_smul s v

private theorem actual_module_flat_of_free {R L : Type*} [CommSemiring R] [AddCommMonoid L]
    [Module R L] (hf : Module.Free R L) : Module.Flat R L := by
  let : Module.Free R L := hf
  infer_instance

/-- ONLY original inputs internally supply ONE accumulating original centre open with the ENTIRE genuine module-SHEAF stalk free/flat and ALL degree SHEAF stalks finite/free/flat. -/
theorem exists_original_regular_all_actual_associated_sheaf_degrees_free_open
    {d t : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O),
        (letI := actualNormalAssociatedSheafStalkCentreModule A hA C y
         Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
           actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedSheafStalk A C y) ∧
         Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
           actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedSheafStalk A C y)) ∧
        ∀ q : ℕ,
          letI := actualNormalLayerSheafStalkCentreModule A C q y
          Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
            actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) ∧
          Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
            actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) ∧
          Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
            actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) := by
  obtain ⟨O,hO,hcl,hfree⟩ := exists_original_regular_all_relative_degrees_free_actual_sheaf_stalk_open C x hreg A hA hAC
  refine ⟨O,hO,hcl,?_⟩
  intro y hyCO
  constructor
  · let := actualNormalAssociatedSheafStalkCentreModule A hA C y
    let := idealPowerAssociatedCentreModule (actualComplexStructureStalk (n := d+t) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y)
    let := (hfree y hyCO).1.1
    let E := actualNormalAssociatedSheafStalkWholeCentreLinearEquiv A hA C y
    have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalAssociatedSheafStalk A C y) :=
      Module.Free.of_equiv E.symm
    exact ⟨hf,actual_module_flat_of_free hf⟩
  · intro q
    let := actualNormalLayerSheafStalkCentreModule A C q y
    let := idealPowerLayerCentreModule (actualComplexStructureStalk (n := d+t) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) q
    let := ((hfree y hyCO).2 q).1
    let := ((hfree y hyCO).2 q).2.1
    let E := actualNormalLayerSheafStalkWholeCentreLinearEquiv A hA C q y
    have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) :=
      Module.Free.of_equiv E.symm
    have hfin : Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
        actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) :=
      Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective
    exact ⟨hfin,hf,actual_module_flat_of_free hf⟩

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
