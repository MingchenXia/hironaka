/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechSheafMorphisms

/-! # Actual original global-section and native H0 map naturality

All canonical kernel, native cycle and sheaf-gluing comparisons are the actual
original maps. No naturality, representative or global-section output premise.
-/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.SheafH0Naturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
section NativeZero
variable {K : Type u} [CommRing K]

/-- The canonical actual original kernel representative of EVERY actual native H0 class. -/
def zeroRepresentative (C : CochainComplex (ModuleCat.{u} K) ℕ) : C.homology 0 ⟶ C.X 0 :=
  (nativeCochainZeroCocyclesIso C).inv ≫ ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype

/-- The SAME original representative is the actual native inverse homology projection and original cycle inclusion. -/
theorem zeroRepresentative_eq (C : CochainComplex (ModuleCat.{u} K) ℕ) :
    zeroRepresentative C=C.isoHomologyπ₀.inv ≫ C.iCycles 0 := by
  have hK : (C.sc' 0 0 1).moduleCatCyclesIso.hom ≫
      ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype=(C.sc' 0 0 1).iCycles :=
    (C.sc' 0 0 1).moduleCatCyclesIso_hom_i
  simp only [zeroRepresentative, nativeCochainZeroCocyclesIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [hK, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- EVERY actual original cochain map retains the SAME original canonical H0 representative. -/
theorem zeroRepresentative_naturality {C D : CochainComplex (ModuleCat.{u} K) ℕ} (v : C ⟶ D) :
    HomologicalComplex.homologyMap v 0 ≫ zeroRepresentative D=zeroRepresentative C ≫ v.f 0 := by
  rw [zeroRepresentative_eq, zeroRepresentative_eq, ← Category.assoc,
    CochainComplex.isoHomologyπ₀_inv_naturality, Category.assoc, HomologicalComplex.cyclesMap_i]
  rfl

/-- The ENTIRE actual native H0 class is determined by its SAME original zeroth-term representative. -/
theorem zeroRepresentative_injective (C : CochainComplex (ModuleCat.{u} K) ℕ) :
    Function.Injective (zeroRepresentative C).hom := by
  intro x y hxy
  apply (nativeCochainZeroCocyclesIso C).toLinearEquiv.symm.injective
  exact Subtype.val_injective hxy

variable {ι : Type u} [LinearOrder ι] (F : Finset ι ⥤ ModuleCat.{u} K)

/-- The actual original subset zero-cocycle comparison retains precisely the SAME literal original kernel inclusion. -/
theorem subset_hom_zeroRepresentative :
    (actualSubsetCechZeroCocyclesIso F).hom ≫ zeroRepresentative (subsetCechComplex F) =
      ModuleCat.ofHom (LinearMap.ker (subsetCechCardDifferential F 1)).subtype := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((nativeCochainZeroCocyclesIso (subsetCechComplex F)).inv
    ((actualSubsetCechZeroCocyclesIso F).hom x)).val = x.val
  have h := (nativeCochainZeroCocyclesIso (subsetCechComplex F)).toLinearEquiv.symm_apply_apply x
  exact congrArg Subtype.val h
end NativeZero


section NativeOpen
variable {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)

/-- Every actual native open-equality frame commutes with the SAME original sheaf component. -/
theorem openIso_naturality {V W : X.Opens} (h : V=W) (s : bundleSections M V) :
    (actualSchemeModuleOpenIso N h).hom ((a.val.app (op V)).hom s)=
      (a.val.app (op W)).hom ((actualSchemeModuleOpenIso M h).hom s) := by
  exact (ConcreteCategory.congr_hom (a.val.naturality (homOfLE h.symm.le).op) s).symm
end NativeOpen

section OriginalSheaf
variable {X : Scheme.{u}} {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤))
  (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U=⊤)

/-- The SAME original global comparison followed by its actual canonical native representative. -/
def globalRepresentative :
    actualSchemeModuleBaseGlobalSections M c ⟶
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M U c)).X 0 :=
  (actualSchemeModuleBaseGlobalHomologyIso M U c hU).hom ≫
    zeroRepresentative (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M U c))

/-- The WHOLE original global representative is the actual original gluing zero-cocycle inclusion. -/
theorem globalRepresentative_eq :
    globalRepresentative c M U hU =
      (actualSchemeModuleBaseGlobalZeroCocyclesIso M U c hU).hom ≫
        ModuleCat.ofHom (LinearMap.ker
          (subsetCechCardDifferential (actualSchemeModuleBaseSubsetDiagram M U c) 1)).subtype := by
  unfold globalRepresentative actualSchemeModuleBaseGlobalHomologyIso
  rw [Iso.trans_hom, Category.assoc, subset_hom_zeroRepresentative]

/-- EVERY singleton value of the genuine original global representative is the SAME literal original restriction. -/
theorem globalRepresentative_singleton (i : ι) (s : actualSchemeModuleBaseGlobalSections M c) :
    (actualSchemeModuleSingletonIso M U i).hom
      ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram M U c) 1 from
        (globalRepresentative c M U hU).hom s).val {i}) =
      M.val.map (U i).leTop.op (show bundleSections M ⊤ from s) := by
  have hrep := congrArg (fun b : actualSchemeModuleBaseGlobalSections M c ⟶
      (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M U c)).X 0 =>
    (actualSchemeModuleSingletonIso M U i).hom
      ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram M U c) 1 from b.hom s).val {i}))
    (globalRepresentative_eq c M U hU)
  refine hrep.trans ?_
  change (actualSchemeModuleSingletonIso M U i).hom
    (((actualSchemeModuleGlobalZeroCocyclesEquiv M U hU)
      (show bundleSections M ⊤ from s)).val.val {i}) = _
  let b := (bundleGlobalCechEquiv M U hU) (show bundleSections M ⊤ from s)
  let a := (actualSchemeModuleCompatibleEquiv M U).symm b
  let z := (actualSubsetCechZeroCocyclesCompatibleEquiv (actualSchemeModuleSubsetDiagram M U)).symm a
  change (actualSchemeModuleSingletonIso M U i).hom (z.val.val {i}) = _
  have hz := congrArg (fun v : actualSubsetSingletonCompatible (actualSchemeModuleSubsetDiagram M U) => v.val i)
    ((actualSubsetCechZeroCocyclesCompatibleEquiv (actualSchemeModuleSubsetDiagram M U)).apply_symm_apply a)
  change z.val.val {i}=a.val i at hz
  have ha := congrArg (fun v : bundleCechSections M U => v.val i)
    ((actualSchemeModuleCompatibleEquiv M U).apply_symm_apply b)
  change (actualSchemeModuleSingletonIso M U i).hom (a.val i)=
    M.val.map (U i).leTop.op (show bundleSections M ⊤ from s) at ha
  exact (congrArg (actualSchemeModuleSingletonIso M U i).hom hz).trans ha

variable {N : X.Modules} (a : M ⟶ N)

/-- The ENTIRE actual original global cochain representative retains EVERY original sheaf morphism. -/
theorem globalRepresentative_naturality :
    SheafMorphisms.globalMap c a ≫ globalRepresentative c N U hU =
      globalRepresentative c M U hU ≫ ((SheafMorphisms.complexFunctor c U).map a).f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext S
  by_cases hS : S.card=1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
    apply (actualSchemeModuleSingletonIso N U i).toLinearEquiv.injective
    change (actualSchemeModuleSingletonIso N U i).hom
        ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram N U c) 1 from
          (globalRepresentative c N U hU).hom ((SheafMorphisms.globalMap c a).hom s)).val {i}) =
      (actualSchemeModuleSingletonIso N U i).hom
        ((a.val.app (op (actualSchemeSubsetOpen U {i}))).hom
          ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram M U c) 1 from
            (globalRepresentative c M U hU).hom s).val {i}))
    rw [globalRepresentative_singleton]
    let x := (show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram M U c) 1 from
      (globalRepresentative c M U hU).hom s).val {i}
    have ho := openIso_naturality a (Finset.inf_singleton (f := U)) x
    have hs := globalRepresentative_singleton c M U hU i s
    have hn := (ConcreteCategory.congr_hom (a.val.naturality (U i).leTop.op)
      (show bundleSections M ⊤ from s)).symm
    exact hn.trans ((congrArg (a.val.app (op (U i))).hom hs).symm.trans ho.symm)
  · exact ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram N U c) 1 from
      (globalRepresentative c N U hU).hom ((SheafMorphisms.globalMap c a).hom s)).property S hS).trans
      ((show subsetCechCardPiece (actualSchemeModuleBaseSubsetDiagram N U c) 1 from
        (((SheafMorphisms.complexFunctor c U).map a).f 0).hom
          ((globalRepresentative c M U hU).hom s)).property S hS).symm

/-- The WHOLE actual original global-section/native H0 comparison is natural for EVERY actual original native sheaf morphism. -/
theorem globalHomologyIso_naturality :
    SheafMorphisms.globalMap c a ≫ (actualSchemeModuleBaseGlobalHomologyIso N U c hU).hom =
      (actualSchemeModuleBaseGlobalHomologyIso M U c hU).hom ≫
        HomologicalComplex.homologyMap ((SheafMorphisms.complexFunctor c U).map a) 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply zeroRepresentative_injective (subsetCechComplex (actualSchemeModuleBaseSubsetDiagram N U c))
  have hg := congrArg (fun b => b.hom s) (globalRepresentative_naturality c M U hU a)
  have hn := congrArg (fun b => b.hom ((actualSchemeModuleBaseGlobalHomologyIso M U c hU).hom s))
    (zeroRepresentative_naturality ((SheafMorphisms.complexFunctor c U).map a))
  exact hg.trans hn.symm
end OriginalSheaf

end Hironaka.Geometry.ProperSteinProjectiveCech.SheafH0Naturality
