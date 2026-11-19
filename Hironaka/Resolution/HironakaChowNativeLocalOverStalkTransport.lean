import Hironaka.Resolution.HironakaChowNativeLocalOverFiniteDataTransport
import Hironaka.Resolution.HironakaSingularLocallyFreeStalk
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Native original local/Over sections and whole stalk comparisons.
Blueprint first: `hironaka-g10-native-local-over-stalk-transport.tex`.
No finite-type or finite-presentation assumptions or ambient extensions. -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaChowNativeLocalOverStalkTransport

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeModuleStalkExact HironakaChowNativeArbitraryOverRealization
  HironakaChowNativeLocalOverFiniteDataTransport

private abbrev ambientOpen (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) := (U.overEquivalence.inverse.obj V).left

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual accepted return equivalence followed by native literal realization. -/
def localOverTransport (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    SheafOfModules.{0}
        (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) ⥤
      SheafOfModules.{0} (forgetRing (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪) :=
  (localModuleEquivalence X U V).inverse ⋙ realizationFunctor X (ambientOpen X U V)

private abbrev sourceObject (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (B : Opens (TopCat.of (ambientOpen X U V))) :=
  (localSiteEquivalence X U V).inverse.obj
    ((ambientOpen X U V).overEquivalence.inverse.obj B)

private def sectionOpenIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (B : Opens (TopCat.of (ambientOpen X U V))) :=
  (Over.forget (ambientOpen X U V)).mapIso
    ((localSiteEquivalence X U V).counitIso.app
      ((ambientOpen X U V).overEquivalence.inverse.obj B))

/-- The original ring presheaf on the actual site counit; no replacement scalar map. -/
def localOverRingSectionEquiv (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (B : Opens (TopCat.of (ambientOpen X U V))) :
    ↑((X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.obj (op B)) ≃+*
      ↑((X.restrict U.isOpenEmbedding).presheaf.obj
        (op (sourceObject X U V B).left)) :=
  (X.presheaf.mapIso (sectionOpenIso X U V B).op).commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- Every native Over module retains its original section, with the original counit scalars. -/
def localOverSectionIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (Q : SheafOfModules.{0}
      (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
      ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    (B : Opens (TopCat.of (ambientOpen X U V))) :
    (ModuleCat.restrictScalars (localOverRingSectionEquiv X U V B).symm.toRingHom).obj
        (((localOverTransport X U V).obj Q).val.obj (op B)) ≅
      Q.val.obj (op (sourceObject X U V B)) := by
  change (ModuleCat.restrictScalars
    (localOverRingSectionEquiv X U V B).symm.toRingHom).obj
      ((ModuleCat.restrictScalars (localOverRingSectionEquiv X U V B).toRingHom).obj
        (Q.val.obj (op (sourceObject X U V B)))) ≅ _
  exact ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (localOverRingSectionEquiv X U V B)).unitIso.app
      (Q.val.obj (op (sourceObject X U V B)))).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionIso_hom_apply (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (Q : SheafOfModules.{0} ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    (B : Opens (TopCat.of (ambientOpen X U V)))
    (m : ((localOverTransport X U V).obj Q).val.obj (op B)) :
    (localOverSectionIso X U V Q B).hom m = m := rfl

private def originalPoint (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) : ambientOpen X U V :=
  ⟨p.val,⟨p,hpV,rfl⟩⟩

/-- Original ring stalks compared through the SAME original X-stalk. -/
def localOverRingStalkEquiv (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    ↑((X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.stalk
      (originalPoint X U V p hpV)) ≃+*
      ↑((X.restrict U.isOpenEmbedding).presheaf.stalk p) :=
  (X.restrictStalkIso (ambientOpen X U V).isOpenEmbedding
    (originalPoint X U V p hpV)).commRingCatIsoToRingEquiv.trans
      (X.restrictStalkIso U.isOpenEmbedding p).symm.commRingCatIsoToRingEquiv

private def nativeInclusion (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) : TopCat.of (ambientOpen X U V) ⟶ TopCat.of U :=
  (Opens.toTopCat X.toTopCat).map (U.overEquivalence.inverse.obj V).hom

private theorem nativeInclusion_isOpenEmbedding (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U)) :
    Topology.IsOpenEmbedding (nativeInclusion X U V) :=
  Topology.IsOpenEmbedding.inclusion (U.overEquivalence.inverse.obj V).hom.le
    ((ambientOpen X U V).isOpen.preimage continuous_subtype_val)

private theorem sourceOpen_eq_image (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (B : Opens (TopCat.of (ambientOpen X U V))) :
    (sourceObject X U V B).left = (nativeInclusion_isOpenEmbedding X U V).functor.obj B := by
  ext p
  change (p.val ∈ Subtype.val '' (B : Set (ambientOpen X U V))) ↔
    p ∈ (nativeInclusion X U V) '' (B : Set (ambientOpen X U V))
  constructor
  · rintro ⟨q,hq,h⟩
    exact ⟨q,hq,Subtype.ext h⟩
  · rintro ⟨q,hq,h⟩
    exact ⟨q,hq,congrArg Subtype.val h⟩

private abbrev originalSourceFunctor (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :=
  (ambientOpen X U V).overEquivalence.inverse ⋙
    (localSiteEquivalence X U V).inverse ⋙ Over.forget V

set_option backward.isDefEq.respectTransparency.types false in
private def underlyingPresheafIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪)) :
    ((localOverTransport X U V).obj (M.over V)).val.presheaf ≅
      (nativeInclusion_isOpenEmbedding X U V).functor.op ⋙ M.val.presheaf := by
  refine NatIso.ofComponents (fun B => ?_) ?_
  · change M.val.presheaf.obj (op (sourceObject X U V B.unop).left) ≅
      M.val.presheaf.obj (op ((nativeInclusion_isOpenEmbedding X U V).functor.obj B.unop))
    exact (M.val.presheaf.mapIso (eqToIso (sourceOpen_eq_image X U V B.unop)).op).symm
  · intro B C f
    change M.val.presheaf.map ((originalSourceFunctor X U V).map f.unop).op ≫
        M.val.presheaf.map (eqToHom (sourceOpen_eq_image X U V C.unop).symm).op =
      M.val.presheaf.map (eqToHom (sourceOpen_eq_image X U V B.unop).symm).op ≫
        M.val.presheaf.map ((nativeInclusion_isOpenEmbedding X U V).functor.map f.unop).op
    rw [← Functor.map_comp,← Functor.map_comp]
    congr 1

private theorem nativeInclusion_point (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (p : U) (hpV : p ∈ V) :
    nativeInclusion X U V (originalPoint X U V p hpV) = p := Subtype.ext rfl

set_option backward.isDefEq.respectTransparency.types false in
private def underlyingStalkIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) :
    TopCat.Presheaf.stalk
      ((localOverTransport X U V).obj (M.over V)).val.presheaf
        (originalPoint X U V p hpV) ≅ TopCat.Presheaf.stalk M.val.presheaf p := by
  let e1 : TopCat.Presheaf.stalk
      ((localOverTransport X U V).obj (M.over V)).val.presheaf
        (originalPoint X U V p hpV) ≅
      TopCat.Presheaf.stalk
        ((nativeInclusion_isOpenEmbedding X U V).functor.op ⋙ M.val.presheaf)
        (originalPoint X U V p hpV) :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0}
      (X := TopCat.of (ambientOpen X U V)) (originalPoint X U V p hpV)).mapIso
        (underlyingPresheafIso X U V M)
  let e2 : TopCat.Presheaf.stalk
      ((nativeInclusion_isOpenEmbedding X U V).functor.op ⋙ M.val.presheaf)
        (originalPoint X U V p hpV) ≅
      TopCat.Presheaf.stalk M.val.presheaf
        (nativeInclusion X U V (originalPoint X U V p hpV)) :=
    PresheafedSpace.restrictStalkIso
      (PresheafedSpace.mk (TopCat.of U) M.val.presheaf)
      (nativeInclusion_isOpenEmbedding X U V) (originalPoint X U V p hpV)
  let e3 : TopCat.Presheaf.stalk M.val.presheaf
      (nativeInclusion X U V (originalPoint X U V p hpV)) ≅
        TopCat.Presheaf.stalk M.val.presheaf p :=
    eqToIso (congrArg (fun q => TopCat.Presheaf.stalk M.val.presheaf q)
      (nativeInclusion_point X U V p hpV))
  exact e1 ≪≫ e2 ≪≫ e3

private theorem originalPoint_mem_source (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (p : U) (hpV : p ∈ V) (B : Opens (TopCat.of (ambientOpen X U V)))
    (hpB : originalPoint X U V p hpV ∈ B) : p ∈ (sourceObject X U V B).left := by
  rw [sourceOpen_eq_image]
  exact ⟨originalPoint X U V p hpV,hpB,nativeInclusion_point X U V p hpV⟩

/-- EVERY original section germ has the actual original ring-stalk value. -/
theorem localOverRingStalkEquiv_germ (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (p : U) (hpV : p ∈ V) (B : Opens (TopCat.of (ambientOpen X U V)))
    (hpB : originalPoint X U V p hpV ∈ B)
    (r : (X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.obj (op B)) :
    localOverRingStalkEquiv X U V p hpV
        ((X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.germ B
          (originalPoint X U V p hpV) hpB r) =
      (X.restrict U.isOpenEmbedding).presheaf.germ (sourceObject X U V B).left p
        (originalPoint_mem_source X U V p hpV B hpB) (localOverRingSectionEquiv X U V B r) := by
  let eU := (X.restrictStalkIso U.isOpenEmbedding p).commRingCatIsoToRingEquiv
  apply eU.injective
  let eW := (X.restrictStalkIso (ambientOpen X U V).isOpenEmbedding
    (originalPoint X U V p hpV)).commRingCatIsoToRingEquiv
  change eU ((eW.trans eU.symm)
    ((X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.germ B
      (originalPoint X U V p hpV) hpB r)) = _
  erw [RingEquiv.trans_apply,RingEquiv.apply_symm_apply]
  change (X.restrictStalkIso (ambientOpen X U V).isOpenEmbedding
      (originalPoint X U V p hpV)).hom
        ((X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.germ B
          (originalPoint X U V p hpV) hpB r) =
    (X.restrictStalkIso U.isOpenEmbedding p).hom
      ((X.restrict U.isOpenEmbedding).presheaf.germ (sourceObject X U V B).left p
        (originalPoint_mem_source X U V p hpV B hpB) (localOverRingSectionEquiv X U V B r))
  erw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply,
    LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (sectionOpenIso X U V B).hom
    p.val ⟨p,originalPoint_mem_source X U V p hpV B hpB,rfl⟩ r).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem underlyingStalkIso_hom_germ (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) (B : Opens (TopCat.of (ambientOpen X U V)))
    (hpB : originalPoint X U V p hpV ∈ B)
    (m : ((localOverTransport X U V).obj (M.over V)).val.obj (op B)) :
    (underlyingStalkIso X U V M p hpV).hom
      (TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
        B (originalPoint X U V p hpV) hpB m) =
    TopCat.Presheaf.germ M.val.presheaf (sourceObject X U V B).left p
      (originalPoint_mem_source X U V p hpV B hpB)
      ((localOverSectionIso X U V (M.over V) B).hom m) := by
  have hsection := sectionIso_hom_apply X U V (M.over V) B m
  erw [hsection]
  change (PresheafedSpace.restrictStalkIso
      (PresheafedSpace.mk (TopCat.of U) M.val.presheaf)
      (nativeInclusion_isOpenEmbedding X U V) (originalPoint X U V p hpV)).hom
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0}
      (X := TopCat.of (ambientOpen X U V)) (originalPoint X U V p hpV)).map
        (underlyingPresheafIso X U V M).hom)
      (TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
        B (originalPoint X U V p hpV) hpB m)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply B
    (originalPoint X U V p hpV) hpB (underlyingPresheafIso X U V M).hom m]
  erw [PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (PresheafedSpace.mk (TopCat.of U) M.val.presheaf)
    (nativeInclusion_isOpenEmbedding X U V) B (originalPoint X U V p hpV) hpB
    ((underlyingPresheafIso X U V M).hom.app (op B) m)]
  change TopCat.Presheaf.germ M.val.presheaf
      ((nativeInclusion_isOpenEmbedding X U V).functor.obj B) p _
        (M.val.presheaf.map (eqToHom (sourceOpen_eq_image X U V B).symm).op m) =
    TopCat.Presheaf.germ M.val.presheaf (sourceObject X U V B).left p _ m
  exact TopCat.Presheaf.germ_res_apply M.val.presheaf
    (eqToHom (sourceOpen_eq_image X U V B).symm) p _ m

set_option backward.isDefEq.respectTransparency.types false in
/-- All whole native Over maps retain their section square. -/
theorem localOverSectionIso_naturality (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    {Q Q' : SheafOfModules.{0} ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)}
    (f : Q ⟶ Q') (B : Opens (TopCat.of (ambientOpen X U V))) :
    (ModuleCat.restrictScalars (localOverRingSectionEquiv X U V B).symm.toRingHom).map
        (((localOverTransport X U V).map f).val.app (op B)) ≫
          (localOverSectionIso X U V Q' B).hom =
      (localOverSectionIso X U V Q B).hom ≫ f.val.app (op (sourceObject X U V B)) := by
  ext m
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every section restriction is the original native restriction. -/
theorem localOverSectionIso_restrict (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (Q : SheafOfModules.{0} ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    {B C : Opens (TopCat.of (ambientOpen X U V))} (f : C ⟶ B)
    (m : ((localOverTransport X U V).obj Q).val.obj (op B)) :
    (localOverSectionIso X U V Q C).hom
        (((localOverTransport X U V).obj Q).val.map f.op m) =
      Q.val.map (((localSiteEquivalence X U V).inverse.map
        ((ambientOpen X U V).overEquivalence.inverse.map f)).op)
          ((localOverSectionIso X U V Q B).hom m) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar action is the actual original counit scalar action. -/
theorem localOverSectionIso_smul (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (Q : SheafOfModules.{0} ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    (B : Opens (TopCat.of (ambientOpen X U V)))
    (r : (X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.obj (op B))
    (m : ((localOverTransport X U V).obj Q).val.obj (op B)) :
    (localOverSectionIso X U V Q B).hom (r • m) =
      localOverRingSectionEquiv X U V B r • (localOverSectionIso X U V Q B).hom m := by
  have h := (localOverSectionIso X U V Q B).hom.hom.map_smul
    (localOverRingSectionEquiv X U V B r) m
  change (localOverSectionIso X U V Q B).hom
      ((localOverRingSectionEquiv X U V B).symm
        (localOverRingSectionEquiv X U V B r) • m) =
    localOverRingSectionEquiv X U V B r • (localOverSectionIso X U V Q B).hom m at h
  simpa only [RingEquiv.symm_apply_apply] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse section map retains the same original inverse scalar action. -/
theorem localOverSectionIso_inv_smul (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (Q : SheafOfModules.{0} ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    (B : Opens (TopCat.of (ambientOpen X U V)))
    (r : ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V).obj.obj
      (op (sourceObject X U V B)))
    (m : Q.val.obj (op (sourceObject X U V B))) :
    (localOverSectionIso X U V Q B).inv (r • m) =
      (localOverRingSectionEquiv X U V B).symm r •
        (localOverSectionIso X U V Q B).inv m :=
  (localOverSectionIso X U V Q B).inv.hom.map_smul r m

set_option backward.isDefEq.respectTransparency.types false in
private theorem underlyingStalkIso_smul (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V)
    (r : ↑(TopCat.Presheaf.stalk
      (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪.obj
      (originalPoint X U V p hpV)))
    (m : (nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
      (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V))) :
    (underlyingStalkIso X U V M p hpV).hom (r • m) =
      (show ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) from
        localOverRingStalkEquiv X U V p hpV r) •
        (show (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M from
          (underlyingStalkIso X U V M p hpV).hom m) := by
  let TM := (localOverTransport X U V).obj (M.over V)
  let RY := (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
  obtain ⟨B,hpB,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq TM.val.presheaf m
  obtain ⟨C,hCB,hpC,r,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq RY.obj r hpB
  let mC : TM.val.obj (op C) := TM.val.map (homOfLE hCB).op m
  have hm : TopCat.Presheaf.germ TM.val.presheaf C
      (originalPoint X U V p hpV) hpC mC =
    TopCat.Presheaf.germ TM.val.presheaf B (originalPoint X U V p hpV) hpB m :=
    TopCat.Presheaf.germ_res_apply TM.val.presheaf (homOfLE hCB)
      (originalPoint X U V p hpV) hpC m
  erw [← hm]
  have hsmul := TM.val.germ_smul (R := RY.obj)
    (originalPoint X U V p hpV) C hpC r mC
  erw [← hsmul]
  erw [underlyingStalkIso_hom_germ X U V M p hpV C hpC (r • mC)]
  erw [underlyingStalkIso_hom_germ X U V M p hpV C hpC mC]
  erw [localOverRingStalkEquiv_germ X U V p hpV C hpC r]
  have hgamma := localOverSectionIso_smul X U V (M.over V) C r mC
  exact (congrArg (TopCat.Presheaf.germ M.val.presheaf (sourceObject X U V C).left
    p (originalPoint_mem_source X U V p hpV C hpC)) hgamma).trans
      (M.val.germ_smul (R := (X.restrict U.isOpenEmbedding).𝒪.obj) p
        (sourceObject X U V C).left (originalPoint_mem_source X U V p hpV C hpC)
        (localOverRingSectionEquiv X U V C r)
        ((localOverSectionIso X U V (M.over V) C).hom mC))

set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME original module stalk, with the actual native restriction scalar action. -/
def localOverModuleStalkIso (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) :
    (ModuleCat.restrictScalars (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).obj
      ((nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
        (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V))) ≅
      (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M := by
  let a := ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p)
  let G : ModuleCat a :=
    (ModuleCat.restrictScalars (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).obj
      ((nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
        (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V)))
  let H : ModuleCat a := (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M
  change G ≅ H
  letI : Module a G := G.isModule
  letI : Module a H := H.isModule
  let f : G ⟶ H := ModuleCat.ofHom (R := a) (X := G) (Y := H) {
    toFun := fun m => (underlyingStalkIso X U V M p hpV).hom m
    map_add' := (underlyingStalkIso X U V M p hpV).addCommGroupIsoToAddEquiv.map_add'
    map_smul' := by
      intro r m
      change (underlyingStalkIso X U V M p hpV).hom
          ((localOverRingStalkEquiv X U V p hpV).symm r • m) =
        r • (show H from (underlyingStalkIso X U V M p hpV).hom m)
      have h := underlyingStalkIso_smul X U V M p hpV
        ((localOverRingStalkEquiv X U V p hpV).symm r) m
      erw [(localOverRingStalkEquiv X U V p hpV).apply_symm_apply r] at h
      exact h }
  have hf : Function.Bijective f := by
    change Function.Bijective (fun m => (underlyingStalkIso X U V M p hpV).hom m)
    exact ConcreteCategory.bijective_of_isIso (underlyingStalkIso X U V M p hpV).hom
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  exact asIso f

set_option backward.isDefEq.respectTransparency.types false in
private theorem rho_hom_apply (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V)
    (m : (nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
      (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V))) :
    (localOverModuleStalkIso X U V M p hpV).hom m =
      (underlyingStalkIso X U V M p hpV).hom m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY section germ has its original native module-stalk value. -/
theorem localOverModuleStalkIso_hom_germ (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) (B : Opens (TopCat.of (ambientOpen X U V)))
    (hpB : originalPoint X U V p hpV ∈ B)
    (m : ((localOverTransport X U V).obj (M.over V)).val.obj (op B)) :
    (localOverModuleStalkIso X U V M p hpV).hom
      (TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
        B (originalPoint X U V p hpV) hpB m) =
    TopCat.Presheaf.germ M.val.presheaf (sourceObject X U V B).left p
      (originalPoint_mem_source X U V p hpV B hpB)
      ((localOverSectionIso X U V (M.over V) B).hom m) := by
  erw [rho_hom_apply X U V M p hpV]
  exact underlyingStalkIso_hom_germ X U V M p hpV B hpB m

private abbrev inverseSourceObject (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V H : Opens (TopCat.of U)) : Over V :=
  Over.mk (homOfLE (inf_le_right : H ⊓ V ≤ V))

private abbrev inverseTargetOpen (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V H : Opens (TopCat.of U)) : Opens (TopCat.of (ambientOpen X U V)) :=
  (ambientOpen X U V).overEquivalence.functor.obj
    ((localSiteEquivalence X U V).functor.obj (inverseSourceObject X U V H))

private def inverseSourceIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V H : Opens (TopCat.of U)) :
    sourceObject X U V (inverseTargetOpen X U V H) ≅ inverseSourceObject X U V H :=
  (localSiteEquivalence X U V).inverse.mapIso
      ((ambientOpen X U V).overEquivalence.unitIso.app
        ((localSiteEquivalence X U V).functor.obj (inverseSourceObject X U V H))).symm ≪≫
    ((localSiteEquivalence X U V).unitIso.app (inverseSourceObject X U V H)).symm

private theorem originalPoint_mem_inverseTargetOpen (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V H : Opens (TopCat.of U))
    (p : U) (hpV : p ∈ V) (hpH : p ∈ H) :
    originalPoint X U V p hpV ∈ inverseTargetOpen X U V H := by
  change p.val ∈ Subtype.val '' ((H ⊓ V : Opens (TopCat.of U)) : Set U)
  exact ⟨p,⟨hpH,hpV⟩,rfl⟩

/-- The inverse formula uses EVERY original neighborhood, the literal intersection,
    and precisely the two original site units. -/
theorem localOverRingStalkEquiv_symm_germ (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (p : U) (hpV : p ∈ V) (H : Opens (TopCat.of U)) (hpH : p ∈ H)
    (r : (X.restrict U.isOpenEmbedding).presheaf.obj (op H)) :
    (localOverRingStalkEquiv X U V p hpV).symm
        ((X.restrict U.isOpenEmbedding).presheaf.germ H p hpH r) =
      (X.restrict (ambientOpen X U V).isOpenEmbedding).presheaf.germ
        (inverseTargetOpen X U V H) (originalPoint X U V p hpV)
        (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH)
        ((localOverRingSectionEquiv X U V (inverseTargetOpen X U V H)).symm
          ((X.restrict U.isOpenEmbedding).presheaf.map
            ((Over.forget V).mapIso (inverseSourceIso X U V H)).hom.op
              ((X.restrict U.isOpenEmbedding).presheaf.map
                (homOfLE (inf_le_left : H ⊓ V ≤ H)).op r))) := by
  apply (localOverRingStalkEquiv X U V p hpV).injective
  erw [(localOverRingStalkEquiv X U V p hpV).apply_symm_apply]
  erw [localOverRingStalkEquiv_germ X U V p hpV (inverseTargetOpen X U V H)
    (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH)]
  erw [(localOverRingSectionEquiv X U V (inverseTargetOpen X U V H)).apply_symm_apply]
  exact ((TopCat.Presheaf.germ_res_apply (X.restrict U.isOpenEmbedding).presheaf
      ((Over.forget V).mapIso (inverseSourceIso X U V H)).hom p
      (originalPoint_mem_source X U V p hpV (inverseTargetOpen X U V H)
        (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH))
      ((X.restrict U.isOpenEmbedding).presheaf.map
        (homOfLE (inf_le_left : H ⊓ V ≤ H)).op r)).trans
    (TopCat.Presheaf.germ_res_apply (X.restrict U.isOpenEmbedding).presheaf
      (homOfLE (inf_le_left : H ⊓ V ≤ H)) p ⟨hpH,hpV⟩ r)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY original module germ has the inverse value on the literal intersection. -/
theorem localOverModuleStalkIso_inv_germ (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V) (H : Opens (TopCat.of U)) (hpH : p ∈ H)
    (m : M.val.obj (op H)) :
    (localOverModuleStalkIso X U V M p hpV).inv
        (TopCat.Presheaf.germ M.val.presheaf H p hpH m) =
      TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
        (inverseTargetOpen X U V H) (originalPoint X U V p hpV)
        (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH)
        ((localOverSectionIso X U V (M.over V) (inverseTargetOpen X U V H)).inv
          (M.val.map ((Over.forget V).mapIso (inverseSourceIso X U V H)).hom.op
            (M.val.map (homOfLE (inf_le_left : H ⊓ V ≤ H)).op m))) := by
  apply (ConcreteCategory.bijective_of_isIso
    (localOverModuleStalkIso X U V M p hpV).hom).injective
  erw [Iso.inv_hom_id_apply]
  erw [localOverModuleStalkIso_hom_germ X U V M p hpV (inverseTargetOpen X U V H)
    (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH)]
  erw [Iso.inv_hom_id_apply]
  exact ((TopCat.Presheaf.germ_res_apply M.val.presheaf
      ((Over.forget V).mapIso (inverseSourceIso X U V H)).hom p
      (originalPoint_mem_source X U V p hpV (inverseTargetOpen X U V H)
        (originalPoint_mem_inverseTargetOpen X U V H p hpV hpH))
      (M.val.map (homOfLE (inf_le_left : H ⊓ V ≤ H)).op m)).trans
    (TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE (inf_le_left : H ⊓ V ≤ H)) p ⟨hpH,hpV⟩ m)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The full original forward scalar action, before restriction of scalars. -/
theorem localOverModuleStalkIso_smul (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V)
    (r : ↑(TopCat.Presheaf.stalk
      (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪.obj
      (originalPoint X U V p hpV)))
    (m : (nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
      (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V))) :
    (localOverModuleStalkIso X U V M p hpV).hom (r • m) =
      (show ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p) from
        localOverRingStalkEquiv X U V p hpV r) •
        (localOverModuleStalkIso X U V M p hpV).hom m := by
  erw [rho_hom_apply X U V M p hpV (r • m),rho_hom_apply X U V M p hpV m]
  exact underlyingStalkIso_smul X U V M p hpV r m

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse uses the SAME original inverse scalar map. -/
theorem localOverModuleStalkIso_inv_smul (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    (p : U) (hpV : p ∈ V)
    (r : ↑(TopCat.Presheaf.stalk (X.restrict U.isOpenEmbedding).𝒪.obj p))
    (m : (nativeStalkFunctor (X.restrict U.isOpenEmbedding).𝒪 p).obj M) :
    (localOverModuleStalkIso X U V M p hpV).inv (r • m) =
      (show ↑(TopCat.Presheaf.stalk
        (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪.obj
        (originalPoint X U V p hpV)) from
          (localOverRingStalkEquiv X U V p hpV).symm r) •
        (show (nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
          (originalPoint X U V p hpV)).obj ((localOverTransport X U V).obj (M.over V)) from
          (localOverModuleStalkIso X U V M p hpV).inv m) :=
  (localOverModuleStalkIso X U V M p hpV).inv.hom.map_smul r m

set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY whole map on the actual Over site has its original native stalk square. -/
theorem localOverModuleStalkIso_naturality (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    {M N : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪)}
    (f : M.over V ⟶ N.over V) (p : U) (hpV : p ∈ V) :
    (ModuleCat.restrictScalars (localOverRingStalkEquiv X U V p hpV).symm.toRingHom).map
        ((nativeStalkFunctor (X.restrict (ambientOpen X U V).isOpenEmbedding).𝒪
          (originalPoint X U V p hpV)).map ((localOverTransport X U V).map f)) ≫
        (localOverModuleStalkIso X U V N p hpV).hom =
      (localOverModuleStalkIso X U V M p hpV).hom ≫
        ModuleCat.ofHom (stalkLinearMapOfOver (X.restrict U.isOpenEmbedding).𝒪
          V f p hpV) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  obtain ⟨B,hpB,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((localOverTransport X U V).obj (M.over V)).val.presheaf m
  change (localOverModuleStalkIso X U V N p hpV).hom
      (stalkLinearMap ((localOverTransport X U V).map f).val
        (originalPoint X U V p hpV)
        (TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
          B (originalPoint X U V p hpV) hpB m)) =
    stalkLinearMapOfOver (X.restrict U.isOpenEmbedding).𝒪 V f p hpV
      ((localOverModuleStalkIso X U V M p hpV).hom
        (TopCat.Presheaf.germ ((localOverTransport X U V).obj (M.over V)).val.presheaf
          B (originalPoint X U V p hpV) hpB m))
  erw [stalkLinearMap_germ ((localOverTransport X U V).map f).val
    (originalPoint X U V p hpV) B hpB m]
  erw [localOverModuleStalkIso_hom_germ X U V N p hpV B hpB
    (((localOverTransport X U V).map f).val.app (op B) m)]
  erw [localOverModuleStalkIso_hom_germ X U V M p hpV B hpB m]
  erw [stalkLinearMapOfOver_germ_of_le (X.restrict U.isOpenEmbedding).𝒪
    V f p hpV (sourceObject X U V B).left
    (originalPoint_mem_source X U V p hpV B hpB) (sourceObject X U V B).hom.le
    ((localOverSectionIso X U V (M.over V) B).hom m)]
  rfl

end Hironaka.HironakaChowNativeLocalOverStalkTransport
