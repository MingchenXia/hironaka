import Hironaka.Resolution.HironakaChowNativeFiniteFreeStalk
import Hironaka.Resolution.HironakaChowNativeModuleStalkExact
import Hironaka.Resolution.HironakaChowNativeSectionSpreading
import Hironaka.Resolution.HironakaSingularRankOneLocalGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! Native original over-site morphisms, generator images and finite-presentation
spreading. Blueprint: `hironaka-g10-native-finite-presentation-spreading.tex`.
All module categories, actions, free sheaves and restrictions are native. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaChowNativeFinitePresentationSpreading

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaSingularRankOneLocalGenerators HironakaChowNativeFiniteFreeStalk
  HironakaChowNativeModuleStalkExact HironakaChowNativeSectionSpreading

universe u
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M N : SheafOfModules.{u} (forgetRing R)}

/-- Forward the native over-site adjunction through the native restriction expression. -/
instance overFunctor_isLeftAdjoint (U : Opens X) :
    (SheafOfModules.overFunctor (forgetRing R) U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := forgetRing R) U).isLeftAdjoint

/-- Restricting a global original morphism acts on the SAME original stalks. -/
theorem stalkLinearMapOfOver_homOver (f : M ⟶ N) (U : Opens X)
    (x : X) (hxU : x ∈ U) :
    stalkLinearMapOfOver R U (f.over U) x hxU = stalkLinearMap f.val x := by
  ext m
  obtain ⟨V,hVU,hxV,m,rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxU
  erw [stalkLinearMapOfOver_germ_of_le R U _ x hxU V hxV hVU,
    stalkLinearMap_germ]
  rfl

/-- The native restriction of the original free sheaf keeps the SAME original index. -/
def freeOverIso (U : Opens X) (I : Type u) :
    SheafOfModules.free (R := (forgetRing R).over U) I ≅
      (SheafOfModules.free (R := forgetRing R) I).over U :=
  SheafOfModules.mapFreeIso (SheafOfModules.overFunctor (forgetRing R) U) I (Iso.refl _)

private theorem freeOverIso_ι (U : Opens X) {I : Type u} (i : I) :
    SheafOfModules.ιFree i ≫ (freeOverIso R U I).hom =
      (SheafOfModules.ιFree (R := forgetRing R) i).over U := by
  simpa only [freeOverIso, Iso.refl_hom, Category.id_comp] using
    SheafOfModules.ιFree_mapFreeIso_hom
      (SheafOfModules.overFunctor (forgetRing R) U) I (Iso.refl _) i

/-- Actual original sections on one open define a WHOLE native free-module morphism. -/
def freeOverMap (U : Opens X) {I : Type u} (s : I → M.val.obj (op U)) :
    (SheafOfModules.free (R := forgetRing R) I).over U ⟶ M.over U :=
  (freeOverIso R U I).inv ≫ (M.over U).freeHomEquiv.symm
    (fun i => (M.over U).unitHomEquiv (localUnitMap R U (s i)))

/-- Every original free inclusion has the stated actual original section image. -/
theorem ι_freeOverMap (U : Opens X) {I : Type u}
    (s : I → M.val.obj (op U)) (i : I) :
    (SheafOfModules.ιFree (R := forgetRing R) i).over U ≫ freeOverMap R U s =
      localUnitMap R U (s i) := by
  rw [← freeOverIso_ι R U i, freeOverMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The actual free morphism has the stated images on the SAME original stalk inclusions. -/
theorem freeOverMap_stalk_ι (U : Opens X) {I : Type u}
    (s : I → M.val.obj (op U)) (x : X) (hxU : x ∈ U) (i : I)
    (a : ↑(TopCat.Presheaf.stalk R.obj x)) :
    stalkLinearMapOfOver R U (freeOverMap R U s) x hxU
      (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
        ((unitStalkLinearEquiv R x).symm a)) =
      a • TopCat.Presheaf.germ M.val.presheaf U x hxU (s i) := by
  have h := congrArg (fun f : (SheafOfModules.unit (forgetRing R)).over U ⟶ M.over U =>
    stalkLinearMapOfOver R U f x hxU) (ι_freeOverMap R U s i)
  rw [stalkLinearMapOfOver_comp, stalkLinearMapOfOver_homOver] at h
  have hh := LinearMap.congr_fun h ((unitStalkLinearEquiv R x).symm a)
  simpa only [LinearMap.comp_apply, localUnitMap_stalk] using hh

/-- An arbitrary linear map on the ORIGINAL finite free stalk has an actual local lift. -/
theorem exists_free_local_lift {I : Type u} [Finite I]
    (x : X) (U : Opens X) (hxU : x ∈ U)
    (φ : ↑(TopCat.Presheaf.stalk (SheafOfModules.free (R := forgetRing R) I).val.presheaf x)
      →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V)
      (F : (SheafOfModules.free (R := forgetRing R) I).over V ⟶ N.over V),
      stalkLinearMapOfOver R V F x hxV = φ := by
  classical
  let := Fintype.ofFinite I
  let e := finiteFreeStalkLinearEquiv R I x
  let a (i : I) := φ (e.symm (Pi.single i 1))
  obtain ⟨V,hVU,hxV,s,hs⟩ := exists_common_germ_representatives N.val x U hxU a
  refine ⟨V,hVU,hxV,freeOverMap R V s,?_⟩
  have h : (stalkLinearMapOfOver R V (freeOverMap R V s) x hxV).comp e.symm.toLinearMap =
      φ.comp e.symm.toLinearMap := by
    apply (Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) I).ext
    intro i
    change stalkLinearMapOfOver R V (freeOverMap R V s) x hxV
      (e.symm (Pi.single i 1)) = a i
    have he : e.symm (Pi.single i 1) =
        stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
          ((unitStalkLinearEquiv R x).symm 1) :=
      e.symm_apply_eq.mpr (finiteFreeStalkLinearEquiv_ι R I x i 1).symm
    rw [he,freeOverMap_stalk_ι,one_smul]
    exact hs i
  ext m
  have hm := LinearMap.congr_fun h (e m)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
    using hm

/-- Shrink an actual original over-site morphism by the native over-map functor. -/
def restrictOverHom (U V : Opens X) (hVU : V ≤ U) (f : M.over U ⟶ N.over U) :
    M.over V ⟶ N.over V :=
  ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app M).inv ≫
    (SheafOfModules.overMap (forgetRing R) (homOfLE hVU)).map f ≫
      ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app N).hom

private theorem restrictOverHom_app (U V : Opens X) (hVU : V ≤ U)
    (f : M.over U ⟶ N.over U) (W : Opens X) (hWV : W ≤ V)
    (m : M.val.obj (op W)) :
    (restrictOverHom R U V hVU f).val.app (op (Over.mk (homOfLE hWV))) m =
      f.val.app (op (Over.mk (homOfLE (hWV.trans hVU)))) m := rfl

/-- Shrinking the actual original morphism does not change its original stalk map. -/
theorem stalkLinearMapOfOver_restrictOverHom (U V : Opens X) (hVU : V ≤ U)
    (f : M.over U ⟶ N.over U) (x : X) (hxV : x ∈ V) :
    stalkLinearMapOfOver R V (restrictOverHom R U V hVU f) x hxV =
      stalkLinearMapOfOver R U f x (hVU hxV) := by
  ext m
  obtain ⟨W,hWV,hxW,m,rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxV
  erw [stalkLinearMapOfOver_germ_of_le R V _ x hxV W hxW hWV,
    stalkLinearMapOfOver_germ_of_le R U _ x (hVU hxV) W hxW (hWV.trans hVU)]
  rfl

private theorem restrictOverHom_zero (U V : Opens X) (hVU : V ≤ U) :
    restrictOverHom R U V hVU (0 : M.over U ⟶ N.over U) = 0 := by
  ext W m
  rfl

private theorem restrictOverHom_comp {P : SheafOfModules.{u} (forgetRing R)}
    (U V : Opens X) (hVU : V ≤ U) (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) :
    restrictOverHom R U V hVU (f ≫ g) =
      restrictOverHom R U V hVU f ≫ restrictOverHom R U V hVU g := by
  ext W m
  rfl

private theorem restrictOverHom_trans (U V W : Opens X) (hVU : V ≤ U) (hWV : W ≤ V)
    (f : M.over U ⟶ N.over U) :
    restrictOverHom R V W hWV (restrictOverHom R U V hVU f) =
      restrictOverHom R U W (hWV.trans hVU) f := by
  ext T m
  rfl

private theorem stalkLinearMapOfOver_zero (U : Opens X) (x : X) (hxU : x ∈ U) :
    stalkLinearMapOfOver R U (0 : M.over U ⟶ N.over U) x hxU = 0 := by
  change stalkLinearMapOfOver R U ((0 : M ⟶ N).over U) x hxU = 0
  rw [stalkLinearMapOfOver_homOver]
  exact stalkLinearMap_zero x

private def restrictOverIsColimit {P : SheafOfModules.{u} (forgetRing R)}
    (U V : Opens X) (hVU : V ≤ U) (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U)
    (h : f ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g h)) :
    IsColimit (CokernelCofork.ofπ (restrictOverHom R U V hVU g)
      (f := restrictOverHom R U V hVU f)
      (by rw [← restrictOverHom_comp,h,restrictOverHom_zero])) := by
  let F := SheafOfModules.overMap (forgetRing R) (homOfLE hVU)
  refine IsCokernel.ofIso _
    (CokernelCofork.mapIsColimit (CokernelCofork.ofπ g h) hc F) _
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app M)
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app N)
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app P) ?_ ?_
  · simp only [restrictOverHom,Iso.hom_inv_id_assoc,F]
  · simp only [CokernelCofork.π_ofπ,CokernelCofork.map_π,restrictOverHom,
      Iso.hom_inv_id_assoc,F]

private def presentationGenerators (U : Opens X) (P : (M.over U).Presentation) :
    (SheafOfModules.free (R := forgetRing R) P.generators.I).over U ⟶ M.over U :=
  (freeOverIso R U P.generators.I).inv ≫ P.generators.π

private def presentationRelations (U : Opens X) (P : (M.over U).Presentation) :
    (SheafOfModules.free (R := forgetRing R) P.relations.I).over U ⟶
      (SheafOfModules.free (R := forgetRing R) P.generators.I).over U :=
  (freeOverIso R U P.relations.I).inv ≫
    ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι _) ≫
      (freeOverIso R U P.generators.I).hom

private theorem presentationRelations_generators (U : Opens X) (P : (M.over U).Presentation) :
    presentationRelations R U P ≫ presentationGenerators R U P = 0 := by
  simp only [presentationRelations,presentationGenerators,Category.assoc,Iso.hom_inv_id_assoc,
    kernel.condition,comp_zero]

private def originalPresentationIsColimit (U : Opens X) (P : (M.over U).Presentation) :
    IsColimit (CokernelCofork.ofπ (presentationGenerators R U P)
      (presentationRelations_generators R U P)) := by
  refine IsCokernel.ofIso _ P.isColimit _
    (freeOverIso R U P.relations.I) (freeOverIso R U P.generators.I) (Iso.refl _) ?_ ?_
  · simp only [presentationRelations,Category.assoc,Iso.hom_inv_id_assoc]
  · simp only [CokernelCofork.π_ofπ,presentationGenerators,Iso.hom_inv_id_assoc,
      Iso.refl_hom,Category.comp_id]

private def originalOpenStalkIso (M : SheafOfModules.{u} (forgetRing R))
    (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj
        ((SheafOfModules.toSheaf _).obj (M.over U))).obj x ≅
      TopCat.Presheaf.stalk M.val.presheaf x.val :=
  PresheafedSpace.restrictStalkIso
    (PresheafedSpace.mk X M.val.presheaf) U.isOpenEmbedding x

private theorem originalOpenStalk_square (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : U) (m : ↑(TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (M.over U))).obj x)) :
    (originalOpenStalkIso R N U x).hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := TopCat.of U) x).map
        ((U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)).hom m) =
      stalkLinearMapOfOver R U f x.val x.property ((originalOpenStalkIso R M U x).hom m) := by
  obtain ⟨V,hxV,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of U)
    ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (M.over U))).obj m
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (PresheafedSpace.mk X N.val.presheaf) U.isOpenEmbedding V x hxV,
    PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
      (PresheafedSpace.mk X M.val.presheaf) U.isOpenEmbedding V x hxV]
  erw [stalkLinearMapOfOver_germ_of_le R U f x.val x.property
    (U.isOpenEmbedding.functor.obj V) _ (by rintro y ⟨z,hz,rfl⟩; exact z.property)]
  rfl

/-- A genuine epimorphism on the original open is onto the SAME original module stalk. -/
theorem stalkLinearMapOfOver_surjective_of_epi (U : Opens X)
    (f : M.over U ⟶ N.over U) [Epi f] (x : X) (hxU : x ∈ U) :
    Function.Surjective (stalkLinearMapOfOver R U f x hxU) := by
  classical
  have := underlyingSheaf_preservesFiniteColimits ((forgetRing R).over U)
  let g := (U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)
  have : Epi ((SheafOfModules.toSheaf _).map f) := Functor.map_epi _ f
  have : Epi g := Functor.map_epi U.sheafEquivOver.functor _
  let xU : U := ⟨x,hxU⟩
  let S := TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of U) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := TopCat.of U) xU
  have : S.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := TopCat.of U) xU).isLeftAdjoint
  have hsurj : Function.Surjective (S.map g) :=
    (AddCommGrpCat.epi_iff_surjective (S.map g)).mp (Functor.map_epi S g)
  intro b
  obtain ⟨b',hb'⟩ := (ConcreteCategory.bijective_of_isIso
    (originalOpenStalkIso R N U xU).hom).2 b
  obtain ⟨a,ha⟩ := hsurj b'
  refine ⟨(originalOpenStalkIso R M U xU).hom a,?_⟩
  exact (originalOpenStalk_square R U f xU a).symm.trans
    ((congrArg (fun t => (originalOpenStalkIso R N U xU).hom t) ha).trans hb')

private theorem freeOver_generator_app {I : Type u} (U : Opens X)
    (f : (SheafOfModules.free (R := forgetRing R) I).over U ⟶ N.over U)
    (i : I) (W : Opens X) (hWU : W ≤ U) :
    f.val.app (op (Over.mk (homOfLE hWU)))
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op W)) =
      N.val.map (homOfLE hWU).op
        (f.val.app (op (Over.mk (𝟙 U)))
          ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))) := by
  let j : Over.mk (homOfLE hWU) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE hWU)
  have hf := PresheafOfModules.naturality_apply f.val j.op
    ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))
  change f.val.app (op (Over.mk (homOfLE hWU)))
      ((SheafOfModules.free (R := forgetRing R) I).val.map (homOfLE hWU).op
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))) =
    N.val.map (homOfLE hWU).op
      (f.val.app (op (Over.mk (𝟙 U)))
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))) at hf
  simpa only [PresheafOfModules.sections_property] using hf

private theorem freeOverHom_ext {I : Type u} (U : Opens X)
    (f g : (SheafOfModules.free (R := forgetRing R) I).over U ⟶ N.over U)
    (h : ∀ i : I, f.val.app (op (Over.mk (𝟙 U)))
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U)) =
      g.val.app (op (Over.mk (𝟙 U)))
        ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))) : f = g := by
  apply (cancel_epi (freeOverIso R U I).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ← Category.assoc]
  erw [freeOverIso_ι]
  apply (N.over U).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro W
  change f.val.app W ((SheafOfModules.freeSection (R := forgetRing R) i).val (op W.unop.left)) =
    g.val.app W ((SheafOfModules.freeSection (R := forgetRing R) i).val (op W.unop.left))
  change f.val.app (op (Over.mk (homOfLE W.unop.hom.le)))
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op W.unop.left)) =
    g.val.app (op (Over.mk (homOfLE W.unop.hom.le)))
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op W.unop.left))
  rw [freeOver_generator_app,freeOver_generator_app,h i]

/-- For the SAME finite original free source, stalk equality yields WHOLE local morphism equality. -/
theorem exists_restrictOverHom_eq_of_free_stalk_eq {I : Type u} [Finite I]
    (U : Opens X) (f g : (SheafOfModules.free (R := forgetRing R) I).over U ⟶ N.over U)
    (x : X) (hxU : x ∈ U)
    (h : stalkLinearMapOfOver R U f x hxU = stalkLinearMapOfOver R U g x hxU) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
      restrictOverHom R U V hVU f = restrictOverHom R U V hVU g := by
  classical
  let s (i : I) := f.val.app (op (Over.mk (𝟙 U)))
    ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))
  let t (i : I) := g.val.app (op (Over.mk (𝟙 U)))
    ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U))
  have hst (i : I) : TopCat.Presheaf.germ N.val.presheaf U x hxU (s i) =
      TopCat.Presheaf.germ N.val.presheaf U x hxU (t i) := by
    have hi := LinearMap.congr_fun h (TopCat.Presheaf.germ
      (SheafOfModules.free (R := forgetRing R) I).val.presheaf U x hxU
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op U)))
    erw [stalkLinearMapOfOver_germ_of_le R U f x hxU U hxU le_rfl,
      stalkLinearMapOfOver_germ_of_le R U g x hxU U hxU le_rfl] at hi
    exact hi
  obtain ⟨V,hVU,hxV,heq⟩ :=
    exists_common_restriction_eq_of_germ_eq N.val x U hxU s t hst
  refine ⟨V,hVU,hxV,freeOverHom_ext R V _ _ ?_⟩
  intro i
  change f.val.app (op (Over.mk (homOfLE hVU)))
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op V)) =
    g.val.app (op (Over.mk (homOfLE hVU)))
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op V))
  rw [freeOver_generator_app,freeOver_generator_app]
  exact heq i

private theorem original_relation_stalk_zero {A B : SheafOfModules.{u} (forgetRing R)}
    (U V : Opens X) (hVU : V ≤ U) (r : A.over U ⟶ B.over U) (g : B.over U ⟶ M.over U)
    (hrg : r ≫ g = 0) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (φ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x))
    (f : B.over V ⟶ N.over V)
    (hf : stalkLinearMapOfOver R V f x hxV = φ.comp (stalkLinearMapOfOver R U g x hxU)) :
    stalkLinearMapOfOver R V (restrictOverHom R U V hVU r ≫ f) x hxV =
      stalkLinearMapOfOver R V (0 : A.over V ⟶ N.over V) x hxV := by
  have h0 : (stalkLinearMapOfOver R U g x hxU).comp
      (stalkLinearMapOfOver R U r x hxU) = 0 := by
    rw [← stalkLinearMapOfOver_comp,hrg,stalkLinearMapOfOver_zero]
  rw [stalkLinearMapOfOver_zero,stalkLinearMapOfOver_comp,hf,
    stalkLinearMapOfOver_restrictOverHom]
  ext a
  change φ (stalkLinearMapOfOver R U g x hxU
    (stalkLinearMapOfOver R U r x hxU a)) = 0
  have ha := LinearMap.congr_fun h0 a
  change stalkLinearMapOfOver R U g x hxU
    (stalkLinearMapOfOver R U r x hxU a) = 0 at ha
  rw [ha,map_zero]

private theorem exists_cokernel_lift_with_original_stalk
    {A B : SheafOfModules.{u} (forgetRing R)} (U V : Opens X) (hVU : V ≤ U)
    (r : A.over U ⟶ B.over U) (g : B.over U ⟶ M.over U)
    (hrg : r ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g hrg))
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (φ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x))
    (f : B.over V ⟶ N.over V)
    (hf : stalkLinearMapOfOver R V f x hxV = φ.comp (stalkLinearMapOfOver R U g x hxU))
    (hrf : restrictOverHom R U V hVU r ≫ f = 0) :
    ∃ F : M.over V ⟶ N.over V, stalkLinearMapOfOver R V F x hxV = φ := by
  let hcV := restrictOverIsColimit R U V hVU r g hrg hc
  obtain ⟨F,hF⟩ := CokernelCofork.IsColimit.desc' hcV f hrf
  change restrictOverHom R U V hVU g ≫ F = f at hF
  have : Epi (restrictOverHom R U V hVU g) := epi_of_isColimit_cofork hcV
  have hsurj := stalkLinearMapOfOver_surjective_of_epi R V
    (restrictOverHom R U V hVU g) x hxV
  refine ⟨F,?_⟩
  have hcomp : (stalkLinearMapOfOver R V F x hxV).comp
      (stalkLinearMapOfOver R U g x hxU) = φ.comp (stalkLinearMapOfOver R U g x hxU) := by
    rw [← stalkLinearMapOfOver_restrictOverHom R U V hVU g x hxV,
      ← stalkLinearMapOfOver_comp,hF,hf,stalkLinearMapOfOver_restrictOverHom]
  ext m
  obtain ⟨a,ha⟩ := hsurj m
  rw [stalkLinearMapOfOver_restrictOverHom] at ha
  have hm := LinearMap.congr_fun hcomp a
  simpa only [LinearMap.comp_apply,ha] using hm

/-- The original native finite presentation on an original open INTERNALLY lifts any given
original module-stalk map to a WHOLE morphism on one smaller original open. -/
theorem exists_local_lift_of_presentation_on_open (U : Opens X)
    (P : (M.over U).Presentation) [P.IsFinite] (x : X) (hxU : x ∈ U)
    (φ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ (V : Opens X) (_hVU : V ≤ U) (hxV : x ∈ V) (F : M.over V ⟶ N.over V),
      stalkLinearMapOfOver R V F x hxV = φ := by
  let g := presentationGenerators R U P
  let ρ := presentationRelations R U P
  have hρg : ρ ≫ g = 0 := presentationRelations_generators R U P
  have hc : IsColimit (CokernelCofork.ofπ g hρg) := originalPresentationIsColimit R U P
  obtain ⟨V,hVU,hxV,f,hf⟩ := exists_free_local_lift R x U hxU
    (φ.comp (stalkLinearMapOfOver R U g x hxU))
  have hzero := original_relation_stalk_zero R U V hVU ρ g hρg x hxU hxV φ f hf
  obtain ⟨W,hWV,hxW,hW⟩ := exists_restrictOverHom_eq_of_free_stalk_eq R V
    (restrictOverHom R U V hVU ρ ≫ f) 0 x hxV hzero
  let hWU : W ≤ U := hWV.trans hVU
  let fW := restrictOverHom R V W hWV f
  have hρf : restrictOverHom R U W hWU ρ ≫ fW = 0 := by
    simpa only [restrictOverHom_comp,restrictOverHom_trans,restrictOverHom_zero] using hW
  have hfW : stalkLinearMapOfOver R W fW x hxW =
      φ.comp (stalkLinearMapOfOver R U g x hxU) := by
    rw [stalkLinearMapOfOver_restrictOverHom]
    exact hf
  obtain ⟨F,hF⟩ := exists_cokernel_lift_with_original_stalk R U W hWU ρ g hρg hc
    x hxU hxW φ fW hfW hρf
  exact ⟨W,hWU,hxW,F,hF⟩

/-- STANDARD native finite-presentation data produces the actual whole local lift of an
arbitrary ORIGINAL stalk-linear map, with no separation or lifted-map certificate. -/
theorem exists_local_lift_of_isFinitePresentation [M.IsFinitePresentation]
    (x : X) (φ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ (U : Opens X) (hxU : x ∈ U) (F : M.over U ⟶ N.over U),
      stalkLinearMapOfOver R U F x hxU = φ := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have := hq
  obtain ⟨V,f,hV,hxV⟩ :=
    (Opens.mem_grothendieckTopology X).mp (q.coversTop ⊤) x (by trivial)
  obtain ⟨i,⟨g⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hV
  have hxU : x ∈ q.X i := g.le hxV
  obtain ⟨U,_hU,hxU,F,hF⟩ :=
    exists_local_lift_of_presentation_on_open R (q.X i) (q.presentation i) x hxU φ
  exact ⟨U,hxU,F,hF⟩

end Hironaka.HironakaChowNativeFinitePresentationSpreading
