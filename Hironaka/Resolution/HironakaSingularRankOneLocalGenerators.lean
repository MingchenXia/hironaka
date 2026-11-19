import Hironaka.Resolution.HironakaSingularLocallyFreeStalk
import Mathlib.Topology.Sheaves.Over
import Mathlib.Geometry.RingedSpace.Stalks

/-! Actual regular generating sections produce native local-free rank-one data.
All scalar actions, original stalks, module categories and over sites are native.
Blueprint: hironaka-singular-rank-one-local-generators.tex. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaSingularRankOneLocalGenerators

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk

universe u
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M N : SheafOfModules.{u} (forgetRing R)}

private def sectionOver (U : Opens X) (s : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map V.unop.hom.op s) (by
      intro V W f
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op s) =
        M.val.map W.unop.hom.op s
      rw [← M.val.map_comp_apply]
      congr 1)

/-- The native actual local multiplication morphism from a genuine original section. -/
def localUnitMap (U : Opens X) (s : M.val.obj (op U)) :
    SheafOfModules.unit ((forgetRing R).over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm (sectionOver R U s)

@[simp] theorem localUnitMap_app (U : Opens X) (s : M.val.obj (op U))
    (V : Over U) (r : (forgetRing R).obj.obj (op V.left)) :
    (localUnitMap R U s).val.app (op V) r = r • M.val.map V.hom.op s := rfl

private def restrictedStalkIso (M : SheafOfModules.{u} (forgetRing R))
    (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj
        ((SheafOfModules.toSheaf _).obj (M.over U))).obj x ≅
      TopCat.Presheaf.stalk M.val.presheaf x.val :=
  PresheafedSpace.restrictStalkIso
    (PresheafedSpace.mk X M.val.presheaf) U.isOpenEmbedding x

private theorem restrictedStalk_square (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : U) (m : ↑(TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (M.over U))).obj x)) :
    (restrictedStalkIso R N U x).hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := TopCat.of U) x).map
        ((U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)).hom m) =
      stalkLinearMapOfOver R U f x.val x.property ((restrictedStalkIso R M U x).hom m) := by
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

private theorem overIso_of_original_stalk_bijective (U : Opens X)
    (f : M.over U ⟶ N.over U)
    (hf : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      (stalkLinearMapOfOver R U f x hx)) : IsIso f := by
  let g := (U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)
  have (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (X := TopCat.of U) x).map g.hom) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro a b hab
      apply (ConcreteCategory.bijective_of_isIso (restrictedStalkIso R M U x).hom).1
      apply (hf x.val x.property).1
      rw [← restrictedStalk_square, ← restrictedStalk_square, hab]
    · intro b
      obtain ⟨a,ha⟩ := (hf x.val x.property).2 ((restrictedStalkIso R N U x).hom b)
      obtain ⟨c,hc⟩ := (ConcreteCategory.bijective_of_isIso
        (restrictedStalkIso R M U x).hom).2 a
      refine ⟨c,?_⟩
      apply (ConcreteCategory.bijective_of_isIso (restrictedStalkIso R N U x).hom).1
      rw [restrictedStalk_square, hc, ha]
  have : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    (C := AddCommGrpCat.{u}) (X := TopCat.of U) g
  have : IsIso ((SheafOfModules.toSheaf _).map f) :=
    isIso_of_reflects_iso _ U.sheafEquivOver.functor
  -- Reflection through the native module components, on the actual over site.
  let e : (M.over U).val ≅ (N.over U).val := PresheafOfModules.isoMk
    (fun V => (LinearEquiv.ofBijective (f.val.app V).hom
      (ConcreteCategory.bijective_of_isIso
        (((SheafOfModules.toSheaf _).map f).hom.app V))).toModuleIso)
    (by intro V W h; exact f.val.naturality h)
  have he : f.val = e.hom := rfl
  have : IsIso ((SheafOfModules.forget _).map f) := by
    change IsIso f.val
    rw [he]
    infer_instance
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/-- The actual local multiplication map acts on the SAME original stalks. -/
theorem localUnitMap_stalk (U : Opens X) (s : M.val.obj (op U))
    (x : X) (hx : x ∈ U) (r : ↑(TopCat.Presheaf.stalk R.obj x)) :
    stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R)) U (localUnitMap R U s) x hx
      ((unitStalkLinearEquiv R x).symm r) =
        r • TopCat.Presheaf.germ M.val.presheaf U x hx s := by
  obtain ⟨V,hVU,hxV,r,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R.obj r hx
  rw [← unitStalkLinearEquiv_germ R x V hxV r, LinearEquiv.symm_apply_apply,
    stalkLinearMapOfOver_germ_of_le R U _ x hx V hxV hVU]
  erw [localUnitMap_app,unitStalkLinearEquiv_germ R x V hxV r,
    M.val.germ_smul (R := R.obj),TopCat.Presheaf.germ_res_apply]

/-- Regularity and ENTIRE original inclusion-image generation produce a real local isomorphism. -/
theorem localUnitMap_isIso (f : M ⟶ SheafOfModules.unit (forgetRing R))
    (hf : ∀ V : Opens X, Function.Injective (f.val.app (op V)))
    (U : Opens X) (s : M.val.obj (op U))
    (hreg : ∀ (x : X) (hx : x ∈ U),
      IsRegular (TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)))
    (hspan : ∀ (x : X) (hx : x ∈ U),
      LinearMap.range (stalkInclusionLinearMap R M f x) =
        Ideal.span {TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)}) :
    IsIso (localUnitMap R U s) := by
  apply overIso_of_original_stalk_bijective R (M := SheafOfModules.unit (forgetRing R))
  intro x hx
  let k := (stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R))
    U (localUnitMap R U s) x hx).comp (unitStalkLinearEquiv R x).symm.toLinearMap
  let a := TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)
  have hformula (r : ↑(TopCat.Presheaf.stalk R.obj x)) :
      stalkInclusionLinearMap R M f x (k r) = r * a := by
    change stalkInclusionLinearMap R M f x
      (stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R)) U (localUnitMap R U s) x hx
        ((unitStalkLinearEquiv R x).symm r)) = r * a
    rw [localUnitMap_stalk,map_smul,stalkInclusionLinearMap_germ]
    rfl
  have hk : Function.Bijective k := by
    constructor
    · intro r t hrt
      apply (hreg x hx).right
      change r * a = t * a
      rw [← hformula,← hformula,hrt]
    · intro m
      have hm : stalkInclusionLinearMap R M f x m ∈ Ideal.span {a} := by
        rw [← hspan x hx]
        exact ⟨m,rfl⟩
      obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hm
      refine ⟨r,stalkInclusionLinearMap_injective R M f hf x ?_⟩
      rw [hformula,hr,mul_comm]
  have heq : stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R)) U (localUnitMap R U s) x hx =
      k.comp (unitStalkLinearEquiv R x).toLinearMap := by
    ext m
    simp only [k,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
  rw [heq]
  exact hk.comp (unitStalkLinearEquiv R x).bijective

private def singletonGenerators (f : M ⟶ SheafOfModules.unit (forgetRing R))
    (hf : ∀ V : Opens X, Function.Injective (f.val.app (op V)))
    (U : Opens X) (s : M.val.obj (op U))
    (hreg : ∀ (x : X) (hx : x ∈ U),
      IsRegular (TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)))
    (hspan : ∀ (x : X) (hx : x ∈ U),
      LinearMap.range (stalkInclusionLinearMap R M f x) =
        Ideal.span {TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)}) :
    (M.over U).GeneratingSections := by
  have : IsIso (localUnitMap R U s) := localUnitMap_isIso R f hf U s hreg hspan
  let e : SheafOfModules.free (R := (forgetRing R).over U) PUnit ≅ M.over U :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit ((forgetRing R).over U)) ≪≫
      asIso (localUnitMap R U s)
  exact (SheafOfModules.free.generatingSections PUnit).ofEpi e.hom

private theorem singletonGenerators_isIso (f : M ⟶ SheafOfModules.unit (forgetRing R))
    (hf : ∀ V : Opens X, Function.Injective (f.val.app (op V)))
    (U : Opens X) (s : M.val.obj (op U))
    (hreg : ∀ (x : X) (hx : x ∈ U),
      IsRegular (TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)))
    (hspan : ∀ (x : X) (hx : x ∈ U),
      LinearMap.range (stalkInclusionLinearMap R M f x) =
        Ideal.span {TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) s)}) :
    IsIso (singletonGenerators R f hf U s hreg hspan).π := by
  dsimp only [singletonGenerators]
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  infer_instance

variable {I : Type u} (f : M ⟶ SheafOfModules.unit (forgetRing R))
  (hf : ∀ V : Opens X, Function.Injective (f.val.app (op V)))
  (U : I → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
  (s : ∀ i, M.val.obj (op (U i)))
  (hreg : ∀ i (x : X) (hx : x ∈ U i),
    IsRegular (TopCat.Presheaf.germ R.obj (U i) x hx (f.val.app (op (U i)) (s i))))
  (hspan : ∀ i (x : X) (hx : x ∈ U i),
    LinearMap.range (stalkInclusionLinearMap R M f x) =
      Ideal.span {TopCat.Presheaf.germ R.obj (U i) x hx (f.val.app (op (U i)) (s i))})

/-- Actual original opens/sections supply the GENUINE native local-generators data. -/
def localGeneratorsData : M.LocalGeneratorsData where
  I := I
  X := U
  coversTop V := by
    apply (Opens.mem_grothendieckTopology X).mpr
    intro x hx
    obtain ⟨i,hi⟩ := hcover x
    refine ⟨V ⊓ U i,homOfLE inf_le_left,?_,⟨hx,hi⟩⟩
    exact (Sieve.mem_ofObjects_iff U _).mpr ⟨i,⟨homOfLE inf_le_right⟩⟩
  generators i := singletonGenerators R f hf (U i) (s i) (hreg i) (hspan i)

/-- Each ORIGINAL generating morphism is an actual native isomorphism. -/
instance localGeneratorsData_isLocallyFree :
    (localGeneratorsData R f hf U hcover s hreg hspan).IsLocallyFreeData where
  isIso i := singletonGenerators_isIso R f hf (U i) (s i) (hreg i) (hspan i)

/-- Each ORIGINAL generator index is literally the singleton, not a rank certificate. -/
instance localGeneratorsData_unique (i : I) :
    Unique ((localGeneratorsData R f hf U hcover s hreg hspan).generators i).I :=
  inferInstanceAs (Unique PUnit)

include f hf U hcover s hreg hspan in
/-- No local isomorphism, stalk invertibility or native q is assumed. -/
theorem exists_locallyFreeData_of_regular_sections :
    ∃ q : M.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
      ∀ i, Nonempty (Unique (q.generators i).I) := by
  exact ⟨localGeneratorsData R f hf U hcover s hreg hspan,inferInstance,
    fun _ => ⟨inferInstance⟩⟩

end Hironaka.HironakaSingularRankOneLocalGenerators
