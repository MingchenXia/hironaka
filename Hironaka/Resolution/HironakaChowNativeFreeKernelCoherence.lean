import Hironaka.Resolution.HironakaChowNativeOkaMatrixKernel
import Hironaka.Resolution.HironakaChowNativeNeighborhoodMatrix
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-! Finite presentation of the SAME actual categorical kernel of an arbitrary
native finite-free morphism. The accepted Oka producer is used twice.
Blueprint FIRST: hironaka-g10-native-free-kernel-coherence.tex. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators Manifold

namespace Hironaka.HironakaChowNativeFreeKernelCoherence

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSingularModuleSheafStalk
  HironakaSingularLocallyFreeStalk HironakaChowNativeFiniteFreeStalk
  HironakaChowNativeFinitePresentationSpreading HironakaChowNativeModuleStalkExact
  HironakaChowNativeNeighborhoodMatrix HironakaChowNativeOkaMatrixKernel

section Native
variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  {M N P : SheafOfModules.{0} (forgetRing R)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private instance overFunctor_isRightAdjointNative (U : Opens X) :
    (SheafOfModules.overFunctor.{0} (forgetRing R) U).IsRightAdjoint := by
  unfold SheafOfModules.overFunctor
  infer_instance

-- Existing original restriction-stalk plumbing, repeated only because the
-- corresponding declarations in the accepted spreading parent are private.
private def originalOpenStalkIso (M : SheafOfModules.{0} (forgetRing R))
    (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj
        ((SheafOfModules.toSheaf _).obj (M.over U))).obj x ≅
      TopCat.Presheaf.stalk M.val.presheaf x.val :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso
    (AlgebraicGeometry.PresheafedSpace.mk X M.val.presheaf) U.isOpenEmbedding x

private theorem originalOpenStalk_square (U : Opens X) (f : M.over U ⟶ N.over U)
    (x : U) (m : ↑(TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (M.over U))).obj x)) :
    (originalOpenStalkIso R N U x).hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (X := TopCat.of U) x).map
        ((U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)).hom m) =
      stalkLinearMapOfOver R U f x.val x.property ((originalOpenStalkIso R M U x).hom m) := by
  obtain ⟨V,hxV,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of U)
    ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (M.over U))).obj m
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (AlgebraicGeometry.PresheafedSpace.mk X N.val.presheaf) U.isOpenEmbedding V x hxV,
    AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
      (AlgebraicGeometry.PresheafedSpace.mk X M.val.presheaf) U.isOpenEmbedding V x hxV]
  erw [stalkLinearMapOfOver_germ_of_le R U f x.val x.property
    (U.isOpenEmbedding.functor.obj V) _ (by rintro y ⟨z,hz,rfl⟩; exact z.property)]
  rfl

private theorem epi_of_all_original_stalks (U : Opens X) (f : M.over U ⟶ N.over U)
    (hf : ∀ (x : X) (hx : x ∈ U), Function.Surjective (stalkLinearMapOfOver R U f x hx)) :
    Epi f := by
  let A := SheafOfModules.toSheaf ((forgetRing R).over U)
  let L : CategoryTheory.Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0} ⥤
      TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) := U.sheafEquivOver.functor
  let : L.IsEquivalence :=
    (U.sheafEquivOver (A := AddCommGrpCat.{0})).isEquivalence_functor
  let g := L.map (A.map f)
  have hsurj (x : U) : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (X := TopCat.of U) x).map g.hom) := by
    intro b
    let eM := originalOpenStalkIso R M U x
    let eN := originalOpenStalkIso R N U x
    obtain ⟨a,ha⟩ := hf x.val x.property (eN.hom b)
    obtain ⟨a',ha'⟩ := (ConcreteCategory.bijective_of_isIso eM.hom).2 a
    refine ⟨a',?_⟩
    apply (ConcreteCategory.bijective_of_isIso eN.hom).1
    change eN.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0}
      (X := TopCat.of U) x).map g.hom a') = _
    rw [originalOpenStalk_square]
    rw [ha',ha]
  have hg : Epi g := (TopCat.Sheaf.isLocallySurjective_iff_epi g).mp
    ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks g.hom).mpr hsurj)
  have : Epi (A.map f) := L.epi_of_epi_map hg
  exact A.epi_of_epi_map inferInstance

private theorem overHom_ext_stalk (U : Opens X) (f g : M.over U ⟶ N.over U)
    (h : ∀ (x : X) (hx : x ∈ U),
      stalkLinearMapOfOver R U f x hx = stalkLinearMapOfOver R U g x hx) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf (forgetRing R)).obj N)
    W.unop.left _ _
  intro x hx
  have hh := LinearMap.congr_fun (h x (W.unop.hom.le hx))
    (TopCat.Presheaf.germ M.val.presheaf W.unop.left x hx m)
  erw [stalkLinearMapOfOver_germ_of_le R U f x _ W.unop.left hx W.unop.hom.le,
    stalkLinearMapOfOver_germ_of_le R U g x _ W.unop.left hx W.unop.hom.le] at hh
  exact hh

private def cofork_of_all_original_stalks (U : Opens X)
    (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) (hfg : f ≫ g = 0)
    (hex : ∀ (x : X) (hx : x ∈ U)
      (b : ↑(TopCat.Presheaf.stalk N.val.presheaf x)),
      stalkLinearMapOfOver R U g x hx b = 0 →
      ∃ a, stalkLinearMapOfOver R U f x hx a = b)
    (hsurj : ∀ (x : X) (hx : x ∈ U),
      Function.Surjective (stalkLinearMapOfOver R U g x hx)) :
    IsColimit (CokernelCofork.ofπ g hfg) := by
  let S : ShortComplex (SheafOfModules.{0} ((forgetRing R).over U)) :=
    ShortComplex.mk f g hfg
  let A := SheafOfModules.toSheaf ((forgetRing R).over U)
  let L : CategoryTheory.Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0} ⥤
      TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of U) := U.sheafEquivOver.functor
  let : L.IsEquivalence :=
    (U.sheafEquivOver (A := AddCommGrpCat.{0})).isEquivalence_functor
  letI : L.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hS : S.Exact := by
    apply A.reflects_exact_of_faithful
    apply L.reflects_exact_of_faithful
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact ((S.map A).map L)).mpr
    intro x
    apply (ShortComplex.ab_exact_iff _).mpr
    intro b hb
    let eM := originalOpenStalkIso R M U x
    let eN := originalOpenStalkIso R N U x
    let eP := originalOpenStalkIso R P U x
    have hzero : stalkLinearMapOfOver R U g x.val x.property (eN.hom b) = 0 := by
      calc
        _ = eP.hom (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (X := TopCat.of U) x).map
          (L.map (A.map g)).hom) b) := (originalOpenStalk_square R U g x b).symm
        _ = eP.hom 0 := congrArg eP.hom hb
        _ = 0 := map_zero _
    obtain ⟨a,ha⟩ := hex x.val x.property (eN.hom b) hzero
    obtain ⟨a',ha'⟩ := (ConcreteCategory.bijective_of_isIso eM.hom).2 a
    refine ⟨a',?_⟩
    apply (ConcreteCategory.bijective_of_isIso eN.hom).1
    change eN.hom (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (X := TopCat.of U) x).map
      (L.map (A.map f)).hom) a') = eN.hom b
    calc
      _ = stalkLinearMapOfOver R U f x.val x.property (eM.hom a') :=
        originalOpenStalk_square R U f x a'
      _ = stalkLinearMapOfOver R U f x.val x.property a := congrArg _ ha'
      _ = eN.hom b := ha
  letI : Epi g := epi_of_all_original_stalks R U g hsurj
  exact hS.gIsCokernel

private def columnSection {q : ℕ} (U : Opens X) (a : Fin q → R.obj.obj (op U)) :
    (SheafOfModules.free (R := forgetRing R) (Fin q)).val.obj (op U) :=
  ∑ i, (SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i)

set_option backward.isDefEq.respectTransparency false in
private theorem columnSection_germ {q : ℕ} (U : Opens X)
    (a : Fin q → R.obj.obj (op U)) (x : X) (hx : x ∈ U) :
    finiteFreeStalkLinearEquiv R (Fin q) x
      (TopCat.Presheaf.germ
        (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf U x hx
          (columnSection R U a)) =
      fun i => TopCat.Presheaf.germ R.obj U x hx (a i) := by
  unfold columnSection
  let gm := (TopCat.Presheaf.germ
    (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf U x hx).hom
  have hsum : gm (∑ i, (SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i)) =
      ∑ i, gm ((SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i)) :=
    map_sum gm _ Finset.univ
  change finiteFreeStalkLinearEquiv R (Fin q) x (gm _) = _
  have hterm (i : Fin q) : finiteFreeStalkLinearEquiv R (Fin q) x
      (TopCat.Presheaf.germ (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf U x hx
        ((SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i))) =
        Pi.single i (TopCat.Presheaf.germ R.obj U x hx (a i)) := by
    let eu := unitStalkLinearEquiv R x
    have hu : eu.symm (TopCat.Presheaf.germ R.obj U x hx (a i)) =
        TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf U x hx (a i) :=
      eu.symm_apply_eq.mpr (unitStalkLinearEquiv_germ R x U hx (a i)).symm
    calc
      _ = finiteFreeStalkLinearEquiv R (Fin q) x
          (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
            (TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf U x hx (a i))) :=
        congrArg _ (stalkLinearMap_germ (SheafOfModules.ιFree (R := forgetRing R) i).val x U hx (a i)).symm
      _ = finiteFreeStalkLinearEquiv R (Fin q) x
          (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
            (eu.symm (TopCat.Presheaf.germ R.obj U x hx (a i)))) :=
        congrArg (fun t => finiteFreeStalkLinearEquiv R (Fin q) x
          (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x t)) hu.symm
      _ = _ := finiteFreeStalkLinearEquiv_ι R (Fin q) x i _
  calc
    _ = finiteFreeStalkLinearEquiv R (Fin q) x
        (∑ i, gm ((SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i))) := congrArg _ hsum
    _ = ∑ i, finiteFreeStalkLinearEquiv R (Fin q) x
        (gm ((SheafOfModules.ιFree (R := forgetRing R) i).val.app (op U) (a i))) := map_sum _ _ _
    _ = ∑ i, Pi.single i (TopCat.Presheaf.germ R.obj U x hx (a i)) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := by ext i; simp

private def sectionMatrixMap {r q : ℕ} (U : Opens X)
    (B : Matrix (Fin r) (Fin q) (R.obj.obj (op U))) :
    (SheafOfModules.free (R := forgetRing R) (Fin q)).over U ⟶
      (SheafOfModules.free (R := forgetRing R) (Fin r)).over U :=
  freeOverMap R U (fun j => columnSection R U (fun i => B i j))

private theorem sectionMatrixMap_stalk {r q : ℕ} (U : Opens X)
    (B : Matrix (Fin r) (Fin q) (R.obj.obj (op U))) (x : X) (hx : x ∈ U) :
    (finiteFreeStalkLinearEquiv R (Fin r) x).toLinearMap.comp
      ((stalkLinearMapOfOver R U (sectionMatrixMap R U B) x hx).comp
        (finiteFreeStalkLinearEquiv R (Fin q) x).symm.toLinearMap) =
      Matrix.toLin' (B.map (TopCat.Presheaf.germ R.obj U x hx).hom) := by
  apply (Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) (Fin q)).ext
  intro j
  let e := finiteFreeStalkLinearEquiv R (Fin q) x
  have he : e.symm (Pi.single j 1) =
      stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) j).val x
        ((unitStalkLinearEquiv R x).symm 1) :=
    e.symm_apply_eq.mpr (finiteFreeStalkLinearEquiv_ι R (Fin q) x j 1).symm
  simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap]
  rw [he]
  change finiteFreeStalkLinearEquiv R (Fin r) x
    (stalkLinearMapOfOver R U (freeOverMap R U _) x hx _) = _
  rw [freeOverMap_stalk_ι,one_smul,columnSection_germ,Matrix.toLin'_apply,Matrix.mulVec_single_one]
  rfl

private theorem sectionMatrixMap_stalk_apply {r q : ℕ} (U : Opens X)
    (B : Matrix (Fin r) (Fin q) (R.obj.obj (op U))) (x : X) (hx : x ∈ U)
    (m : ↑(TopCat.Presheaf.stalk
      (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf x)) :
    finiteFreeStalkLinearEquiv R (Fin r) x
      (stalkLinearMapOfOver R U (sectionMatrixMap R U B) x hx m) =
      Matrix.toLin' (B.map (TopCat.Presheaf.germ R.obj U x hx).hom)
        (finiteFreeStalkLinearEquiv R (Fin q) x m) := by
  have h := LinearMap.congr_fun (sectionMatrixMap_stalk R U B x hx)
    (finiteFreeStalkLinearEquiv R (Fin q) x m)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] using h

private def originalMatrix {r q : ℕ}
    (F : SheafOfModules.free (R := forgetRing R) (Fin q) ⟶
      SheafOfModules.free (R := forgetRing R) (Fin r)) :
    Matrix (Fin r) (Fin q) (R.obj.obj (op ⊤)) :=
  sectionMatrix R ⊤ (F.over ⊤)
    (fun j => (SheafOfModules.freeSection (R := forgetRing R) j).val (op ⊤))

private theorem originalMatrix_stalk_apply {r q : ℕ}
    (F : SheafOfModules.free (R := forgetRing R) (Fin q) ⟶
      SheafOfModules.free (R := forgetRing R) (Fin r)) (x : X)
    (m : ↑(TopCat.Presheaf.stalk
      (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf x)) :
    finiteFreeStalkLinearEquiv R (Fin r) x (stalkLinearMap F.val x m) =
      Matrix.toLin' ((originalMatrix R F).map (TopCat.Presheaf.germ R.obj ⊤ x (by trivial)).hom)
        (finiteFreeStalkLinearEquiv R (Fin q) x m) := by
  let eq := finiteFreeStalkLinearEquiv R (Fin q) x
  let er := finiteFreeStalkLinearEquiv R (Fin r) x
  have hmat : er.toLinearMap.comp ((stalkLinearMap F.val x).comp eq.symm.toLinearMap) =
      Matrix.toLin' ((originalMatrix R F).map (TopCat.Presheaf.germ R.obj ⊤ x (by trivial)).hom) := by
    apply (Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) (Fin q)).ext
    intro j
    simp only [Pi.basisFun_apply,Matrix.toLin'_apply,Matrix.mulVec_single_one]
    change er (stalkLinearMap F.val x (eq.symm (Pi.single j 1))) = _
    have hs := finiteFreeStalkLinearEquiv_freeSection_germ R (Fin q) x ⊤ (by trivial) j
    have he : eq.symm (Pi.single j 1) =
        TopCat.Presheaf.germ (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf
          ⊤ x (by trivial) ((SheafOfModules.freeSection (R := forgetRing R) j).val (op ⊤)) :=
      eq.symm_apply_eq.mpr hs.symm
    rw [he]
    funext i
    have hh := sectionMatrix_germ R ⊤ (F.over ⊤)
      (fun j => (SheafOfModules.freeSection (R := forgetRing R) j).val (op ⊤))
      x (by trivial) i j
    have hH := congrArg (fun L => er (L
      (TopCat.Presheaf.germ (SheafOfModules.free (R := forgetRing R) (Fin q)).val.presheaf
        ⊤ x (by trivial) ((SheafOfModules.freeSection (R := forgetRing R) j).val (op ⊤)))) i)
      (stalkLinearMapOfOver_homOver R F ⊤ x (by trivial))
    exact hH.symm.trans hh.symm
  have h := LinearMap.congr_fun hmat (eq m)
  change er (stalkLinearMap F.val x (eq.symm (eq m))) = _ at h
  rw [eq.symm_apply_apply] at h
  exact h

private theorem over_stalk_zero (U : Opens X) (x : X) (hx : x ∈ U) :
    stalkLinearMapOfOver R U (0 : M.over U ⟶ N.over U) x hx = 0 := by
  change stalkLinearMapOfOver R U ((0 : M ⟶ N).over U) x hx = 0
  rw [stalkLinearMapOfOver_homOver]
  exact stalkLinearMap_zero x

private theorem kernel_stalk_injective (F : M ⟶ N) (x : X) :
    Function.Injective (stalkLinearMap (kernel.ι F).val x) := by
  have : Mono ((nativeStalkFunctor R x).map (kernel.ι F)) := Functor.map_mono _ _
  exact (ModuleCat.mono_iff_injective ((nativeStalkFunctor R x).map (kernel.ι F))).mp this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernel_stalk_comp_zero (F : M ⟶ N) (x : X)
    (a : ↑(TopCat.Presheaf.stalk (kernel F).val.presheaf x)) :
    stalkLinearMap F.val x (stalkLinearMap (kernel.ι F).val x a) = 0 := by
  have hh := congrArg (fun f : kernel F ⟶ N => stalkLinearMap f.val x a) (kernel.condition F)
  calc
    _ = stalkLinearMap ((kernel.ι F).val ≫ F.val) x a :=
      (LinearMap.congr_fun (stalkLinearMap_comp (kernel.ι F).val F.val x) a).symm
    _ = stalkLinearMap (0 : (kernel F).val ⟶ N.val) x a := hh
    _ = 0 := LinearMap.congr_fun (stalkLinearMap_zero x) a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelGenerator_of_relation_matrix {r q s : ℕ}
    (F : SheafOfModules.free (R := forgetRing R) (Fin q) ⟶
      SheafOfModules.free (R := forgetRing R) (Fin r))
    (U : Opens X) (C : Matrix (Fin q) (Fin s) (R.obj.obj (op U)))
    (hC : ∀ (x : X) (hx : x ∈ U),
      (Matrix.toLin' (C.map (TopCat.Presheaf.germ R.obj U x hx).hom)).range =
        LinearMap.ker (Matrix.toLin' ((originalMatrix R F).map
          (TopCat.Presheaf.germ R.obj ⊤ x (by trivial)).hom))) :
    ∃ π : (SheafOfModules.free (R := forgetRing R) (Fin s)).over U ⟶ (kernel F).over U,
      π ≫ (kernel.ι F).over U = sectionMatrixMap R U C ∧
      ∀ (x : X) (hx : x ∈ U), Function.Surjective (stalkLinearMapOfOver R U π x hx) := by
  let T := sectionMatrixMap R U C
  let eq (x : X) := finiteFreeStalkLinearEquiv R (Fin q) x
  let er (x : X) := finiteFreeStalkLinearEquiv R (Fin r) x
  let es (x : X) := finiteFreeStalkLinearEquiv R (Fin s) x
  let Bg (x : X) := (originalMatrix R F).map (TopCat.Presheaf.germ R.obj ⊤ x (by trivial)).hom
  let Cg (x : X) (hx : x ∈ U) := C.map (TopCat.Presheaf.germ R.obj U x hx).hom
  have hTF : T ≫ F.over U = 0 := by
    apply overHom_ext_stalk R U
    intro x hx
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_homOver,over_stalk_zero]
    apply LinearMap.ext
    intro m
    change stalkLinearMap F.val x (stalkLinearMapOfOver R U T x hx m) = 0
    apply (er x).injective
    rw [map_zero]
    calc
      _ = Matrix.toLin' (Bg x) (eq x (stalkLinearMapOfOver R U T x hx m)) :=
        originalMatrix_stalk_apply R F x _
      _ = Matrix.toLin' (Bg x) (Matrix.toLin' (Cg x hx) (es x m)) :=
        congrArg (Matrix.toLin' (Bg x)) (sectionMatrixMap_stalk_apply R U C x hx m)
      _ = 0 := (hC x hx).le ⟨es x m,rfl⟩
  have hlim := (KernelFork.ofι (kernel.ι F) (kernel.condition F)).mapIsLimit
    (kernelIsKernel F) (SheafOfModules.overFunctor (forgetRing R) U)
  obtain ⟨π,hπ⟩ := KernelFork.IsLimit.lift' hlim T hTF
  have hπι : π ≫ (kernel.ι F).over U = T := hπ
  have hπx (x : X) (hx : x ∈ U)
      (m : ↑(TopCat.Presheaf.stalk
        (SheafOfModules.free (R := forgetRing R) (Fin s)).val.presheaf x)) :
      stalkLinearMap (kernel.ι F).val x (stalkLinearMapOfOver R U π x hx m) =
        stalkLinearMapOfOver R U T x hx m := by
    have h := congrArg (fun f => stalkLinearMapOfOver R U f x hx) hπι
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_homOver] at h
    exact LinearMap.congr_fun h m
  have hsurj (x : X) (hx : x ∈ U) : Function.Surjective (stalkLinearMapOfOver R U π x hx) := by
    intro k
    let v := eq x (stalkLinearMap (kernel.ι F).val x k)
    have hv : v ∈ LinearMap.ker (Matrix.toLin' (Bg x)) := by
      change Matrix.toLin' (Bg x) v = 0
      calc
        _ = er x (stalkLinearMap F.val x (stalkLinearMap (kernel.ι F).val x k)) :=
          (originalMatrix_stalk_apply R F x _).symm
        _ = 0 := by rw [kernel_stalk_comp_zero,map_zero]
    have hvC : v ∈ (Matrix.toLin' (Cg x hx)).range := (hC x hx).symm.le hv
    obtain ⟨a,ha⟩ := hvC
    refine ⟨(es x).symm a,kernel_stalk_injective R F x ?_⟩
    calc
      _ = stalkLinearMapOfOver R U T x hx ((es x).symm a) := hπx x hx _
      _ = stalkLinearMap (kernel.ι F).val x k := by
        apply (eq x).injective
        calc
          _ = Matrix.toLin' (Cg x hx) (es x ((es x).symm a)) :=
            sectionMatrixMap_stalk_apply R U C x hx _
          _ = v := by rw [LinearEquiv.apply_symm_apply]; exact ha
  exact ⟨π,hπι,hsurj⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presentation_of_relation_matrices {r q s t : ℕ}
    (F : SheafOfModules.free (R := forgetRing R) (Fin q) ⟶
      SheafOfModules.free (R := forgetRing R) (Fin r))
    (U : Opens X) (C : Matrix (Fin q) (Fin s) (R.obj.obj (op U)))
    (D : Matrix (Fin s) (Fin t) (R.obj.obj (op U)))
    (hC : ∀ (x : X) (hx : x ∈ U),
      (Matrix.toLin' (C.map (TopCat.Presheaf.germ R.obj U x hx).hom)).range =
        LinearMap.ker (Matrix.toLin' ((originalMatrix R F).map
          (TopCat.Presheaf.germ R.obj ⊤ x (by trivial)).hom)))
    (hD : ∀ (x : X) (hx : x ∈ U),
      (Matrix.toLin' (D.map (TopCat.Presheaf.germ R.obj U x hx).hom)).range =
        LinearMap.ker (Matrix.toLin' (C.map (TopCat.Presheaf.germ R.obj U x hx).hom))) :
    ∃ σ : ((kernel F).over U).Presentation, σ.IsFinite := by
  let T := sectionMatrixMap R U C
  let Q := sectionMatrixMap R U D
  let eq (x : X) := finiteFreeStalkLinearEquiv R (Fin q) x
  let es (x : X) := finiteFreeStalkLinearEquiv R (Fin s) x
  let et (x : X) := finiteFreeStalkLinearEquiv R (Fin t) x
  let Cg (x : X) (hx : x ∈ U) := C.map (TopCat.Presheaf.germ R.obj U x hx).hom
  let Dg (x : X) (hx : x ∈ U) := D.map (TopCat.Presheaf.germ R.obj U x hx).hom
  obtain ⟨π,hπι,hsurj⟩ := kernelGenerator_of_relation_matrix R F U C hC
  have hπx (x : X) (hx : x ∈ U)
      (m : ↑(TopCat.Presheaf.stalk
        (SheafOfModules.free (R := forgetRing R) (Fin s)).val.presheaf x)) :
      stalkLinearMap (kernel.ι F).val x (stalkLinearMapOfOver R U π x hx m) =
        stalkLinearMapOfOver R U T x hx m := by
    have h := congrArg (fun f => stalkLinearMapOfOver R U f x hx) hπι
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_homOver] at h
    exact LinearMap.congr_fun h m
  have hQT : Q ≫ T = 0 := by
    apply overHom_ext_stalk R U
    intro x hx
    rw [stalkLinearMapOfOver_comp,over_stalk_zero]
    apply LinearMap.ext
    intro m
    change stalkLinearMapOfOver R U T x hx (stalkLinearMapOfOver R U Q x hx m) = 0
    apply (eq x).injective
    rw [map_zero]
    calc
      _ = Matrix.toLin' (Cg x hx) (es x (stalkLinearMapOfOver R U Q x hx m)) :=
        sectionMatrixMap_stalk_apply R U C x hx _
      _ = Matrix.toLin' (Cg x hx) (Matrix.toLin' (Dg x hx) (et x m)) :=
        congrArg (Matrix.toLin' (Cg x hx)) (sectionMatrixMap_stalk_apply R U D x hx m)
      _ = 0 := (hD x hx).le ⟨et x m,rfl⟩
  have hQπ : Q ≫ π = 0 := by
    apply (cancel_mono ((kernel.ι F).over U)).mp
    rw [Category.assoc,hπι,hQT,zero_comp]
  have hex (x : X) (hx : x ∈ U)
      (b : ↑(TopCat.Presheaf.stalk
        (SheafOfModules.free (R := forgetRing R) (Fin s)).val.presheaf x))
      (hb : stalkLinearMapOfOver R U π x hx b = 0) :
      ∃ a, stalkLinearMapOfOver R U Q x hx a = b := by
    have hTb : stalkLinearMapOfOver R U T x hx b = 0 := by
      calc
        _ = stalkLinearMap (kernel.ι F).val x (stalkLinearMapOfOver R U π x hx b) :=
          (hπx x hx b).symm
        _ = 0 := by rw [hb,map_zero]
    have hbC : es x b ∈ LinearMap.ker (Matrix.toLin' (Cg x hx)) := by
      change Matrix.toLin' (Cg x hx) (es x b) = 0
      calc
        _ = eq x (stalkLinearMapOfOver R U T x hx b) :=
          (sectionMatrixMap_stalk_apply R U C x hx b).symm
        _ = 0 := by rw [hTb,map_zero]
    obtain ⟨a,ha⟩ := (hD x hx).symm.le hbC
    refine ⟨(et x).symm a,(es x).injective ?_⟩
    calc
      _ = Matrix.toLin' (Dg x hx) (et x ((et x).symm a)) :=
        sectionMatrixMap_stalk_apply R U D x hx _
      _ = es x b := by rw [LinearEquiv.apply_symm_apply]; exact ha
  let hc := cofork_of_all_original_stalks R U Q π hQπ hex hsurj
  let eT := freeOverIso R U (Fin t)
  let eS := freeOverIso R U (Fin s)
  let f := eT.hom ≫ Q ≫ eS.inv
  let g := eS.hom ≫ π
  have hfg : f ≫ g = 0 := by
    simp only [f,g,Category.assoc,Iso.inv_hom_id_assoc,hQπ,comp_zero]
  have hc' : IsColimit (CokernelCofork.ofπ g hfg) := by
    refine IsCokernel.ofIso _ hc _ eT.symm eS.symm (Iso.refl _) ?_ ?_
    · simp only [f,Iso.symm_hom,Iso.inv_hom_id_assoc]
    · simp only [g,Iso.symm_hom,CokernelCofork.π_ofπ,Iso.inv_hom_id_assoc,Iso.refl_hom,Category.comp_id]
  let σ := SheafOfModules.presentationOfIsCokernelFree f g hfg hc'
  have hσ : σ.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (Fin s))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (Fin t))⟩ }
  exact ⟨σ,hσ⟩

private theorem isFinitePresentation_of_localPresentations
    (h : ∀ x : X, ∃ (U : Opens X) (_hx : x ∈ U)
      (σ : (M.over U).Presentation), σ.IsFinite) : M.IsFinitePresentation := by
  choose U hp σ hσ using h
  let data : M.QuasicoherentData.{0} :=
    { I := X
      X := U
      coversTop := by
        intro W
        apply (Opens.mem_grothendieckTopology X).mpr
        intro x hxW
        refine ⟨W ⊓ U x,homOfLE inf_le_left,?_,⟨hxW,hp x⟩⟩
        exact (Sieve.mem_ofObjects_iff U _).mpr ⟨x,⟨homOfLE inf_le_right⟩⟩
      presentation := σ }
  exact ⟨data,⟨hσ⟩⟩

end Native

private theorem exists_two_relation_matrices {n r q : ℕ}
    (B : Matrix (Fin r) (Fin q) (actualComplexSection (n := n) (⊤ : Opens (ComplexModel n))))
    (p : ComplexModel n) :
    ∃ (U : Opens (ComplexModel n)) (_hp : p ∈ U) (s t : ℕ)
      (C : Matrix (Fin q) (Fin s) (actualComplexSection (n := n) U))
      (D : Matrix (Fin s) (Fin t) (actualComplexSection (n := n) U)),
      (∀ (x : ComplexModel n) (hx : x ∈ U),
        (Matrix.toLin' (C.map
          ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U x hx).hom)).range =
          LinearMap.ker (Matrix.toLin' (B.map
            ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ ⊤ x (by trivial)).hom))) ∧
      ∀ (x : ComplexModel n) (hx : x ∈ U),
        (Matrix.toLin' (D.map
          ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U x hx).hom)).range =
          LinearMap.ker (Matrix.toLin' (C.map
            ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U x hx).hom)) := by
  let R := actualComplexStructureSheaf (n := n) (ComplexModel n)
  obtain ⟨V,_hV,hpV,s,C,_hBC,hC⟩ :=
    exists_relation_matrix_all_original_stalks ⊤ p (by trivial) B
  obtain ⟨U,hUV,hpU,t,D,_hCD,hD⟩ :=
    exists_relation_matrix_all_original_stalks V p hpV C
  let CU := C.map (R.presheaf.map (homOfLE hUV).op).hom
  have hCU (x : ComplexModel n) (hx : x ∈ U) :
      CU.map (R.presheaf.germ U x hx).hom = C.map (R.presheaf.germ V x (hUV hx)).hom := by
    ext i j
    exact TopCat.Presheaf.germ_res_apply R.presheaf (homOfLE hUV) x hx (C i j)
  have hc (x : ComplexModel n) (hx : x ∈ U) :
      (Matrix.toLin' (CU.map (R.presheaf.germ U x hx).hom)).range =
        LinearMap.ker (Matrix.toLin' (B.map (R.presheaf.germ ⊤ x (by trivial)).hom)) := by
    rw [hCU]
    exact hC x (hUV hx)
  have hd (x : ComplexModel n) (hx : x ∈ U) :
      (Matrix.toLin' (D.map (R.presheaf.germ U x hx).hom)).range =
        LinearMap.ker (Matrix.toLin' (CU.map (R.presheaf.germ U x hx).hom)) := by
    rw [hCU]
    exact hD x hx
  exact ⟨U,hpU,s,t,CU,D,hc,hd⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME actual categorical kernel is finitely presented as a native
sheaf, with its local finite presentations produced by TWO Oka applications. -/
theorem kernel_isFinitePresentation {n r q : ℕ}
    (F : SheafOfModules.free
      (R := forgetRing (actualComplexStructureSheaf (n := n) (ComplexModel n))) (Fin q) ⟶
      SheafOfModules.free
        (R := forgetRing (actualComplexStructureSheaf (n := n) (ComplexModel n))) (Fin r)) :
    (kernel F).IsFinitePresentation := by
  let R := actualComplexStructureSheaf (n := n) (ComplexModel n)
  apply isFinitePresentation_of_localPresentations
    (X := TopCat.of (ComplexModel n))
    (M := kernel F) R
  intro p
  obtain ⟨U,hpU,s,t,C,D,hC,hD⟩ := exists_two_relation_matrices (originalMatrix R F) p
  refine ⟨U,hpU,?_⟩
  exact presentation_of_relation_matrices
    (X := TopCat.of (ComplexModel n))
    (r := r) (q := q) (s := s) (t := t) R F U C D hC hD

end Hironaka.HironakaChowNativeFreeKernelCoherence
