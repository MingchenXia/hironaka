import Hironaka.Resolution.HironakaChowNativeFlatNeighborhood
import Hironaka.Resolution.HironakaChowNativeArbitraryOverRealization
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk
import Hironaka.Analytic.HolomorphicZeroSetThin
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-! Uniform native module continuation on an internally produced free part.
The original target chooses ONE connected open BEFORE EVERY arbitrary native
finite-type source and full morphism on that literal restricted space.
Torsion/coprimary continuation and compact-fibre S3 remain separate.
Blueprint FIRST: hironaka-g10-native-free-part-continuation.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaChowNativeFreePartContinuation


open Hironaka.HolomorphicIdealSheaves
  HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeSectionSpreading
  HironakaChowNativeFinitePresentationSpreading HironakaChowNativeFiniteTypeSpreading
  HironakaChowNativeFlatNeighborhood HironakaChowNativeArbitraryOverRealization
  HironakaNativeLiteralModuleRestriction HironakaSmoothCentreRealDomainActualSheafStalk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictOverHom_homOver {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} (f : G ⟶ H)
    (U V : Opens X) (hVU : V ≤ U) :
    restrictOverHom R U V hVU (f.over U) = f.over V := by
  ext W m
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem over_stalk_zero {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} (U : Opens X) (x : X) (hxU : x ∈ U) :
    stalkLinearMapOfOver R U (0 : G.over U ⟶ H.over U) x hxU = 0 := by
  change stalkLinearMapOfOver R U ((0 : G ⟶ H).over U) x hxU = 0
  rw [stalkLinearMapOfOver_homOver]
  change stalkLinearMap (0 : G.val ⟶ H.val) x = 0
  exact stalkLinearMap_zero x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalk_zero_of_over_zero {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} (f : G ⟶ H)
    (U : Opens X) (h : f.over U = 0) (x : X) (hxU : x ∈ U) :
    stalkLinearMap f.val x = 0 := by
  have hh := congrArg (fun k => stalkLinearMapOfOver R U k x hxU) h
  rwa [stalkLinearMapOfOver_homOver,over_stalk_zero] at hh

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Internal analytic-to-module argument; the scalar premise is derived
from the actual holomorphic structure in the public consumers below. -/
private theorem unit_continuation_of_scalar_identity {X : TopCat.{0}}
    [LocallyConnectedSpace X] [PreconnectedSpace X] (R : X.Sheaf CommRingCat.{0})
    (hscalar : ∀ (V : Opens X), _root_.IsPreconnected (V : Set X) →
      ∀ (s : R.obj.obj (op V)) (x : X) (hxV : x ∈ V),
        R.presheaf.germ V x hxV s = 0 → s = 0)
    {G : SheafOfModules.{0} (forgetRing R)} [G.IsFiniteType]
    (f : G ⟶ SheafOfModules.unit (forgetRing R)) (p : X)
    (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  classical
  let Z : Set X := {x | stalkInclusionLinearMap R G f x = 0}
  have hraw (x : X) (hx : x ∈ Z) : stalkLinearMap f.val x = 0 := by
    apply DFunLike.ext
    intro m
    apply (unitStalkLinearEquiv R x).injective
    have hh := LinearMap.congr_fun hx m
    simpa only [stalkInclusionLinearMap,LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap,LinearMap.zero_apply,map_zero] using hh
  have hZo : IsOpen Z := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have he : stalkLinearMapOfOver R ⊤ (f.over ⊤) x (by trivial) =
        stalkLinearMapOfOver R ⊤ (0 : G.over ⊤ ⟶
          (SheafOfModules.unit (forgetRing R)).over ⊤) x (by trivial) := by
      erw [stalkLinearMapOfOver_homOver,over_stalk_zero]
      exact hraw x hx
    obtain ⟨V,hV,hxV,hfV⟩ := exists_restriction_eq_of_isFiniteType R ⊤
      (f.over ⊤) 0 x (by trivial) he
    have hfv : f.over V = 0 := by
      have hz : restrictOverHom R ⊤ V hV
          (0 : G.over ⊤ ⟶ (SheafOfModules.unit (forgetRing R)).over ⊤) = 0 := by
        ext W m
        rfl
      simpa only [restrictOverHom_homOver,hz] using hfV
    apply mem_of_superset (V.isOpen.mem_nhds hxV)
    intro y hy
    change stalkInclusionLinearMap R G f y = 0
    unfold stalkInclusionLinearMap
    rw [stalk_zero_of_over_zero R f V hfv y hy]
    apply LinearMap.ext
    intro m
    change (unitStalkLinearEquiv R y) 0 = 0
    exact map_zero _
  have hZc : closure Z ⊆ Z := by
    intro q hq
    let A := ↑(TopCat.Presheaf.stalk R.obj q)
    let P := ↑(TopCat.Presheaf.stalk G.val.presheaf q)
    let : Module.Finite A P := moduleFinite_stalk_of_isFiniteType (M := G) R q
    obtain ⟨k,v,hv⟩ := Module.Finite.exists_fin (R := A) (M := P)
    obtain ⟨W,_hW,hqW,s,hs⟩ :=
      exists_common_germ_representatives G.val q ⊤ (by trivial) v
    obtain ⟨V,hVW,hVo,hqV,hVc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
        (inferInstance : LocallyConnectedSpace X) q W (W.isOpen.mem_nhds hqW)
    let V' : Opens X := ⟨V,hVo⟩
    have hV'W : V' ≤ W := hVW
    let sV (i : Fin k) := G.val.map (homOfLE hV'W).op (s i)
    let a (i : Fin k) : R.obj.obj (op V') := f.val.app (op V') (sV i)
    obtain ⟨z,hzV,hzZ⟩ := mem_closure_iff.mp hq V hVo hqV
    have ha (i : Fin k) : a i = 0 := by
      apply hscalar V' hVc.isPreconnected (a i) z hzV
      have hi := LinearMap.congr_fun hzZ
        (TopCat.Presheaf.germ G.val.presheaf V' z hzV (sV i))
      rw [stalkInclusionLinearMap_germ] at hi
      exact hi
    have hker : Submodule.span A (range v) ≤
        LinearMap.ker (stalkInclusionLinearMap R G f q) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change stalkInclusionLinearMap R G f q (v i) = 0
      have hsV : TopCat.Presheaf.germ G.val.presheaf V' q hqV (sV i) = v i :=
        (TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hV'W) q hqV (s i)).trans (hs i)
      rw [← hsV,stalkInclusionLinearMap_germ]
      change (R.presheaf.germ V' q hqV).hom (a i) = 0
      rw [ha i,map_zero]
    change stalkInclusionLinearMap R G f q = 0
    rw [hv] at hker
    exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
  have hpZ : p ∈ Z := by
    change stalkInclusionLinearMap R G f p = 0
    unfold stalkInclusionLinearMap
    rw [hp]
    apply LinearMap.ext
    intro m
    change (unitStalkLinearEquiv R p) 0 = 0
    exact map_zero _
  have hAll : (univ : Set X) ⊆ Z :=
    isPreconnected_univ.subset_of_closure_inter_subset hZo ⟨p,mem_univ p,hpZ⟩
      (fun _ h => hZc h.1)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change f.val.app V m = 0
  apply TopCat.Presheaf.section_ext R (unop V) _ 0
  intro x hx
  have hi := LinearMap.congr_fun (hAll (mem_univ x))
    (TopCat.Presheaf.germ G.val.presheaf (unop V) x hx m)
  rw [stalkInclusionLinearMap_germ] at hi
  simpa only [LinearMap.zero_apply,map_zero] using hi

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem free_continuation_of_scalar_identity {X : TopCat.{0}}
    [LocallyConnectedSpace X] [PreconnectedSpace X] (R : X.Sheaf CommRingCat.{0})
    (hscalar : ∀ (V : Opens X), _root_.IsPreconnected (V : Set X) →
      ∀ (s : R.obj.obj (op V)) (x : X) (hxV : x ∈ V),
        R.presheaf.germ V x hxV s = 0 → s = 0)
    {G : SheafOfModules.{0} (forgetRing R)} [G.IsFiniteType]
    {I : Type} [Finite I] (f : G ⟶ SheafOfModules.free (R := forgetRing R) I)
    (p : X) (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  classical
  let := Fintype.ofFinite I
  let T := fun _ : I => SheafOfModules.unit (forgetRing R)
  have hproj (i : I) : f ≫ Sigma.π T i = 0 := by
    apply unit_continuation_of_scalar_identity R hscalar (f ≫ Sigma.π T i) p
    change stalkLinearMap (f.val ≫ (Sigma.π T i).val) p = 0
    erw [stalkLinearMap_comp,hp]
    exact LinearMap.comp_zero _
  have hjp (i j : I) : Sigma.ι T i ≫ Sigma.π T j = if i=j then 𝟙 (T i) else 0 := by
    by_cases h : i=j
    · subst j
      rw [if_pos rfl]
      exact Sigma.ι_π_eq_id T i
    · exact (Sigma.ι_π_of_ne T h).trans (if_neg h).symm
  have htotal : ∑ i : I, Sigma.π T i ≫ Sigma.ι T i = 𝟙 (SheafOfModules.free (R := forgetRing R) I) := by
    apply Sigma.hom_ext
    intro j
    change Sigma.ι T j ≫ (∑ i : I, Sigma.π T i ≫ Sigma.ι T i) = Sigma.ι T j
    simp only [Preadditive.comp_sum,← Category.assoc,hjp,ite_comp,Category.id_comp,zero_comp]
    simp
  calc
    f = f ≫ (∑ i : I, Sigma.π T i ≫ Sigma.ι T i) := by rw [htotal,Category.comp_id]
    _ = (0 : G ⟶ SheafOfModules.free (R := forgetRing R) I) := by simp only [Preadditive.comp_sum,← Category.assoc,hproj,zero_comp,Finset.sum_const_zero]

abbrev originalSpace (n : ℕ) := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) (ComplexModel n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal restricted scalar sheaf satisfies the actual holomorphic identity theorem. -/
theorem restricted_scalar_eq_zero_of_germ_zero {n : ℕ}
    (U : Opens (originalSpace n).toTopCat)
    (V : Opens (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toTopCat)
    (hV : _root_.IsPreconnected (V : Set (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toTopCat))
    (s : ((originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf.obj.obj (op V)))
    (x : U) (hxV : x ∈ V)
    (hs : ((originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).presheaf.germ V x hxV) s = 0) : s = 0 := by
  change Opens (ComplexModel n) at U
  change Opens U at V
  change _root_.IsPreconnected (V : Set U) at hV
  let X := originalSpace n
  let W : Opens (ComplexModel n) := (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U).functor.obj V
  have hxW : x.val ∈ W := ⟨x,hxV,rfl⟩
  change actualComplexSection (n := n) W at s
  have hz : (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ W x.val hxW s = 0 := by
    have h := congrArg (fun t => (X.restrictStalkIso (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U) x).hom t) hs
    have hformula := LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply X
      (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U) V x hxV s
    exact hformula.symm.trans (by simpa only [map_zero] using h)
  have hWc : _root_.IsPreconnected (W : Set (ComplexModel n)) :=
    hV.image Subtype.val continuous_subtype_val.continuousOn
  have hdiff : DifferentiableOn ℂ (sectionExtension W s) W := by
    intro y hy
    exact ((sectionExtension_holomorphicAt W s y hy).self_of_nhds).differentiableAt.differentiableWithinAt
  have heq : (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ W x.val hxW s =
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ W x.val hxW 0 := by
    simpa only [map_zero] using hz
  obtain ⟨K,hxK,iK,jK,hK⟩ :=
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ_eq x.val hxW hxW s 0 heq
  have hnear : ∀ᶠ y in 𝓝 x.val, sectionExtension W s y = 0 := by
    filter_upwards [K.isOpen.mem_nhds hxK] with y hy
    rw [sectionExtension_apply W s y (iK.le hy)]
    have h := congrArg (fun t : actualComplexSection (n := n) K => t ⟨y,hy⟩) hK
    exact h
  have hzero := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero
    W.isOpen hWc hdiff hxW hnear
  apply ContMDiffMap.ext
  intro y
  have h := (hzero y.val y.property).self_of_nhds
  change s y = 0
  simpa only [sectionExtension_apply W s y.val y.property] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY finite-type source on the SAME literal connected restricted space
and EVERY native full map into its finite free sheaf satisfy continuation. -/
theorem native_free_hom_eq_zero_of_stalk_zero {n : ℕ}
    (U : Opens (originalSpace n).toTopCat) (hU : _root_.IsPreconnected (U : Set (originalSpace n).toTopCat))
    {G : SheafOfModules.{0} (forgetRing (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf)}
    [G.IsFiniteType] {I : Type} [Finite I]
    (f : G ⟶ SheafOfModules.free (R := forgetRing (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf) I)
    (p : U) (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  change Opens (ComplexModel n) at U
  change _root_.IsPreconnected (U : Set (ComplexModel n)) at hU
  let : PreconnectedSpace (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toTopCat := by
    change PreconnectedSpace U
    exact isPreconnected_iff_preconnectedSpace.mp hU
  let : LocallyConnectedSpace (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toTopCat := by
    change LocallyConnectedSpace U
    exact U.isOpen.locallyConnectedSpace
  exact free_continuation_of_scalar_identity
    (X := (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toTopCat)
    (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf
    (restricted_scalar_eq_zero_of_germ_zero U) f p hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restrictOverIso {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} (U V : Opens X) (hVU : V ≤ U)
    (e : G.over U ≅ H.over U) : G.over V ≅ H.over V where
  hom := restrictOverHom R U V hVU e.hom
  inv := restrictOverHom R U V hVU e.inv
  hom_inv_id := by
    rw [← restrictOverHom_comp,e.hom_inv_id]
    ext W m
    rfl
  inv_hom_id := by
    rw [← restrictOverHom_comp,e.inv_hom_id]
    ext W m
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def realizedRestrictionIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (F : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf)) :
    (realizationFunctor X U).obj (F.over U) ≅ nativeModuleRestriction X U F where
  hom := by
    refine ⟨{ app := fun _ => ?_, naturality := ?_ }⟩
    · exact ModuleCat.ofHom {
        toFun := fun m => m
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    · intros
      ext m
      rfl
  inv := by
    refine ⟨{ app := fun _ => ?_, naturality := ?_ }⟩
    · exact ModuleCat.ofHom {
        toFun := fun m => m
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    · intros
      ext m
      rfl
  hom_inv_id := by ext W m; rfl
  inv_hom_id := by ext W m; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_literal_free_ball {n : ℕ}
    (F : SheafOfModules.{0} (forgetRing (originalSpace n).toSheafedSpace.sheaf)) [F.IsFinitePresentation]
    (p : ComplexModel n)
    (hflat : Module.Flat ↑(TopCat.Presheaf.stalk (originalSpace n).toSheafedSpace.sheaf.obj p)
      ↑(TopCat.Presheaf.stalk F.val.presheaf p)) :
    ∃ (r : ℕ) (U : Opens (originalSpace n).toTopCat) (_hpU : p ∈ U),
      _root_.IsPreconnected (U : Set (originalSpace n).toTopCat) ∧
      Nonempty (nativeModuleRestriction (originalSpace n) U F ≅
        SheafOfModules.free (R := forgetRing
          (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf)
          (ULift.{0} (Fin r))) := by
  let X := originalSpace n
  let : IsLocalRing ↑(TopCat.Presheaf.stalk X.toSheafedSpace.sheaf.obj p) := X.isLocalRing p
  obtain ⟨r,V,hpV,⟨e⟩⟩ := exists_free_neighborhood_of_flat_stalk X.toSheafedSpace.sheaf p hflat
  change Opens (ComplexModel n) at V
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp V.isOpen p hpV
  let U : Opens (ComplexModel n) := ⟨Metric.ball p ε,Metric.isOpen_ball⟩
  have hpU : p ∈ U := Metric.mem_ball_self hε
  have hUV : U ≤ V := hεV
  let I := ULift.{0} (Fin r)
  let eU := (restrictOverIso X.toSheafedSpace.sheaf V U hUV e).trans (freeOverIso X.toSheafedSpace.sheaf U I).symm
  let E := ((realizationFunctor X U).mapIso eU).trans (realizationFreeIso X U I)
  have eLiteral : nativeModuleRestriction X U F ≅
      SheafOfModules.free (R := forgetRing
        (X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) U)).toSheafedSpace.sheaf) I :=
    (realizedRestrictionIso X U F).symm.trans E
  have hUc : _root_.IsPreconnected (U : Set (ComplexModel n)) := (convex_ball p ε).isPreconnected
  exact ⟨r,U,hpU,hUc,⟨eLiteral⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ORIGINAL FP target and ONE flat original stalk choose U before ALL
native finite-type G/f on the literal restriction. No ambient G extension. -/
theorem exists_uniform_continuation_neighborhood_of_flat_stalk {n : ℕ}
    (F : SheafOfModules.{0} (forgetRing (originalSpace n).toSheafedSpace.sheaf)) [F.IsFinitePresentation]
    (p : ComplexModel n)
    (hflat : Module.Flat ↑(TopCat.Presheaf.stalk (originalSpace n).toSheafedSpace.sheaf.obj p)
      ↑(TopCat.Presheaf.stalk F.val.presheaf p)) :
    ∃ (U : Opens (originalSpace n).toTopCat) (hpU : p ∈ U),
      _root_.IsPreconnected (U : Set (originalSpace n).toTopCat) ∧
      ∀ (G : SheafOfModules.{0} (forgetRing (originalSpace n |>.restrict (Opens.isOpenEmbedding (X := (originalSpace n).toTopCat) U)).toSheafedSpace.sheaf))
        (_hG : G.IsFiniteType)
        (f : G ⟶ nativeModuleRestriction (originalSpace n) U F),
        stalkLinearMap f.val (⟨p,hpU⟩ : U) = 0 → f = 0 := by
  obtain ⟨r,U,hpU,hUc,⟨eLiteral⟩⟩ := exists_literal_free_ball F p hflat
  refine ⟨U,hpU,hUc,?_⟩
  intro G hG f hf
  let := hG
  have hz : stalkLinearMap ((f ≫ eLiteral.hom).val) (⟨p,hpU⟩ : U) = 0 := by
    change stalkLinearMap (f.val ≫ eLiteral.hom.val) (⟨p,hpU⟩ : U) = 0
    erw [stalkLinearMap_comp,hf]
    exact LinearMap.comp_zero _
  have he := native_free_hom_eq_zero_of_stalk_zero U hUc (f ≫ eLiteral.hom) ⟨p,hpU⟩ hz
  exact (cancel_mono eLiteral.hom).mp (by simpa only [zero_comp] using he)

end Hironaka.HironakaChowNativeFreePartContinuation
