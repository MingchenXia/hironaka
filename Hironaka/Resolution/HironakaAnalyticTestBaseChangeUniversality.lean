import Hironaka.Resolution.HironakaAnalyticBaseChangeQuotientModel
import Hironaka.Resolution.HironakaNonreducedQuotientNeighborhoodLifting
import Hironaka.Resolution.HironakaAnalyticBaseChangeLocalFactorization
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Actual analytic-test universality of the original nonreduced joint model.
Blueprint FIRST: `hironaka-analytic-test-basechange-universality.tex`.

Native descent and full factor uniqueness use the genuine neighborhood and
local-factor producers. The ordinary inputs are the full analytic test cone.
No product of all bare locally ringed spaces or analytic tensor identity is asserted.
-/
set_option autoImplicit false
noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
  AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaAnalyticTestBaseChangeUniversality

open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaAnalyticBaseChangeQuotientModel HironakaNonreducedAnalyticQuotientModel
  HironakaNonreducedAnalyticQuotientMorphism
  HironakaNonreducedQuotientNeighborhoodLifting HironakaNonreducedQuotientGermLifting
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaActualAnalyticBaseChangeCoefficients HironakaActualWholeStalkHolomorphicPullback

/-- Ring maps glue by the ORIGINAL sheaf condition, without reconstructing
any operations: covariant representable Hom(S,-) preserves limits. -/
private theorem existsUnique_ring_hom_gluing {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) (S : CommRingCat.{0})
    {ι : Type} (U : ι → Opens X) (V : Opens X)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (f : ∀ i, S ⟶ R.obj.obj (op (U i)))
    (hcompat : ∀ i j,
      f i ≫ R.obj.map (Opens.infLELeft (U i) (U j)).op =
      f j ≫ R.obj.map (Opens.infLERight (U i) (U j)).op) :
    ∃! g : S ⟶ R.obj.obj (op V),
      ∀ i, g ≫ R.obj.map (iUV i).op = f i := by
  let H : X.Sheaf (Type 0) := {
    obj := R.obj ⋙ coyoneda.obj (op S)
    property := CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
      (Opens.grothendieckTopology X) R.obj (coyoneda.obj (op S)) R.property }
  have hc : TopCat.Presheaf.IsCompatible H.obj U f := by
    intro i j
    exact hcompat i j
  exact H.existsUnique_gluing' U V iUV hcover f hc

private theorem ring_hom_ext_on_cover {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) (S : CommRingCat.{0})
    {ι : Type} (U : ι → Opens X) (V : Opens X)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (f g : S ⟶ R.obj.obj (op V))
    (heq : ∀ i, f ≫ R.obj.map (iUV i).op = g ≫ R.obj.map (iUV i).op) :
    f = g := by
  let H : X.Sheaf (Type 0) := {
    obj := R.obj ⋙ coyoneda.obj (op S)
    property := CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
      (Opens.grothendieckTopology X) R.obj (coyoneda.obj (op S)) R.property }
  exact H.eq_of_locally_eq' U V iUV hcover f g heq

private theorem exists_components_of_base_eq
    {X Y : PresheafedSpace CommRingCat.{0}} (f : X ⟶ Y)
    (h : X.carrier ⟶ Y.carrier) (hf : f.base = h) :
    ∃ c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat h).obj X.presheaf,
      ({ base := h, c := c } : X ⟶ Y) = f := by
  rcases f with ⟨f,c⟩
  dsimp at hf
  subst f
  exact ⟨c,rfl⟩

private theorem image_restricted_preimage {X Y : TopCat.{0}}
    (U : Opens X) (h : X ⟶ Y) (V : Opens Y) :
    U.isOpenEmbedding.functor.obj ((Opens.map (U.inclusion' ≫ h)).obj V) =
      U ⊓ (Opens.map h).obj V := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,hy⟩
  · rintro ⟨hxU,hxV⟩
    exact ⟨⟨x,hxU⟩,hxV,rfl⟩

/-- The actual topological inclusion between two existing carrier opens. -/
private def restrictionTopMap {X : TopCat.{0}} (W U : Opens X) (hWU : W ≤ U) :
    (Opens.toTopCat X).obj W ⟶ (Opens.toTopCat X).obj U :=
  (Opens.toTopCat X).map (homOfLE hWU)

private theorem restriction_image_le {X : TopCat.{0}} (W U : Opens X) (hWU : W ≤ U)
    (V : Opens ((Opens.toTopCat X).obj U)) :
    W.isOpenEmbedding.functor.obj ((Opens.map (restrictionTopMap W U hWU)).obj V) ≤
      U.isOpenEmbedding.functor.obj V := by
  rintro x ⟨w,hw,rfl⟩
  exact ⟨⟨w.val,hWU w.property⟩,hw,rfl⟩

/-- A restriction MORPHISM using only the existing presheaf maps on opens. -/
private def restrictionPresheafMap (X : PresheafedSpace CommRingCat.{0})
    (W U : Opens X.carrier) (hWU : W ≤ U) :
    X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding where
  base := restrictionTopMap W U hWU
  c := {
    app := fun V => X.presheaf.map (homOfLE (restriction_image_le W U hWU V.unop)).op
    naturality := by
      rintro ⟨V⟩ ⟨T⟩ j
      change X.presheaf.map _ ≫ X.presheaf.map _ =
        X.presheaf.map _ ≫ X.presheaf.map _
      exact (X.presheaf.map_comp _ _).symm.trans
        ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans
          (X.presheaf.map_comp _ _)) }

private theorem restrictionPresheafMap_fac (X : PresheafedSpace CommRingCat.{0})
    (W U : Opens X.carrier) (hWU : W ≤ U) :
    restrictionPresheafMap X W U hWU ≫ X.ofRestrict U.isOpenEmbedding =
      X.ofRestrict W.isOpenEmbedding := by
  apply PresheafedSpace.hext (restrictionPresheafMap X W U hWU ≫
    X.ofRestrict U.isOpenEmbedding) (X.ofRestrict W.isOpenEmbedding) rfl
  apply heq_of_eq
  apply NatTrans.ext
  funext V
  change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
  exact (X.presheaf.map_comp _ _).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))

/-- The EXISTING native open-immersion lift is the actual restriction map;
its explicit underlying formula follows from the native inclusion mono. -/
private def nativeRestrictionMap (X : LocallyRingedSpace.{0})
    (W U : Opens X.toTopCat) (hWU : W ≤ U) :
    X.restrict W.isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict W.isOpenEmbedding)
    (by rintro x ⟨w,rfl⟩; exact ⟨⟨w.val,hWU w.property⟩,rfl⟩)

private theorem nativeRestrictionMap_fac (X : LocallyRingedSpace.{0})
    (W U : Opens X.toTopCat) (hWU : W ≤ U) :
    nativeRestrictionMap X W U hWU ≫ X.ofRestrict U.isOpenEmbedding =
      X.ofRestrict W.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

private theorem nativeRestrictionMap_toHom (X : LocallyRingedSpace.{0})
    (W U : Opens X.toTopCat) (hWU : W ≤ U) :
    (nativeRestrictionMap X W U hWU).toHom =
      restrictionPresheafMap X.toPresheafedSpace W U hWU := by
  apply (cancel_mono (X.toPresheafedSpace.ofRestrict U.isOpenEmbedding)).mp
  exact (congrArg LocallyRingedSpace.Hom.toHom
    (nativeRestrictionMap_fac X W U hWU)).trans
      (restrictionPresheafMap_fac X.toPresheafedSpace W U hWU).symm

private theorem components_eq_of_fixed_base {X Y : PresheafedSpace CommRingCat.{0}}
    (f : X.carrier ⟶ Y.carrier)
    (c d : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat f).obj X.presheaf)
    (he : ({ base := f, c := c } : X ⟶ Y) = { base := f, c := d }) : c = d := by
  cases he
  rfl

/-- The SAME local component, read on its actual image open. Only the native
presheaf's map along an equality of opens transports its section ring. -/
private def localComponent {X Y : PresheafedSpace CommRingCat.{0}}
    (h : X.carrier ⟶ Y.carrier) (U : Opens X.carrier)
    (c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj
        (X.restrict (Opens.isOpenEmbedding (X := X.carrier) U)).presheaf)
    (V : Opens Y.carrier) :
    Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op (U ⊓ (Opens.map h).obj V)) :=
  c.app (op V) ≫ X.presheaf.map
    (eqToHom (congrArg op (image_restricted_preimage U h V)))

set_option backward.isDefEq.respectTransparency false in
private theorem localComponent_naturality {X Y : PresheafedSpace CommRingCat.{0}}
    (h : X.carrier ⟶ Y.carrier) (U : Opens X.carrier)
    (c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj
        (X.restrict (Opens.isOpenEmbedding (X := X.carrier) U)).presheaf)
    {V W : Opens Y.carrier} (j : V ⟶ W) :
    Y.presheaf.map j.op ≫ localComponent h U c V =
      localComponent h U c W ≫ X.presheaf.map (homOfLE
        (inf_le_inf le_rfl ((Opens.map h).map j).le)).op := by
  unfold localComponent
  erw [← Category.assoc,c.naturality,Category.assoc]
  change c.app (op W) ≫ (X.presheaf.map _ ≫ X.presheaf.map _) =
    (c.app (op W) ≫ X.presheaf.map _) ≫ X.presheaf.map _
  simp only [Category.assoc,← X.presheaf.map_comp]
  apply congrArg (fun k => c.app (op W) ≫ X.presheaf.map k)
  exact Subsingleton.elim _ _

private theorem map_path_comp {D : Type*} {E : Type*} [Category D] [Category E]
    (P : D ⥤ E) {R : E} {A B Z : D} (a : R ⟶ P.obj A)
    (f : A ⟶ B) (g : B ⟶ Z) (k : A ⟶ Z) (he : f ≫ g = k) :
    (a ≫ P.map f) ≫ P.map g = a ≫ P.map k :=
  (Category.assoc _ _ _).trans (congrArg (fun m => a ≫ m)
    ((P.map_comp f g).symm.trans (congrArg P.map he)))

private theorem map_path_eq {D : Type*} {E : Type*} [Category D] [Category E]
    (P : D ⥤ E) {R : E} {A B B' Z : D} (a : R ⟶ P.obj A)
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' : B' ⟶ Z)
    (he : f ≫ g = f' ≫ g') :
    (a ≫ P.map f) ≫ P.map g = (a ≫ P.map f') ≫ P.map g' :=
  (map_path_comp P a f g (f' ≫ g') he).trans
    (map_path_comp P a f' g' (f' ≫ g') rfl).symm

/-- Equality on the actual native overlap implies compatibility on the
SAME image opens used by the existing structure sheaf. -/
private theorem localComponent_compatible {X Y : PresheafedSpace CommRingCat.{0}}
    (h : X.carrier ⟶ Y.carrier) (U W : Opens X.carrier)
    (cU : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj (X.restrict U.isOpenEmbedding).presheaf)
    (cW : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (W.inclusion' ≫ h)).obj (X.restrict W.isOpenEmbedding).presheaf)
    (he : restrictionPresheafMap X (U ⊓ W) U inf_le_left ≫
        ({ base := U.inclusion' ≫ h, c := cU } : X.restrict U.isOpenEmbedding ⟶ Y) =
      restrictionPresheafMap X (U ⊓ W) W inf_le_right ≫
        ({ base := W.inclusion' ≫ h, c := cW } : X.restrict W.isOpenEmbedding ⟶ Y))
    (V : Opens Y.carrier) :
    localComponent h U cU V ≫ X.presheaf.map (Opens.infLELeft
        (U ⊓ (Opens.map h).obj V) (W ⊓ (Opens.map h).obj V)).op =
      localComponent h W cW V ≫ X.presheaf.map (Opens.infLERight
        (U ⊓ (Opens.map h).obj V) (W ⊓ (Opens.map h).obj V)).op := by
  let Z := U ⊓ W
  have hc := components_eq_of_fixed_base (X := X.restrict Z.isOpenEmbedding) (Y := Y)
    (Z.inclusion' ≫ h)
    ((restrictionPresheafMap X Z U inf_le_left ≫
      ({ base := U.inclusion' ≫ h, c := cU } : X.restrict U.isOpenEmbedding ⟶ Y)).c)
    ((restrictionPresheafMap X Z W inf_le_right ≫
      ({ base := W.inclusion' ≫ h, c := cW } : X.restrict W.isOpenEmbedding ⟶ Y)).c) he
  have ha := congrArg (fun c => c.app (op V)) hc
  let rU := (homOfLE (restriction_image_le Z U inf_le_left
    ((Opens.map (U.inclusion' ≫ h)).obj V))).op
  let rW := (homOfLE (restriction_image_le Z W inf_le_right
    ((Opens.map (W.inclusion' ≫ h)).obj V))).op
  change cU.app (op V) ≫ X.presheaf.map rU = cW.app (op V) ≫ X.presheaf.map rW at ha
  let K := Z.isOpenEmbedding.functor.obj ((Opens.map (Z.inclusion' ≫ h)).obj V)
  let T := (U ⊓ (Opens.map h).obj V) ⊓ (W ⊓ (Opens.map h).obj V)
  have hTK : T ≤ K := by
    rintro x ⟨⟨hxU,hxV⟩,hxW,_hxV'⟩
    exact ⟨⟨x,hxU,hxW⟩,hxV,rfl⟩
  have hat := congrArg (fun k => k ≫ X.presheaf.map (homOfLE hTK).op) ha
  exact (map_path_eq X.presheaf (cU.app (op V)) _ _ rU (homOfLE hTK).op
    (Subsingleton.elim _ _)).trans
      (hat.trans (map_path_eq X.presheaf (cW.app (op V)) rW (homOfLE hTK).op _ _
        (Subsingleton.elim _ _)))

/-- The overlap equation used here is DERIVED internally for each pair
of original opens; this only reads its actual native sheaf components. -/
private theorem native_overlap_implies_local_components
    {X Y : LocallyRingedSpace.{0}}
    (h : X.toTopCat ⟶ Y.toTopCat) (U W : Opens X.toTopCat)
    (fU : X.restrict U.isOpenEmbedding ⟶ Y)
    (fW : X.restrict W.isOpenEmbedding ⟶ Y)
    (cU : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj (X.restrict U.isOpenEmbedding).presheaf)
    (cW : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (W.inclusion' ≫ h)).obj (X.restrict W.isOpenEmbedding).presheaf)
    (hcfU : ({base := U.inclusion' ≫ h, c := cU} :
      (X.restrict U.isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace) = fU.toHom)
    (hcfW : ({base := W.inclusion' ≫ h, c := cW} :
      (X.restrict W.isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace) = fW.toHom)
    (he : nativeRestrictionMap X (U ⊓ W) U inf_le_left ≫ fU =
      nativeRestrictionMap X (U ⊓ W) W inf_le_right ≫ fW)
    (V : Opens Y.toTopCat) :
    localComponent h U cU V ≫ X.presheaf.map (Opens.infLELeft
      (U ⊓ (Opens.map h).obj V) (W ⊓ (Opens.map h).obj V)).op =
    localComponent h W cW V ≫ X.presheaf.map (Opens.infLERight
      (U ⊓ (Opens.map h).obj V) (W ⊓ (Opens.map h).obj V)).op := by
  refine localComponent_compatible
    (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace) h U W cU cW ?_ V
  have he' : ((nativeRestrictionMap X (U ⊓ W) U inf_le_left).toHom ≫ fU.toHom :
      (X.restrict (U ⊓ W).isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace) =
    ((nativeRestrictionMap X (U ⊓ W) W inf_le_right).toHom ≫ fW.toHom :
      (X.restrict (U ⊓ W).isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace) :=
    congrArg LocallyRingedSpace.Hom.toHom he
  rw [nativeRestrictionMap_toHom,nativeRestrictionMap_toHom] at he'
  exact (congrArg (fun k : (X.restrict U.isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace =>
    restrictionPresheafMap X.toPresheafedSpace (U ⊓ W) U inf_le_left ≫ k) hcfU).trans
      (he'.trans (congrArg (fun k : (X.restrict W.isOpenEmbedding).toPresheafedSpace ⟶ Y.toPresheafedSpace =>
        restrictionPresheafMap X.toPresheafedSpace (U ⊓ W) W inf_le_right ≫ k) hcfW.symm))

/-- The actual structure-sheaf condition glues compatible LOCAL COMPONENTS
over a fixed continuous map into a WHOLE presheaf morphism. All ring maps
and operations are the existing native ones. This is a private descent
step; its component family will be constructed from actual local factors. -/
private theorem exists_glued_presheaf_map {X Y : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) (P : Y.Presheaf CommRingCat.{0})
    (h : X ⟶ Y) {ι : Type} (U : ι → Opens X)
    (hcover : (⊤ : Opens X) ≤ iSup U)
    (f : ∀ (i : ι) (V : Opens Y),
      P.obj (op V) ⟶ R.obj.obj (op (U i ⊓ (Opens.map h).obj V)))
    (hcompat : ∀ (V : Opens Y) (i j : ι),
      f i V ≫ R.obj.map (Opens.infLELeft
        (U i ⊓ (Opens.map h).obj V) (U j ⊓ (Opens.map h).obj V)).op =
      f j V ≫ R.obj.map (Opens.infLERight
        (U i ⊓ (Opens.map h).obj V) (U j ⊓ (Opens.map h).obj V)).op)
    (hnat : ∀ (i : ι) {V W : Opens Y} (j : V ⟶ W),
      P.map j.op ≫ f i V =
      f i W ≫ R.obj.map (homOfLE
        (inf_le_inf le_rfl ((Opens.map h).map j).le)).op) :
    ∃ g : P ⟶ (TopCat.Presheaf.pushforward CommRingCat h).obj R.obj,
      ∀ (i : ι) (V : Opens Y),
        g.app (op V) ≫ R.obj.map (Opens.infLERight
          (U i) ((Opens.map h).obj V)).op = f i V := by
  classical
  have hVcover (V : Opens Y) :
      (Opens.map h).obj V ≤ ⨆ i, U i ⊓ (Opens.map h).obj V := by
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : Opens X) by trivial))
    exact Opens.mem_iSup.mpr ⟨i,hi,hx⟩
  have hex (V : Opens Y) :
      ∃! g : P.obj (op V) ⟶ R.obj.obj (op ((Opens.map h).obj V)),
        ∀ i, g ≫ R.obj.map (Opens.infLERight
          (U i) ((Opens.map h).obj V)).op = f i V := by
    exact existsUnique_ring_hom_gluing R (P.obj (op V))
      (fun i => U i ⊓ (Opens.map h).obj V) ((Opens.map h).obj V)
      (fun i => Opens.infLERight (U i) ((Opens.map h).obj V))
      (hVcover V) (fun i => f i V) (hcompat V)
  choose g hg using fun V => (hex V).exists
  refine ⟨{ app := fun V => g V.unop, naturality := ?_ },?_⟩
  · rintro ⟨V⟩ ⟨W⟩ j
    change P.map j ≫ g W =
      g V ≫ R.obj.map ((Opens.map h).map j.unop).op
    apply ring_hom_ext_on_cover R (P.obj (op V))
      (fun i => U i ⊓ (Opens.map h).obj W) ((Opens.map h).obj W)
      (fun i => Opens.infLERight (U i) ((Opens.map h).obj W)) (hVcover W)
    intro i
    calc
      (P.map j ≫ g W) ≫ R.obj.map (Opens.infLERight
          (U i) ((Opens.map h).obj W)).op = P.map j ≫ f i W := by
        rw [Category.assoc,hg W i]
      _ = f i V ≫ R.obj.map (homOfLE
          (inf_le_inf le_rfl ((Opens.map h).map j.unop).le)).op := hnat i j.unop
      _ = (g V ≫ R.obj.map (Opens.infLERight
          (U i) ((Opens.map h).obj V)).op) ≫ R.obj.map (homOfLE
          (inf_le_inf le_rfl ((Opens.map h).map j.unop).le)).op := by
        rw [hg V i]
      _ = (g V ≫ R.obj.map ((Opens.map h).map j.unop).op) ≫
          R.obj.map (Opens.infLERight (U i) ((Opens.map h).obj W)).op := by
        simp only [Category.assoc,← R.obj.map_comp]
        apply congrArg (fun k => g V ≫ R.obj.map k)
        exact Subsingleton.elim _ _
  · intro i V
    exact hg V i

/-- Locality is descended for the actual glued ringed-space map, through
the literal source restrictions. The local maps and full equations are
internal descent data, not hypotheses of the analytic-test producer. -/
private def nativeHomOfLocal {X Y : LocallyRingedSpace.{0}} {ι : Type}
    (U : ι → Opens X.toTopCat) (hcover : (⊤ : Opens X.toTopCat) ≤ iSup U)
    (g : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)
    (f : ∀ i, X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i)) ⟶ Y)
    (heq : ∀ i,
      (X.ofRestrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).toHom ≫ g =
        (f i).toHom) : X ⟶ Y where
  toHom := g
  prop x := by
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp
      (hcover (show x ∈ (⊤ : Opens X.toTopCat) by trivial))
    let xi : U i := ⟨x,hi⟩
    let j := (X.ofRestrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).toHom
    have he : IsLocalHom (((j ≫ g).stalkMap xi).hom) =
        IsLocalHom (((f i).toHom.stalkMap xi).hom) :=
      congrArg (fun k => IsLocalHom ((k.stalkMap xi).hom)) (heq i)
    have hlocal := he.mpr ((f i).prop xi)
    have hc := PresheafedSpace.stalkMap.comp j g xi
    have he' : IsLocalHom (((j ≫ g).stalkMap xi).hom) =
        IsLocalHom (((g.stalkMap (j.base xi)) ≫ j.stalkMap xi).hom) :=
      congrArg (fun k : Y.presheaf.stalk (g.base (j.base xi)) ⟶
        (X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).presheaf.stalk xi =>
          IsLocalHom k.hom) hc
    let : IsLocalHom ((j.stalkMap xi).hom.comp (g.stalkMap x).hom) := he'.mp hlocal
    exact isLocalHom_of_comp (g.stalkMap x).hom (j.stalkMap xi).hom

set_option backward.isDefEq.respectTransparency false in
private theorem full_restriction_equation_of_components
    {X Y : PresheafedSpace CommRingCat.{0}} (h : X.carrier ⟶ Y.carrier)
    (U : Opens X.carrier)
    (c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj
        (X.restrict (Opens.isOpenEmbedding (X := X.carrier) U)).presheaf)
    (g : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat h).obj X.presheaf)
    (hg : ∀ (V : Opens Y.carrier),
      g.app (op V) ≫ X.presheaf.map
        (Opens.infLERight U ((Opens.map h).obj V)).op = localComponent h U c V) :
    (X.ofRestrict (Opens.isOpenEmbedding (X := X.carrier) U)) ≫
        ({ base := h, c := g } : X ⟶ Y) =
      ({ base := U.inclusion' ≫ h, c := c } :
        (X.restrict (Opens.isOpenEmbedding (X := X.carrier) U)) ⟶
          Y) := by
  apply PresheafedSpace.hext (X.ofRestrict (Opens.isOpenEmbedding (X := X.carrier) U) ≫
    ({ base := h, c := g } : X ⟶ Y))
    ({ base := U.inclusion' ≫ h, c := c } : X.restrict
      (Opens.isOpenEmbedding (X := X.carrier) U) ⟶ Y) rfl
  apply heq_of_eq
  apply NatTrans.ext
  funext Q
  rcases Q with ⟨V⟩
  change g.app (op V) ≫ X.presheaf.map
    (U.isOpenEmbedding.isOpenMap.adjunction.counit.app ((Opens.map h).obj V)).op =
      c.app (op V)
  apply (cancel_mono (X.presheaf.map
    (eqToHom (congrArg op (image_restricted_preimage U h V))))).mp
  rw [Category.assoc,← X.presheaf.map_comp]
  have he :
      (U.isOpenEmbedding.isOpenMap.adjunction.counit.app ((Opens.map h).obj V)).op ≫
        eqToHom (congrArg op (image_restricted_preimage U h V)) =
      (Opens.infLERight U ((Opens.map h).obj V)).op := Subsingleton.elim _ _
  rw [he]
  exact hg V

/-- Converse of the exact FULL restriction equation, on actual native
components. The equality transports only along existing maps of opens. -/
private theorem full_restriction_components_of_equation
    {X Y : PresheafedSpace CommRingCat.{0}} (h : X.carrier ⟶ Y.carrier)
    (U : Opens X.carrier)
    (c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      (U.inclusion' ≫ h)).obj (X.restrict U.isOpenEmbedding).presheaf)
    (g : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat h).obj X.presheaf)
    (he : X.ofRestrict U.isOpenEmbedding ≫ ({ base := h, c := g } : X ⟶ Y) =
      ({ base := U.inclusion' ≫ h, c := c } : X.restrict U.isOpenEmbedding ⟶ Y))
    (V : Opens Y.carrier) :
    g.app (op V) ≫ X.presheaf.map (Opens.infLERight U ((Opens.map h).obj V)).op =
      localComponent h U c V := by
  have hc := components_eq_of_fixed_base (X := X.restrict U.isOpenEmbedding) (Y := Y)
    (U.inclusion' ≫ h)
    ((X.ofRestrict U.isOpenEmbedding ≫ ({ base := h, c := g } : X ⟶ Y)).c) c he
  have ha := congrArg (fun k => k.app (op V)) hc
  change g.app (op V) ≫ X.presheaf.map
    (U.isOpenEmbedding.isOpenMap.adjunction.counit.app ((Opens.map h).obj V)).op = c.app (op V) at ha
  let e := eqToHom (congrArg op (image_restricted_preimage U h V))
  have hat := congrArg (fun k => k ≫ X.presheaf.map e) ha
  exact (map_path_comp X.presheaf (g.app (op V)) _ e
    (Opens.infLERight U ((Opens.map h).obj V)).op (Subsingleton.elim _ _)).symm.trans hat

private theorem presheaf_components_ext_on_cover {X Y : LocallyRingedSpace.{0}}
    (h : X.toTopCat ⟶ Y.toTopCat) {ι : Type} (U : ι → Opens X.toTopCat)
    (hcover : (⊤ : Opens X.toTopCat) ≤ iSup U)
    (c d : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat h).obj X.presheaf)
    (he : ∀ i, X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫
        ({ base := h, c := c } : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) =
      X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫
        ({ base := h, c := d } : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)) : c = d := by
  apply NatTrans.ext
  funext Q
  rcases Q with ⟨V⟩
  have hVcover : (Opens.map h).obj V ≤ ⨆ i, U i ⊓ (Opens.map h).obj V := by
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : Opens X.toTopCat) by trivial))
    exact Opens.mem_iSup.mpr ⟨i,hi,hx⟩
  apply ring_hom_ext_on_cover X.sheaf (Y.presheaf.obj (op V))
    (fun i => U i ⊓ (Opens.map h).obj V) ((Opens.map h).obj V)
    (fun i => Opens.infLERight (U i) ((Opens.map h).obj V)) hVcover
  intro i
  let ci := (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫
    ({ base := h, c := c } : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)).c
  exact (full_restriction_components_of_equation h (U i) ci c rfl V).trans
    (full_restriction_components_of_equation h (U i) ci d (he i).symm V).symm

private theorem native_hom_ext_on_cover {X Y : LocallyRingedSpace.{0}}
    {ι : Type} (U : ι → Opens X.toTopCat) (hcover : (⊤ : Opens X.toTopCat) ≤ iSup U)
    (F G : X ⟶ Y)
    (he : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ F =
      X.ofRestrict (U i).isOpenEmbedding ≫ G) : F = G := by
  have hb : F.base = G.base := by
    ext x
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : Opens X.toTopCat) by trivial))
    exact congrArg (fun k : X.restrict (U i).isOpenEmbedding ⟶ Y => k.base ⟨x,hi⟩) (he i)
  obtain ⟨c,hc⟩ := exists_components_of_base_eq F.toHom F.base rfl
  obtain ⟨d,hd⟩ := exists_components_of_base_eq G.toHom F.base hb.symm
  have hcd : c = d := presheaf_components_ext_on_cover F.base U hcover c d (by
    intro i
    rw [hc,hd]
    exact congrArg LocallyRingedSpace.Hom.toHom (he i))
  apply LocallyRingedSpace.Hom.ext'
  exact hc.symm.trans ((congrArg (fun k =>
    ({ base := F.base, c := k } : X.toPresheafedSpace ⟶ Y.toPresheafedSpace)) hcd).trans hd)

/-- Full native gluing of internally normalized LOCAL maps. The public UP
will produce this descent data from the ordinary original analytic cone. -/
private theorem exists_glued_native_hom {X Y : LocallyRingedSpace.{0}}
    (h : X.toTopCat ⟶ Y.toTopCat) {ι : Type} (U : ι → Opens X.toTopCat)
    (hcover : (⊤ : Opens X.toTopCat) ≤ iSup U)
    (f : ∀ i, X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i)) ⟶ Y)
    (c : ∀ i, Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat
      ((U i).inclusion' ≫ h)).obj
        (X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).presheaf)
    (hcf : ∀ i, ({ base := (U i).inclusion' ≫ h, c := c i } :
      (X.restrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).toPresheafedSpace ⟶
        Y.toPresheafedSpace) = (f i).toHom)
    (hcompat : ∀ (V : Opens Y.toTopCat) (i j : ι),
      localComponent h (U i) (c i) V ≫ X.presheaf.map (Opens.infLELeft
        (U i ⊓ (Opens.map h).obj V) (U j ⊓ (Opens.map h).obj V)).op =
      localComponent h (U j) (c j) V ≫ X.presheaf.map (Opens.infLERight
        (U i ⊓ (Opens.map h).obj V) (U j ⊓ (Opens.map h).obj V)).op) :
    ∃ F : X ⟶ Y, F.base = h ∧
      ∀ i, X.ofRestrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i)) ≫ F = f i := by
  obtain ⟨g,hg⟩ := exists_glued_presheaf_map X.toSheafedSpace.sheaf Y.presheaf h U hcover
    (fun i V => localComponent h (U i) (c i) V) hcompat
    (fun i _ _ j => localComponent_naturality h (U i) (c i) j)
  let gp : X.toPresheafedSpace ⟶ Y.toPresheafedSpace := { base := h, c := g }
  have heq (i : ι) :
      (X.ofRestrict (Opens.isOpenEmbedding (X := X.toTopCat) (U i))).toHom ≫ gp =
        (f i).toHom :=
    (full_restriction_equation_of_components h (U i) (c i) g (hg i)).trans (hcf i)
  let F := nativeHomOfLocal U hcover gp f heq
  refine ⟨F,rfl,?_⟩
  intro i
  apply LocallyRingedSpace.Hom.ext'
  exact heq i

section RawChartMaps

variable {n m l : ℕ} {M N P : Type}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  [ChartedSpace (ComplexModel l) P] [IsComplexManifold l P]

/-- Private bookkeeping on the INDEPENDENT328 charts. This is only a RING
homomorphism; genuine complex linearity is derived from the full scalar
square by the neighborhood parent, never assumed for bare LRS maps. -/
private def chartRingHom (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (x : C.zeroLocus) :
    (HolGerm (ComplexModel m) ⧸ wholeChartStalkIdeal A
      (F.base x).val (F.base x).val (mem_chart_source _ _)) →+*
      (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal C
        x.val x.val (mem_chart_source _ _)) :=
  (quotientStalkChartEquiv C hC x).toRingHom.comp
    ((F.stalkMap x).hom.comp (quotientStalkChartEquiv A hA (F.base x)).symm.toRingHom)

private def rawChartRingHom (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (x : C.zeroLocus) :
    HolGerm (ComplexModel m) →+* (HolGerm (ComplexModel n) ⧸
      wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)) :=
  (chartRingHom C hC A hA F x).comp (Ideal.Quotient.mk _)

/-- Native stalk composition and BOTH original chart inverse identities;
the raw analytic domain agrees before transporting image-point ideals. -/
private theorem rawChartRingHom_comp (C : GermIdeal n M) (hC : C.IsCoherent)
    (A : GermIdeal m N) (hA : A.IsCoherent) (B : GermIdeal l P) (hB : B.IsCoherent)
    (F : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (G : quotientLocallyRingedSpace A hA ⟶ quotientLocallyRingedSpace B hB)
    (x : C.zeroLocus) (r : HolGerm (ComplexModel l)) :
    rawChartRingHom C hC B hB (F ≫ G) x r =
      chartRingHom C hC A hA F x (rawChartRingHom A hA B hB G (F.base x) r) := by
  let EC := quotientStalkChartEquiv C hC x
  let EA := quotientStalkChartEquiv A hA (F.base x)
  let EB := quotientStalkChartEquiv B hB (G.base (F.base x))
  change EC ((F ≫ G).stalkMap x (EB.symm (Ideal.Quotient.mk _ r))) =
    EC (F.stalkMap x (EA.symm (EA
      (G.stalkMap (F.base x) (EB.symm (Ideal.Quotient.mk _ r))))))
  rw [RingEquiv.symm_apply_apply,LocallyRingedSpace.stalkMap_comp]
  rfl

end RawChartMaps

section AnalyticTest

variable {r d b t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel r) M] [IsComplexManifold r M]
  {U : Opens (ComplexModel (d+t))} {V : Opens (ComplexModel b)}
  (φ : V → ComplexModel d)
  (hφ : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel d) ∞ φ)
  (C : GermIdeal r M) (hC : C.IsCoherent)
  (A : GermIdeal (d+t) U) (hA : A.IsCoherent)
  (q : GermIdeal b V) (hq : q.IsCoherent)

private theorem tangentPullback_coordinate (i : Fin b) :
    tangentPullback b t (coordinateGerm i) = coordinateGerm (i.castAdd t) := by
  unfold tangentPullback HironakaHolomorphicJetMonomialSpan.coordinateGerm
  rw [HironakaHolomorphicJetChartInvariance.compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun _ => rfl

private theorem raw_baseProjection_mk
    (x : (jointIdeal d b t φ hφ A q).zeroLocus) (r : HolGerm (ComplexModel b)) :
    rawChartRingHom (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq) q hq
        (baseQuotientProjection d b t φ hφ A hA q hq) x r =
      Ideal.Quotient.mk _ (tangentPullback b t r) :=
  baseQuotientProjection_chart_mk d b t φ hφ A hA q hq x r

private theorem raw_sourceProjection_normal
    (x : (jointIdeal d b t φ hφ A q).zeroLocus) (i : Fin t) :
    rawChartRingHom (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq) A hA
        (sourceQuotientProjection d b t φ hφ A hA q hq) x (normalCoordinate d t i) =
      Ideal.Quotient.mk _ (normalCoordinate b t i) := by
  have hs := sourceQuotientProjection_chart_mk d b t φ hφ A hA q hq x
    (normalCoordinate d t i)
  exact hs.trans (congrArg (Ideal.Quotient.mk _)
    (jointBasePullback_normalCoordinate d b t
      (actualTranslatedMap (n := d) (m := b) φ
        (baseProjection d b t U V φ hφ x.val))
      (actualTranslatedMap_holomorphic hφ _) (actualTranslatedMap_zero φ _) i))

/-- Both FULL original projection equations determine every raw joint
coordinate class. No scalar, reducedness or point-faithfulness shortcut is
used here; genuine complex linearity enters only in the later185 step. -/
private theorem raw_coordinates_eq_of_projection_composites
    (F G : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hs : F ≫ sourceQuotientProjection d b t φ hφ A hA q hq =
      G ≫ sourceQuotientProjection d b t φ hφ A hA q hq)
    (hp : F ≫ baseQuotientProjection d b t φ hφ A hA q hq =
      G ≫ baseQuotientProjection d b t φ hφ A hA q hq)
    (x : C.zeroLocus) (i : Fin (b+t)) :
    rawChartRingHom C hC _ (jointIdeal_coherent d b t φ hφ A hA q hq) F x (coordinateGerm i) =
      rawChartRingHom C hC _ (jointIdeal_coherent d b t φ hφ A hA q hq) G x (coordinateGerm i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have hh := congrArg (fun f : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace q hq => rawChartRingHom C hC q hq f x (coordinateGerm j)) hp
    rw [rawChartRingHom_comp,rawChartRingHom_comp,
      raw_baseProjection_mk,raw_baseProjection_mk,tangentPullback_coordinate] at hh
    exact hh
  · have hh := congrArg (fun f : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace A hA => rawChartRingHom C hC A hA f x (normalCoordinate d t j)) hs
    have hf := rawChartRingHom_comp C hC _
      (jointIdeal_coherent d b t φ hφ A hA q hq) A hA F
      (sourceQuotientProjection d b t φ hφ A hA q hq) x (normalCoordinate d t j)
    have hg := rawChartRingHom_comp C hC _
      (jointIdeal_coherent d b t φ hφ A hA q hq) A hA G
      (sourceQuotientProjection d b t φ hφ A hA q hq) x (normalCoordinate d t j)
    exact (hf.trans (congrArg (chartRingHom C hC _
      (jointIdeal_coherent d b t φ hφ A hA q hq) F x)
        (raw_sourceProjection_normal φ hφ A hA q hq (F.base x) j))).symm.trans
      (hh.trans (hg.trans (congrArg (chartRingHom C hC _
        (jointIdeal_coherent d b t φ hφ A hA q hq) G x)
          (raw_sourceProjection_normal φ hφ A hA q hq (G.base x) j))))

private def coneSupportPair
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ)
    (x : C.zeroLocus) : supportPairs d b t φ A q :=
  ⟨(a.base x,β.base x),by
    have hp := congrArg (fun f : quotientLocallyRingedSpace C hC ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) (ComplexModel d) => f.base x) hcomm
    exact hp⟩

private theorem coneSupportPair_continuous
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ) :
    Continuous (coneSupportPair φ hφ C hC A hA q hq a β hcomm) := by
  apply Continuous.subtype_mk
  exact a.base.hom.continuous.prodMk β.base.hom.continuous

/-- The full original cone internally determines its actual continuous
point factor, independently of every choice of local analytic lifts. -/
private def conePointMap
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ) :
    (quotientLocallyRingedSpace C hC).toTopCat ⟶
      (quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq)).toTopCat :=
  TopCat.ofHom ⟨fun x => (supportPairHomeomorph d b t φ hφ A hA q hq).symm
      (coneSupportPair φ hφ C hC A hA q hq a β hcomm x),
    (supportPairHomeomorph d b t φ hφ A hA q hq).symm.continuous.comp
      (coneSupportPair_continuous φ hφ C hC A hA q hq a β hcomm)⟩

/-- On actual analytic test quotients, the two FULL native projections
jointly determine every complex-compatible FULL morphism. -/
theorem factor_hom_ext
    (F G : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hF : F ≫ quotientPointMap _ (jointIdeal_coherent d b t φ hφ A hA q hq) =
      quotientPointMap C hC)
    (hG : G ≫ quotientPointMap _ (jointIdeal_coherent d b t φ hφ A hA q hq) =
      quotientPointMap C hC)
    (hs : F ≫ sourceQuotientProjection d b t φ hφ A hA q hq =
      G ≫ sourceQuotientProjection d b t φ hφ A hA q hq)
    (hp : F ≫ baseQuotientProjection d b t φ hφ A hA q hq =
      G ≫ baseQuotientProjection d b t φ hφ A hA q hq) : F = G := by
  let J := jointIdeal d b t φ hφ A q
  let hJ := jointIdeal_coherent d b t φ hφ A hA q hq
  have hbase : F.base = G.base := by
    ext x
    apply (supportPairHomeomorph d b t φ hφ A hA q hq).injective
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun f : quotientLocallyRingedSpace C hC ⟶
        quotientLocallyRingedSpace A hA => f.base x) hs
    · exact congrArg (fun f : quotientLocallyRingedSpace C hC ⟶
        quotientLocallyRingedSpace q hq => f.base x) hp
  apply quotientHom_ext_chart C hC J hJ F G hF hG hbase
  intro x g
  let IC := wholeChartStalkIdeal C x.val x.val (mem_chart_source _ _)
  let IF := wholeChartStalkIdeal J (F.base x).val (F.base x).val (mem_chart_source _ _)
  let IG := wholeChartStalkIdeal J (G.base x).val (G.base x).val (mem_chart_source _ _)
  let T := HolGerm (ComplexModel r) ⧸ IC
  let : IsNoetherianRing (HolGerm (ComplexModel r)) := isNoetherianRing_holGerm_euclidean r
  let : IsNoetherianRing T := inferInstance
  let : IsLocalRing T := chartQuotient_isLocalRing C x
  let : IsLocalRing (HolGerm (ComplexModel (b+t)) ⧸ IF) := chartQuotient_isLocalRing J (F.base x)
  let : IsLocalRing (HolGerm (ComplexModel (b+t)) ⧸ IG) := chartQuotient_isLocalRing J (G.base x)
  let : IsLocalHom (Ideal.Quotient.mk IF) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk IG) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let f : HolGerm (ComplexModel (b+t)) →ₐ[ℂ] T :=
    (quotientChartStalkAlgHom C hC J hJ F hF x).comp (Ideal.Quotient.mkₐ ℂ IF)
  let g' : HolGerm (ComplexModel (b+t)) →ₐ[ℂ] T :=
    (quotientChartStalkAlgHom C hC J hJ G hG x).comp (Ideal.Quotient.mkₐ ℂ IG)
  let : IsLocalHom f.toRingHom := by
    change IsLocalHom ((quotientChartStalkAlgHom C hC J hJ F hF x).toRingHom.comp (Ideal.Quotient.mk IF))
    infer_instance
  let : IsLocalHom g'.toRingHom := by
    change IsLocalHom ((quotientChartStalkAlgHom C hC J hJ G hG x).toRingHom.comp (Ideal.Quotient.mk IG))
    infer_instance
  have he : f = g' := local_algHom_ext_coordinates (b+t) f g' (fun i =>
    raw_coordinates_eq_of_projection_composites φ hφ C hC A hA q hq F G hs hp x i)
  exact congrArg (fun a : HolGerm (ComplexModel (b+t)) →ₐ[ℂ] T => a g) he

private theorem baseProjection_point :
    baseQuotientProjection d b t φ hφ A hA q hq ≫ quotientPointMap q hq =
      quotientPointMap (jointIdeal d b t φ hφ A q) (jointIdeal_coherent d b t φ hφ A hA q hq) :=
  quotientMap_point (baseProjection_holomorphic d b t U V φ hφ) _
    (jointIdeal_coherent d b t φ hφ A hA q hq) q hq
    (RestrictedIdealExtension.le_sumIdeal_right (GermIdealPullbackCalculus.isCoherent_pullback (baseProjection_holomorphic d b t U V φ hφ) hq))

/-- Every competitor with the base triangle has genuine complex scalars;
the final uniqueness predicate need not assume them separately. -/
private theorem factor_point
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hβ : β ≫ quotientPointMap q hq = quotientPointMap C hC)
    (F : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hp : F ≫ baseQuotientProjection d b t φ hφ A hA q hq = β) :
    F ≫ quotientPointMap _ (jointIdeal_coherent d b t φ hφ A hA q hq) = quotientPointMap C hC := by
  calc
    _ = F ≫ (baseQuotientProjection d b t φ hφ A hA q hq ≫ quotientPointMap q hq) :=
      congrArg (fun k => F ≫ k) (baseProjection_point φ hφ A hA q hq).symm
    _ = (F ≫ baseQuotientProjection d b t φ hφ A hA q hq) ≫ quotientPointMap q hq :=
      (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun k => k ≫ quotientPointMap q hq) hp).trans hβ

private theorem nativeRestrictionMap_triangle {X Y Z : LocallyRingedSpace.{0}}
    (W U : Opens X.toTopCat) (hWU : W ≤ U)
    (F : X.restrict U.isOpenEmbedding ⟶ Y) (s : Y ⟶ Z) (a : X ⟶ Z)
    (hs : F ≫ s = X.ofRestrict U.isOpenEmbedding ≫ a) :
    (nativeRestrictionMap X W U hWU ≫ F) ≫ s = X.ofRestrict W.isOpenEmbedding ≫ a := by
  rw [Category.assoc,hs,←Category.assoc,nativeRestrictionMap_fac]

/-- Genuine overlap uniqueness: the literal intersection restriction is
an actual analytic test quotient through the independent1010 isomorphism. -/
private theorem overlap_factor_eq
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hβ : β ≫ quotientPointMap q hq = quotientPointMap C hC)
    (O P : Opens M)
    (F : quotientOpenRestriction C hC O ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (G : quotientOpenRestriction C hC P ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hFs : F ≫ sourceQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC O ≫ a)
    (hFp : F ≫ baseQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC O ≫ β)
    (hGs : G ≫ sourceQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC P ≫ a)
    (hGp : G ≫ baseQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC P ≫ β) :
    nativeRestrictionMap (quotientLocallyRingedSpace C hC)
        (quotientCarrierOpen C hC O ⊓ quotientCarrierOpen C hC P)
        (quotientCarrierOpen C hC O) inf_le_left ≫ F =
      nativeRestrictionMap (quotientLocallyRingedSpace C hC)
        (quotientCarrierOpen C hC O ⊓ quotientCarrierOpen C hC P)
        (quotientCarrierOpen C hC P) inf_le_right ≫ G := by
  let X := quotientLocallyRingedSpace C hC
  let UO := quotientCarrierOpen C hC O
  let UP := quotientCarrierOpen C hC P
  let D := quotientOpenIdeal C (O ⊓ P)
  let hD := quotientOpenIdeal_coherent C hC (O ⊓ P)
  let e : quotientLocallyRingedSpace D hD ≅ X.restrict (UO ⊓ UP).isOpenEmbedding :=
    quotientOpenIso C hC (O ⊓ P)
  let F' := nativeRestrictionMap X (UO ⊓ UP) UO inf_le_left ≫ F
  let G' := nativeRestrictionMap X (UO ⊓ UP) UP inf_le_right ≫ G
  have hcut (Z : LocallyRingedSpace.{0}) (s : _ ⟶ Z) (a₀ : X ⟶ Z)
      (hF : F ≫ s = X.ofRestrict UO.isOpenEmbedding ≫ a₀)
      (hG : G ≫ s = X.ofRestrict UP.isOpenEmbedding ≫ a₀) :
      (e.hom ≫ F') ≫ s = quotientOpenMap C hC (O ⊓ P) ≫ a₀ ∧
      (e.hom ≫ G') ≫ s = quotientOpenMap C hC (O ⊓ P) ≫ a₀ := by
    constructor
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.hom ≫ k)
          (nativeRestrictionMap_triangle (UO ⊓ UP) UO inf_le_left F s a₀ hF)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ a₀) (quotientOpenIso_hom_inclusion C hC (O ⊓ P)))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.hom ≫ k)
          (nativeRestrictionMap_triangle (UO ⊓ UP) UP inf_le_right G s a₀ hG)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ a₀) (quotientOpenIso_hom_inclusion C hC (O ⊓ P)))))
  have hs := hcut _ (sourceQuotientProjection d b t φ hφ A hA q hq) a hFs hGs
  have hp := hcut _ (baseQuotientProjection d b t φ hφ A hA q hq) β hFp hGp
  have hβ' : (quotientOpenMap C hC (O ⊓ P) ≫ β) ≫ quotientPointMap q hq = quotientPointMap D hD :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => quotientOpenMap C hC (O ⊓ P) ≫ k) hβ).trans
      (quotientOpenMap_point C hC (O ⊓ P)))
  apply (cancel_epi e.hom).mp
  exact factor_hom_ext φ hφ D hD A hA q hq (e.hom ≫ F') (e.hom ≫ G')
    (factor_point φ hφ D hD A hA q hq _ hβ' _ hp.1)
    (factor_point φ hφ D hD A hA q hq _ hβ' _ hp.2)
    (hs.1.trans hs.2.symm) (hp.1.trans hp.2.symm)

private theorem relative_factor_base
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ)
    {Z : LocallyRingedSpace.{0}} (k : Z ⟶ quotientLocallyRingedSpace C hC)
    (F : Z ⟶ quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
      (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hs : F ≫ sourceQuotientProjection d b t φ hφ A hA q hq = k ≫ a)
    (hp : F ≫ baseQuotientProjection d b t φ hφ A hA q hq = k ≫ β) :
    F.base = k.base ≫ conePointMap φ hφ C hC A hA q hq a β hcomm := by
  ext x
  apply (supportPairHomeomorph d b t φ hφ A hA q hq).injective
  change (supportPairHomeomorph d b t φ hφ A hA q hq) (F.base x) =
    (supportPairHomeomorph d b t φ hφ A hA q hq)
      ((supportPairHomeomorph d b t φ hφ A hA q hq).symm
        (coneSupportPair φ hφ C hC A hA q hq a β hcomm (k.base x)))
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun f : Z ⟶ quotientLocallyRingedSpace A hA => f.base x) hs
  · exact congrArg (fun f : Z ⟶ quotientLocallyRingedSpace q hq => f.base x) hp

/-- PRIVATE native descent assembly. The final public producer will derive
the actual local maps and cover from the ordinary analytic test cone. -/
private theorem exists_factor_of_open_factors
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (hβ : β ≫ quotientPointMap q hq = quotientPointMap C hC)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ)
    {ι : Type} (O : ι → Opens M)
    (hcover : (⊤ : Opens (quotientLocallyRingedSpace C hC).toTopCat) ≤
      ⨆ i, quotientCarrierOpen C hC (O i))
    (f : ∀ i, quotientOpenRestriction C hC (O i) ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq))
    (hs : ∀ i, f i ≫ sourceQuotientProjection d b t φ hφ A hA q hq =
      quotientOpenInclusion C hC (O i) ≫ a)
    (hp : ∀ i, f i ≫ baseQuotientProjection d b t φ hφ A hA q hq =
      quotientOpenInclusion C hC (O i) ≫ β) :
    ∃ F : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq),
      F ≫ sourceQuotientProjection d b t φ hφ A hA q hq = a ∧
      F ≫ baseQuotientProjection d b t φ hφ A hA q hq = β := by
  classical
  let X := quotientLocallyRingedSpace C hC
  let Y := quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
    (jointIdeal_coherent d b t φ hφ A hA q hq)
  let UO : ι → Opens X.toTopCat := fun i => quotientCarrierOpen C hC (O i)
  let h := conePointMap φ hφ C hC A hA q hq a β hcomm
  have hb (i : ι) : (f i).base = (UO i).inclusion' ≫ h :=
    relative_factor_base φ hφ C hC A hA q hq a β hcomm
      (quotientOpenInclusion C hC (O i)) (f i) (hs i) (hp i)
  choose c hc using fun i => exists_components_of_base_eq (f i).toHom
    ((UO i).inclusion' ≫ h) (hb i)
  have hcompat (V₀ : Opens Y.toTopCat) (i j : ι) :
      localComponent h (UO i) (c i) V₀ ≫ X.presheaf.map (Opens.infLELeft
        (UO i ⊓ (Opens.map h).obj V₀) (UO j ⊓ (Opens.map h).obj V₀)).op =
      localComponent h (UO j) (c j) V₀ ≫ X.presheaf.map (Opens.infLERight
        (UO i ⊓ (Opens.map h).obj V₀) (UO j ⊓ (Opens.map h).obj V₀)).op :=
    native_overlap_implies_local_components h (UO i) (UO j) (f i) (f j) (c i) (c j)
      (hc i) (hc j) (overlap_factor_eq φ hφ C hC A hA q hq a β hβ (O i) (O j)
        (f i) (f j) (hs i) (hp i) (hs j) (hp j)) V₀
  obtain ⟨F,_hFbase,hF⟩ := exists_glued_native_hom h UO hcover f c hc hcompat
  refine ⟨F,?_,?_⟩
  · apply native_hom_ext_on_cover UO hcover
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ sourceQuotientProjection d b t φ hφ A hA q hq) (hF i)).trans (hs i))
  · apply native_hom_ext_on_cover UO hcover
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ baseQuotientProjection d b t φ hφ A hA q hq) (hF i)).trans (hp i))

/-- Actual analytic-test fibreproduct universality for the original WHOLE
nonreduced joint ideal. Every local lift, ideal condition, factor and gluing
equation is derived from the ordinary FULL genuine-complex test cone. -/
theorem exists_unique_joint_factor
    (a : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace A hA)
    (β : quotientLocallyRingedSpace C hC ⟶ quotientLocallyRingedSpace q hq)
    (ha : a ≫ quotientPointMap A hA = quotientPointMap C hC)
    (hβ : β ≫ quotientPointMap q hq = quotientPointMap C hC)
    (hcomm : a ≫ quotientInclusion A hA ≫
        ChartedSpace.locallyRingedSpaceMap (fun y : U => tangentProjection d t y.val)
          ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val) =
      β ≫ quotientInclusion q hq ≫ ChartedSpace.locallyRingedSpaceMap φ hφ) :
    ∃! F : quotientLocallyRingedSpace C hC ⟶
      quotientLocallyRingedSpace (jointIdeal d b t φ hφ A q)
        (jointIdeal_coherent d b t φ hφ A hA q hq),
      F ≫ sourceQuotientProjection d b t φ hφ A hA q hq = a ∧
      F ≫ baseQuotientProjection d b t φ hφ A hA q hq = β := by
  classical
  let J := jointIdeal d b t φ hφ A q
  let hJ := jointIdeal_coherent d b t φ hφ A hA q hq
  let Y := quotientLocallyRingedSpace J hJ
  have hlocal (x : C.zeroLocus) :
      ∃ (O : Opens M) (_hx : x.val ∈ O) (f : quotientOpenRestriction C hC O ⟶ Y),
        f ≫ sourceQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC O ≫ a ∧
        f ≫ baseQuotientProjection d b t φ hφ A hA q hq = quotientOpenInclusion C hC O ≫ β := by
    obtain ⟨O,hx,H,hH,hCJ,hs,hp⟩ :=
      HironakaAnalyticBaseChangeLocalFactorization.exists_local_joint_factor
        d b t U V φ hφ A hA q hq C hC a β ha hβ hcomm x
    let L := quotientMap hH (quotientOpenIdeal C O) (quotientOpenIdeal_coherent C hC O) J hJ hCJ
    let e := quotientOpenIso C hC O
    refine ⟨O,hx,e.inv ≫ L,?_,?_⟩
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hs).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ a) (quotientOpenIso_inv_inclusion C hC O))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => e.inv ≫ k) hp).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ β) (quotientOpenIso_inv_inclusion C hC O))))
  choose O hx f hs hp using hlocal
  have hcover : (⊤ : Opens (quotientLocallyRingedSpace C hC).toTopCat) ≤
      ⨆ x, quotientCarrierOpen C hC (O x) := by
    intro x _hx
    exact Opens.mem_iSup.mpr ⟨x,hx x⟩
  obtain ⟨F,hFs,hFp⟩ := exists_factor_of_open_factors φ hφ C hC A hA q hq
    a β hβ hcomm O hcover f hs hp
  refine ⟨F,⟨hFs,hFp⟩,?_⟩
  intro G hG
  exact factor_hom_ext φ hφ C hC A hA q hq G F
    (factor_point φ hφ C hC A hA q hq β hβ G hG.2)
    (factor_point φ hφ C hC A hA q hq β hβ F hFp)
    (hG.1.trans hFs.symm) (hG.2.trans hFp.symm)

end AnalyticTest

end Hironaka.HironakaAnalyticTestBaseChangeUniversality
