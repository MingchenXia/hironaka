import Hironaka.Resolution.HironakaChowNativeLocalOverFreeKernelCoherence
import Hironaka.Resolution.HironakaChowNativeLocalOverFiniteDataTransport
import Hironaka.Resolution.HironakaChowNativeGeneratorNeighborhood
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! Whole native kernel coherence, from ordinary local finite presentations.
BP FIRST: hironaka-g10-native-finite-presentation-kernel-coherence.tex.
Generic native finite-data transport below receives zero analytic-engine credit. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
namespace Hironaka.HironakaChowNativeFinitePresentationKernelCoherence
open HironakaChowNativeFreePartContinuation HironakaChowNativeArbitraryOverRealization
  HironakaChowNativeLocalOverFiniteDataTransport
  HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeGeneratorNeighborhood
  HironakaChowNativeModuleStalkExact HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk

private theorem realization_preservesZero (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) : (realizationEquivalence X U).functor.PreservesZeroMorphisms where
  map_zero M N := by
    ext T m
    rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem local_return_preservesZero (X : LocallyRingedSpace.{0})
    (U : Opens X.toTopCat) (V : Opens (TopCat.of U)) :
    (localModuleEquivalence X U V).inverse.PreservesZeroMorphisms where
  map_zero M N := by
    ext T m
    rfl


-- The actual native Presentation.map retains the original two finite index sets.
private theorem presentation_map_finite
    {C D : Type} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{0}} {S : Sheaf K RingCat.{0}}
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [HasSheafify K AddCommGrpCat.{0}] [K.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M : SheafOfModules.{0} R} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{0} R ⥤ SheafOfModules.{0} S)
    [PreservesColimitsOfSize.{0,0} F] (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by change Finite P.generators.I; infer_instance⟩
  isFiniteType_relations := ⟨by change Finite P.relations.I; infer_instance⟩

private theorem finitePresentation_of_iso
    {C : Type} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M N : SheafOfModules.{0} R} (e : M ≅ N) (hM : M.IsFinitePresentation) :
    N.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation R).prop_of_iso e hM

private theorem native_over_rightAdjoint
    {C : Type} [Category.{0} C] [HasBinaryProducts C] [HasPullbacks C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (U : C) : (SheafOfModules.overFunctor.{0} R U).IsRightAdjoint := by
  let φ : R.over U ⟶
      ((Over.forget U).sheafPushforwardContinuous RingCat.{0} (J.over U) J).obj R := 𝟙 _
  have : (PresheafOfModules.pushforward.{0} (F := Over.forget U) φ.hom).IsRightAdjoint := by
    exact inferInstanceAs ((PresheafOfModules.pushforward.{0}
      (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R.obj))).IsRightAdjoint)
  change (SheafOfModules.pushforward.{0} φ).IsRightAdjoint
  exact (SheafOfModules.PullbackConstruction.adjunction φ).isRightAdjoint


private theorem free_isFiniteType
    {C : Type} [Category C] [HasBinaryProducts C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (I : Type) [Finite I] : (SheafOfModules.free (R := R) I).IsFiniteType := by
  let M := SheafOfModules.free (R := R) I
  let G : M.GeneratingSections := {
    I := I
    s := M.freeHomEquiv (𝟙 M)
    epi := by
      rw [Equiv.symm_apply_apply]
      infer_instance }
  refine ⟨G.localGeneratorsData,⟨fun i => ⟨?_⟩⟩⟩
  change Finite I
  infer_instance

-- Whole block-kernel surjectivity follows from the actual presentation's
-- universal property. The held abelian pushout/kernel theorem is reused.
private theorem relation_block_isPushout
    {C : Type*} [Category* C] [Abelian C] {A B D M N : C}
    (m : A ⟶ M) [Epi m] (ρ : D ⟶ B) (n : B ⟶ N)
    (hρ : ρ ≫ n = 0) (hn : IsColimit (CokernelCofork.ofπ n hρ))
    (L : A ⟶ B) (f : M ⟶ N) (hL : L ≫ n = m ≫ f) :
    IsPushout (coprod.desc L (-ρ)) (coprod.desc m 0) n f := by
  let H := coprod.desc L (-ρ)
  let p : A ⨿ D ⟶ M := coprod.desc m 0
  have hw : H ≫ n = p ≫ f := by
    dsimp only [H,p]
    rw [coprod.desc_comp,coprod.desc_comp,hL,Preadditive.neg_comp,hρ,neg_zero,zero_comp]
  have hrel (s : PushoutCocone H p) : ρ ≫ s.inl = 0 := by
    have h := congrArg (fun k => (coprod.inr : D ⟶ A ⨿ D) ≫ k) s.condition
    dsimp only [H,p] at h
    simp only [← Category.assoc,coprod.inr_desc,Preadditive.neg_comp,zero_comp] at h
    exact neg_eq_zero.mp h
  let desc (s : PushoutCocone H p) : N ⟶ s.pt := (CokernelCofork.IsColimit.desc' hn s.inl (hrel s)).val
  have hd (s : PushoutCocone H p) : n ≫ desc s = s.inl :=
    (CokernelCofork.IsColimit.desc' hn s.inl (hrel s)).property
  have : Epi n := epi_of_isColimit_cofork hn
  apply IsPushout.of_isColimit' ⟨hw⟩
  refine PushoutCocone.IsColimit.mk hw desc hd ?_ ?_
  · intro s
    apply (cancel_epi m).mp
    have ha := congrArg (fun k => (coprod.inl : A ⟶ A ⨿ D) ≫ k) s.condition
    have ha' : L ≫ s.inl = m ≫ s.inr := by
      dsimp only [H,p] at ha
      simpa only [← Category.assoc,coprod.inl_desc] using ha
    calc
      m ≫ f ≫ desc s = L ≫ n ≫ desc s := by rw [← Category.assoc,← hL,Category.assoc]
      _ = m ≫ s.inr := by rw [hd,ha']
  · intro s k hk _
    exact (cancel_epi n).mp (hk.trans (hd s).symm)

private theorem relation_block_kernel_epi
    {C : Type*} [Category* C] [Abelian C] {A B D M N : C}
    (m : A ⟶ M) [Epi m] (ρ : D ⟶ B) (n : B ⟶ N)
    (hρ : ρ ≫ n = 0) (hn : IsColimit (CokernelCofork.ofπ n hρ))
    (L : A ⟶ B) (f : M ⟶ N) (hL : L ≫ n = m ≫ f) :
    Epi (kernel.map (coprod.desc L (-ρ)) f (coprod.desc m 0) n
      (relation_block_isPushout m ρ n hρ hn L f hL).w) :=
  Abelian.epi_kernel_map_of_isPushout (relation_block_isPushout m ρ n hρ hn L f hL)

-- Native finite generating sections and actual local covers; no new analytic engine.
private theorem finiteType_of_epi
    {C : Type} [Category C] [HasBinaryProducts C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M N : SheafOfModules.{0} R} (f : M ⟶ N) [Epi f] [M.IsFiniteType] :
    N.IsFiniteType := by
  obtain ⟨P,hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let Q : N.LocalGeneratorsData := {
    I := P.I
    X := P.X
    coversTop := P.coversTop
    generators i := by
      have : (SheafOfModules.overFunctor R (P.X i)).IsLeftAdjoint :=
        (SheafOfModules.overPushforwardOverAdj (R := R) (P.X i)).isLeftAdjoint
      have : Epi (f.over (P.X i)) := Functor.map_epi _ _
      exact (P.generators i).ofEpi (f.over (P.X i)) }
  refine ⟨Q,⟨fun i => ⟨?_⟩⟩⟩
  exact (hP.isFiniteType i).finite

-- Actual native site equivalences supply the nested sheafification proofs.
-- LOCAL instance attributes only: no imported instance or native object is replaced.
private theorem singleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0} :=
  U.overEquivalence.hasSheafify ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0}

private theorem doubleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (Over.iteratedSliceEquiv V).hasSheafify (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left) AddCommGrpCat.{0}

private theorem doubleOverAddGroupWeakSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (doubleOverAddGroupSheafify U V).isRightAdjoint

section NativeOpenOver
attribute [local instance] singleOverAddGroupSheafify doubleOverAddGroupSheafify doubleOverAddGroupWeakSheafify

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def flattenGenerators
    {X : TopCat.{0}} (R : X.Sheaf RingCat.{0})
    (M : SheafOfModules.{0} R) (U : Opens X) (V : Over U)
    (G : ((M.over U).over V).GeneratingSections) :
    (M.over V.left).GeneratingSections := by
  letI e := SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv V)
    (S := (R.over U).over V) (R := R.over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.obj.map_id _)
    (by ext : 2; exact R.obj.map_id _)
  exact (G.map e.inverse (Iso.refl _)).ofEpi
    (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over U).over V))).hom

private theorem flattenGenerators_finite
    {X : TopCat.{0}} (R : X.Sheaf RingCat.{0})
    (M : SheafOfModules.{0} R) (U : Opens X) (V : Over U)
    (G : ((M.over U).over V).GeneratingSections) (hG : G.IsFiniteType) :
    (flattenGenerators R M U V G).IsFiniteType := ⟨hG.finite⟩

private def pointGeneratorsData
    {X : TopCat.{0}} (R : X.Sheaf RingCat.{0})
    (M : SheafOfModules.{0} R) (U : X → Opens X) (hx : ∀ x, x ∈ U x)
    (D : ∀ x, (M.over (U x)).LocalGeneratorsData) : M.LocalGeneratorsData where
  I := (x : X) × (D x).I
  X i := ((D i.1).X i.2).left
  coversTop := by
    have hCover : (Opens.grothendieckTopology X).CoversTop U := by
      intro V
      apply (Opens.mem_grothendieckTopology X).mpr
      intro x hxV
      refine ⟨V ⊓ U x,homOfLE inf_le_left,?_,⟨hxV,hx x⟩⟩
      exact (Sieve.mem_ofObjects_iff U _).mpr ⟨x,⟨homOfLE inf_le_right⟩⟩
    exact hCover.over (fun x => (D x).coversTop)
  generators i := flattenGenerators R M (U i.1) ((D i.1).X i.2) ((D i.1).generators i.2)

private theorem pointGeneratorsData_finite
    {X : TopCat.{0}} (R : X.Sheaf RingCat.{0})
    (M : SheafOfModules.{0} R) (U : X → Opens X) (hx : ∀ x, x ∈ U x)
    (D : ∀ x, (M.over (U x)).LocalGeneratorsData) (hD : ∀ x, (D x).IsFiniteType) :
    (pointGeneratorsData R M U hx D).IsFiniteType := by
  refine ⟨fun i => ?_⟩
  exact flattenGenerators_finite R M (U i.1) ((D i.1).X i.2)
    ((D i.1).generators i.2) ((hD i.1).isFiniteType i.2)

private theorem finiteType_of_localFiniteType
    {X : TopCat.{0}} (R : X.Sheaf RingCat.{0}) (M : SheafOfModules.{0} R)
    (h : ∀ x : X, ∃ (U : Opens X), x ∈ U ∧ (M.over U).IsFiniteType) :
    M.IsFiniteType := by
  choose U hx hU using h
  have hData (x : X) : ∃ q : (M.over (U x)).LocalGeneratorsData, q.IsFiniteType :=
    @SheafOfModules.IsFiniteType.exists_localGeneratorsData _ _ _ _ _ _ (M.over (U x)) (hU x)
  choose D hD using hData
  exact ⟨pointGeneratorsData R M U hx D,pointGeneratorsData_finite R M U hx D hD⟩

end NativeOpenOver

private theorem exists_local_generators
    {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (forgetRing R)) [M.IsFiniteType] (x : X) :
    ∃ (U : Opens X), x ∈ U ∧ ∃ (G : (M.over U).GeneratingSections), G.IsFiniteType := by
  obtain ⟨P,hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨W,j,hW,hxW⟩ :=
    (Opens.mem_grothendieckTopology X).mp (P.coversTop ⊤) x (by trivial)
  obtain ⟨i,⟨k⟩⟩ := (Sieve.mem_ofObjects_iff P.X j).mp hW
  exact ⟨P.X i,k.le hxW,P.generators i,hP.isFiniteType i⟩

private theorem exists_local_presentation
    {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (forgetRing R)) [M.IsFinitePresentation] (x : X) :
    ∃ (U : Opens X), x ∈ U ∧ ∃ (P : (M.over U).Presentation), P.IsFinite := by
  obtain ⟨P,hP⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨W,j,hW,hxW⟩ :=
    (Opens.mem_grothendieckTopology X).mp (P.coversTop ⊤) x (by trivial)
  obtain ⟨i,⟨k⟩⟩ := (Sieve.mem_ofObjects_iff P.X j).mp hW
  exact ⟨P.X i,k.le hxW,P.presentation i,hP.isFinite_presentation i⟩

private def presentationOnSubopen
    {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (forgetRing R))
    (U V : Opens X) (hVU : V ≤ U) (P : (M.over U).Presentation) :
    (M.over V).Presentation :=
  (P.map (SheafOfModules.overMap (forgetRing R) (homOfLE hVU))
    (SheafOfModules.overMapUnitIso (R := forgetRing R) (homOfLE hVU)).symm).ofIsIso
      ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app M).hom

private theorem presentationOnSubopen_finite
    {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (forgetRing R))
    (U V : Opens X) (hVU : V ≤ U) (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationOnSubopen R M U V hVU P).IsFinite := by
  have : (P.map (SheafOfModules.overMap (forgetRing R) (homOfLE hVU))
      (SheafOfModules.overMapUnitIso (R := forgetRing R) (homOfLE hVU)).symm).IsFinite :=
    presentation_map_finite _ _ _
  unfold presentationOnSubopen
  infer_instance

section LocalBlock
variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  {M N P : SheafOfModules.{0} (forgetRing R)}

private theorem restrict_homOver (U V : Opens X) (hVU : V ≤ U) (f : M ⟶ N) :
    restrictOverHom R U V hVU (f.over U) = f.over V := by
  ext W m
  rfl

private theorem restrict_zero (U V : Opens X) (hVU : V ≤ U) :
    restrictOverHom R U V hVU (0 : M.over U ⟶ N.over U) = 0 := by
  ext W m
  rfl

-- Existing private native cokernel transport, repeated at zero engine credit.
private def restrictCofork (U V : Opens X) (hVU : V ≤ U)
    (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U)
    (h : f ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g h)) :
    IsColimit (CokernelCofork.ofπ (restrictOverHom R U V hVU g)
      (f := restrictOverHom R U V hVU f)
      (by rw [← restrictOverHom_comp,h,restrict_zero])) := by
  let F := SheafOfModules.overMap (forgetRing R) (homOfLE hVU)
  refine IsCokernel.ofIso _
    (CokernelCofork.mapIsColimit (CokernelCofork.ofπ g h) hc F) _
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app M)
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app N)
    ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app P) ?_ ?_
  · simp only [restrictOverHom,Iso.hom_inv_id_assoc,F]
  · change ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app N).hom ≫
      (((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app N).inv ≫
        F.map g ≫ ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app P).hom) = _
    exact Iso.hom_inv_id_assoc _ _

private def generatorMap (U : Opens X) (G : (M.over U).GeneratingSections) :
    (SheafOfModules.free (R := forgetRing R) G.I).over U ⟶ M.over U :=
  (freeOverIso R U G.I).inv ≫ G.π

private def relationMap (U : Opens X) (P : (N.over U).Presentation) :
    (SheafOfModules.free (R := forgetRing R) P.relations.I).over U ⟶
      (SheafOfModules.free (R := forgetRing R) P.generators.I).over U :=
  (freeOverIso R U P.relations.I).inv ≫
    (P.relations.π ≫ kernel.ι _) ≫ (freeOverIso R U P.generators.I).hom

private theorem relation_generator_zero (U : Opens X) (P : (N.over U).Presentation) :
    relationMap R U P ≫ generatorMap R U P.generators = 0 := by
  simp only [relationMap,generatorMap,Category.assoc,Iso.hom_inv_id_assoc,kernel.condition,comp_zero]

private def presentationCofork (U : Opens X) (P : (N.over U).Presentation) :
    IsColimit (CokernelCofork.ofπ (generatorMap R U P.generators)
      (relation_generator_zero R U P)) := by
  refine IsCokernel.ofIso _ P.isColimit _
    (freeOverIso R U P.relations.I) (freeOverIso R U P.generators.I) (Iso.refl _) ?_ ?_
  · simp only [relationMap,Category.assoc,Iso.hom_inv_id_assoc]
  · change (freeOverIso R U P.generators.I).hom ≫
      ((freeOverIso R U P.generators.I).inv ≫ P.generators.π) = P.generators.π
    exact Iso.hom_inv_id_assoc _ _

private theorem restrict_epi (U V : Opens X) (hVU : V ≤ U)
    (f : M.over U ⟶ N.over U) [Epi f] : Epi (restrictOverHom R U V hVU f) := by
  have : Epi ((SheafOfModules.overMap (forgetRing R) (homOfLE hVU)).map f) := Functor.map_epi _ _
  unfold restrictOverHom
  infer_instance

private theorem exists_free_factor_on_subopen {I : Type} [Finite I]
    (U : Opens X) (g : (SheafOfModules.free (R := forgetRing R) I).over U ⟶ N.over U)
    (p : P.over U ⟶ N.over U) [Epi p] (x : X) (hxU : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ L : (SheafOfModules.free (R := forgetRing R) I).over V ⟶ P.over V,
        L ≫ restrictOverHom R U V hVU p = restrictOverHom R U V hVU g := by
  classical
  let := Fintype.ofFinite I
  let e := HironakaChowNativeFiniteFreeStalk.finiteFreeStalkLinearEquiv R I x
  have : Module.Free ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk (SheafOfModules.free (R := forgetRing R) I).val.presheaf x) :=
    Module.Free.of_basis ((Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) I).map e.symm)
  obtain ⟨t,ht⟩ := Module.projective_lifting_property
    (stalkLinearMapOfOver R U p x hxU) (stalkLinearMapOfOver R U g x hxU)
      (stalkLinearMapOfOver_surjective_of_epi R U p x hxU)
  obtain ⟨V,hVU,hxV,L,hL⟩ := exists_free_local_lift R x U hxU t
  have hstalk : stalkLinearMapOfOver R V
      (L ≫ restrictOverHom R U V hVU p) x hxV =
        stalkLinearMapOfOver R V (restrictOverHom R U V hVU g) x hxV := by
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_restrictOverHom,hL,ht,
      stalkLinearMapOfOver_restrictOverHom]
  obtain ⟨W,hWV,hxW,hW⟩ := exists_restrictOverHom_eq_of_free_stalk_eq R V
    (L ≫ restrictOverHom R U V hVU p) (restrictOverHom R U V hVU g) x hxV hstalk
  refine ⟨W,hWV.trans hVU,hxW,restrictOverHom R V W hWV L,?_⟩
  simpa only [restrictOverHom_comp,restrictOverHom_trans] using hW

private theorem coproduct_kernel_finitePresentation
    (hFree : ∀ (V : Opens X) {I J : Type} [Finite I] [Finite J]
      (F : SheafOfModules.free (R := (forgetRing R).over V) I ⟶
        SheafOfModules.free (R := (forgetRing R).over V) J),
          (kernel F).IsFinitePresentation)
    (V : Opens X) {I J K : Type} [Finite I] [Finite J] [Finite K]
    (H : (SheafOfModules.free (R := forgetRing R) I).over V ⨿
      (SheafOfModules.free (R := forgetRing R) J).over V ⟶
        (SheafOfModules.free (R := forgetRing R) K).over V) :
    (kernel H).IsFinitePresentation := by
  let eDom : SheafOfModules.free (R := (forgetRing R).over V) (I ⊕ J) ≅
      (SheafOfModules.free (R := forgetRing R) I).over V ⨿
        (SheafOfModules.free (R := forgetRing R) J).over V :=
    (SheafOfModules.freeSumIso (R := (forgetRing R).over V) I J).symm ≪≫
      coprod.mapIso (freeOverIso R V I) (freeOverIso R V J)
  let eCod := freeOverIso R V K
  let Hfree : SheafOfModules.free (R := (forgetRing R).over V) (I ⊕ J) ⟶
      SheafOfModules.free (R := (forgetRing R).over V) K := eDom.hom ≫ H ≫ eCod.inv
  have hFinite : (kernel Hfree).IsFinitePresentation := hFree V Hfree
  let eK : kernel Hfree ≅ kernel H := kernel.mapIso Hfree H eDom eCod (by simp [Hfree])
  exact finitePresentation_of_iso eK hFinite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem local_kernel_epi
    (hFree : ∀ (V : Opens X) {I J : Type} [Finite I] [Finite J]
      (F : SheafOfModules.free (R := (forgetRing R).over V) I ⟶
        SheafOfModules.free (R := (forgetRing R).over V) J),
          (kernel F).IsFinitePresentation)
    (f : M ⟶ N) (U : Opens X) (G : (M.over U).GeneratingSections) [G.IsFiniteType]
    (P : (N.over U).Presentation) [P.IsFinite] (x : X) (hxU : x ∈ U) :
    ∃ (V : Opens X) (_hVU : V ≤ U), x ∈ V ∧
      ∃ S : SheafOfModules.{0} ((forgetRing R).over V), S.IsFinitePresentation ∧
        ∃ π : S ⟶ (kernel f).over V, Epi π := by
  let A := SheafOfModules.free (R := forgetRing R) G.I
  let B := SheafOfModules.free (R := forgetRing R) P.generators.I
  let C := SheafOfModules.free (R := forgetRing R) P.relations.I
  let m : A.over U ⟶ M.over U := generatorMap R U G
  let n : B.over U ⟶ N.over U := generatorMap R U P.generators
  let ρ : C.over U ⟶ B.over U := relationMap R U P
  have : Epi m := by dsimp [m,generatorMap]; infer_instance
  have : Epi n := by dsimp [n,generatorMap]; infer_instance
  obtain ⟨V,hVU,hxV,L,hL⟩ := exists_free_factor_on_subopen R U
    (m ≫ f.over U) n x hxU
  let mV : A.over V ⟶ M.over V := restrictOverHom R U V hVU m
  let nV : B.over V ⟶ N.over V := restrictOverHom R U V hVU n
  let ρV : C.over V ⟶ B.over V := restrictOverHom R U V hVU ρ
  have : Epi mV := restrict_epi R U V hVU m
  have hρn : ρV ≫ nV = 0 := by
    change restrictOverHom R U V hVU ρ ≫ restrictOverHom R U V hVU n = 0
    rw [← restrictOverHom_comp]
    change restrictOverHom R U V hVU (relationMap R U P ≫ generatorMap R U P.generators) = 0
    rw [relation_generator_zero,restrict_zero]
  have hn : IsColimit (CokernelCofork.ofπ nV hρn) :=
    restrictCofork R U V hVU ρ n (relation_generator_zero R U P) (presentationCofork R U P)
  have hLift : L ≫ nV = mV ≫ f.over V := by
    simpa only [restrictOverHom_comp,restrict_homOver] using hL
  let H : A.over V ⨿ C.over V ⟶ B.over V := coprod.desc L (-ρV)
  let p : A.over V ⨿ C.over V ⟶ M.over V := coprod.desc mV (0 : (SheafOfModules.free
    (R := forgetRing R) P.relations.I).over V ⟶ M.over V)
  let sq := relation_block_isPushout mV ρV nV hρn hn L (f.over V) hLift
  let α : kernel H ⟶ kernel (f.over V) := kernel.map H (f.over V) p nV sq.w
  have : Epi α := relation_block_kernel_epi mV ρV nV hρn hn L (f.over V) hLift
  have hS : (kernel H).IsFinitePresentation := coproduct_kernel_finitePresentation R hFree V H
  have : (SheafOfModules.overFunctor (forgetRing R) V).IsRightAdjoint :=
    native_over_rightAdjoint (forgetRing R) V
  let e := PreservesKernel.iso (SheafOfModules.overFunctor (forgetRing R) V) f
  refine ⟨V,hVU,hxV,kernel H,hS,α ≫ e.inv,?_⟩
  infer_instance

private theorem kernel_finiteType_of_free_kernels
    (hFree : ∀ (V : Opens X) {I J : Type} [Finite I] [Finite J]
      (F : SheafOfModules.free (R := (forgetRing R).over V) I ⟶
        SheafOfModules.free (R := (forgetRing R).over V) J),
          (kernel F).IsFinitePresentation)
    (f : M ⟶ N) [M.IsFiniteType] [N.IsFinitePresentation] :
    (kernel f).IsFiniteType := by
  apply finiteType_of_localFiniteType (forgetRing R) (kernel f)
  intro x
  obtain ⟨A,hxA,G,hG⟩ := exists_local_generators R M x
  obtain ⟨B,hxB,P,hP⟩ := exists_local_presentation R N x
  let : G.IsFiniteType := hG
  let : P.IsFinite := hP
  let U := A ⊓ B
  let GU := generatorsOnSubopen R A U inf_le_left G
  have : GU.IsFiniteType := generatorsOnSubopen_finite R A U inf_le_left G
  let PU := presentationOnSubopen R N B U inf_le_right P
  have : PU.IsFinite := presentationOnSubopen_finite R N B U inf_le_right P
  obtain ⟨V,_hVU,hxV,S,hS,π,hπ⟩ := local_kernel_epi R hFree f U GU PU x ⟨hxA,hxB⟩
  let : S.IsFinitePresentation := hS
  let : Epi π := hπ
  exact ⟨V,hxV,finiteType_of_epi π⟩

end LocalBlock

section NativeOpenReturn
attribute [local instance] singleOverAddGroupSheafify doubleOverAddGroupSheafify doubleOverAddGroupWeakSheafify

/-- The SAME whole native kernel has finite type, from ordinary local properties. -/
theorem original_open_kernel_isFiniteType {n : ℕ}
    (U : Opens (originalSpace n).toTopCat)
    {M N : SheafOfModules.{0} (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪)}
    [M.IsFiniteType] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFiniteType := by
  refine kernel_finiteType_of_free_kernels ((originalSpace n).restrict U.isOpenEmbedding).𝒪 ?_ f
  intro V I J hI hJ F
  exact HironakaChowNativeLocalOverFreeKernelCoherence.original_open_over_free_kernel_isFinitePresentation U V F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem literal_over_free_to_fp_kernel_isFiniteType {n : ℕ}
    (U : Opens (originalSpace n).toTopCat) (V : Opens (TopCat.of U))
    {I : Type} [Finite I]
    {N : SheafOfModules.{0} ((forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪).over V)}
    [N.IsFinitePresentation]
    (f : SheafOfModules.free I ⟶ N) : (kernel f).IsFiniteType := by
  let X := originalSpace n
  let W := (U.overEquivalence.inverse.obj V).left
  let E := localModuleEquivalence X U V
  let EW := realizationEquivalence X W
  have : E.inverse.PreservesZeroMorphisms := local_return_preservesZero X U V
  have : EW.functor.PreservesZeroMorphisms := realization_preservesZero X W
  let F := E.inverse ⋙ EW.functor
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have : EW.functor.IsEquivalence := EW.isEquivalence_functor
  have : F.IsEquivalence := inferInstance
  have : F.PreservesZeroMorphisms := inferInstance
  let e0 := localReturnFreeIso X U V I
  let ea := EW.functor.mapIso e0 ≪≫ realizationFreeIso X W I
  let g := ea.inv ≫ F.map f
  have : (E.inverse.obj N).IsFinitePresentation := local_inverse_isFinitePresentation X U V N
  have : (F.obj N).IsFinitePresentation := realization_isFinitePresentation X W _
  have : (SheafOfModules.free
      (R := forgetRing (X.restrict W.isOpenEmbedding).𝒪) I).IsFiniteType :=
    free_isFiniteType _ I
  have : (kernel g).IsFiniteType := original_open_kernel_isFiniteType W g
  let e : F.obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso F f ≪≫ kernel.mapIso (F.map f) g ea (Iso.refl _) (by simp [g])
  have : (F.obj (kernel f)).IsFiniteType := finiteType_of_epi e.inv
  have hReturnFT : (EW.inverse.obj (F.obj (kernel f))).IsFiniteType := return_isFiniteType X W _
  have : ((EW.functor ⋙ EW.inverse).obj (E.inverse.obj (kernel f))).IsFiniteType := by
    change (EW.inverse.obj (F.obj (kernel f))).IsFiniteType
    exact hReturnFT
  have : (E.inverse.obj (kernel f)).IsFiniteType :=
    finiteType_of_epi (EW.unitIso.app (E.inverse.obj (kernel f))).inv
  have hForwardFT : (E.functor.obj (E.inverse.obj (kernel f))).IsFiniteType :=
    local_forward_isFiniteType X U V _
  have : ((E.inverse ⋙ E.functor).obj (kernel f)).IsFiniteType := by
    change (E.functor.obj (E.inverse.obj (kernel f))).IsFiniteType
    exact hForwardFT
  exact finiteType_of_epi (E.counitIso.app (kernel f)).hom

end NativeOpenReturn

-- A finite generator family with a finite-type ACTUAL kernel yields standard
-- native finite presentation. This is kernel/cokernel and cover plumbing only.
private def presentationFromKernelGenerators
    {C : Type} [Category.{0} C] [HasBinaryProducts C] [HasPullbacks C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections) (U : C)
    (A : ((kernel G.π).over U).GeneratingSections) : (M.over U).Presentation := by
  let F := SheafOfModules.overFunctor R U
  have : F.IsLeftAdjoint := (SheafOfModules.overPushforwardOverAdj (R := R) U).isLeftAdjoint
  have : F.IsRightAdjoint := native_over_rightAdjoint R U
  have : Epi (G.π.over U) := Functor.map_epi F G.π
  let e := SheafOfModules.mapFreeIso F G.I (Iso.refl _)
  let k := (kernel.ι G.π).over U
  have hkzero : k ≫ G.π.over U = 0 := by
    change F.map (kernel.ι G.π) ≫ F.map G.π = 0
    rw [← F.map_comp,kernel.condition,F.map_zero]
  have hlim := (KernelFork.ofι (kernel.ι G.π) (kernel.condition G.π)).mapIsLimit
    (kernelIsKernel G.π) F
  have hc : IsColimit (CokernelCofork.ofπ (G.π.over U) hkzero) :=
    Abelian.epiIsCokernelOfKernel _ hlim
  let q := A.π ≫ k
  have hq : q ≫ G.π.over U = 0 := by simp only [q,Category.assoc,hkzero,comp_zero]
  have hcq : IsColimit (CokernelCofork.ofπ (G.π.over U) hq) :=
    isCokernelEpiComp hc A.π rfl
  let ρ := q ≫ e.inv
  let n := e.hom ≫ G.π.over U
  have hρn : ρ ≫ n = 0 := by
    simp only [ρ,n,Category.assoc,Iso.inv_hom_id_assoc,hq]
  have hcn : IsColimit (CokernelCofork.ofπ n hρn) := by
    refine IsCokernel.ofIso _ hcq _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
    · simp only [ρ,Iso.refl_hom,Category.id_comp,Iso.symm_hom]
    · change e.inv ≫ (e.hom ≫ G.π.over U) = G.π.over U
      exact e.inv_hom_id_assoc _
  exact SheafOfModules.presentationOfIsCokernelFree ρ n hρn hcn

private theorem presentationFromKernelGenerators_finite
    {C : Type} [Category.{0} C] [HasBinaryProducts C] [HasPullbacks C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections) [G.IsFiniteType] (U : C)
    (A : ((kernel G.π).over U).GeneratingSections) [A.IsFiniteType] :
    (presentationFromKernelGenerators R M G U A).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite G.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite A.I)⟩

private theorem finitePresentation_of_generators_kernelFiniteType
    {C : Type} [Category.{0} C] [HasBinaryProducts C] [HasPullbacks C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections) [G.IsFiniteType]
    [(kernel G.π).IsFiniteType] : M.IsFinitePresentation := by
  obtain ⟨D,hD⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (kernel G.π)
  let Q : M.QuasicoherentData := {
    I := D.I
    X := D.X
    coversTop := D.coversTop
    presentation i := presentationFromKernelGenerators R M G (D.X i) (D.generators i) }
  refine ⟨Q,⟨fun i => ?_⟩⟩
  have : (D.generators i).IsFiniteType := hD.isFiniteType i
  exact presentationFromKernelGenerators_finite R M G (D.X i) (D.generators i)

private theorem finitePresentation_of_covers
    {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{0}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ U V, HasSheafify ((J.over U).over V) AddCommGrpCat.{0}]
    [∀ U V, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} R) {I : Type} (U : I → C) (hU : J.CoversTop U)
    (h : ∀ i, (M.over (U i)).IsFinitePresentation) : M.IsFinitePresentation := by
  have hData (i : I) : ∃ Q : (M.over (U i)).QuasicoherentData, Q.IsFinitePresentation := by
    have : (M.over (U i)).IsFinitePresentation := h i
    exact SheafOfModules.IsFinitePresentation.exists_quasicoherentData (M.over (U i))
  choose Q hQ using hData
  let P := SheafOfModules.QuasicoherentData.bind M U hU Q
  refine ⟨P,⟨fun i => { isFiniteType_generators := ⟨?_⟩, isFiniteType_relations := ⟨?_⟩ }⟩⟩
  · change Finite ((Q i.1).presentation i.2).generators.I
    exact ((hQ i.1).isFinite_presentation i.2).isFiniteType_generators.finite
  · change Finite ((Q i.1).presentation i.2).relations.I
    exact ((hQ i.1).isFinite_presentation i.2).isFiniteType_relations.finite

section NativeOpenPresentation
attribute [local instance] singleOverAddGroupSheafify doubleOverAddGroupSheafify doubleOverAddGroupWeakSheafify

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME whole native kernel is finitely presented from ordinary FP inputs. -/
theorem original_open_kernel_isFinitePresentation {n : ℕ}
    (U : Opens (originalSpace n).toTopCat)
    {M N : SheafOfModules.{0} (forgetRing ((originalSpace n).restrict U.isOpenEmbedding).𝒪)}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  let Z := (originalSpace n).restrict U.isOpenEmbedding
  let R := forgetRing Z.𝒪
  let K := kernel f
  have : K.IsFiniteType := original_open_kernel_isFiniteType U f
  obtain ⟨D,hD⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData K
  have hLocal (i : D.I) : (K.over (D.X i)).IsFinitePresentation := by
    let V := D.X i
    let G := D.generators i
    have : G.IsFiniteType := hD.isFiniteType i
    have : (M.over V).IsFinitePresentation := over_isFinitePresentation Z.𝒪 M V
    let F := SheafOfModules.overFunctor R V
    have : F.IsRightAdjoint := native_over_rightAdjoint R V
    let j : K.over V ⟶ M.over V := (kernel.ι f).over V
    have : Mono j := Functor.map_mono F (kernel.ι f)
    have : (kernel (G.π ≫ j)).IsFiniteType :=
      literal_over_free_to_fp_kernel_isFiniteType U V (G.π ≫ j)
    have : (kernel G.π).IsFiniteType := finiteType_of_epi (kernelCompMono G.π j).hom
    exact finitePresentation_of_generators_kernelFiniteType (R.over V) (K.over V) G
  exact finitePresentation_of_covers R K D.X D.coversTop hLocal

end NativeOpenPresentation

end Hironaka.HironakaChowNativeFinitePresentationKernelCoherence
end
