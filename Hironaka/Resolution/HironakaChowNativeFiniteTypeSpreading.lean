import Hironaka.Resolution.HironakaChowNativeFinitePresentationSpreading

/-! Standard native finite-type data spreads equal ORIGINAL stalk maps to
WHOLE morphism equalities on one original open, and produces actual finite
ORIGINAL module stalks. Blueprint: `hironaka-g10-native-finite-type-spreading.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hironaka.HironakaChowNativeFiniteTypeSpreading

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading

universe u
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M N P : SheafOfModules.{u} (forgetRing R)}

theorem restrictOverHom_comp (U V : Opens X) (hVU : V ≤ U)
    (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) :
    restrictOverHom R U V hVU (f ≫ g) =
      restrictOverHom R U V hVU f ≫ restrictOverHom R U V hVU g := by
  ext W m
  rfl

theorem restrictOverHom_trans (U V W : Opens X) (hVU : V ≤ U) (hWV : W ≤ V)
    (f : M.over U ⟶ N.over U) :
    restrictOverHom R V W hWV (restrictOverHom R U V hVU f) =
      restrictOverHom R U W (hWV.trans hVU) f := by
  ext T m
  rfl

private def generatorMap (U : Opens X) (G : (M.over U).GeneratingSections) :
    (SheafOfModules.free (R := forgetRing R) G.I).over U ⟶ M.over U :=
  (freeOverIso R U G.I).inv ≫ G.π

private instance generatorMap_epi (U : Opens X) (G : (M.over U).GeneratingSections) :
    Epi (generatorMap R U G) := by
  dsimp [generatorMap]
  infer_instance

/-- Actual native finite generating sections give WHOLE original local equality. -/
theorem exists_restriction_eq_of_generatingSections
    (U : Opens X) (G : (M.over U).GeneratingSections) [G.IsFiniteType]
    (f g : M.over U ⟶ N.over U) (x : X) (hxU : x ∈ U)
    (h : stalkLinearMapOfOver R U f x hxU = stalkLinearMapOfOver R U g x hxU) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
      restrictOverHom R U V hVU f = restrictOverHom R U V hVU g := by
  let p := generatorMap R U G
  have hp : stalkLinearMapOfOver R U (p ≫ f) x hxU =
      stalkLinearMapOfOver R U (p ≫ g) x hxU := by
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_comp,h]
  obtain ⟨V,hVU,hxV,hV⟩ := exists_restrictOverHom_eq_of_free_stalk_eq R U
    (p ≫ f) (p ≫ g) x hxU hp
  have : Epi p := generatorMap_epi R U G
  have : Epi ((SheafOfModules.overMap (forgetRing R) (homOfLE hVU)).map p) :=
    Functor.map_epi _ p
  have : Epi (restrictOverHom R U V hVU p) := by
    unfold restrictOverHom
    infer_instance
  refine ⟨V,hVU,hxV,(cancel_epi (restrictOverHom R U V hVU p)).mp ?_⟩
  simpa only [restrictOverHom_comp] using hV

def generatorsOnSubopen (U V : Opens X) (hVU : V ≤ U)
    (G : (M.over U).GeneratingSections) : (M.over V).GeneratingSections :=
  (G.map (SheafOfModules.overMap (forgetRing R) (homOfLE hVU))
    (SheafOfModules.overMapUnitIso (R := forgetRing R) (homOfLE hVU)).symm).ofEpi
      ((SheafOfModules.overFunctorMap (forgetRing R) (homOfLE hVU)).app M).hom

instance generatorsOnSubopen_finite (U V : Opens X) (hVU : V ≤ U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (generatorsOnSubopen R U V hVU G).IsFiniteType := by
  dsimp [generatorsOnSubopen]
  infer_instance

/-- STANDARD native finite type gives WHOLE equality on one original sub-neighbourhood. -/
theorem exists_restriction_eq_of_isFiniteType [M.IsFiniteType]
    (U : Opens X) (f g : M.over U ⟶ N.over U) (x : X) (hxU : x ∈ U)
    (h : stalkLinearMapOfOver R U f x hxU = stalkLinearMapOfOver R U g x hxU) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
      restrictOverHom R U V hVU f = restrictOverHom R U V hVU g := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨W,j,hW,hxW⟩ :=
    (Opens.mem_grothendieckTopology X).mp (q.coversTop ⊤) x (by trivial)
  obtain ⟨i,⟨k⟩⟩ := (Sieve.mem_ofObjects_iff q.X j).mp hW
  have hxi : x ∈ q.X i := k.le hxW
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  let A := q.X i ⊓ U
  have hAi : A ≤ q.X i := inf_le_left
  have hAU : A ≤ U := inf_le_right
  have hxA : x ∈ A := ⟨hxi,hxU⟩
  let G := generatorsOnSubopen R (q.X i) A hAi (q.generators i)
  have hA : stalkLinearMapOfOver R A (restrictOverHom R U A hAU f) x hxA =
      stalkLinearMapOfOver R A (restrictOverHom R U A hAU g) x hxA := by
    rw [stalkLinearMapOfOver_restrictOverHom,stalkLinearMapOfOver_restrictOverHom]
    exact h
  obtain ⟨V,hVA,hxV,hV⟩ := exists_restriction_eq_of_generatingSections R A G
    (restrictOverHom R U A hAU f) (restrictOverHom R U A hAU g) x hxA hA
  refine ⟨V,hVA.trans hAU,hxV,?_⟩
  simpa only [restrictOverHom_trans] using hV

/-- Actual native finite generators imply finiteness of the SAME actual original module stalk. -/
theorem moduleFinite_stalk_of_generatingSections (U : Opens X)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] (x : X) (hxU : x ∈ U) :
    Module.Finite ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) := by
  classical
  let := Fintype.ofFinite G.I
  let e := finiteFreeStalkLinearEquiv R G.I x
  let p := generatorMap R U G
  let f := (stalkLinearMapOfOver R U p x hxU).comp e.symm.toLinearMap
  exact Module.Finite.of_surjective f
    ((stalkLinearMapOfOver_surjective_of_epi R U p x hxU).comp e.symm.surjective)

/-- STANDARD native finite type supplies actual original stalk finiteness internally. -/
theorem moduleFinite_stalk_of_isFiniteType [M.IsFiniteType] (x : X) :
    Module.Finite ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨W,j,hW,hxW⟩ :=
    (Opens.mem_grothendieckTopology X).mp (q.coversTop ⊤) x (by trivial)
  obtain ⟨i,⟨k⟩⟩ := (Sieve.mem_ofObjects_iff q.X j).mp hW
  have hxi : x ∈ q.X i := k.le hxW
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact moduleFinite_stalk_of_generatingSections R (q.X i) (q.generators i) x hxi

/-- ONE original open before ALL original finite whole-morphism identities. -/
theorem exists_common_restriction_eq {I : Type*} [Finite I]
    (A B : I → SheafOfModules.{u} (forgetRing R)) [∀ i, (A i).IsFiniteType]
    (U : Opens X) (f g : ∀ i, (A i).over U ⟶ (B i).over U) (x : X) (hxU : x ∈ U)
    (h : ∀ i, stalkLinearMapOfOver R U (f i) x hxU = stalkLinearMapOfOver R U (g i) x hxU) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V),
      ∀ i, restrictOverHom R U V hVU (f i) = restrictOverHom R U V hVU (g i) := by
  classical
  choose V hVU hxV heq using fun i =>
    exists_restriction_eq_of_isFiniteType R U (f i) (g i) x hxU (h i)
  let W : Opens X := U ⊓ ⨅ i, V i
  have hWU : W ≤ U := inf_le_left
  have hWV (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  have hxW : x ∈ W := by
    change x ∈ (U : Set X) ∩ ((⨅ i, V i : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact ⟨hxU,Set.mem_iInter.mpr hxV⟩
  refine ⟨W,hWU,hxW,?_⟩
  intro i
  have hi := congrArg (fun t => restrictOverHom R (V i) W (hWV i) t) (heq i)
  simpa only [restrictOverHom_trans] using hi

end Hironaka.HironakaChowNativeFiniteTypeSpreading
