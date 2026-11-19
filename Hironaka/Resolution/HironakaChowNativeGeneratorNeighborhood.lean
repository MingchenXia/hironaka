import Hironaka.Resolution.HironakaChowNativeFiniteTypeSpreading
import Mathlib.Algebra.Module.Projective

/-! The SAME original native map with surjective original stalk is epi
on an actual smaller original open when its target is of finite type.
The EXACT old finite stalk generators consequently extend to genuine
local generators. Blueprint: `hironaka-g10-native-generator-neighborhood.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hironaka.HironakaChowNativeGeneratorNeighborhood

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeSectionSpreading

universe u
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})
  {M N P : SheafOfModules.{u} (forgetRing R)}

private theorem epi_restrict (U V : Opens X) (hVU : V ≤ U)
    (p : P.over U ⟶ M.over U) [Epi p] : Epi (restrictOverHom R U V hVU p) := by
  have : Epi ((SheafOfModules.overMap (forgetRing R) (homOfLE hVU)).map p) :=
    Functor.map_epi _ p
  unfold restrictOverHom
  infer_instance

private theorem exists_original_stalk_factor {J : Type u} [Finite J]
    (U : Opens X) (p : P.over U ⟶ M.over U)
    (g : (SheafOfModules.free (R := forgetRing R) J).over U ⟶ M.over U)
    (x : X) (hxU : x ∈ U) (hp : Function.Surjective (stalkLinearMapOfOver R U p x hxU)) :
    ∃ T : ↑(TopCat.Presheaf.stalk (SheafOfModules.free (R := forgetRing R) J).val.presheaf x)
        →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] ↑(TopCat.Presheaf.stalk P.val.presheaf x),
      (stalkLinearMapOfOver R U p x hxU).comp T = stalkLinearMapOfOver R U g x hxU := by
  classical
  let := Fintype.ofFinite J
  let e := finiteFreeStalkLinearEquiv R J x
  have : Module.Free ↑(TopCat.Presheaf.stalk R.obj x)
      ↑(TopCat.Presheaf.stalk (SheafOfModules.free (R := forgetRing R) J).val.presheaf x) :=
    Module.Free.of_basis ((Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) J).map e.symm)
  exact Module.projective_lifting_property
    (stalkLinearMapOfOver R U p x hxU) (stalkLinearMapOfOver R U g x hxU) hp

/-- The SAME actual original morphism is epi on an internally chosen smaller open;
only standard target finite type and original ONE-point stalk surjectivity are inputs. -/
theorem exists_subopen_epi_of_stalk_surjective [M.IsFiniteType]
    (U : Opens X) (p : P.over U ⟶ M.over U) (x : X) (hxU : x ∈ U)
    (hp : Function.Surjective (stalkLinearMapOfOver R U p x hxU)) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V), Epi (restrictOverHom R U V hVU p) := by
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
  let g := (freeOverIso R A G.I).inv ≫ G.π
  have : Epi g := by dsimp [g]; infer_instance
  let pA := restrictOverHom R U A hAU p
  have hpA : Function.Surjective (stalkLinearMapOfOver R A pA x hxA) := by
    rw [stalkLinearMapOfOver_restrictOverHom]
    exact hp
  obtain ⟨t,ht⟩ := exists_original_stalk_factor R A pA g x hxA hpA
  obtain ⟨B,hBA,hxB,T,hT⟩ := exists_free_local_lift R x A hxA t
  have hstalk : stalkLinearMapOfOver R B
      (T ≫ restrictOverHom R A B hBA pA) x hxB =
      stalkLinearMapOfOver R B (restrictOverHom R A B hBA g) x hxB := by
    rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_restrictOverHom,hT,ht,
      stalkLinearMapOfOver_restrictOverHom]
  obtain ⟨V,hVB,hxV,hV⟩ := exists_restrictOverHom_eq_of_free_stalk_eq R B
    (T ≫ restrictOverHom R A B hBA pA) (restrictOverHom R A B hBA g) x hxB hstalk
  let hVA : V ≤ A := hVB.trans hBA
  let hVU : V ≤ U := hVA.trans hAU
  have hwhole : restrictOverHom R B V hVB T ≫ restrictOverHom R U V hVU p =
      restrictOverHom R A V hVA g := by
    simpa only [pA,restrictOverHom_comp,restrictOverHom_trans] using hV
  have : Epi (restrictOverHom R A V hVA g) := epi_restrict R A V hVA g
  have : Epi (restrictOverHom R B V hVB T ≫ restrictOverHom R U V hVU p) := by
    rw [hwhole]
    infer_instance
  exact ⟨V,hVU,hxV,epi_of_epi (restrictOverHom R B V hVB T) (restrictOverHom R U V hVU p)⟩

/-- Native restriction preserves the WHOLE free-sheaf morphism of the SAME original sections. -/
theorem freeOverMap_restrict (U V : Opens X) (hVU : V ≤ U) {I : Type u}
    (s : I → M.val.obj (op U)) :
    freeOverMap R V (fun i => M.val.map (homOfLE hVU).op (s i)) =
      restrictOverHom R U V hVU (freeOverMap R U s) := by
  apply (cancel_epi (freeOverIso R V I).hom).mp
  apply Sigma.hom_ext
  intro i
  have hι : SheafOfModules.ιFree i ≫ (freeOverIso R V I).hom =
      (SheafOfModules.ιFree (R := forgetRing R) i).over V := by
    simpa only [freeOverIso,Iso.refl_hom,Category.id_comp] using
      SheafOfModules.ιFree_mapFreeIso_hom
        (SheafOfModules.overFunctor (forgetRing R) V) I (Iso.refl _) i
  rw [← Category.assoc,← Category.assoc]
  erw [hι]
  rw [ι_freeOverMap]
  have hιV : (SheafOfModules.ιFree (R := forgetRing R) i).over V =
      restrictOverHom R U V hVU ((SheafOfModules.ιFree (R := forgetRing R) i).over U) := by
    ext W
    rfl
  rw [hιV,← restrictOverHom_comp,ι_freeOverMap]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change m • M.val.map W.unop.hom.op (M.val.map (homOfLE hVU).op (s i)) =
    m • M.val.map (homOfLE (W.unop.hom.le.trans hVU)).op (s i)
  rw [← M.val.map_comp_apply]
  exact congrArg (fun t => m • t) (M.val.congr_map_apply (Subsingleton.elim _ _) (s i))

/-- The EXACT ORIGINAL finite stalk-generating family extends to actual native local
generating sections, with its original indices and germs retained internally. -/
theorem exists_local_generators_with_original_germs [M.IsFiniteType]
    {I : Type u} [Finite I] (x : X)
    (v : I → ↑(TopCat.Presheaf.stalk M.val.presheaf x))
    (hv : Submodule.span ↑(TopCat.Presheaf.stalk R.obj x) (Set.range v) = ⊤) :
    ∃ (U : Opens X) (hxU : x ∈ U) (s : I → M.val.obj (op U)),
      (∀ i, TopCat.Presheaf.germ M.val.presheaf U x hxU (s i) = v i) ∧
        Epi (freeOverMap R U s) := by
  obtain ⟨U,_hU,hxU,s,hs⟩ := exists_common_germ_representatives M.val x ⊤ (by trivial) v
  have hp : Function.Surjective (stalkLinearMapOfOver R U (freeOverMap R U s) x hxU) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
      ((unitStalkLinearEquiv R x).symm 1),?_⟩
    rw [freeOverMap_stalk_ι,one_smul,hs i]
  obtain ⟨V,hVU,hxV,hpV⟩ :=
    exists_subopen_epi_of_stalk_surjective R U (freeOverMap R U s) x hxU hp
  let sV (i : I) := M.val.map (homOfLE hVU).op (s i)
  refine ⟨V,hxV,sV,?_,?_⟩
  · intro i
    exact (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVU) x hxV (s i)).trans (hs i)
  · rw [freeOverMap_restrict]
    exact hpV

end Hironaka.HironakaChowNativeGeneratorNeighborhood
