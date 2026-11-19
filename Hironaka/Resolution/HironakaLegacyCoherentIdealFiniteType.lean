import Hironaka.Resolution.HironakaLegacyCoherentIdealSheaf
import Hironaka.Resolution.HironakaChowCoherentOriginalMinorIdeal
import Hironaka.Resolution.HironakaChowNativeFinitePresentationSpreading
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Original legacy coherence implies native finite type of the SAME ideal sheaf

The old all-germ section presheaf, its inclusion and its native stalk actions
are retained literally. Blueprint FIRST: `hironaka-legacy-coherent-ideal-finite-type.tex`.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set Filter AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaLegacyCoherentIdealFiniteType

open Hironaka.HolomorphicIdealSheaves InvertibleIdealQuotient
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf HironakaLegacyCoherentIdealSheaf
  HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFinitePresentationSpreading HironakaChowCoherentOriginalMinorIdeal
  HironakaActualCoherentWeightedCoefficientMarked

section EpiCriterion
variable {X : TopCat} (R : X.Sheaf CommRingCat)
  {B D : SheafOfModules.{0} (forgetRing R)}

-- These are the existing native restriction/stalk comparisons, specialized here
-- only because the original exports have private visibility. No new model/action.
private def restrictedStalkIso (B : SheafOfModules.{0} (forgetRing R))
    (U : Opens X) (x : U) :
    TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj
        ((SheafOfModules.toSheaf _).obj (B.over U))).obj x ≅
      TopCat.Presheaf.stalk B.val.presheaf x.val :=
  PresheafedSpace.restrictStalkIso
    (PresheafedSpace.mk X B.val.presheaf) U.isOpenEmbedding x

private theorem restrictedStalk_square (U : Opens X) (f : B.over U ⟶ D.over U)
    (x : U) (m : ↑(TopCat.Presheaf.stalk (X := TopCat.of U)
      ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (B.over U))).obj x)) :
    (restrictedStalkIso R D U x).hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of U) x).map
        ((U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)).hom m) =
      stalkLinearMapOfOver R U f x.val x.property ((restrictedStalkIso R B U x).hom m) := by
  obtain ⟨V,hxV,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of U)
    ((U.sheafEquivOver.functor).obj ((SheafOfModules.toSheaf _).obj (B.over U))).obj m
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (PresheafedSpace.mk X D.val.presheaf) U.isOpenEmbedding V x hxV,
    PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
      (PresheafedSpace.mk X B.val.presheaf) U.isOpenEmbedding V x hxV]
  erw [stalkLinearMapOfOver_germ_of_le R U f x.val x.property
    (U.isOpenEmbedding.functor.obj V) _ (by rintro y ⟨z,hz,rfl⟩; exact z.property)]
  rfl

private theorem epi_of_all_original_stalks_surjective (U : Opens X)
    (f : B.over U ⟶ D.over U)
    (hf : ∀ (x : X) (hx : x ∈ U), Function.Surjective
      (stalkLinearMapOfOver R U f x hx)) : Epi f := by
  let g := (U.sheafEquivOver.functor).map ((SheafOfModules.toSheaf _).map f)
  have hg : ∀ x : U, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of U) x).map g.hom) := by
    intro x b
    obtain ⟨a,ha⟩ := hf x.val x.property ((restrictedStalkIso R D U x).hom b)
    obtain ⟨c,hc⟩ := (ConcreteCategory.bijective_of_isIso
      (restrictedStalkIso R B U x).hom).2 a
    refine ⟨c,?_⟩
    apply (ConcreteCategory.bijective_of_isIso (restrictedStalkIso R D U x).hom).1
    exact (restrictedStalk_square R U f x c).trans ((congrArg
      (stalkLinearMapOfOver R U f x.val x.property) hc).trans ha)
  have hls : TopCat.Presheaf.IsLocallySurjective
      (X := TopCat.of U) (C := AddCommGrpCat.{0}) g.hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      (X := TopCat.of U) (C := AddCommGrpCat.{0}) g.hom).mpr hg
  have : Epi g := (TopCat.Sheaf.isLocallySurjective_iff_epi
    (X := TopCat.of U) (C := AddCommGrpCat.{0}) g).mp hls
  have : Epi ((SheafOfModules.toSheaf _).map f) :=
    U.sheafEquivOver.functor.epi_of_epi_map inferInstance
  exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance

/-- On the SAME native ideal sheaf, an all-point whole-image span gives a full epi. -/
theorem finite_free_epi_of_whole_image_span
    (b : B ⟶ SheafOfModules.unit (forgetRing R))
    (hb : ∀ W : Opens X, Function.Injective (b.val.app (op W)))
    (U : Opens X) {r : ℕ} (s : Fin r → B.val.obj (op U))
    (hspan : ∀ (y : X) (hy : y ∈ U),
      LinearMap.range (stalkInclusionLinearMap R B b y) =
        Ideal.span (range fun i => TopCat.Presheaf.germ R.obj U y hy (b.val.app (op U) (s i)))) :
    Epi (freeOverMap R U s) := by
  apply epi_of_all_original_stalks_surjective R U (freeOverMap R U s)
  intro y hy m
  let k := stalkInclusionLinearMap R B b y
  let p := stalkLinearMapOfOver R U (freeOverMap R U s) y hy
  have hk : Function.Injective k := stalkInclusionLinearMap_injective R B b hb y
  have hle : Ideal.span (range fun i => TopCat.Presheaf.germ R.obj U y hy (b.val.app (op U) (s i))) ≤
      LinearMap.range (k.comp p) := by
    apply Ideal.span_le.mpr
    rintro z ⟨i,rfl⟩
    refine ⟨stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val y
      ((unitStalkLinearEquiv R y).symm 1),?_⟩
    exact (congrArg k (freeOverMap_stalk_ι R U s y hy i 1)).trans
      ((congrArg k (one_smul _ _)).trans (stalkInclusionLinearMap_germ R B b y U hy (s i)))
  have hm : k m ∈ LinearMap.range (k.comp p) := by
    apply hle
    rw [← hspan y hy]
    exact ⟨m,rfl⟩
  obtain ⟨v,hv⟩ := hm
  exact ⟨v,hk hv⟩
end EpiCriterion

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem wholeIdeal_eq_function_span (A : GermIdeal n M) (y : M)
    {r : ℕ} (f : Fin r → M → ℂ) (hf : ∀ i, HolomorphicAt n (f i) y)
    (hgen : ∀ g, A.mem y g ↔ IsInSpanAt (n := n) (· ∈ range f) y g) :
    actualWholeSheafStalkIdeal A y =
      Ideal.span (range fun i => actualOriginalFunctionGerm y (f i) (hf i)) := by
  have hI : actualWholeSheafStalkIdeal A y =
      actualWholeSheafStalkIdeal (finiteFunctionIdeal (n := n) f) y := by
    unfold actualWholeSheafStalkIdeal
    congr 1
    ext z
    constructor
    · rintro ⟨g,hg,hm,rfl⟩
      exact ⟨g,hg,(hgen g).mp hm,rfl⟩
    · rintro ⟨g,hg,hm,rfl⟩
      exact ⟨g,hg,(hgen g).mpr hm,rfl⟩
  exact hI.trans (actualWholeStalk_finiteFunctionIdeal f y hf)

private theorem exists_coherent_actual_section_family
    (A : GermIdeal n M) (hA : A.IsCoherent) (x : M) :
    ∃ (U : Opens M) (_hxU : x ∈ U) (r : ℕ)
      (s : Fin r → (actualIdealModuleSheaf A).val.obj (op U)),
      ∀ (y : M) (hy : y ∈ U),
        LinearMap.range (stalkInclusionLinearMap (actualComplexStructureSheaf (n := n) M)
          (actualIdealModuleSheaf A) (actualIdealModuleInclusion A) y) =
        Ideal.span (range fun i => (actualComplexStructureSheaf (n := n) M).presheaf.germ
          U y hy ((actualIdealModuleInclusion A).val.app (op U) (s i))) := by
  classical
  obtain ⟨V,hV,hx,r,f,hf,hgen⟩ := hA x
  let U : Opens M := ⟨V,hV⟩
  let R := actualComplexStructureSheaf (n := n) M
  let B := actualIdealModuleSheaf A
  have hhol (i : Fin r) (y : M) (hy : y ∈ U) : HolomorphicAt n (f i) y :=
    holomorphicAt_of_mdifferentiableOn hV (hf i) hy
  let t (i : Fin r) : actualComplexSection (n := n) U := ⟨fun z => f i z,by
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun z : U => f i z)
    intro z
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_eventually_mdifferentiableAt (hhol i z z.property)⟩
  have htg (i : Fin r) (y : M) (hy : y ∈ U) :
      actualOriginalFunctionGerm y (f i) (hhol i y hy) = R.presheaf.germ U y hy (t i) := by
    apply actualOriginalFunctionGerm_eq_section U y hy (t i) (f i) (hhol i y hy)
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    rw [sectionExtension_apply U (t i) z hz]
  have ht (i : Fin r) : t i ∈ actualSectionIdeal A U := by
    intro y hy
    rw [← htg i y hy]
    exact Ideal.subset_span ⟨f i,hhol i y hy,
      (hgen y hy (f i)).mpr (isInSpanAt_self ⟨i,rfl⟩ (hhol i y hy)),rfl⟩
  let s (i : Fin r) : B.val.obj (op U) := ⟨t i,ht i⟩
  refine ⟨U,hx,r,s,?_⟩
  intro y hy
  calc
    _ = actualWholeSheafStalkIdeal A y := actualIdealModule_stalkRange A hA y
    _ = Ideal.span (range fun i => actualOriginalFunctionGerm y (f i) (hhol i y hy)) :=
      wholeIdeal_eq_function_span A y f (fun i => hhol i y hy) (hgen y hy)
    _ = _ := by congr 1; exact congrArg range (funext fun i => htg i y hy)

/-- Original coherence gives one actual finite epi and WHOLE nearby image span. -/
theorem exists_local_finite_generators (A : GermIdeal n M) (hA : A.IsCoherent) (x : M) :
    ∃ (U : Opens M) (_hxU : x ∈ U) (r : ℕ)
      (s : Fin r → (actualIdealModuleSheaf A).val.obj (op U)),
      Epi (freeOverMap (actualComplexStructureSheaf (n := n) M) U s) ∧
      ∀ (y : M) (hy : y ∈ U),
        LinearMap.range (stalkInclusionLinearMap (actualComplexStructureSheaf (n := n) M)
          (actualIdealModuleSheaf A) (actualIdealModuleInclusion A) y) =
        Ideal.span (range fun i => (actualComplexStructureSheaf (n := n) M).presheaf.germ
          U y hy ((actualIdealModuleInclusion A).val.app (op U) (s i))) := by
  obtain ⟨U,hx,r,s,hspan⟩ := exists_coherent_actual_section_family A hA x
  exact ⟨U,hx,r,s,finite_free_epi_of_whole_image_span
    (actualComplexStructureSheaf (n := n) M) (actualIdealModuleInclusion A)
      (by intro W; exact Subtype.val_injective) U s hspan,hspan⟩

/-- This is the STANDARD native finite-type property of the SAME old module. -/
theorem actualIdealModuleSheaf_isFiniteType (A : GermIdeal n M) (hA : A.IsCoherent) :
    (actualIdealModuleSheaf A).IsFiniteType := by
  classical
  let R := actualComplexStructureSheaf (n := n) M
  let B := actualIdealModuleSheaf A
  choose U hx r s hp hspan using exists_local_finite_generators A hA
  let gs (x : M) : (B.over (U x)).GeneratingSections := by
    letI : Epi (freeOverMap R (U x) (s x)) := hp x
    exact (SheafOfModules.free.generatingSections (Fin (r x))).ofEpi
      ((freeOverIso R (U x) (Fin (r x))).hom ≫ freeOverMap R (U x) (s x))
  have hgs (x : M) : (gs x).IsFiniteType := ⟨inferInstanceAs (Finite (Fin (r x)))⟩
  let q : B.LocalGeneratorsData.{0} :=
    { I := M
      X := U
      coversTop := by
        intro V
        apply (Opens.mem_grothendieckTopology (TopCat.of M)).mpr
        intro x hxV
        refine ⟨V ⊓ U x,homOfLE inf_le_left,?_,⟨hxV,hx x⟩⟩
        exact (Sieve.mem_ofObjects_iff U _).mpr ⟨x,⟨homOfLE inf_le_right⟩⟩
      generators := gs }
  exact ⟨⟨q,⟨hgs⟩⟩⟩

end Hironaka.HironakaLegacyCoherentIdealFiniteType
