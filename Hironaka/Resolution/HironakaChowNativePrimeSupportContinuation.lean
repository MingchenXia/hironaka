import Hironaka.Resolution.HironakaChowNativeFiniteTypeSpreading
import Hironaka.Resolution.HironakaChowNativeArbitraryOverRealization
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions
import Hironaka.Resolution.HironakaLegacyCoherentIdealFiniteType
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Analytic.IrreducibleGermConnected
import Hironaka.Analytic.LocalStatementAssembly
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.FibreDimensionLowerBound
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! Actual native cyclic prime layers and whole morphism continuation.
The ordinary input is a prime in the actual ambient stalk.  The target
and its real open are chosen BEFORE arbitrary finite-type sources/maps.
No claim that all nearby stalks are prime is used.  Exact filtration
spreading of a general module, including repeated/embedded layers, is
separate.  Blueprint FIRST: hironaka-g10-native-prime-support-continuation.tex. -/

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaChowNativePrimeSupportContinuation

open Hironaka.HolomorphicIdealSheaves
  HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk HironakaChowNativeModuleStalkExact
  HironakaChowNativeFiniteFreeStalk HironakaSingularRankOneLocalGenerators
  HironakaChowNativeSectionSpreading HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading HironakaChowNativeArbitraryOverRealization
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceResidue

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private instance subspaceMapContinuous (W : Set M) :
    (Opens.map (actualSubspaceTopInclusion W)).IsContinuous
      (Opens.grothendieckTopology (TopCat.of M))
      (Opens.grothendieckTopology (TopCat.of W)) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (actualSubspaceTopInclusion W)
  · exact coverPreserving_opens_map (actualSubspaceTopInclusion W)

/-- The native ring-sheaf morphism underlying the actual closed inclusion.
The underlying sections and scalar maps are the original factories. -/
private def subspaceRingMap (W : Set M) :
    forgetRing (actualComplexStructureSheaf (n := n) M) ⟶
      ((Opens.map (actualSubspaceTopInclusion W)).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (TopCat.of M))
        (Opens.grothendieckTopology (TopCat.of W))).obj
          (forgetRing (actualSubspaceSheaf (n := n) W)) where
  hom := Functor.whiskerRight (actualSubspaceInclusion (n := n) W).toHom.c
    (forget₂ CommRingCat RingCat)

/-- The existing native pushforward of the actual subspace unit module. -/
private abbrev supportModule (W : Set M) :
    SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M)) :=
  (SheafOfModules.pushforward (subspaceRingMap (n := n) W)).obj
    (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W)))

private def supportQuotient (W : Set M) :
    SheafOfModules.unit (forgetRing (actualComplexStructureSheaf (n := n) M)) ⟶
      supportModule (n := n) W :=
  SheafOfModules.unitToPushforwardObjUnit (subspaceRingMap (n := n) W)

private theorem supportQuotient_app (W : Set M) (V : Opens M)
    (s : actualComplexSection (n := n) V) :
    (supportQuotient (n := n) W).val.app (op V) s =
      (actualSubspaceInclusion (n := n) W).toHom.c.app (op V) s := rfl

private def supportValue (W : Set M) (V : Opens M)
    (s : (supportModule (n := n) W).val.obj (op V))
    (y : W) (hy : y.val ∈ V) : ℂ :=
  actualSubspaceStalkEval (n := n) W y
    ((actualSubspaceSheaf (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion W)).obj V) y hy s)

private theorem supportValue_restrict (W : Set M) (V T : Opens M) (hTV : T ≤ V)
    (s : (supportModule (n := n) W).val.obj (op V)) (y : W) (hy : y.val ∈ T) :
    supportValue W T ((supportModule W).val.map (homOfLE hTV).op s) y hy =
      supportValue W V s y (hTV hy) := by
  exact congrArg (actualSubspaceStalkEval (n := n) W y)
    ((actualSubspaceSheaf (n := n) W).presheaf.germ_res_apply
      ((Opens.map (actualSubspaceTopInclusion W)).map (homOfLE hTV)) y hy s)

private theorem supportValue_quotient (W : Set M) (V : Opens M)
    (s : actualComplexSection (n := n) V) (y : W) (hy : y.val ∈ V) :
    supportValue W V ((supportQuotient W).val.app (op V) s) y hy = s ⟨y.val,hy⟩ := by
  exact (congrArg (actualSubspaceStalkEval (n := n) W y)
    (LocallyRingedSpace.stalkMap_germ_apply (actualSubspaceInclusion (n := n) W)
      V y hy s).symm).trans (actualSubspaceStalkEval_inclusion_germ W V s y hy)

private theorem supportSection_eq_zero (W : Set M) (V : Opens M)
    (s : (supportModule (n := n) W).val.obj (op V))
    (hs : ∀ (y : W) (hy : y.val ∈ V), supportValue W V s y hy = 0) : s = 0 := by
  exact actualSubspaceSection_eq_zero_of_eval W
    ((Opens.map (actualSubspaceTopInclusion W)).obj V) s hs

private def supportStalkValue (W : Set M) (y : W) :
    ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y.val) →+ ℂ :=
  (actualSubspaceStalkEval (n := n) W y).toAddMonoidHom.comp
    ((unitStalkLinearEquiv (actualSubspaceSheaf (n := n) W) y).toAddMonoidHom.comp
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat (actualSubspaceTopInclusion W)
        (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf y).hom)

private theorem supportStalkValue_germ (W : Set M) (V : Opens M)
    (s : (supportModule (n := n) W).val.obj (op V)) (y : W) (hy : y.val ∈ V) :
    supportStalkValue W y (TopCat.Presheaf.germ (supportModule W).val.presheaf V y.val hy s) =
      supportValue W V s y hy := by
  unfold supportStalkValue
  simp only [AddMonoidHom.comp_apply]
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat (actualSubspaceTopInclusion W)
      (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf V y hy) s
  exact (congrArg (fun a => actualSubspaceStalkEval (n := n) W y
    (unitStalkLinearEquiv (actualSubspaceSheaf (n := n) W) y a)) h).trans
      (congrArg (actualSubspaceStalkEval (n := n) W y)
        (unitStalkLinearEquiv_germ (actualSubspaceSheaf (n := n) W) y
          ((Opens.map (actualSubspaceTopInclusion W)).obj V) hy s))

private theorem supportValue_smul (W : Set M) (V : Opens M)
    (r : (forgetRing (actualComplexStructureSheaf (n := n) M)).obj.obj (op V))
    (s : (supportModule (n := n) W).val.obj (op V)) (y : W) (hy : y.val ∈ V) :
    supportValue W V (r • s) y hy =
      (show actualComplexSection (n := n) V from r) ⟨y.val,hy⟩ * supportValue W V s y hy := by
  let T := ((Opens.map (actualSubspaceTopInclusion W)).obj V)
  let a : (actualSubspaceSheaf (n := n) W).presheaf.obj (op T) :=
    (actualSubspaceInclusion (n := n) W).toHom.c.app (op V) r
  let b : (actualSubspaceSheaf (n := n) W).presheaf.obj (op T) := s
  let ev := (actualSubspaceStalkEval (n := n) W y).comp
    ((actualSubspaceSheaf (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion W)).obj V) y hy).hom
  change ev (a * b) = (show actualComplexSection (n := n) V from r) ⟨y.val,hy⟩ * ev b
  exact (ev.map_mul _ _).trans
    (congrArg (fun a => a * ev s) (supportValue_quotient W V r y hy))

private def supportScalarResidue (W : Set M) (y : W) :
    actualComplexStructureStalk (n := n) y.val →+* ℂ :=
  (actualSubspaceStalkEval (n := n) W y).comp
    ((actualSubspaceInclusion (n := n) W).stalkMap y).hom

private theorem supportScalarResidue_germ (W : Set M) (V : Opens M)
    (r : actualComplexSection (n := n) V) (y : W) (hy : y.val ∈ V) :
    supportScalarResidue W y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ V y.val hy r) = r ⟨y.val,hy⟩ :=
  actualSubspaceStalkEval_inclusion_germ W V r y hy

private instance manifoldNativeStalkModule
    (G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))) (y : M) :
    Module ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y) :=
  nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) G y

private instance manifoldNativePresheafStalkModule
    (G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))) (y : M) :
    Module ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).presheaf y)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y) :=
  nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) G y

private theorem supportStalkValue_smul (W : Set M) (y : W)
    (r : ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y.val))
    (m : ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y.val)) :
    supportStalkValue W y (r • m) = supportScalarResidue W y r * supportStalkValue W y m := by
  obtain ⟨U,hyU,m,rfl⟩ := TopCat.Presheaf.exists_germ_eq (supportModule W).val.presheaf m
  obtain ⟨V,hVU,hyV,r,rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (actualComplexStructureSheaf (n := n) M).presheaf r hyU
  rw [← TopCat.Presheaf.germ_res_apply (supportModule W).val.presheaf
    (homOfLE hVU) y.val hyV m]
  erw [← PresheafOfModules.germ_smul (R := (actualComplexStructureSheaf (n := n) M).obj),
    supportStalkValue_germ,supportValue_smul,supportScalarResidue_germ,supportStalkValue_germ]

/-- An intrinsic zero locus defined by all original local source sections.
Finite type will derive finite analytic equations for this same set. -/
private def fibreZeroLocus (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    (f : G ⟶ supportModule (n := n) W) : Set M :=
  {y | ∃ hyW : y ∈ W, ∀ (V : Opens M) (hy : y ∈ V) (s : G.val.obj (op V)),
    supportValue W V (f.val.app (op V) s) ⟨y,hyW⟩ hy = 0}

private def supportValueKernel (W : Set M) (y : W) :
    Submodule ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y.val)
      ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y.val) where
  carrier := {m | supportStalkValue (n := n) W y m = 0}
  zero_mem' := (supportStalkValue (n := n) W y).map_zero
  add_mem' := by
    intro m k hm hk
    exact ((supportStalkValue (n := n) W y).map_add m k).trans
      ((congrArg₂ (·+·) hm hk).trans (add_zero 0))
  smul_mem' := by
    intro r m hm
    exact (supportStalkValue_smul (n := n) W y r m).trans
      ((congrArg (fun a => supportScalarResidue (n := n) W y r * a) hm).trans (mul_zero _))

private def fibreKernel (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    (f : G ⟶ supportModule (n := n) W) (y : W) :
    Submodule ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y.val)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y.val) := by
  exact @Submodule.comap
    ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y.val)
    ↑(TopCat.Presheaf.stalk (actualComplexStructureSheaf (n := n) M).obj y.val)
    ↑(TopCat.Presheaf.stalk G.val.presheaf y.val)
    ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y.val)
    inferInstance inferInstance inferInstance inferInstance
    (nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) G y.val)
    (nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) (supportModule W) y.val)
    (RingHom.id _)
    (stalkLinearMap (R := (actualComplexStructureSheaf (n := n) M).obj)
      (M := G.val) (N := (supportModule (n := n) W).val) f.val y.val)
    (supportValueKernel (n := n) W y)

private theorem mem_fibreZeroLocus_iff (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    (f : G ⟶ supportModule (n := n) W) (y : W) :
    y.val ∈ fibreZeroLocus W f ↔ fibreKernel W f y = ⊤ := by
  constructor
  · rintro ⟨_,hy⟩
    apply top_unique
    intro m _
    obtain ⟨V,hyV,s,rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
    change supportStalkValue W y
      (stalkLinearMap f.val y.val (TopCat.Presheaf.germ G.val.presheaf V y.val hyV s)) = 0
    erw [stalkLinearMap_germ,supportStalkValue_germ]
    exact hy V hyV s
  · intro h
    refine ⟨y.property,?_⟩
    intro V hyV s
    have hm : TopCat.Presheaf.germ G.val.presheaf V y.val hyV s ∈ fibreKernel W f y := by
      rw [h]
      trivial
    change supportStalkValue W y
      (stalkLinearMap f.val y.val (TopCat.Presheaf.germ G.val.presheaf V y.val hyV s)) = 0 at hm
    erw [stalkLinearMap_germ,supportStalkValue_germ] at hm
    exact hm

section Generators
variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  {G : SheafOfModules.{0} (forgetRing R)}

private def generatorSection (U : Opens X) (σ : (G.over U).GeneratingSections) (i : σ.I) :
    G.val.obj (op U) := (σ.s i).val (op (Over.mk (𝟙 U)))

private def generatorMap (U : Opens X) (σ : (G.over U).GeneratingSections) :
    (SheafOfModules.free (R := forgetRing R) σ.I).over U ⟶ G.over U :=
  (freeOverIso R U σ.I).inv ≫ σ.π

private instance generatorMap_epi (U : Opens X) (σ : (G.over U).GeneratingSections) :
    Epi (generatorMap R U σ) := by
  dsimp [generatorMap]
  infer_instance

private theorem generatorMap_ι (U : Opens X) (σ : (G.over U).GeneratingSections) (i : σ.I) :
    (SheafOfModules.ιFree (R := forgetRing R) i).over U ≫ generatorMap R U σ =
      localUnitMap R U (generatorSection R U σ i) := by
  have hs : σ.s = fun j => (G.over U).unitHomEquiv
      (localUnitMap R U (generatorSection R U σ j)) := by
    funext j
    ext V
    rw [SheafOfModules.unitHomEquiv_apply_coe]
    erw [localUnitMap_app,one_smul]
    let a : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
    exact ((σ.s j).property a.op).symm
  have he : generatorMap R U σ = freeOverMap R U (generatorSection R U σ) := by
    unfold generatorMap freeOverMap
    exact congrArg (fun s => (freeOverIso R U σ.I).inv ≫ (G.over U).freeHomEquiv.symm s) hs
  exact (congrArg (fun k => (SheafOfModules.ιFree (R := forgetRing R) i).over U ≫ k) he).trans
    (ι_freeOverMap R U (generatorSection R U σ) i)

private theorem generatorMap_stalk_ι (U : Opens X) (σ : (G.over U).GeneratingSections)
    (x : X) (hxU : x ∈ U) (i : σ.I) (a : ↑(TopCat.Presheaf.stalk R.obj x)) :
    stalkLinearMapOfOver R U (generatorMap R U σ) x hxU
      (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
        ((unitStalkLinearEquiv R x).symm a)) =
      a • TopCat.Presheaf.germ G.val.presheaf U x hxU (generatorSection R U σ i) := by
  have h := congrArg (fun k => stalkLinearMapOfOver R U k x hxU) (generatorMap_ι R U σ i)
  rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_homOver] at h
  exact (LinearMap.congr_fun h ((unitStalkLinearEquiv R x).symm a)).trans
    (localUnitMap_stalk R U (generatorSection R U σ i) x hxU a)

private theorem generatorSection_stalk_span (U : Opens X) (σ : (G.over U).GeneratingSections)
    [σ.IsFiniteType] (x : X) (hxU : x ∈ U) :
    Submodule.span ↑(TopCat.Presheaf.stalk R.obj x)
      (range fun i => TopCat.Presheaf.germ G.val.presheaf U x hxU (generatorSection R U σ i)) = ⊤ := by
  classical
  let := Fintype.ofFinite σ.I
  let e := finiteFreeStalkLinearEquiv R σ.I x
  let p := stalkLinearMapOfOver R U (generatorMap R U σ) x hxU
  apply top_unique
  intro m _
  obtain ⟨v,rfl⟩ := stalkLinearMapOfOver_surjective_of_epi R U (generatorMap R U σ) x hxU m
  have hv : v = ∑ i : σ.I, (e v i) • e.symm (Pi.single i 1) := by
    apply e.injective
    simp only [map_sum,map_smul,LinearEquiv.apply_symm_apply]
    exact ((Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) σ.I).sum_repr (e v)).symm
  change p v ∈ _
  rw [hv,map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  have hi : e.symm (Pi.single i 1) =
      stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
        ((unitStalkLinearEquiv R x).symm 1) :=
    e.symm_apply_eq.mpr (finiteFreeStalkLinearEquiv_ι R σ.I x i 1).symm
  rw [hi]
  change stalkLinearMapOfOver R U (generatorMap R U σ) x hxU _ ∈ _
  rw [generatorMap_stalk_ι,one_smul]
  exact Submodule.subset_span (mem_range_self i)
end Generators

private theorem exists_open_stalk_zero {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} [G.IsFiniteType] (f : G ⟶ H)
    (p : X) (hp : stalkLinearMap f.val p = 0) :
    ∃ (U : Opens X), p ∈ U ∧ ∀ (y : X), y ∈ U → stalkLinearMap f.val y = 0 := by
  have he : stalkLinearMapOfOver R ⊤ (f.over ⊤) p (by trivial) =
      stalkLinearMapOfOver R ⊤ ((0 : G ⟶ H).over ⊤) p (by trivial) :=
    (stalkLinearMapOfOver_homOver R f ⊤ p (by trivial)).trans
      (hp.trans ((stalkLinearMapOfOver_homOver R (0 : G ⟶ H) ⊤ p (by trivial)).trans
        (stalkLinearMap_zero p)).symm)
  obtain ⟨U,hU,hpU,hfU⟩ := exists_restriction_eq_of_isFiniteType R ⊤
    (f.over ⊤) ((0 : G ⟶ H).over ⊤) p (by trivial) he
  refine ⟨U,hpU,?_⟩
  intro y hyU
  have hs := congrArg (fun k => stalkLinearMapOfOver R U k y hyU) hfU
  have hf := (stalkLinearMapOfOver_restrictOverHom R ⊤ U hU (f.over ⊤) y hyU).trans
    (stalkLinearMapOfOver_homOver R f ⊤ y (by trivial))
  have hz := (stalkLinearMapOfOver_restrictOverHom R ⊤ U hU ((0 : G ⟶ H).over ⊤) y hyU).trans
    ((stalkLinearMapOfOver_homOver R (0 : G ⟶ H) ⊤ y (by trivial)).trans (stalkLinearMap_zero y))
  exact hf.symm.trans (hs.trans hz)

private theorem mem_fibreZeroLocus_iff_generators (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    (f : G ⟶ supportModule (n := n) W) (U : Opens M)
    (σ : (G.over U).GeneratingSections) [σ.IsFiniteType] (y : W) (hyU : y.val ∈ U) :
    y.val ∈ fibreZeroLocus W f ↔ ∀ i : σ.I,
      supportValue W U (f.val.app (op U)
        (generatorSection (actualComplexStructureSheaf (n := n) M) U σ i)) y hyU = 0 := by
  constructor
  · rintro ⟨_,hy⟩ i
    exact hy U hyU _
  · intro h
    apply (mem_fibreZeroLocus_iff W f y).mpr
    apply top_unique
    rw [← generatorSection_stalk_span (actualComplexStructureSheaf (n := n) M) U σ y.val hyU]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change supportStalkValue W y (stalkLinearMap f.val y.val
      (TopCat.Presheaf.germ G.val.presheaf U y.val hyU
        (generatorSection (actualComplexStructureSheaf (n := n) M) U σ i))) = 0
    erw [stalkLinearMap_germ,supportStalkValue_germ]
    exact h i

private theorem hom_eq_zero_of_fibreZero (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    (f : G ⟶ supportModule (n := n) W) (h : W ⊆ fibreZeroLocus W f) : f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change f.val.app V s = 0
  apply supportSection_eq_zero W V.unop
  intro y hy
  exact (h y.property).choose_spec V.unop hy s

private theorem common_zero_analytic {k : ℕ} (g : Fin k → M → ℂ)
    (hg : ∀ i, ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (g i)) :
    IsComplexAnalyticSubset (n := n) {y | ∀ i, g i y = 0} := by
  let F : M → ComplexModel k := fun y =>
    (EuclideanSpace.equiv (Fin k) ℂ).symm (fun i => g i y)
  have hF : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k) ∞ F :=
    (EuclideanSpace.equiv (Fin k) ℂ).symm.toContinuousLinearMap.contMDiff.comp
      (contMDiff_pi_space.mpr hg)
  have ha := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hF
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel k))
  have he : F ⁻¹' {0} = {y | ∀ i, g i y = 0} := by
    ext y
    change F y = 0 ↔ ∀ i, g i y = 0
    constructor
    · intro h i
      exact congrArg (fun z : ComplexModel k => z i) h
    · intro h
      apply PiLp.ext
      intro i
      exact h i
  exact he ▸ ha

private theorem exists_fibreZero_equations (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    [G.IsFiniteType] (f : G ⟶ supportModule (n := n) W) (y : W) :
    ∃ (O : Opens M) (_hyO : y.val ∈ O) (k : ℕ)
      (t : Fin k → actualComplexSection (n := n) O),
      ∀ (z : M) (hz : z ∈ O),
        z ∈ fibreZeroLocus W f ↔ z ∈ W ∧ ∀ i, t i ⟨z,hz⟩ = 0 := by
  classical
  let R := actualComplexStructureSheaf (n := n) M
  obtain ⟨q,hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  obtain ⟨V,j,hV,hyV⟩ :=
    (Opens.mem_grothendieckTopology (TopCat.of M)).mp (q.coversTop ⊤) y.val (by trivial)
  obtain ⟨a,⟨ha⟩⟩ := (Sieve.mem_ofObjects_iff q.X j).mp hV
  let Q := q.X a
  have hyQ : y.val ∈ Q := ha.le hyV
  let σ := q.generators a
  have : σ.IsFiniteType := hq.isFiniteType a
  let := Fintype.ofFinite σ.I
  let k := Fintype.card σ.I
  let e := Fintype.equivFin σ.I
  let s (i : Fin k) : (supportModule (n := n) W).val.obj (op Q) :=
    f.val.app (op Q) (generatorSection R Q σ (e.symm i))
  choose O hyO t hOQ ht using fun i : Fin k =>
    actualSubspaceSection_local_ambient W
      ((Opens.map (actualSubspaceTopInclusion W)).obj Q) (s i) y hyQ
  let T : Opens M := Q ⊓ ⨅ i : Fin k, O i
  have hTQ : T ≤ Q := inf_le_left
  have hTO (i : Fin k) : T ≤ O i := inf_le_right.trans (iInf_le O i)
  have hyT : y.val ∈ T := by
    change y.val ∈ (Q : Set M) ∩ ((⨅ i : Fin k, O i : Opens M) : Set M)
    rw [Opens.coe_iInf]
    exact ⟨hyQ,mem_iInter.mpr hyO⟩
  let tT (i : Fin k) : actualComplexSection (n := n) T :=
    R.obj.map (homOfLE (hTO i)).op (t i)
  have hvalue (i : Fin k) (z : W) (hz : z.val ∈ T) :
      supportValue W Q (s i) z (hTQ hz) = tT i ⟨z.val,hz⟩ := by
    have hh := congrArg (actualSubspaceStalkEval (n := n) W z) (ht i z (hTO i hz))
    exact hh.trans (actualSubspaceStalkEval_inclusion_germ W (O i) (t i) z (hTO i hz))
  refine ⟨T,hyT,k,tT,?_⟩
  intro z hz
  constructor
  · rintro h
    have hzW : z ∈ W := h.choose
    refine ⟨hzW,?_⟩
    have hgens := (mem_fibreZeroLocus_iff_generators W f Q σ ⟨z,hzW⟩ (hTQ hz)).mp h
    intro i
    exact (hvalue i ⟨z,hzW⟩ hz).symm.trans (hgens (e.symm i))
  · rintro ⟨hzW,h⟩
    apply (mem_fibreZeroLocus_iff_generators W f Q σ ⟨z,hzW⟩ (hTQ hz)).mpr
    intro i
    have hh := (hvalue (e i) ⟨z,hzW⟩ hz).trans (h (e i))
    simpa only [s,Equiv.symm_apply_apply] using hh

private theorem fibreZero_analytic (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    [G.IsFiniteType] (f : G ⟶ supportModule (n := n) W) :
    IsComplexAnalyticSubset (n := n) (fibreZeroLocus W f) := by
  classical
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro y
  by_cases hyW : y ∈ W
  · obtain ⟨O,hyO,k,t,ht⟩ := exists_fibreZero_equations W f ⟨y,hyW⟩
    refine ⟨O,hyO,?_⟩
    have he : (Subtype.val ⁻¹' fibreZeroLocus W f : Set O) =
        (Subtype.val ⁻¹' W) ∩ {z : O | ∀ i : Fin k, t i z = 0} := by
      ext z
      exact ht z.val z.property
    rw [he]
    exact (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O).inter
      (common_zero_analytic (fun i z => t i z) (fun i => smoothSheaf.contMDiff_section (t i)))
  · let O : Opens M := ⟨Wᶜ,hW.isClosed.isOpen_compl⟩
    refine ⟨O,hyW,?_⟩
    have he : (Subtype.val ⁻¹' fibreZeroLocus W f : Set O) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact z.property hz.choose
    rw [he]
    exact isComplexAnalyticSubset_empty

private theorem exists_fibreZero_neighborhood (W : Set M)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    [G.IsFiniteType] (f : G ⟶ supportModule (n := n) W) (p : M)
    (hp : stalkLinearMap f.val p = 0) :
    ∃ (U : Opens M), p ∈ U ∧ W ∩ (U : Set M) ⊆ fibreZeroLocus W f := by
  obtain ⟨U,hpU,hfU⟩ := exists_open_stalk_zero (actualComplexStructureSheaf (n := n) M) f p hp
  refine ⟨U,hpU,?_⟩
  rintro y ⟨hyW,hyU⟩
  refine ⟨hyW,?_⟩
  intro V hyV s
  let : Module ↑(TopCat.Presheaf.stalk
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of M)) CommRingCat).obj
        (actualComplexStructureSheaf (n := n) M)) y)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y) :=
    nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) G y
  let : Module ↑(TopCat.Presheaf.stalk
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of M)) CommRingCat).obj
        (actualComplexStructureSheaf (n := n) M)) y)
      ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y) :=
    nativeSheafStalkModule (actualComplexStructureSheaf (n := n) M) (supportModule W) y
  have hh := congrArg (fun L =>
    L (TopCat.Presheaf.germ G.val.presheaf V y hyV s)) (hfU y hyU)
  have hv := (congrArg (supportStalkValue W ⟨y,hyW⟩) hh).trans (map_zero _)
  erw [stalkLinearMap_germ,supportStalkValue_germ] at hv
  exact hv

/-- The target support and ambient are fixed before every source/map.
The regular point is part of the actual geometry, not a supplied
continuation certificate.  The prime producer constructs it internally. -/
private theorem component_support_hom_continuation {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k)
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    [G.IsFiniteType]
    (f : G ⟶ supportModule (n := n) (closure (RegularLocusComponent.component (n := n) A c)))
    (p : M) (hpW : p ∈ closure (RegularLocusComponent.component (n := n) A c))
    (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  let K := RegularLocusComponent.component (n := n) A c
  let W := closure K
  have hW : IsComplexAnalyticSubset (n := n) W :=
    RegularLocusComponent.isComplexAnalyticSubset_closure_component hA hc
  have hB := fibreZero_analytic W hW f
  obtain ⟨U,hpU,hUB⟩ := exists_fibreZero_neighborhood W f p hp
  obtain ⟨q,hqU,hqK⟩ := mem_closure_iff.mp hpW U U.isOpen hpU
  have hKB : K ⊆ fibreZeroLocus W f :=
    RegularLocusComponent.component_subset_of_isOpen hB U.isOpen
      ⟨q,hqU,hqK⟩ (fun y hy => hUB ⟨subset_closure hy.2,hy.1⟩)
  exact hom_eq_zero_of_fibreZero W f (closure_minimal hKB hB.isClosed)

private def unitDomainStalkMap {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X) :
    ↑(TopCat.Presheaf.stalk R.obj y) →ₗ[↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk T.val.presheaf y) :=
  (stalkLinearMap f.val y).comp (unitStalkLinearEquiv R y).symm.toLinearMap

private theorem unitDomainStalkMap_germ {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X)
    (V : Opens X) (hy : y ∈ V) (r : R.obj.obj (op V)) :
    unitDomainStalkMap R f y (R.presheaf.germ V y hy r) =
      TopCat.Presheaf.germ T.val.presheaf V y hy (f.val.app (op V) r) := by
  have hm : (unitStalkLinearEquiv R y).symm (R.presheaf.germ V y hy r) =
      TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf V y hy r :=
    (unitStalkLinearEquiv R y).symm_apply_eq.mpr (unitStalkLinearEquiv_germ R y V hy r).symm
  exact (congrArg (stalkLinearMap f.val y) hm).trans (stalkLinearMap_germ f.val y V hy r)

private def unitStalkAddEquiv {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0}) (y : X) :
    ↑(TopCat.Presheaf.stalk (SheafOfModules.unit (forgetRing R)).val.presheaf y) ≃+
      ↑(TopCat.Presheaf.stalk R.obj y) :=
  (unitStalkLinearEquiv R y).toAddEquiv

private def supportStalkAddEquiv (W : Set M) (y : W) :
    ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y.val) ≃+
      ↑((actualSubspaceSheaf (n := n) W).presheaf.stalk y) := by
  let F := (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf
  let f := TopCat.Presheaf.stalkPushforward AddCommGrpCat (actualSubspaceTopInclusion W) F y
  have h : IsIso f :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat
      (show Topology.IsInducing (actualSubspaceTopInclusion W) from Topology.IsInducing.subtypeVal) F y
  exact (asIso f).addCommGroupIsoToAddEquiv.trans
    (unitStalkAddEquiv (actualSubspaceSheaf (n := n) W) y)

private theorem supportStalkAddEquiv_germ (W : Set M) (V : Opens M)
    (s : (supportModule (n := n) W).val.obj (op V)) (y : W) (hy : y.val ∈ V) :
    supportStalkAddEquiv W y (TopCat.Presheaf.germ (supportModule W).val.presheaf V y.val hy s) =
      (actualSubspaceSheaf (n := n) W).presheaf.germ
        ((Opens.map (actualSubspaceTopInclusion W)).obj V) y hy s := by
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat (actualSubspaceTopInclusion W)
      (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf V y hy) s
  exact (congrArg (unitStalkLinearEquiv (actualSubspaceSheaf (n := n) W) y) h).trans
    (unitStalkLinearEquiv_germ (actualSubspaceSheaf (n := n) W) y
      ((Opens.map (actualSubspaceTopInclusion W)).obj V) hy s)

private theorem supportStalkAddEquiv_quotient (W : Set M) (y : W)
    (r : actualComplexStructureStalk (n := n) y.val) :
    supportStalkAddEquiv W y
      (unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y.val r) =
      (actualSubspaceInclusion (n := n) W).stalkMap y r := by
  obtain ⟨V,hyV,r,rfl⟩ :=
    (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  erw [unitDomainStalkMap_germ,supportStalkAddEquiv_germ]
  exact (LocallyRingedSpace.stalkMap_germ_apply (actualSubspaceInclusion (n := n) W) V y hyV r).symm

private theorem supportQuotientStalk_surjective (W : Set M) (y : W) :
    Function.Surjective
      (unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y.val) := by
  intro m
  obtain ⟨r,hr⟩ := actualSubspaceInclusionRingedHom_stalk_surjective W y (supportStalkAddEquiv W y m)
  refine ⟨r,(supportStalkAddEquiv W y).injective ?_⟩
  exact (supportStalkAddEquiv_quotient W y r).trans hr

private theorem supportQuotientStalk_kernel (W : Set M) (y : W) :
    LinearMap.ker
      (unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y.val) =
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y.val :
        Submodule (actualComplexStructureStalk (n := n) y.val) (actualComplexStructureStalk (n := n) y.val)) := by
  ext r
  change unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y.val r = 0 ↔ _
  rw [← (supportStalkAddEquiv W y).map_eq_zero_iff,supportStalkAddEquiv_quotient]
  exact Iff.rfl.trans (show (actualSubspaceInclusion (n := n) W).stalkMap y r = 0 ↔ _ from by
    change r ∈ RingHom.ker ((actualSubspaceInclusion (n := n) W).stalkMap y).hom ↔ _
    rw [actualSubspaceInclusion_stalk_kernel])

private theorem exists_native_ideal_generators (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) :
    ∃ (U : Opens (ComplexModel n)) (hpU : p ∈ U) (r : ℕ)
      (g : Fin r → actualComplexSection (n := n) U),
      P = Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U p hpU (g i)) := by
  classical
  let R := actualComplexStructureSheaf (n := n) (ComplexModel n)
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  let : IsNoetherianRing (actualComplexStructureStalk (n := n) p) :=
    isNoetherianRing_of_ringEquiv _ (actualStalkChartEquiv (n := n) p).symm
  obtain ⟨r,a,ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (Ideal.fg_of_isNoetherianRing P)
  let v (i : Fin r) := (unitStalkLinearEquiv R p).symm (a i)
  obtain ⟨U,_hU,hpU,s,hs⟩ := exists_common_germ_representatives
    (SheafOfModules.unit (forgetRing R)).val p ⊤ (by trivial) v
  let g (i : Fin r) : actualComplexSection (n := n) U := s i
  have hg (i : Fin r) : R.presheaf.germ U p hpU (g i) = a i :=
    (unitStalkLinearEquiv_germ R p U hpU (s i)).symm.trans
      ((congrArg (unitStalkLinearEquiv R p) (hs i)).trans
        ((unitStalkLinearEquiv R p).apply_symm_apply (a i)))
  refine ⟨U,hpU,r,g,?_⟩
  change Ideal.span (range a) = P at ha
  exact ha.symm.trans (congrArg Ideal.span (congrArg range (funext fun i => (hg i).symm)))

private theorem actualStalkChartEquiv_eval_germ (U : Opens M) (p : M) (hpU : p ∈ U)
    (g : actualComplexSection (n := n) U) :
    HolGerm.eval (actualStalkChartEquiv (n := n) p
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U p hpU g)) = g ⟨p,hpU⟩ := by
  rw [actualStalkChartEquiv_germ]
  change HolGerm.eval (chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p)
    (sectionExtension U g) (sectionExtension_holomorphicAt U g p hpU)) = _
  simpa only [chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,zero_add,
    (chartAt (ComplexModel n) p).left_inv (mem_chart_source (ComplexModel n) p)] using
    sectionExtension_apply U g p hpU

/-- These total functions are used ONLY as representatives near zero,
inside the genuine translated original section domain. -/
private def translatedSectionFamily {r : ℕ} (p : ComplexModel n)
    (U : Opens (ComplexModel n)) (g : Fin r → actualComplexSection (n := n) U) :
    Fin r → ComplexModel n → ℂ := fun i z => sectionExtension U (g i) (z+p)

private theorem translatedSectionFamily_hol {r : ℕ} (p : ComplexModel n)
    (U : Opens (ComplexModel n)) (hpU : p ∈ U)
    (g : Fin r → actualComplexSection (n := n) U) (i : Fin r) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (translatedSectionFamily p U g i) z :=
  translated_holomorphic p
    ((sectionExtension_holomorphicAt U (g i) p hpU).mono fun _ h => h.differentiableAt)

private theorem prime_section_zero_germ {r : ℕ} (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime]
    (U : Opens (ComplexModel n)) (hpU : p ∈ U)
    (g : Fin r → actualComplexSection (n := n) U)
    (hP : P = Ideal.span (range fun i =>
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U p hpU (g i))) :
    AnalyticGermDecomposition.vanishingIdeal
        {z | ∀ i, translatedSectionFamily p U g i z = 0} =
      Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom P := by
  classical
  let R := actualComplexStructureSheaf (n := n) (ComplexModel n)
  let e := actualStalkChartEquiv (n := n) p
  let Q := Ideal.map e.toRingHom P
  have : Q.IsPrime := Ideal.map_isPrime_of_equiv e
  let f := translatedSectionFamily p U g
  have hf (i : Fin r) := translatedSectionFamily_hol p U hpU g i
  have he (i : Fin r) : e (R.presheaf.germ U p hpU (g i)) = HolGerm.mk (f i) (hf i) := by
    rw [actualStalkChartEquiv_germ]
    change chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p)
      (sectionExtension U (g i)) (sectionExtension_holomorphicAt U (g i) p hpU) = _
    simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
    rfl
  have hQ : Q = Ideal.span (range fun i => HolGerm.mk (f i) (hf i)) := by
    change Ideal.map e.toRingHom P = _
    rw [hP,Ideal.map_span,← Set.range_comp]
    exact congrArg Ideal.span (congrArg range (funext he))
  have hmem (i : Fin r) : HolGerm.mk (f i) (hf i) ∈ Q := by
    rw [hQ]
    exact Ideal.subset_span (mem_range_self i)
  apply le_antisymm
  · exact GermPrimeNullstellensatz.vanishingIdeal_le_of_isPrime Q f (fun i => ⟨hf i,hmem i⟩)
  · change Q ≤ AnalyticGermDecomposition.vanishingIdeal {z | ∀ i, f i z = 0}
    rw [hQ]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun z hz => hz i)

private theorem supportStalk_eq_zero_off (W : Set M) (hW : IsClosed W)
    (y : M) (hyW : y ∉ W)
    (m : ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y)) : m = 0 := by
  obtain ⟨U,hyU,s,rfl⟩ := TopCat.Presheaf.exists_germ_eq (supportModule W).val.presheaf m
  let V : Opens M := U ⊓ ⟨Wᶜ,hW.isOpen_compl⟩
  have hVU : V ≤ U := inf_le_left
  have hyV : y ∈ V := ⟨hyU,hyW⟩
  have hs : (supportModule W).val.map (homOfLE hVU).op s = 0 := by
    apply supportSection_eq_zero W V
    intro z hz
    exact (hz.2 z.property).elim
  exact (TopCat.Presheaf.germ_res_apply (supportModule W).val.presheaf
    (homOfLE hVU) y hyV s).symm.trans
      ((congrArg (TopCat.Presheaf.germ (supportModule W).val.presheaf V y hyV) hs).trans (map_zero _))

private theorem supportWholeIdeal_eq_top_off (W : Set M) (hW : IsClosed W)
    (y : M) (hyW : y ∉ W) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y = ⊤ := by
  apply top_unique
  intro r _
  obtain ⟨U,hyU,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  let f := sectionExtension U s
  have hf : HolomorphicAt n f y := sectionExtension_holomorphicAt U s y hyU
  have hm : (vanishingIdeal (n := n) W).mem y f := by
    refine ⟨hf,?_⟩
    filter_upwards [hW.isOpen_compl.mem_nhds hyW] with z hz hzW
    exact (hz hzW).elim
  have hg : actualOriginalFunctionGerm y f hf ∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y :=
    Ideal.subset_span ⟨f,hf,hm,rfl⟩
  have he := actualOriginalFunctionGerm_eq_section U y hyU s f hf (EventuallyEq.refl _ _)
  exact he ▸ hg

private theorem supportQuotientStalk_surjective_all (W : Set M) (hW : IsClosed W) (y : M) :
    Function.Surjective
      (unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y) := by
  classical
  by_cases hyW : y ∈ W
  · exact supportQuotientStalk_surjective W ⟨y,hyW⟩
  · intro m
    refine ⟨0,?_⟩
    exact (supportStalk_eq_zero_off W hW y hyW _).trans
      (supportStalk_eq_zero_off W hW y hyW m).symm

private theorem supportQuotientStalk_kernel_all (W : Set M) (hW : IsClosed W) (y : M) :
    LinearMap.ker
      (unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y) =
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y :
        Submodule (actualComplexStructureStalk (n := n) y) (actualComplexStructureStalk (n := n) y)) := by
  classical
  by_cases hyW : y ∈ W
  · exact supportQuotientStalk_kernel W ⟨y,hyW⟩
  · ext r
    constructor
    · intro _
      rw [supportWholeIdeal_eq_top_off W hW y hyW]
      trivial
    · intro _
      exact supportStalk_eq_zero_off W hW y hyW _

private def unitDomainStalkQuotientEquiv {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X)
    (I : Ideal ↑(TopCat.Presheaf.stalk R.obj y))
    (hI : LinearMap.ker (unitDomainStalkMap R f y) =
      (I : Submodule ↑(TopCat.Presheaf.stalk R.obj y) ↑(TopCat.Presheaf.stalk R.obj y)))
    (hs : Function.Surjective (unitDomainStalkMap R f y)) :
    (↑(TopCat.Presheaf.stalk R.obj y) ⧸ I) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk T.val.presheaf y) :=
  (Submodule.quotEquivOfEq (I : Submodule _ _) (LinearMap.ker (unitDomainStalkMap R f y)) hI.symm).trans
    ((unitDomainStalkMap R f y).quotKerEquivOfSurjective hs)

private theorem unitDomainStalkQuotientEquiv_mk {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X)
    (I : Ideal ↑(TopCat.Presheaf.stalk R.obj y))
    (hI : LinearMap.ker (unitDomainStalkMap R f y) =
      (I : Submodule ↑(TopCat.Presheaf.stalk R.obj y) ↑(TopCat.Presheaf.stalk R.obj y)))
    (hs : Function.Surjective (unitDomainStalkMap R f y))
    (r : ↑(TopCat.Presheaf.stalk R.obj y)) :
    unitDomainStalkQuotientEquiv R f y I hI hs (Ideal.Quotient.mk I r) =
      unitDomainStalkMap R f y r := rfl

private def supportStalkQuotientEquiv (W : Set M) (hW : IsClosed W) (y : M) :
    (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y)
      ≃ₗ[actualComplexStructureStalk (n := n) y]
      ↑(TopCat.Presheaf.stalk (supportModule (n := n) W).val.presheaf y) :=
  unitDomainStalkQuotientEquiv (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y)
    (supportQuotientStalk_kernel_all W hW y) (supportQuotientStalk_surjective_all W hW y)

private theorem supportStalkQuotientEquiv_mk (W : Set M) (hW : IsClosed W) (y : M)
    (r : actualComplexStructureStalk (n := n) y) :
    supportStalkQuotientEquiv W hW y (Ideal.Quotient.mk _ r) =
      unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y r := rfl

private theorem prime_section_zero_irreducible {r : ℕ} (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime]
    (U : Opens (ComplexModel n)) (hpU : p ∈ U)
    (g : Fin r → actualComplexSection (n := n) U)
    (hP : P = Ideal.span (range fun i =>
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U p hpU (g i))) :
    AnalyticGermDecomposition.IsIrreducibleGerm
        {z | ∀ i, translatedSectionFamily p U g i z = 0} ∧
      (0 : ComplexModel n) ∈ {z | ∀ i, translatedSectionFamily p U g i z = 0} := by
  let A : Set (ComplexModel n) := {z | ∀ i, translatedSectionFamily p U g i z = 0}
  let f := translatedSectionFamily p U g
  have hf (i : Fin r) := translatedSectionFamily_hol p U hpU g i
  have hA : AnalyticGermDecomposition.IsAnalyticGerm A :=
    ⟨r,f,hf,Eventually.of_forall fun _ => Iff.rfl⟩
  have hprime : (AnalyticGermDecomposition.vanishingIdeal A).IsPrime := by
    rw [prime_section_zero_germ p P U hpU g hP]
    exact Ideal.map_isPrime_of_equiv (actualStalkChartEquiv (n := n) p)
  refine ⟨(AnalyticGermDecomposition.isIrreducibleGerm_iff_isPrime hA).mpr hprime,?_⟩
  intro i
  have hm : HolGerm.mk (f i) (hf i) ∈ AnalyticGermDecomposition.vanishingIdeal A :=
    AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun z hz => hz i)
  by_contra hi
  have hu : IsUnit (HolGerm.mk (f i) (hf i)) :=
    (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk] using hi)
  exact hprime.ne_top ((AnalyticGermDecomposition.vanishingIdeal A).eq_top_of_isUnit_mem hm hu)

private def sectionZeroSetOn {r : ℕ} (U D : Opens (ComplexModel n))
    (g : Fin r → actualComplexSection (n := n) U) : Set D :=
  {z | ∀ i, sectionExtension U (g i) z.val = 0}

/-- A single prime representative is chosen inside the actual prior window.
The window truncation retains the ENTIRE selected support and regular part;
it is not an arbitrary intersection of irreducible representatives. -/
private theorem exists_prime_section_representative {r : ℕ} (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime]
    (U : Opens (ComplexModel n)) (hpU : p ∈ U)
    (g : Fin r → actualComplexSection (n := n) U)
    (hP : P = Ideal.span (range fun i =>
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U p hpU (g i)))
    (N : Opens (ComplexModel n)) (hpN : p ∈ N) (hNU : N ≤ U) :
    ∃ (D : Opens (ComplexModel n)) (hpD : p ∈ D) (_hDN : D ≤ N) (d : ℕ) (c : D),
      IsComplexAnalyticSubset (n := n) (sectionZeroSetOn U D g) ∧
      (⟨p,hpD⟩ : D) ∈ sectionZeroSetOn U D g ∧
      RegularAtDim (n := n) (sectionZeroSetOn U D g) c d ∧
      sectionZeroSetOn U D g = closure (RegularLocusComponent.component (n := n) (sectionZeroSetOn U D g) c) ∧
      IsComplexAnalyticallyIrreducible (n := n) (sectionZeroSetOn U D g) := by
  classical
  let A : Set (ComplexModel n) := {z | ∀ i, translatedSectionFamily p U g i z = 0}
  obtain ⟨hA,h0A⟩ := prime_section_zero_irreducible p P U hpU g hP
  let N₀ : Set (ComplexModel n) := (fun z => z+p) ⁻¹' (N : Set (ComplexModel n))
  have hN₀ : IsOpen N₀ := N.isOpen.preimage (continuous_id.add continuous_const)
  have h0N₀ : (0 : ComplexModel n) ∈ N₀ := by
    change (0 : ComplexModel n)+p ∈ (N : Set (ComplexModel n))
    rw [zero_add]
    exact hpN
  obtain ⟨d,Δ,G₀,hΔ,h0Δ,hAN,hGA,hGc,hDense₀,_hAvoid,hReg₀⟩ :=
    IrreducibleGermConnected.exists_connected_nhds (m := 0) hA
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (hN₀.mem_nhds h0N₀)
  let D : Opens (ComplexModel n) := N ⊓
    ⟨(fun z => z-p) ⁻¹' Δ,hΔ.preimage (continuous_id.sub continuous_const)⟩
  have hDN : D ≤ N := inf_le_left
  have hDU : D ≤ U := hDN.trans hNU
  have hpD : p ∈ D := by
    refine ⟨hpN,?_⟩
    change p-p ∈ Δ
    rw [sub_self]
    exact h0Δ
  let W := sectionZeroSetOn U D g
  let B : Set (ComplexModel n) := {z | z-p ∈ A ∩ Δ}
  let G : Set (ComplexModel n) := (Homeomorph.addRight p) '' G₀
  let G' : Set D := Subtype.val ⁻¹' G
  have hGD : G ⊆ (D : Set (ComplexModel n)) := by
    rintro _ ⟨z,hz,rfl⟩
    change z+p ∈ N ∧ (z+p)-p ∈ Δ
    exact ⟨hAN (hGA hz),by simpa only [add_sub_cancel_right] using (hGA hz).2⟩
  have hRange : G ⊆ range (Subtype.val : D → ComplexModel n) :=
    fun z hz => ⟨⟨z,hGD hz⟩,rfl⟩
  have hImage : (Subtype.val : D → ComplexModel n) '' G' = G :=
    image_preimage_eq_of_subset hRange
  have hCl : closure G' = (Subtype.val : D → ComplexModel n) ⁻¹' closure G := by
    exact (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image G').trans
      (congrArg (fun S : Set (ComplexModel n) => (Subtype.val : D → ComplexModel n) ⁻¹' closure S) hImage)
  have hWB : W = (Subtype.val : D → ComplexModel n) ⁻¹' B := by
    ext z
    change (∀ i, sectionExtension U (g i) z.val = 0) ↔ z.val-p ∈ A ∩ Δ
    constructor
    · intro hz
      refine ⟨?_,z.property.2⟩
      intro i
      simpa only [translatedSectionFamily,sub_add_cancel] using hz i
    · intro hz i
      simpa only [translatedSectionFamily,sub_add_cancel] using hz.1 i
  have hW : IsComplexAnalyticSubset (n := n) W := by
    change IsComplexAnalyticSubset (n := n) {z : D | ∀ i, sectionExtension U (g i) z.val = 0}
    apply common_zero_analytic (n := n) (M := D) (fun (i : Fin r) (z : D) => sectionExtension U (g i) z.val)
    intro i z
    apply contMDiffAt_subtype_iff.mpr
    exact sectionExtension_contMDiffAt U (g i) z.val (hDU z.property)
  have hpW : (⟨p,hpD⟩ : D) ∈ W := by
    intro i
    simpa only [translatedSectionFamily,zero_add] using h0A i
  have hDense : W ⊆ closure G' := by
    rw [hCl]
    intro z hz
    have hzB : z.val-p ∈ A ∩ Δ := (show z ∈ (Subtype.val : D → ComplexModel n) ⁻¹' B from hWB ▸ hz)
    have hzC := hDense₀ hzB
    have hh : z.val ∈ (Homeomorph.addRight p) '' closure G₀ :=
      ⟨z.val-p,hzC,by change (z.val-p)+p = z.val; exact sub_add_cancel _ _⟩
    rw [(Homeomorph.addRight p).image_closure] at hh
    exact hh
  have hG'c : IsPreconnected G' :=
    IsPreconnected.preimage_of_isOpenMap
      (hGc.image (Homeomorph.addRight p) (Homeomorph.addRight p).continuous.continuousOn)
      Subtype.val_injective
      (show IsOpenMap (Subtype.val : D → ComplexModel n) from D.isOpen.isOpenMap_subtype_val) hRange
  have hReg (z : D) (hz : z ∈ G') : RegularAtDim (n := n) W z d := by
    rw [hWB]
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    change RegularAtDim (n := n) {w : ComplexModel n | w-p ∈ A ∩ Δ} z.val d
    apply (AnalyticLocalStatement.regularAtDim_translate_iff p z.val).mpr
    obtain ⟨w,hw,hwz⟩ := hz
    have he : z.val-p = w := by
      change w+p = z.val at hwz
      rw [← hwz,add_sub_cancel_right]
    rw [he]
    exact hReg₀ w hw
  obtain ⟨c,hcG⟩ := Set.Nonempty.of_closure (⟨⟨p,hpD⟩,hDense hpW⟩ : (closure G').Nonempty)
  have hc := hReg c hcG
  have hGK : G' ⊆ RegularLocusComponent.component (n := n) W c :=
    RegularLocusComponent.subset_component_of_isPreconnected hG'c
      (fun z hz => ⟨d,hReg z hz⟩) ⟨c,hcG,RegularLocusComponent.mem_component_self hc⟩
  have hWC : W = closure (RegularLocusComponent.component (n := n) W c) :=
    Subset.antisymm (fun z hz => closure_mono hGK (hDense hz))
      (closure_minimal (RegularLocusComponent.component_subset (n := n) W c) hW.isClosed)
  refine ⟨D,hpD,hDN,d,c,hW,hpW,hc,hWC,?_⟩
  change IsComplexAnalyticallyIrreducible (n := n) W
  exact Eq.mpr (congrArg (fun S : Set D => IsComplexAnalyticallyIrreducible (n := n) S) hWC)
    (RegularLocusComponent.isComplexAnalyticallyIrreducible_closure_component hW hc)

private def scalarFamily {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (a : R.obj.obj (op ⊤)) : (SheafOfModules.unit (forgetRing R)).sections :=
  PresheafOfModules.sectionsMk
    (fun V => R.obj.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op a) (by
      intro V T f
      change R.obj.map f (R.obj.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op a) =
        R.obj.map (homOfLE (show T.unop ≤ ⊤ from le_top)).op a
      rw [← Functor.map_comp_apply]
      exact congrArg (fun k => R.obj.map k a) (Subsingleton.elim _ _))

private def cyclicRelationMap {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0}) {r : ℕ}
    (a : Fin r → R.obj.obj (op ⊤)) :
    SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R) :=
  (SheafOfModules.unit (forgetRing R)).freeHomEquiv.symm (fun i => scalarFamily R (a i))

private def freeOneUnitIso {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0}) :
    SheafOfModules.free (R := forgetRing R) PUnit ≅ SheafOfModules.unit (forgetRing R) where
  hom := Sigma.desc (fun _ : PUnit => 𝟙 (SheafOfModules.unit (forgetRing R)))
  inv := SheafOfModules.ιFree PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ SheafOfModules.ιFree (R := forgetRing R) PUnit.unit)
        (Sigma.ι_desc (fun _ : PUnit => 𝟙 (SheafOfModules.unit (forgetRing R))) PUnit.unit)).trans
          ((Category.id_comp _).trans (Category.comp_id _).symm))
  inv_hom_id := Sigma.ι_desc (fun _ : PUnit => 𝟙 (SheafOfModules.unit (forgetRing R))) PUnit.unit

/-- Finite presentation comes directly from this ACTUAL finite relation
cokernel.  No kernel-closure or supplied finite-presentation packet. -/
private theorem cokernel_to_unit_finitePresentation {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R)) :
    (cokernel δ).IsFinitePresentation := by
  let e := freeOneUnitIso R
  let f := δ ≫ e.inv
  let g := e.hom ≫ cokernel.π δ
  have hfg : f ≫ g = 0 := by
    simp only [f,g,Category.assoc,Iso.inv_hom_id_assoc,cokernel.condition]
  have hc : IsColimit (CokernelCofork.ofπ g hfg) := by
    refine IsCokernel.ofIso δ (cokernelIsCokernel δ) _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
    · simp only [f,Iso.refl_hom,Category.id_comp,Iso.symm_hom]
    · simp only [g,Iso.symm_hom,CokernelCofork.π_ofπ,Iso.inv_hom_id_assoc,
        Iso.refl_hom,Category.comp_id,Cofork.π_ofπ]
  let P := SheafOfModules.presentationOfIsCokernelFree f g hfg hc
  let q := P.quasicoherentData
  have hq : q.IsFinitePresentation := by
    constructor
    intro V
    exact
      { isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit)⟩
        isFiniteType_relations := ⟨inferInstanceAs (Finite (Fin r))⟩ }
  exact ⟨q,hq⟩

private theorem epi_of_all_native_stalks {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {B C : SheafOfModules.{0} (forgetRing R)} (f : B ⟶ C)
    (hf : ∀ y : X, Function.Surjective (stalkLinearMap f.val y)) : Epi f := by
  let A := SheafOfModules.toSheaf (forgetRing R)
  have hs (y : X) : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (A.map f).hom) := hf y
  have hE : Epi (A.map f) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (A.map f)).mp
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks (A.map f).hom).mpr hs)
  exact A.epi_of_epi_map hE

/-- Applied only to already constructed WHOLE native maps below. Native
sheaf exactness detection does not invent or glue pointwise ideal data. -/
private def cofork_of_all_native_stalks {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {B C D : SheafOfModules.{0} (forgetRing R)} (f : B ⟶ C) (g : C ⟶ D) (hfg : f ≫ g = 0)
    (hex : ∀ (y : X) (b : ↑(TopCat.Presheaf.stalk C.val.presheaf y)),
      stalkLinearMap g.val y b = 0 → ∃ a, stalkLinearMap f.val y a = b)
    (hsurj : ∀ y : X, Function.Surjective (stalkLinearMap g.val y)) :
    IsColimit (CokernelCofork.ofπ g hfg) := by
  let S : ShortComplex (SheafOfModules.{0} (forgetRing R)) := ShortComplex.mk f g hfg
  let A : SheafOfModules.{0} (forgetRing R) ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
    SheafOfModules.toSheaf (forgetRing R)
  let : A.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : A.Faithful := inferInstanceAs (SheafOfModules.toSheaf (forgetRing R)).Faithful
  have hS : S.Exact := by
    apply A.reflects_exact_of_faithful
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map A)).mpr
    intro y
    apply (ShortComplex.ab_exact_iff _).mpr
    intro b hb
    exact hex y b hb
  have : Epi g := epi_of_all_native_stalks R g hsurj
  exact hS.gIsCokernel

private theorem scalarFamily_top {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (a : R.obj.obj (op ⊤)) : (scalarFamily R a).val (op ⊤) = a := by
  change R.obj.map (homOfLE (show (⊤ : Opens X) ≤ ⊤ from le_top)).op a = a
  rw [show (homOfLE (show (⊤ : Opens X) ≤ ⊤ from le_top)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _,
    ]
  exact ConcreteCategory.congr_hom (R.obj.map_id (op ⊤)) a

private theorem cyclicRelationMap_top_freeSection {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) {r : ℕ} (a : Fin r → R.obj.obj (op ⊤)) (i : Fin r) :
    (cyclicRelationMap R a).val.app (op ⊤)
      ((SheafOfModules.freeSection (R := forgetRing R) i).val (op ⊤)) = a i := by
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (M := SheafOfModules.unit (forgetRing R)) (fun j => scalarFamily R (a j)) i
  have hh := congrArg (fun s => s.val (op ⊤)) h
  exact hh.trans (scalarFamily_top R (a i))

private theorem cyclicRelationMap_stalk_basis {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) {r : ℕ} (a : Fin r → R.obj.obj (op ⊤)) (y : X) (i : Fin r) :
    stalkInclusionLinearMap R (SheafOfModules.free (R := forgetRing R) (Fin r))
      (cyclicRelationMap R a) y
        ((finiteFreeStalkLinearEquiv R (Fin r) y).symm (Pi.single i 1)) =
      R.presheaf.germ ⊤ y (by trivial) (a i) := by
  have hm := (finiteFreeStalkLinearEquiv R (Fin r) y).symm_apply_eq.mpr
    (finiteFreeStalkLinearEquiv_freeSection_germ R (Fin r) y ⊤ (by trivial) i).symm
  exact (congrArg (stalkInclusionLinearMap R
    (SheafOfModules.free (R := forgetRing R) (Fin r)) (cyclicRelationMap R a) y) hm).trans
      ((stalkInclusionLinearMap_germ R
        (SheafOfModules.free (R := forgetRing R) (Fin r)) (cyclicRelationMap R a) y ⊤
          (by trivial) ((SheafOfModules.freeSection (R := forgetRing R) i).val (op ⊤))).trans
            (congrArg (R.presheaf.germ ⊤ y (by trivial)) (cyclicRelationMap_top_freeSection R a i)))

/-- The entire image of the ACTUAL native relation map, with its original
coefficient germs. The finite-free decomposition is only at this stalk. -/
private theorem cyclicRelationMap_stalk_range {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) {r : ℕ} (a : Fin r → R.obj.obj (op ⊤)) (y : X) :
    LinearMap.range (stalkInclusionLinearMap R
      (SheafOfModules.free (R := forgetRing R) (Fin r)) (cyclicRelationMap R a) y) =
      Ideal.span (range fun i => R.presheaf.germ ⊤ y (by trivial) (a i)) := by
  classical
  let e := finiteFreeStalkLinearEquiv R (Fin r) y
  let L := stalkInclusionLinearMap R
    (SheafOfModules.free (R := forgetRing R) (Fin r)) (cyclicRelationMap R a) y
  apply le_antisymm
  · rintro z ⟨v,rfl⟩
    have hv : v = ∑ i : Fin r, (e v i) • e.symm (Pi.single i 1) := by
      apply e.injective
      simp only [map_sum,map_smul,LinearEquiv.apply_symm_apply]
      simpa only [Pi.basisFun_repr,Pi.basisFun_apply] using
        ((Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj y) (Fin r)).sum_repr (e v)).symm
    change L v ∈ _
    rw [hv,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    exact (cyclicRelationMap_stalk_basis R a y i) ▸ Ideal.subset_span (mem_range_self i)
  · apply Ideal.span_le.mpr
    rintro z ⟨i,rfl⟩
    exact ⟨e.symm (Pi.single i 1),cyclicRelationMap_stalk_basis R a y i⟩

private theorem nativeHom_ext_stalk {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {B C : SheafOfModules.{0} (forgetRing R)} (f g : B ⟶ C)
    (h : ∀ y : X, stalkLinearMap f.val y = stalkLinearMap g.val y) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf (forgetRing R)).obj C)
    V.unop _ _
  intro y hy
  have hh := DFunLike.congr_fun (h y) (TopCat.Presheaf.germ B.val.presheaf V.unop y hy m)
  erw [stalkLinearMap_germ,stalkLinearMap_germ] at hh
  exact hh

/-- The finite family below will be chosen INTERNALLY from actual Cartan
coherence. Every map here is the original native map, including off-support. -/
private def supportCokernelCofork (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → (actualComplexStructureSheaf (n := n) M).obj.obj (op ⊤))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i))) :
    Σ' hfg : cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a ≫ supportQuotient W = 0,
      IsColimit (CokernelCofork.ofπ (supportQuotient W) hfg) := by
  let R := actualComplexStructureSheaf (n := n) M
  let δ := cyclicRelationMap R a
  let κ := supportQuotient (n := n) W
  have hI (y : M) :
      LinearMap.range (stalkInclusionLinearMap R
        (SheafOfModules.free (R := forgetRing R) (Fin r)) δ y) =
        LinearMap.ker (unitDomainStalkMap R κ y) :=
    (cyclicRelationMap_stalk_range R a y).trans
      ((hspan y).symm.trans (supportQuotientStalk_kernel_all W hW y).symm)
  have hz (y : M) (v : ↑(TopCat.Presheaf.stalk
      (SheafOfModules.free (R := forgetRing R) (Fin r)).val.presheaf y)) :
      stalkLinearMap κ.val y (stalkLinearMap δ.val y v) = 0 := by
    have hm : stalkInclusionLinearMap R _ δ y v ∈ LinearMap.ker (unitDomainStalkMap R κ y) := by
      rw [← hI y]
      exact ⟨v,rfl⟩
    change stalkLinearMap κ.val y
      ((unitStalkLinearEquiv R y).symm ((unitStalkLinearEquiv R y)
        (stalkLinearMap δ.val y v))) = 0 at hm
    exact (congrArg (stalkLinearMap κ.val y)
      ((unitStalkLinearEquiv R y).symm_apply_apply _)).symm.trans hm
  have hfg : δ ≫ κ = 0 := by
    apply nativeHom_ext_stalk R
    intro y
    apply DFunLike.ext
    intro v
    exact (DFunLike.congr_fun (stalkLinearMap_comp δ.val κ.val y) v).trans
      ((hz y v).trans (DFunLike.congr_fun (stalkLinearMap_zero y) v).symm)
  refine ⟨hfg,cofork_of_all_native_stalks R δ κ hfg ?_ ?_⟩
  · intro y b hb
    have hm : (unitStalkLinearEquiv R y) b ∈ LinearMap.ker (unitDomainStalkMap R κ y) := by
      change stalkLinearMap κ.val y
        ((unitStalkLinearEquiv R y).symm ((unitStalkLinearEquiv R y) b)) = 0
      exact (congrArg (stalkLinearMap κ.val y)
        ((unitStalkLinearEquiv R y).symm_apply_apply b)).trans hb
    rw [← hI y] at hm
    obtain ⟨v,hv⟩ := hm
    exact ⟨v,(unitStalkLinearEquiv R y).injective hv⟩
  · intro y b
    obtain ⟨v,hv⟩ := supportQuotientStalk_surjective_all W hW y b
    exact ⟨(unitStalkLinearEquiv R y).symm v,hv⟩

private def supportCokernelIso (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → (actualComplexStructureSheaf (n := n) M).obj.obj (op ⊤))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i))) :
    cokernel (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a) ≅ supportModule W :=
  (cokernelIsCokernel (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a)).coconePointUniqueUpToIso
    (supportCokernelCofork W hW a hspan).2

private theorem supportCokernelIso_quotient (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → (actualComplexStructureSheaf (n := n) M).obj.obj (op ⊤))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i))) :
    cokernel.π (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a) ≫
      (supportCokernelIso W hW a hspan).hom = supportQuotient W :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a))
    (supportCokernelCofork W hW a hspan).2 WalkingParallelPair.one

private theorem supportCokernelIso_app (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → (actualComplexStructureSheaf (n := n) M).obj.obj (op ⊤))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    (V : Opens M) (s : actualComplexSection (n := n) V) :
    (supportCokernelIso W hW a hspan).hom.val.app (op V)
      ((cokernel.π (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a)).val.app (op V) s) =
        (actualSubspaceInclusion (n := n) W).toHom.c.app (op V) s :=
  congrArg (fun f => f.val.app (op V) s) (supportCokernelIso_quotient W hW a hspan)

/-- The support, finite relation target, and real domain are FIXED before
ALL native finite-type sources and whole maps. This is not nilpotent-target
continuation: the target is the actual reduced support quotient just proved. -/
private theorem cyclic_component_hom_continuation {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {r : ℕ}
    (a : Fin r → (actualComplexStructureSheaf (n := n) M).obj.obj (op ⊤))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal
      (vanishingIdeal (n := n) (closure (RegularLocusComponent.component (n := n) A c))) y =
        Ideal.span (range fun i =>
          (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    (p : M) (hpW : p ∈ closure (RegularLocusComponent.component (n := n) A c))
    {G : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) M))}
    [G.IsFiniteType]
    (f : G ⟶ cokernel (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a))
    (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  let W := closure (RegularLocusComponent.component (n := n) A c)
  let e := supportCokernelIso W isClosed_closure a hspan
  have hz : stalkLinearMap (f ≫ e.hom).val p = 0 := by
    apply DFunLike.ext
    intro b
    exact (DFunLike.congr_fun (stalkLinearMap_comp f.val e.hom.val p) b).trans
      ((congrArg (stalkLinearMap e.hom.val p) (DFunLike.congr_fun hp b)).trans (map_zero _))
  have hf := component_support_hom_continuation hA hc (f ≫ e.hom) p hpW hz
  exact (cancel_mono e.hom).mp (hf.trans (zero_comp).symm)

omit [IsComplexManifold n M] in
/-- The genuine manifold restriction comparison fixes every actual point.
Its full ambient square, rather than support faithfulness, proves this. -/
private theorem restrictLocallyRingedSpaceIso_base (U : Opens M) :
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom.base =
      𝟙 (TopCat.of U) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  have h :
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val =
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).ofRestrict U.isOpenEmbedding :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (by rfl)
  exact congrArg (fun f => f.base x) h

/-- The literal original restricted sheaf, merely retyped over its
actual underlying open to keep elaboration independent of hidden projections. -/
private def literalRingSheaf (U : Opens M) : (TopCat.of U).Sheaf CommRingCat.{0} := by
  exact ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).restrict U.isOpenEmbedding).𝒪

/-- Actual scalar identification on the SAME open site, induced solely by
the genuine native open-restriction LRS isomorphism. -/
private def actualLiteralRingIso (U : Opens M) :
    actualComplexStructureSheaf (n := n) U ≅ literalRingSheaf (n := n) U := by
  let e := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U)
  let eP := PresheafedSpace.sheafIsoOfIso e
  let eQ := eP ≪≫ TopCat.Presheaf.pushforwardEq (restrictLocallyRingedSpaceIso_base (n := n) U) _ ≪≫
    TopCat.Presheaf.Pushforward.id _
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).preimageIso eQ

/-- Only the existing native change-of-ringed-site equivalence is used.
The site is identical and the ring isomorphism is genuine. -/
private abbrev scalarIsoEquivalence {C : Type} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{0}} (e : R ≅ S) :
    SheafOfModules.{0} R ≌ SheafOfModules.{0} S := by
  let d : C ≌ C := CategoryTheory.Equivalence.refl
  letI : Functor.IsContinuous d.functor J J := by
    change Functor.IsContinuous (𝟭 C) J J
    infer_instance
  letI : Functor.IsContinuous d.inverse J J := by
    change Functor.IsContinuous (𝟭 C) J J
    infer_instance
  let φ : S ⟶ (d.functor.sheafPushforwardContinuous RingCat J J).obj R := e.inv
  let ψ : R ⟶ (d.inverse.sheafPushforwardContinuous RingCat J J).obj S := e.hom
  have H₁ : Functor.whiskerRight (NatTrans.op d.counit) R.obj =
      ψ.hom ≫ d.inverse.op.whiskerLeft φ.hom := by
    ext V x
    change R.obj.map (𝟙 V) x = e.inv.hom.app V (e.hom.hom.app V x)
    exact (ConcreteCategory.congr_hom (R.obj.map_id V) x).trans
      (ConcreteCategory.congr_hom
        (NatTrans.congr_app (congrArg (fun f => f.hom) e.hom_inv_id) V) x).symm
  have H₂ : φ.hom ≫ d.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op d.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change S.obj.map (𝟙 V) (e.hom.hom.app V (e.inv.hom.app V x)) = x
    exact (ConcreteCategory.congr_hom (S.obj.map_id V)
      (e.hom.hom.app V (e.inv.hom.app V x))).trans
        (ConcreteCategory.congr_hom
          (NatTrans.congr_app (congrArg (fun f => f.hom) e.inv_hom_id) V) x)
  exact SheafOfModules.pushforwardPushforwardEquivalence d φ ψ H₁ H₂

private def scalarIsoUnitIso {C : Type} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{0}} (e : R ≅ S) :
    SheafOfModules.unit S ≅ (scalarIsoEquivalence e).functor.obj (SheafOfModules.unit R) := by
  let u := SheafOfModules.unitToPushforwardObjUnit (F := 𝟭 C) e.inv
  have h (V : Cᵒᵖ) : IsIso (u.val.app V) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (e.inv.hom.app V)
  exact (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ (u.val.app V) (h V))
      (by intro X Y f; exact u.val.naturality f))

/-- Transport the SAME local finite native generating data along the
actual scalar isomorphism. There is no extension beyond this open. -/
private theorem scalarIso_isFiniteType {X : TopCat.{0}}
    {R S : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{0}} (e : R ≅ S) (B : SheafOfModules.{0} R) [B.IsFiniteType] :
    ((scalarIsoEquivalence e).functor.obj B).IsFiniteType := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData B
  let eU (V : Opens X) := ((Opens.grothendieckTopology X).overPullback RingCat V).mapIso e
  let gs (i : q.I) : (((scalarIsoEquivalence e).functor.obj B).over (q.X i)).GeneratingSections := by
    exact (q.generators i).map (scalarIsoEquivalence (eU (q.X i))).functor
      (scalarIsoUnitIso (eU (q.X i)))
  have hgs (i : q.I) : (gs i).IsFiniteType := by
    exact ⟨(hq.isFiniteType i).finite⟩
  let q' : ((scalarIsoEquivalence e).functor.obj B).LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := gs }
  exact ⟨q',⟨hgs⟩⟩

private theorem scalarIso_map_app {C : Type} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{0}} (e : R ≅ S) {B D : SheafOfModules.{0} R}
    (f : B ⟶ D) (V : Cᵒᵖ) (b : B.val.obj V) :
    ((scalarIsoEquivalence e).functor.map f).val.app V b = f.val.app V b := rfl

private theorem scalarIso_map_stalk {X : TopCat.{0}}
    {R S : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{0}} (e : R ≅ S) {B D : SheafOfModules.{0} R}
    (f : B ⟶ D) (y : X) (b : ↑(TopCat.Presheaf.stalk B.val.presheaf y)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((PresheafOfModules.toPresheaf S.obj).map
        ((scalarIsoEquivalence e).functor.map f).val)) b =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        ((PresheafOfModules.toPresheaf R.obj).map f.val)) b := rfl

/-- Only a local zero extension is used; holomorphicity is asserted at the
included point. The genuine open pullback is the identity in these charts. -/
private theorem chartTranslatedGerm_extendOpens (U : Opens M) (y : U) (f : U → ℂ)
    (hf : HolomorphicAt n f y) :
    chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y) f hf =
      chartTranslatedGerm y.val y.val (mem_chart_source (ComplexModel n) y.val)
        (extendOpens U f) ((holomorphicAt_iff_extendOpens U).mp hf) := by
  have h := HironakaActualWholeStalkHolomorphicPullback.actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : U → M)) contMDiff_subtype_val y (extendOpens U f)
      ((holomorphicAt_iff_extendOpens U).mp hf)
  rw [HironakaActualOpenIntrinsicHS.actualHolomorphicGermPullback_val] at h
  have he : extendOpens U f ∘ (Subtype.val : U → M) = f :=
    funext fun z => extendOpens_val U f z
  simpa only [AlgHom.id_apply,he] using h.symm

/-- A private all-representative bridge, valid for any subset and only at
the actual translated point. It does not assume global analytic extension. -/
private theorem wholeChart_vanishing_eq_translated_germ (W : Set (ComplexModel n))
    (p : ComplexModel n) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) W) p p (mem_chart_source (ComplexModel n) p) =
      AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p ∈ W} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hfW,rfl⟩
    change HolGerm.mk (fun z => f (z+p))
      (translated_holomorphic p (hf.mono fun _ h => h.differentiableAt)) ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have ht : Tendsto (fun z : ComplexModel n => z+p) (𝓝 0) (𝓝 p) := by
      simpa only [zero_add] using (show Continuous (fun z : ComplexModel n => z+p) from
        continuous_id.add continuous_const).tendsto (0 : ComplexModel n)
    exact ht.eventually hfW.2
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    have hv := AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg
    let F : ComplexModel n → ℂ := fun w => f (w-p)
    have hT : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun w : ComplexModel n => w-p) := contMDiff_id.sub contMDiff_const
    have hf' : HolomorphicAt n f ((fun w : ComplexModel n => w-p) p) := by
      simpa only [sub_self] using
        (show HolomorphicAt n f (0 : ComplexModel n) from hf.mono fun _ h => h.mdifferentiableAt)
    have hF : HolomorphicAt n F p :=
      HolomorphicAt.comp_contMDiff (m := n) (n := n) (b := f)
        (f := (fun w : ComplexModel n => w-p)) (y := p) hf'
          (Eventually.of_forall fun w => hT w)
    have hFW : (vanishingIdeal (n := n) W).mem p F := by
      refine ⟨hF,?_⟩
      have ht : Tendsto (fun w : ComplexModel n => w-p) (𝓝 p) (𝓝 0) := by
        simpa only [sub_self] using (show Continuous (fun w : ComplexModel n => w-p) from
          continuous_id.sub continuous_const).tendsto p
      filter_upwards [ht.eventually hv] with w hw hwW
      exact hw (by simpa only [sub_add_cancel] using hwW)
    have he : chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) F hF =
        HolGerm.mk f hf := by
      simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by
        change f ((z+p)-p) = f z
        rw [add_sub_cancel_right]
    exact Ideal.subset_span ⟨F,hF,hFW,he.symm⟩

private def topScalarSection (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f) :
    actualComplexSection (n := n) (⊤ : Opens M) :=
  ⟨fun z => f z.val,hf.comp contMDiff_subtype_val⟩

private theorem topScalarSection_chart (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f)
    (y : M) (hy : HolomorphicAt n f y) :
    actualStalkChartEquiv (n := n) y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial)
        (topScalarSection f hf)) =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y) f hy := by
  have hs : sectionExtension ⊤ (topScalarSection f hf) =ᶠ[𝓝 y] f :=
    Eventually.of_forall fun z => sectionExtension_apply ⊤ (topScalarSection f hf) z (by trivial)
  exact (congrArg (actualStalkChartEquiv (n := n) y)
    (actualOriginalFunctionGerm_eq_section ⊤ y (by trivial) (topScalarSection f hf) f hy hs)).symm.trans
      (actualOriginalFunctionGerm_chart y f hy)

private theorem chartTranslatedGerm_comp_val (U : Opens M) (y : U)
    (f : M → ℂ) (hf : HolomorphicAt n f y.val) :
    chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
      (f ∘ (Subtype.val : U → M)) ((holomorphicAt_comp_val_iff U).mpr hf) =
      chartTranslatedGerm y.val y.val (mem_chart_source (ComplexModel n) y.val) f hf := by
  have h := HironakaActualWholeStalkHolomorphicPullback.actualHolomorphicGermPullback_original_function
    (f := (Subtype.val : U → M)) contMDiff_subtype_val y f hf
  rw [HironakaActualOpenIntrinsicHS.actualHolomorphicGermPullback_val] at h
  simpa only [AlgHom.id_apply] using h.symm

/-- Ordinary P only: actual Cartan generators of the WHOLE vanishing ideal
are restricted onto ONE internally constructed cofinal prime representative.
All scalar functions live on their genuine real domains. -/
private theorem exists_prime_native_whole_family (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    ∃ (D : Opens (ComplexModel n)) (hpD : p ∈ D) (k : ℕ)
      (a : Fin k → actualComplexSection (n := n) (⊤ : Opens D))
      (W : Set D) (d : ℕ) (c : D),
      IsComplexAnalyticSubset (n := n) W ∧ (⟨p,hpD⟩ : D) ∈ W ∧
      RegularAtDim (n := n) W c d ∧ W = closure (RegularLocusComponent.component (n := n) W c) ∧
      IsComplexAnalyticallyIrreducible (n := n) W ∧
      (∀ y : D, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
        Ideal.span (range fun i =>
          (actualComplexStructureSheaf (n := n) D).presheaf.germ ⊤ y (by trivial) (a i))) ∧
      Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom P =
        wholeChartStalkIdeal (vanishingIdeal (n := n) W) (⟨p,hpD⟩ : D) ⟨p,hpD⟩
          (mem_chart_source (ComplexModel n) (⟨p,hpD⟩ : D)) := by
  classical
  obtain ⟨U,hpU,r,g,hP⟩ := exists_native_ideal_generators p P
  let Z : Set (ComplexModel n) := {z | ∀ i, sectionExtension U (g i) z = 0}
  let WU : Set U := (Subtype.val : U → ComplexModel n) ⁻¹' Z
  have hWU : IsComplexAnalyticSubset (n := n) WU := by
    change IsComplexAnalyticSubset (n := n) {z : U | ∀ i, sectionExtension U (g i) z.val = 0}
    apply common_zero_analytic (n := n) (M := U) (fun (i : Fin r) (z : U) => sectionExtension U (g i) z.val)
    intro i z
    apply contMDiffAt_subtype_iff.mpr
    exact sectionExtension_contMDiffAt U (g i) z.val z.property
  let A := vanishingIdeal (n := n) WU
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence (n := n) (X := U) WU hWU
  obtain ⟨V,hpV,k,s,_hEpi,hspan⟩ :=
    HironakaLegacyCoherentIdealFiniteType.exists_local_finite_generators A hA (⟨p,hpU⟩ : U)
  let t (i : Fin k) : actualComplexSection (n := n) V :=
    (HironakaLegacyCoherentIdealSheaf.actualIdealModuleInclusion A).val.app (op V) (s i)
  let N : Opens (ComplexModel n) :=
    ⟨(Subtype.val : U → ComplexModel n) '' (V : Set U),
      U.isOpen.isOpenMap_subtype_val (V : Set U) V.isOpen⟩
  have hpN : p ∈ N := by
    change p ∈ (Subtype.val : U → ComplexModel n) '' (V : Set U)
    exact ⟨⟨p,hpU⟩,hpV,rfl⟩
  have hNU : N ≤ U := by
    change (Subtype.val : U → ComplexModel n) '' (V : Set U) ⊆ (U : Set (ComplexModel n))
    rintro z ⟨u,_,rfl⟩
    exact u.property
  obtain ⟨D,hpD,hDN,d,c,hW,hpW,hc,hWC,hIrr⟩ :=
    exists_prime_section_representative p P U hpU g hP N hpN hNU
  let W := sectionZeroSetOn U D g
  have hDU : D ≤ U := hDN.trans hNU
  let liftD (y : D) : U := ⟨y.val,hDU y.property⟩
  have hyV (y : D) : liftD y ∈ V := by
    have hyN : y.val ∈ N := hDN y.property
    change y.val ∈ (Subtype.val : U → ComplexModel n) '' (V : Set U) at hyN
    obtain ⟨u,hu,he⟩ := hyN
    have hu' : u = liftD y := Subtype.ext he
    exact hu' ▸ hu
  let F (i : Fin k) : ComplexModel n → ℂ := extendOpens U (sectionExtension V (t i))
  have hF (i : Fin k) (y : D) : HolomorphicAt n (F i) y.val :=
    (holomorphicAt_iff_extendOpens U).mp (sectionExtension_holomorphicAt V (t i) (liftD y) (hyV y))
  let FD (i : Fin k) : D → ℂ := F i ∘ (Subtype.val : D → ComplexModel n)
  have hFD (i : Fin k) : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (FD i) := by
    intro y
    change ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun z : D => F i z.val) y
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_eventually_mdifferentiableAt (hF i y)
  have hFDhol (i : Fin k) (y : D) : HolomorphicAt n (FD i) y :=
    (holomorphicAt_comp_val_iff D).mpr (hF i y)
  let a (i : Fin k) : actualComplexSection (n := n) (⊤ : Opens D) := topScalarSection (FD i) (hFD i)
  have hSourceCoeff (i : Fin k) (y : D) :
      actualStalkChartEquiv (n := n) (liftD y)
        ((actualComplexStructureSheaf (n := n) U).presheaf.germ V (liftD y) (hyV y) (t i)) =
      chartTranslatedGerm y.val y.val (mem_chart_source (ComplexModel n) y.val) (F i) (hF i y) := by
    rw [actualStalkChartEquiv_germ]
    change chartTranslatedGerm (liftD y) (liftD y) (mem_chart_source (ComplexModel n) (liftD y))
      (sectionExtension V (t i)) (sectionExtension_holomorphicAt V (t i) (liftD y) (hyV y)) = _
    exact chartTranslatedGerm_extendOpens U (liftD y) (sectionExtension V (t i))
      (sectionExtension_holomorphicAt V (t i) (liftD y) (hyV y))
  have hDestCoeff (i : Fin k) (y : D) :
      actualStalkChartEquiv (n := n) y
        ((actualComplexStructureSheaf (n := n) D).presheaf.germ ⊤ y (by trivial) (a i)) =
      chartTranslatedGerm y.val y.val (mem_chart_source (ComplexModel n) y.val) (F i) (hF i y) :=
    (topScalarSection_chart (FD i) (hFD i) y (hFDhol i y)).trans
      (chartTranslatedGerm_comp_val D y (F i) (hF i y))
  have hChartWhole (y : D) :
      wholeChartStalkIdeal A (liftD y) (liftD y) (mem_chart_source (ComplexModel n) (liftD y)) =
      Ideal.span (range fun i =>
        chartTranslatedGerm y.val y.val (mem_chart_source (ComplexModel n) y.val) (F i) (hF i y)) := by
    have hS := (HironakaLegacyCoherentIdealSheaf.actualIdealModule_stalkRange A hA (liftD y)).symm.trans
      (hspan (liftD y) (hyV y))
    have hm := congrArg (Ideal.map (actualStalkChartEquiv (n := n) (liftD y)).toRingHom) hS
    rw [map_actualWholeSheafStalkIdeal,Ideal.map_span,← Set.range_comp] at hm
    exact hm.trans (congrArg Ideal.span (congrArg range (funext fun i => hSourceCoeff i y)))
  have hWhole (y : D) : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) D).presheaf.germ ⊤ y (by trivial) (a i)) := by
    have hSame : wholeChartStalkIdeal (vanishingIdeal (n := n) W) y y
        (mem_chart_source (ComplexModel n) y) =
        wholeChartStalkIdeal A (liftD y) (liftD y) (mem_chart_source (ComplexModel n) (liftD y)) :=
      (HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open D Z y).trans
        (HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open U Z (liftD y)).symm
    rw [actualWholeSheafStalkIdeal_eq_map_chart,hSame,hChartWhole,Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg range
    funext i
    exact (actualStalkChartEquiv (n := n) y).symm_apply_eq.mpr (hDestCoeff i y).symm
  have hPZero : Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom P =
      AnalyticGermDecomposition.vanishingIdeal {z : ComplexModel n | z+p ∈ Z} := by
    simpa only [Z,translatedSectionFamily,mem_ofPred_eq] using (prime_section_zero_germ p P U hpU g hP).symm
  have hPChart := hPZero.trans (wholeChart_vanishing_eq_translated_germ Z p).symm
  refine ⟨D,hpD,k,a,W,d,c,hW,hpW,hc,hWC,hIrr,hWhole,?_⟩
  exact hPChart.trans
    (HironakaActualVanishingIntrinsicHSTransport.wholeChartStalkIdeal_vanishing_actual_open D Z (⟨p,hpD⟩ : D)).symm

private abbrev nativeForgetRingIso {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) : forgetRing R ≅ forgetRing S :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).mapIso e

/-- The SAME finite relation map is transported through native free and
unit comparisons. No presentation or kernel packet is an input. -/
private def scalarRelationMap {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R)) :
    SheafOfModules.free (R := forgetRing S) (Fin r) ⟶ SheafOfModules.unit (forgetRing S) :=
  let E := scalarIsoEquivalence (nativeForgetRingIso e)
  let η := scalarIsoUnitIso (nativeForgetRingIso e)
  (SheafOfModules.mapFreeIso E.functor (Fin r) η).hom ≫ E.functor.map δ ≫ η.inv

private def scalarCokernelIso {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R)) :
    cokernel (scalarRelationMap e δ) ≅
      (scalarIsoEquivalence (nativeForgetRingIso e)).functor.obj (cokernel δ) := by
  let E := scalarIsoEquivalence (nativeForgetRingIso e)
  let η := scalarIsoUnitIso (nativeForgetRingIso e)
  let ε := SheafOfModules.mapFreeIso E.functor (Fin r) η
  letI : E.functor.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have w : scalarRelationMap e δ ≫ η.hom = ε.hom ≫ E.functor.map δ := by
    change (ε.hom ≫ E.functor.map δ ≫ η.inv) ≫ η.hom = ε.hom ≫ E.functor.map δ
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact cokernel.mapIso (scalarRelationMap e δ) (E.functor.map δ) ε η w ≪≫
    asIso (cokernelComparison δ E.functor)

private theorem scalarCokernelIso_quotient {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R)) :
    cokernel.π (scalarRelationMap e δ) ≫ (scalarCokernelIso e δ).hom =
      (scalarIsoUnitIso (nativeForgetRingIso e)).hom ≫
        (scalarIsoEquivalence (nativeForgetRingIso e)).functor.map (cokernel.π δ) := by
  simp only [scalarCokernelIso,Iso.trans_hom,asIso_hom,cokernel.mapIso_hom,cokernel.map,
    Category.assoc,cokernel.π_desc_assoc,π_comp_cokernelComparison]

/-- This is the EXISTING native stalk functor applied to the ACTUAL scalar
isomorphism. Its action on EVERY numerator is the original section map. -/
private def scalarStalkEquiv {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) (y : X) :
    ↑(TopCat.Presheaf.stalk R.presheaf y) ≃+* ↑(TopCat.Presheaf.stalk S.presheaf y) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat y).mapIso
    ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).mapIso e)).commRingCatIsoToRingEquiv

private theorem scalarStalkEquiv_germ {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) (y : X) (V : Opens X) (hy : y ∈ V) (s : R.obj.obj (op V)) :
    scalarStalkEquiv e y (R.presheaf.germ V y hy s) =
      S.presheaf.germ V y hy (e.hom.hom.app (op V) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy e.hom.hom s

private def fixedBasePresheafMap {T : TopCat.{0}}
    {F G : T.Presheaf CommRingCat.{0}}
    (f : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G) (hf : f.base = 𝟙 T) : G ⟶ F :=
  f.c ≫ (TopCat.Presheaf.pushforwardEq hf F).hom ≫ (TopCat.Presheaf.Pushforward.id F).hom

private def idBasePresheafHom {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    (c : G ⟶ F) : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G := ⟨𝟙 T,c⟩

private theorem normalize_base_presheaf_hom {T : TopCat.{0}}
    {F G : T.Presheaf CommRingCat.{0}}
    (f : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G) (hf : f.base = 𝟙 T) :
    idBasePresheafHom (fixedBasePresheafMap f hf) = f := by
  rcases f with ⟨b,c⟩
  change b = 𝟙 T at hf
  subst b
  change (⟨𝟙 T,c ≫ (TopCat.Presheaf.pushforwardEq (rfl : (𝟙 T) = 𝟙 T) F).hom ≫
    (TopCat.Presheaf.Pushforward.id F).hom⟩ : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G) = ⟨𝟙 T,c⟩
  apply congrArg (fun k : G ⟶ F => (⟨𝟙 T,k⟩ : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G))
  apply NatTrans.ext
  funext V
  change c.app V ≫ F.map (𝟙 V) ≫ 𝟙 (F.obj V) = c.app V
  exact (Category.assoc _ _ _).symm.trans
    ((Category.comp_id _).trans
      ((congrArg (fun k => c.app V ≫ k) (F.map_id V)).trans (Category.comp_id _)))

private theorem idBasePresheafHom_stalkMap {T : TopCat.{0}}
    {F G : T.Presheaf CommRingCat.{0}} (c : G ⟶ F) (y : T)
    (r : ↑(TopCat.Presheaf.stalk G y)) :
    (idBasePresheafHom c).stalkMap y r =
      ((TopCat.Presheaf.stalkFunctor CommRingCat y).map c) r := by
  obtain ⟨V,hy,s,rfl⟩ := G.exists_germ_eq r
  exact (PresheafedSpace.stalkMap_germ_apply (idBasePresheafHom c) V y hy s).trans
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy c s).symm

private theorem scalarIsoUnitIso_app {X : TopCat.{0}} {R S : X.Sheaf CommRingCat.{0}}
    (e : R ≅ S) (V : Opens X) (s : S.obj.obj (op V)) :
    (scalarIsoUnitIso (nativeForgetRingIso e)).hom.val.app (op V) s =
      e.inv.hom.app (op V) s := rfl

private theorem scalarIsoUnitIso_stalk_numerator {X : TopCat.{0}}
    {R S : X.Sheaf CommRingCat.{0}} (e : R ≅ S) (y : X)
    (r : ↑(TopCat.Presheaf.stalk R.presheaf y)) :
    stalkLinearMap (scalarIsoUnitIso (nativeForgetRingIso e)).hom.val y
      ((unitStalkLinearEquiv S y).symm (scalarStalkEquiv e y r)) =
      (unitStalkLinearEquiv R y).symm r := by
  obtain ⟨V,hy,s,rfl⟩ := R.presheaf.exists_germ_eq r
  rw [scalarStalkEquiv_germ]
  have hS : (unitStalkLinearEquiv S y).symm
      (S.presheaf.germ V y hy (e.hom.hom.app (op V) s)) =
      TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing S)).val.presheaf V y hy
        (e.hom.hom.app (op V) s) :=
    (unitStalkLinearEquiv S y).symm_apply_eq.mpr
      (unitStalkLinearEquiv_germ S y V hy (e.hom.hom.app (op V) s)).symm
  have hR : (unitStalkLinearEquiv R y).symm (R.presheaf.germ V y hy s) =
      TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf V y hy s :=
    (unitStalkLinearEquiv R y).symm_apply_eq.mpr (unitStalkLinearEquiv_germ R y V hy s).symm
  rw [hS,hR]
  erw [stalkLinearMap_germ,scalarIsoUnitIso_app]
  change TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf V y hy
    (e.inv.hom.app (op V) (e.hom.hom.app (op V) s)) =
      TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf V y hy s
  exact congrArg (TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf V y hy)
    (ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f => f.hom) e.hom_inv_id) (op V)) s)

/-- Genuine literal-open continuation is derived from the actual analytic
component, not supplied as an incoming continuation or module-model packet. -/
private theorem literal_component_hom_continuation (U : Opens M) {A : Set U}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : U} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens U))
    (hspan : ∀ y : U, actualWholeSheafStalkIdeal
      (vanishingIdeal (n := n) (closure (RegularLocusComponent.component (n := n) A c))) y =
        Ideal.span (range fun i =>
          (actualComplexStructureSheaf (n := n) U).presheaf.germ ⊤ y (by trivial) (a i)))
    (p : U) (hpW : p ∈ closure (RegularLocusComponent.component (n := n) A c))
    {G : SheafOfModules.{0} (forgetRing (literalRingSheaf (n := n) U))} [G.IsFiniteType]
    (f : G ⟶ cokernel (scalarRelationMap (actualLiteralRingIso (n := n) U)
      (cyclicRelationMap (actualComplexStructureSheaf (n := n) U) a)))
    (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  let R := actualComplexStructureSheaf (n := n) U
  let e := actualLiteralRingIso (n := n) U
  let E := scalarIsoEquivalence (nativeForgetRingIso e)
  let δ := cyclicRelationMap R a
  let t := scalarCokernelIso e δ
  let f' := f ≫ t.hom
  let G' : SheafOfModules.{0} (forgetRing R) := E.inverse.obj G
  let : G'.IsFiniteType := scalarIso_isFiniteType (nativeForgetRingIso e).symm G
  let : E.inverse.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let fA : G' ⟶ cokernel δ := E.inverse.map f' ≫ E.unitIso.inv.app (cokernel δ)
  have hf' : stalkLinearMap f'.val p = 0 := by
    apply DFunLike.ext
    intro b
    exact (DFunLike.congr_fun (stalkLinearMap_comp f.val t.hom.val p) b).trans
      ((congrArg (stalkLinearMap t.hom.val p) (DFunLike.congr_fun hp b)).trans (map_zero _))
  have hE : stalkLinearMap (E.inverse.map f').val p = 0 := by
    apply DFunLike.ext
    intro b
    exact (scalarIso_map_stalk (nativeForgetRingIso e).symm f' p b).trans
      (DFunLike.congr_fun hf' b)
  have hAp : stalkLinearMap fA.val p = 0 := by
    apply DFunLike.ext
    intro b
    exact (DFunLike.congr_fun
      (stalkLinearMap_comp (E.inverse.map f').val (E.unitIso.inv.app (cokernel δ)).val p) b).trans
        ((congrArg (stalkLinearMap (E.unitIso.inv.app (cokernel δ)).val p)
          (DFunLike.congr_fun hE b)).trans (map_zero _))
  have hAf : fA = 0 := cyclic_component_hom_continuation hA hc a hspan p hpW fA hAp
  have hmap : E.inverse.map f' = 0 :=
    (cancel_mono (E.unitIso.inv.app (cokernel δ))).mp (hAf.trans (zero_comp).symm)
  have hz : f' = 0 := E.inverse.map_injective (hmap.trans (E.inverse.map_zero _ _).symm)
  exact (cancel_mono t.hom).mp (hz.trans (zero_comp).symm)

private def supportScalarCokernelIso (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens M))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    {S : (TopCat.of M).Sheaf CommRingCat.{0}}
    (e : actualComplexStructureSheaf (n := n) M ≅ S) :
    cokernel (scalarRelationMap e (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a)) ≅
      (scalarIsoEquivalence (nativeForgetRingIso e)).functor.obj (supportModule W) :=
  scalarCokernelIso e (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a) ≪≫
    (scalarIsoEquivalence (nativeForgetRingIso e)).functor.mapIso (supportCokernelIso W hW a hspan)

private theorem supportScalarCokernelIso_quotient (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens M))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    {S : (TopCat.of M).Sheaf CommRingCat.{0}}
    (e : actualComplexStructureSheaf (n := n) M ≅ S) :
    cokernel.π (scalarRelationMap e (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a)) ≫
      (supportScalarCokernelIso W hW a hspan e).hom =
        (scalarIsoUnitIso (nativeForgetRingIso e)).hom ≫
          (scalarIsoEquivalence (nativeForgetRingIso e)).functor.map (supportQuotient W) := by
  let E := scalarIsoEquivalence (nativeForgetRingIso e)
  change cokernel.π _ ≫ ((scalarCokernelIso e _).hom ≫ E.functor.map (supportCokernelIso W hW a hspan).hom) = _
  rw [← Category.assoc,scalarCokernelIso_quotient,Category.assoc,← E.functor.map_comp,
    supportCokernelIso_quotient]

private theorem supportScalarCokernelIso_stalk_numerator (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens M))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    {S : (TopCat.of M).Sheaf CommRingCat.{0}}
    (e : actualComplexStructureSheaf (n := n) M ≅ S) (y : M)
    (s : actualComplexStructureStalk (n := n) y) :
    stalkLinearMap (supportScalarCokernelIso W hW a hspan e).hom.val y
      (unitDomainStalkMap S
        (cokernel.π (scalarRelationMap e (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a))) y
          (scalarStalkEquiv e y s)) =
      unitDomainStalkMap (actualComplexStructureSheaf (n := n) M) (supportQuotient W) y s := by
  let R := actualComplexStructureSheaf (n := n) M
  let E := scalarIsoEquivalence (nativeForgetRingIso e)
  let η := scalarIsoUnitIso (nativeForgetRingIso e)
  let κ := cokernel.π (scalarRelationMap e (cyclicRelationMap R a))
  let ν := supportScalarCokernelIso W hW a hspan e
  have h₀ := congrArg (fun f => stalkLinearMap f.val y) (supportScalarCokernelIso_quotient W hW a hspan e)
  have hL : stalkLinearMap (κ ≫ ν.hom).val y =
      (stalkLinearMap ν.hom.val y).comp (stalkLinearMap κ.val y) :=
    stalkLinearMap_comp κ.val ν.hom.val y
  have hR : stalkLinearMap (η.hom ≫ E.functor.map (supportQuotient W)).val y =
      (stalkLinearMap (E.functor.map (supportQuotient W)).val y).comp (stalkLinearMap η.hom.val y) :=
    stalkLinearMap_comp η.hom.val (E.functor.map (supportQuotient W)).val y
  have h := hL.symm.trans (h₀.trans hR)
  have hh := DFunLike.congr_fun h ((unitStalkLinearEquiv S y).symm (scalarStalkEquiv e y s))
  change stalkLinearMap ν.hom.val y (unitDomainStalkMap S κ y (scalarStalkEquiv e y s)) =
    stalkLinearMap (E.functor.map (supportQuotient W)).val y
      (stalkLinearMap η.hom.val y ((unitStalkLinearEquiv S y).symm (scalarStalkEquiv e y s))) at hh
  rw [scalarIsoUnitIso_stalk_numerator] at hh
  exact hh.trans (scalarIso_map_stalk (nativeForgetRingIso e) (supportQuotient W) y
    ((unitStalkLinearEquiv R y).symm s))

private theorem supportScalarCokernel_stalk_zero_iff (W : Set M) (hW : IsClosed W) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens M))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    {S : (TopCat.of M).Sheaf CommRingCat.{0}}
    (e : actualComplexStructureSheaf (n := n) M ≅ S) (y : M)
    (z : ↑(TopCat.Presheaf.stalk S.presheaf y)) :
    unitDomainStalkMap S
      (cokernel.π (scalarRelationMap e (cyclicRelationMap (actualComplexStructureSheaf (n := n) M) a))) y z = 0 ↔
      z ∈ Ideal.map (scalarStalkEquiv e y).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) := by
  let R := actualComplexStructureSheaf (n := n) M
  let κ := cokernel.π (scalarRelationMap e (cyclicRelationMap R a))
  let ν := supportScalarCokernelIso W hW a hspan e
  let L := scalarStalkEquiv e y
  have hinj : Function.Injective (stalkLinearMap ν.hom.val y) :=
    (ConcreteCategory.bijective_of_isIso ((nativeStalkFunctor S y).map ν.hom)).1
  constructor
  · intro hz
    let x := L.symm z
    have hz' : unitDomainStalkMap S κ y (L x) = 0 := by
      simpa only [x,RingEquiv.apply_symm_apply] using hz
    have h0 : unitDomainStalkMap R (supportQuotient W) y x = 0 :=
      (supportScalarCokernelIso_stalk_numerator W hW a hspan e y x).symm.trans
        ((congrArg (stalkLinearMap ν.hom.val y) hz').trans (map_zero _))
    have hx : x ∈ LinearMap.ker (unitDomainStalkMap R (supportQuotient W) y) := h0
    rw [supportQuotientStalk_kernel_all W hW y] at hx
    have hm := Ideal.mem_map_of_mem L.toRingHom hx
    change L (L.symm z) ∈ Ideal.map L.toRingHom (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) at hm
    exact (L.apply_symm_apply z) ▸ hm
  · intro hz
    obtain ⟨x,hx,rfl⟩ := (Ideal.mem_map_iff_of_surjective L.toRingHom L.surjective).mp hz
    change unitDomainStalkMap S κ y (L x) = 0
    apply hinj
    have hx' : x ∈ LinearMap.ker (unitDomainStalkMap R (supportQuotient W) y) := by
      rw [supportQuotientStalk_kernel_all W hW y]
      exact hx
    have hx0 : unitDomainStalkMap R (supportQuotient W) y x = 0 := hx'
    exact (supportScalarCokernelIso_stalk_numerator W hW a hspan e y x).trans
      (hx0.trans (map_zero (stalkLinearMap ν.hom.val y)).symm)

private theorem map_whole_family_eq_scalar_span (W : Set M) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens M))
    (hspan : ∀ y : M, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial) (a i)))
    {S : (TopCat.of M).Sheaf CommRingCat.{0}}
    (e : actualComplexStructureSheaf (n := n) M ≅ S) (y : M) :
    Ideal.map (scalarStalkEquiv e y).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) =
      Ideal.span (range fun i => S.presheaf.germ ⊤ y (by trivial) (e.hom.hom.app (op ⊤) (a i))) := by
  rw [hspan y,Ideal.map_span,← Set.range_comp]
  exact congrArg Ideal.span (congrArg range
    (funext fun i => scalarStalkEquiv_germ e y ⊤ (by trivial) (a i)))

/-- A typed use of the existing native module quotient factory. The
public producer derives EVERY zero iff internally, before this is used. -/
private def unitDomainStalkQuotientOfZeroIff {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X)
    (I : Ideal ↑(TopCat.Presheaf.stalk R.obj y))
    (hI : ∀ s, unitDomainStalkMap R f y s = 0 ↔ s ∈ I)
    (hs : Function.Surjective (unitDomainStalkMap R f y)) :
    (↑(TopCat.Presheaf.stalk R.obj y) ⧸ (I : Submodule _ _)) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk T.val.presheaf y) :=
  unitDomainStalkQuotientEquiv R f y I (by ext s; exact hI s) hs

private theorem unitDomainStalkQuotientOfZeroIff_mk {X : TopCat.{0}}
    (R : X.Sheaf CommRingCat.{0}) {T : SheafOfModules.{0} (forgetRing R)}
    (f : SheafOfModules.unit (forgetRing R) ⟶ T) (y : X)
    (I : Ideal ↑(TopCat.Presheaf.stalk R.obj y))
    (hI : ∀ s, unitDomainStalkMap R f y s = 0 ↔ s ∈ I)
    (hs : Function.Surjective (unitDomainStalkMap R f y))
    (s : ↑(TopCat.Presheaf.stalk R.obj y)) :
    unitDomainStalkQuotientOfZeroIff R f y I hI hs (Submodule.Quotient.mk s) =
      unitDomainStalkMap R f y s := rfl

private def actualOpenComparisonPresheafHom (U : Opens M) :
    PresheafedSpace.mk (TopCat.of U) (literalRingSheaf (n := n) U).presheaf ⟶
      PresheafedSpace.mk (TopCat.of U) (actualComplexStructureSheaf (n := n) U).presheaf := by
  exact (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom

private def actualOpenValPresheafHom (U : Opens M) :
    PresheafedSpace.mk (TopCat.of U) (actualComplexStructureSheaf (n := n) U).presheaf ⟶
      PresheafedSpace.mk (TopCat.of M) (actualComplexStructureSheaf (n := n) M).presheaf := by
  exact (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
    (ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val)

private def originalRestrictionPresheafHom (U : Opens M) :
    PresheafedSpace.mk (TopCat.of U) (literalRingSheaf (n := n) U).presheaf ⟶
      PresheafedSpace.mk (TopCat.of M) (actualComplexStructureSheaf (n := n) M).presheaf := by
  exact (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
    ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).ofRestrict U.isOpenEmbedding)

omit [IsComplexManifold n M] in
private theorem actualLiteralRingIso_normalized (U : Opens M) :
    idBasePresheafHom (actualLiteralRingIso (n := n) U).hom.hom =
      actualOpenComparisonPresheafHom (n := n) U := by
  have hb : (actualOpenComparisonPresheafHom (n := n) U).base = 𝟙 (TopCat.of U) :=
    restrictLocallyRingedSpaceIso_base (n := n) U
  have hm : (actualLiteralRingIso (n := n) U).hom.hom =
      fixedBasePresheafMap (actualOpenComparisonPresheafHom (n := n) U) hb := rfl
  exact (congrArg idBasePresheafHom hm).trans
    (normalize_base_presheaf_hom (actualOpenComparisonPresheafHom (n := n) U) hb)

omit [IsComplexManifold n M] in
private theorem actualLiteralRingIso_full_ambient (U : Opens M) :
    idBasePresheafHom (actualLiteralRingIso (n := n) U).hom.hom ≫
      actualOpenValPresheafHom (n := n) U = originalRestrictionPresheafHom (n := n) U := by
  rw [actualLiteralRingIso_normalized]
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  have h :
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val =
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M).ofRestrict U.isOpenEmbedding :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (by rfl)
  exact (F.map_comp _ _).symm.trans (F.congr_map h)

omit [IsComplexManifold n M] in
private theorem actualLiteralRingIso_original_stalk (U : Opens M) (y : U)
    (s : actualComplexStructureStalk (n := n) y.val) :
    scalarStalkEquiv (actualLiteralRingIso (n := n) U) y
      ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val).stalkMap y s) =
      (originalRestrictionPresheafHom (n := n) U).stalkMap y s := by
  let e := actualLiteralRingIso (n := n) U
  let f := idBasePresheafHom e.hom.hom
  let v := actualOpenValPresheafHom (n := n) U
  let j := originalRestrictionPresheafHom (n := n) U
  have H : f ≫ v = j := actualLiteralRingIso_full_ambient (n := n) U
  have hEq : (f ≫ v).stalkMap y = j.stalkMap y := by
    have h := PresheafedSpace.stalkMap.congr_hom (f ≫ v) j H y
    change (f ≫ v).stalkMap y =
      𝟙 ((actualComplexStructureSheaf (n := n) M).presheaf.stalk y.val) ≫ j.stalkMap y at h
    exact h.trans (Category.id_comp _)
  have hc : v.stalkMap y ≫ f.stalkMap y = j.stalkMap y :=
    (PresheafedSpace.stalkMap.comp f v y).symm.trans hEq
  have hs := ConcreteCategory.congr_hom hc s
  change ((TopCat.Presheaf.stalkFunctor CommRingCat y).map e.hom.hom) (v.stalkMap y s) = j.stalkMap y s
  exact (idBasePresheafHom_stalkMap e.hom.hom y (v.stalkMap y s)).symm.trans hs

private theorem actualOpenVal_stalk_chart (U : Opens M) (y : U)
    (s : actualComplexStructureStalk (n := n) y.val) :
    actualStalkChartEquiv (n := n) y
      ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val).stalkMap y s) =
      actualStalkChartEquiv (n := n) y.val s := by
  have h := HironakaActualAnalyticSubspaceOpenRestriction.actualNativeStalk_chart_pullback
    (f := (Subtype.val : U → M)) contMDiff_subtype_val y s
  exact h.trans (DFunLike.congr_fun
    (HironakaActualOpenIntrinsicHS.actualHolomorphicGermPullback_val U y)
      (actualStalkChartEquiv (n := n) y.val s))

/-- The LITERAL original restricted structure sheaf, with its native values
and operations. This abbreviation only gives the existing factory a typed
open-domain interface. -/
abbrev originalOpenStructureSheaf (U : Opens (ComplexModel n)) :
    (TopCat.of U).Sheaf CommRingCat.{0} := literalRingSheaf (n := n) U

/-- The existing native pushforward of the actual closed-subspace unit,
through the genuine native open-scalar comparison. -/
abbrev originalPrimeSupportModule (U : Opens (ComplexModel n)) (W : Set U) :
    SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)) :=
  (scalarIsoEquivalence (nativeForgetRingIso (actualLiteralRingIso (n := n) U))).functor.obj
    (supportModule (n := n) W)

/-- The actual native scalar quotient into that same support module. -/
def originalPrimeSupportQuotient (U : Opens (ComplexModel n)) (W : Set U) :
    SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) ⟶ originalPrimeSupportModule U W :=
  (scalarIsoUnitIso (nativeForgetRingIso (actualLiteralRingIso (n := n) U))).hom ≫
    (scalarIsoEquivalence (nativeForgetRingIso (actualLiteralRingIso (n := n) U))).functor.map
      (supportQuotient (n := n) W)

/-- The actual native stalk equivalence induced by the genuine manifold
open-restriction structure-sheaf isomorphism. -/
def actualOpenLiteralStalkEquiv (U : Opens (ComplexModel n)) (y : U) :
    actualComplexStructureStalk (n := n) y ≃+*
      ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).presheaf y) :=
  scalarStalkEquiv (actualLiteralRingIso (n := n) U) y

/-- Mathlib's native ORIGINAL restriction-stalk isomorphism, retyped over
the same literal open carrier. No point or scalar action is replaced. -/
def originalRestrictionStalkEquiv (U : Opens (ComplexModel n)) (y : U) :
    actualComplexStructureStalk (n := n) y.val ≃+*
      ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).presheaf y) := by
  let X := PresheafedSpace.mk (TopCat.of (ComplexModel n))
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let i : TopCat.of U ⟶ TopCat.of (ComplexModel n) := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩
  have hi : Topology.IsOpenEmbedding i.hom := U.isOpenEmbedding'
  exact (PresheafedSpace.restrictStalkIso X (f := i) hi y).symm.commRingCatIsoToRingEquiv

private theorem originalRestrictionStalkEquiv_apply (U : Opens (ComplexModel n)) (y : U)
    (s : actualComplexStructureStalk (n := n) y.val) :
    originalRestrictionStalkEquiv U y s = (originalRestrictionPresheafHom (n := n) U).stalkMap y s := by
  let X := PresheafedSpace.mk (TopCat.of (ComplexModel n))
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let i : TopCat.of U ⟶ TopCat.of (ComplexModel n) := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩
  have hi : Topology.IsOpenEmbedding i.hom := U.isOpenEmbedding'
  exact ConcreteCategory.congr_hom (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X (f := i) hi y) s

private theorem originalPrimeWhole_mem_iff (U : Opens (ComplexModel n))
    (p : ComplexModel n) (hpU : p ∈ U) (W : Set U)
    (P : Ideal (actualComplexStructureStalk (n := n) p))
    (hP : Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom P =
      wholeChartStalkIdeal (vanishingIdeal (n := n) W) (⟨p,hpU⟩ : U) ⟨p,hpU⟩
        (mem_chart_source (ComplexModel n) (⟨p,hpU⟩ : U)))
    (s : actualComplexStructureStalk (n := n) p) :
    (ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → ComplexModel n) contMDiff_subtype_val).stalkMap
      (⟨p,hpU⟩ : U) s ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) (⟨p,hpU⟩ : U) ↔ s ∈ P := by
  let y : U := ⟨p,hpU⟩
  let I := actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y
  let α := actualStalkChartEquiv (n := n) y
  let β := actualStalkChartEquiv (n := n) p
  let x := (ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → ComplexModel n) contMDiff_subtype_val).stalkMap y s
  have hm : x ∈ I ↔ α x ∈ wholeChartStalkIdeal (vanishingIdeal (n := n) W) y y
      (mem_chart_source (ComplexModel n) y) := by
    rw [← map_actualWholeSheafStalkIdeal]
    change x ∈ I ↔ x ∈ Ideal.comap α.toRingHom (Ideal.map α.toRingHom I)
    rw [I.comap_map_of_bijective α.toRingHom α.bijective]
  change x ∈ I ↔ s ∈ P
  change x ∈ I ↔ α
    ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → ComplexModel n) contMDiff_subtype_val).stalkMap y s) ∈
      wholeChartStalkIdeal (vanishingIdeal (n := n) W) y y (mem_chart_source (ComplexModel n) y) at hm
  rw [actualOpenVal_stalk_chart,← hP] at hm
  change x ∈ I ↔ s ∈ Ideal.comap β.toRingHom (Ideal.map β.toRingHom P) at hm
  rw [P.comap_map_of_bijective β.toRingHom β.bijective] at hm
  exact hm

/-- Pure ORIGINAL-ring comparison. The whole chart ideal is obtained
internally from the ordinary prime; no module, kernel, or continuation
certificate is an input to this scalar identity. -/
private theorem original_prime_ideal_membership (U : Opens (ComplexModel n))
    (p : ComplexModel n) (hpU : p ∈ U) (W : Set U)
    (P : Ideal (actualComplexStructureStalk (n := n) p))
    (hP : Ideal.map (actualStalkChartEquiv (n := n) p).toRingHom P =
      wholeChartStalkIdeal (vanishingIdeal (n := n) W) (⟨p,hpU⟩ : U) ⟨p,hpU⟩
        (mem_chart_source (ComplexModel n) (⟨p,hpU⟩ : U)))
    (s : actualComplexStructureStalk (n := n) p) :
    originalRestrictionStalkEquiv U (⟨p,hpU⟩ : U) s ∈
      Ideal.map (actualOpenLiteralStalkEquiv U (⟨p,hpU⟩ : U)).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) (⟨p,hpU⟩ : U)) ↔ s ∈ P := by
  let y : U := ⟨p,hpU⟩
  let x := (ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → ComplexModel n) contMDiff_subtype_val).stalkMap y s
  let I := actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y
  let L := actualOpenLiteralStalkEquiv U y
  have hOrig : L x = originalRestrictionStalkEquiv U y s :=
    (actualLiteralRingIso_original_stalk (n := n) U y s).trans
      (originalRestrictionStalkEquiv_apply U y s).symm
  change originalRestrictionStalkEquiv U y s ∈ Ideal.map L.toRingHom I ↔ s ∈ P
  rw [← hOrig]
  have hm : L x ∈ Ideal.map L.toRingHom I ↔ x ∈ I := by
    change x ∈ Ideal.comap L.toRingHom (Ideal.map L.toRingHom I) ↔ x ∈ I
    rw [I.comap_map_of_bijective L.toRingHom L.bijective]
  exact hm.trans (originalPrimeWhole_mem_iff U p hpU W P hP s)

/-- Apply the actual regular-component continuation on the SAME whole
representative. This is a private elaboration boundary, not a new input
packet or a new continuation hypothesis in the public result. -/
private theorem literal_whole_support_continuation (U : Opens (ComplexModel n))
    {W : Set U} (hW : IsComplexAnalyticSubset (n := n) W) {c : U} {d : ℕ}
    (hc : RegularAtDim (n := n) W c d)
    (hWC : W = closure (RegularLocusComponent.component (n := n) W c)) {r : ℕ}
    (a : Fin r → actualComplexSection (n := n) (⊤ : Opens U))
    (hspan : ∀ y : U, actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y =
      Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) U).presheaf.germ ⊤ y (by trivial) (a i)))
    (p : U) (hpW : p ∈ W)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))} [G.IsFiniteType]
    (f : G ⟶ cokernel (scalarRelationMap (actualLiteralRingIso (n := n) U)
      (cyclicRelationMap (actualComplexStructureSheaf (n := n) U) a)))
    (hp : stalkLinearMap f.val p = 0) : f = 0 := by
  have hspan' (y : U) : actualWholeSheafStalkIdeal
      (vanishingIdeal (n := n) (closure (RegularLocusComponent.component (n := n) W c))) y =
        Ideal.span (range fun i =>
          (actualComplexStructureSheaf (n := n) U).presheaf.germ ⊤ y (by trivial) (a i)) :=
    (congrArg (fun T : Set U => actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) y) hWC).symm.trans
      (hspan y)
  have hp' : p ∈ closure (RegularLocusComponent.component (n := n) W c) := hWC ▸ hpW
  exact literal_component_hom_continuation (n := n) (M := ComplexModel n)
    (A := W) (c := c) (k := d) (G := G) U hW hc a hspan' p hp' f hp

/-- An ordinary prime in the ACTUAL original ambient stalk constructs a
native finitely presented cyclic target on ONE genuine original open.
That target/open precedes ALL finite-type sources and FULL maps. -/
theorem exists_native_prime_support_continuation (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    ∃ (U : Opens (ComplexModel n)) (hpU : p ∈ U),
      let R := originalOpenStructureSheaf U
      ∃ (r : ℕ) (g : Fin r → R.obj.obj (op ⊤)) (W : Set U)
        (δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R))
        (C : SheafOfModules.{0} (forgetRing R)) (κ : SheafOfModules.unit (forgetRing R) ⟶ C),
        IsComplexAnalyticSubset (n := n) W ∧ (⟨p,hpU⟩ : U) ∈ W ∧
        IsComplexAnalyticallyIrreducible (n := n) W ∧ C.IsFinitePresentation ∧
        (∃ e : cokernel δ ≅ C, cokernel.π δ ≫ e.hom = κ) ∧
        (∃ e : C ≅ originalPrimeSupportModule U W,
          κ ≫ e.hom = originalPrimeSupportQuotient U W) ∧
        (∀ y : U,
          let q := Ideal.span (range fun i => R.presheaf.germ ⊤ y (by trivial) (g i))
          q = Ideal.map (actualOpenLiteralStalkEquiv U y).toRingHom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) ∧
          (∀ s : ↑(TopCat.Presheaf.stalk R.obj y),
            stalkLinearMap κ.val y ((unitStalkLinearEquiv R y).symm s) = 0 ↔ s ∈ q) ∧
          ∃ Q : ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj y)
              (↑(TopCat.Presheaf.stalk R.obj y) ⧸ (q : Submodule _ _)) ≅
                (nativeStalkFunctor R y).obj C,
            ∀ s : ↑(TopCat.Presheaf.stalk R.obj y),
              Q.hom (Submodule.Quotient.mk s) =
                stalkLinearMap κ.val y ((unitStalkLinearEquiv R y).symm s)) ∧
        (∀ s : actualComplexStructureStalk (n := n) p,
          stalkLinearMap κ.val (⟨p,hpU⟩ : U)
            ((unitStalkLinearEquiv R (⟨p,hpU⟩ : U)).symm
              (originalRestrictionStalkEquiv U (⟨p,hpU⟩ : U) s)) = 0 ↔ s ∈ P) ∧
        ∀ (G : SheafOfModules.{0} (forgetRing R)) (_hG : G.IsFiniteType) (f : G ⟶ C),
          stalkLinearMap f.val (⟨p,hpU⟩ : U) = 0 → f = 0 := by
  classical
  obtain ⟨U,hpU,r,a,W,d,c,hW,hpW,hc,hWC,hIrr,hspan,hP⟩ := exists_prime_native_whole_family (n := n) p P
  let R : (TopCat.of U).Sheaf CommRingCat.{0} := originalOpenStructureSheaf U
  let e : actualComplexStructureSheaf (n := n) U ≅ R := actualLiteralRingIso (n := n) U
  let g (i : Fin r) : R.obj.obj (op ⊤) := e.hom.hom.app (op ⊤) (a i)
  let δ : SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R) :=
    scalarRelationMap e (cyclicRelationMap (actualComplexStructureSheaf (n := n) U) a)
  let C : SheafOfModules.{0} (forgetRing R) := cokernel δ
  let κ : SheafOfModules.unit (forgetRing R) ⟶ C := cokernel.π δ
  let ν := supportScalarCokernelIso W hW.isClosed a hspan e
  refine ⟨U,hpU,r,g,W,δ,C,κ,hW,hpW,hIrr,cokernel_to_unit_finitePresentation R δ,
    ⟨Iso.refl C,Category.comp_id _⟩,
    ⟨ν,supportScalarCokernelIso_quotient W hW.isClosed a hspan e⟩,?_,?_,?_⟩
  · intro y
    let q : Ideal ↑(TopCat.Presheaf.stalk R.obj y) :=
      Ideal.span (range fun i => R.presheaf.germ ⊤ y (by trivial) (g i))
    have hmap : Ideal.map (actualOpenLiteralStalkEquiv U y).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) = q :=
      map_whole_family_eq_scalar_span W a hspan e y
    have hz (s : ↑(TopCat.Presheaf.stalk R.obj y)) : unitDomainStalkMap R κ y s = 0 ↔ s ∈ q := by
      have hs := supportScalarCokernel_stalk_zero_iff W hW.isClosed a hspan e y s
      have hmap' : Ideal.map (scalarStalkEquiv e y).toRingHom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y) = q := hmap
      have hm := congrArg (fun J : Ideal ↑(TopCat.Presheaf.stalk R.obj y) => s ∈ J) hmap'
      exact hs.trans (Iff.of_eq hm)
    have hsurj : Function.Surjective (unitDomainStalkMap R κ y) :=
      (stalkLinearMap_surjective_of_epi R κ y).comp (unitStalkLinearEquiv R y).symm.surjective
    let Q := unitDomainStalkQuotientOfZeroIff R κ y q hz hsurj
    let QI : ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj y)
        (↑(TopCat.Presheaf.stalk R.obj y) ⧸ (q : Submodule _ _)) ≅
          (nativeStalkFunctor R y).obj (cokernel δ) := by
      exact Q.toModuleIso
    refine ⟨hmap.symm,hz,⟨QI,?_⟩⟩
    intro s
    exact unitDomainStalkQuotientOfZeroIff_mk R κ y q hz hsurj s
  · intro s
    have hz := supportScalarCokernel_stalk_zero_iff W hW.isClosed a hspan e (⟨p,hpU⟩ : U)
      (originalRestrictionStalkEquiv U (⟨p,hpU⟩ : U) s)
    exact hz.trans (original_prime_ideal_membership (n := n) U p hpU W P hP s)
  · intro G hG f hf
    let : G.IsFiniteType := hG
    exact literal_whole_support_continuation (n := n) U hW hc hWC a hspan
      (⟨p,hpU⟩ : U) hpW f hf

end Hironaka.HironakaChowNativePrimeSupportContinuation
