import Hironaka.Resolution.HironakaChowNativePrimeSupportContinuation
import Hironaka.Analytic.ClosureDifferenceAnalytic

/-! Whole morphism continuation into a fixed actual reduced irreducible
support. The literal original open and native target are fixed before all
finite-type sources and full maps. No new open, target presentation or
continuation certificate is an input. Blueprint FIRST:
`hironaka-g10-native-irreducible-support-continuation.tex`. -/

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaNativeIrreducibleSupportContinuation

open Hironaka.HolomorphicIdealSheaves
  HironakaChowNativePrimeSupportContinuation
  HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaSingularRankOneLocalGenerators
  HironakaChowNativeModuleStalkExact HironakaChowNativeFiniteFreeStalk
  HironakaChowNativeSectionSpreading HironakaChowNativeFinitePresentationSpreading
  HironakaChowNativeFiniteTypeSpreading
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceResidue

variable {n : ℕ}

private theorem restrictionIso_base (U : Opens (ComplexModel n)) :
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom.base =
      𝟙 (TopCat.of U) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  have h :
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U).hom ≫
        ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → ComplexModel n) contMDiff_subtype_val =
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) (ComplexModel n)).ofRestrict
        U.isOpenEmbedding :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (by rfl)
  exact congrArg (fun f => f.base x) h

private def openScalarIso (U : Opens (ComplexModel n)) :
    actualComplexStructureSheaf (n := n) U ≅ originalOpenStructureSheaf U := by
  let e := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ,ComplexModel n)) U)
  let eP := PresheafedSpace.sheafIsoOfIso e
  let eQ := eP ≪≫ TopCat.Presheaf.pushforwardEq (restrictionIso_base U) _ ≪≫
    TopCat.Presheaf.Pushforward.id _
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of U))
    CommRingCat).preimageIso eQ

private theorem inverseScalar_germ (U : Opens (ComplexModel n)) (y : U)
    (O : Opens U) (hy : y ∈ O) (r : (originalOpenStructureSheaf U).obj.obj (op O)) :
    (actualOpenLiteralStalkEquiv U y).symm
        ((originalOpenStructureSheaf U).presheaf.germ O y hy r) =
      (actualComplexStructureSheaf (n := n) U).presheaf.germ O y hy
        ((openScalarIso U).inv.hom.app (op O) r) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply O y hy (openScalarIso U).inv.hom r

private def supportValue (U : Opens (ComplexModel n)) (W : Set U) (O : Opens U)
    (s : (originalPrimeSupportModule U W).val.obj (op O))
    (y : W) (hy : y.val ∈ O) : ℂ :=
  actualSubspaceStalkEval (n := n) W y
    ((actualSubspaceSheaf (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion W)).obj O) y hy s)

private theorem supportValue_restrict (U : Opens (ComplexModel n)) (W : Set U)
    (O T : Opens U) (hTO : T ≤ O)
    (s : (originalPrimeSupportModule U W).val.obj (op O))
    (y : W) (hy : y.val ∈ T) :
    supportValue U W T ((originalPrimeSupportModule U W).val.map (homOfLE hTO).op s) y hy =
      supportValue U W O s y (hTO hy) := by
  exact congrArg (actualSubspaceStalkEval (n := n) W y)
    ((actualSubspaceSheaf (n := n) W).presheaf.germ_res_apply
      ((Opens.map (actualSubspaceTopInclusion W)).map (homOfLE hTO)) y hy s)

private theorem supportSection_eq_zero (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (s : (originalPrimeSupportModule U W).val.obj (op O))
    (hs : ∀ (y : W) (hy : y.val ∈ O), supportValue U W O s y hy = 0) : s = 0 := by
  exact actualSubspaceSection_eq_zero_of_eval W
    ((Opens.map (actualSubspaceTopInclusion W)).obj O) s hs

private def supportScalarResidue (U : Opens (ComplexModel n)) (W : Set U) (y : W) :
    ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).presheaf y.val) →+* ℂ :=
  (actualSubspaceStalkEval (n := n) W y).comp
    (((actualSubspaceInclusion (n := n) W).stalkMap y).hom.comp
      (actualOpenLiteralStalkEquiv U y.val).symm.toRingHom)

private theorem supportScalarResidue_germ (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (r : (originalOpenStructureSheaf U).obj.obj (op O))
    (y : W) (hy : y.val ∈ O) :
    supportScalarResidue U W y ((originalOpenStructureSheaf U).presheaf.germ O y.val hy r) =
      ((openScalarIso U).inv.hom.app (op O) r) ⟨y.val,hy⟩ := by
  unfold supportScalarResidue
  simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe]
  rw [inverseScalar_germ]
  exact actualSubspaceStalkEval_inclusion_germ W O
    ((openScalarIso U).inv.hom.app (op O) r) y hy

private theorem supportValue_smul (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (r : (forgetRing (originalOpenStructureSheaf U)).obj.obj (op O))
    (s : (originalPrimeSupportModule U W).val.obj (op O)) (y : W) (hy : y.val ∈ O) :
    supportValue U W O (r • s) y hy =
      supportScalarResidue U W y ((originalOpenStructureSheaf U).presheaf.germ O y.val hy r) *
        supportValue U W O s y hy := by
  let t := (openScalarIso U).inv.hom.app (op O) r
  let T := ((Opens.map (actualSubspaceTopInclusion W)).obj O)
  let a : (actualSubspaceSheaf (n := n) W).presheaf.obj (op T) :=
    (actualSubspaceInclusion (n := n) W).toHom.c.app (op O) t
  let b : (actualSubspaceSheaf (n := n) W).presheaf.obj (op T) := s
  let ev := (actualSubspaceStalkEval (n := n) W y).comp
    ((actualSubspaceSheaf (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion W)).obj O) y hy).hom
  change ev (a * b) = _
  have ht : ev ((actualSubspaceInclusion (n := n) W).toHom.c.app (op O) t) =
      t ⟨y.val,hy⟩ := by
    exact (congrArg (actualSubspaceStalkEval (n := n) W y)
      (LocallyRingedSpace.stalkMap_germ_apply (actualSubspaceInclusion (n := n) W)
        O y hy t).symm).trans (actualSubspaceStalkEval_inclusion_germ W O t y hy)
  exact (ev.map_mul _ _).trans ((congrArg (fun z => z * ev b) ht).trans
    (congrArg (fun z => z * ev b) (supportScalarResidue_germ U W O r y hy).symm))

private def supportStalkValue (U : Opens (ComplexModel n)) (W : Set U) (y : W) :
    ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf y.val) →+ ℂ :=
  (actualSubspaceStalkEval (n := n) W y).toAddMonoidHom.comp
    ((unitStalkLinearEquiv (actualSubspaceSheaf (n := n) W) y).toAddMonoidHom.comp
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat (actualSubspaceTopInclusion W)
        (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf y).hom)

private theorem supportStalkValue_germ (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (s : (originalPrimeSupportModule U W).val.obj (op O))
    (y : W) (hy : y.val ∈ O) :
    supportStalkValue U W y
        (TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf O y.val hy s) =
      supportValue U W O s y hy := by
  unfold supportStalkValue
  simp only [AddMonoidHom.comp_apply]
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat (actualSubspaceTopInclusion W)
      (SheafOfModules.unit (forgetRing (actualSubspaceSheaf (n := n) W))).val.presheaf O y hy) s
  exact (congrArg (fun a => actualSubspaceStalkEval (n := n) W y
    (unitStalkLinearEquiv (actualSubspaceSheaf (n := n) W) y a)) h).trans
      (congrArg (actualSubspaceStalkEval (n := n) W y)
        (unitStalkLinearEquiv_germ (actualSubspaceSheaf (n := n) W) y
          ((Opens.map (actualSubspaceTopInclusion W)).obj O) hy s))

private theorem stalkValue_smul_of_germs {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (T : SheafOfModules.{0} (forgetRing R)) (y : X)
    (v : ↑(TopCat.Presheaf.stalk T.val.presheaf y) →+ ℂ)
    (ρ : ↑(TopCat.Presheaf.stalk R.obj y) →+* ℂ)
    (values : ∀ O : Opens X, y ∈ O → T.val.obj (op O) → ℂ)
    (hg : ∀ (O : Opens X) (hy : y ∈ O) (s : T.val.obj (op O)),
      v (TopCat.Presheaf.germ T.val.presheaf O y hy s) = values O hy s)
    (hs : ∀ (O : Opens X) (hy : y ∈ O)
      (a : (forgetRing R).obj.obj (op O)) (s : T.val.obj (op O)),
      values O hy (a • s) = ρ (R.presheaf.germ O y hy a) * values O hy s)
    (a : ↑(TopCat.Presheaf.stalk R.obj y))
    (s : ↑(TopCat.Presheaf.stalk T.val.presheaf y)) :
    v (a • s) = ρ a * v s := by
  obtain ⟨O,hyO,s,rfl⟩ := TopCat.Presheaf.exists_germ_eq T.val.presheaf s
  obtain ⟨P,hPO,hyP,a,rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R.presheaf a hyO
  rw [← TopCat.Presheaf.germ_res_apply T.val.presheaf (homOfLE hPO) y hyP s]
  erw [← PresheafOfModules.germ_smul (R := R.obj),hg,hs,hg]

private theorem supportStalkValue_smul (U : Opens (ComplexModel n)) (W : Set U) (y : W)
    (r : ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val))
    (m : ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf y.val)) :
    letI := nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) y.val
    supportStalkValue U W y (r • m) =
      supportScalarResidue U W y r * supportStalkValue U W y m := by
  exact stalkValue_smul_of_germs (originalOpenStructureSheaf U) (originalPrimeSupportModule U W)
    y.val (supportStalkValue U W y) (supportScalarResidue U W y)
    (fun O hy s => supportValue U W O s y hy)
    (fun O hy s => supportStalkValue_germ U W O s y hy)
    (fun O hy a s => supportValue_smul U W O a s y hy) r m

section Generators
variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  {G : SheafOfModules.{0} (forgetRing R)}

private def generatorSection (O : Opens X) (σ : (G.over O).GeneratingSections) (i : σ.I) :
    G.val.obj (op O) := (σ.s i).val (op (Over.mk (𝟙 O)))

private def generatorMap (O : Opens X) (σ : (G.over O).GeneratingSections) :
    (SheafOfModules.free (R := forgetRing R) σ.I).over O ⟶ G.over O :=
  (freeOverIso R O σ.I).inv ≫ σ.π

private instance generatorMap_epi (O : Opens X) (σ : (G.over O).GeneratingSections) :
    Epi (generatorMap R O σ) := by
  dsimp [generatorMap]
  infer_instance

private theorem generatorMap_ι (O : Opens X) (σ : (G.over O).GeneratingSections) (i : σ.I) :
    (SheafOfModules.ιFree (R := forgetRing R) i).over O ≫ generatorMap R O σ =
      localUnitMap R O (generatorSection R O σ i) := by
  have hs : σ.s = fun j => (G.over O).unitHomEquiv
      (localUnitMap R O (generatorSection R O σ j)) := by
    funext j
    ext P
    rw [SheafOfModules.unitHomEquiv_apply_coe]
    erw [localUnitMap_app,one_smul]
    let a : P.unop ⟶ Over.mk (𝟙 O) := Over.homMk P.unop.hom
    exact ((σ.s j).property a.op).symm
  have he : generatorMap R O σ = freeOverMap R O (generatorSection R O σ) := by
    unfold generatorMap freeOverMap
    exact congrArg (fun s => (freeOverIso R O σ.I).inv ≫ (G.over O).freeHomEquiv.symm s) hs
  exact (congrArg (fun k => (SheafOfModules.ιFree (R := forgetRing R) i).over O ≫ k) he).trans
    (ι_freeOverMap R O (generatorSection R O σ) i)

private theorem generatorMap_stalk_ι (O : Opens X) (σ : (G.over O).GeneratingSections)
    (x : X) (hxO : x ∈ O) (i : σ.I) (a : ↑(TopCat.Presheaf.stalk R.obj x)) :
    stalkLinearMapOfOver R O (generatorMap R O σ) x hxO
      (stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) i).val x
        ((unitStalkLinearEquiv R x).symm a)) =
      a • TopCat.Presheaf.germ G.val.presheaf O x hxO (generatorSection R O σ i) := by
  have h := congrArg (fun k => stalkLinearMapOfOver R O k x hxO) (generatorMap_ι R O σ i)
  rw [stalkLinearMapOfOver_comp,stalkLinearMapOfOver_homOver] at h
  exact (LinearMap.congr_fun h ((unitStalkLinearEquiv R x).symm a)).trans
    (localUnitMap_stalk R O (generatorSection R O σ i) x hxO a)

private theorem generatorSection_stalk_span (O : Opens X) (σ : (G.over O).GeneratingSections)
    [σ.IsFiniteType] (x : X) (hxO : x ∈ O) :
    Submodule.span ↑(TopCat.Presheaf.stalk R.obj x)
      (range fun i => TopCat.Presheaf.germ G.val.presheaf O x hxO (generatorSection R O σ i)) = ⊤ := by
  classical
  let := Fintype.ofFinite σ.I
  let e := finiteFreeStalkLinearEquiv R σ.I x
  let p := stalkLinearMapOfOver R O (generatorMap R O σ) x hxO
  apply top_unique
  intro m _
  obtain ⟨v,rfl⟩ := stalkLinearMapOfOver_surjective_of_epi R O (generatorMap R O σ) x hxO m
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
  change p _ ∈ _
  rw [generatorMap_stalk_ι,one_smul]
  exact Submodule.subset_span (mem_range_self i)
end Generators

private def fibreZeroLocus (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    (f : G ⟶ originalPrimeSupportModule U W) : Set U :=
  {y | ∃ hyW : y ∈ W, ∀ (O : Opens U) (hy : y ∈ O) (s : G.val.obj (op O)),
    supportValue U W O (f.val.app (op O) s) ⟨y,hyW⟩ hy = 0}

private def valueKernel {A T : Type} [CommRing A] [AddCommGroup T] [Module A T]
    (v : T →+ ℂ) (ρ : A →+* ℂ) (hv : ∀ a t, v (a • t) = ρ a * v t) : Submodule A T where
  carrier := {t | v t = 0}
  zero_mem' := v.map_zero
  add_mem' := by
    intro a b ha hb
    exact (v.map_add a b).trans ((congrArg₂ (·+·) ha hb).trans (add_zero 0))
  smul_mem' := by
    intro a t ht
    exact (hv a t).trans ((congrArg (fun z => ρ a * z) ht).trans (mul_zero _))

private def supportValueKernel (U : Opens (ComplexModel n)) (W : Set U) (y : W) :
    letI := nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) y.val
    Submodule ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val)
      ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf y.val) := by
  letI := nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) y.val
  exact valueKernel (supportStalkValue U W y) (supportScalarResidue U W y)
    (supportStalkValue_smul U W y)

private def fibreKernel (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    (f : G ⟶ originalPrimeSupportModule U W) (y : W) :
    letI := nativeSheafStalkModule (originalOpenStructureSheaf U) G y.val
    Submodule ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y.val) := by
  exact @Submodule.comap
    ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val)
    ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val)
    ↑(TopCat.Presheaf.stalk G.val.presheaf y.val)
    ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf y.val)
    inferInstance inferInstance inferInstance inferInstance
    (nativeSheafStalkModule (originalOpenStructureSheaf U) G y.val)
    (nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) y.val)
    (RingHom.id _)
    (stalkLinearMap (R := (originalOpenStructureSheaf U).obj)
      (M := G.val) (N := (originalPrimeSupportModule U W).val) f.val y.val)
    (supportValueKernel U W y)

private theorem mem_fibreZeroLocus_iff (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    (f : G ⟶ originalPrimeSupportModule U W) (y : W) :
    y.val ∈ fibreZeroLocus U W f ↔ fibreKernel U W f y = ⊤ := by
  constructor
  · rintro ⟨_,hy⟩
    apply top_unique
    intro m _
    obtain ⟨O,hyO,s,rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
    change supportStalkValue U W y
      (stalkLinearMap (R := (originalOpenStructureSheaf U).obj) f.val y.val
        (TopCat.Presheaf.germ G.val.presheaf O y.val hyO s)) = 0
    erw [stalkLinearMap_germ,supportStalkValue_germ]
    exact hy O hyO s
  · intro h
    refine ⟨y.property,?_⟩
    intro O hyO s
    have hm : TopCat.Presheaf.germ G.val.presheaf O y.val hyO s ∈ fibreKernel U W f y := by
      rw [h]
      trivial
    change supportStalkValue U W y
      (stalkLinearMap (R := (originalOpenStructureSheaf U).obj) f.val y.val
        (TopCat.Presheaf.germ G.val.presheaf O y.val hyO s)) = 0 at hm
    erw [stalkLinearMap_germ,supportStalkValue_germ] at hm
    exact hm

private theorem mem_fibreZeroLocus_iff_generators (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    (f : G ⟶ originalPrimeSupportModule U W) (O : Opens U)
    (σ : (G.over O).GeneratingSections) [σ.IsFiniteType] (y : W) (hyO : y.val ∈ O) :
    y.val ∈ fibreZeroLocus U W f ↔ ∀ i : σ.I,
      supportValue U W O (f.val.app (op O)
        (generatorSection (originalOpenStructureSheaf U) O σ i)) y hyO = 0 := by
  let : Module ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).obj y.val)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y.val) :=
    nativeSheafStalkModule (originalOpenStructureSheaf U) G y.val
  constructor
  · rintro ⟨_,hy⟩ i
    exact hy O hyO _
  · intro h
    apply (mem_fibreZeroLocus_iff U W f y).mpr
    apply top_unique
    rw [← generatorSection_stalk_span (originalOpenStructureSheaf U) O σ y.val hyO]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change supportStalkValue U W y
      (stalkLinearMap (R := (originalOpenStructureSheaf U).obj) f.val y.val
        (TopCat.Presheaf.germ G.val.presheaf O y.val hyO
          (generatorSection (originalOpenStructureSheaf U) O σ i))) = 0
    erw [stalkLinearMap_germ,supportStalkValue_germ]
    exact h i

private theorem hom_eq_zero_of_fibreZero (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    (f : G ⟶ originalPrimeSupportModule U W) (h : W ⊆ fibreZeroLocus U W f) : f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change f.val.app O s = 0
  apply supportSection_eq_zero U W O.unop
  intro y hy
  exact (h y.property).choose_spec O.unop hy s

private theorem common_zero_analytic {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {k : ℕ}
    (g : Fin k → M → ℂ)
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

private theorem exists_fibreZero_equations (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    [G.IsFiniteType] (f : G ⟶ originalPrimeSupportModule U W) (y : W) :
    ∃ (O : Opens U) (_hyO : y.val ∈ O) (k : ℕ)
      (t : Fin k → actualComplexSection (n := n) O),
      ∀ (z : U) (hz : z ∈ O),
        z ∈ fibreZeroLocus U W f ↔ z ∈ W ∧ ∀ i, t i ⟨z,hz⟩ = 0 := by
  classical
  let R := originalOpenStructureSheaf U
  obtain ⟨q,hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  obtain ⟨O,j,hO,hyO⟩ :=
    (Opens.mem_grothendieckTopology (TopCat.of U)).mp (q.coversTop ⊤) y.val (by trivial)
  obtain ⟨a,⟨ha⟩⟩ := (Sieve.mem_ofObjects_iff q.X j).mp hO
  let Q := q.X a
  have hyQ : y.val ∈ Q := ha.le hyO
  let σ := q.generators a
  have : σ.IsFiniteType := hq.isFiniteType a
  let := Fintype.ofFinite σ.I
  let k := Fintype.card σ.I
  let e := Fintype.equivFin σ.I
  let s (i : Fin k) : (originalPrimeSupportModule U W).val.obj (op Q) :=
    f.val.app (op Q) (generatorSection R Q σ (e.symm i))
  choose O hyO t hOQ ht using fun i : Fin k =>
    actualSubspaceSection_local_ambient W
      ((Opens.map (actualSubspaceTopInclusion W)).obj Q) (s i) y hyQ
  let T : Opens U := Q ⊓ ⨅ i : Fin k, O i
  have hTQ : T ≤ Q := inf_le_left
  have hTO (i : Fin k) : T ≤ O i := inf_le_right.trans (iInf_le O i)
  have hyT : y.val ∈ T := by
    change y.val ∈ (Q : Set U) ∩ ((⨅ i : Fin k, O i : Opens U) : Set U)
    rw [Opens.coe_iInf]
    exact ⟨hyQ,mem_iInter.mpr hyO⟩
  let tT (i : Fin k) : actualComplexSection (n := n) T :=
    (actualComplexStructureSheaf (n := n) U).obj.map (homOfLE (hTO i)).op (t i)
  have hvalue (i : Fin k) (z : W) (hz : z.val ∈ T) :
      supportValue U W Q (s i) z (hTQ hz) = tT i ⟨z.val,hz⟩ := by
    have hh := congrArg (actualSubspaceStalkEval (n := n) W z) (ht i z (hTO i hz))
    exact hh.trans (actualSubspaceStalkEval_inclusion_germ W (O i) (t i) z (hTO i hz))
  refine ⟨T,hyT,k,tT,?_⟩
  intro z hz
  constructor
  · rintro h
    have hzW : z ∈ W := h.choose
    refine ⟨hzW,?_⟩
    have hgens := (mem_fibreZeroLocus_iff_generators U W f Q σ ⟨z,hzW⟩ (hTQ hz)).mp h
    intro i
    exact (hvalue i ⟨z,hzW⟩ hz).symm.trans (hgens (e.symm i))
  · rintro ⟨hzW,h⟩
    apply (mem_fibreZeroLocus_iff_generators U W f Q σ ⟨z,hzW⟩ (hTQ hz)).mpr
    intro i
    have hh := (hvalue (e i) ⟨z,hzW⟩ hz).trans (h (e i))
    simpa only [s,Equiv.symm_apply_apply] using hh

private theorem fibreZero_analytic (U : Opens (ComplexModel n)) (W : Set U)
    (hW : IsComplexAnalyticSubset (n := n) W)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    [G.IsFiniteType] (f : G ⟶ originalPrimeSupportModule U W) :
    IsComplexAnalyticSubset (n := n) (fibreZeroLocus U W f) := by
  classical
  apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro y
  by_cases hyW : y ∈ W
  · obtain ⟨O,hyO,k,t,ht⟩ := exists_fibreZero_equations U W f ⟨y,hyW⟩
    refine ⟨O,hyO,?_⟩
    have he : (Subtype.val ⁻¹' fibreZeroLocus U W f : Set O) =
        (Subtype.val ⁻¹' W) ∩ {z : O | ∀ i : Fin k, t i z = 0} := by
      ext z
      exact ht z.val z.property
    rw [he]
    exact (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O).inter
      (common_zero_analytic (fun i z => t i z) (fun i => smoothSheaf.contMDiff_section (t i)))
  · let O : Opens U := ⟨Wᶜ,hW.isClosed.isOpen_compl⟩
    refine ⟨O,hyW,?_⟩
    have he : (Subtype.val ⁻¹' fibreZeroLocus U W f : Set O) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact z.property hz.choose
    rw [he]
    exact isComplexAnalyticSubset_empty

private theorem exists_open_stalk_zero {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    {G H : SheafOfModules.{0} (forgetRing R)} [G.IsFiniteType] (f : G ⟶ H)
    (p : X) (hp : stalkLinearMap f.val p = 0) :
    ∃ O : Opens X, p ∈ O ∧ ∀ y : X, y ∈ O → stalkLinearMap f.val y = 0 := by
  have he : stalkLinearMapOfOver R ⊤ (f.over ⊤) p (by trivial) =
      stalkLinearMapOfOver R ⊤ ((0 : G ⟶ H).over ⊤) p (by trivial) :=
    (stalkLinearMapOfOver_homOver R f ⊤ p (by trivial)).trans
      (hp.trans ((stalkLinearMapOfOver_homOver R (0 : G ⟶ H) ⊤ p (by trivial)).trans
        (stalkLinearMap_zero p)).symm)
  obtain ⟨O,hO,hpO,hfO⟩ := exists_restriction_eq_of_isFiniteType R ⊤
    (f.over ⊤) ((0 : G ⟶ H).over ⊤) p (by trivial) he
  refine ⟨O,hpO,?_⟩
  intro y hyO
  have hs := congrArg (fun k => stalkLinearMapOfOver R O k y hyO) hfO
  have hf := (stalkLinearMapOfOver_restrictOverHom R ⊤ O hO (f.over ⊤) y hyO).trans
    (stalkLinearMapOfOver_homOver R f ⊤ y (by trivial))
  have hz := (stalkLinearMapOfOver_restrictOverHom R ⊤ O hO ((0 : G ⟶ H).over ⊤) y hyO).trans
    ((stalkLinearMapOfOver_homOver R (0 : G ⟶ H) ⊤ y (by trivial)).trans (stalkLinearMap_zero y))
  exact hf.symm.trans (hs.trans hz)

private theorem exists_fibreZero_neighborhood (U : Opens (ComplexModel n)) (W : Set U)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    [G.IsFiniteType] (f : G ⟶ originalPrimeSupportModule U W) (p : U)
    (hp : stalkLinearMap (R := (originalOpenStructureSheaf U).obj) f.val p = 0) :
    ∃ O : Opens U, p ∈ O ∧ W ∩ (O : Set U) ⊆ fibreZeroLocus U W f := by
  obtain ⟨O,hpO,hfO⟩ := exists_open_stalk_zero (originalOpenStructureSheaf U) f p hp
  refine ⟨O,hpO,?_⟩
  rintro y ⟨hyW,hyO⟩
  refine ⟨hyW,?_⟩
  intro T hyT s
  let instG : Module ↑(TopCat.Presheaf.stalk
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).obj
        (originalOpenStructureSheaf U)) y)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y) :=
    nativeSheafStalkModule (originalOpenStructureSheaf U) G y
  let instC : Module ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).presheaf y)
      ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf y) :=
    nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) y
  have hh := DFunLike.congr_fun (hfO y hyO)
    (TopCat.Presheaf.germ G.val.presheaf T y hyT s)
  have hv := (congrArg (supportStalkValue U W ⟨y,hyW⟩) hh).trans (map_zero _)
  erw [stalkLinearMap_germ,supportStalkValue_germ] at hv
  exact hv

/-- Fixed actual original domain and reduced irreducible support precede
ALL native finite-type sources and FULL maps. No new open is chosen. -/
theorem hom_eq_zero_of_stalk_eq_zero (U : Opens (ComplexModel n)) (W : Set U)
    (hW : IsComplexAnalyticallyIrreducible (n := n) W) (p : U) (hpW : p ∈ W)
    {G : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))}
    [G.IsFiniteType] (f : G ⟶ originalPrimeSupportModule U W)
    (hp : stalkLinearMap (R := (originalOpenStructureSheaf U).obj) f.val p = 0) : f = 0 := by
  have hB := fibreZero_analytic U W hW.analytic f
  obtain ⟨O,hpO,hOB⟩ := exists_fibreZero_neighborhood U W f p hp
  have hBW : fibreZeroLocus U W f ⊆ W := fun _ h => h.choose
  have he : fibreZeroLocus U W f = W :=
    ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset hB hW hBW O.isOpen
      ⟨p,hpW,hpO⟩ hOB
  exact hom_eq_zero_of_fibreZero U W f he.symm.subset

end Hironaka.HironakaNativeIrreducibleSupportContinuation
