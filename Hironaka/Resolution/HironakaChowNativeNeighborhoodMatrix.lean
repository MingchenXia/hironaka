import Hironaka.Resolution.HironakaChowNativeGeneratorNeighborhood
import Hironaka.Resolution.HironakaChowGenericFreePrincipal

/-! ONE actual original neighbourhood matrix, retaining the OLD generator
germs, OLD map and OLD full minor ideal, before ALL original points.
All free sheaves, scalar actions, stalks and germ maps are native.
Blueprint: `hironaka-g10-native-neighborhood-matrix.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hironaka.HironakaChowNativeNeighborhoodMatrix

open HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaChowNativeFiniteFreeStalk HironakaChowNativeFinitePresentationSpreading
  HironakaChowPureTransformBaseChange HironakaChowDeterminantalImage
  HironakaChowNativeGeneratorNeighborhood HironakaChowNativeFiniteTypeSpreading

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  {M : SheafOfModules.{0} (forgetRing R)}

/-- The ORIGINAL native free coordinate projection, with no replacement basis. -/
def freeCoordinateProjection (r : ℕ) (i : Fin r) :
    SheafOfModules.free (R := forgetRing R) (Fin r) ⟶ SheafOfModules.unit (forgetRing R) :=
  Sigma.π (fun _ : Fin r => SheafOfModules.unit (forgetRing R)) i

/-- The literal coordinate of the ORIGINAL finite-free stalk equivalence. -/
theorem freeStalkCoordinate_apply (r : ℕ) (x : X)
    (m : ↑(TopCat.Presheaf.stalk
      (SheafOfModules.free (R := forgetRing R) (Fin r)).val.presheaf x)) (i : Fin r) :
    finiteFreeStalkLinearEquiv R (Fin r) x m i =
      unitStalkLinearEquiv R x (stalkLinearMap (freeCoordinateProjection R r i).val x m) := rfl

/-- Every ORIGINAL free-section germ has its same original coordinate ring germ. -/
theorem freeStalkCoordinate_germ (r : ℕ) (U : Opens X) (x : X) (hxU : x ∈ U)
    (m : (SheafOfModules.free (R := forgetRing R) (Fin r)).val.obj (op U)) (i : Fin r) :
    finiteFreeStalkLinearEquiv R (Fin r) x
      (TopCat.Presheaf.germ
        (SheafOfModules.free (R := forgetRing R) (Fin r)).val.presheaf U x hxU m) i =
      TopCat.Presheaf.germ R.obj U x hxU
        ((freeCoordinateProjection R r i).val.app (op U) m) := by
  rw [freeStalkCoordinate_apply]
  erw [stalkLinearMap_germ,unitStalkLinearEquiv_germ]
  rfl

/-- The actual original coordinate map on the SAME original module stalk. -/
def coordinateStalkMap {r : ℕ} (U : Opens X)
    (F : M.over U ⟶ (SheafOfModules.free (R := forgetRing R) (Fin r)).over U)
    (x : X) (hxU : x ∈ U) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      (Fin r → ↑(TopCat.Presheaf.stalk R.obj x)) :=
  (finiteFreeStalkLinearEquiv R (Fin r) x).toLinearMap.comp
    (stalkLinearMapOfOver R U F x hxU)

/-- ONE actual matrix of original ring sections, defined before every point. -/
def sectionMatrix {r q : ℕ} (U : Opens X)
    (F : M.over U ⟶ (SheafOfModules.free (R := forgetRing R) (Fin r)).over U)
    (s : Fin q → M.val.obj (op U)) : Matrix (Fin r) (Fin q) ↑(R.obj.obj (op U)) :=
  fun i j => (freeCoordinateProjection R r i).val.app (op U)
    (F.val.app (op (Over.mk (𝟙 U))) (s j))

/-- The SAME actual section matrix has its actual original germ dictionary at EVERY point. -/
theorem sectionMatrix_germ {r q : ℕ} (U : Opens X)
    (F : M.over U ⟶ (SheafOfModules.free (R := forgetRing R) (Fin r)).over U)
    (s : Fin q → M.val.obj (op U)) (x : X) (hxU : x ∈ U) (i : Fin r) (j : Fin q) :
    TopCat.Presheaf.germ R.obj U x hxU (sectionMatrix R U F s i j) =
      coordinateStalkMap R U F x hxU
        (TopCat.Presheaf.germ M.val.presheaf U x hxU (s j)) i := by
  change _ = finiteFreeStalkLinearEquiv R (Fin r) x
    (stalkLinearMapOfOver R U F x hxU
      (TopCat.Presheaf.germ M.val.presheaf U x hxU (s j))) i
  erw [stalkLinearMapOfOver_germ_of_le R U F x hxU U hxU le_rfl]
  rw [freeStalkCoordinate_germ]
  rfl

private theorem sectionMatrix_image {r q : ℕ} (U : Opens X)
    (F : M.over U ⟶ (SheafOfModules.free (R := forgetRing R) (Fin r)).over U)
    (s : Fin q → M.val.obj (op U)) [Epi (freeOverMap R U s)] (x : X) (hxU : x ∈ U) :
    (coordinateStalkMap R U F x hxU).range =
      (Matrix.toLin' ((sectionMatrix R U F s).map (TopCat.Presheaf.germ R.obj U x hxU).hom)).range := by
  let e := finiteFreeStalkLinearEquiv R (Fin q) x
  let p := stalkLinearMapOfOver R U (freeOverMap R U s) x hxU
  let c := p.comp e.symm.toLinearMap
  have hc : Function.Surjective c :=
    (stalkLinearMapOfOver_surjective_of_epi R U (freeOverMap R U s) x hxU).comp e.symm.surjective
  have hm : (coordinateStalkMap R U F x hxU).comp c =
      Matrix.toLin' ((sectionMatrix R U F s).map (TopCat.Presheaf.germ R.obj U x hxU).hom) := by
    apply (Pi.basisFun ↑(TopCat.Presheaf.stalk R.obj x) (Fin q)).ext
    intro j
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,c,LinearEquiv.coe_toLinearMap]
    change coordinateStalkMap R U F x hxU (p (e.symm (Pi.single j 1))) = _
    have he : e.symm (Pi.single j 1) =
        stalkLinearMap (SheafOfModules.ιFree (R := forgetRing R) j).val x
          ((unitStalkLinearEquiv R x).symm 1) :=
      e.symm_apply_eq.mpr (finiteFreeStalkLinearEquiv_ι R (Fin q) x j 1).symm
    rw [he]
    change coordinateStalkMap R U F x hxU
      (stalkLinearMapOfOver R U (freeOverMap R U s) x hxU _) = _
    rw [freeOverMap_stalk_ι,one_smul]
    funext i
    rw [Matrix.toLin'_apply,Matrix.mulVec_single_one]
    exact (sectionMatrix_germ R U F s x hxU i j).symm
  rw [← hm,LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hc)]

/-- Ordinary native FP and the FIXED OLD spanning germs/map/matrix produce ONE actual
neighbourhood matrix before ALL points, retaining the literal OLD full minor ideal. -/
theorem exists_neighborhood_matrix [M.IsFinitePresentation] {r q : ℕ} (x : X)
    (v : Fin q → ↑(TopCat.Presheaf.stalk M.val.presheaf x))
    (hv : Submodule.span ↑(TopCat.Presheaf.stalk R.obj x) (Set.range v) = ⊤)
    (f : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      (Fin r → ↑(TopCat.Presheaf.stalk R.obj x)))
    (A : Matrix (Fin r) (Fin q) ↑(TopCat.Presheaf.stalk R.obj x))
    (hA : ∀ j, A.col j = f (v j)) :
    ∃ (U : Opens X) (hxU : x ∈ U) (s : Fin q → M.val.obj (op U))
      (F : M.over U ⟶ (SheafOfModules.free (R := forgetRing R) (Fin r)).over U)
      (B : Matrix (Fin r) (Fin q) ↑(R.obj.obj (op U))),
      (∀ j, TopCat.Presheaf.germ M.val.presheaf U x hxU (s j) = v j) ∧
      Epi (freeOverMap R U s) ∧ coordinateStalkMap R U F x hxU = f ∧
      B = sectionMatrix R U F s ∧ B.map (TopCat.Presheaf.germ R.obj U x hxU).hom = A ∧
      (∀ (y : X) (hyU : y ∈ U),
        (coordinateStalkMap R U F y hyU).range =
          (Matrix.toLin' (B.map (TopCat.Presheaf.germ R.obj U y hyU).hom)).range ∧
        minorIdeal (B.map (TopCat.Presheaf.germ R.obj U y hyU).hom) r =
          Ideal.map (TopCat.Presheaf.germ R.obj U y hyU).hom (minorIdeal B r)) ∧
      (minorIdeal B r).FG ∧
      Ideal.map (TopCat.Presheaf.germ R.obj U x hxU).hom (minorIdeal B r) = minorIdeal A r := by
  obtain ⟨Ug,hxUg,sg,hsg,hpg⟩ := exists_local_generators_with_original_germs R x v hv
  let e := finiteFreeStalkLinearEquiv R (Fin r) x
  let φ := e.symm.toLinearMap.comp f
  obtain ⟨Uf,hxUf,F₀,hF₀⟩ := exists_local_lift_of_isFinitePresentation
    (M := M) (N := SheafOfModules.free (R := forgetRing R) (Fin r)) R x φ
  let U := Ug ⊓ Uf
  have hUg : U ≤ Ug := inf_le_left
  have hUf : U ≤ Uf := inf_le_right
  have hxU : x ∈ U := ⟨hxUg,hxUf⟩
  let s (j : Fin q) := M.val.map (homOfLE hUg).op (sg j)
  let F := restrictOverHom R Uf U hUf F₀
  let B := sectionMatrix R U F s
  have hs (j : Fin q) : TopCat.Presheaf.germ M.val.presheaf U x hxU (s j) = v j :=
    (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hUg) x hxU (sg j)).trans (hsg j)
  have : Epi (freeOverMap R Ug sg) := hpg
  have : Epi ((SheafOfModules.overMap (forgetRing R) (homOfLE hUg)).map (freeOverMap R Ug sg)) :=
    Functor.map_epi _ _
  have hEpi : Epi (freeOverMap R U s) := by
    rw [freeOverMap_restrict]
    unfold restrictOverHom
    infer_instance
  have hcoord : coordinateStalkMap R U F x hxU = f := by
    apply LinearMap.ext
    intro m
    change e (stalkLinearMapOfOver R U (restrictOverHom R Uf U hUf F₀) x hxU m) = f m
    rw [stalkLinearMapOfOver_restrictOverHom,hF₀]
    exact e.apply_symm_apply (f m)
  have hB : B.map (TopCat.Presheaf.germ R.obj U x hxU).hom = A := by
    ext i j
    change TopCat.Presheaf.germ R.obj U x hxU (sectionMatrix R U F s i j) = A i j
    rw [sectionMatrix_germ,hs j,hcoord]
    exact (congrFun (hA j) i).symm
  have hfg : (minorIdeal B r).FG := Submodule.fg_span (Set.finite_range _)
  have hI : Ideal.map (TopCat.Presheaf.germ R.obj U x hxU).hom (minorIdeal B r) = minorIdeal A r := by
    rw [← minorIdeal_map,hB]
  refine ⟨U,hxU,s,F,B,hs,hEpi,hcoord,rfl,hB,?_,hfg,hI⟩
  intro y hyU
  exact ⟨sectionMatrix_image R U F s y hyU,minorIdeal_map B r _⟩

open HironakaSmoothCentreRealDomainActualSheafStalk

/-- ACTUAL smooth geometry derives the original stalk domain, native FP derives the
original finite module, and the OLD generic matrix is selected ONCE internally before
its actual neighbourhood matrix and ALL original point-image dictionaries. -/
theorem actual_smooth_exists_neighborhood_matrix
    {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (𝓜 : SheafOfModules.{0} (forgetRing (actualComplexStructureSheaf (n := n) Y)))
    [𝓜.IsFinitePresentation] (x : Y) :
    let R₀ := actualComplexStructureSheaf (n := n) Y
    let P := ↑(TopCat.Presheaf.stalk 𝓜.val.presheaf x)
    ∃ (d : actualComplexStructureStalk (n := n) x) (r : ℕ)
      (e : LocalizedModule (Submonoid.powers d) P ≃ₗ[Localization.Away d]
        (Fin r → Localization.Away d))
      (N q : ℕ) (v : Fin q → P)
      (f : P →ₗ[actualComplexStructureStalk (n := n) x]
        (Fin r → actualComplexStructureStalk (n := n) x))
      (A : Matrix (Fin r) (Fin q) (actualComplexStructureStalk (n := n) x))
      (E : (P ⧸ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) P))
        ≃ₗ[actualComplexStructureStalk (n := n) x] (Matrix.toLin' A).range) (K : ℕ)
      (U : Opens Y) (hxU : x ∈ U) (s : Fin q → 𝓜.val.obj (op U))
      (F : 𝓜.over U ⟶ (SheafOfModules.free (R := forgetRing R₀) (Fin r)).over U)
      (B : Matrix (Fin r) (Fin q) ↑(R₀.obj.obj (op U))),
      d ≠ 0 ∧ Submodule.span (actualComplexStructureStalk (n := n) x) (Set.range v) = ⊤ ∧
      (∀ m i, algebraMap (actualComplexStructureStalk (n := n) x) (Localization.Away d) (f m i) =
        d ^ N • e (LocalizedModule.mkLinearMap (Submonoid.powers d) P m) i) ∧
      (∀ j, A.col j = f (v j)) ∧ f.range = (Matrix.toLin' A).range ∧
      LinearMap.ker f = LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers d) P) ∧
      (∀ m, (E (Submodule.Quotient.mk m)).val = f m) ∧
      (minorIdeal A r).FG ∧ d ^ K ∈ minorIdeal A r ∧ IsRegular (d ^ K) ∧
      (∀ j, TopCat.Presheaf.germ 𝓜.val.presheaf U x hxU (s j) = v j) ∧
      Epi (freeOverMap R₀ U s) ∧ coordinateStalkMap R₀ U F x hxU = f ∧
      B = sectionMatrix R₀ U F s ∧ B.map (TopCat.Presheaf.germ R₀.obj U x hxU).hom = A ∧
      (∀ (y : Y) (hyU : y ∈ U),
        (coordinateStalkMap R₀ U F y hyU).range =
          (Matrix.toLin' (B.map (TopCat.Presheaf.germ R₀.obj U y hyU).hom)).range ∧
        minorIdeal (B.map (TopCat.Presheaf.germ R₀.obj U y hyU).hom) r =
          Ideal.map (TopCat.Presheaf.germ R₀.obj U y hyU).hom (minorIdeal B r)) ∧
      (minorIdeal B r).FG ∧
      Ideal.map (TopCat.Presheaf.germ R₀.obj U x hxU).hom (minorIdeal B r) = minorIdeal A r := by
  dsimp only
  let R₀ := actualComplexStructureSheaf (n := n) Y
  let P := ↑(TopCat.Presheaf.stalk 𝓜.val.presheaf x)
  let : IsDomain (actualComplexStructureStalk (n := n) x) :=
    MulEquiv.isDomain _ (actualStalkChartEquiv (n := n) x).toMulEquiv
  have : Module.Finite (actualComplexStructureStalk (n := n) x) P :=
    moduleFinite_stalk_of_isFiniteType (M := 𝓜) R₀ x
  obtain ⟨d,r,e,hd⟩ := HironakaChowGenericFreePrincipal.exists_generic_free_principal
    (R := actualComplexStructureStalk (n := n) x) (M := P)
  obtain ⟨N,q,v,f,A,E,K,hv,hclear,hA,hrange,hker,hE,hfg,hK,hreg⟩ :=
    HironakaChowPureTransformMinorDensity.exists_pure_transform_matrix_with_regular_minor_power
      d (IsRegular.of_ne_zero' hd) r e
  obtain ⟨U,hxU,s,F,B,hs,hEpi,hcoord,hB,hBx,hall,hfgB,hI⟩ :=
    exists_neighborhood_matrix (M := 𝓜) R₀ x v hv f A hA
  exact ⟨d,r,e,N,q,v,f,A,E,K,U,hxU,s,F,B,hd,hv,hclear,hA,hrange,hker,hE,hfg,hK,hreg,
    hs,hEpi,hcoord,hB,hBx,hall,hfgB,hI⟩

end Hironaka.HironakaChowNativeNeighborhoodMatrix
