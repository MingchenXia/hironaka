/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerScalars
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Sheafify
/-! Genuine actual normal-layer module sheaves and their original whole stalks.
Complete four-node Mathematics.tex precedes code. Module sheafification and
independent sheaf-stalk actions precede all whole original layer equivalences. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerSheaf
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk HironakaSmoothCentreRealDomainActualNormalLayerScalars
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The LITERAL original complex structure sheaf viewed as a genuine sheaf of rings. -/
abbrev actualComplexStructureRingSheaf (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of M)) (forget₂ CommRingCat RingCat)).obj
    (actualComplexStructureSheaf (n := n) M)

/-- Genuine MODULE sheafification of the independent original section-layer module presheaf. -/
def actualNormalLayerModuleSheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    SheafOfModules (actualComplexStructureRingSheaf n M) :=
  (PresheafOfModules.sheafification (R := actualComplexStructureRingSheaf n M)
    (𝟙 (actualComplexStructureRingSheaf n M).obj)).obj (actualNormalLayerModulePresheaf A C q)

/-- The actual sheaf's genuine underlying module presheaf, retaining independent sheafified section actions. -/
abbrev actualNormalLayerSheafModulePresheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :=
  (SheafOfModules.forget (actualComplexStructureRingSheaf n M)).obj (actualNormalLayerModuleSheaf A C q)

/-- The true underlying additive presheaf of the genuine actual module sheaf. -/
abbrev actualNormalLayerSheafPresheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    (TopCat.of M).Presheaf AddCommGrpCat :=
  (actualNormalLayerSheafModulePresheaf A C q).presheaf

/-- The literal neighbourhood colimit stalk of the genuine actual module sheaf. -/
abbrev actualNormalLayerSheafStalk (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) : Type :=
  ((actualNormalLayerSheafPresheaf A C q).stalk y).carrier

/-- The actual module sheaf has its independently constructed genuine filtered-colimit ambient action. -/
instance actualNormalLayerSheafStalkModule (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module (actualComplexStructureStalk (n := n) y) (actualNormalLayerSheafStalk A C q y) :=
  (actualNormalLayerSheafModulePresheaf A C q).instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier y

/-- The SAME actual additive sheafification unit, independently of all whole original stalk maps. -/
abbrev actualNormalLayerSheafUnit (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    actualNormalLayerPresheaf A C q ⟶ actualNormalLayerSheafPresheaf A C q :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M)) (actualNormalLayerPresheaf A C q)

/-- Actual neighbourhood colimits supply the genuine unit stalk map. -/
def actualNormalLayerSheafUnitStalkHom (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y →+ actualNormalLayerSheafStalk A C q y := by
  let f : (actualNormalLayerPresheaf A C q).stalk y ⟶ (actualNormalLayerSheafPresheaf A C q).stalk y :=
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) AddCommGrpCat y).map (actualNormalLayerSheafUnit A C q)
  exact f.hom

/-- The actual unit stalk map is intrinsically bijective, by genuine sheafification stalk invariance. -/
theorem actualNormalLayerSheafUnitStalkHom_bijective (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Function.Bijective (actualNormalLayerSheafUnitStalkHom A C q y) := by
  have h := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (X := TopCat.of M) y
    AddCommGrpCat (actualNormalLayerPresheaf A C q)
  exact (ConcreteCategory.isIso_iff_bijective ((TopCat.Presheaf.stalkFunctor (X := TopCat.of M)
    AddCommGrpCat y).map (actualNormalLayerSheafUnit A C q))).mp h

/-- Actual sheafified section modules inherit their genuine action before every stalk dictionary. -/
instance actualNormalLayerSheafSectionModule (A : GermIdeal n M) (C : Set M) (q : ℕ) (U : Opens M) :
    Module (actualComplexSection (n := n) U) ((actualNormalLayerSheafPresheaf A C q).obj (op U)) := by
  change Module ((actualComplexStructureRingSheaf n M).obj.obj (op U))
    ((actualNormalLayerSheafModulePresheaf A C q).presheaf.obj (op U))
  infer_instance

/-- The real MODULE sheafification unit is section-linear for the independently inherited actions. -/
theorem actualNormalLayerSheafUnit_section_smul (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (r : actualComplexSection (n := n) U) (s : actualNormalLayerSection A C q U) :
    (actualNormalLayerSheafUnit A C q).app (op U) (r • s) =
      r • (actualNormalLayerSheafUnit A C q).app (op U) s := by
  let R := actualComplexStructureRingSheaf n M
  let P := actualNormalLayerModulePresheaf A C q
  let η := (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P
  exact (η.app (op U)).hom.map_smul (show R.obj.obj (op U) from r) s

/-- EVERY actual sheaf section product germ retains the independent genuine sheaf-stalk action. -/
theorem actualNormalLayerSheafStalk_germ_smul (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (r : actualComplexSection (n := n) U)
    (s : (actualNormalLayerSheafPresheaf A C q).obj (op U)) :
    (actualNormalLayerSheafPresheaf A C q).germ U y hy (r • s) =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy r •
        (actualNormalLayerSheafPresheaf A C q).germ U y hy s :=
  (actualNormalLayerSheafModulePresheaf A C q).germ_smul y U hy r s

/-- EVERY original section germ maps to the SAME actual unit section image germ. -/
theorem actualNormalLayerSheafUnitStalkHom_germ (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalLayerSection A C q U) :
    actualNormalLayerSheafUnitStalkHom A C q y ((actualNormalLayerPresheaf A C q).germ U y hy s) =
      (actualNormalLayerSheafPresheaf A C q).germ U y hy ((actualNormalLayerSheafUnit A C q).app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy (actualNormalLayerSheafUnit A C q) s

/-- True common-open section products prove linearity for ALL actual ambient stalk scalars. -/
theorem actualNormalLayerSheafUnitStalkHom_smul (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualNormalLayerStalk A C q y) :
    actualNormalLayerSheafUnitStalkHom A C q y (r • v) = r • actualNormalLayerSheafUnitStalkHom A C q y v := by
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let L := actualNormalLayerPresheaf A C q
  obtain ⟨V,hyV,s,hs⟩ := L.exists_germ_eq v
  obtain ⟨U,hUV,hyU,t,ht⟩ := F.exists_le_germ_eq r hyV
  change actualNormalLayerSection A C q V at s
  change actualComplexSection (n := n) U at t
  let su := actualNormalLayerRestrict A C q U V hUV s
  have hsu : L.germ U y hyU su = v := (L.germ_res_apply (homOfLE hUV) y hyU s).trans hs
  rw [← ht,← hsu,← actualNormalLayerStalk_germ_smul A C q U y hyU t su,
    actualNormalLayerSheafUnitStalkHom_germ,actualNormalLayerSheafUnitStalkHom_germ,
    actualNormalLayerSheafUnit_section_smul,actualNormalLayerSheafStalk_germ_smul]

/-- The genuine unit stalk map is linear for BOTH independently constructed actual colimit actions. -/
def actualNormalLayerSheafUnitStalkLinear (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y →ₗ[actualComplexStructureStalk (n := n) y] actualNormalLayerSheafStalk A C q y where
  toFun := actualNormalLayerSheafUnitStalkHom A C q y
  map_add' := (actualNormalLayerSheafUnitStalkHom A C q y).map_add
  map_smul' := actualNormalLayerSheafUnitStalkHom_smul A C q y

/-- Intrinsic unit bijectivity upgrades the SAME actual linear map, without a caller sheaf or equivalence. -/
def actualNormalLayerSheafUnitStalkLinearEquiv (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y] actualNormalLayerSheafStalk A C q y :=
  LinearEquiv.ofBijective (actualNormalLayerSheafUnitStalkLinear A C q y)
    (actualNormalLayerSheafUnitStalkHom_bijective A C q y)

/-- Original coherence INTERNALLY gives the whole original ambient-linear actual SHEAF-stalk equivalence. -/
def actualNormalLayerSheafStalkWholeLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerSheafStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y] actualWholeNormalLayer A C q y :=
  (actualNormalLayerSheafUnitStalkLinearEquiv A C q y).symm.trans
    (actualNormalLayerStalkWholeLinearEquiv A hA C q y)

/-- ENTIRE original centre annihilation follows from the true independent sheaf-stalk action and actual unit surjectivity. -/
theorem actualNormalLayerSheafStalk_isTorsionByCentre (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module.IsTorsionBySet (actualComplexStructureStalk (n := n) y) (actualNormalLayerSheafStalk A C q y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) := by
  intro v r
  obtain ⟨s,rfl⟩ := (actualNormalLayerSheafUnitStalkHom_bijective A C q y).2 v
  rw [← actualNormalLayerSheafUnitStalkHom_smul]
  have h := actualNormalLayerStalk_isTorsionByCentre A C q y (x := s) (a := r)
  rw [h]
  exact (actualNormalLayerSheafUnitStalkHom A C q y).map_zero

/-- Genuine quotient scalar descent on the actual sheaf stalk, BEFORE the whole original comparison. -/
@[instance_reducible] def actualNormalLayerSheafStalkCentreModule (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (actualNormalLayerSheafStalk A C q y) :=
  (actualNormalLayerSheafStalk_isTorsionByCentre A C q y).module

/-- Every original scalar representative acts by its SAME independent actual sheaf-stalk ambient product. -/
theorem actualNormalLayerSheafStalkCentre_mk_smul (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualNormalLayerSheafStalk A C q y) :
    letI := actualNormalLayerSheafStalkCentreModule A C q y
    Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r • v = r • v := rfl

/-- The canonical unit is centre-linear for BOTH independently descended actual actions. -/
def actualNormalLayerSheafUnitStalkCentreLinearEquiv (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    letI := actualNormalLayerStalkCentreModule A C q y
    letI := actualNormalLayerSheafStalkCentreModule A C q y
    actualNormalLayerStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualNormalLayerSheafStalk A C q y := by
  letI := actualNormalLayerStalkCentreModule A C q y
  letI := actualNormalLayerSheafStalkCentreModule A C q y
  let f : actualNormalLayerStalk A C q y →ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualNormalLayerSheafStalk A C q y := {
    toFun := actualNormalLayerSheafUnitStalkHom A C q y
    map_add' := (actualNormalLayerSheafUnitStalkHom A C q y).map_add
    map_smul' := by
      intro r v
      obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective r
      exact actualNormalLayerSheafUnitStalkHom_smul A C q y s v }
  exact LinearEquiv.ofBijective f (actualNormalLayerSheafUnitStalkHom_bijective A C q y)

/-- Original coherence internally supplies the genuine whole actual SHEAF-stalk centre-linear comparison. -/
def actualNormalLayerSheafStalkWholeCentreLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    letI := actualNormalLayerSheafStalkCentreModule A C q y
    letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
    actualNormalLayerSheafStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualWholeNormalLayer A C q y := by
  letI := actualNormalLayerStalkCentreModule A C q y
  letI := actualNormalLayerSheafStalkCentreModule A C q y
  letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
  exact (actualNormalLayerSheafUnitStalkCentreLinearEquiv A C q y).symm.trans
    (actualNormalLayerStalkWholeCentreLinearEquiv A hA C q y)

/-- EVERY original unit-section germ retains its literal ENTIRE original layer representative. -/
theorem actualNormalLayerSheafStalkWholeCentreLinearEquiv_germ_unit (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalLayerSection A C q U) :
    letI := actualNormalLayerSheafStalkCentreModule A C q y
    letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
    actualNormalLayerSheafStalkWholeCentreLinearEquiv A hA C q y
      ((actualNormalLayerSheafPresheaf A C q).germ U y hy ((actualNormalLayerSheafUnit A C q).app (op U) s)) =
        actualNormalLayerSectionGermHom A C q U y hy s := by
  let := actualNormalLayerStalkCentreModule A C q y
  let := actualNormalLayerSheafStalkCentreModule A C q y
  let := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
  rw [← actualNormalLayerSheafUnitStalkHom_germ]
  change actualNormalLayerStalkWholeCentreLinearEquiv A hA C q y
    ((actualNormalLayerSheafUnitStalkCentreLinearEquiv A C q y).symm
      ((actualNormalLayerSheafUnitStalkCentreLinearEquiv A C q y)
        ((actualNormalLayerPresheaf A C q).germ U y hy s))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact actualNormalLayerStalkToWholeHom_germ A C q U y hy s

/-- EVERY literal original power-section class retains its actual original germ class in the genuine SHEAF-stalk comparison. -/
theorem actualNormalLayerSheafStalkWholeCentreLinearEquiv_power_class (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    letI := actualNormalLayerSheafStalkCentreModule A C q y
    letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
    actualNormalLayerSheafStalkWholeCentreLinearEquiv A hA C q y
      ((actualNormalLayerSheafPresheaf A C q).germ U y hy
        ((actualNormalLayerSheafUnit A C q).app (op U)
          (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩))) =
      idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
          ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
            actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩ := by
  rw [actualNormalLayerSheafStalkWholeCentreLinearEquiv_germ_unit,actualNormalLayerSectionGermHom_class]

private theorem actual_module_flat_of_free {R L : Type*} [CommSemiring R] [AddCommMonoid L]
    [Module R L] (hf : Module.Free R L) : Module.Flat R L := by
  let : Module.Free R L := hf
  infer_instance

/-- ONLY original regular/coherent/containment inputs give ONE accumulating original open with ALL genuine actual layer SHEAF-stalk degrees finite/free/flat. -/
theorem exists_original_regular_all_actual_layer_sheaf_degrees_free_open
    {d t : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O) (q : ℕ),
        letI := actualNormalLayerSheafStalkCentreModule A C q y
        Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) ∧
        Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) ∧
        Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) := by
  obtain ⟨O,hO,hcl,hfree⟩ := exists_original_regular_all_actual_layer_colimit_degrees_free_open C x hreg A hA hAC
  refine ⟨O,hO,hcl,?_⟩
  intro y hyCO q
  let := actualNormalLayerStalkCentreModule A C q y
  let := actualNormalLayerSheafStalkCentreModule A C q y
  let := (hfree y hyCO q).1
  let := (hfree y hyCO q).2.1
  let e := actualNormalLayerSheafUnitStalkCentreLinearEquiv A C q y
  have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) :=
    Module.Free.of_equiv e
  have hfin : Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerSheafStalk A C q y) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact ⟨hfin,hf,actual_module_flat_of_free hf⟩

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerSheaf
