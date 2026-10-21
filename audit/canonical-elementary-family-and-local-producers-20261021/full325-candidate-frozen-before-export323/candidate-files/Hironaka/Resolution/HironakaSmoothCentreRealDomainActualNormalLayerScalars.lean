/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalLayerStalk
import Mathlib.Algebra.Category.ModuleCat.Stalk
/-! Independent actual normal-layer stalk actions and original nearby freeness.
Complete four-node Mathematics.tex precedes code. Real section multiplication
defines the colimit action; whole centre annihilation precedes quotient descent.
No action is transported through the subsequent whole-layer equivalence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerScalars
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk HironakaSmoothCentreRealDomainOriginalCentreOpen
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual section multiplication makes the SAME layer presheaf a genuine module presheaf. -/
def actualNormalLayerModulePresheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    PresheafOfModules ((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat) := by
  letI (U : (Opens M)ᵒᵖ) :
      Module (((actualComplexStructureSheaf (n := n) M).presheaf ⋙ forget₂ CommRingCat RingCat).obj U)
        ((actualNormalLayerPresheaf A C q).obj U) := by
    change Module (actualComplexSection (n := n) (unop U)) (actualNormalLayerSection A C q (unop U))
    infer_instance
  apply PresheafOfModules.ofPresheaf (actualNormalLayerPresheaf A C q)
  intro U V i r s
  change actualComplexSection (n := n) (unop U) at r
  change actualNormalLayerSection A C q (unop U) at s
  apply Subtype.ext
  change actualRemainderQuotientRestrict A C (q+1) (unop V) (unop U) _
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) (unop U)) r *
        (show actualRemainderSectionQuotient A C (q+1) (unop U) from s.val)) =
    Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) (unop V))
      ((actualComplexStructureSheaf (n := n) M).presheaf.map i r) *
        actualRemainderQuotientRestrict A C (q+1) (unop V) (unop U) _
          (show actualRemainderSectionQuotient A C (q+1) (unop U) from s.val)
  rw [map_mul,actualRemainderQuotientRestrict_mk]
  rfl

/-- The independently defined module presheaf retains the EXACT old additive presheaf. -/
theorem actualNormalLayerModulePresheaf_presheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    (actualNormalLayerModulePresheaf A C q).presheaf = actualNormalLayerPresheaf A C q := rfl

/-- The actual filtered-colimit module action, independently of every whole-layer equivalence. -/
instance actualNormalLayerStalkModule (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module (actualComplexStructureStalk (n := n) y) (actualNormalLayerStalk A C q y) := by
  change Module (((actualComplexStructureSheaf (n := n) M).presheaf.stalk y).carrier)
    ((TopCat.Presheaf.stalk (actualNormalLayerModulePresheaf A C q).presheaf y).carrier)
  exact (actualNormalLayerModulePresheaf A C q).instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier y

/-- EVERY real section product yields the actual independent stalk scalar-product formula. -/
theorem actualNormalLayerStalk_germ_smul (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (r : actualComplexSection (n := n) U)
    (s : actualNormalLayerSection A C q U) :
    (actualNormalLayerPresheaf A C q).germ U y hy (r • s) =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy r •
        (actualNormalLayerPresheaf A C q).germ U y hy s :=
  (actualNormalLayerModulePresheaf A C q).germ_smul y U hy r s

/-- Genuine actual quotient-germ multiplication proves the section-layer scalar formula on EVERY layer element. -/
theorem actualNormalLayerSectionGermHom_smul (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (r : actualComplexSection (n := n) U)
    (s : actualNormalLayerSection A C q U) :
    actualNormalLayerSectionGermHom A C q U y hy (r • s) =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy r •
        actualNormalLayerSectionGermHom A C q U y hy s := by
  apply Subtype.ext
  change actualRemainderQuotientSectionGermHom A C (q+1) U y hy
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) U) r *
        (show actualRemainderSectionQuotient A C (q+1) U from s.val)) =
    Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy r) *
        actualRemainderQuotientSectionGermHom A C (q+1) U y hy
          (show actualRemainderSectionQuotient A C (q+1) U from s.val)
  rw [map_mul,actualRemainderQuotientSectionGermHom_mk]

/-- ALL genuine ring-stalk scalars and layer-colimit elements obey the actual whole map's scalar law. -/
theorem actualNormalLayerStalkToWholeHom_smul (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualNormalLayerStalk A C q y) :
    actualNormalLayerStalkToWholeHom A C q y (r • v) = r • actualNormalLayerStalkToWholeHom A C q y v := by
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let L := actualNormalLayerPresheaf A C q
  obtain ⟨V,hyV,s,hs⟩ := L.exists_germ_eq v
  obtain ⟨U,hUV,hyU,t,ht⟩ := F.exists_le_germ_eq r hyV
  change actualNormalLayerSection A C q V at s
  change actualComplexSection (n := n) U at t
  let su := actualNormalLayerRestrict A C q U V hUV s
  have hsv : L.germ U y hyU su = v := (L.germ_res_apply (homOfLE hUV) y hyU s).trans hs
  rw [← ht,← hsv,← actualNormalLayerStalk_germ_smul A C q U y hyU t su,
    actualNormalLayerStalkToWholeHom_germ,actualNormalLayerStalkToWholeHom_germ]
  exact actualNormalLayerSectionGermHom_smul A C q U y hyU t su

/-- The actual whole map is linear for the independently constructed genuine colimit module action. -/
def actualNormalLayerStalkToWholeLinear (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y →ₗ[actualComplexStructureStalk (n := n) y] actualWholeNormalLayer A C q y where
  toFun := actualNormalLayerStalkToWholeHom A C q y
  map_add' := (actualNormalLayerStalkToWholeHom A C q y).map_add
  map_smul' := actualNormalLayerStalkToWholeHom_smul A C q y

/-- ONLY original coherence internally supplies the whole ambient-linear equivalence. -/
def actualNormalLayerStalkWholeLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y] actualWholeNormalLayer A C q y :=
  LinearEquiv.ofBijective (actualNormalLayerStalkToWholeLinear A C q y)
    ⟨actualNormalLayerStalkToWholeHom_injective A hA C q y,actualNormalLayerStalkToWholeHom_surjective A C q y⟩

/-- The ENTIRE genuine centre ideal annihilates the independent actual colimit action, from real section powers. -/
theorem actualNormalLayerStalk_isTorsionByCentre (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module.IsTorsionBySet (actualComplexStructureStalk (n := n) y) (actualNormalLayerStalk A C q y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) := by
  intro v r
  have hr : r.val ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) y := by
    rw [actualCentreIdealSectionGermImage_eq_whole (n := n) C y]
    exact r.property
  obtain ⟨U,hyU,t,ht⟩ := hr
  let L := actualNormalLayerPresheaf A C q
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  obtain ⟨V,hyV,s,hs⟩ := L.exists_germ_eq v
  change actualNormalLayerSection A C q V at s
  let W : Opens M := U ⊓ V
  have hyW : y ∈ W := ⟨hyU,hyV⟩
  let tw := actualIdealSectionRestrict (vanishingIdeal (n := n) C) W U inf_le_left t
  let sw := actualNormalLayerRestrict A C q W V inf_le_right s
  have htw : F.germ W y hyW tw.val = r.val :=
    (F.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) y hyW t.val).trans ht
  have hsw : L.germ W y hyW sw = v :=
    (L.germ_res_apply (homOfLE (show W ≤ V from inf_le_right)) y hyW s).trans hs
  have hann : tw.val • sw = 0 :=
    idealPowerLayer_isTorsionBySet (actualComplexSection (n := n) W) (actualSectionIdeal A W)
      (actualSectionIdeal (vanishingIdeal (n := n) C) W) q (x := sw) (a := tw)
  rw [← htw,← hsw,← actualNormalLayerStalk_germ_smul A C q W y hyW tw.val sw,hann]
  exact (L.germ W y hyW).hom.map_zero

/-- The actual centre quotient action descends from internally proved annihilation, BEFORE all comparisons. -/
@[instance_reducible] def actualNormalLayerStalkCentreModule (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Module (actualComplexStructureStalk (n := n) y ⧸ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (actualNormalLayerStalk A C q y) :=
  (actualNormalLayerStalk_isTorsionByCentre A C q y).module

/-- EVERY original ambient scalar representative acts by its SAME independent actual colimit product. -/
theorem actualNormalLayerStalkCentre_mk_smul (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M)
    (r : actualComplexStructureStalk (n := n) y) (v : actualNormalLayerStalk A C q y) :
    letI := actualNormalLayerStalkCentreModule A C q y
    Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) r • v = r • v := rfl

/-- The SAME actual whole map is centre-linear for BOTH independently descended canonical actions. -/
def actualNormalLayerStalkToWholeCentreLinear (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    letI := actualNormalLayerStalkCentreModule A C q y
    letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
    actualNormalLayerStalk A C q y →ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualWholeNormalLayer A C q y := by
  letI := actualNormalLayerStalkCentreModule A C q y
  letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
  refine { toFun := actualNormalLayerStalkToWholeHom A C q y
           map_add' := (actualNormalLayerStalkToWholeHom A C q y).map_add
           map_smul' := ?_ }
  intro r v
  obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective r
  exact actualNormalLayerStalkToWholeHom_smul A C q y s v

/-- ONLY original coherence internally yields the whole centre-linear equivalence with canonical original scalars. -/
def actualNormalLayerStalkWholeCentreLinearEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    letI := actualNormalLayerStalkCentreModule A C q y
    letI := idealPowerLayerCentreModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
    actualNormalLayerStalk A C q y ≃ₗ[actualComplexStructureStalk (n := n) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y] actualWholeNormalLayer A C q y :=
  LinearEquiv.ofBijective (actualNormalLayerStalkToWholeCentreLinear A C q y)
    ⟨actualNormalLayerStalkToWholeHom_injective A hA C q y,actualNormalLayerStalkToWholeHom_surjective A C q y⟩

private theorem actual_module_flat_of_free {R L : Type*} [CommSemiring R] [AddCommMonoid L]
    [Module R L] (hf : Module.Free R L) : Module.Flat R L := by
  let : Module.Free R L := hf
  infer_instance

/-- Original regular/coherent/containment inputs internally give ONE accumulating true open with ALL actual layer-colimit degrees finite/free/flat. -/
theorem exists_original_regular_all_actual_layer_colimit_degrees_free_open
    {d t : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O) (q : ℕ),
        letI := actualNormalLayerStalkCentreModule A C q y
        Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerStalk A C q y) ∧
        Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerStalk A C q y) ∧
        Module.Flat (actualComplexStructureStalk (n := d+t) y ⧸
          actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerStalk A C q y) := by
  obtain ⟨O,hO,hcl,hfree⟩ := exists_original_regular_all_relative_degrees_free_actual_sheaf_stalk_open C x hreg A hA hAC
  refine ⟨O,hO,hcl,?_⟩
  intro y hyCO q
  let := actualNormalLayerStalkCentreModule A C q y
  let := idealPowerLayerCentreModule (actualComplexStructureStalk (n := d+t) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) q
  let := ((hfree y hyCO).2 q).1
  let := ((hfree y hyCO).2 q).2.1
  let e := actualNormalLayerStalkWholeCentreLinearEquiv A hA C q y
  have hf : Module.Free (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerStalk A C q y) :=
    Module.Free.of_equiv e.symm
  have hfin : Module.Finite (actualComplexStructureStalk (n := d+t) y ⧸
      actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) (actualNormalLayerStalk A C q y) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact ⟨hfin,hf,actual_module_flat_of_free hf⟩

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerScalars
