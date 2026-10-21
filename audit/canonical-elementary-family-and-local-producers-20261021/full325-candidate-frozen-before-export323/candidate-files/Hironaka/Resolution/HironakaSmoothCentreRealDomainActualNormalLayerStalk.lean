/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
/-! Literal image layers on actual original opens and their entire colimit stalks.
Complete three-node Mathematics.tex precedes code. Actual quotient image
operations precede all stalk comparisons; every power class is retained. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The LITERAL actual power image in the real next-remainder section quotient. -/
abbrev actualNormalLayerSection (A : GermIdeal n M) (C : Set M) (q : ℕ) (U : Opens M) : Type :=
  idealPowerLayer (actualComplexSection (n := n) U) (actualSectionIdeal A U)
    (actualSectionIdeal (vanishingIdeal (n := n) C) U) q

/-- The ENTIRE original actual stalk layer, using all original ideal members. -/
abbrev actualWholeNormalLayer (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) : Type :=
  idealPowerLayer (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
    (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q

/-- Real quotient restriction preserves the entire literal image layer by actual power restriction. -/
def actualNormalLayerRestrict (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) :
    actualNormalLayerSection A C q V →+ actualNormalLayerSection A C q U where
  toFun x := ⟨actualRemainderQuotientRestrict A C (q+1) U V hUV x.val, by
    obtain ⟨g,hg,he⟩ := x.property
    refine ⟨(actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op g,
      actualCentrePowerSectionIdeal_restrict (n := n) C q U V hUV g hg,?_⟩
    change Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) U) _ = _
    rw [← actualRemainderQuotientRestrict_mk A C (q+1) U V hUV g]
    exact congrArg (actualRemainderQuotientRestrict A C (q+1) U V hUV) he⟩
  map_zero' := by
    apply Subtype.ext
    exact (actualRemainderQuotientRestrict A C (q+1) U V hUV).map_zero
  map_add' x z := by
    apply Subtype.ext
    exact (actualRemainderQuotientRestrict A C (q+1) U V hUV).map_add x.val z.val

/-- EVERY actual power-section representative has the SAME actual restricted layer class. -/
theorem actualNormalLayerRestrict_class (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) (s : actualCentrePowerSectionIdeal (n := n) C q V) :
    actualNormalLayerRestrict A C q U V hUV
      (idealPowerLayerMap (actualComplexSection (n := n) V) (actualSectionIdeal A V)
        (actualSectionIdeal (vanishingIdeal (n := n) C) V) q ⟨s.val,s.property⟩) =
      idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) q
          ⟨(actualCentrePowerSectionRestrict (n := n) C q U V hUV s).val,
            (actualCentrePowerSectionRestrict (n := n) C q U V hUV s).property⟩ := by
  apply Subtype.ext
  rfl

/-- The genuine original-open image-layer additive presheaf, BEFORE all whole stalk dictionaries. -/
def actualNormalLayerPresheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    (TopCat.of M).Presheaf AddCommGrpCat where
  obj U := AddCommGrpCat.of (actualNormalLayerSection A C q (unop U))
  map i := AddCommGrpCat.ofHom (actualNormalLayerRestrict A C q _ _ (leOfHom i.unop))
  map_id := by
    intro U
    ext s
    obtain ⟨g,hg,he⟩ := s.property
    change actualRemainderQuotientRestrict A C (q+1) (unop U) (unop U) _ s.val = s.val
    rw [← he]
    rfl
  map_comp := by
    intro U V W i j
    ext s
    obtain ⟨g,hg,he⟩ := s.property
    change actualRemainderQuotientRestrict A C (q+1) (unop W) (unop U) _ s.val =
      actualRemainderQuotientRestrict A C (q+1) (unop W) (unop V) _
        (actualRemainderQuotientRestrict A C (q+1) (unop V) (unop U) _ s.val)
    rw [← he]
    rfl

/-- The LITERAL neighbourhood colimit stalk of actual original image-layer sections. -/
abbrev actualNormalLayerStalk (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) : Type :=
  ((actualNormalLayerPresheaf A C q).stalk y).carrier

/-- The true section quotient germ maps ALL actual power images into the whole original layer. -/
def actualNormalLayerSectionGermHom (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) :
    actualNormalLayerSection A C q U →+ actualWholeNormalLayer A C q y where
  toFun x := ⟨actualRemainderQuotientSectionGermHom A C (q+1) U y hy x.val, by
    obtain ⟨g,hg,he⟩ := x.property
    refine ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy g,
      actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy g hg,?_⟩
    change Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y) _ = _
    rw [← actualRemainderQuotientSectionGermHom_mk A C (q+1) U y hy g]
    exact congrArg (actualRemainderQuotientSectionGermHom A C (q+1) U y hy) he⟩
  map_zero' := by
    apply Subtype.ext
    exact (actualRemainderQuotientSectionGermHom A C (q+1) U y hy).map_zero
  map_add' x z := by
    apply Subtype.ext
    exact (actualRemainderQuotientSectionGermHom A C (q+1) U y hy).map_add x.val z.val

/-- EVERY genuine actual power class maps to its SAME actual original power germ class. -/
theorem actualNormalLayerSectionGermHom_class (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualNormalLayerSectionGermHom A C q U y hy
      (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩) =
      idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
          ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
            actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩ := by
  apply Subtype.ext
  rfl

/-- Actual original layer germs form a genuine neighbourhood cocone with the whole original layer. -/
def actualNormalLayerGermCocone (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualNormalLayerPresheaf A C q) where
  pt := AddCommGrpCat.of (actualWholeNormalLayer A C q y)
  ι := {
    app := fun U => AddCommGrpCat.ofHom (actualNormalLayerSectionGermHom A C q (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext x
      apply Subtype.ext
      change actualRemainderQuotientSectionGermHom A C (q+1) (unop V).val y (unop V).property
          (actualRemainderQuotientRestrict A C (q+1) (unop V).val (unop U).val (leOfHom i.unop) x.val) =
        actualRemainderQuotientSectionGermHom A C (q+1) (unop U).val y (unop U).property x.val
      obtain ⟨s,hs⟩ := Ideal.Quotient.mk_surjective x.val
      rw [← hs]
      change Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop V).val y (unop V).property
            ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE (leOfHom i.unop)).op s)) =
        Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop U).val y (unop U).property s)
      exact congrArg (Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y))
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
          (homOfLE (leOfHom i.unop)) y (unop V).property s) }

/-- The actual additive colimit supplies the whole original layer map INTERNALLY. -/
def actualNormalLayerStalkToWholeHom (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y →+ actualWholeNormalLayer A C q y :=
  (colimit.desc _ (actualNormalLayerGermCocone A C q y)).hom

/-- EVERY actual section image germ retains its SAME whole original quotient image. -/
theorem actualNormalLayerStalkToWholeHom_germ (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalLayerSection A C q U) :
    actualNormalLayerStalkToWholeHom A C q y ((actualNormalLayerPresheaf A C q).germ U y hy s) =
      actualNormalLayerSectionGermHom A C q U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualNormalLayerPresheaf A C q
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualNormalLayerGermCocone A C q y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- ALL original power members have true power-section representatives, supplying whole layer surjectivity. -/
theorem actualNormalLayerStalkToWholeHom_surjective (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Function.Surjective (actualNormalLayerStalkToWholeHom A C q y) := by
  intro x
  obtain ⟨g,rfl⟩ := idealPowerLayerMap_surjective (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q x
  have hg : g.val ∈ actualCentrePowerSectionGermImage (n := n) C q y := by
    rw [actualCentrePowerSectionGermImage_eq_whole (n := n) C q y]
    exact g.property
  obtain ⟨U,hyU,s,hs⟩ := hg
  let z := idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
    (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩
  refine ⟨(actualNormalLayerPresheaf A C q).germ U y hyU z,?_⟩
  rw [actualNormalLayerStalkToWholeHom_germ,actualNormalLayerSectionGermHom_class]
  apply Subtype.ext
  change Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hyU s.val) =
      Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y) g.val
  rw [hs]

/-- Original coherence and true quotient-colimit common opens INTERNALLY prove whole layer injectivity. -/
theorem actualNormalLayerStalkToWholeHom_injective (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    Function.Injective (actualNormalLayerStalkToWholeHom A C q y) := by
  intro a b hab
  let L := actualNormalLayerPresheaf A C q
  let Q := actualRemainderQuotientPresheaf A C (q+1)
  obtain ⟨U,hyU,s,rfl⟩ := L.exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := L.exists_germ_eq b
  change actualNormalLayerSection A C q U at s
  change actualNormalLayerSection A C q V at t
  rw [actualNormalLayerStalkToWholeHom_germ,actualNormalLayerStalkToWholeHom_germ] at hab
  have hquot : Q.germ U y hyU s.val = Q.germ V y hyV t.val := by
    apply actualRemainderQuotientStalkToWholeHom_injective A hA C (q+1) y
    change actualRemainderQuotientStalkToWholeHom A C (q+1) y
        ((actualRemainderQuotientPresheaf A C (q+1)).germ U y hyU
          (show actualRemainderSectionQuotient A C (q+1) U from s.val)) =
      actualRemainderQuotientStalkToWholeHom A C (q+1) y
        ((actualRemainderQuotientPresheaf A C (q+1)).germ V y hyV
          (show actualRemainderSectionQuotient A C (q+1) V from t.val))
    rw [actualRemainderQuotientStalkToWholeHom_germ,actualRemainderQuotientStalkToWholeHom_germ]
    exact congrArg Subtype.val hab
  obtain ⟨W,hyW,iU,iV,he⟩ := Q.germ_eq y hyU hyV s.val t.val hquot
  apply L.germ_ext W hyW iU iV
  apply Subtype.ext
  exact he

/-- ONLY original coherence yields the actual image-layer COLIMIT equivalence with the ENTIRE original layer. -/
def actualNormalLayerStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    actualNormalLayerStalk A C q y ≃+ actualWholeNormalLayer A C q y :=
  AddEquiv.ofBijective (actualNormalLayerStalkToWholeHom A C q y)
    ⟨actualNormalLayerStalkToWholeHom_injective A hA C q y,
      actualNormalLayerStalkToWholeHom_surjective A C q y⟩

/-- EVERY original actual layer section germ has the literal whole original image formula. -/
theorem actualNormalLayerStalkWholeEquiv_germ (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalLayerSection A C q U) :
    actualNormalLayerStalkWholeEquiv A hA C q y ((actualNormalLayerPresheaf A C q).germ U y hy s) =
      actualNormalLayerSectionGermHom A C q U y hy s := actualNormalLayerStalkToWholeHom_germ A C q U y hy s

/-- EVERY power-section class retains its SAME original actual ring-germ class under the whole equivalence. -/
theorem actualNormalLayerStalkWholeEquiv_class (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualNormalLayerStalkWholeEquiv A hA C q y ((actualNormalLayerPresheaf A C q).germ U y hy
      (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩)) =
      idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
          ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
            actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩ := by
  rw [actualNormalLayerStalkWholeEquiv_germ,actualNormalLayerSectionGermHom_class]

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalLayerStalk
