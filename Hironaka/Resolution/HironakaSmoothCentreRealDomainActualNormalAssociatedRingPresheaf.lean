/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
/-! Literal actual SECTION graded rings, genuine restrictions and whole ring-stalk map.
All four complete Mathematics.tex nodes precede proof code. The intrinsic
representative products precede every stalk comparison; no ring operation
or actual action is defined by a subsequent whole-stalk equivalence. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaRelativeNormalGradedAlgebra
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
  HironakaSmoothCentreRealDomainActualNormalLayerStalk HironakaSmoothCentreRealDomainActualNormalLayerScalars
  HironakaSmoothCentreRealDomainActualNormalAssociatedSheaf
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine homogeneous representative products commute with every true original restriction. -/
theorem actualNormalLayerRestrict_mul (A : GermIdeal n M) (C : Set M) (p q : ℕ)
    (U V : Opens M) (hUV : U ≤ V)
    (x : actualNormalLayerSection A C p V) (z : actualNormalLayerSection A C q V) :
    actualNormalLayerRestrict A C (p+q) U V hUV
        (idealPowerLayerMul (actualComplexSection (n := n) V) (actualSectionIdeal A V)
          (actualSectionIdeal (vanishingIdeal (n := n) C) V) x z) =
      idealPowerLayerMul (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U)
        (actualNormalLayerRestrict A C p U V hUV x) (actualNormalLayerRestrict A C q U V hUV z) := by
  obtain ⟨g,rfl⟩ := idealPowerLayerMap_surjective (actualComplexSection (n := n) V)
    (actualSectionIdeal A V) (actualSectionIdeal (vanishingIdeal (n := n) C) V) p x
  obtain ⟨t,rfl⟩ := idealPowerLayerMap_surjective (actualComplexSection (n := n) V)
    (actualSectionIdeal A V) (actualSectionIdeal (vanishingIdeal (n := n) C) V) q z
  let r := (actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op
  let gu : powerModule (actualComplexSection (n := n) U)
      (actualSectionIdeal (vanishingIdeal (n := n) C) U) p :=
    ⟨r g.val,actualCentrePowerSectionIdeal_restrict (n := n) C p U V hUV g.val g.property⟩
  let tu : powerModule (actualComplexSection (n := n) U)
      (actualSectionIdeal (vanishingIdeal (n := n) C) U) q :=
    ⟨r t.val,actualCentrePowerSectionIdeal_restrict (n := n) C q U V hUV t.val t.property⟩
  rw [idealPowerLayerMul_map]
  change actualNormalLayerRestrict A C (p+q) U V hUV
      (idealPowerLayerMap (actualComplexSection (n := n) V) (actualSectionIdeal A V)
        (actualSectionIdeal (vanishingIdeal (n := n) C) V) (p+q)
        (GradedMonoid.GMul.mul (A := powerFamily (actualComplexSection (n := n) V)
          (actualSectionIdeal (vanishingIdeal (n := n) C) V)) g t)) =
    idealPowerLayerMul (actualComplexSection (n := n) U) (actualSectionIdeal A U)
      (actualSectionIdeal (vanishingIdeal (n := n) C) U)
      (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) p gu)
      (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) q tu)
  rw [idealPowerLayerMul_map]
  apply Subtype.ext
  change actualRemainderQuotientRestrict A C (p+q+1) U V hUV
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (p+q+1) V) (g.val*t.val)) =
    Ideal.Quotient.mk (actualRemainderSectionIdeal A C (p+q+1) U) (r g.val*r t.val)
  rw [actualRemainderQuotientRestrict_mk,r.hom.map_mul]

/-- The literal finite-support direct sum of the actual original section layers. -/
abbrev actualNormalAssociatedRingSection (A : GermIdeal n M) (C : Set M) (U : Opens M) : Type :=
  ⨁ q : ℕ,actualNormalLayerSection A C q U

/-- Independent intrinsic commutative graded-ring operations from actual power representatives. -/
instance actualNormalAssociatedRingSectionCommRing (A : GermIdeal n M) (C : Set M) (U : Opens M) :
    CommRing (actualNormalAssociatedRingSection A C U) :=
  idealPowerAssociatedCommRing (actualComplexSection (n := n) U) (actualSectionIdeal A U)
    (actualSectionIdeal (vanishingIdeal (n := n) C) U)

/-- Independent actual ambient section algebra before any stalk comparison. -/
instance actualNormalAssociatedRingSectionAlgebra (A : GermIdeal n M) (C : Set M) (U : Opens M) :
    Algebra (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U) :=
  idealPowerAssociatedAlgebra (actualComplexSection (n := n) U) (actualSectionIdeal A U)
    (actualSectionIdeal (vanishingIdeal (n := n) C) U)

/-- Every genuine homogeneous section product retains its original degree and representative product. -/
theorem actualNormalAssociatedRingSection_of_mul_of (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (p q : ℕ) (x : actualNormalLayerSection A C p U) (z : actualNormalLayerSection A C q U) :
    DirectSum.of (fun k => actualNormalLayerSection A C k U) p x *
      DirectSum.of (fun k => actualNormalLayerSection A C k U) q z =
    DirectSum.of (fun k => actualNormalLayerSection A C k U) (p+q)
      (idealPowerLayerMul (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) x z) :=
  idealPowerAssociated_of_mul_of (actualComplexSection (n := n) U) (actualSectionIdeal A U)
    (actualSectionIdeal (vanishingIdeal (n := n) C) U) p q x z

/-- Actual restrictions on ALL section degrees extend to a genuine entire ring homomorphism. -/
def actualNormalAssociatedRingRestrict (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) :
    actualNormalAssociatedRingSection A C V →+* actualNormalAssociatedRingSection A C U :=
  DirectSum.toSemiring (fun q => (DirectSum.of (fun k => actualNormalLayerSection A C k U) q).comp
    (actualNormalLayerRestrict A C q U V hUV))
    (by
      change DirectSum.of (fun k => actualNormalLayerSection A C k U) 0
        (actualNormalLayerRestrict A C 0 U V hUV
          (idealPowerLayerMap (actualComplexSection (n := n) V) (actualSectionIdeal A V)
            (actualSectionIdeal (vanishingIdeal (n := n) C) V) 0 ⟨1,by simp⟩)) = 1
      change DirectSum.of (fun k => actualNormalLayerSection A C k U) 0
        (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
          (actualSectionIdeal (vanishingIdeal (n := n) C) U) 0 ⟨1,by simp⟩) = 1
      exact DirectSum.of_zero_one _)
    (by
      intro p q x z
      change DirectSum.of (fun k => actualNormalLayerSection A C k U) (p+q)
        (actualNormalLayerRestrict A C (p+q) U V hUV
          (idealPowerLayerMul (actualComplexSection (n := n) V) (actualSectionIdeal A V)
            (actualSectionIdeal (vanishingIdeal (n := n) C) V) x z)) = _
      rw [actualNormalLayerRestrict_mul]
      exact (actualNormalAssociatedRingSection_of_mul_of A C U p q
        (actualNormalLayerRestrict A C p U V hUV x)
        (actualNormalLayerRestrict A C q U V hUV z)).symm)

/-- True whole ring restriction keeps EVERY actual degree inclusion. -/
theorem actualNormalAssociatedRingRestrict_of (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) (q : ℕ) (x : actualNormalLayerSection A C q V) :
    actualNormalAssociatedRingRestrict A C U V hUV
      (DirectSum.of (fun k => actualNormalLayerSection A C k V) q x) =
    DirectSum.of (fun k => actualNormalLayerSection A C k U) q
      (actualNormalLayerRestrict A C q U V hUV x) := by
  unfold actualNormalAssociatedRingRestrict
  exact DirectSum.toSemiring_of (A := fun k => actualNormalLayerSection A C k V)
    (R := actualNormalAssociatedRingSection A C U)
    (fun k => (DirectSum.of (fun t => actualNormalLayerSection A C t U) k).comp
      (actualNormalLayerRestrict A C k U V hUV)) _ _ q x

/-- Genuine CommRingCat presheaf of literal original section graded rings. -/
def actualNormalAssociatedRingPresheaf (A : GermIdeal n M) (C : Set M) :
    (TopCat.of M).Presheaf CommRingCat where
  obj U := CommRingCat.of (actualNormalAssociatedRingSection A C (unop U))
  map i := CommRingCat.ofHom (actualNormalAssociatedRingRestrict A C _ _ (leOfHom i.unop))
  map_id := by
    intro U
    apply CommRingCat.hom_ext
    apply DirectSum.ringHom_ext
    intro q x
    change actualNormalAssociatedRingRestrict A C (unop U) (unop U) _
      (DirectSum.of (fun k => actualNormalLayerSection A C k (unop U)) q x) = _
    rw [actualNormalAssociatedRingRestrict_of]
    apply congrArg (DirectSum.of (fun k => actualNormalLayerSection A C k (unop U)) q)
    exact ConcreteCategory.congr_hom ((actualNormalLayerPresheaf A C q).map_id U) x
  map_comp := by
    intro U V W i j
    apply CommRingCat.hom_ext
    apply DirectSum.ringHom_ext
    intro q x
    change actualNormalAssociatedRingRestrict A C (unop W) (unop U) _
      (DirectSum.of (fun k => actualNormalLayerSection A C k (unop U)) q x) =
      actualNormalAssociatedRingRestrict A C (unop W) (unop V) _
        (actualNormalAssociatedRingRestrict A C (unop V) (unop U) _
          (DirectSum.of (fun k => actualNormalLayerSection A C k (unop U)) q x))
    rw [actualNormalAssociatedRingRestrict_of,actualNormalAssociatedRingRestrict_of,
      actualNormalAssociatedRingRestrict_of]
    apply congrArg (DirectSum.of (fun k => actualNormalLayerSection A C k (unop W)) q)
    exact ConcreteCategory.congr_hom ((actualNormalLayerPresheaf A C q).map_comp i j) x

/-- The original degree-zero section algebra map is genuinely natural for actual restrictions. -/
theorem actualNormalAssociatedRingRestrict_algebraMap (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) (r : actualComplexSection (n := n) V) :
    actualNormalAssociatedRingRestrict A C U V hUV
        (algebraMap (actualComplexSection (n := n) V) (actualNormalAssociatedRingSection A C V) r) =
      algebraMap (actualComplexSection (n := n) U) (actualNormalAssociatedRingSection A C U)
        ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op r) := by
  rw [idealPowerAssociated_algebraMap,actualNormalAssociatedRingRestrict_of,
    idealPowerAssociated_algebraMap]
  apply congrArg (DirectSum.of (fun k => actualNormalLayerSection A C k U) 0)
  apply Subtype.ext
  exact actualRemainderQuotientRestrict_mk A C 1 U V hUV r

/-- The TRUE ambient original structure-ring presheaf acts through actual degree-zero section classes. -/
def actualNormalAssociatedAmbientRingMap (A : GermIdeal n M) (C : Set M) :
    (actualComplexStructureSheaf (n := n) M).presheaf ⟶ actualNormalAssociatedRingPresheaf A C where
  app U := CommRingCat.ofHom
    (algebraMap (actualComplexSection (n := n) (unop U)) (actualNormalAssociatedRingSection A C (unop U)))
  naturality U V i := by
    apply CommRingCat.hom_ext
    ext r
    exact (actualNormalAssociatedRingRestrict_algebraMap A C (unop V) (unop U) (leOfHom i.unop) r).symm

/-- The WHOLE original associated ring at the actual structure-sheaf stalk. -/
abbrev actualWholeNormalAssociatedRing (A : GermIdeal n M) (C : Set M) (y : M) : Type :=
  ⨁ q : ℕ,actualWholeNormalLayer A C q y

/-- Independent original power-representative multiplication on the WHOLE original ring. -/
instance actualWholeNormalAssociatedRingCommRing (A : GermIdeal n M) (C : Set M) (y : M) :
    CommRing (actualWholeNormalAssociatedRing A C y) :=
  idealPowerAssociatedCommRing (actualComplexStructureStalk (n := n) y)
    (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)

/-- Actual section germs preserve every genuine homogeneous representative product. -/
theorem actualNormalLayerSectionGermHom_mul (A : GermIdeal n M) (C : Set M) (p q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U)
    (x : actualNormalLayerSection A C p U) (z : actualNormalLayerSection A C q U) :
    actualNormalLayerSectionGermHom A C (p+q) U y hy
        (idealPowerLayerMul (actualComplexSection (n := n) U) (actualSectionIdeal A U)
          (actualSectionIdeal (vanishingIdeal (n := n) C) U) x z) =
      idealPowerLayerMul (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
        (actualNormalLayerSectionGermHom A C p U y hy x) (actualNormalLayerSectionGermHom A C q U y hy z) := by
  obtain ⟨g,rfl⟩ := idealPowerLayerMap_surjective (actualComplexSection (n := n) U)
    (actualSectionIdeal A U) (actualSectionIdeal (vanishingIdeal (n := n) C) U) p x
  obtain ⟨t,rfl⟩ := idealPowerLayerMap_surjective (actualComplexSection (n := n) U)
    (actualSectionIdeal A U) (actualSectionIdeal (vanishingIdeal (n := n) C) U) q z
  let r := (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy
  let gy : powerModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) p :=
    ⟨r g.val,actualCentrePowerSectionIdeal_germ_mem (n := n) C p U y hy g.val g.property⟩
  let ty : powerModule (actualComplexStructureStalk (n := n) y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q :=
    ⟨r t.val,actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy t.val t.property⟩
  rw [idealPowerLayerMul_map]
  change actualNormalLayerSectionGermHom A C (p+q) U y hy
      (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
        (actualSectionIdeal (vanishingIdeal (n := n) C) U) (p+q)
        (GradedMonoid.GMul.mul (A := powerFamily (actualComplexSection (n := n) U)
          (actualSectionIdeal (vanishingIdeal (n := n) C) U)) g t)) =
    idealPowerLayerMul (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
      (idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) p gy)
      (idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q ty)
  rw [idealPowerLayerMul_map]
  apply Subtype.ext
  change actualRemainderQuotientSectionGermHom A C (p+q+1) U y hy
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (p+q+1) U) (g.val*t.val)) =
    Ideal.Quotient.mk (actualWholeRemainderIdeal A C (p+q+1) y) (r g.val*r t.val)
  rw [actualRemainderQuotientSectionGermHom_mk,r.hom.map_mul]

/-- ALL actual homogeneous section germs extend to the ENTIRE genuine original ring. -/
def actualNormalAssociatedRingSectionGermHom (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) :
    actualNormalAssociatedRingSection A C U →+* actualWholeNormalAssociatedRing A C y :=
  DirectSum.toSemiring (fun q => (DirectSum.of (fun k => actualWholeNormalLayer A C k y) q).comp
    (actualNormalLayerSectionGermHom A C q U y hy))
    (by
      have he : actualNormalLayerSectionGermHom A C 0 U y hy
          (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) 0 ⟨1,by simp⟩) =
        idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) 0 ⟨1,by simp⟩ := by
        apply Subtype.ext
        change actualRemainderQuotientSectionGermHom A C 1 U y hy
            (Ideal.Quotient.mk (actualRemainderSectionIdeal A C 1 U) 1) =
          Ideal.Quotient.mk (actualWholeRemainderIdeal A C 1 y) 1
        rw [actualRemainderQuotientSectionGermHom_mk]
        change Ideal.Quotient.mk (actualWholeRemainderIdeal A C 1 y)
          (((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom (1 : actualComplexSection (n := n) U)) = _
        rw [map_one]
      change DirectSum.of (fun k => actualWholeNormalLayer A C k y) 0
        (actualNormalLayerSectionGermHom A C 0 U y hy
          (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) 0 ⟨1,by simp⟩)) = 1
      rw [he]
      exact DirectSum.of_zero_one _)
    (by
      intro p q x z
      change DirectSum.of (fun k => actualWholeNormalLayer A C k y) (p+q)
        (actualNormalLayerSectionGermHom A C (p+q) U y hy
          (idealPowerLayerMul (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) x z)) = _
      rw [actualNormalLayerSectionGermHom_mul]
      exact (idealPowerAssociated_of_mul_of (actualComplexStructureStalk (n := n) y)
        (actualWholeSheafStalkIdeal A y) (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y)
        p q (actualNormalLayerSectionGermHom A C p U y hy x)
        (actualNormalLayerSectionGermHom A C q U y hy z)).symm)

/-- The ENTIRE ring section germ map retains EVERY homogeneous original layer class. -/
theorem actualNormalAssociatedRingSectionGermHom_of (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) (q : ℕ) (x : actualNormalLayerSection A C q U) :
    actualNormalAssociatedRingSectionGermHom A C U y hy
      (DirectSum.of (fun k => actualNormalLayerSection A C k U) q x) =
    DirectSum.of (fun k => actualWholeNormalLayer A C k y) q
      (actualNormalLayerSectionGermHom A C q U y hy x) := by
  unfold actualNormalAssociatedRingSectionGermHom
  exact DirectSum.toSemiring_of (A := fun k => actualNormalLayerSection A C k U)
    (R := actualWholeNormalAssociatedRing A C y)
    (fun k => (DirectSum.of (fun t => actualWholeNormalLayer A C t y) k).comp
      (actualNormalLayerSectionGermHom A C k U y hy)) _ _ q x

/-- True ordinary-open layer germs commute with restrictions on every actual quotient representative. -/
theorem actualNormalLayerSectionGermHom_restrict (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) (y : M) (hyU : y ∈ U) (hyV : y ∈ V)
    (x : actualNormalLayerSection A C q V) :
    actualNormalLayerSectionGermHom A C q U y hyU (actualNormalLayerRestrict A C q U V hUV x) =
      actualNormalLayerSectionGermHom A C q V y hyV x := by
  apply Subtype.ext
  change actualRemainderQuotientSectionGermHom A C (q+1) U y hyU
      (actualRemainderQuotientRestrict A C (q+1) U V hUV x.val) =
    actualRemainderQuotientSectionGermHom A C (q+1) V y hyV x.val
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective
    (show actualRemainderSectionQuotient A C (q+1) V from x.val)
  have hh : actualRemainderQuotientSectionGermHom A C (q+1) U y hyU
        (actualRemainderQuotientRestrict A C (q+1) U V hUV
          (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) V) r)) =
      actualRemainderQuotientSectionGermHom A C (q+1) V y hyV
        (Ideal.Quotient.mk (actualRemainderSectionIdeal A C (q+1) V) r) := by
    change Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hyU
          ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op r)) =
      Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ V y hyV r)
    exact congrArg (Ideal.Quotient.mk (actualWholeRemainderIdeal A C (q+1) y))
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply (homOfLE hUV) y hyU r)
  exact (congrArg (fun v : actualRemainderSectionQuotient A C (q+1) V =>
    actualRemainderQuotientSectionGermHom A C (q+1) U y hyU
      (actualRemainderQuotientRestrict A C (q+1) U V hUV v)) hr.symm).trans
        (hh.trans (congrArg (actualRemainderQuotientSectionGermHom A C (q+1) V y hyV) hr))

/-- The ENTIRE original ring germ commutes with true restrictions on ordinary actual opens. -/
theorem actualNormalAssociatedRingSectionGermHom_restrict (A : GermIdeal n M) (C : Set M)
    (U V : Opens M) (hUV : U ≤ V) (y : M) (hyU : y ∈ U) (hyV : y ∈ V) :
    (actualNormalAssociatedRingSectionGermHom A C U y hyU).comp
      (actualNormalAssociatedRingRestrict A C U V hUV) =
    actualNormalAssociatedRingSectionGermHom A C V y hyV := by
  apply DirectSum.ringHom_ext
  intro q x
  change actualNormalAssociatedRingSectionGermHom A C U y hyU
      (actualNormalAssociatedRingRestrict A C U V hUV
        (DirectSum.of (fun k => actualNormalLayerSection A C k V) q x)) =
    actualNormalAssociatedRingSectionGermHom A C V y hyV
      (DirectSum.of (fun k => actualNormalLayerSection A C k V) q x)
  rw [actualNormalAssociatedRingRestrict_of,actualNormalAssociatedRingSectionGermHom_of,
    actualNormalAssociatedRingSectionGermHom_of]
  apply congrArg (DirectSum.of (fun k => actualWholeNormalLayer A C k y) q)
  exact actualNormalLayerSectionGermHom_restrict A C q U V hUV y hyU hyV x

/-- True original section-ring germ maps give a genuine neighbourhood RING cocone. -/
def actualNormalAssociatedRingGermCocone (A : GermIdeal n M) (C : Set M) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualNormalAssociatedRingPresheaf A C) where
  pt := CommRingCat.of (actualWholeNormalAssociatedRing A C y)
  ι := {
    app := fun U => CommRingCat.ofHom
      (actualNormalAssociatedRingSectionGermHom A C (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      apply CommRingCat.hom_ext
      exact actualNormalAssociatedRingSectionGermHom_restrict A C
        (unop V).val (unop U).val (leOfHom i.unop) y (unop V).property (unop U).property }


/-- The REAL neighbourhood-colimit ring internally supplies its WHOLE original graded-ring map. -/
def actualNormalAssociatedRingStalkToWholeHom (A : GermIdeal n M) (C : Set M) (y : M) :
    ((actualNormalAssociatedRingPresheaf A C).stalk y).carrier →+* actualWholeNormalAssociatedRing A C y :=
  (colimit.desc _ (actualNormalAssociatedRingGermCocone A C y)).hom

/-- EVERY actual ENTIRE original section-ring germ has the true whole ring class formula. -/
theorem actualNormalAssociatedRingStalkToWholeHom_germ (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualNormalAssociatedRingSection A C U) :
    actualNormalAssociatedRingStalkToWholeHom A C y
      ((actualNormalAssociatedRingPresheaf A C).germ U y hy s) =
    actualNormalAssociatedRingSectionGermHom A C U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualNormalAssociatedRingPresheaf A C
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualNormalAssociatedRingGermCocone A C y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- EVERY original actual homogeneous POWER class retains its literal entire original germ class. -/
theorem actualNormalAssociatedRingStalkToWholeHom_power_class (A : GermIdeal n M) (C : Set M)
    (U : Opens M) (y : M) (hy : y ∈ U) (q : ℕ)
    (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualNormalAssociatedRingStalkToWholeHom A C y
      ((actualNormalAssociatedRingPresheaf A C).germ U y hy
        (DirectSum.of (fun k => actualNormalLayerSection A C k U) q
          (idealPowerLayerMap (actualComplexSection (n := n) U) (actualSectionIdeal A U)
            (actualSectionIdeal (vanishingIdeal (n := n) C) U) q ⟨s.val,s.property⟩))) =
    DirectSum.of (fun k => actualWholeNormalLayer A C k y) q
      (idealPowerLayerMap (actualComplexStructureStalk (n := n) y) (actualWholeSheafStalkIdeal A y)
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y) q
          ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
            actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩) := by
  rw [actualNormalAssociatedRingStalkToWholeHom_germ,actualNormalAssociatedRingSectionGermHom_of,
    actualNormalLayerSectionGermHom_class]

end
end Hironaka.HironakaSmoothCentreRealDomainActualNormalAssociatedRingPresheaf
