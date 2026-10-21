/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf
/-! Literal centre-power section presheaves and their entire original stalks.
Complete three-node Mathematics.tex precedes code. Genuine section powers and
all actual colimit germs, not a desired power-stalk certificate, are retained. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualCentrePowerStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
/-- These are the LITERAL powers of true original centre section ideals on each actual open. -/
abbrev actualCentrePowerSectionIdeal (C : Set M) (q : ℕ) (U : Opens M) :
    Ideal (actualComplexSection (n := n) U) := actualSectionIdeal (vanishingIdeal (n := n) C) U ^ q

/-- Actual ring restrictions map the ENTIRE original centre section ideal into the real smaller-open ideal. -/
theorem map_actualCentreSectionIdeal_restrict_le (C : Set M) (U V : Opens M) (hUV : U ≤ V) :
    Ideal.map ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom
      (actualSectionIdeal (vanishingIdeal (n := n) C) V) ≤
        actualSectionIdeal (vanishingIdeal (n := n) C) U := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro s hs
  exact actualSectionIdeal_restrict _ U V hUV s hs

/-- EVERY real section-power member restricts into the SAME whole degree power on a genuine smaller open. -/
theorem actualCentrePowerSectionIdeal_restrict (C : Set M) (q : ℕ) (U V : Opens M)
    (hUV : U ≤ V) (s : actualComplexSection (n := n) V) (hs : s ∈ actualCentrePowerSectionIdeal (n := n) C q V) :
    (actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s ∈
      actualCentrePowerSectionIdeal (n := n) C q U := by
  let r := ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom
  have hmap := Ideal.mem_map_of_mem r hs
  rw [Ideal.map_pow] at hmap
  exact (pow_le_pow_left' (map_actualCentreSectionIdeal_restrict_le (n := n) C U V hUV) q) hmap

/-- The genuine actual power-section restriction homomorphism. -/
def actualCentrePowerSectionRestrict (C : Set M) (q : ℕ) (U V : Opens M) (hUV : U ≤ V) :
    actualCentrePowerSectionIdeal (n := n) C q V →+ actualCentrePowerSectionIdeal (n := n) C q U where
  toFun s := ⟨(actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s.val,
    actualCentrePowerSectionIdeal_restrict (n := n) C q U V hUV s.val s.property⟩
  map_zero' := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom.map_add s.val t.val

/-- ALL degrees use actual section ideal powers, not a stalk-prescribed family. -/
def actualCentrePowerSectionPresheaf (C : Set M) (q : ℕ) : (TopCat.of M).Presheaf AddCommGrpCat where
  obj U := AddCommGrpCat.of (actualCentrePowerSectionIdeal (n := n) C q (unop U))
  map i := AddCommGrpCat.ofHom (actualCentrePowerSectionRestrict (n := n) C q _ _ (leOfHom i.unop))
  map_id := by
    intro U
    ext s
    rfl
  map_comp := by
    intro U V W i j
    ext s
    rfl

/-- The LITERAL actual neighbourhood colimit stalk of the original centre-power sections. -/
abbrev actualCentrePowerSectionStalk (C : Set M) (q : ℕ) (y : M) : Type :=
  ((actualCentrePowerSectionPresheaf (n := n) C q).stalk y).carrier

/-- Every actual original section-to-stalk ring germ takes the ENTIRE centre section ideal into its original whole ideal. -/
theorem map_actualCentreSectionIdeal_germ_le (C : Set M) (U : Opens M) (y : M) (hy : y ∈ U) :
    Ideal.map ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom
      (actualSectionIdeal (vanishingIdeal (n := n) C) U) ≤
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro s hs
  exact hs y hy

/-- EVERY genuine power-section germ lies in the ENTIRE original whole centre ideal power. -/
theorem actualCentrePowerSectionIdeal_germ_mem (C : Set M) (q : ℕ) (U : Opens M)
    (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U) (hs : s ∈ actualCentrePowerSectionIdeal (n := n) C q U) :
    (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s ∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q := by
  let r := ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom
  have hmap := Ideal.mem_map_of_mem r hs
  rw [Ideal.map_pow] at hmap
  exact (pow_le_pow_left' (map_actualCentreSectionIdeal_germ_le (n := n) C U y hy) q) hmap

/-- TRUE actual power-section germs form an additive map to the entire original power. -/
def actualCentrePowerSectionGermHom (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) :
    actualCentrePowerSectionIdeal (n := n) C q U →+ ↥(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q) where
  toFun s := ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,
    actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy s.val s.property⟩
  map_zero' := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom.map_add s.val t.val

/-- All TRUE power-section germs make a cocone on the actual original neighbourhood diagram. -/
def actualCentrePowerSectionGermCocone (C : Set M) (q : ℕ) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualCentrePowerSectionPresheaf (n := n) C q) where
  pt := AddCommGrpCat.of ↥(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q)
  ι := {
    app := fun U => AddCommGrpCat.ofHom (actualCentrePowerSectionGermHom (n := n) C q (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext s
      apply Subtype.ext
      change (actualComplexStructureSheaf (n := n) M).presheaf.germ (unop V).val y (unop V).property
        ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE (leOfHom i.unop)).op s.val) =
        (actualComplexStructureSheaf (n := n) M).presheaf.germ (unop U).val y (unop U).property s.val
      exact (actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (leOfHom i.unop)) y (unop V).property s.val }

/-- The genuine actual colimit universal property supplies the whole original power stalk map internally. -/
def actualCentrePowerStalkToWholeHom (C : Set M) (q : ℕ) (y : M) :
    actualCentrePowerSectionStalk (n := n) C q y →+ ↥(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q) :=
  (colimit.desc _ (actualCentrePowerSectionGermCocone (n := n) C q y)).hom

/-- EVERY literal power-section colimit germ retains its SAME original ring germ formula. -/
theorem actualCentrePowerStalkToWholeHom_germ (C : Set M) (q : ℕ) (U : Opens M) (y : M)
    (hy : y ∈ U) (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualCentrePowerStalkToWholeHom (n := n) C q y ((actualCentrePowerSectionPresheaf (n := n) C q).germ U y hy s) =
      actualCentrePowerSectionGermHom (n := n) C q U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualCentrePowerSectionPresheaf (n := n) C q
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualCentrePowerSectionGermCocone (n := n) C q y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- ALL actual power-section germs form a TRUE ideal using genuine common-open representatives. -/
def actualCentrePowerSectionGermImage (C : Set M) (q : ℕ) (y : M) :
    Ideal (actualComplexStructureStalk (n := n) y) where
  carrier := {g | ∃ (U : Opens M) (hy : y ∈ U) (s : actualCentrePowerSectionIdeal (n := n) C q U),
    (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val = g}
  zero_mem' := by
    refine ⟨⊤,by trivial,0,?_⟩
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ y (by trivial)).hom.map_zero
  add_mem' := by
    intro g h hg hh
    obtain ⟨U,hyU,s,hgs⟩ := hg
    obtain ⟨V,hyV,t,hht⟩ := hh
    let W : Opens M := U ⊓ V
    have hyW : y ∈ W := ⟨hyU,hyV⟩
    let su := actualCentrePowerSectionRestrict (n := n) C q W U inf_le_left s
    let tv := actualCentrePowerSectionRestrict (n := n) C q W V inf_le_right t
    refine ⟨W,hyW,su+tv,?_⟩
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (su.val+tv.val) = g+h
    rw [map_add]
    have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = g :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans hgs
    have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv.val = h :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ V from inf_le_right)) y hyW t.val).trans hht
    rw [hs,ht]
  smul_mem' := by
    intro r g hg
    obtain ⟨U,hyU,s,hgs⟩ := hg
    obtain ⟨V,hyV,t,hrt⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
    let W : Opens M := U ⊓ V
    have hyW : y ∈ W := ⟨hyU,hyV⟩
    let su := actualCentrePowerSectionRestrict (n := n) C q W U inf_le_left s
    let tv := (actualComplexStructureSheaf (n := n) M).presheaf.map
      (homOfLE (show W ≤ V from inf_le_right)).op t
    let v : actualCentrePowerSectionIdeal (n := n) C q W :=
      ⟨tv*su.val,(actualCentrePowerSectionIdeal (n := n) C q W).mul_mem_left tv su.property⟩
    refine ⟨W,hyW,v,?_⟩
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (tv*su.val) = r*g
    rw [map_mul]
    have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = g :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans hgs
    have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv = r :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ V from inf_le_right)) y hyW t).trans hrt
    rw [ht,hs]

/-- The ENTIRE genuine power-section germ image lies in the actual original whole power. -/
theorem actualCentrePowerSectionGermImage_le_whole (C : Set M) (q : ℕ) (y : M) :
    actualCentrePowerSectionGermImage (n := n) C q y ≤
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q := by
  rintro g ⟨U,hyU,s,hgs⟩
  rw [← hgs]
  exact actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hyU s.val s.property

/-- Genuine section products on true common opens INTERNALLY supply BOTH whole power-image inclusions at ALL degrees. -/
theorem actualCentrePowerSectionGermImage_eq_whole (C : Set M) (q : ℕ) (y : M) :
    actualCentrePowerSectionGermImage (n := n) C q y =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q := by
  induction q with
  | zero =>
    apply le_antisymm (actualCentrePowerSectionGermImage_le_whole (n := n) C 0 y)
    intro g _
    obtain ⟨U,hyU,s,heq⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq g
    exact ⟨U,hyU,⟨s,by simp [actualCentrePowerSectionIdeal]⟩,heq⟩
  | succ q ih =>
    apply le_antisymm (actualCentrePowerSectionGermImage_le_whole (n := n) C (q+1) y)
    rw [pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have hai : a ∈ actualCentrePowerSectionGermImage (n := n) C q y := by
      rw [ih]
      exact ha
    obtain ⟨U,hyU,s,has⟩ := hai
    have hbi : b ∈ actualIdealSectionGermImage (vanishingIdeal (n := n) C) y := by
      rw [actualCentreIdealSectionGermImage_eq_whole C y]
      exact hb
    obtain ⟨V,hyV,t,hbt⟩ := hbi
    let W : Opens M := U ⊓ V
    have hyW : y ∈ W := ⟨hyU,hyV⟩
    let su := actualCentrePowerSectionRestrict (n := n) C q W U inf_le_left s
    let tv := actualIdealSectionRestrict (vanishingIdeal (n := n) C) W V inf_le_right t
    have hprod : su.val*tv.val ∈ actualCentrePowerSectionIdeal (n := n) C (q+1) W := by
      change _ ∈ actualSectionIdeal (vanishingIdeal (n := n) C) W ^ (q+1)
      rw [pow_succ]
      exact Ideal.mul_mem_mul su.property tv.property
    refine ⟨W,hyW,⟨su.val*tv.val,hprod⟩,?_⟩
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (su.val*tv.val) = a*b
    rw [map_mul]
    have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = a :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans has
    have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv.val = b :=
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ V from inf_le_right)) y hyW t.val).trans hbt
    rw [hs,ht]

/-- The actual ring-colimit germ equality supplies a true common open, proving literal power-colimit injectivity. -/
theorem actualCentrePowerStalkToWholeHom_injective (C : Set M) (q : ℕ) (y : M) :
    Function.Injective (actualCentrePowerStalkToWholeHom (n := n) C q y) := by
  intro a b hab
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  obtain ⟨U,hyU,s,rfl⟩ := (actualCentrePowerSectionPresheaf (n := n) C q).exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := (actualCentrePowerSectionPresheaf (n := n) C q).exists_germ_eq b
  change actualCentrePowerSectionIdeal (n := n) C q U at s
  change actualCentrePowerSectionIdeal (n := n) C q V at t
  rw [actualCentrePowerStalkToWholeHom_germ (n := n) C q U y hyU s,
    actualCentrePowerStalkToWholeHom_germ (n := n) C q V y hyV t] at hab
  have hval : F.germ U y hyU s.val = F.germ V y hyV t.val := congrArg Subtype.val hab
  obtain ⟨W,hyW,iU,iV,heq⟩ := F.germ_eq y hyU hyV s.val t.val hval
  apply (actualCentrePowerSectionPresheaf (n := n) C q).germ_ext W hyW iU iV
  apply Subtype.ext
  exact heq

/-- ALL original whole power elements have genuine literal power-presheaf COLIMIT preimages. -/
theorem actualCentrePowerStalkToWholeHom_surjective (C : Set M) (q : ℕ) (y : M) :
    Function.Surjective (actualCentrePowerStalkToWholeHom (n := n) C q y) := by
  intro g
  have hg : g.val ∈ actualCentrePowerSectionGermImage (n := n) C q y := by
    rw [actualCentrePowerSectionGermImage_eq_whole (n := n) C q y]
    exact g.property
  obtain ⟨U,hyU,s,heq⟩ := hg
  refine ⟨(actualCentrePowerSectionPresheaf (n := n) C q).germ U y hyU s,?_⟩
  rw [actualCentrePowerStalkToWholeHom_germ (n := n) C q U y hyU s]
  apply Subtype.ext
  exact heq

/-- EVERY actual degree-power colimit stalk is INTERNALLY equivalent to the ENTIRE original centre power. -/
def actualCentrePowerStalkWholeEquiv (C : Set M) (q : ℕ) (y : M) :
    actualCentrePowerSectionStalk (n := n) C q y ≃+
      ↥(actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q) :=
  AddEquiv.ofBijective (actualCentrePowerStalkToWholeHom (n := n) C q y)
    ⟨actualCentrePowerStalkToWholeHom_injective (n := n) C q y,
      actualCentrePowerStalkToWholeHom_surjective (n := n) C q y⟩

/-- EVERY genuine power-section germ retains its SAME original representative under the whole equivalence. -/
theorem actualCentrePowerStalkWholeEquiv_germ (C : Set M) (q : ℕ) (U : Opens M) (y : M)
    (hy : y ∈ U) (s : actualCentrePowerSectionIdeal (n := n) C q U) :
    actualCentrePowerStalkWholeEquiv (n := n) C q y
      ((actualCentrePowerSectionPresheaf (n := n) C q).germ U y hy s) =
      actualCentrePowerSectionGermHom (n := n) C q U y hy s :=
  actualCentrePowerStalkToWholeHom_germ (n := n) C q U y hy s

end
end Hironaka.HironakaSmoothCentreRealDomainActualCentrePowerStalk
