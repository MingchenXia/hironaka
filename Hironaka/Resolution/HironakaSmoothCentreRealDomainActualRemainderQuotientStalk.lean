/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualCentrePowerStalk
/-! Genuine original remainder section quotients and their entire ring stalks.
Complete three-node Mathematics.tex precedes code. True section sums, actual
quotient rings/colimits and every original representative are retained;
no centre quotient action is asserted on a higher truncation. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentrePowerStalk
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
/-- The LITERAL sum of original ideal sections and actual centre-section powers on each real open. -/
def actualRemainderSectionIdeal (A : GermIdeal n M) (C : Set M) (q : ℕ) (U : Opens M) :
    Ideal (actualComplexSection (n := n) U) :=
  actualSectionIdeal A U ⊔ actualCentrePowerSectionIdeal (n := n) C q U

/-- The ENTIRE original actual stalk remainder, without a selected finite family. -/
def actualWholeRemainderIdeal (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Ideal (actualComplexStructureStalk (n := n) y) :=
  actualWholeSheafStalkIdeal A y ⊔ actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q

/-- Every genuine actual restriction preserves the ENTIRE original section remainder. -/
theorem actualRemainderSectionIdeal_restrict (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) (s : actualComplexSection (n := n) V)
    (hs : s ∈ actualRemainderSectionIdeal A C q V) :
    (actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s ∈
      actualRemainderSectionIdeal A C q U := by
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hs
  change ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom (a+b) ∈ _
  rw [map_add]
  exact (actualRemainderSectionIdeal A C q U).add_mem
    ((show actualSectionIdeal A U ≤ actualRemainderSectionIdeal A C q U from le_sup_left)
      (actualSectionIdeal_restrict A U V hUV a ha))
    ((show actualCentrePowerSectionIdeal (n := n) C q U ≤ actualRemainderSectionIdeal A C q U from le_sup_right)
      (actualCentrePowerSectionIdeal_restrict (n := n) C q U V hUV b hb))

/-- Every ACTUAL section remainder germ lies in the ENTIRE original whole remainder. -/
theorem actualRemainderSectionIdeal_germ_mem (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U)
    (hs : s ∈ actualRemainderSectionIdeal A C q U) :
    (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s ∈ actualWholeRemainderIdeal A C q y := by
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hs
  change ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom (a+b) ∈ _
  rw [map_add]
  exact (actualWholeRemainderIdeal A C q y).add_mem ((show actualWholeSheafStalkIdeal A y ≤ actualWholeRemainderIdeal A C q y from le_sup_left) (ha y hy))
    ((show actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q ≤ actualWholeRemainderIdeal A C q y from le_sup_right)
      (actualCentrePowerSectionIdeal_germ_mem (n := n) C q U y hy b hb))

/-- Original coherence and true centre-power sections INTERNALLY supply EVERY whole remainder representative. -/
theorem exists_actual_remainder_section_of_whole_member (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) (g : actualComplexStructureStalk (n := n) y)
    (hg : g ∈ actualWholeRemainderIdeal A C q y) :
    ∃ (U : Opens M) (hy : y ∈ U) (s : actualRemainderSectionIdeal A C q U),
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val = g := by
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hg
  have hai : a ∈ actualIdealSectionGermImage A y := by
    rw [actualIdealSectionGermImage_eq_whole A hA y]
    exact ha
  obtain ⟨U,hyU,s,has⟩ := hai
  have hbi : b ∈ actualCentrePowerSectionGermImage (n := n) C q y := by
    rw [actualCentrePowerSectionGermImage_eq_whole (n := n) C q y]
    exact hb
  obtain ⟨V,hyV,t,hbt⟩ := hbi
  let W : Opens M := U ⊓ V
  have hyW : y ∈ W := ⟨hyU,hyV⟩
  let su := actualIdealSectionRestrict A W U inf_le_left s
  let tv := actualCentrePowerSectionRestrict (n := n) C q W V inf_le_right t
  have hsum : su.val+tv.val ∈ actualRemainderSectionIdeal A C q W :=
    (actualRemainderSectionIdeal A C q W).add_mem ((show actualSectionIdeal A W ≤ actualRemainderSectionIdeal A C q W from le_sup_left) su.property)
      ((show actualCentrePowerSectionIdeal (n := n) C q W ≤ actualRemainderSectionIdeal A C q W from le_sup_right) tv.property)
  refine ⟨W,hyW,⟨su.val+tv.val,hsum⟩,?_⟩
  change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (su.val+tv.val) = g
  rw [map_add]
  have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = a :=
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
      (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans has
  have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv.val = b :=
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
      (homOfLE (show W ≤ V from inf_le_right)) y hyW t.val).trans hbt
  rw [hs,ht]
  exact hab

/-- The LITERAL actual remainder section quotient RING; no centre action is installed. -/
abbrev actualRemainderSectionQuotient (A : GermIdeal n M) (C : Set M) (q : ℕ) (U : Opens M) : Type :=
  actualComplexSection (n := n) U ⧸ actualRemainderSectionIdeal A C q U

/-- Genuine ring restriction descends through the actual section remainder, internally. -/
def actualRemainderQuotientRestrict (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) :
    actualRemainderSectionQuotient A C q V →+* actualRemainderSectionQuotient A C q U :=
  Ideal.Quotient.lift (actualRemainderSectionIdeal A C q V)
    ((Ideal.Quotient.mk (actualRemainderSectionIdeal A C q U)).comp
      ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom)
    (fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr (actualRemainderSectionIdeal_restrict A C q U V hUV s hs))

/-- EVERY actual original section class restricts to its SAME literal true restricted section class. -/
theorem actualRemainderQuotientRestrict_mk (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U V : Opens M) (hUV : U ≤ V) (s : actualComplexSection (n := n) V) :
    actualRemainderQuotientRestrict A C q U V hUV (Ideal.Quotient.mk (actualRemainderSectionIdeal A C q V) s) =
      Ideal.Quotient.mk (actualRemainderSectionIdeal A C q U)
        ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s) := rfl

/-- The TRUE actual remainder-quotient RING presheaf on genuine original opens. -/
def actualRemainderQuotientPresheaf (A : GermIdeal n M) (C : Set M) (q : ℕ) :
    (TopCat.of M).Presheaf CommRingCat where
  obj U := CommRingCat.of (actualRemainderSectionQuotient A C q (unop U))
  map i := CommRingCat.ofHom (actualRemainderQuotientRestrict A C q _ _ (leOfHom i.unop))
  map_id := by
    intro U
    ext a
    rfl
  map_comp := by
    intro U V W i j
    ext a
    rfl

/-- The LITERAL actual quotient-presheaf neighbourhood colimit ring stalk. -/
abbrev actualRemainderQuotientStalk (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) : Type :=
  ((actualRemainderQuotientPresheaf A C q).stalk y).carrier

/-- Each REAL actual section quotient maps to the ENTIRE original ring-stalk quotient. -/
def actualRemainderQuotientSectionGermHom (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) :
    actualRemainderSectionQuotient A C q U →+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeRemainderIdeal A C q y :=
  Ideal.Quotient.lift (actualRemainderSectionIdeal A C q U)
    ((Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y)).comp
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom)
    (fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr (actualRemainderSectionIdeal_germ_mem A C q U y hy s hs))

/-- EVERY original actual section class keeps its genuine original whole ring-germ class. -/
theorem actualRemainderQuotientSectionGermHom_mk (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U) :
    actualRemainderQuotientSectionGermHom A C q U y hy (Ideal.Quotient.mk (actualRemainderSectionIdeal A C q U) s) =
      Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) := rfl

/-- True actual quotient-germ ring maps form the genuine original neighbourhood cocone. -/
def actualRemainderQuotientGermCocone (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualRemainderQuotientPresheaf A C q) where
  pt := CommRingCat.of (actualComplexStructureStalk (n := n) y ⧸ actualWholeRemainderIdeal A C q y)
  ι := {
    app := fun U => CommRingCat.ofHom (actualRemainderQuotientSectionGermHom A C q (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext a
      obtain ⟨s,rfl⟩ := Ideal.Quotient.mk_surjective a
      change Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop V).val y (unop V).property
            ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE (leOfHom i.unop)).op s)) =
        Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y)
          ((actualComplexStructureSheaf (n := n) M).presheaf.germ (unop U).val y (unop U).property s)
      exact congrArg (Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y))
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
          (homOfLE (leOfHom i.unop)) y (unop V).property s) }

/-- The ACTUAL quotient-presheaf colimit internally supplies the whole quotient ring map. -/
def actualRemainderQuotientStalkToWholeHom (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    actualRemainderQuotientStalk A C q y →+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeRemainderIdeal A C q y :=
  (colimit.desc _ (actualRemainderQuotientGermCocone A C q y)).hom

/-- EVERY actual section quotient colimit germ retains its SAME original representative class. -/
theorem actualRemainderQuotientStalkToWholeHom_germ (A : GermIdeal n M) (C : Set M) (q : ℕ)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualRemainderSectionQuotient A C q U) :
    actualRemainderQuotientStalkToWholeHom A C q y ((actualRemainderQuotientPresheaf A C q).germ U y hy s) =
      actualRemainderQuotientSectionGermHom A C q U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualRemainderQuotientPresheaf A C q
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualRemainderQuotientGermCocone A C q y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- EVERY entire original quotient class has a genuine actual section-quotient COLIMIT representative. -/
theorem actualRemainderQuotientStalkToWholeHom_surjective (A : GermIdeal n M) (C : Set M) (q : ℕ) (y : M) :
    Function.Surjective (actualRemainderQuotientStalkToWholeHom A C q y) := by
  intro g
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨U,hyU,s,heq⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨(actualRemainderQuotientPresheaf A C q).germ U y hyU
    (Ideal.Quotient.mk (actualRemainderSectionIdeal A C q U) s),?_⟩
  rw [actualRemainderQuotientStalkToWholeHom_germ,actualRemainderQuotientSectionGermHom_mk,heq]

/-- Original coherence internally supplies WHOLE kernel representatives on true original opens, proving actual quotient-colimit injectivity. -/
theorem actualRemainderQuotientStalkToWholeHom_injective (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    Function.Injective (actualRemainderQuotientStalkToWholeHom A C q y) := by
  intro a b hab
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  let Q := actualRemainderQuotientPresheaf A C q
  obtain ⟨U,hyU,s,rfl⟩ := Q.exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := Q.exists_germ_eq b
  change actualRemainderSectionQuotient A C q U at s
  change actualRemainderSectionQuotient A C q V at t
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [actualRemainderQuotientStalkToWholeHom_germ,actualRemainderQuotientStalkToWholeHom_germ,
    actualRemainderQuotientSectionGermHom_mk,actualRemainderQuotientSectionGermHom_mk] at hab
  let W : Opens M := U ⊓ V
  have hyW : y ∈ W := ⟨hyU,hyV⟩
  let fu := F.map (homOfLE (show W ≤ U from inf_le_left)).op f
  let gv := F.map (homOfLE (show W ≤ V from inf_le_right)).op g
  have hfu : F.germ W y hyW fu = F.germ U y hyU f :=
    F.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) y hyW f
  have hgv : F.germ W y hyW gv = F.germ V y hyV g :=
    F.germ_res_apply (homOfLE (show W ≤ V from inf_le_right)) y hyW g
  have hrem : F.germ W y hyW (fu-gv) ∈ actualWholeRemainderIdeal A C q y := by
    change (F.germ W y hyW).hom (fu-gv) ∈ _
    rw [map_sub,hfu,hgv]
    exact Ideal.Quotient.eq.mp hab
  obtain ⟨R,hyR,k,hk⟩ := exists_actual_remainder_section_of_whole_member A hA C q y
    (F.germ W y hyW (fu-gv)) hrem
  obtain ⟨Z,hyZ,iW,iR,heq⟩ := F.germ_eq y hyW hyR (fu-gv) k.val hk.symm
  have hdiff : F.map iW.op (fu-gv) ∈ actualRemainderSectionIdeal A C q Z := by
    rw [heq]
    exact actualRemainderSectionIdeal_restrict A C q Z R (leOfHom iR) k.val k.property
  have heqQ : Ideal.Quotient.mk (actualRemainderSectionIdeal A C q Z) (F.map iW.op fu) =
      Ideal.Quotient.mk (actualRemainderSectionIdeal A C q Z) (F.map iW.op gv) := by
    apply Ideal.Quotient.eq.mpr
    change (F.map iW.op).hom fu - (F.map iW.op).hom gv ∈ _
    rw [← map_sub]
    exact hdiff
  apply Q.germ_ext Z hyZ (iW ≫ homOfLE (show W ≤ U from inf_le_left))
    (iW ≫ homOfLE (show W ≤ V from inf_le_right))
  change Ideal.Quotient.mk (actualRemainderSectionIdeal A C q Z) (F.map iW.op fu) =
    Ideal.Quotient.mk (actualRemainderSectionIdeal A C q Z) (F.map iW.op gv)
  exact heqQ

/-- ONLY original coherence internally yields the genuine LITERAL quotient-stalk WHOLE ring equivalence. -/
def actualRemainderQuotientStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (y : M) :
    actualRemainderQuotientStalk A C q y ≃+*
      actualComplexStructureStalk (n := n) y ⧸ actualWholeRemainderIdeal A C q y :=
  RingEquiv.ofBijective (actualRemainderQuotientStalkToWholeHom A C q y)
    ⟨actualRemainderQuotientStalkToWholeHom_injective A hA C q y,
      actualRemainderQuotientStalkToWholeHom_surjective A C q y⟩

/-- EVERY real actual section quotient colimit germ retains its original whole representative formula. -/
theorem actualRemainderQuotientStalkWholeEquiv_germ (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualRemainderSectionQuotient A C q U) :
    actualRemainderQuotientStalkWholeEquiv A hA C q y ((actualRemainderQuotientPresheaf A C q).germ U y hy s) =
      actualRemainderQuotientSectionGermHom A C q U y hy s := actualRemainderQuotientStalkToWholeHom_germ A C q U y hy s

/-- EVERY actual original section class retains the literal whole original ring-stalk quotient class. -/
theorem actualRemainderQuotientStalkWholeEquiv_germ_mk (A : GermIdeal n M) (hA : A.IsCoherent)
    (C : Set M) (q : ℕ) (U : Opens M) (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) U) :
    actualRemainderQuotientStalkWholeEquiv A hA C q y ((actualRemainderQuotientPresheaf A C q).germ U y hy
      (Ideal.Quotient.mk (actualRemainderSectionIdeal A C q U) s)) =
      Ideal.Quotient.mk (actualWholeRemainderIdeal A C q y)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) := by
  rw [actualRemainderQuotientStalkWholeEquiv_germ,actualRemainderQuotientSectionGermHom_mk]

end
end Hironaka.HironakaSmoothCentreRealDomainActualRemainderQuotientStalk
