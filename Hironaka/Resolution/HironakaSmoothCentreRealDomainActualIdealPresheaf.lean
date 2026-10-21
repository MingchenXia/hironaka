/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk
/-! Actual ideal section presheaves and their entire original colimit stalks.
Complete four-node mathematics precedes code. Original coherent membership
spreads on real original opens; no caller ideal/stalk certificate is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualIdealPresheaf
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  RelativePrincipalizationSpan InvertibleIdealQuotient
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
omit [IsComplexManifold n M] in
/-- Original coherent membership in the SAME function persists on genuine nearby ORIGINAL points. -/
theorem coherent_original_membership_eventually (A : GermIdeal n M) (hA : A.IsCoherent)
    (y : M) (f : M → ℂ) (hfy : A.mem y f) : ∀ᶠ z in 𝓝 y, A.mem z f := by
  obtain ⟨U,hU,hyU,N,g,hg,hmem⟩ := hA y
  obtain ⟨hf,K,s,a,hs,ha,heq⟩ := (hmem y hyU f).mp hfy
  have hall : ∀ᶠ z in 𝓝 y, ∀ i, HolomorphicAt n (a i) z :=
    eventually_all.mpr fun i => (ha i).eventually
  filter_upwards [hU.mem_nhds hyU,hf.eventually,hall,heq.eventually_nhds] with z hz hzf hza hzeq
  exact (hmem z hz f).mpr ⟨hzf,K,s,a,hs,hza,hzeq⟩

omit [IsComplexManifold n M] in
/-- A real ORIGINAL open, not a stalk-generation certificate, is internally supplied. -/
theorem coherent_original_membership_exists_open (A : GermIdeal n M) (hA : A.IsCoherent)
    (y : M) (f : M → ℂ) (hfy : A.mem y f) :
    ∃ V : Opens M, y ∈ V ∧ ∀ z∈V, A.mem z f := by
  obtain ⟨V,hVmem,hVopen,hyV⟩ := mem_nhds_iff.mp
    (coherent_original_membership_eventually A hA y f hfy)
  exact ⟨⟨V,hVopen⟩,hyV,hVmem⟩

/-- ALL actual sections whose ACTUAL germs lie in the ENTIRE original ideal at EVERY included point. -/
def actualSectionIdeal (A : GermIdeal n M) (U : Opens M) :
    Ideal (actualComplexSection (n := n) U) where
  carrier := {s | ∀ (y : M) (hy : y ∈ U),
    (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s ∈
      actualWholeSheafStalkIdeal A y}
  zero_mem' := by
    intro y hy
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom 0 ∈ _
    rw [map_zero]
    exact (actualWholeSheafStalkIdeal A y).zero_mem
  add_mem' := by
    intro s t hs ht y hy
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom (s+t) ∈ _
    rw [map_add]
    exact (actualWholeSheafStalkIdeal A y).add_mem (hs y hy) (ht y hy)
  smul_mem' := by
    intro r s hs y hy
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom (r*s) ∈ _
    rw [map_mul]
    exact (actualWholeSheafStalkIdeal A y).mul_mem_left _ (hs y hy)

/-- Literal actual restriction preserves every pointwise whole original ideal condition. -/
theorem actualSectionIdeal_restrict (A : GermIdeal n M) (U V : Opens M)
    (hUV : U ≤ V) (s : actualComplexSection (n := n) V) (hs : s ∈ actualSectionIdeal A V) :
    (actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s ∈
      actualSectionIdeal A U := by
  intro y hy
  rw [(actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply (homOfLE hUV) y hy s]
  exact hs y (hUV hy)

/-- The real restriction additive homomorphism on the actual ideal sections. -/
def actualIdealSectionRestrict (A : GermIdeal n M) (U V : Opens M) (hUV : U ≤ V) :
    actualSectionIdeal A V →+ actualSectionIdeal A U where
  toFun s := ⟨(actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s.val,
    actualSectionIdeal_restrict A U V hUV s.val s.property⟩
  map_zero' := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op).hom.map_add s.val t.val

/-- The literal actual ideal section presheaf on ALL genuine original opens. -/
def actualIdealSectionPresheaf (A : GermIdeal n M) : (TopCat.of M).Presheaf AddCommGrpCat where
  obj U := AddCommGrpCat.of (actualSectionIdeal A (unop U))
  map i := AddCommGrpCat.ofHom (actualIdealSectionRestrict A _ _ (leOfHom i.unop))
  map_id := by
    intro U
    ext s
    rfl
  map_comp := by
    intro U V W i j
    ext s
    rfl

/-- This is the ACTUAL ideal section presheaf neighbourhood COLIMIT stalk. -/
abbrev actualIdealSectionStalk (A : GermIdeal n M) (y : M) : Type :=
  ((actualIdealSectionPresheaf A).stalk y).carrier

/-- EVERY actual ideal section maps to its original whole structure-sheaf germ. -/
def actualIdealSectionGermHom (A : GermIdeal n M) (U : Opens M) (y : M) (hy : y ∈ U) :
    actualSectionIdeal A U →+ actualWholeSheafStalkIdeal A y where
  toFun s := ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s.val,s.property y hy⟩
  map_zero' := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy).hom.map_add s.val t.val

/-- TRUE actual ideal section germ homomorphisms form the genuine restriction cocone. -/
def actualIdealSectionGermCocone (A : GermIdeal n M) (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualIdealSectionPresheaf A) where
  pt := AddCommGrpCat.of (actualWholeSheafStalkIdeal A y)
  ι := {
    app := fun U => AddCommGrpCat.ofHom (actualIdealSectionGermHom A (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext s
      apply Subtype.ext
      change (actualComplexStructureSheaf (n := n) M).presheaf.germ (unop V).val y (unop V).property
        ((actualComplexStructureSheaf (n := n) M).presheaf.map
          (homOfLE (leOfHom i.unop)).op s.val) =
        (actualComplexStructureSheaf (n := n) M).presheaf.germ (unop U).val y (unop U).property s.val
      exact (actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (leOfHom i.unop)) y (unop V).property s.val }

/-- The genuine ideal COLIMIT universal property INTERNALLY supplies the whole stalk additive map. -/
def actualIdealStalkToWholeHom (A : GermIdeal n M) (y : M) :
    actualIdealSectionStalk A y →+ actualWholeSheafStalkIdeal A y :=
  (colimit.desc _ (actualIdealSectionGermCocone A y)).hom

/-- EVERY actual ideal section germ retains its genuine ORIGINAL structure-sheaf formula. -/
theorem actualIdealStalkToWholeHom_germ (A : GermIdeal n M) (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualSectionIdeal A U) :
    actualIdealStalkToWholeHom A y ((actualIdealSectionPresheaf A).germ U y hy s) =
      actualIdealSectionGermHom A U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙ actualIdealSectionPresheaf A
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫ colimit.desc D (actualIdealSectionGermCocone A y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- Actual ring colimit equality gives true common open equality; no ideal stalk injectivity is supplied. -/
theorem actualIdealStalkToWholeHom_injective (A : GermIdeal n M) (y : M) :
    Function.Injective (actualIdealStalkToWholeHom A y) := by
  intro a b hab
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  obtain ⟨U,hyU,s,rfl⟩ := (actualIdealSectionPresheaf A).exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := (actualIdealSectionPresheaf A).exists_germ_eq b
  change actualSectionIdeal A U at s
  change actualSectionIdeal A V at t
  rw [actualIdealStalkToWholeHom_germ A U y hyU s,actualIdealStalkToWholeHom_germ A V y hyV t] at hab
  have hval : F.germ U y hyU s.val = F.germ V y hyV t.val := congrArg Subtype.val hab
  obtain ⟨W,hyW,iU,iV,heq⟩ := F.germ_eq y hyU hyV s.val t.val hval
  apply (actualIdealSectionPresheaf A).germ_ext W hyW iU iV
  apply Subtype.ext
  exact heq

omit [IsComplexManifold n M] in
/-- Genuine restriction extensions agree with the SAME original section near EVERY included point. -/
theorem sectionExtension_restrict_eventuallyEq (U V : Opens M) (hUV : U ≤ V)
    (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) V) :
    sectionExtension U ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s) =ᶠ[𝓝 y]
      sectionExtension V s := by
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  rw [sectionExtension_apply U _ z hz,sectionExtension_apply V s z (hUV hz)]
  rfl

/-- EACH original coherent membership germ is represented by a TRUE ideal section on a genuine original open. -/
private theorem exists_actual_ideal_section_of_spreading_member (A : GermIdeal n M) (y : M)
    (hspread : ∀ f, A.mem y f → ∀ᶠ z in 𝓝 y, A.mem z f)
    (f : M → ℂ) (hf : HolomorphicAt n f y) (hfy : A.mem y f) :
    ∃ (W : Opens M) (hyW : y ∈ W) (s : actualSectionIdeal A W),
      (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW s.val =
        actualOriginalFunctionGerm y f hf := by
  obtain ⟨V₀,hVmem,hVopen,hyV⟩ := mem_nhds_iff.mp (hspread f hfy)
  let V : Opens M := ⟨V₀,hVopen⟩
  obtain ⟨U,hyU,t,hsec⟩ := exists_actual_section_of_original_holomorphicAt y f hf
  obtain ⟨Q,hQeq,hQopen,hyQ⟩ := mem_nhds_iff.mp hsec
  let W : Opens M := ⟨Q ∩ V ∩ U,(hQopen.inter V.isOpen).inter U.isOpen⟩
  have hyW : y ∈ W := ⟨⟨hyQ,hyV⟩,hyU⟩
  have hWU : W ≤ U := fun _ hz => hz.2
  let s := (actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hWU).op t
  have heq : ∀ (z : M) (_hz : z ∈ W), sectionExtension W s =ᶠ[𝓝 z] f := by
    intro z hz
    filter_upwards [W.isOpen.mem_nhds hz] with p hp
    rw [sectionExtension_apply W s p hp]
    change t ⟨p,hWU hp⟩ = f p
    exact (sectionExtension_apply U t p (hWU hp)).symm.trans (hQeq hp.1.1)
  have hs : s ∈ actualSectionIdeal A W := by
    intro z hz
    have hzf := hVmem hz.1.2
    have hfz := (sectionExtension_holomorphicAt W s z hz).congr (heq z hz)
    rw [← actualOriginalFunctionGerm_eq_section W z hz s f hfz (heq z hz)]
    exact Ideal.subset_span ⟨f,hfz,hzf,rfl⟩
  refine ⟨W,hyW,⟨s,hs⟩,?_⟩
  exact (actualOriginalFunctionGerm_eq_section W y hyW s f hf (heq y hyW)).symm

/-- Original coherence internally supplies the real membership spreading used for EVERY actual ideal section representative. -/
theorem exists_actual_ideal_section_of_original_member (A : GermIdeal n M) (hA : A.IsCoherent)
    (y : M) (f : M → ℂ) (hf : HolomorphicAt n f y) (hfy : A.mem y f) :
    ∃ (W : Opens M) (hyW : y ∈ W) (s : actualSectionIdeal A W),
      (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW s.val =
        actualOriginalFunctionGerm y f hf :=
  exists_actual_ideal_section_of_spreading_member A y
    (fun g hg => coherent_original_membership_eventually A hA y g hg) f hf hfy

/-- The genuine actual ideal-section germ image is an ideal, with ALL scalar representatives on true common opens. -/
def actualIdealSectionGermImage (A : GermIdeal n M) (y : M) :
    Ideal (actualComplexStructureStalk (n := n) y) where
  carrier := {g | ∃ (U : Opens M) (hy : y ∈ U) (s : actualSectionIdeal A U),
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
    let su := actualIdealSectionRestrict A W U inf_le_left s
    let tv := actualIdealSectionRestrict A W V inf_le_right t
    refine ⟨W,hyW,su+tv,?_⟩
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (su.val+tv.val) = g+h
    rw [map_add]
    have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = g := by
      exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans hgs
    have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv.val = h := by
      exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ V from inf_le_right)) y hyW t.val).trans hht
    rw [hs,ht]
  smul_mem' := by
    intro r g hg
    obtain ⟨U,hyU,s,hgs⟩ := hg
    obtain ⟨V,hyV,t,hrt⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
    let W : Opens M := U ⊓ V
    have hyW : y ∈ W := ⟨hyU,hyV⟩
    let su := actualIdealSectionRestrict A W U inf_le_left s
    let tv := (actualComplexStructureSheaf (n := n) M).presheaf.map
      (homOfLE (show W ≤ V from inf_le_right)).op t
    let v : actualSectionIdeal A W := ⟨tv*su.val,(actualSectionIdeal A W).mul_mem_left tv su.property⟩
    refine ⟨W,hyW,v,?_⟩
    change ((actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW).hom (tv*su.val) = r*g
    rw [map_mul]
    have hs : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW su.val = g := by
      exact ((actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ U from inf_le_left)) y hyW s.val).trans hgs
    have ht : (actualComplexStructureSheaf (n := n) M).presheaf.germ W y hyW tv = r := by
      rw [(actualComplexStructureSheaf (n := n) M).presheaf.germ_res_apply
        (homOfLE (show W ≤ V from inf_le_right)) y hyW t]
      exact hrt
    rw [ht,hs]

/-- Original coherence supplies BOTH entire inclusions, not merely a chosen finite generator image. -/
private theorem actualIdealSectionGermImage_eq_whole_of_spreading (A : GermIdeal n M) (y : M)
    (hspread : ∀ f, A.mem y f → ∀ᶠ z in 𝓝 y, A.mem z f) :
    actualIdealSectionGermImage A y = actualWholeSheafStalkIdeal A y := by
  apply le_antisymm
  · rintro g ⟨U,hyU,s,hgs⟩
    rw [← hgs]
    exact s.property y hyU
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hfy,rfl⟩
    obtain ⟨U,hyU,s,heq⟩ := exists_actual_ideal_section_of_spreading_member A y hspread f hf hfy
    exact ⟨U,hyU,s,heq⟩

/-- Original coherence internally supplies the ENTIRE actual ideal section germ image. -/
theorem actualIdealSectionGermImage_eq_whole (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    actualIdealSectionGermImage A y = actualWholeSheafStalkIdeal A y :=
  actualIdealSectionGermImage_eq_whole_of_spreading A y
    (fun f hf => coherent_original_membership_eventually A hA y f hf)

/-- EVERY original whole ideal element has an actual ideal-presheaf COLIMIT preimage internally. -/
private theorem actualIdealStalkToWholeHom_surjective_of_spreading (A : GermIdeal n M) (y : M)
    (hspread : ∀ f, A.mem y f → ∀ᶠ z in 𝓝 y, A.mem z f) :
    Function.Surjective (actualIdealStalkToWholeHom A y) := by
  intro g
  have hg : g.val ∈ actualIdealSectionGermImage A y := by
    rw [actualIdealSectionGermImage_eq_whole_of_spreading A y hspread]
    exact g.property
  obtain ⟨U,hyU,s,heq⟩ := hg
  refine ⟨(actualIdealSectionPresheaf A).germ U y hyU s,?_⟩
  rw [actualIdealStalkToWholeHom_germ A U y hyU s]
  apply Subtype.ext
  exact heq

/-- Original coherence internally proves genuine actual ideal-colimit representative surjectivity. -/
theorem actualIdealStalkToWholeHom_surjective (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    Function.Surjective (actualIdealStalkToWholeHom A y) :=
  actualIdealStalkToWholeHom_surjective_of_spreading A y
    (fun f hf => coherent_original_membership_eventually A hA y f hf)

/-- The true actual ideal presheaf colimit is INTERNALLY equivalent to the ENTIRE original stalk ideal. -/
def actualIdealStalkWholeEquiv (A : GermIdeal n M) (hA : A.IsCoherent) (y : M) :
    actualIdealSectionStalk A y ≃+ actualWholeSheafStalkIdeal A y :=
  AddEquiv.ofBijective (actualIdealStalkToWholeHom A y)
    ⟨actualIdealStalkToWholeHom_injective A y,actualIdealStalkToWholeHom_surjective A hA y⟩

/-- EVERY actual ideal section germ has the SAME original value under the genuine whole stalk equivalence. -/
theorem actualIdealStalkWholeEquiv_germ (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (y : M) (hy : y ∈ U) (s : actualSectionIdeal A U) :
    actualIdealStalkWholeEquiv A hA y ((actualIdealSectionPresheaf A).germ U y hy s) =
      actualIdealSectionGermHom A U y hy s := actualIdealStalkToWholeHom_germ A U y hy s

omit [IsComplexManifold n M] in
/-- Original centre vanishing membership spreads on REAL original points, with NO global centre coherence premise. -/
theorem vanishing_original_membership_eventually (C : Set M) (y : M) (f : M → ℂ)
    (hf : (vanishingIdeal (n := n) C).mem y f) :
    ∀ᶠ z in 𝓝 y, (vanishingIdeal (n := n) C).mem z f := by
  filter_upwards [hf.1.eventually,hf.2.eventually_nhds] with z hhol hvan
  exact ⟨hhol,hvan⟩

/-- BOTH ENTIRE centre ideal germ-image inclusions follow internally from actual vanishing membership. -/
theorem actualCentreIdealSectionGermImage_eq_whole (C : Set M) (y : M) :
    actualIdealSectionGermImage (vanishingIdeal (n := n) C) y =
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  actualIdealSectionGermImage_eq_whole_of_spreading _ y
    (fun f hf => vanishing_original_membership_eventually C y f hf)

/-- EVERY actual original centre ideal stalk element has a genuine ideal-section COLIMIT preimage, internally. -/
theorem actualCentreIdealStalkToWholeHom_surjective (C : Set M) (y : M) :
    Function.Surjective (actualIdealStalkToWholeHom (vanishingIdeal (n := n) C) y) :=
  actualIdealStalkToWholeHom_surjective_of_spreading _ y
    (fun f hf => vanishing_original_membership_eventually C y f hf)

/-- The ACTUAL centre ideal presheaf colimit is the ENTIRE original centre ideal, without a global coherence extension. -/
def actualCentreIdealStalkWholeEquiv (C : Set M) (y : M) :
    actualIdealSectionStalk (vanishingIdeal (n := n) C) y ≃+
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y :=
  AddEquiv.ofBijective (actualIdealStalkToWholeHom _ y)
    ⟨actualIdealStalkToWholeHom_injective _ y,actualCentreIdealStalkToWholeHom_surjective C y⟩

/-- EVERY real actual centre ideal section germ retains its original whole germ formula. -/
theorem actualCentreIdealStalkWholeEquiv_germ (C : Set M) (U : Opens M) (y : M)
    (hy : y ∈ U) (s : actualSectionIdeal (vanishingIdeal (n := n) C) U) :
    actualCentreIdealStalkWholeEquiv C y ((actualIdealSectionPresheaf _).germ U y hy s) =
      actualIdealSectionGermHom (vanishingIdeal (n := n) C) U y hy s :=
  actualIdealStalkToWholeHom_germ _ U y hy s

end
end Hironaka.HironakaSmoothCentreRealDomainActualIdealPresheaf
