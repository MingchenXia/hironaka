/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The strict transform at the first containing centre is a component of the centre

In the proof of [Kol07, Corollary 22], at the first blow-up whose centre `Z_j` contains the strict
transform `X̄_j` of `X`, the image `π_0 ⋯ π_{j−1}(Z_j)` lies in `X̄`, so `η_X` is the generic
point of `Z_j`: the resolution of `X` is the component of the smooth centre through the generic
point. This file proves that identification in general form, as a lemma about closed subschemes:

* on any scheme `B` with a Noetherian underlying space, for closed subschemes `V(T) ⊆ V(Z)`
  (`Z ≤ T`) with `V(T)` integral, `V(Z)` regular (every stalk a regular local ring), and the
  generic point `η'` of `V(T)` maximal in `V(Z)` (no point of `V(Z)` generalises it), the
  inclusion `V(T) ⟶ V(Z)` is an open immersion: `V(T)` is the irreducible component of `V(Z)`
  through `η'`, and the irreducible components of a regular Noetherian scheme are open (they are
  pairwise disjoint, a regular local ring having a single minimal prime);
* along a blow-up sequence on a Noetherian scheme `A`, at the first centre `Z_j` containing the
  strict transform `X̄_j` of an integral `V(I)`, the hypotheses hold when `Z_j` is regular and lies
  over `V(I)`: `η_j` is the unique point over `η`
  (`Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter`), so a point of `Z_j` generalising `η_j`
  maps to a point of `V(I)` generalising `η`, which is `η`, hence it is `η_j`
  (`isOpenImmersion_inclusion_of_firstCenterIndex`).

The smoothness of the end result of the affine resolution then follows, since an open subscheme
of a smooth scheme is smooth (`smooth_subschemeι_comp_of_isOpenImmersion_inclusion`; see
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult`).

## Conventions

`IsRegular` means that every stalk is a regular local ring (`Hironaka.RegularSmooth`);
`Closeds.genericPoints` is the set of points of a closed subset maximal for specialisation;
`IdealSheafData.inclusion hle : T.subscheme ⟶ Z.subscheme` is Mathlib's inclusion of closed
subschemes for `hle : Z ≤ T`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

/-! ### Irreducible components of a Noetherian space with pairwise disjoint components are open -/

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- In a Noetherian space whose irreducible components are pairwise disjoint, every irreducible
component is open: its complement is the finite union of the other (closed) components. -/
theorem isOpen_irreducibleComponent_of_inter_nonempty_imp_eq [NoetherianSpace α]
    (h : ∀ C₁ ∈ irreducibleComponents α, ∀ C₂ ∈ irreducibleComponents α,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂) (x : α) : IsOpen (irreducibleComponent x) := by
  set 𝒟 : Set (Set α) := {D | D ∈ irreducibleComponents α ∧ D ≠ irreducibleComponent x} with h𝒟
  have hfin : 𝒟.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun D hD => hD.1
  have hcl : IsClosed (⋃ D ∈ 𝒟, D) :=
    hfin.isClosed_biUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1
  have heq : irreducibleComponent x = (⋃ D ∈ 𝒟, D)ᶜ := by
    ext y
    constructor
    · intro hy hmem
      obtain ⟨D, hD, hyD⟩ := Set.mem_iUnion₂.mp hmem
      exact hD.2 (h D hD.1 _ (irreducibleComponent_mem_irreducibleComponents x) ⟨y, hyD, hy⟩)
    · intro hy
      by_cases hxy : irreducibleComponent y = irreducibleComponent x
      · rw [← hxy]; exact mem_irreducibleComponent
      · exact absurd (Set.mem_iUnion₂.mpr ⟨irreducibleComponent y,
          ⟨irreducibleComponent_mem_irreducibleComponents y, hxy⟩, mem_irreducibleComponent⟩) hy
  rw [heq]
  exact hcl.isOpen_compl

end Topology

/-! ### Regular closed subschemes: disjoint components, reducedness -/

section Regular

variable {B : Scheme.{u}}

/-- The image in `B` of the generic point of an irreducible component of the closed subscheme
`V(Z)` is a maximal point of its support (`Closeds.genericPoints`). -/
theorem mem_genericPoints_support_of_isGenericPoint_of_mem_irreducibleComponents
    (Z : B.IdealSheafData) {C : Set Z.subscheme} (hC : C ∈ irreducibleComponents Z.subscheme)
    {ξ : Z.subscheme} (hξ : IsGenericPoint ξ C) : Z.subschemeι ξ ∈ Z.support.genericPoints := by
  refine ⟨?_, fun ξ' hξ' hspec => ?_⟩
  · have h : Z.subschemeι ξ ∈ Set.range Z.subschemeι := ⟨ξ, rfl⟩
    rwa [Z.range_subschemeι] at h
  · have hξ'r : ξ' ∈ Set.range Z.subschemeι := by rw [Z.range_subschemeι]; exact hξ'
    obtain ⟨ζ, rfl⟩ := hξ'r
    have hζ : ζ ⤳ ξ :=
      (Scheme.Hom.isClosedEmbedding Z.subschemeι).isInducing.specializes_iff.mp hspec
    rw [eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hC hξ hζ]

/-- Two irreducible components of a regular closed subscheme meeting at a point coincide: their
generic points are maximal points of the support specialising to a common point, hence equal
(`Hironaka.Sequence.eq_of_specializes_of_isRegular`). -/
theorem eq_of_mem_irreducibleComponents_of_isRegular (Z : B.IdealSheafData)
    (hZ : IsRegular Z.subscheme) {C₁ C₂ : Set Z.subscheme}
    (h₁ : C₁ ∈ irreducibleComponents Z.subscheme) (h₂ : C₂ ∈ irreducibleComponents Z.subscheme)
    (hne : (C₁ ∩ C₂).Nonempty) : C₁ = C₂ := by
  obtain ⟨c, hc₁, hc₂⟩ := hne
  have hirr₁ : IsIrreducible C₁ := h₁.1
  have hirr₂ : IsIrreducible C₂ := h₂.1
  have hcl₁ : IsClosed C₁ := isClosed_of_mem_irreducibleComponents C₁ h₁
  have hcl₂ : IsClosed C₂ := isClosed_of_mem_irreducibleComponents C₂ h₂
  have hξ₁ := hirr₁.isGenericPoint_genericPoint hcl₁
  have hξ₂ := hirr₂.isGenericPoint_genericPoint hcl₂
  have hm₁ := mem_genericPoints_support_of_isGenericPoint_of_mem_irreducibleComponents Z h₁ hξ₁
  have hm₂ := mem_genericPoints_support_of_isGenericPoint_of_mem_irreducibleComponents Z h₂ hξ₂
  have hs₁ : Z.subschemeι hirr₁.genericPoint ⤳ Z.subschemeι c :=
    (hξ₁.specializes hc₁).map Z.subschemeι.continuous
  have hs₂ : Z.subschemeι hirr₂.genericPoint ⤳ Z.subschemeι c :=
    (hξ₂.specializes hc₂).map Z.subschemeι.continuous
  have heq := Hironaka.Sequence.eq_of_specializes_of_isRegular _ hZ hm₁ hm₂ hs₁ hs₂
  have heq' : hirr₁.genericPoint = hirr₂.genericPoint :=
    (Scheme.Hom.isClosedEmbedding Z.subschemeι).injective heq
  calc C₁ = closure {hirr₁.genericPoint} := hξ₁.def.symm
    _ = closure {hirr₂.genericPoint} := by rw [heq']
    _ = C₂ := hξ₂.def

/-- A regular scheme is reduced (regular local rings are domains). -/
theorem isReduced_of_isRegular (hB : IsRegular B) : IsReduced B := by
  have : ∀ x : B, _root_.IsReduced (B.presheaf.stalk x) := fun x => by
    have : IsRegularLocalRing (B.presheaf.stalk x) := hB.isRegularAt x
    infer_instance
  exact isReduced_of_isReduced_stalk B

/-- The underlying space of a closed subscheme of a Noetherian space is Noetherian. -/
theorem noetherianSpace_subscheme [NoetherianSpace B] (Z : B.IdealSheafData) :
    NoetherianSpace Z.subscheme :=
  (noetherianSpace_iff_of_homeomorph
    (Scheme.Hom.isClosedEmbedding Z.subschemeι).isEmbedding.toHomeomorph).mpr
    (NoetherianSpace.set _)

/-- Every irreducible component of a regular closed subscheme of a Noetherian scheme is open. -/
theorem isOpen_irreducibleComponent_of_isRegular [NoetherianSpace B] (Z : B.IdealSheafData)
    (hZ : IsRegular Z.subscheme) (z : Z.subscheme) : IsOpen (irreducibleComponent z) := by
  have := noetherianSpace_subscheme Z
  exact isOpen_irreducibleComponent_of_inter_nonempty_imp_eq
    (fun C₁ h₁ C₂ h₂ hne => eq_of_mem_irreducibleComponents_of_isRegular Z hZ h₁ h₂ hne) z

end Regular

/-! ### The identification -/

section Identification

variable {B : Scheme.{u}}

/-- A closed immersion into a reduced scheme whose range is open is an open immersion: restricted
over its range it is a surjective closed immersion onto a reduced scheme, hence an isomorphism
(`isIso_of_isClosedImmersion_of_surjective`). -/
theorem isOpenImmersion_of_isClosedImmersion_of_isOpen_range {W : Scheme.{u}} (ι : W ⟶ B)
    [IsClosedImmersion ι] [IsReduced B] (hopen : IsOpen (Set.range ι)) : IsOpenImmersion ι := by
  set C : B.Opens := ⟨Set.range ι, hopen⟩ with hC
  have hres : IsClosedImmersion (ι ∣_ C) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› C
  have hsurj : Surjective (ι ∣_ C) := by
    refine ⟨fun c => ?_⟩
    obtain ⟨t, ht⟩ := c.2
    have htC : t ∈ ι ⁻¹ᵁ C := by
      change ι t ∈ (C : Set B)
      rw [ht]; exact c.2
    refine ⟨⟨t, htC⟩, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe ι C ⟨t, htC⟩).trans ht
  have hredC : IsReduced C := isReduced_of_isOpenImmersion C.ι
  have hiso : IsIso (ι ∣_ C) := isIso_of_isClosedImmersion_of_surjective _
  have hcomp : IsOpenImmersion ((ι ⁻¹ᵁ C).ι ≫ ι) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hpre : ι ⁻¹ᵁ C = ⊤ := by
    rw [eq_top_iff]
    intro t _
    exact ⟨t, rfl⟩
  have hιC : IsIso (ι ⁻¹ᵁ C).ι := by
    rw [hpre, ← Scheme.topIso_hom]
    infer_instance
  have heq : ι = inv (ι ⁻¹ᵁ C).ι ≫ ((ι ⁻¹ᵁ C).ι ≫ ι) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- The identification in general form [Kol07, Corollary 22, proof]: for closed subschemes
`V(T) ⊆ V(Z)` of a Noetherian scheme with `V(Z)` regular and the generic point `η'` of `V(T)` a
maximal point of `V(Z)`, the inclusion `V(T) ⟶ V(Z)` is an open immersion: `V(T)` is the
irreducible component of `V(Z)` through `η'`. -/
theorem isOpenImmersion_inclusion_of_isGenericPoint [NoetherianSpace B] (Z T : B.IdealSheafData)
    (hle : Z ≤ T) (hZ : IsRegular Z.subscheme) {η' : B}
    (hη' : IsGenericPoint η' (T.support : Set B)) (hmax : η' ∈ Z.support.genericPoints) :
    IsOpenImmersion (IdealSheafData.inclusion hle) := by
  set ι := IdealSheafData.inclusion hle with hι
  have hιZ : ι ≫ Z.subschemeι = T.subschemeι := IdealSheafData.inclusion_subschemeι hle
  have hinj : Function.Injective Z.subschemeι :=
    (Scheme.Hom.isClosedEmbedding Z.subschemeι).injective
  have hind := (Scheme.Hom.isClosedEmbedding Z.subschemeι).isInducing
  have hιapp : ∀ t : T.subscheme, Z.subschemeι (ι t) = T.subschemeι t := fun t => by
    rw [← hιZ]; rfl
  -- the closed immersion `ι`
  have hci : IsClosedImmersion ι := by
    have : IsClosedImmersion (ι ≫ Z.subschemeι) := by rw [hιZ]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion ι Z.subschemeι
  -- the point `z₀` of `V(Z)` over `η'`
  have hη'r : η' ∈ Set.range Z.subschemeι := by rw [Z.range_subschemeι]; exact hmax.1
  obtain ⟨z₀, hz₀⟩ := hη'r
  -- the range of `ι` is the irreducible component of `z₀`
  have hrange : Set.range ι = irreducibleComponent z₀ := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨t, rfl⟩
      have h1 : T.subschemeι t ∈ T.support := by
        have h : T.subschemeι t ∈ Set.range T.subschemeι := ⟨t, rfl⟩
        rwa [T.range_subschemeι] at h
      have h2 : η' ⤳ T.subschemeι t := hη'.specializes h1
      have h3 : Z.subschemeι z₀ ⤳ Z.subschemeι (ι t) := by rw [hz₀, hιapp]; exact h2
      have h4 : z₀ ⤳ ι t := hind.specializes_iff.mp h3
      exact closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
        isClosed_irreducibleComponent (specializes_iff_mem_closure.mp h4)
    · intro c hc
      have hirr : IsIrreducible (irreducibleComponent z₀) := isIrreducible_irreducibleComponent
      have hcl : IsClosed (irreducibleComponent z₀) := isClosed_irreducibleComponent
      have hξ := hirr.isGenericPoint_genericPoint hcl
      set ξ := hirr.genericPoint with hξdef
      have hξz₀ : ξ ⤳ z₀ := hξ.specializes mem_irreducibleComponent
      have hξc : ξ ⤳ c := hξ.specializes hc
      have hξZ : Z.subschemeι ξ ∈ Z.support := by
        have h : Z.subschemeι ξ ∈ Set.range Z.subschemeι := ⟨ξ, rfl⟩
        rwa [Z.range_subschemeι] at h
      have hξη' : Z.subschemeι ξ ⤳ η' := hz₀ ▸ hξz₀.map Z.subschemeι.continuous
      have hξeq : Z.subschemeι ξ = η' := hmax.2 hξZ hξη'
      have hξz₀' : ξ = z₀ := hinj (hξeq.trans hz₀.symm)
      have h5 : η' ⤳ Z.subschemeι c := hz₀ ▸ (hξz₀' ▸ hξc).map Z.subschemeι.continuous
      have h6 : Z.subschemeι c ∈ T.support := by
        have h := specializes_iff_mem_closure.mp h5
        rwa [hη'.def] at h
      have h7 : Z.subschemeι c ∈ Set.range T.subschemeι := by rw [T.range_subschemeι]; exact h6
      obtain ⟨t, ht⟩ := h7
      refine ⟨t, hinj ?_⟩
      rw [hιapp, ht]
  -- the component is open, `V(Z)` is reduced
  have hopen : IsOpen (irreducibleComponent z₀) := isOpen_irreducibleComponent_of_isRegular Z hZ z₀
  have hred : IsReduced Z.subscheme := isReduced_of_isRegular hZ
  set C : Z.subscheme.Opens := ⟨irreducibleComponent z₀, hopen⟩ with hC
  -- `ι` restricted over `C` is a surjective closed immersion onto the reduced `C`, hence an iso
  have hres : IsClosedImmersion (ι ∣_ C) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) hci C
  have hsurj : Surjective (ι ∣_ C) := by
    refine ⟨fun c => ?_⟩
    have hc : c.1 ∈ Set.range ι := by rw [hrange]; exact c.2
    obtain ⟨t, ht⟩ := hc
    have htC : t ∈ ι ⁻¹ᵁ C := by
      change ι t ∈ (C : Set Z.subscheme)
      rw [ht]; exact c.2
    refine ⟨⟨t, htC⟩, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe ι C ⟨t, htC⟩).trans ht
  have hredC : IsReduced C := isReduced_of_isOpenImmersion C.ι
  have hiso : IsIso (ι ∣_ C) := isIso_of_isClosedImmersion_of_surjective _
  -- `(ι ⁻¹ᵁ C).ι ≫ ι = (ι ∣_ C) ≫ C.ι` is an open immersion, and `(ι ⁻¹ᵁ C).ι` is an iso
  have hcomp : IsOpenImmersion ((ι ⁻¹ᵁ C).ι ≫ ι) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hpre : ι ⁻¹ᵁ C = ⊤ := by
    rw [eq_top_iff]
    intro t _
    change ι t ∈ (C : Set Z.subscheme)
    rw [hC]
    change ι t ∈ irreducibleComponent z₀
    rw [← hrange]
    exact ⟨t, rfl⟩
  have hιC : IsIso (ι ⁻¹ᵁ C).ι := by
    rw [hpre, ← Scheme.topIso_hom]
    infer_instance
  have heq : ι = inv (ι ⁻¹ᵁ C).ι ≫ ((ι ⁻¹ᵁ C).ι ≫ ι) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- An open subscheme of a smooth scheme is smooth: if the inclusion `V(T) ⟶ V(Z)` is an open
immersion and `V(Z)` is smooth over `Y`, so is `V(T)` ("`Z_j` is smooth since we blow it up",
[Kol07, Corollary 22, proof]; the component `X̄_j` of `Z_j` inherits the smoothness). -/
theorem smooth_subschemeι_comp_of_isOpenImmersion_inclusion {Z T : B.IdealSheafData} (hle : Z ≤ T)
    [IsOpenImmersion (IdealSheafData.inclusion hle)] {Y : Scheme.{u}} (g : B ⟶ Y) [Smooth
        (Z.subschemeι ≫ g)] :
    Smooth (T.subschemeι ≫ g) := by
  rw [← IdealSheafData.inclusion_subschemeι hle, Category.assoc]
  exact MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance

end Identification

/-! ### Noetherian stages -/

section Stages

variable {A : Scheme.{u}}

/-- The stages of a blow-up sequence on a Noetherian scheme are Noetherian
(`blowUp.isNoetherian`). -/
theorem isNoetherian_stage_mk (hA : IsNoetherian A) (S : BlowUpSequence A) (n : ℕ)
    (hn : n < S.length + 1) : IsNoetherian (S.stage ⟨n, hn⟩) := by
  induction S generalizing n with
  | nil X =>
    have h0 : (nil X).length = 0 := rfl
    obtain rfl : n = 0 := by omega
    exact hA
  | cons X D rest ih =>
    cases n with
    | zero => exact hA
    | succ n =>
      have hB : IsNoetherian D.blowUp := IdealSheafData.blowUp.isNoetherian D
      exact ih hB n (Nat.lt_of_succ_lt_succ hn)

/-- `isNoetherian_stage_mk` in the `Fin` form. -/
theorem isNoetherian_stage [hA : IsNoetherian A] (S : BlowUpSequence A) (i : Fin (S.length + 1)) :
    IsNoetherian (S.stage i) := by
  obtain ⟨n, hn⟩ := i
  exact isNoetherian_stage_mk hA S n hn

end Stages

/-! ### At the first containing centre -/

section FirstCenter

variable {A : Scheme.{u}}

/-- "`η_X` is the generic point of `Z_j`" [Kol07, Corollary 22, proof]: along a blow-up sequence on
a Noetherian scheme, at the first centre `Z_j` containing the strict transform `X̄_j` of an
integral closed subscheme `V(I)`, if `Z_j` is regular and lies over `V(I)`, then `X̄_j` is an
irreducible component of `Z_j`: the inclusion `V(X̄_j) ⟶ V(Z_j)` is an open immersion. The generic
point `η_j` of `X̄_j` is the unique point of the stage over the generic point `η` of `V(I)`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter`), so a point of `Z_j` generalising `η_j`
maps to a point of `V(I)` generalising `η`, which is `η`; hence it is `η_j`, and
`isOpenImmersion_inclusion_of_isGenericPoint` applies. -/
theorem isOpenImmersion_inclusion_of_firstCenterIndex [IsNoetherian A] (S : BlowUpSequence A)
    (I : A.IdealSheafData) [IsIntegral I.subscheme] (j : Fin S.length)
    (hj : j.val = firstCenterIndex S I) (hle : S.center j ≤ S.strictTransformSeq I j.castSucc)
    (hZ : IsRegular (S.center j).subscheme)
    (hcos : ∀ y ∈ (S.center j).support, S.stageMap j.castSucc y ∈ I.support) :
    IsOpenImmersion (IdealSheafData.inclusion hle) := by
  have hLN : IsLocallyNoetherian A := inferInstance
  have hst : IsNoetherian (S.stage j.castSucc) := isNoetherian_stage S j.castSucc
  have hint : IsIntegral (S.strictTransformSeq I j.castSucc).subscheme :=
    isIntegral_strictTransformSeq_of_le_firstCenterIndex S I j.castSucc (le_of_eq hj)
  obtain ⟨η, hη⟩ := exists_isGenericPoint_support I
  obtain ⟨η', hgen, hmap, huniq⟩ :=
    exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex S I hη j.castSucc (le_of_eq hj)
  have hmax : η' ∈ (S.center j).support.genericPoints := by
    refine ⟨IdealSheafData.support_antitone hle hgen.mem, fun ξ hξ hspec => ?_⟩
    have h1 : S.stageMap j.castSucc ξ ⤳ S.stageMap j.castSucc η' :=
      hspec.map (S.stageMap j.castSucc).continuous
    rw [hmap] at h1
    have h2 : η ⤳ S.stageMap j.castSucc ξ := hη.specializes (hcos ξ hξ)
    exact huniq ξ (h1.antisymm h2).eq
  exact isOpenImmersion_inclusion_of_isGenericPoint (S.center j) _ hle hZ hgen hmax

end FirstCenter

end Hironaka.Resolution
