/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineAlgebra
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
public import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The affine charts of the blow-up: covers, membership and overlaps as sets

The chart statements of `Hironaka.Scheme.BlowUp.Glue.BlowUp` with images and preimages as sets,
together with two statements that rest on the universal property of the affine blow-up:

* the charts of any generating set of `I(U)` cover `π⁻¹(U)` — for generators `g₁, …, g_k` of
  `I` the blow-up is covered by the charts of the `gᵢ` [Hau14, Theorem 4.19] (from
  `affineBlowUp.exists_mem_opensRange_chart_of_span_eq` on the affine piece);
* the chart membership criterion for the blow-up [Sta, Tag 0BFL]: a point `x'` over `U` lies in
  the chart of `a ∈ I(U)` iff the image of `a` in `𝒪_{B,x'}` generates the stalk of the
  exceptional ideal — transported from the affine criterion (`affineBlowUp.mem_chart_iff`) along
  the open immersion `ι U : affineBlowUp (I.ideal U) ⟶ B`, whose stalk maps are isomorphisms, with
  the germ of `a` moved through `Spec Γ(X, U) → X` (`IsAffineOpen.fromSpec_app_self`).
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- As sets: the charts of all `a ∈ I(U)` cover `π⁻¹(U)`. -/
theorem Scheme.IdealSheafData.blowUp.iUnion_range_chart :
    ⋃ a : I.ideal U, Set.range (blowUp.chart I U a) = (blowUpπ I ⁻¹ᵁ U.1 : Set (blowUp I)) := by
  rw [← blowUp.iSup_opensRange_chart, Opens.coe_iSup]
  rfl

/-- Every chart of `U` lands in `π⁻¹(U)`. -/
theorem Scheme.IdealSheafData.blowUp.range_chart_subset (a : I.ideal U) :
    Set.range (blowUp.chart I U a) ⊆ (blowUpπ I ⁻¹ᵁ U.1 : Set (blowUp I)) := by
  rw [← blowUp.iUnion_range_chart]
  exact Set.subset_iUnion (fun a : I.ideal U => Set.range (blowUp.chart I U a)) a

/-- The charts of any generating set of `I(U)` cover `π⁻¹(U)` [Hau14, Theorem 4.19]. -/
theorem Scheme.IdealSheafData.blowUp.iUnion_range_chart_of_span_eq (s : Set (I.ideal U))
    (hs : Ideal.span (Subtype.val '' s) = I.ideal U) :
    ⋃ a ∈ s, Set.range (blowUp.chart I U a) = (blowUpπ I ⁻¹ᵁ U.1 : Set (blowUp I)) := by
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun a _ => blowUp.range_chart_subset I U a) ?_
  intro x' hx'
  have hx'' : x' ∈ (blowUp.ι I U).opensRange := by
    rw [blowUp.opensRange_ι]
    exact hx'
  obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx''
  obtain ⟨⟨z, hz⟩, hy⟩ :=
    affineBlowUp.exists_mem_opensRange_chart_of_span_eq (I.ideal U) (Subtype.val '' s) hs y
  obtain ⟨a, has, rfl⟩ := hz
  have hsub : ∀ h : (a : Γ(X, U)) ∈ I.ideal U, (⟨(a : Γ(X, U)), h⟩ : I.ideal U) = a :=
    fun _ => Subtype.ext rfl
  rw [hsub] at hy
  obtain ⟨w, hw⟩ := Scheme.Hom.mem_opensRange.mp hy
  refine Set.mem_iUnion₂.mpr ⟨a, has, w, ?_⟩
  rw [blowUp.chart_eq, Scheme.Hom.comp_apply, hw]

/-- As sets: inside the chart of `a` the chart of `b` is `D(b/a)`, with `b/a` the generator
`affineBlowUpAlgebra.frac`. -/
theorem Scheme.IdealSheafData.blowUp.preimage_range_chart (a b : I.ideal U) :
    blowUp.chart I U a ⁻¹' Set.range (blowUp.chart I U b) =
      (PrimeSpectrum.basicOpen (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2) :
        Set (PrimeSpectrum (affineBlowUpAlgebra (I.ideal U) a))) := by
  have h := congrArg SetLike.coe (blowUp.chart_preimage_chart I U a b)
  have hfrac : affineBlowUpAlgebra.ratio (I.ideal U) a b =
      affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2 :=
    Subtype.ext (affineBlowUpAlgebra.coe_frac_eq_awayFrac _).symm
  rw [hfrac] at h
  exact h

section Membership

/-- The stalk map of `fromSpec : Spec Γ(X, U) ⟶ X` sends the germ of `a ∈ Γ(X, U)` at `fromSpec p`
to the germ of `a` read as a global section of `Spec Γ(X, U)` (`fromSpec_app_self`). -/
theorem fromSpec_stalkMap_germ (p : Spec Γ(X, U))
    (hp : (affineOpens_isAffineOpen U).fromSpec p ∈ U.1) (a : Γ(X, U)) :
    (affineOpens_isAffineOpen U).fromSpec.stalkMap p
        (X.presheaf.germ U.1 ((affineOpens_isAffineOpen U).fromSpec p) hp a) =
      specGerm p a := by
  rw [Scheme.Hom.germ_stalkMap_apply, IsAffineOpen.fromSpec_app_self_apply, specGerm_apply]
  exact TopCat.Presheaf.germ_res_apply _
    (eqToHom (affineOpens_isAffineOpen U).fromSpec_preimage_self) p hp _

/-- The image of `a ∈ Γ(X, U)` in `𝒪_{B, ι y}`, transported to `𝒪_{affineBlowUp, y}` along the stalk
isomorphism of `ι U`, is the image of `a` under the affine blow-up map (the composite
`ι U ≫ π = affineBlowUp.π ≫ fromSpec`). -/
theorem stalkMap_ι_stalkMap_π (y : affineBlowUp (I.ideal U))
    (hy : blowUpπ I (blowUp.ι I U y) ∈ U.1) (a : Γ(X, U)) :
    (blowUp.ι I U).stalkMap y ((blowUpπ I).stalkMap (blowUp.ι I U y)
        (X.presheaf.germ U.1 (blowUpπ I (blowUp.ι I U y)) hy a)) =
      (affineBlowUp.π (I.ideal U)).stalkMap y (specGerm (affineBlowUp.π (I.ideal U) y) a) := by
  have hcomp : blowUp.ι I U ≫ blowUpπ I =
      affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).fromSpec := by
    rw [blowUp.ι_π, Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  have key : ∀ f : affineBlowUp (I.ideal U) ⟶ X,
      f = affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).fromSpec →
      ∀ hfy : f y ∈ U.1, f.stalkMap y (X.presheaf.germ U.1 (f y) hfy a) =
        (affineBlowUp.π (I.ideal U)).stalkMap y (specGerm (affineBlowUp.π (I.ideal U) y) a) := by
    rintro f rfl hfy
    have h2 := congrArg (fun φ : X.presheaf.stalk
          ((affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).fromSpec) y) ⟶
          (affineBlowUp (I.ideal U)).presheaf.stalk y =>
        φ (X.presheaf.germ U.1
          ((affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).fromSpec) y) hfy a))
      (Scheme.Hom.stalkMap_comp (affineBlowUp.π (I.ideal U))
        (affineOpens_isAffineOpen U).fromSpec y)
    refine h2.trans ?_
    exact congrArg (fun t => (affineBlowUp.π (I.ideal U)).stalkMap y t)
      (fromSpec_stalkMap_germ U _ hfy a)
  have h1 := congrArg (fun φ : X.presheaf.stalk ((blowUp.ι I U ≫ blowUpπ I) y) ⟶
        (affineBlowUp (I.ideal U)).presheaf.stalk y =>
      φ (X.presheaf.germ U.1 ((blowUp.ι I U ≫ blowUpπ I) y) hy a))
    (Scheme.Hom.stalkMap_comp (blowUp.ι I U) (blowUpπ I) y)
  exact h1.symm.trans (key _ hcomp hy)

/-- The chart membership criterion [Sta, Tag 0BFL]: a point `x'` of the blow-up over `U` lies in
the chart of `a ∈ I(U)` iff the image of `a` in `𝒪_{B,x'}` generates the stalk of the exceptional
ideal at `x'` (from the affine criterion `affineBlowUp.mem_chart_iff` along `ι U`). -/
theorem Scheme.IdealSheafData.blowUp.mem_range_chart_iff (a : I.ideal U) (x' : blowUp I)
    (hx' : blowUpπ I x' ∈ U.1) :
    x' ∈ Set.range (blowUp.chart I U a) ↔
      I.exceptionalDivisor.stalkIdeal x' =
        Ideal.span {(blowUpπ I).stalkMap x' (X.presheaf.germ U.1 (blowUpπ I x') hx' a)} := by
  have hx'' : x' ∈ (blowUp.ι I U).opensRange := by
    rw [blowUp.opensRange_ι]
    exact hx'
  obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx''
  set j := blowUp.ι I U
  have hL : j y ∈ Set.range (blowUp.chart I U a) ↔
      y ∈ (affineBlowUp.chart (I.ideal U) a).opensRange := by
    constructor
    · rintro ⟨z, hz⟩
      rw [blowUp.chart_eq, Scheme.Hom.comp_apply] at hz
      exact ⟨z, j.injective hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [blowUp.chart_eq, Scheme.Hom.comp_apply, hz]⟩
  set σ : (blowUp I).presheaf.stalk (j y) ≃+* (affineBlowUp (I.ideal U)).presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv with hσ_def
  have hσ : (j.stalkMap y).hom = (σ : (blowUp I).presheaf.stalk (j y) →+*
      (affineBlowUp (I.ideal U)).presheaf.stalk y) := rfl
  have hinj : Function.Injective (Ideal.map (σ : (blowUp I).presheaf.stalk (j y) →+*
      (affineBlowUp (I.ideal U)).presheaf.stalk y)) := by
    intro A B h
    rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at h
    exact Ideal.comap_injective_of_surjective _ σ.symm.surjective h
  rw [hL, affineBlowUp.mem_chart_iff, ← hinj.eq_iff, ← hσ, ← stalkIdeal_comap,
    blowUp.comap_exceptionalDivisor_ι, Ideal.map_span, Set.image_singleton,
    stalkMap_ι_stalkMap_π I U y hx' a]
  rfl

end Membership

end AlgebraicGeometry
