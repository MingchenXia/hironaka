/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Glue.BlowUp
public import Hironaka.Scheme.BlowUp.UniversalProperty
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Existence
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Uniqueness
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The universal property of the blow-up from the affine statements

The exceptional ideal of the blow-up is invertible and the blow-up is universal among the
morphisms along which `I` becomes invertible [Sta, Tags 0806 and 02OS]; [Hau14, Definition 4.4
and Theorem 4.18]. Both statements are proved by locality over the affine opens of `X`, from the
affine statements of the modules under `Hironaka/Scheme/BlowUp/AffineBlowUp/`:

* `blowUp.isInvertible_comap_π`: the exceptional ideal `I·𝒪_B` is invertible.  On
  `π⁻¹(U) ≅ affineBlowUp (I.ideal U)` it is the exceptional ideal of the affine blow-up
  (`comap_exceptionalDivisor_ι`, from `ι_toBase` and the affine computation of inverse images
  through `fromSpec`), invertible by `affineBlowUp.isInvertible_exceptionalIdeal`; the `π⁻¹(U)`
  cover `B`, and invertibility is local (`IsInvertible.of_forall_comap_isOpenImmersion`).
* `blowUp.hom_ext`: two lifts `g, g'` of an admissible `f : Y ⟶ X` are equal.  For `y ∈ Y` choose
  an affine `U ∋ f y`; on `f⁻¹(U)` both lifts land in `π⁻¹(U) ≅ affineBlowUp (I.ideal U)` over
  the admissible `f⁻¹(U) → U ≅ Spec Γ(X, U)`, so they agree by the affine uniqueness
  (`affineBlowUp.hom_ext`); conclude with `Scheme.hom_ext_of_forall`.
* `blowUp.exists_lift`: an admissible `f : Y ⟶ X` lifts.  For every affine open `U ⊆ X`,
  `f⁻¹(U) → U ≅ Spec Γ(X, U)` is admissible for `I(U)`, so the affine universal property
  (`affineBlowUp.lift`) gives `f⁻¹(U) → affineBlowUp (I.ideal U) → B` over `f`; the local lifts
  agree on the overlaps by uniqueness and glue over the cover `{f⁻¹(U)}` of `Y`
  (`Scheme.Cover.glueMorphisms`).

Together: the blow-up satisfies the predicate `IsBlowUp` of
`Hironaka.Scheme.BlowUp.UniversalProperty` (`blowUp.isBlowUp`). The reduction of the universal
property to the affine case, by uniqueness on overlaps, is the argument of
[Hau14, Theorem 4.18, proof (a)].
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.IdealSheafData TopologicalSpace

universe u

section Cover

variable {Y : Scheme.{u}}

/-- An ideal sheaf is invertible as soon as its inverse images along a family of open immersions
with jointly surjective images are — the local generator on an affine open of the source is
transported along `Scheme.Hom.appIso`. -/
theorem Scheme.IdealSheafData.IsInvertible.of_forall_comap_isOpenImmersion
    {ι : Type*} (J : Y.IdealSheafData) {Z : ι → Scheme.{u}} (j : ∀ i, Z i ⟶ Y)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ y : Y, ∃ i, y ∈ (j i).opensRange)
    (h : ∀ i, (J.comap (j i)).IsInvertible) : J.IsInvertible := by
  intro y
  obtain ⟨i, hy⟩ := hcov y
  obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
  obtain ⟨V, hzV, g, hg, hJV⟩ := h i z
  refine ⟨⟨j i ''ᵁ V.1, V.2.image_of_isOpenImmersion (j i)⟩, ⟨z, hzV, rfl⟩, ?_⟩
  set e := ((j i).appIso V.1).commRingCatIsoToRingEquiv with he
  let ψ : Γ(Z i, V) →+* Γ(Y, j i ''ᵁ V.1) := e.symm
  have hψ : ((j i).appIso V.1).inv.hom = ψ := RingHom.ext fun _ => rfl
  have hψs : Function.Surjective ψ := e.symm.surjective
  rw [ideal_comap_of_isOpenImmersion, hψ] at hJV
  refine ⟨ψ g, map_mem_nonZeroDivisors_of_ringEquiv e.symm hg, ?_⟩
  have h2 := congrArg (Ideal.map ψ) hJV
  rw [Ideal.map_comap_of_surjective ψ hψs, Ideal.map_span, Set.image_singleton] at h2
  exact h2

end Cover

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On the component `ι U`, the exceptional ideal of the blow-up is the exceptional ideal of the
affine blow-up `affineBlowUp (I.ideal U)` (`comap_fromSpec`, `ι_toBase`). -/
theorem Scheme.IdealSheafData.blowUp.comap_exceptionalDivisor_ι (U : X.affineOpens) :
    I.exceptionalDivisor.comap (blowUp.ι I U) =
      affineBlowUp.exceptionalIdeal (I.ideal U) := by
  rw [Scheme.IdealSheafData.exceptionalDivisor, ← comap_comp, blowUp.ι_π, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, comap_comp]
  change (I.comap U.2.fromSpec).comap _ = _
  rw [comap_fromSpec]
  rfl

/-- Every point of the blow-up lies in the image of some component `ι U`. -/
theorem Scheme.IdealSheafData.blowUp.exists_mem_opensRange_ι (b : blowUp I) :
    ∃ U : X.affineOpens, b ∈ (blowUp.ι I U).opensRange := by
  obtain ⟨U, hU⟩ := exists_affineOpens_mem (blowUpπ I b)
  exact ⟨U, by rw [blowUp.opensRange_ι]; exact hU⟩

/-- **The exceptional ideal of the blow-up is invertible** — the exceptional divisor
`I.exceptionalDivisor = I.comap (blowUpπ I)` is an effective Cartier divisor [Sta, Tag 02OS];
[Hau14, Definition 4.4]: the blow-up map is admissible for `I`. -/
theorem Scheme.IdealSheafData.blowUp.isInvertible_comap_π : (I.comap (blowUpπ I)).IsInvertible :=
  IsInvertible.of_forall_comap_isOpenImmersion _ (blowUp.ι I) (blowUp.exists_mem_opensRange_ι I)
    fun U => by
      rw [← Scheme.IdealSheafData.exceptionalDivisor, blowUp.comap_exceptionalDivisor_ι]
      exact affineBlowUp.isInvertible_exceptionalIdeal _

section Universal

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- The restriction of `f` over an affine open `U ⊆ X`, as a morphism `f⁻¹(U) ⟶ Spec Γ(X, U)`. -/
noncomputable def restrictToSpec (U : X.affineOpens) :
    (f ⁻¹ᵁ U.1 : Scheme.{u}) ⟶ Spec Γ(X, U) :=
  (f ∣_ U.1) ≫ (affineOpens_isAffineOpen U).isoSpec.hom

theorem restrictToSpec_isoSpec_inv_ι (U : X.affineOpens) :
    restrictToSpec f U ≫ (affineOpens_isAffineOpen U).isoSpec.inv ≫ U.1.ι = (f ⁻¹ᵁ U.1).ι ≫ f := by
  rw [restrictToSpec, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- The ideal sheaf of `I(U)` pulled back along `f⁻¹(U) → Spec Γ(X, U)` is the inverse image
ideal sheaf `I·𝒪_Y` restricted to the open `f⁻¹(U)` (`comap_fromSpec`). -/
theorem comap_specIdealSheaf_restrictToSpec (U : X.affineOpens) :
    (specIdealSheaf (I.ideal U)).comap (restrictToSpec f U) =
      (I.comap f).comap (f ⁻¹ᵁ U.1).ι := by
  rw [show specIdealSheaf (I.ideal U) = I.comap (affineOpens_isAffineOpen U).fromSpec from
    (comap_fromSpec I U).symm, ← comap_comp, ← comap_comp, ← IsAffineOpen.isoSpec_inv_ι,
    restrictToSpec_isoSpec_inv_ι]

/-- Admissibility restricts: if `f` is admissible for `I`, then `f⁻¹(U) → Spec Γ(X, U)` is
admissible for `I(U)`. -/
theorem isInvertible_comap_restrictToSpec (hf : (I.comap f).IsInvertible) (U : X.affineOpens) :
    ((specIdealSheaf (I.ideal U)).comap (restrictToSpec f U)).IsInvertible := by
  rw [comap_specIdealSheaf_restrictToSpec]
  exact hf.comap_of_isOpenImmersion _

/-- The local lift `f⁻¹(U) ⟶ blowUp I` of an admissible `f` over an affine open `U`: the affine
lift into `affineBlowUp (I.ideal U)` followed by the component `ι U`. -/
noncomputable def Scheme.IdealSheafData.blowUp.localLift (hf : (I.comap f).IsInvertible)
    (U : X.affineOpens) :
    (f ⁻¹ᵁ U.1 : Scheme.{u}) ⟶ blowUp I :=
  affineBlowUp.lift (I.ideal U) (restrictToSpec f U) (isInvertible_comap_restrictToSpec I f hf U) ≫
    blowUp.ι I U

theorem Scheme.IdealSheafData.blowUp.localLift_π (hf : (I.comap f).IsInvertible)
    (U : X.affineOpens) :
    blowUp.localLift I f hf U ≫ blowUpπ I = (f ⁻¹ᵁ U.1).ι ≫ f := by
  rw [blowUp.localLift, Category.assoc, blowUp.ι_π, ← Category.assoc, ← Category.assoc,
    affineBlowUp.lift_π, Category.assoc, restrictToSpec_isoSpec_inv_ι]

/-- A lift `h` of `f` maps `f⁻¹(U)` into `π⁻¹(U)`, the image of `ι U`. -/
theorem range_ι_comp_subset (h : Y ⟶ blowUp I) (hh : h ≫ blowUpπ I = f) (U : X.affineOpens) :
    Set.range ((f ⁻¹ᵁ U.1).ι ≫ h) ⊆ Set.range (blowUp.ι I U) := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  change h ((f ⁻¹ᵁ U.1).ι w) ∈ (blowUp.ι I U).opensRange
  rw [blowUp.opensRange_ι, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hh]
  exact w.2

/-- The factorization of a lift restricted to `f⁻¹(U)` through `ι U` lies over
`f⁻¹(U) → Spec Γ(X, U)`. -/
theorem lift_comp_π_eq_restrictToSpec (h : Y ⟶ blowUp I) (hh : h ≫ blowUpπ I = f)
    (U : X.affineOpens) :
    IsOpenImmersion.lift (blowUp.ι I U) ((f ⁻¹ᵁ U.1).ι ≫ h) (range_ι_comp_subset I f h hh U) ≫
        affineBlowUp.π (I.ideal U) = restrictToSpec f U := by
  rw [← cancel_mono ((affineOpens_isAffineOpen U).isoSpec.inv ≫ U.1.ι), Category.assoc,
    restrictToSpec_isoSpec_inv_ι, ← Category.assoc (affineBlowUp.π (I.ideal U)), ← blowUp.ι_π,
    ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hh]

/-- **Uniqueness of the lift** [Sta, Tag 0806]; [Hau14, Theorem 4.18, proof (a)]: two lifts of an
admissible `f : Y ⟶ X` to the blow-up are equal. -/
theorem Scheme.IdealSheafData.blowUp.hom_ext (hf : (I.comap f).IsInvertible) (g g' : Y ⟶ blowUp I)
    (e : g ≫ blowUpπ I = f) (e' : g' ≫ blowUpπ I = f) : g = g' := by
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨U, hU⟩ := exists_affineOpens_mem (f y)
  refine ⟨f ⁻¹ᵁ U.1, hU, ?_⟩
  have key := affineBlowUp.hom_ext (I.ideal U) (restrictToSpec f U)
    (isInvertible_comap_restrictToSpec I f hf U) _ _
    (lift_comp_π_eq_restrictToSpec I f g e U) (lift_comp_π_eq_restrictToSpec I f g' e' U)
  calc (f ⁻¹ᵁ U.1).ι ≫ g
      = IsOpenImmersion.lift (blowUp.ι I U) ((f ⁻¹ᵁ U.1).ι ≫ g) (range_ι_comp_subset I f g e U) ≫
          blowUp.ι I U := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = IsOpenImmersion.lift (blowUp.ι I U) ((f ⁻¹ᵁ U.1).ι ≫ g')
          (range_ι_comp_subset I f g' e' U) ≫ blowUp.ι I U := by rw [key]
    _ = (f ⁻¹ᵁ U.1).ι ≫ g' := IsOpenImmersion.lift_fac _ _ _

/-- **Existence of the lift** [Sta, Tag 0806]; [Hau14, Theorem 4.18 (a)]: an admissible
`f : Y ⟶ X` lifts to the blow-up. -/
theorem Scheme.IdealSheafData.blowUp.exists_lift (hf : (I.comap f).IsInvertible) :
    ∃ g : Y ⟶ blowUp I, g ≫ blowUpπ I = f := by
  have hcov : IsOpenCover fun U : X.affineOpens => f ⁻¹ᵁ U.1 := by
    refine top_le_iff.mp fun z _ => Opens.mem_iSup.mpr ?_
    obtain ⟨U, hU⟩ := exists_affineOpens_mem (f z)
    exact ⟨U, hU⟩
  let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover (fun U : X.affineOpens => f ⁻¹ᵁ U.1) hcov
  let lifts : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ blowUp I := fun U => blowUp.localLift I f hf U
  have hlifts : ∀ U : 𝒰.I₀, lifts U ≫ blowUpπ I = 𝒰.f U ≫ f := fun U =>
    blowUp.localLift_π I f hf U
  have compat : ∀ U V, pullback.fst (𝒰.f U) (𝒰.f V) ≫ lifts U =
      pullback.snd (𝒰.f U) (𝒰.f V) ≫ lifts V := by
    intro U V
    refine blowUp.hom_ext I (pullback.fst (𝒰.f U) (𝒰.f V) ≫ 𝒰.f U ≫ f) ?_ _ _ ?_ ?_
    · rw [← Category.assoc, comap_comp]
      exact hf.comap_of_isOpenImmersion _
    · rw [Category.assoc]
      exact congrArg (fun m => pullback.fst (𝒰.f U) (𝒰.f V) ≫ m) (hlifts U)
    · rw [Category.assoc]
      refine (congrArg (fun m => pullback.snd (𝒰.f U) (𝒰.f V) ≫ m) (hlifts V)).trans ?_
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
  refine ⟨𝒰.glueMorphisms lifts compat, 𝒰.hom_ext _ _ fun U => ?_⟩
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact hlifts U

/-- **The universal property of the blow-up** [Sta, Tag 0806]; [Hau14, Definition 4.4]: the
blow-up is final among the admissible `X`-schemes — an admissible `f : Y ⟶ X` has exactly one
lift. -/
theorem Scheme.IdealSheafData.blowUp.existsUnique_lift (hf : (I.comap f).IsInvertible) :
    ∃! g : Y ⟶ blowUp I, g ≫ blowUpπ I = f := by
  obtain ⟨g, hg⟩ := blowUp.exists_lift I f hf
  exact ⟨g, hg, fun g' hg' => blowUp.hom_ext I f hf g' g hg' hg⟩

end Universal

/-- The blow-up is a blow-up in the sense of the universal property [Hau14, Definition 4.4]: the
predicate `IsBlowUp`. -/
theorem Scheme.IdealSheafData.blowUp.isBlowUp : IsBlowUp I (blowUpπ I) :=
  ⟨blowUp.isInvertible_comap_π I, fun f hf => blowUp.existsUnique_lift I f hf⟩

end AlgebraicGeometry
