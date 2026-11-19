/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Glue.Global
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Morphisms into blow-ups

The morphisms that the universal property of the blow-up provides [Hau14, Definition 4.4];
[Sta, Tag 0806]. The blow-up map `π : blowUp I ⟶ X` is admissible for `I` — the inverse image of
`I` is invertible — and every admissible `f : Y ⟶ X` factors through it:

* `blowUp.lift I f hf : Y ⟶ blowUp I`, the lift of an admissible `f`;
* `Scheme.Hom.blowUpMap h D : blowUp (D.comap h) ⟶ blowUp D`, the morphism of blow-ups over a
  morphism `h : Y ⟶ X` of the base, the lift of the admissible `π_Y ≫ h`: the morphism `h^*π` of
  the pull-back of a blow-up sequence along `h` [Kol07, Definition 30, 30.1] and the top arrow of
  the cartesian square of blow-ups under flat base change [Sta, Tag 0805];
* `Scheme.Hom.pushforwardBlowUp j Z : Z.blowUp ⟶ (Z.map j).blowUp`, for a closed immersion
  `j : Y ⟶ X` and a centre `Z ⊆ Y`, the morphism `blowUpMap j (Z.map j)` read with the source
  `Z.blowUp`, which is the blow-up of `Y` along `(Z.map j).comap j` because the ideal sheaves of `Y`
  are the ideal sheaves of `X` containing the ideal of `Y` (`comap_map_of_isClosedImmersion`): the
  push-forward of a blow-up sequence along a closed immersion [Kol07, Definition 30, 30.3].
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.IdealSheafData Scheme.Hom

section Lift

variable {X : Scheme.{u}} (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The lift** of an admissible `f : Y ⟶ X` to the blow-up. -/
noncomputable def Scheme.IdealSheafData.blowUp.lift (hf : (I.comap f).IsInvertible) : Y ⟶ blowUp I
    :=
  (blowUp.exists_lift I f hf).choose

end Lift

section BlowUpMap

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)

/-- `π_Y ≫ h : B_{D·𝒪_Y} Y ⟶ X` is admissible for `D` — its inverse image of `D` is the
exceptional ideal of `B_{D·𝒪_Y} Y`. -/
theorem isInvertible_comap_π_comp : (D.comap (blowUpπ (D.comap h) ≫ h)).IsInvertible := by
  rw [comap_comp]
  exact blowUp.isInvertible_comap_π (D.comap h)

/-- **The morphism of blow-ups induced by `h : Y ⟶ X`**, `blowUp (D.comap h) ⟶ blowUp D` over `h`
[Kol07, Definition 30, 30.1]; [Sta, Tag 0805]: the lift of the admissible `π_Y ≫ h` through the
universal property of `B_D X`. For an open immersion `h = U.ι` it is the restriction
`blowUp (D|_U) ⟶ blowUp D`, an isomorphism onto `π⁻¹(U)` (`blowUp.restrictIso`). -/
noncomputable def Scheme.Hom.blowUpMap : blowUp (D.comap h) ⟶ blowUp D :=
  blowUp.lift D (blowUpπ (D.comap h) ≫ h) (isInvertible_comap_π_comp h D)

end BlowUpMap

section Pushforward

variable {X Y : Scheme.{u}}

/-- For a closed immersion `j : Y ⟶ X`, the inverse image of the pushforward of `Z` is `Z` — the
ideal sheaves of `Y` correspond to the ideal sheaves of `X` containing `ker j`, so that a centre
of `Y` and its push-forward to `X` are the same subscheme [Kol07, Definition 30, 30.3]. The fibre
product of the closed immersion `V(j_* Z) → X` (the scheme-theoretic image of `V(Z) → Y → X`)
with `j` is `V(Z)`, since `j` is a monomorphism and `V(Z) ≅ V(j_* Z)`. -/
theorem comap_map_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j] (Z : Y.IdealSheafData) :
    (Z.map j).comap j = Z := by
  -- `V(Z) → Y → X` is a closed immersion with kernel `Z.map j` (definitionally); its
  -- scheme-theoretic image is `V(Z.map j)`, and `toImage` is an isomorphism onto it
  have hfac : (Z.subschemeι ≫ j).toImage ≫ (Z.map j).subschemeι = Z.subschemeι ≫ j :=
    (Z.subschemeι ≫ j).toImage_imageι
  -- the square `V(Z) → Y`, `V(Z) → V(Z.map j)`, `j`, `V(Z.map j) → X` is a pullback: `j` is mono
  have hpb : IsPullback Z.subschemeι (Z.subschemeι ≫ j).toImage j (Z.map j).subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨hfac.symm⟩
  -- `comap` is the kernel of the first projection of the fibre product
  have hf : pullback.fst j (Z.map j).subschemeι = hpb.isoPullback.inv ≫ Z.subschemeι :=
    hpb.isoPullback_inv_fst.symm
  calc (Z.map j).comap j = (pullback.fst j (Z.map j).subschemeι).ker := rfl
    _ = (hpb.isoPullback.inv ≫ Z.subschemeι).ker := congrArg Scheme.Hom.ker hf
    _ = Z.subschemeι.ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = Z := Scheme.IdealSheafData.ker_subschemeι Z

/-- For a closed immersion `j : Y ⟶ X` and a centre `Z ⊆ Y`, the induced closed immersion
`Z.blowUp ⟶ blowUp X (j_* Z)` onto the strict transform of `Y` [Kol07, Definition 30,
30.2 and 30.3]: the lift `blowUpMap j (j_* Z)`, whose source `blowUp Y ((j_* Z)·𝒪_Y)` is
`Z.blowUp` because `(Z.map j).comap j = Z` for a closed immersion
(`AlgebraicGeometry.comap_map_of_isClosedImmersion`). The closed-immersion hypothesis is
essential: for a general `j` the hom-set can be empty (the fold `X ⊔ X ⟶ X` with `Z = (⊤, ⊥)`
has `Z.blowUp ≅ X` and `(Z.map j).blowUp = blowUp X ⊥ = ∅`). -/
noncomputable def Scheme.Hom.pushforwardBlowUp (j : Y ⟶ X) [IsClosedImmersion j]
    (Z : Y.IdealSheafData) : Z.blowUp ⟶ (Z.map j).blowUp :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp (comap_map_of_isClosedImmersion j Z).symm) ≫
    Scheme.Hom.blowUpMap j (Z.map j)

end Pushforward

end AlgebraicGeometry
