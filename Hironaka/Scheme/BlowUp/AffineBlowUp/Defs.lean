/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Rees.Map
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Affine blow-ups and their gluing datum

For an ideal `I` of a commutative ring `R`, the blow-up of `Spec R` along the closed subscheme
`Spec (R/I)` is `Proj` of the graded Rees algebra `⨁ₙ Iⁿ tⁿ`, with the morphism to `Spec R` induced
by the inclusion `R → Rees(I)` in degree zero [Hau14, Definition 4.7]; [Sta, Tags 01OF and 0804],
restricted to an affine base: `affineBlowUp I` and `affineBlowUp.π I`. The map `π` is
`Proj.toSpecZero` followed by `Spec.map` of the degree-zero identification `R ≅ (Rees I)₀`
(`reesAlgebra.gradingZeroEquiv`), written as the `hom` of the corresponding isomorphism of
`CommRingCat` so that Mathlib's instances see an isomorphism; `Spec.map` reverses the direction.

For `φ : R → S` with `I S = J`, the graded map `Rees(I) → Rees(J)` induces, through Mathlib's
`Proj.map`, the morphism of affine blow-ups
`affineBlowUp.mapOfEq φ : affineBlowUp J ⟶ affineBlowUp I` over `Spec.map φ` (the functoriality of
`Proj` in the graded ring, [Sta, Tags 01OF and 01LH]); `affineBlowUp.mapHom` is the same morphism
for a morphism of `CommRingCat`. It is functorial, from `Proj.map_id` and `Proj.map_comp`, and lies
over `Spec.map φ`, from `Proj.map_toSpecZero` and the degree-zero identifications `R ≅ (Rees I)₀`,
`S ≅ (Rees J)₀`.

The blow-up of a scheme `X` along an ideal sheaf `I` is `Proj_X (⨁ₙ Iⁿ)`, obtained by gluing the
affine blow-ups `Proj Rees(I(U))` over the affine opens `U` of `X` along the canonical isomorphisms
`π⁻¹(U) ≅ Proj Rees(I(U))`; the relative gluing lemma [Sta, Tag 01LH] performs this from a functor
on the affine opens and pullback squares over the inclusions, in Mathlib's form
`Scheme.Cover.RelativeGluingData` over the directed cover `X.directedAffineCover` of all affine
opens. The functor is `affineBlowUpFunctor I : U ↦ affineBlowUp (I.ideal U)`, with transition map
for `U ≤ V` the morphism of affine blow-ups induced by the restriction `Γ(X, V) → Γ(X, U)`, along
which `I(U) = I(V) Γ(U)` (Mathlib's `IdealSheafData.map_ideal`); `affineBlowUpNatTrans I` has the
components `affineBlowUp.π ≫ U.isoSpec.inv : affineBlowUp (I.ideal U) ⟶ U`. Given a proof `h` that
its naturality squares are pullbacks, `relativeGluingDataOf I h` is the gluing datum and
`blowUpOf I h` with `blowUpOf.π I h` the glued scheme over `X`.
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

section AffineBlowUp

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **The affine blow-up** of `Spec R` along `I`: `Proj` of the graded Rees algebra `⨁ₙ Iⁿ tⁿ`
[Hau14, Definition 4.7]; [Sta, Tags 01OF and 0804].  An `abbrev`, so that Mathlib's instances on
`Proj` (separatedness, the chart cover, …) apply to it directly. -/
noncomputable abbrev affineBlowUp : Scheme.{u} := Proj (reesAlgebra.grading I)

/-- **The blow-up map** `π : affineBlowUp I ⟶ Spec R`, induced by the natural ring homomorphism
`R → Rees(I)` [Hau14, Definition 4.7]: `Proj.toSpecZero` followed by `Spec` of the degree-zero
identification `R ≅ (Rees I)₀`. -/
noncomputable def affineBlowUp.π : affineBlowUp I ⟶ Spec (.of R) :=
  Proj.toSpecZero (reesAlgebra.grading I) ≫
    Spec.map (reesAlgebra.gradingZeroEquiv I).symm.toCommRingCatIso.hom

end AffineBlowUp

section Map

open Polynomial

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {I : Ideal R} {J : Ideal S} {K : Ideal T}

/-- The morphism of affine blow-ups `affineBlowUp J ⟶ affineBlowUp I` induced by `φ : R →+* S`
with `I.map φ = J`: `Proj.map` of the graded map `Rees(I) → Rees(J)` [Sta, Tag 01OF]. -/
noncomputable def affineBlowUp.mapOfEq (φ : R →+* S) (hJ : I.map φ = J) :
    affineBlowUp J ⟶ affineBlowUp I :=
  Proj.map (reesAlgebra.mapOfLe φ hJ.le) (reesAlgebra.irrelevant_le_map_mapOfEq φ hJ)

/-- Functoriality, identity: the identity ring map induces the identity of the affine blow-up
(from `Proj.map_id`). -/
theorem affineBlowUp.mapOfEq_id (I : Ideal R) (hJ : I.map (RingHom.id R) = I) :
    affineBlowUp.mapOfEq (RingHom.id R) hJ = 𝟙 (affineBlowUp I) := by
  have key : ∀ (f : reesAlgebra.grading I →+*ᵍ reesAlgebra.grading I) (hf),
      f = GradedRingHom.id _ → Proj.map f hf = 𝟙 (Proj (reesAlgebra.grading I)) := by
    rintro f hf rfl
    exact Proj.map_id
  exact key _ _ (reesAlgebra.mapOfLe_id hJ.le)

theorem affineBlowUp.mapOfEq_eq_id {φ : R →+* R} (hφ : φ = RingHom.id R) (I : Ideal R)
    (hJ : I.map φ = I) : affineBlowUp.mapOfEq φ hJ = 𝟙 (affineBlowUp I) := by
  subst hφ
  exact affineBlowUp.mapOfEq_id I hJ

/-- Functoriality, composites (from `Proj.map_comp`). -/
theorem affineBlowUp.mapOfEq_comp (φ : R →+* S) (ψ : S →+* T) (hJ : I.map φ = J)
    (hK : J.map ψ = K) (hK' : I.map (ψ.comp φ) = K) :
    affineBlowUp.mapOfEq (ψ.comp φ) hK' =
      affineBlowUp.mapOfEq ψ hK ≫ affineBlowUp.mapOfEq φ hJ := by
  have key : ∀ (g : reesAlgebra.grading I →+*ᵍ reesAlgebra.grading K) (hg),
      g = (reesAlgebra.mapOfLe ψ hK.le).comp (reesAlgebra.mapOfLe φ hJ.le) →
        Proj.map g hg = Proj.map (reesAlgebra.mapOfLe ψ hK.le)
          (reesAlgebra.irrelevant_le_map_mapOfEq ψ hK) ≫ Proj.map (reesAlgebra.mapOfLe φ hJ.le)
          (reesAlgebra.irrelevant_le_map_mapOfEq φ hJ) := by
    rintro g hg rfl
    exact Proj.map_comp _ _ _ _
  exact key _ _ (reesAlgebra.mapOfLe_comp φ ψ hJ.le hK.le hK'.le)

theorem affineBlowUp.mapOfEq_eq_comp {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T}
    (hχ : χ = ψ.comp φ) (hJ : I.map φ = J) (hK : J.map ψ = K) (hK' : I.map χ = K) :
    affineBlowUp.mapOfEq χ hK' = affineBlowUp.mapOfEq ψ hK ≫ affineBlowUp.mapOfEq φ hJ := by
  subst hχ
  exact affineBlowUp.mapOfEq_comp φ ψ hJ hK hK'

/-- Over the base: `mapOfEq φ` lies over `Spec.map φ` — the blow-up map is induced by `R → Rees(I)`
[Hau14, Definition 4.7], naturally in `R`; from `Proj.map_toSpecZero` and the degree-zero
identifications `reesAlgebra.gradingZeroEquiv`. -/
theorem affineBlowUp.mapOfEq_π (φ : R →+* S) (hJ : I.map φ = J) :
    affineBlowUp.mapOfEq φ hJ ≫ affineBlowUp.π I =
      affineBlowUp.π J ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold affineBlowUp.mapOfEq affineBlowUp.π
  rw [Category.assoc, Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom]
  exact Subtype.ext (Subtype.ext (reesAlgebra.coe_mapOfLe_gradingZeroEquiv_symm φ hJ.le r))

section CommRingCat

/-! ### The same morphisms for morphisms of `CommRingCat`

Applying `affineBlowUp.mapOfEq` to a restriction map `Γ(X, V) ⟶ Γ(X, U)` of a scheme through its
underlying ring map makes Lean unify the ring instances on the carrier `↑Γ(X, U)` obtained by two
different routes, which unfolds the presheaf and times out; passing the rings as objects of
`CommRingCat` avoids it.  The gluing functor `affineBlowUpFunctor` below uses these forms. -/

variable {R S T : CommRingCat.{u}} {I : Ideal R} {J : Ideal S} {K : Ideal T}

/-- `affineBlowUp.mapOfEq` for a morphism `φ : R ⟶ S` of `CommRingCat`. -/
noncomputable def affineBlowUp.mapHom (φ : R ⟶ S) (hJ : I.map φ.hom = J) :
    affineBlowUp J ⟶ affineBlowUp I :=
  affineBlowUp.mapOfEq φ.hom hJ

theorem affineBlowUp.mapHom_eq_id {φ : R ⟶ R} (hφ : φ = 𝟙 R) (I : Ideal R)
    (hJ : I.map φ.hom = I) : affineBlowUp.mapHom φ hJ = 𝟙 (affineBlowUp I) := by
  subst hφ
  exact affineBlowUp.mapOfEq_eq_id CommRingCat.hom_id I hJ

theorem affineBlowUp.mapHom_eq_comp {φ : R ⟶ S} {ψ : S ⟶ T} {χ : R ⟶ T} (hχ : χ = φ ≫ ψ)
    (hJ : I.map φ.hom = J) (hK : J.map ψ.hom = K) (hK' : I.map χ.hom = K) :
    affineBlowUp.mapHom χ hK' = affineBlowUp.mapHom ψ hK ≫ affineBlowUp.mapHom φ hJ := by
  subst hχ
  exact affineBlowUp.mapOfEq_eq_comp (CommRingCat.hom_comp φ ψ) hJ hK hK'

/-- Over the base, for a morphism of `CommRingCat`: `mapHom φ` lies over `Spec.map φ`. -/
@[reassoc]
theorem affineBlowUp.mapHom_π (φ : R ⟶ S) (hJ : I.map φ.hom = J) :
    affineBlowUp.mapHom φ hJ ≫ affineBlowUp.π I = affineBlowUp.π J ≫ Spec.map φ := by
  unfold affineBlowUp.mapHom
  rw [affineBlowUp.mapOfEq_π, CommRingCat.ofHom_hom]

end CommRingCat

end Map

section Gluing

open Polynomial

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The affineness of an affine open, as a term whose type is syntactically `IsAffineOpen U.1`
(the membership `U.2 : U.1 ∈ X.affineOpens` unfolds to it only at default transparency, which
breaks the motives of `rw`). -/
theorem affineOpens_isAffineOpen (U : X.affineOpens) : IsAffineOpen U.1 := U.2

section Functor

/-- **The functor of affine blow-ups** on the affine opens of `X`, `U ↦ affineBlowUp (I.ideal U)`,
with transition map for `U ≤ V` the morphism induced by the restriction `Γ(X, V) → Γ(X, U)`,
along which `I(U) = I(V) Γ(U)` (`IdealSheafData.map_ideal`) [Sta, Tags 01OF and 01LH]. -/
noncomputable def affineBlowUpFunctor : X.affineOpens ⥤ Scheme.{u} where
  obj U := affineBlowUp (I.ideal U)
  map {U V} h :=
    affineBlowUp.mapHom (R := Γ(X, V)) (S := Γ(X, U)) (I := I.ideal V) (J := I.ideal U)
      (X.presheaf.map (homOfLE h.le).op) (I.map_ideal h.le)
  map_id U := by
    have hφ : X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (𝟙 U))).op = 𝟙 Γ(X, U) := by
      rw [show homOfLE (X := X.Opens) (leOfHom (𝟙 U)) = 𝟙 (U : X.Opens) from rfl, op_id,
        CategoryTheory.Functor.map_id]
    exact affineBlowUp.mapHom_eq_id hφ _ _
  map_comp {U V W} f g := by
    have hχ : X.presheaf.map (homOfLE (X := X.Opens) (leOfHom (f ≫ g))).op =
        X.presheaf.map (homOfLE (X := X.Opens) (leOfHom g)).op ≫
          X.presheaf.map (homOfLE (X := X.Opens) (leOfHom f)).op := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp]
      rfl
    exact affineBlowUp.mapHom_eq_comp hχ (I.map_ideal g.le) (I.map_ideal f.le) _

/-- **The structure maps** `affineBlowUp (I.ideal U) ⟶ U`, `π` followed by `U ≅ Spec Γ(X, U)`, as
a natural transformation to the directed affine cover's diagram [Sta, Tag 01LH]. -/
noncomputable def affineBlowUpNatTrans :
    affineBlowUpFunctor I ⟶ X.directedAffineCover.functorOfLocallyDirected where
  app U := affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv
  naturality {U V} h := by
    have hle : U ≤ V := h.le
    have hle' : (U : X.Opens) ≤ V := hle
    obtain rfl : h = homOfLE hle := (homOfLE_leOfHom h).symm
    have key : Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op) ≫
        (affineOpens_isAffineOpen V).isoSpec.inv =
        (affineOpens_isAffineOpen U).isoSpec.inv ≫ X.homOfLE hle' := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, IsAffineOpen.isoSpec_hom,
        IsAffineOpen.isoSpec_hom]
      exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle'
    change affineBlowUp.mapHom (R := Γ(X, V)) (S := Γ(X, U)) (I := I.ideal V) (J := I.ideal U)
        (X.presheaf.map (homOfLE (X := X.Opens) hle).op) (I.map_ideal hle) ≫
        (affineBlowUp.π (I.ideal V) ≫ (affineOpens_isAffineOpen V).isoSpec.inv) =
      (affineBlowUp.π (I.ideal U) ≫ (affineOpens_isAffineOpen U).isoSpec.inv) ≫ X.homOfLE hle'
    calc _ = affineBlowUp.π (I.ideal U) ≫
          Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hle).op) ≫
            (affineOpens_isAffineOpen V).isoSpec.inv :=
          affineBlowUp.mapHom_π_assoc (R := Γ(X, V)) (S := Γ(X, U)) (I := I.ideal V)
            (J := I.ideal U) _ (I.map_ideal hle) _
      _ = affineBlowUp.π (I.ideal U) ≫
          (affineOpens_isAffineOpen U).isoSpec.inv ≫ X.homOfLE hle' := by
          rw [key]
      _ = _ := (Category.assoc _ _ _).symm

end Functor

section Glued

variable (h : (affineBlowUpNatTrans I).Equifibered)

/-- The relative gluing datum of the affine blow-ups over the directed affine cover
[Sta, Tag 01LH], given the pullback squares `h`. -/
noncomputable def relativeGluingDataOf : X.directedAffineCover.RelativeGluingData where
  functor := affineBlowUpFunctor I
  natTrans := affineBlowUpNatTrans I
  equifibered := h

/-- **The blow-up of `X` along `I`**, glued from the affine blow-ups over the affine opens
[Sta, Tags 01OF and 01LH], given the pullback squares `h`. -/
noncomputable abbrev blowUpOf : Scheme.{u} := (relativeGluingDataOf I h).glued

/-- The blow-up map `blowUpOf I h ⟶ X`. -/
noncomputable def blowUpOf.π : blowUpOf I h ⟶ X := (relativeGluingDataOf I h).toBase

end Glued

end Gluing

end AlgebraicGeometry
