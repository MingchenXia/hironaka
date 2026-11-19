/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.BlowUp.UniversalProperty
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Uniqueness
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.BlowUp.ProductCenter
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The blow-up of a chart of étale coordinates

`k` a field, `f : X ⟶ Spec k`, `E` a chart of étale coordinates at `x` adapted to `Z`
(`EtaleCoordinatesAdapted`): an affine open `U ∋ x`, sections `v` with
`g = toAffineSpace f U v : U ⟶ 𝔸ⁿ_k` étale and `Z ∩ U = g⁻¹(L)`, `L = coordinateSubspace k n r`.
Three statements about `B_{Z∩U} U`:

* `B_{Z∩U} U` is the fibre product `U ×_{𝔸ⁿ} B_L 𝔸ⁿ` (`exists_isPullback_blowUp`): the flat
  base-change square `isPullback_blowUpMap` for the étale (hence flat) `g`, read along
  `Z ∩ U = g⁻¹(L)`. A blow-up commutes with flat base change [Sta, Tag 0805]; in general the
  blow-up of `Y` along `φ⁻¹(Z)` is the closure of `p⁻¹(Y ∖ φ⁻¹(Z))` in the fibre product
  [Hau14, Proposition 5.1].
* The projection `φ : B_{Z∩U} U ⟶ B_L 𝔸ⁿ` is étale, as a base change of `g`
  (`etale_of_isPullback_blowUp`; Mathlib's `IsStableUnderBaseChange` for `Etale`).
* `B_{Z∩U} U → Spec k` is smooth of relative dimension `n`, the composite of the étale `φ` with
  `B_L 𝔸ⁿ → 𝔸ⁿ → Spec k` (`smoothOfRelativeDimension_blowUpπ_comap`). The last morphism is the
  smoothness of the affine model `modelBlowUp k n r` (`smoothOfRelativeDimension_modelBlowUp`),
  transported to the glued `blowUp (coordinateSubspace k n r)` by the uniqueness of the blow-up
  (`IsBlowUp.exists_iso`): `coordinateSubspace k n r` is by definition
  `specIdealSheaf (centerIdeal k n r)`, and the affine model is a blow-up in the sense of the
  universal property (`affineBlowUp.isBlowUp`). The structure morphism of the chart is
  `g ≫ (𝔸ⁿ → Spec k) = U.ι ≫ f` (`toAffineSpace_comp_structure`).

This is the chart computation from which `Hironaka/Scheme/Smooth/BlowUpSmooth.lean` glues the
smoothness of `B_Z X`: Kollár's "`B_Z X` is smooth" for a smooth blow-up [Kol07, Notation 19]
read on one chart, whose coordinates are those of [Hau14, Proposition 5.4].
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

section AffineModel

variable {R : Type u} [CommRing R]

/-- The affine blow-up `affineBlowUp I` of `Spec R` along `I` is a blow-up in the sense of the
universal property ([Hau14, Definition 4.4]; the predicate `IsBlowUp`): the exceptional ideal is
invertible, and every morphism making `I` invertible lifts uniquely. -/
theorem affineBlowUp.isBlowUp (I : Ideal R) : IsBlowUp (specIdealSheaf I) (affineBlowUp.π I) where
  admissible := affineBlowUp.isInvertible_exceptionalIdeal I
  existsUnique_lift f hf := by
    obtain ⟨g, hg⟩ := affineBlowUp.exists_lift I f hf
    exact ⟨g, hg, fun g' hg' => affineBlowUp.hom_ext I f hf g' g hg' hg⟩

end AffineModel

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.IdealSheafData AlgebraicGeometry CoordinateSubspace

section Model

variable (k : Type u) [Field k] (n r : ℕ)

/-- The glued blow-up `blowUp (coordinateSubspace k n r)` of `𝔸ⁿ_k` along `L` and the affine model
`modelBlowUp k n r` are isomorphic over `𝔸ⁿ_k`, by the uniqueness of the blow-up. -/
theorem exists_iso_blowUp_coordinateSubspace :
    ∃ e : blowUp (coordinateSubspace k n r) ≅ modelBlowUp k n r,
      e.hom ≫ affineBlowUp.π (centerIdeal k n r) = blowUpπ (coordinateSubspace k n r) := by
  obtain ⟨e, he, -⟩ := IsBlowUp.exists_iso (blowUp.isBlowUp (coordinateSubspace k n r))
    (affineBlowUp.isBlowUp (centerIdeal k n r))
  exact ⟨e, he⟩

/-- `B_L 𝔸ⁿ_k → Spec k` is smooth of relative dimension `n`, for the glued blow-up along the
coordinate subspace `L` (transported from the affine model). -/
theorem smoothOfRelativeDimension_blowUpπ_coordinateSubspace :
    SmoothOfRelativeDimension n (blowUpπ (coordinateSubspace k n r) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace k n r
  rw [← he, Category.assoc]
  have := smoothOfRelativeDimension_modelBlowUp k n r
  have : SmoothOfRelativeDimension (0 + n) (e.hom ≫ affineBlowUp.π (centerIdeal k n r) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := inferInstance
  rwa [zero_add] at this

end Model

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- `k → k[t] → A`, `t_i ↦ v_i`, is the structure map of the `k`-algebra `A`. -/
theorem ofHom_algebraMap_comp_aeval {A : Type u} [CommRing A] [Algebra k A] {n : ℕ}
    (v : Fin n → A) :
    CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)) ≫
        CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom =
      CommRingCat.ofHom (algebraMap k A) := by
  ext a
  exact (MvPolynomial.aeval v).commutes a

/-- The coordinate morphism is a morphism over `k`: `g ≫ (𝔸ⁿ_k → Spec k) = U.ι ≫ f`. -/
theorem toAffineSpace_comp_structure (f : X ⟶ Spec (.of k)) {n : ℕ} (U : X.Opens)
    (v : Fin n → Γ(X, U)) :
    toAffineSpace f U v ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
      U.ι ≫ f := by
  have h1 := @ofHom_algebraMap_comp_aeval k _ Γ(X, U) _ (f.sectionsAlgebra U) n v
  have h2 : CommRingCat.ofHom (@algebraMap k Γ(X, U) _ _ (f.sectionsAlgebra U)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top := rfl
  have key := Scheme.Opens.toSpecΓ_SpecMap_appLE f ⊤ U le_top
  unfold toAffineSpace
  rw [Category.assoc, ← Spec.map_comp, h1, h2, Spec.map_comp, ← Category.assoc, key,
    Category.assoc, Scheme.Opens.toSpecΓ_top, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]
  exact Scheme.Hom.resLE_comp_ι f le_top

variable {f : X ⟶ Spec (.of k)} {n r : ℕ} {Z : X.IdealSheafData} {x : X}

/-- For a chart `E` of étale coordinates adapted to `Z`, `B_{Z∩U} U` is the fibre product
`U ×_{𝔸ⁿ} B_L 𝔸ⁿ`: a blow-up commutes with flat base change ([Sta, Tag 0805]; cf.
[Hau14, Proposition 5.1]). -/
theorem exists_isPullback_blowUp (E : EtaleCoordinatesAdapted f n r Z x) :
    ∃ φ : blowUp (Z.comap E.U.1.ι) ⟶ blowUp (coordinateSubspace k n r),
      IsPullback φ (blowUpπ (Z.comap E.U.1.ι)) (blowUpπ (coordinateSubspace k n r))
        (toAffineSpace f E.U.1 E.v) := by
  have := E.etale
  rw [E.adapted]
  exact ⟨_, isPullback_blowUpMap (toAffineSpace f E.U.1 E.v) (coordinateSubspace k n r)⟩

/-- The projection `φ : B_{Z∩U} U ⟶ B_L 𝔸ⁿ` of any cartesian square as in `exists_isPullback_blowUp`
is étale, being the base change of the étale `g` along `π_L`. -/
theorem etale_of_isPullback_blowUp (E : EtaleCoordinatesAdapted f n r Z x)
    {φ : blowUp (Z.comap E.U.1.ι) ⟶ blowUp (coordinateSubspace k n r)}
    (H : IsPullback φ (blowUpπ (Z.comap E.U.1.ι)) (blowUpπ (coordinateSubspace k n r))
      (toAffineSpace f E.U.1 E.v)) : Etale φ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) H.flip E.etale

/-- `B_{Z∩U} U → Spec k` is smooth of relative dimension `n`: the composite of the étale `φ` with
`B_L 𝔸ⁿ → 𝔸ⁿ → Spec k` (the chart form of "`B_Z X` is smooth", [Kol07, Notation 19]). -/
theorem smoothOfRelativeDimension_blowUpπ_comap (E : EtaleCoordinatesAdapted f n r Z x) :
    SmoothOfRelativeDimension n (blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι ≫ f) := by
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp E
  have : Etale φ := etale_of_isPullback_blowUp E H
  have := smoothOfRelativeDimension_blowUpπ_coordinateSubspace k n r
  rw [← toAffineSpace_comp_structure f E.U.1 E.v, ← Category.assoc, ← H.w, Category.assoc]
  have : SmoothOfRelativeDimension (0 + n) (φ ≫ blowUpπ (coordinateSubspace k n r) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))) := inferInstance
  rwa [zero_add] at this

end Chart

end AlgebraicGeometry
