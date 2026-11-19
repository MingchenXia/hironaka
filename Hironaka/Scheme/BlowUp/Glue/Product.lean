/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.BlowUp.UniversalProperty
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.GlobalCharts
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Blowing up a product centre is the iterated blow-up

The general theorems of `Hironaka.Scheme.BlowUp.ProductCenter`, for the blow-up
`AlgebraicGeometry.Scheme.IdealSheafData.blowUp`: for ideal sheaves `I`, `J` on `X`, with `b =
blowUp.π I : X' ⟶ X` and `b' = blowUp.π (J.comap b) : X'' ⟶ X'`,

* `blowUp.isInvertible_comap_of_isInvertible`: `b` pulls invertible ideal sheaves back to
  invertible ones (`isInvertible_comap_of_charts` at the charts `blowUp.chart I U a`);
* `blowUp.isInvertible_comap_mul_π_comp`: `b' ≫ b` is admissible for `I * J`;
* `blowUp.existsUnique_lift_comp`: `b' ≫ b` is universal for `I * J`;
* `blowUp.exists_mulIso`, `blowUp.mulIso` [Sta, Tag 080A]: `X'' ≅ blowUp (I * J)` over `X`,
  uniquely;
* `blowUp.exists_powIso`: `blowUp (I ^ m) ≅ blowUp I` over `X` for `m ≥ 1`
  [Hau14, Definition 4.6 and Example 4.52], through `blowUp.exists_mulIso I (I ^ (m - 1))` and
  the trivial blow-up of the invertible `(I ^ (m - 1)).comap b` (`blowUp.isIso_π_of_isInvertible`);
* `blowUp.isBlowUp_comp`: the composite `b' ≫ b` satisfies the predicate `IsBlowUp` of
  `Hironaka.Scheme.BlowUp.UniversalProperty`, the universal property of [Hau14, Definition 4.4]
  (as the blow-up does, `blowUp.isBlowUp` of `Hironaka.Scheme.BlowUp.Glue.Global`).
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I J : X.IdealSheafData)

/-- The inverse image along `IdealSheafData.blowUpπ I` of an invertible ideal sheaf is invertible
[Sta, Tags 080A and 0809]. -/
theorem blowUp.isInvertible_comap_of_isInvertible (K : X.IdealSheafData) (hK : K.IsInvertible) :
    (K.comap (blowUpπ I)).IsInvertible :=
  isInvertible_comap_of_charts I (blowUpπ I) (blowUp.chart I) (fun _ _ => inferInstance)
    (blowUp.chart_π I) (blowUp.iUnion_range_chart I) K hK

/-- `I` pulls back along `b' ≫ b` to an invertible ideal sheaf (`I.comap b` is the exceptional
ideal of `b`, invertible by `blowUp.isInvertible_comap_π`). -/
theorem blowUp.isInvertible_comap_π_comp :
    (I.comap (blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I)).IsInvertible := by
  rw [comap_comp]
  exact blowUp.isInvertible_comap_of_isInvertible _ _ (blowUp.isInvertible_comap_π I)

/-- `b' ≫ b` is admissible for `I * J`. -/
theorem blowUp.isInvertible_comap_mul_π_comp :
    ((I * J).comap (blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I)).IsInvertible :=
  isInvertible_comap_mul_comp I J _ _ (blowUp.isInvertible_comap_π_comp I J)
    (blowUp.isInvertible_comap_π _)

/-- `b' ≫ b` is universal for `I * J`: every morphism along which `I * J` becomes invertible
lifts uniquely through it. -/
theorem blowUp.existsUnique_lift_comp {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : ((I * J).comap f).IsInvertible) :
    ∃! g : Y ⟶ blowUp (J.comap (blowUpπ I)),
      g ≫ (blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I) = f :=
  AlgebraicGeometry.existsUnique_lift_comp I J (blowUpπ I) (blowUpπ (J.comap (blowUpπ I)))
    (fun f hf => blowUp.existsUnique_lift I f hf)
    (fun f hf => blowUp.existsUnique_lift (J.comap (blowUpπ I)) f hf) f hf

/-- The composite `b' ≫ b` is a blow-up along `I * J` in the sense of the universal property. -/
theorem blowUp.isBlowUp_comp : IsBlowUp (I * J) (blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I) :=
  (blowUp.isBlowUp I).comp (blowUp.isBlowUp _) (blowUp.isInvertible_comap_π_comp I J)

/-- The blow-up of `X'` along `J.comap b` is isomorphic over `X` to the blow-up of `X` along
`I * J`, by a unique isomorphism over `X` [Sta, Tag 080A]. -/
theorem blowUp.exists_mulIso :
    ∃ e : blowUp (J.comap (blowUpπ I)) ≅ blowUp (I * J),
      e.hom ≫ blowUpπ (I * J) = blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I ∧
      ∀ ψ : blowUp (J.comap (blowUpπ I)) ⟶ blowUp (I * J),
        ψ ≫ blowUpπ (I * J) = blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I → ψ = e.hom :=
  exists_iso_of_universal (I * J) _ (blowUpπ (I * J)) (blowUp.isInvertible_comap_mul_π_comp I J)
    (fun f hf => blowUp.existsUnique_lift_comp I J f hf) (blowUp.isInvertible_comap_π (I * J))
    (fun f hf => blowUp.existsUnique_lift (I * J) f hf)

/-- The canonical isomorphism `blowUp (J.comap b) ≅ blowUp (I * J)` over `X`. -/
noncomputable def blowUp.mulIso : blowUp (J.comap (blowUpπ I)) ≅ blowUp (I * J) :=
  (blowUp.exists_mulIso I J).choose

theorem blowUp.mulIso_hom_π :
    (blowUp.mulIso I J).hom ≫ blowUpπ (I * J) = blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I :=
  (blowUp.exists_mulIso I J).choose_spec.1

theorem blowUp.eq_mulIso_hom (ψ : blowUp (J.comap (blowUpπ I)) ⟶ blowUp (I * J))
    (hψ : ψ ≫ blowUpπ (I * J) = blowUpπ (J.comap (blowUpπ I)) ≫ blowUpπ I) :
    ψ = (blowUp.mulIso I J).hom :=
  (blowUp.exists_mulIso I J).choose_spec.2 ψ hψ

/-- For `m ≥ 1`, `blowUp (I ^ m) ≅ blowUp I` over `X`, uniquely: the Rees algebras of `I` and
`I ^ m` have isomorphic `Proj` [Hau14, Definition 4.6 and Example 4.52].  Write
`I ^ m = I * I ^ (m - 1)`; `blowUp.exists_mulIso` identifies `blowUp (I * I ^ (m - 1))` with the
blow-up of `X'` along `(I ^ (m - 1)).comap b = (I.comap b) ^ (m - 1)`, a power of the invertible
exceptional ideal, whose blow-up map is an isomorphism (`blowUp.isIso_π_of_isInvertible`). -/
theorem blowUp.exists_powIso (m : ℕ) (hm : 1 ≤ m) :
    ∃ e : blowUp (I ^ m) ≅ blowUp I, e.hom ≫ blowUpπ I = blowUpπ (I ^ m) ∧
      ∀ ψ : blowUp (I ^ m) ⟶ blowUp I, ψ ≫ blowUpπ I = blowUpπ (I ^ m) → ψ = e.hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [pow_succ']
  have hinv : ((I ^ k).comap (blowUpπ I)).IsInvertible := by
    rw [comap_pow]; exact Scheme.IdealSheafData.isInvertible_pow (blowUp.isInvertible_comap_π I) k
  have : IsIso (blowUpπ ((I ^ k).comap (blowUpπ I))) := blowUp.isIso_π_of_isInvertible _ hinv
  obtain ⟨e₁, he₁, -⟩ := blowUp.exists_mulIso I (I ^ k)
  set e : blowUp (I * I ^ k) ≅ blowUp I :=
    e₁.symm ≪≫ asIso (blowUpπ ((I ^ k).comap (blowUpπ I))) with he_def
  have he : e.hom ≫ blowUpπ I = blowUpπ (I * I ^ k) := by
    simp only [he_def, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [← he₁, Iso.inv_hom_id_assoc]
  refine ⟨e, he, fun ψ hψ => ?_⟩
  have h := blowUp.isInvertible_comap_π (I * I ^ k)
  rw [comap_mul] at h
  exact blowUp.hom_ext I (blowUpπ (I * I ^ k)) (IsInvertible.of_mul h).1 ψ e.hom hψ he

end AlgebraicGeometry.Scheme.IdealSheafData
