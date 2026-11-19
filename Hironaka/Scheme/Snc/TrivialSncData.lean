/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.TrivialTotalTransform
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.TransformIso
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe

/-!
# Simple normal crossings of the trivial total transform

For a trivial blow-up `π : B_Z X ⟶ X` (an isomorphism, `Z` invertible; [Kol07, Warning 20]),
Kollár's conditions (1)–(3) for the total transform `(π_*^{-1} E^i, F)` at a point `x'` of `B_Z X`
are read off from the snc data of `E` and `Z` at `x = π(x')` ([Kol07, Definition 24 (4)]): the
coordinates `z` at `x` are carried to `x'` by the stalk map of `π` (an isomorphism of local rings,
so a regular system of parameters goes to one); the stalk of the strict transform of `E^i` at `x'`
is the image of the stalk of the saturation `E^i.saturate Z` at `x`, which is `(E^i)_x = (z_{c(i)})`
wherever `x'` lies on the strict transform (`stalkIdeal_saturate_eq_of_mem_support` of
`Hironaka.Scheme.Snc.TrivialTotalTransform`), and the stalk of `F = Z.comap π` is the image of
`Z_x = (z_j)`; the component with `c(i) = j` has died (its strict transform has stalk `(1)` at
`x'`), so the new index map — `c` on the surviving old components, `j` on `F` — is injective. This
is Kollár's `π⁻¹_{tot}(E) = E + Z` for a trivial blow-up [Kol07, Definition 65], used by
`Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp` and by the single-centre and boundary-clearing
arguments of `Hironaka.Resolution` and `Hironaka.BoundaryClearing`.

## Main declarations

* `AlgebraicGeometry.stalkMapEquiv` — the stalk map of an isomorphism as a ring equivalence, with
  the transport of a regular system of parameters (`maximalIdeal_eq_span_range_stalkMap`,
  `natCast_eq_ringKrullDim_stalk_of_isIso`).
* `IsRegular AlgebraicGeometry.of_isIso` — regularity along an isomorphism of schemes.
* `AlgebraicGeometry.stalkIdeal_strictTransformAlong_of_isIso`,
  `mem_support_strictTransformAlong_of_isIso_iff`, `notMem_support_saturate_of_stalkIdeal_eq`.
* `AlgebraicGeometry.exists_snc_data_trivialTotalTransform` — the snc data of the family
  `(strict transforms, F)` at a point of `B_Z X`.

Sources: [Kol07, Definition 24; Definition 65; Warning 20].
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData

namespace AlgebraicGeometry

section Iso

variable {X B : Scheme.{u}} (π : B ⟶ X) [IsIso π]

/-- The stalk map of an isomorphism of schemes, as a ring equivalence. -/
noncomputable def stalkMapEquiv (x' : B) : X.presheaf.stalk (π x') ≃+* B.presheaf.stalk x' :=
  (asIso (π.stalkMap x')).commRingCatIsoToRingEquiv

theorem stalkMapEquiv_apply (x' : B) (a : X.presheaf.stalk (π x')) :
    stalkMapEquiv π x' a = π.stalkMap x' a := rfl

/-- A regular system of parameters at `π x'` is carried by the stalk map to one at `x'`
(`𝔪` goes to `𝔪` under a surjective local homomorphism). -/
theorem maximalIdeal_eq_span_range_stalkMap (x' : B) {n : ℕ} {z : Fin n → X.presheaf.stalk (π x')}
    (hz : maximalIdeal (X.presheaf.stalk (π x')) = span (Set.range z)) :
    maximalIdeal (B.presheaf.stalk x') = span (Set.range fun i => π.stalkMap x' (z i)) := by
  rw [← map_maximalIdeal_of_surjective (π.stalkMap x').hom (stalkMapEquiv π x').surjective, hz,
    Ideal.map_span, ← Set.range_comp]
  rfl

/-- The Krull dimension is carried along the stalk map of an isomorphism. -/
theorem natCast_eq_ringKrullDim_stalk_of_isIso (x' : B) {n : ℕ}
    (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (π x'))) :
    (n : WithBot ℕ∞) = ringKrullDim (B.presheaf.stalk x') :=
  hn.trans (ringKrullDim_eq_of_ringEquiv (stalkMapEquiv π x'))

/-- The stalk at `x'` of the strict transform along the isomorphism `π` is the image of the stalk
of the saturation at `π x'`. -/
theorem stalkIdeal_strictTransformAlong_of_isIso (Z J : X.IdealSheafData) (x' : B) :
    (J.strictTransformAlong π (Z.comap π)).stalkIdeal x' =
      ((J.saturate Z).stalkIdeal (π x')).map (π.stalkMap x').hom := by
  rw [strictTransformAlong_of_isIso, Scheme.IdealSheafData.stalkIdeal_comap]

/-- `x'` lies on the strict transform iff `π x'` lies on the saturation. -/
theorem mem_support_strictTransformAlong_of_isIso_iff (Z J : X.IdealSheafData) (x' : B) :
    x' ∈ (J.strictTransformAlong π (Z.comap π)).support ↔
      π x' ∈ (J.saturate Z).support := by
  rw [strictTransformAlong_of_isIso, Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

omit [IsIso π] in
/-- `x'` lies on `F = Z.comap π` iff `π x'` lies on `Z`. -/
theorem mem_support_comap_of_isIso_iff (Z : X.IdealSheafData) (x' : B) :
    x' ∈ (Z.comap π).support ↔ π x' ∈ Z.support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

/-- Regularity of a scheme transports along an isomorphism (stalks are isomorphic). -/
theorem IsRegular.of_isIso {Y Y' : Scheme.{u}} (e : Y ⟶ Y') [IsIso e] (h : IsRegular Y) :
    IsRegular Y' := ⟨fun y' =>
  have : IsRegularLocalRing (Y.presheaf.stalk (inv e y')) := h.isRegularAt (inv e y')
  IsRegularLocalRing.of_ringEquiv (stalkMapEquiv (inv e) y')⟩

end Iso

/-- A component equal to the centre near `x` dies: `x` is not on the support of its saturation. -/
theorem notMem_support_saturate_of_stalkIdeal_eq {X : Scheme.{u}} (D Z : X.IdealSheafData)
    (hZ : Z.IsInvertible) {x : X} (hD : D.stalkIdeal x = Z.stalkIdeal x) :
    x ∉ (D.saturate Z).support := by
  intro hx
  have hle := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hx
  rw [Scheme.IdealSheafData.stalkIdeal_saturate_of_isInvertible D hZ x] at hle
  have htop : (⊤ : Ideal (X.presheaf.stalk x)) ≤ maximalIdeal (X.presheaf.stalk x) := by
    refine le_trans ?_ hle
    refine le_trans ?_ (le_iSup _ 1)
    rw [pow_one, hD, Ideal.colon_coe_self]
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp htop)

section Data

variable {X B : Scheme.{u}} (π : B ⟶ X) [IsIso π]
  (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
  (Z : X.IdealSheafData) (hZ : Z.IsInvertible) {ι : Type*} (E : ι → X.IdealSheafData)
  (hdata : ∀ i, ∀ x ∈ (E i).support, x ∈ Z.support → SncDataAt (E i) Z x)

/-- The family `(π_*^{-1} E^i, F)` of the total transform under the isomorphism `π`, as an
unbundled family on `B` indexed by `ι ⊕ PUnit`. -/
noncomputable def trivialTotalTransformFamily : ι ⊕ PUnit.{u + 1} → B.IdealSheafData :=
  Sum.elim (fun i => (E i).strictTransformAlong π (Z.comap π)) fun _ =>
      Z.comap π

include hreg hZ hdata in
/-- **Kollár's conditions (1)–(3) at a point `x'` of `B_Z X` for the trivial total transform** —
given coordinates `z` at `x = π x'`, an injective assignment `c` of coordinates to the components of
`E` through `x`, and (if `x ∈ Z`) the coordinate `z_j` of `Z`, the assignment `c` on the surviving
old components, `j` on `F`, is an injective assignment of the coordinates `π♯ z` at `x'` to the
members of `(π_*^{-1} E^i, F)` through `x'` (the transport of the regular system of parameters
itself is `maximalIdeal_eq_span_range_stalkMap`). -/
theorem exists_snc_data_trivialTotalTransform (x' : B) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (π x')}
    (c : {i : ι // π x' ∈ (E i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (E i.1).stalkIdeal (π x') = span {z (c i)})
    (hj : π x' ∈ Z.support → ∃ j : Fin n, Z.stalkIdeal (π x') = span {z j}) :
    ∃ c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (trivialTotalTransformFamily π Z E k).support} → Fin n,
      Function.Injective c' ∧ ∀ k, (trivialTotalTransformFamily π Z E k.1).stalkIdeal x' =
        span {π.stalkMap x' (z (c' k))} := by
  classical
  have hregx := hreg (π x')
  -- the surviving old components pass through `π x'`, with unchanged stalk
  have hmemE : ∀ i, x' ∈ (trivialTotalTransformFamily π Z E (Sum.inl i)).support →
      π x' ∈ (E i).support := fun i hi =>
    Scheme.IdealSheafData.support_antitone (Scheme.IdealSheafData.le_saturate (E i) Z)
      ((mem_support_strictTransformAlong_of_isIso_iff π Z (E i) x').mp hi)
  have hstalkE : ∀ i (hi : x' ∈ (trivialTotalTransformFamily π Z E (Sum.inl i)).support),
      (trivialTotalTransformFamily π Z E (Sum.inl i)).stalkIdeal x' =
        ((E i).stalkIdeal (π x')).map (π.stalkMap x').hom := fun i hi => by
    change ((E i).strictTransformAlong π (Z.comap π)).stalkIdeal x' = _
    rw [stalkIdeal_strictTransformAlong_of_isIso,
      stalkIdeal_saturate_eq_of_mem_support hreg (E i) Z hZ (hdata i)
        ((mem_support_strictTransformAlong_of_isIso_iff π Z (E i) x').mp hi)]
  -- the coordinate of `F`
  have hmemF : ∀ k : PUnit.{u + 1}, x' ∈ (trivialTotalTransformFamily π Z E (Sum.inr k)).support →
      π x' ∈ Z.support := fun _ h => (mem_support_comap_of_isIso_iff π Z x').mp h
  let jF : ∀ k : PUnit.{u + 1}, x' ∈ (trivialTotalTransformFamily π Z E (Sum.inr k)).support → Fin n
      :=
    fun k h => Classical.choose (hj (hmemF k h))
  have hjF : ∀ k h, Z.stalkIdeal (π x') = span {z (jF k h)} :=
    fun k h => Classical.choose_spec (hj (hmemF k h))
  -- the new index map
  let c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (trivialTotalTransformFamily π Z E k).support} → Fin n :=
    fun k => match k with
      | ⟨Sum.inl i, hi⟩ => c ⟨i, hmemE i hi⟩
      | ⟨Sum.inr u, h⟩ => jF u h
  -- a surviving old component does not use the coordinate of `F`
  have hne : ∀ (i : ι) (hi : x' ∈ (trivialTotalTransformFamily π Z E (Sum.inl i)).support)
      (u : PUnit.{u + 1}) (h : x' ∈ (trivialTotalTransformFamily π Z E (Sum.inr u)).support),
      c ⟨i, hmemE i hi⟩ ≠ jF u h := by
    intro i hi u h heq
    apply notMem_support_saturate_of_stalkIdeal_eq (E i) Z hZ
      (x := π x') (by rw [hc ⟨i, hmemE i hi⟩, hjF u h, heq])
    exact (mem_support_strictTransformAlong_of_isIso_iff π Z (E i) x').mp hi
  refine ⟨c', ?_, ?_⟩
  · rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ heq
    match k₁, h₁, k₂, h₂, heq with
    | Sum.inl i₁, h₁, Sum.inl i₂, h₂, heq =>
      have := hcinj (heq : c ⟨i₁, hmemE i₁ h₁⟩ = c ⟨i₂, hmemE i₂ h₂⟩)
      rw [Subtype.mk.injEq] at this
      exact Subtype.ext (congrArg Sum.inl this)
    | Sum.inl i, h₁, Sum.inr u, h₂, heq => exact (hne i h₁ u h₂ heq).elim
    | Sum.inr u, h₁, Sum.inl i, h₂, heq => exact (hne i h₂ u h₁ heq.symm).elim
    | Sum.inr u₁, h₁, Sum.inr u₂, h₂, _ => rfl
  · rintro ⟨k, hk⟩
    match k, hk with
    | Sum.inl i, hi =>
      change (trivialTotalTransformFamily π Z E (Sum.inl i)).stalkIdeal x' =
        span {π.stalkMap x' (z (c ⟨i, hmemE i hi⟩))}
      rw [hstalkE i hi, hc ⟨i, hmemE i hi⟩, Ideal.map_span, Set.image_singleton]
    | Sum.inr u, h =>
      change (Z.comap π).stalkIdeal x' = span {π.stalkMap x' (z (jF u h))}
      rw [Scheme.IdealSheafData.stalkIdeal_comap, hjF u h, Ideal.map_span, Set.image_singleton]

end Data

end AlgebraicGeometry
