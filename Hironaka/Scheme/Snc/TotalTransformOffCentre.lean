/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The total transform off the centre

[Kol07, Definition 25] and the proof of [Hau14, Proposition 5.3]: off the exceptional divisor the
blow-up `π : B_Z X → X` is a local isomorphism, so the total transform
`π^{-1}_{tot}(E) = (π_*^{-1} E^i, F)` "restricts to `E`" there. At a point `x' ∈ B_Z X` with
`π(x') ∉ Z`:

* the stalk map `π^* : 𝒪_{X,π(x')} → 𝒪_{B,x'}` is an isomorphism
  (`isIso_stalkMap_π_of_notMem_support`: `π` is an isomorphism over `X ∖ Z`, and Mathlib's stalkwise
  characterization of isomorphisms);
* the exceptional ideal has stalk `(1)` at `x'`, so the saturation defining the strict transform is
  trivial there and `(π_*^{-1} D)_{x'} = π^*(D_{π(x')})`
  (`stalkIdeal_strictTransformAlong_of_notMem_support`), whence `x' ∈ π_*^{-1} D ⟺ π(x') ∈ D`
  (`mem_support_strictTransformAlong_iff_of_notMem_support`);
* Kollár's conditions (1)–(3) at `π(x')` for `E` — a regular system of parameters `z` and an
  injective assignment of coordinates to the components through `π(x')` — transport along `π^*` to
  the family `(π_*^{-1} E^i, F)` at `x'`, the entry `F` being absent
  (`exists_snc_data_totalTransform_of_notMem_support`).

These are the facts about a blow-up sequence away from its centres that `Hironaka.Sequence`
(`OffCenters`, `CosuppTransport`, `TransformDerivative`) and `Hironaka.Resolution`
(`OffCentreTransport`, `Absorption`) use.

Sources: [Kol07, Definition 25]; [Hau14, Proposition 5.3] (the proof).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData TopologicalSpace

universe u

variable {X : Scheme.{u}} (Z : X.IdealSheafData)

/-- A point of the blow-up off the exceptional divisor lies over the complement of the centre. -/
theorem π_mem_compl_support_of_notMem_support {x' : blowUp Z}
    (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) :
    blowUpπ Z x' ∈ (Z.support.compl : X.Opens) := by
  change blowUpπ Z x' ∉ (Z.support : Set X)
  intro h
  apply hx'
  rw [support_comap]
  exact h

/-- [Kol07, Definition 25]: at a point `x'` of `B_Z X` over `X ∖ Z`, the stalk map
`π^* : 𝒪_{X,π(x')} → 𝒪_{B,x'}` is an isomorphism — `π` is an isomorphism over `X ∖ Z`, and an
isomorphism of schemes has isomorphic stalk maps. -/
theorem isIso_stalkMap_π_of_notMem_support {x' : blowUp Z}
    (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) :
    IsIso ((blowUpπ Z).stalkMap x') := by
  set W : X.Opens := Z.support.compl with hW
  have hxW : blowUpπ Z x' ∈ W := π_mem_compl_support_of_notMem_support Z hx'
  let u : (blowUpπ Z ⁻¹ᵁ W : Scheme.{u}) := ⟨x', hxW⟩
  have hiso : IsIso (blowUpπ Z ∣_ W) := blowUp.isIso_π_restrict_compl_support Z
  have h1 : IsIso ((blowUpπ Z ∣_ W).stalkMap u) :=
    ((isIso_iff_isIso_stalkMap _).mp hiso).2 u
  -- the open immersions have isomorphic stalk maps; the instances are passed explicitly because
  -- the point `u` of the open subscheme is not recognised by instance synthesis at reducible
  -- transparency (`backward.isDefEq.respectTransparency.types`)
  have h2 : IsIso (W.ι.stalkMap ((blowUpπ Z ∣_ W) u)) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have h3 : IsIso ((blowUpπ Z ⁻¹ᵁ W).ι.stalkMap u) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap _ u
  have hcomp : IsIso (((blowUpπ Z ⁻¹ᵁ W).ι ≫ blowUpπ Z).stalkMap u) := by
    rw [← morphismRestrict_ι, Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 hcomp

/-- The stalk map at a point off the exceptional divisor, as a ring equivalence. -/
noncomputable def stalkMapπEquiv {x' : blowUp Z} (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) :
    X.presheaf.stalk (blowUpπ Z x') ≃+* (blowUp Z).presheaf.stalk x' :=
  haveI := isIso_stalkMap_π_of_notMem_support Z hx'
  (asIso ((blowUpπ Z).stalkMap x')).commRingCatIsoToRingEquiv

theorem stalkMapπEquiv_apply {x' : blowUp Z} (hx' : x' ∉ (Z.comap (blowUpπ Z)).support)
    (a : X.presheaf.stalk (blowUpπ Z x')) :
    stalkMapπEquiv Z hx' a = (blowUpπ Z).stalkMap x' a := rfl

/-- The colon by the unit ideal is the ideal itself. -/
theorem _root_.Ideal.colon_coe_top {R : Type*} [CommRing R] (I : Ideal R) :
    I.colon ((⊤ : Ideal R) : Set R) = I := by
  ext r
  rw [Submodule.mem_colon]
  exact ⟨fun h => by simpa using h 1 (Submodule.mem_top), fun h p _ => I.mul_mem_right p h⟩

/-- At `x'` off the exceptional divisor the strict transform of `D` has stalk `π^*(D_{π(x')})` — the
exceptional ideal has stalk `(1)`, so the saturation is trivial. -/
theorem stalkIdeal_strictTransformAlong_of_notMem_support (D : X.IdealSheafData) {x' : blowUp Z}
    (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) :
    (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' =
      (D.stalkIdeal (blowUpπ Z x')).map ((blowUpπ Z).stalkMap x').hom := by
  rw [strictTransformAlong, stalkIdeal_saturate_of_isInvertible _ (blowUp.isInvertible_comap_π Z),
    stalkIdeal_comap, stalkIdeal_eq_top_of_notMem_support _ hx']
  simp only [Ideal.top_pow, Ideal.colon_coe_top, iSup_const]

/-- Off the exceptional divisor, `x'` lies on the strict transform of `D` iff `π(x')` lies on `D`.
-/
theorem mem_support_strictTransformAlong_iff_of_notMem_support (D : X.IdealSheafData)
    {x' : blowUp Z} (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) :
    x' ∈ (D.strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).support ↔
      blowUpπ Z x' ∈ D.support := by
  have := isIso_stalkMap_π_of_notMem_support Z hx'
  have hbij : Function.Bijective ((blowUpπ Z).stalkMap x').hom :=
    (stalkMapπEquiv Z hx').bijective
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, mem_support_iff_stalkIdeal_le_maximalIdeal,
    stalkIdeal_strictTransformAlong_of_notMem_support Z D hx',
    ← map_maximalIdeal_of_surjective ((blowUpπ Z).stalkMap x').hom hbij.surjective,
    Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hbij]

section Data

variable {ι : Type*} (E : ι → X.IdealSheafData)

/-- The unbundled total-transform family `(π_*^{-1} E^i, F)` on `B_Z X`, indexed by `ι ⊕ PUnit` (the
body of `DivisorFamily.totalTransform`). -/
noncomputable def totalTransformFamily : ι ⊕ PUnit.{u + 1} → (blowUp Z).IdealSheafData :=
  Sum.elim (fun i => (E i).strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z)))
    fun _ => Z.comap (blowUpπ Z)

/-- [Kol07, Definition 25], the proof of [Hau14, Proposition 5.3]: **Kollár's conditions (1)–(3) at
a point `x'` of `B_Z X` off the exceptional divisor** — the regular system of parameters `z` at
`x = π(x')` and the injective assignment `c` of coordinates to the components of `E` through `x`
transport along the isomorphism `π^*` to the family `(π_*^{-1} E^i, F)` at `x'`; the entry `F` is
absent there. -/
theorem exists_snc_data_totalTransform_of_notMem_support {x' : blowUp Z}
    (hx' : x' ∉ (Z.comap (blowUpπ Z)).support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (blowUpπ Z x')}
    (hz : maximalIdeal (X.presheaf.stalk (blowUpπ Z x')) = span (Set.range z))
    (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z x')))
    (c : {i : ι // blowUpπ Z x' ∈ (E i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (E i.1).stalkIdeal (blowUpπ Z x') = span {z (c i)}) :
    (maximalIdeal ((blowUp Z).presheaf.stalk x') =
        span (Set.range fun i => (blowUpπ Z).stalkMap x' (z i)) ∧
      (n : WithBot ℕ∞) = ringKrullDim ((blowUp Z).presheaf.stalk x')) ∧
    ∃ c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (totalTransformFamily Z E k).support} → Fin n,
      Function.Injective c' ∧ ∀ k, (totalTransformFamily Z E k.1).stalkIdeal x' =
        span {(blowUpπ Z).stalkMap x' (z (c' k))} := by
  classical
  have := isIso_stalkMap_π_of_notMem_support Z hx'
  set e := stalkMapπEquiv Z hx' with he
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← map_maximalIdeal_of_surjective ((blowUpπ Z).stalkMap x').hom e.surjective, hz,
      Ideal.map_span, ← Set.range_comp]
    rfl
  · rw [hn]
    exact ringKrullDim_eq_of_ringEquiv e
  · -- the old components through `x'` are those through `π x'`; `F` misses `x'`
    have hmem : ∀ i, x' ∈ (totalTransformFamily Z E (Sum.inl i)).support →
        blowUpπ Z x' ∈ (E i).support := fun i hi =>
      (mem_support_strictTransformAlong_iff_of_notMem_support Z (E i) hx').mp hi
    have hF : ∀ u : PUnit.{u + 1}, x' ∉ (totalTransformFamily Z E (Sum.inr u)).support :=
      fun _ h => hx' h
    let c' : {k : ι ⊕ PUnit.{u + 1} // x' ∈ (totalTransformFamily Z E k).support} → Fin n :=
      fun k => match k with
        | ⟨Sum.inl i, hi⟩ => c ⟨i, hmem i hi⟩
        | ⟨Sum.inr u, h⟩ => (hF u h).elim
    refine ⟨c', ?_, ?_⟩
    · rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ heq
      match k₁, h₁, k₂, h₂, heq with
      | Sum.inl i₁, h₁, Sum.inl i₂, h₂, heq =>
        have := hcinj (heq : c ⟨i₁, hmem i₁ h₁⟩ = c ⟨i₂, hmem i₂ h₂⟩)
        rw [Subtype.mk.injEq] at this
        exact Subtype.ext (congrArg Sum.inl this)
      | Sum.inl _, _, Sum.inr u, h₂, _ => exact (hF u h₂).elim
      | Sum.inr u, h₁, _, _, _ => exact (hF u h₁).elim
    · rintro ⟨k, hk⟩
      match k, hk with
      | Sum.inl i, hi =>
        change ((E i).strictTransformAlong (blowUpπ Z) (Z.comap (blowUpπ Z))).stalkIdeal x' =
          span {(blowUpπ Z).stalkMap x' (z (c ⟨i, hmem i hi⟩))}
        rw [stalkIdeal_strictTransformAlong_of_notMem_support Z (E i) hx', hc ⟨i, hmem i hi⟩,
          Ideal.map_span, Set.image_singleton]
      | Sum.inr u, h => exact (hF u h).elim

end Data

end AlgebraicGeometry
