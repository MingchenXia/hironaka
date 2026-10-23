/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.Geometry.ModificationCenterOpen

/-!
# The fibre map of a modification off the contracted fibres (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (`stabcritlem`, T:3131–3132): Corollary B.2 is applied to the fibre map
`f_s : C′_s → C_s`, which is an isomorphism off the fibres `Z_j = f⁻¹(x_j)` over the points
`x_1, …, x_l` of the modification locus `Z(f)` in `C_s` (blueprint `lem:sm-bd-fibre-iso`, chapter
`sm-blow-down-criterion.tex`). This is the base change of `f|_{f⁻¹U} : f⁻¹U ≅ U`,
`U = C ∖ Z(f)`, along `C_s → C`.

## Main results

* `isPullback_pullbackCompMap`: `C′ ×_S T → C ×_S T` is the base change of `f : C′ → C` along
  `C ×_S T → C`.
* `isIso_pullbackCompMap_morphismRestrict`: if `f` is an isomorphism over an open `U ⊆ C`, then
  its base change `f_T` is an isomorphism over the preimage of `U` in `C ×_S T`;
  `isIso_pullbackCompMap_morphismRestrict_of_forall` for any open with the same points.
* `isIso_pullbackCompMap_restrict_of_center` (blueprint `lem:sm-bd-fibre-iso`): if the points of
  `C ×_S T` over the modification locus `Z(f)` (Codex's `Geometry.ModificationCenter.center`) are
  those of a set `X`, then `f_T` is an isomorphism over every open with complement `X`; for
  `T = Spec κ(s)` this is the fibre map `Curves.fiberMap f g s`
  (`isIso_fiberMap_restrict_of_center`), for a geometric point `T = Spec K` its base change to an
  algebraic closure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.BlowDown

open Geometry.ModificationCenter (isomorphismOpen center)

universe u

variable {C C' S T : Scheme.{u}} (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S)

/-- **`C′ ×_S T → C ×_S T` is the base change of `β : C′ → C` along `C ×_S T → C`.** -/
theorem isPullback_pullbackCompMap :
    IsPullback (pullback.fst (β ≫ g) a) (Curves.pullbackCompMap β g a) β (pullback.fst g a) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback β (pullback.fst g a))
    (pullbackRightPullbackFstIso g a β) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rw [Curves.pullbackCompMap_eq]
    simp
  · simp
  · simp

/-- **The base change of a modification is an isomorphism over the preimage of the isomorphism
locus**: if `β|_{β⁻¹U} : β⁻¹U → U` is an isomorphism, so is the restriction of
`β_T : C′ ×_S T → C ×_S T` over the preimage of `U` in `C ×_S T`. -/
theorem isIso_pullbackCompMap_morphismRestrict (U : C.Opens) [IsIso (β ∣_ U)] :
    IsIso (Curves.pullbackCompMap β g a ∣_ (pullback.fst g a ⁻¹ᵁ U)) := by
  have H := Scheme.Hom.isPullback_resLE (isPullback_pullbackCompMap β g a) (US := U)
    (UT := pullback.fst g a ⁻¹ᵁ U) (UX := β ⁻¹ᵁ U) le_rfl le_rfl
    (UY := Curves.pullbackCompMap β g a ⁻¹ᵁ (pullback.fst g a ⁻¹ᵁ U)) (by
      refine (inf_eq_right.mpr fun y hy => ?_).symm
      change β (pullback.fst (β ≫ g) a y) ∈ U
      rw [← Scheme.Hom.comp_apply, ← Curves.pullbackCompMap_fst, Scheme.Hom.comp_apply]
      exact hy)
  have hβ : IsIso (β.resLE U (β ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have := (MorphismProperty.isomorphisms Scheme).of_isPullback H hβ
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact this

/-- `isIso_pullbackCompMap_morphismRestrict` for any open `U'` of `C ×_S T` with the points of the
preimage of `U`. -/
theorem isIso_pullbackCompMap_morphismRestrict_of_forall (U : C.Opens) [IsIso (β ∣_ U)]
    (U' : (pullback g a).Opens) (hU' : ∀ y, y ∈ U' ↔ pullback.fst g a y ∈ U) :
    IsIso (Curves.pullbackCompMap β g a ∣_ U') := by
  have hU : U' = pullback.fst g a ⁻¹ᵁ U := by
    ext y
    exact hU' y
  subst hU
  exact isIso_pullbackCompMap_morphismRestrict β g a U

/-- **The base change of a modification off the contracted fibres** (blueprint
`lem:sm-bd-fibre-iso`): let `X` be the set of points of `C ×_S T` lying over the modification locus
`Z(β)` (`Geometry.ModificationCenter.center β`). Then `β_T` is an isomorphism over every open
`U'` of `C ×_S T` with complement `X`. -/
theorem isIso_pullbackCompMap_restrict_of_center (X : Set ↥(pullback g a))
    (hX : ∀ y, pullback.fst g a y ∈ center β ↔ y ∈ X) (U' : (pullback g a).Opens)
    (hU' : ∀ y, y ∈ U' ↔ y ∉ X) : IsIso (Curves.pullbackCompMap β g a ∣_ U') :=
  isIso_pullbackCompMap_morphismRestrict_of_forall β g a (isomorphismOpen β) U' fun y => by
    rw [hU', ← hX]
    exact ⟨fun h => by by_contra h'; exact h h', fun h h' => h' h⟩

/-- **The fibre map off the contracted fibres** (blueprint `lem:sm-bd-fibre-iso`, the form used in
Lemma 4.4.2): if the points of the fibre `C_s` lying over `Z(β)` are those of `X`, then
`β_s : C′_s → C_s` is an isomorphism over every open of `C_s` with complement `X`. -/
theorem isIso_fiberMap_restrict_of_center (s : S) (X : Set ↥(g.fiber s))
    (hX : ∀ y, g.fiberι s y ∈ center β ↔ y ∈ X) (U' : (g.fiber s).Opens)
    (hU' : ∀ y, y ∈ U' ↔ y ∉ X) : IsIso (Curves.fiberMap β g s ∣_ U') :=
  isIso_pullbackCompMap_restrict_of_center β g _ X hX U' hU'

end DeJongAlterations.StableModification.BlowDown
