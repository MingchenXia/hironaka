/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NumericalDescentFibre

/-!
# Numerical stability descends from residue fibres to geometric fibres

This file proves `BlowDown.NoClosedExc.NumericalDescent` (`numericalDescent`): for
`β ≫ g : X → C → Spec V` proper, a point `t` of `Spec V` with algebraically closed residue field
`κ(t)` and a geometric point `a : Spec K → Spec V` over `t` (`K` algebraically closed), numerical
stability of the fibre `X_t` (`NoClosedExc.NumericallyStableFibre`) implies that of `X_a`.

The point `a` factors through `Spec κ(t)` (`exists_comp_residuePt_eq`), so `X_a = X_t ×_{κ(t)} K`.
Let `Z ⊆ X_a` be a contracted component with `p_a(Z_red) = 0`. Then:

* `Z = π⁻¹(closure {v})` for a component `closure {v}` of `X_t`
  (`exists_eq_preimage_of_mem_irreducibleComponents`);
* `closure {v}` is contracted (its image in `C_t` is the image of that of `Z` in `C_a`) and
  `p_a(closure{v}) = p_a(Z_red) = 0` (`arithmeticGenus_preimage_closure`), so by hypothesis it
  carries at least three special points, hence at least three closed special points (`X_t` is a
  Jacobson space and the special locus is closed, `three_le_encard_inter_closedPoints`);
* every closed point `y` of `X_t` is the image of a closed point `x` of `X_a`
  (`exists_isClosed_singleton_and_eq`), `x ∈ Z`, and `x` is special if `y` is: the marks are
  pulled back from `X`, and smoothness at `x` implies smoothness at `y`
  (`isSmoothAt_of_isPullback`).

This is Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2
(stability of a multipointed curve over a field is a geometric notion, checked over any
algebraically closed extension).

Blueprint: `sm-blow-down-unconditional.tex`, `prop:sm-bdu-numerical-descent`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.NumericalDescent

universe u

open Cohomology CurvesField.Genus ClosureComponent ExcSpecialize NoClosedExc
open Curves (pullbackCompMap)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The special locus of a fibre locally of finite presentation over a field is closed: it is the
union of the preimage of the marks and the complement of the smooth locus. -/
theorem isClosed_specialPoints {X S : Scheme.{u}} (f : X ⟶ S) (D' : X.IdealSheafData) {K : Type u}
    [Field K] (a : Spec (.of K) ⟶ S) [LocallyOfFinitePresentation (pullback.snd f a)] :
    IsClosed (specialPoints f D' a) := by
  refine (D'.support.isClosed.preimage (pullback.fst f a).continuous).union ?_
  have : {y | ¬ DeJong.IsSmoothAt (pullback.snd f a) y} =
      ((pullback.snd f a).smoothLocus : Set (pullback (C := Scheme.{u}) f a))ᶜ := by
    ext y
    rfl
  rw [this]
  exact (pullback.snd f a).smoothLocus.isOpen.isClosed_compl

/-- **Numerical stability descends from residue fibres to geometric fibres** (Temkin, §1.2;
blueprint `prop:sm-bdu-numerical-descent`): the named proposition
`BlowDown.NoClosedExc.NumericalDescent` holds. -/
theorem numericalDescent : NoClosedExc.NumericalDescent.{u} := by
  intro V _ X C β g D' _ t _ hst K _ _ a ha
  obtain ⟨ψ, rfl⟩ := exists_comp_residuePt_eq t a ha
  -- the square `X_a → X_t` over `Spec K → Spec κ(t)`
  let π : pullback (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) ⟶
      pullback (β ≫ g) (residuePt t) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
  have e1 : π ≫ pullback.fst (β ≫ g) (residuePt t) =
      pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) := by
    simp [π]
  have H : IsPullback π (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t))
      (pullback.snd (β ≫ g) (residuePt t)) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ (by simp [π]) (IsPullback.of_hasPullback _ _)
    rw [e1]
    exact IsPullback.of_hasPullback _ _
  -- finiteness properties of the fibres
  have : LocallyOfFinitePresentation (pullback.snd (β ≫ g) (residuePt t)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)) :=
    BlowDown.compactSpace_of_quasiCompact (pullback.snd (β ≫ g) (residuePt t))
  have : CompactSpace
      (pullback (C := Scheme.{u}) (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t)) :=
    BlowDown.compactSpace_of_quasiCompact
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t))
  have : JacobsonSpace (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (β ≫ g) (residuePt t))
  have hsurj : Function.Surjective π :=
    surjective_fst_of_isPullback ψ (pullback.snd (β ≫ g) (residuePt t)) H
  intro Z hZ hcontr _ _ hpa
  obtain ⟨v, hv, rfl⟩ := exists_eq_preimage_of_mem_irreducibleComponents ψ
    (pullback.snd (β ≫ g) (residuePt t)) H hZ
  -- `closure {v}` is contracted
  have hcontr' : (pullbackCompMap β g (residuePt t) '' closure {v}).Subsingleton := by
    let πC : pullback g (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) ⟶
        pullback g (residuePt t) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
    have hcomm : pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) ≫ πC =
        π ≫ pullbackCompMap β g (residuePt t) := by
      ext <;> simp [πC, π, pullbackCompMap]
    have hpt : ∀ x, pullbackCompMap β g (residuePt t) (π x) =
        πC (pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    rw [← Set.image_preimage_eq (closure {v}) hsurj, Set.image_image]
    simp_rw [hpt]
    rw [← Set.image_image]
    exact hcontr.image _
  -- `p_a(closure {v}) = 0`
  have : CompactSpace (closureScheme v) := compactSpace_closureScheme v
  have : IsSeparated (terminal.from (closureScheme v)) := by
    have e : closureι v ≫ pullback.snd (β ≫ g) (residuePt t) ≫ terminal.from _ =
        terminal.from (closureScheme v) := terminal.hom_ext _ _
    rw [← e]
    infer_instance
  have hpa' : arithmeticGenus (closureScheme v)
      (structureCoeff (closureι v ≫ pullback.snd (β ≫ g) (residuePt t))) = 0 := by
    rw [← arithmeticGenus_preimage_closure ψ (pullback.snd (β ≫ g) (residuePt t)) H v]
    exact hpa
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {v}, isClosed_of_mem_irreducibleComponents _ hv⟩).subscheme :=
    compactSpace_closureScheme v
  have : IsSeparated (terminal.from (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {v}, isClosed_of_mem_irreducibleComponents _ hv⟩).subscheme) :=
    ‹IsSeparated (terminal.from (closureScheme v))›
  have h3 := hst (closure {v}) hv hcontr' hpa'
  -- at least three closed special points on `closure {v}`
  have h3' := three_le_encard_inter_closedPoints
    (isClosed_closure.inter (isClosed_specialPoints (β ≫ g) D' (residuePt t))) h3
  have hsub : closure {v} ∩ specialPoints (β ≫ g) D' (residuePt t) ∩
      closedPoints (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)) ⊆
        π '' (π ⁻¹' closure {v} ∩
          specialPoints (β ≫ g) D' (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t)) := by
    rintro y ⟨⟨hyv, hys⟩, hyc⟩
    obtain ⟨x, hxc, rfl⟩ := exists_isClosed_singleton_and_eq ψ
      (pullback.snd (β ≫ g) (residuePt t)) H y hyc
    refine ⟨x, ⟨hyv, ?_⟩, rfl⟩
    rcases hys with hD | hns
    · left
      have hx : pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) x =
          pullback.fst (β ≫ g) (residuePt t) (π x) := by
        rw [← Scheme.Hom.comp_apply, e1]
      change pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ residuePt t) x ∈
        (D'.support : Set X)
      rw [hx]
      exact hD
    · right
      intro hsm
      exact hns (isSmoothAt_of_isPullback ψ (pullback.snd (β ≫ g) (residuePt t)) H x hyc hsm)
  calc (3 : ℕ∞) ≤ _ := h3'
    _ ≤ _ := Set.encard_le_encard hsub
    _ ≤ _ := Set.encard_image_le _ _

end DeJongAlterations.StableModification.BlowDown.NumericalDescent
