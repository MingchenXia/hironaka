/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Global.StableOpenStatement
import DeJongAlterations.StableModification.BlowDown.NumericalDescent
import DeJongAlterations.StableModification.DeJong.NodalBaseChange

/-!
# Numerical stability is independent of the geometric point

Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2 (stability of a
multipointed curve over a field is a geometric notion, checked over any algebraically closed
extension); ERRATA DJA-O36 (invariance in both directions is needed by node G4 of `PLAN-T5.md`).

Let `β ≫ g : X ⟶ C ⟶ S` with `β ≫ g` proper and `g` locally of finite type, `a : Spec K ⟶ S` a
geometric point (`K` algebraically closed) and `ψ : K →+* Ω` a field extension. With
`π : X_{Ω} ⟶ X_K` the base change:

* `numericallyStableFibre_comp_specMap` (descent, the general-base form of lane T44E's
  `BlowDown.NoClosedExc.NumericalDescent`, same proof): numerical stability of `X_K` implies that
  of `X_Ω`;
* `numericallyStableFibre_of_comp_specMap` (**ascent**): numerical stability of `X_Ω` implies that
  of `X_K`. For a contracted component `Z = closure {v}` of `X_K` with `p_a(Z_red) = 0`, `π⁻¹(Z)`
  is an irreducible component of `X_Ω` (lane T44E's `exists_eq_preimage_of_mem_irreducibleComponents`
  and maximality of `Z`), contracted (the image of `Z` is a closed point of `C_K`, whose preimage
  in `C_Ω` is one point, `subsingleton_preimage_of_isClosed`) and of arithmetic genus `0`
  (`arithmeticGenus_preimage_closure`), so it has at least three special points. Special points of
  `X_Ω` map to special points of `X_K` (base change of smoothness). If `Z` had at most two special
  points, they would be closed points (a finite closed subset of a Jacobson space), whose preimages
  under `π` are single points; so `π⁻¹(Z)` would have at most two special points.
* `exists_common_extension`: two geometric points over the same point `s` of `S` have a common
  algebraically closed extension (a residue field of `K₁ ⊗_{κ(s)} K₂`, algebraically closed);
* `isNumericallyStableAt_of_numericallyStableFibre`: numerical stability of one geometric fibre
  over `s` implies `IsNumericallyStableAt β g D' s`.

Blueprint: `sm-global-stable-open.tex`, `lem:sm-gso-fibre-closed-point`,
`prop:sm-gso-numerical-ascent`, `lem:sm-gso-common-extension`, `cor:sm-gso-one-point`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology TensorProduct

namespace DeJongAlterations.StableModification.Global

universe u

open Cohomology CurvesField.Genus BlowDown.ClosureComponent BlowDown.ExcSpecialize
  BlowDown.NumericalDescent
open Curves (pullbackCompMap)

set_option backward.isDefEq.respectTransparency false

section FibreOfClosedPoint

variable {K Ω : Type u} [Field K] [IsAlgClosed K] [Field Ω] (ψ : K →+* Ω) {Y : Scheme.{u}}
  (q : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {P : Scheme.{u}} {π : P ⟶ Y}
  {snd : P ⟶ Spec (CommRingCat.of Ω)}

/-- **The fibre of a field extension over a closed point is one point** (blueprint
`lem:sm-gso-fibre-closed-point`): for `Y` locally of finite type over an algebraically closed `K`,
a field extension `K → Ω` and a closed point `y` of `Y`, the preimage of `y` in `Y ×_K Ω` has at
most one point. The residue field of `y` is `K` (`residueFieldIsoBase`), so the fibre is
`Spec κ(y) ×_K Spec Ω ≅ Spec Ω`. -/
theorem subsingleton_preimage_of_isClosed
    (H : IsPullback π snd q (Spec.map (CommRingCat.ofHom ψ))) (y : Y)
    (hy : IsClosed ({y} : Set Y)) : (π ⁻¹' {y}).Subsingleton := by
  let j := Y.fromSpecResidueField y
  have hiso : IsIso (j ≫ q) := by
    rw [← SpecMap_residueFieldIsoBase_inv q y hy]
    infer_instance
  have H₀ := IsPullback.of_hasPullback π j
  have Hp : IsPullback (pullback.fst π j ≫ snd) (pullback.snd π j)
      (Spec.map (CommRingCat.ofHom ψ)) (j ≫ q) := H₀.paste_horiz H.flip
  have : IsIso (pullback.fst π j ≫ snd) := Hp.isIso_fst_of_isIso
  have hss : Subsingleton (pullback (C := Scheme.{u}) π j) :=
    (pullback.fst π j ≫ snd).homeomorph.injective.subsingleton
  have hrange : Set.range (pullback.fst π j) = π ⁻¹' {y} := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← hrange]
  rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩
  rw [Subsingleton.elim x₁ x₂]

end FibreOfClosedPoint

section Extension

variable {X C S : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ S) (D' : X.IdealSheafData)

/-- **Descent of numerical stability along a field extension** (the general-base form of lane
T44E's `BlowDown.NumericalDescent.numericalDescent`, with the same proof): if `K` is algebraically
closed and the geometric fibre over `a : Spec K ⟶ S` is numerically stable, so is the fibre over
`Spec Ω ⟶ Spec K ⟶ S` for every extension `ψ : K →+* Ω` with `Ω` algebraically closed. -/
theorem numericallyStableFibre_comp_specMap [IsProper (β ≫ g)] {K : Type u} [Field K]
    [IsAlgClosed K] (a : Spec (.of K) ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ψ : K →+* Ω)
    (hst : NumericallyStableFibre β g D' a) :
    NumericallyStableFibre β g D' (Spec.map (CommRingCat.ofHom ψ) ≫ a) := by
  -- the square `X_Ω → X_K` over `Spec Ω → Spec K`
  let π : pullback (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) ⟶ pullback (β ≫ g) a :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
  have e1 : π ≫ pullback.fst (β ≫ g) a =
      pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) := by
    simp [π]
  have H : IsPullback π (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a))
      (pullback.snd (β ≫ g) a) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ (by simp [π]) (IsPullback.of_hasPullback _ _)
    rw [e1]
    exact IsPullback.of_hasPullback _ _
  -- finiteness properties of the fibres
  have : LocallyOfFinitePresentation (pullback.snd (β ≫ g) a) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    BlowDown.compactSpace_of_quasiCompact (pullback.snd (β ≫ g) a)
  have : CompactSpace
      (pullback (C := Scheme.{u}) (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a)) :=
    BlowDown.compactSpace_of_quasiCompact
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a))
  have : JacobsonSpace (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (β ≫ g) a)
  have hsurj : Function.Surjective π :=
    surjective_fst_of_isPullback ψ (pullback.snd (β ≫ g) a) H
  intro Z hZ hcontr _ _ hpa
  obtain ⟨v, hv, rfl⟩ := exists_eq_preimage_of_mem_irreducibleComponents ψ
    (pullback.snd (β ≫ g) a) H hZ
  -- `closure {v}` is contracted
  have hcontr' : (pullbackCompMap β g a '' closure {v}).Subsingleton := by
    let πC : pullback g (Spec.map (CommRingCat.ofHom ψ) ≫ a) ⟶ pullback g a :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
    have hcomm : pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ a) ≫ πC =
        π ≫ pullbackCompMap β g a := by
      ext <;> simp [πC, π, pullbackCompMap]
    have hpt : ∀ x, pullbackCompMap β g a (π x) =
        πC (pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ a) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    rw [← Set.image_preimage_eq (closure {v}) hsurj, Set.image_image]
    simp_rw [hpt]
    rw [← Set.image_image]
    exact hcontr.image _
  -- `p_a(closure {v}) = 0`
  have : CompactSpace (closureScheme v) := compactSpace_closureScheme v
  have : IsSeparated (terminal.from (closureScheme v)) := by
    have e : closureι v ≫ pullback.snd (β ≫ g) a ≫ terminal.from _ =
        terminal.from (closureScheme v) := terminal.hom_ext _ _
    rw [← e]
    infer_instance
  have hpa' : arithmeticGenus (closureScheme v)
      (structureCoeff (closureι v ≫ pullback.snd (β ≫ g) a)) = 0 := by
    rw [← arithmeticGenus_preimage_closure ψ (pullback.snd (β ≫ g) a) H v]
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
    (isClosed_closure.inter (isClosed_specialPoints (β ≫ g) D' a)) h3
  have hsub : closure {v} ∩ BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' a ∩
      closedPoints (pullback (C := Scheme.{u}) (β ≫ g) a) ⊆
        π '' (π ⁻¹' closure {v} ∩
          BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' (Spec.map (CommRingCat.ofHom ψ) ≫ a)) := by
    rintro y ⟨⟨hyv, hys⟩, hyc⟩
    obtain ⟨x, hxc, rfl⟩ := exists_isClosed_singleton_and_eq ψ
      (pullback.snd (β ≫ g) a) H y hyc
    refine ⟨x, ⟨hyv, ?_⟩, rfl⟩
    rcases hys with hD | hns
    · left
      have hx : pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) x =
          pullback.fst (β ≫ g) a (π x) := by
        rw [← Scheme.Hom.comp_apply, e1]
      change pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) x ∈
        (D'.support : Set X)
      rw [hx]
      exact hD
    · right
      intro hsm
      exact hns (isSmoothAt_of_isPullback ψ (pullback.snd (β ≫ g) a) H x hyc hsm)
  calc (3 : ℕ∞) ≤ _ := h3'
    _ ≤ _ := Set.encard_le_encard hsub
    _ ≤ _ := Set.encard_image_le _ _

/-- **Ascent of numerical stability along a field extension** (blueprint
`prop:sm-gso-numerical-ascent`; ERRATA DJA-O36): if `K` is algebraically closed and the geometric
fibre over `Spec Ω ⟶ Spec K ⟶ S` is numerically stable for a field extension `ψ : K →+* Ω`, so is
the fibre over `a : Spec K ⟶ S`. -/
theorem numericallyStableFibre_of_comp_specMap [IsProper (β ≫ g)] [LocallyOfFiniteType g]
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S) {Ω : Type u} [Field Ω]
    (ψ : K →+* Ω) (hst : NumericallyStableFibre β g D' (Spec.map (CommRingCat.ofHom ψ) ≫ a)) :
    NumericallyStableFibre β g D' a := by
  -- the squares `X_Ω → X_K` and `C_Ω → C_K` over `Spec Ω → Spec K`
  let π : pullback (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) ⟶ pullback (β ≫ g) a :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
  have e1 : π ≫ pullback.fst (β ≫ g) a =
      pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) := by
    simp [π]
  have H : IsPullback π (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a))
      (pullback.snd (β ≫ g) a) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ (by simp [π]) (IsPullback.of_hasPullback _ _)
    rw [e1]
    exact IsPullback.of_hasPullback _ _
  let πC : pullback g (Spec.map (CommRingCat.ofHom ψ) ≫ a) ⟶ pullback g a :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _) (by simp) (by simp)
  have e1C : πC ≫ pullback.fst g a = pullback.fst g (Spec.map (CommRingCat.ofHom ψ) ≫ a) := by
    simp [πC]
  have HC : IsPullback πC (pullback.snd g (Spec.map (CommRingCat.ofHom ψ) ≫ a))
      (pullback.snd g a) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ (by simp [πC]) (IsPullback.of_hasPullback _ _)
    rw [e1C]
    exact IsPullback.of_hasPullback _ _
  have hcomm : pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ a) ≫ πC =
      π ≫ pullbackCompMap β g a := by
    ext <;> simp [πC, π, pullbackCompMap]
  have hpt : ∀ x, πC (pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ a) x) =
      pullbackCompMap β g a (π x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  -- finiteness properties of the fibres
  have : LocallyOfFinitePresentation (pullback.snd (β ≫ g) a) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    BlowDown.compactSpace_of_quasiCompact (pullback.snd (β ≫ g) a)
  have : CompactSpace
      (pullback (C := Scheme.{u}) (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a)) :=
    BlowDown.compactSpace_of_quasiCompact
      (pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a))
  have : JacobsonSpace (pullback (C := Scheme.{u}) (β ≫ g) a) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (β ≫ g) a)
  have hsurj : Function.Surjective π :=
    surjective_fst_of_isPullback ψ (pullback.snd (β ≫ g) a) H
  intro Z hZ hcontr _ _ hpa
  obtain ⟨v, hv⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hvZ : closure {v} = Z := hv
  subst hvZ
  -- `π⁻¹(closure {v})` is an irreducible component of `X_Ω`
  have hirr := isIrreducible_preimage_closure ψ (pullback.snd (β ≫ g) a) H v
  obtain ⟨Z', hZ', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  obtain ⟨v', hv', rfl⟩ := exists_eq_preimage_of_mem_irreducibleComponents ψ
    (pullback.snd (β ≫ g) a) H hZ'
  have hle : closure {v} ⊆ closure {v'} := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    exact hsub hy
  have heq : closure {v} = closure {v'} := hle.antisymm (hZ.2 hv'.1 hle)
  have hZΩ : π ⁻¹' closure {v} ∈ irreducibleComponents
      (pullback (C := Scheme.{u}) (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a)) := by
    rw [heq]
    exact hZ'
  -- `π⁻¹(closure {v})` is contracted: the image of `closure {v}` is a closed point
  have hcontrΩ : (pullbackCompMap β g (Spec.map (CommRingCat.ofHom ψ) ≫ a) ''
      (π ⁻¹' closure {v})).Subsingleton := by
    obtain ⟨y₀, hy₀, hy₀c⟩ := (isClosed_of_mem_irreducibleComponents _ hZ).exists_closed_singleton
      ⟨v, subset_closure rfl⟩
    have hc : IsClosed ({pullbackCompMap β g a y₀} : Set (pullback (C := Scheme.{u}) g a)) :=
      Curves.isClosed_image_of_isClosed (q := pullback.snd (β ≫ g) a)
        (q' := pullback.snd g a) (pullbackCompMap β g a) (Curves.pullbackCompMap_snd β g a) hy₀c
    have hfib := subsingleton_preimage_of_isClosed ψ (pullback.snd g a) HC _ hc
    refine hfib.anti ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, hpt, Set.mem_singleton_iff]
    exact hcontr ⟨π x, hx, rfl⟩ ⟨y₀, hy₀, rfl⟩
  -- `p_a(π⁻¹(closure {v})_red) = 0`
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme :=
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι.isClosedEmbedding.compactSpace
  have : IsSeparated (terminal.from (Scheme.IdealSheafData.vanishingIdeal
      ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme) := by
    have e : (Scheme.IdealSheafData.vanishingIdeal
        ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι ≫
          pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) ≫ terminal.from _ =
        terminal.from _ := terminal.hom_ext _ _
    rw [← e]
    infer_instance
  have : CompactSpace (closureScheme v) := compactSpace_closureScheme v
  have : IsSeparated (terminal.from (closureScheme v)) := by
    have e : closureι v ≫ pullback.snd (β ≫ g) a ≫ terminal.from _ =
        terminal.from (closureScheme v) := terminal.hom_ext _ _
    rw [← e]
    infer_instance
  have hpaΩ : arithmeticGenus (Scheme.IdealSheafData.vanishingIdeal
        ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subscheme
      (structureCoeff ((Scheme.IdealSheafData.vanishingIdeal
        ⟨π ⁻¹' closure {v}, isClosed_closure.preimage π.continuous⟩).subschemeι ≫
          pullback.snd (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a))) = 0 := by
    rw [arithmeticGenus_preimage_closure ψ (pullback.snd (β ≫ g) a) H v]
    exact hpa
  have h3 := hst (π ⁻¹' closure {v}) hZΩ hcontrΩ hpaΩ
  -- special points of `X_Ω` lie over special points of `X_K`
  have hspec : π ⁻¹' closure {v} ∩
      BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' (Spec.map (CommRingCat.ofHom ψ) ≫ a) ⊆
        π ⁻¹' (closure {v} ∩ BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' a) := by
    rintro x ⟨hxv, hxs⟩
    refine ⟨hxv, ?_⟩
    rcases hxs with hD | hns
    · left
      have hx : pullback.fst (β ≫ g) (Spec.map (CommRingCat.ofHom ψ) ≫ a) x =
          pullback.fst (β ≫ g) a (π x) := by
        rw [← Scheme.Hom.comp_apply, e1]
      change pullback.fst (β ≫ g) a (π x) ∈ (D'.support : Set X)
      rw [← hx]
      exact hD
    · right
      intro hsm
      exact hns (DeJongAlterations.StableModification.DeJong.isSmoothAt_of_isPullback H x hsm)
  by_contra hlt
  push Not at hlt
  set F := closure {v} ∩ BlowDown.ExcSpecialize.specialPoints (β ≫ g) D' a with hF
  have hFfin : F.Finite := Set.encard_lt_top_iff.mp (hlt.trans_le le_top)
  have hFcl : IsClosed F := isClosed_closure.inter (isClosed_specialPoints (β ≫ g) D' a)
  have hFpts : ∀ y ∈ F, IsClosed ({y} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) := by
    have hcl : IsClosed (F ∩ closedPoints (pullback (C := Scheme.{u}) (β ≫ g) a)) := by
      rw [← Set.biUnion_of_singleton (F ∩ closedPoints _)]
      exact (hFfin.subset Set.inter_subset_left).isClosed_biUnion fun x hx => hx.2
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure hFcl.isLocallyClosed
    rw [hcl.closure_eq, hFcl.closure_eq] at h1
    intro y hy
    rw [← h1] at hy
    exact hy.2
  have hinj : Set.InjOn π (π ⁻¹' F) := fun x₁ hx₁ x₂ _ hx =>
    subsingleton_preimage_of_isClosed ψ (pullback.snd (β ≫ g) a) H (π x₁) (hFpts _ hx₁) rfl
      (by rw [Set.mem_preimage, Set.mem_singleton_iff, hx])
  have : (3 : ℕ∞) ≤ F.encard :=
    calc (3 : ℕ∞) ≤ _ := h3
      _ ≤ (π ⁻¹' F).encard := Set.encard_le_encard hspec
      _ = (π '' (π ⁻¹' F)).encard := (hinj.encard_image).symm
      _ ≤ F.encard := Set.encard_le_encard (Set.image_preimage_subset _ _)
  exact absurd hlt (not_lt.mpr this)

end Extension

section CommonExtension

/-- **Two geometric points over the same point have a common algebraically closed extension**
(blueprint `lem:sm-gso-common-extension`): if `a₁ : Spec K₁ ⟶ S` and `a₂ : Spec K₂ ⟶ S` both lie
over `s`, there are an algebraically closed field `Ω` and embeddings `Kᵢ → Ω` with
`Spec Ω ⟶ Spec K₁ ⟶ S = Spec Ω ⟶ Spec K₂ ⟶ S` (`Ω` the algebraic closure of a residue field of
`K₁ ⊗_{κ(s)} K₂`). -/
theorem exists_common_extension {S : Scheme.{u}} {s : S} {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    (a₁ : Spec (.of K₁) ⟶ S) (a₂ : Spec (.of K₂) ⟶ S) (h₁ : ∀ x, a₁ x = s)
    (h₂ : ∀ x, a₂ x = s) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (ψ₁ : K₁ →+* Ω) (ψ₂ : K₂ →+* Ω),
      Spec.map (CommRingCat.ofHom ψ₁) ≫ a₁ = Spec.map (CommRingCat.ofHom ψ₂) ≫ a₂ := by
  classical
  -- `aᵢ = Spec φᵢ ≫ (Spec κ(s) ⟶ S)`
  have hfac : ∀ {L : Type u} [Field L] (b : Spec (.of L) ⟶ S), (∀ x, b x = s) →
      ∃ φ : S.residueField s ⟶ .of L, Spec.map φ ≫ S.fromSpecResidueField s = b := by
    intro L _ b hb
    obtain ⟨⟨s', φ⟩, hφ⟩ := (S.SpecToEquivOfField L).symm.surjective b
    have hs' : s' = s := by
      rw [← hb (IsLocalRing.closedPoint L), ← hφ]
      simp [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply]
    subst hs'
    exact ⟨φ, hφ⟩
  obtain ⟨φ₁, rfl⟩ := hfac a₁ h₁
  obtain ⟨φ₂, rfl⟩ := hfac a₂ h₂
  let κ := S.residueField s
  let : Algebra κ K₁ := φ₁.hom.toAlgebra
  let : Algebra κ K₂ := φ₂.hom.toAlgebra
  let A := TensorProduct κ K₁ K₂
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  let Ω := AlgebraicClosure (A ⧸ M)
  let ψ₁ : K₁ →+* Ω := (algebraMap (A ⧸ M) Ω).comp
    ((Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom)
  let ψ₂ : K₂ →+* Ω := (algebraMap (A ⧸ M) Ω).comp
    ((Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight : K₂ →ₐ[κ] A).toRingHom)
  refine ⟨Ω, inferInstance, inferInstance, ψ₁, ψ₂, ?_⟩
  have hφ : φ₁ ≫ CommRingCat.ofHom ψ₁ = φ₂ ≫ CommRingCat.ofHom ψ₂ := by
    ext x
    change ψ₁ (algebraMap κ K₁ x) = ψ₂ (algebraMap κ K₂ x)
    have ht : (algebraMap κ K₁ x) ⊗ₜ[κ] (1 : K₂) = (1 : K₁) ⊗ₜ[κ] (algebraMap κ K₂ x) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    change algebraMap (A ⧸ M) Ω (Ideal.Quotient.mk M ((algebraMap κ K₁ x) ⊗ₜ[κ] (1 : K₂))) =
      algebraMap (A ⧸ M) Ω (Ideal.Quotient.mk M ((1 : K₁) ⊗ₜ[κ] (algebraMap κ K₂ x)))
    rw [ht]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hφ]

end CommonExtension

section OnePoint

variable {X C S : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ S) (D' : X.IdealSheafData)

/-- **One geometric fibre suffices** (blueprint `cor:sm-gso-one-point`; Temkin §1.2): if the
geometric fibre over one geometric point `a` over `s` is numerically stable, the geometric fibres
over all geometric points over `s` are (pass to a common algebraically closed extension,
`exists_common_extension`, by descent `numericallyStableFibre_comp_specMap` and ascent
`numericallyStableFibre_of_comp_specMap`). -/
theorem isNumericallyStableAt_of_numericallyStableFibre [IsProper (β ≫ g)]
    [LocallyOfFiniteType g] {s : S} {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (ha : ∀ x, a x = s) (h : NumericallyStableFibre β g D' a) :
    IsNumericallyStableAt β g D' s := by
  intro K' _ _ a' ha'
  obtain ⟨Ω, _, _, ψ, ψ', he⟩ := exists_common_extension a a' ha ha'
  have h1 := numericallyStableFibre_comp_specMap β g D' a ψ h
  rw [he] at h1
  exact numericallyStableFibre_of_comp_specMap β g D' a' ψ' h1

/-- Numerical stability over `s` is numerical stability of any one geometric fibre over `s`. -/
theorem isNumericallyStableAt_iff_numericallyStableFibre [IsProper (β ≫ g)]
    [LocallyOfFiniteType g] {s : S} {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (ha : ∀ x, a x = s) :
    IsNumericallyStableAt β g D' s ↔ NumericallyStableFibre β g D' a :=
  ⟨fun h ↦ h K a ha, isNumericallyStableAt_of_numericallyStableFibre β g D' a ha⟩

end OnePoint

end DeJongAlterations.StableModification.Global
