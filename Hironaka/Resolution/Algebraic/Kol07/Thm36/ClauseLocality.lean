/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.SncLocal
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clauses (1)–(3) of Theorem 36 are local on the base

The three clauses of [Kol07, Theorem 36], a smooth end result, an isomorphism over the smooth locus,
and a simple normal crossing preimage of the singular locus, are local on the base. This is not
stated in the sources as such: Kollár's gluing of the local resolutions ([Kol07, Proposition 37],
"Putting together the proof of (27) with (37)" at the statement of Theorem 36) uses it implicitly,
and his only locality remark, "(34.1) is a local property" in the proof of Theorem 36, concerns the
functoriality clause. For a blow-up sequence `T` on `X` and a family of open immersions
`e i : W i ⟶ X` covering `X`:

* `smooth_composite_of_forall_pullback`: the end result of `T` is smooth over a base `f : X ⟶ B` as
  soon as every `T.pullback (e i)` has a smooth end result over `e i ≫ f`; the last stage of `T`
  is covered by the last stages of the `T.pullback (e i)` (the stage lifts at the last index are
  the base changes of the `e i`, `isPullback_pullbackStageHom`), and `Smooth` is Zariski-local at
  the source; `smooth_composite_pullback_of_isOpenImmersion` is the converse restriction.
* `isIso_morphismRestrict_composite_of_forall_pullback`: `T.composite` is an isomorphism over an
  open `V` of `X` as soon as every `(T.pullback (e i)).composite` is an isomorphism over
  `(e i) ⁻¹ᵁ V`; isomorphisms are Zariski-local at the target, and over the piece
  `V ∩ range (e i)` the restriction of `T.composite` is the base change of `T.composite` along
  `(e i) ⁻¹ᵁ V → X`, which is the restriction of the pulled-back composite (Mathlib's
  `morphismRestrictRestrict` and `morphismRestrictOpensRange`, the pasted square);
  `isIso_morphismRestrict_pullback_of_isOpenImmersion` is the converse restriction.
* `exists_snc_support_composite_of_forall_pullback`: the preimage of a set `S` of `X` under
  `T.composite` is the support of a simple normal crossing family on the last stage as soon as it
  is on every `T.pullback (e i)` (`Hironaka.Snc.exists_snc_of_openCover` on the cover of the last
  stage by the last stages of the pulled-back sequences, Noetherian by `isNoetherian_stage`);
  `exists_snc_support_pullback_of_isOpenImmersion` is the converse restriction (the family pulled
  back along the stage lift, `isSnc_comap_of_smooth`; `coe_support_comap`), and
  `preimage_compl_smoothLocus_eq` transports the singular locus along an open immersion.

Both uses are instances of the same statements: the finite affine cover of a member of the class
(the descent of the resolution functor,
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Theorem36Assembly`), and the empty cover of the empty
scheme (the clauses hold vacuously there). The `HEq` transports
`stage_pullbackStageIdx_last`, `heq_stageMap_pullbackStageIdx_last`, `smooth_comp_of_heq` and
`isIso_morphismRestrict_of_heq` pass between the stage indexed by the transport of the last index
(where the stage squares live) and the composite.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence

namespace Hironaka.Resolution


/-- Transport of smoothness of a composite along a `HEq` of the first factor. -/
theorem smooth_comp_of_heq {A B W V : Scheme.{u}} (e : A = B) {g : A ⟶ W} {g' : B ⟶ W}
    (hg : HEq g g') (p : W ⟶ V) (h : Smooth (g ≫ p)) : Smooth (g' ≫ p) := by
  subst e
  cases hg
  exact h

/-- The stage of `T.pullback ι` indexed by the transport of the last index (`pullbackStageIdx_last`)
is its last stage. -/
theorem stage_pullbackStageIdx_last {X W : Scheme.{u}} (T : BlowUpSequence X) (ι : W ⟶ X) :
    (T.pullback ι).stage (T.pullbackStageIdx ι (Fin.last _)) = (T.pullback ι).last := by
  unfold BlowUpSequence.last
  rw [pullbackStageIdx_last]

/-- The stage map of `T.pullback ι` at the transport of the last index is its composite. -/
theorem heq_stageMap_pullbackStageIdx_last {X W : Scheme.{u}} (T : BlowUpSequence X) (ι : W ⟶ X) :
    HEq ((T.pullback ι).stageMap (T.pullbackStageIdx ι (Fin.last _))) (T.pullback ι).composite := by
  unfold BlowUpSequence.composite
  rw [pullbackStageIdx_last]
  exact HEq.rfl

/-- Smoothness of the end result restricts along an open immersion of the base: the last stage of
`T.pullback ι` is an open subscheme of the last stage of `T`. -/
theorem smooth_composite_pullback_of_isOpenImmersion {X W B : Scheme.{u}} (T : BlowUpSequence X)
    (ι : W ⟶ X) [IsOpenImmersion ι] (f : X ⟶ B) (h : Smooth (T.composite ≫ f)) :
    Smooth ((T.pullback ι).composite ≫ ι ≫ f) := by
  have hsq := isPullback_pullbackStageHom T ι (Fin.last _)
  have hopen : IsOpenImmersion (T.pullbackStageHom ι (Fin.last _)) :=
    property_of_isPullback @IsOpenImmersion hsq inferInstance
  have h' : Smooth (T.stageMap (Fin.last _) ≫ f) := h
  have h1 : Smooth (T.pullbackStageHom ι (Fin.last _) ≫ T.stageMap (Fin.last _) ≫ f) :=
    inferInstance
  rw [← Category.assoc, hsq.w, Category.assoc] at h1
  exact smooth_comp_of_heq (stage_pullbackStageIdx_last T ι)
    (heq_stageMap_pullbackStageIdx_last T ι) (ι ≫ f) h1

/-- Clause (1) of [Kol07, Theorem 36] is local on the base (not stated in the sources): for a
family of open immersions `e i : W i ⟶ X` covering `X`, the end result of `T` is smooth over the
base as soon as every `T.pullback (e i)` has a smooth end result over the base. -/
theorem smooth_composite_of_forall_pullback {ι : Type*} {X B : Scheme.{u}} {W : ι → Scheme.{u}}
    (T : BlowUpSequence X) (e : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (e i)]
    (hcov : ∀ x, ∃ i w, e i w = x) (f : X ⟶ B)
    (h : ∀ i, Smooth ((T.pullback (e i)).composite ≫ e i ≫ f)) : Smooth (T.composite ≫ f) := by
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  change Smooth (T.stageMap (Fin.last _) ≫ f)
  -- the preimages of the pieces cover the last stage
  let U : ι → (T.stage (Fin.last T.length)).Opens := fun i =>
    T.stageMap (Fin.last _) ⁻¹ᵁ (e i).opensRange
  have hU : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, w, hw⟩ := hcov (T.stageMap (Fin.last _) y)
    exact Opens.mem_iSup.mpr ⟨i, ⟨w, hw⟩⟩
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth) U hU]
  intro i
  have hsq := isPullback_pullbackStageHom T (e i) (Fin.last _)
  have hopen : IsOpenImmersion (T.pullbackStageHom (e i) (Fin.last _)) :=
    property_of_isPullback @IsOpenImmersion hsq inferInstance
  have hrange : Set.range ⇑(U i).ι = Set.range ⇑(T.pullbackStageHom (e i) (Fin.last _)) := by
    rw [Scheme.Opens.range_ι, range_fst_of_isPullback hsq]
    rfl
  have he := IsOpenImmersion.isoOfRangeEq_hom_fac (U i).ι
    (T.pullbackStageHom (e i) (Fin.last _)) hrange
  have hi : Smooth ((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _)) ≫
      e i ≫ f) :=
    smooth_comp_of_heq (stage_pullbackStageIdx_last T (e i)).symm
      (heq_stageMap_pullbackStageIdx_last T (e i)).symm (e i ≫ f) (h i)
  rw [← Category.assoc, ← hsq.w, Category.assoc] at hi
  have : Smooth ((IsOpenImmersion.isoOfRangeEq (U i).ι _ hrange).hom ≫
      T.pullbackStageHom (e i) (Fin.last _) ≫ T.stageMap (Fin.last _) ≫ f) := inferInstance
  rwa [← Category.assoc, he] at this


/-- Transport of `IsIso` of a restriction along a `HEq` of the morphism. -/
theorem isIso_morphismRestrict_of_heq {A B W : Scheme.{u}} (e : A = B) {g : A ⟶ W} {g' : B ⟶ W}
    (hg : HEq g g') (V : W.Opens) (h : IsIso (g ∣_ V)) : IsIso (g' ∣_ V) := by
  subst e
  cases hg
  exact h

/-- Clause (2) of [Kol07, Theorem 36] is local on the base (not stated in the sources):
`IsIso (T.composite ∣_ V)` holds as soon as, for a family of open immersions `e i : W i ⟶ X`
covering `X`, every `(T.pullback (e i)).composite` is an isomorphism over `(e i) ⁻¹ᵁ V`. -/
theorem isIso_morphismRestrict_composite_of_forall_pullback {ι : Type u} {X : Scheme.{u}}
    {W : ι → Scheme.{u}} (T : BlowUpSequence X) (e : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (e i)]
    (hcov : ∀ x, ∃ i w, e i w = x) (V : X.Opens)
    (h : ∀ i, IsIso ((T.pullback (e i)).composite ∣_ ((e i) ⁻¹ᵁ V))) :
    IsIso (T.composite ∣_ V) := by
  change IsIso (T.stageMap (Fin.last _) ∣_ V)
  have hsq : ∀ i, IsPullback (T.pullbackStageHom (e i) (Fin.last _))
      ((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _)))
      (T.stageMap (Fin.last _)) (e i) := fun i => isPullback_pullbackStageHom T (e i) (Fin.last _)
  have hiso : ∀ i, IsIso (((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _))) ∣_
      ((e i) ⁻¹ᵁ V)) := fun i =>
    isIso_morphismRestrict_of_heq (stage_pullbackStageIdx_last T (e i)).symm
      (heq_stageMap_pullbackStageIdx_last T (e i)).symm _ (h i)
  -- the open immersions `m i : (e i) ⁻¹ᵁ V ⟶ X`, whose ranges cover `V`
  have hm : ∀ i, Set.range ⇑(((e i) ⁻¹ᵁ V).ι ≫ e i) ⊆ (V : Set X) := by
    intro i
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have : ((e i) ⁻¹ᵁ V).ι w ∈ (e i) ⁻¹ᵁ V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    exact this
  let U : ι → (V : Scheme.{u}).Opens := fun i => V.ι ⁻¹ᵁ (((e i) ⁻¹ᵁ V).ι ≫ e i).opensRange
  have hU : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨i, w, hw⟩ := hcov (V.ι v)
    have hwV : w ∈ (e i) ⁻¹ᵁ V := by
      change e i w ∈ V
      rw [hw]
      exact v.2
    obtain ⟨z, hz⟩ : ∃ z, ((e i) ⁻¹ᵁ V).ι z = w := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι] at hwV
      exact hwV
    refine Opens.mem_iSup.mpr ⟨i, ⟨z, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hz, hw]
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro i
  -- `(f ∣_ V) ∣_ U i` is `f ∣_ (range (m i))`
  rw [MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict _ V (U i))]
  have himg : V.ι ''ᵁ U i = (((e i) ⁻¹ᵁ V).ι ≫ e i).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hm i)
  rw [himg, MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange _ _), MorphismProperty.isomorphisms.iff]
  -- the base change of `f` along `m i` is the restriction of the pulled-back stage map
  have hB : IsPullback (((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _))) ∣_
      ((e i) ⁻¹ᵁ V))
      ((((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _))) ⁻¹ᵁ
        ((e i) ⁻¹ᵁ V)).ι ≫ T.pullbackStageHom (e i) (Fin.last _))
      (((e i) ⁻¹ᵁ V).ι ≫ e i) (T.stageMap (Fin.last _)) :=
    (isPullback_morphismRestrict _ _).paste_vert (hsq i).flip
  have hcomp := hB.flip.isoPullback_hom_snd
  have := hiso i
  rw [← hcomp] at this
  exact IsIso.of_isIso_comp_left hB.flip.isoPullback.hom _


/-! ### Clause (3) and the converse restrictions -/


/-- The support of a pulled-back divisor family is the preimage of the support
(`Scheme.IdealSheafData.support_comap` componentwise). -/
theorem coe_support_comap {X Y : Scheme.{u}} (E : DivisorFamily X) (h : Y ⟶ X) :
    ((E.comap h).support : Set Y) = h ⁻¹' (E.support : Set X) := by
  rw [DivisorFamily.coe_support_eq_iUnion, DivisorFamily.coe_support_eq_iUnion, Set.preimage_iUnion]
  refine Set.iUnion_congr fun i => ?_
  change (((E.component i).comap h).support : Set Y) = _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- Transport of a simple-normal-crossing-support statement along a `HEq` of the morphism. -/
theorem exists_snc_support_of_heq {A B W : Scheme.{u}} (e : A = B) {g : A ⟶ W} {g' : B ⟶ W}
    (hg : HEq g g') (S : Set W)
    (h : ∃ F : DivisorFamily A, F.IsSnc ∧ (F.support : Set A) = g ⁻¹' S) :
    ∃ F : DivisorFamily B, F.IsSnc ∧ (F.support : Set B) = g' ⁻¹' S := by
  subst e
  cases hg
  exact h

/-- The simple-normal-crossing-support conclusion restricts along an open immersion `ι` of the base
when the end result is smooth over `k`: the family pulled back along the stage lift
(`isSnc_comap_of_smooth`). -/
theorem exists_snc_support_pullback_of_isOpenImmersion {k : Type u} [Field k] [CharZero k]
    {X W : Scheme.{u}} (T : BlowUpSequence X) (ι : W ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth (T.composite ≫ f)] (S : Set X)
    (h : ∃ F : DivisorFamily T.last, F.IsSnc ∧ (F.support : Set T.last) = T.composite ⁻¹' S) :
    ∃ F : DivisorFamily (T.pullback ι).last, F.IsSnc ∧
      (F.support : Set (T.pullback ι).last) = (T.pullback ι).composite ⁻¹' (ι ⁻¹' S) := by
  obtain ⟨F, hF, hsupp⟩ := h
  have hsq := isPullback_pullbackStageHom T ι (Fin.last _)
  have hopen : IsOpenImmersion (T.pullbackStageHom ι (Fin.last _)) :=
    property_of_isPullback @IsOpenImmersion hsq inferInstance
  have hsm : Smooth (T.stageMap (Fin.last _) ≫ f) := ‹Smooth (T.composite ≫ f)›
  have hsmι : Smooth (T.pullbackStageHom ι (Fin.last _)) := SmoothOfRelativeDimension.smooth 0 _
  have hpt : ∀ p, T.stageMap (Fin.last _) (T.pullbackStageHom ι (Fin.last _) p) =
      ι ((T.pullback ι).stageMap (T.pullbackStageIdx ι (Fin.last _)) p) := fun p => by
    have := congrArg (fun m => m p) hsq.w
    simpa only [Scheme.Hom.comp_apply] using this
  have hsc := coe_support_comap F (T.pullbackStageHom ι (Fin.last _))
  refine exists_snc_support_of_heq (stage_pullbackStageIdx_last T ι)
    (heq_stageMap_pullbackStageIdx_last T ι) (ι ⁻¹' S)
    ⟨F.comap (T.pullbackStageHom ι (Fin.last _)), ?_, ?_⟩
  · exact isSnc_comap_of_smooth (T.stageMap (Fin.last _) ≫ f) (T.pullbackStageHom ι (Fin.last _)) hF
  · rw [hsc, hsupp, ← Set.preimage_comp, ← Set.preimage_comp]
    congr 1
    funext p
    exact hpt p

/-- Clause (3) of [Kol07, Theorem 36] is local on the base (not stated in the sources): for a
family of open immersions `e i : W i ⟶ X` covering `X`, if every
`(T.pullback (e i)).composite ⁻¹' ((e i) ⁻¹' S)` is the support of a simple normal crossing family,
so is `T.composite ⁻¹' S` (`Hironaka.Snc.exists_snc_of_openCover`); the last stage of `T` is
Noetherian because `X` is (`isNoetherian_stage`). -/
theorem exists_snc_support_composite_of_forall_pullback {ι : Type u} {X : Scheme.{u}}
    [IsNoetherian X] {W : ι → Scheme.{u}} (T : BlowUpSequence X) (e : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (e i)] (hcov : ∀ x, ∃ i w, e i w = x) (S : Set X)
    (h : ∀ i, ∃ F : DivisorFamily (T.pullback (e i)).last, F.IsSnc ∧
      (F.support : Set (T.pullback (e i)).last) = (T.pullback (e i)).composite ⁻¹' (e i ⁻¹' S)) :
    ∃ F : DivisorFamily T.last, F.IsSnc ∧ (F.support : Set T.last) = T.composite ⁻¹' S := by
  have : IsNoetherian T.last := isNoetherian_stage T (Fin.last _)
  -- the pieces: the stage lifts at the last index cover the last stage
  have hsq : ∀ i, IsPullback (T.pullbackStageHom (e i) (Fin.last _))
      ((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _)))
      (T.stageMap (Fin.last _)) (e i) := fun i => isPullback_pullbackStageHom T (e i) (Fin.last _)
  have hopen : ∀ i, IsOpenImmersion (T.pullbackStageHom (e i) (Fin.last _)) := fun i =>
    property_of_isPullback @IsOpenImmersion (hsq i) inferInstance
  have hgcov : ∀ y : T.last, ∃ i p, T.pullbackStageHom (e i) (Fin.last _) p = y := by
    intro y
    obtain ⟨i, w, hw⟩ := hcov (T.composite y)
    have hrng := range_fst_of_isPullback (hsq i)
    have hmem : y ∈ Set.range ⇑(T.pullbackStageHom (e i) (Fin.last _)) := by
      rw [hrng]
      exact ⟨w, hw⟩
    obtain ⟨p, hp⟩ := hmem
    exact ⟨i, p, hp⟩
  have hpt : ∀ (i : ι) (p : (T.pullback (e i)).stage (T.pullbackStageIdx (e i) (Fin.last _))),
      T.stageMap (Fin.last _) (T.pullbackStageHom (e i) (Fin.last _) p) =
        e i ((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _)) p) := by
    intro i p
    have := congrArg (fun m => m p) (hsq i).w
    simpa only [Scheme.Hom.comp_apply] using this
  let 𝒰 : T.last.OpenCover := Scheme.Cover.mkOfCovers ι _
    (fun i => (T.pullbackStageHom (e i) (Fin.last _) : _ ⟶ T.last)) hgcov hopen
  refine Hironaka.Snc.exists_snc_of_openCover (T.composite ⁻¹' S) 𝒰 fun i => ?_
  -- on the piece: the family of the pulled-back sequence, transported to the stage
  have hi := exists_snc_support_of_heq (stage_pullbackStageIdx_last T (e i)).symm
    (heq_stageMap_pullbackStageIdx_last T (e i)).symm (e i ⁻¹' S) (h i)
  obtain ⟨F, hF, hsupp⟩ := hi
  refine ⟨F, hF, ?_⟩
  change (F.support : Set ((T.pullback (e i)).stage (T.pullbackStageIdx (e i) (Fin.last _)))) =
    ⇑(T.pullbackStageHom (e i) (Fin.last _)) ⁻¹' (⇑T.composite ⁻¹' S)
  rw [hsupp]
  ext p
  change e i ((T.pullback (e i)).stageMap (T.pullbackStageIdx (e i) (Fin.last _)) p) ∈ S ↔
    T.stageMap (Fin.last _) (T.pullbackStageHom (e i) (Fin.last _) p) ∈ S
  rw [hpt i p]

/-- `IsIso` of the restriction over an open `V` restricts along an open immersion `ι` of the base:
`(T.pullback ι).composite` is an isomorphism over `ι ⁻¹ᵁ V` (the converse of
`isIso_morphismRestrict_composite_of_forall_pullback`, by the same identification). -/
theorem isIso_morphismRestrict_pullback_of_isOpenImmersion {X W : Scheme.{u}}
    (T : BlowUpSequence X) (ι : W ⟶ X) [IsOpenImmersion ι] (V : X.Opens)
    (h : IsIso (T.composite ∣_ V)) : IsIso ((T.pullback ι).composite ∣_ (ι ⁻¹ᵁ V)) := by
  have hsq := isPullback_pullbackStageHom T ι (Fin.last _)
  have hV : IsIso (T.stageMap (Fin.last _) ∣_ V) := h
  -- the open immersion `m : ι ⁻¹ᵁ V ⟶ X` and the open `U` of `V` it cuts out
  have hm : Set.range ⇑((ι ⁻¹ᵁ V).ι ≫ ι) ⊆ (V : Set X) := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have : (ι ⁻¹ᵁ V).ι w ∈ ι ⁻¹ᵁ V := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    exact this
  have hU : IsIso ((T.stageMap (Fin.last _) ∣_ V) ∣_ (V.ι ⁻¹ᵁ ((ι ⁻¹ᵁ V).ι ≫ ι).opensRange)) :=
    inferInstance
  rw [← MorphismProperty.isomorphisms.iff,
    MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (morphismRestrictRestrict _ V _)] at hU
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ ((ι ⁻¹ᵁ V).ι ≫ ι).opensRange) = ((ι ⁻¹ᵁ V).ι ≫ ι).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hm
  rw [himg, MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange _ _), MorphismProperty.isomorphisms.iff] at hU
  -- the base change of `f` along `m` is the restriction of the pulled-back stage map
  have hB : IsPullback (((T.pullback ι).stageMap (T.pullbackStageIdx ι (Fin.last _))) ∣_ (ι ⁻¹ᵁ V))
      ((((T.pullback ι).stageMap (T.pullbackStageIdx ι (Fin.last _))) ⁻¹ᵁ (ι ⁻¹ᵁ V)).ι ≫
        T.pullbackStageHom ι (Fin.last _))
      ((ι ⁻¹ᵁ V).ι ≫ ι) (T.stageMap (Fin.last _)) :=
    (isPullback_morphismRestrict _ _).paste_vert hsq.flip
  have hcomp := hB.flip.isoPullback_hom_snd
  have hc : IsIso (((T.pullback ι).stageMap (T.pullbackStageIdx ι (Fin.last _))) ∣_ (ι ⁻¹ᵁ V)) := by
    rw [← hcomp]
    infer_instance
  exact isIso_morphismRestrict_of_heq (stage_pullbackStageIdx_last T ι)
    (heq_stageMap_pullbackStageIdx_last T ι) _ hc

/-- The preimage of the singular locus along an open immersion `ι` is the singular locus of the
composite structure morphism, as sets (`Scheme.Hom.preimage_smoothLocus_eq`). -/
theorem preimage_compl_smoothLocus_eq {X W B : Scheme.{u}} (ι : W ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ B) [LocallyOfFinitePresentation f] :
    ι ⁻¹' ((f.smoothLocus : Set X)ᶜ) = ((ι ≫ f).smoothLocus : Set W)ᶜ := by
  rw [Set.preimage_compl]
  congr 1
  exact congrArg SetLike.coe (Scheme.Hom.preimage_smoothLocus_eq ι f)

end Hironaka.Resolution
