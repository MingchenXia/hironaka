/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.ChainRunErase
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Local
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Refinement
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Kernel
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackRun
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the realised Step 3 under flat morphisms: the general fold

The second clause of [Kol07, 34.1] for the third step of `BMO_{n,m}`: for a family `Φ'` on `Y`
refining `Φ` on `X` along a flat `h : Y ⟶ X` (no surjectivity), *the realised Step 3 on `Y` is
the pull-back of the realised Step 3 on `X` with the empty blow-ups deleted*, Kollár's "deleting
every blow-up `h^*π_i` whose centre is empty and reindexing", in the form
`BlowUpSequence.pullback` and `BlowUpSequence.eraseEmpty`. Not in the sources beyond that
sentence.

* The run on `Y` is the chain run with skips of the run on `X`
  (`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRunErase.lean`, `step3_chainE`): a centre
  of `X` with no face of `Y` over it is skipped.
* `comap_centerOf_eq_top`, `comap_centerOf_ne_top`: a centre is skipped iff its pull-back is `⊤`
  (its preimage is empty).
* A skip is an empty blow-up of `Y`: the family on `Y` is unchanged while the family on `X`
  becomes `blowUpPieces`; the refinement persists along
  `inv (blowUpπ Y ⊤) ≫ blowUpMap h Z : Y ⟶ Bl_Z X` (`refinesAlongW_skip`; the strict transforms
  pull back to the pieces since `h` misses the centre, the new piece has empty preimage), the
  member transport persists (`totalTransform_component_memberOf_blowUpPieces_skip`), and
  `eraseEmpty_cons_of_eq_top` of `Hironaka/Scheme/BlowUpSequence/EraseEmptyTransport.lean` deletes
  the empty cell of the pulled-back sequence.
* The fold `realizeAux_pullback_eraseEmpty` is `realizeAux_pullback_of_surjective` of
  `Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean` with the skip case added and
  the label-free invariant `RefinesAlongW` (across a skip the family on `X` gains a label the family
  on `Y` does not); `realize_pullback_eraseEmpty` is its form for a smooth `h`.

The result is used for the smooth functoriality of `BMO_{n,m}` in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothStep3.lean`; the helper
`strictTransform_of_eq_top` is used in
`Hironaka/Resolution/Algebraic/Kol07/Thm36/EraseEmptyIndex.lean`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal Scheme
  IdealSheafData Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {X Y : Scheme.{u}} {Φ : PieceFamily X} {h : Y ⟶ X} {ρ : ℕ → ℕ} {Φ' : PieceFamily Y}
  {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel} {E' : DivisorFamily Y}
  {e' : E'.ι ≃o Fin Φ'.nextLabel} {n m : ℕ}

/-! ### Centres missing, or meeting, the image of `h` -/

/-- A centre of `X` with no face of `Y` over it has empty preimage: every point over a face of
the centre lies on a face of `Y` mapping onto it (`RefinesAlongW.exists_image_eq`). -/
theorem comap_centerOf_eq_top (hρ : Φ'.RefinesAlongW h ρ Φ) {S : Finset (Finset ℕ)}
    (hS : S ⊆ Φ.nerve) (hno : (Φ'.nerve.filter fun Q => Q.image ρ ∈ S) = ∅) :
    (Φ.centerOf S).comap h = ⊤ := by
  rw [← support_eq_bot_iff]
  refine eq_bot_iff.mpr fun y hy => ?_
  rw [mem_support_comap_iff'] at hy
  obtain ⟨P, hP, hyP⟩ := (Φ.mem_support_centerOf_iff S _).mp hy
  obtain ⟨Q, hQ, hQP, -⟩ := hρ.exists_image_eq (hS hP) hyP
  exact absurd (Finset.mem_filter.mpr ⟨hQ, hQP ▸ hP⟩) (Finset.eq_empty_iff_forall_notMem.mp hno Q)

/-- A centre of `X` with a face of `Y` over it has nonempty preimage. -/
theorem comap_centerOf_ne_top (hρ : Φ'.RefinesAlongW h ρ Φ) {S : Finset (Finset ℕ)}
    (hne : (Φ'.nerve.filter fun Q => Q.image ρ ∈ S).Nonempty) :
    (Φ.centerOf S).comap h ≠ ⊤ := by
  obtain ⟨Q, hQ⟩ := hne
  obtain ⟨hQn, hQS⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hQr, -, hQb⟩ := Φ'.mem_nerve.mp hQn
  obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hQb
  intro htop
  have hmem : y ∈ ((Φ.centerOf S).comap h).support :=
    (mem_support_comap_iff' _ h y).mpr
      (Φ.faceSet_le_support_centerOf hQS (hρ.mem_faceSet_image hQr hy))
  rw [← support_eq_bot_iff] at htop
  rw [htop, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
  exact hmem

/-! ### Transport across an empty blow-up -/

section Skip

variable (h) [Flat h]

/-- The strict transform under a centre propositionally equal to `⊤` is the pull-back
(`strictTransform_top_left`). -/
theorem strictTransform_of_eq_top {W : Scheme.{u}} {D : W.IdealSheafData} (hD : D = ⊤)
    (J : W.IdealSheafData) : J.strictTransform D = J.comap D.blowUpπ := by
  subst hD
  exact strictTransform_top_left J

/-- Along a skip (`h` misses the centre `Z`, and `Y` maps into `Bl_Z X` through the inverse of
the trivial blow-up of `Y`) the strict transform of `J` pulls back to the pull-back of `J`
(`strictTransform_comap_of_flat` of `Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`). -/
theorem comap_strictTransform_skip {Z : X.IdealSheafData} [IsIso (Z.comap h).blowUpπ]
    (hZ : Z.comap h = ⊤) (J : X.IdealSheafData) :
    (J.strictTransform Z).comap
        (inv (Z.comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h Z) = J.comap h := by
  rw [comap_comp, ← strictTransform_comap_of_flat h Z J,
    strictTransform_of_eq_top hZ, ← comap_comp, IsIso.inv_hom_id, comap_id]

/-- The closed-set form of `comap_strictTransform_skip`. -/
theorem preimage_strictTransformCloseds_skip {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] {Z : X.IdealSheafData}
    [IsIso (Z.comap h).blowUpπ] (hZ : Z.comap h = ⊤) (C : Closeds X) :
    (strictTransformCloseds Z C).preimage
        (inv (Z.comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h Z).continuous =
      C.preimage h.continuous := by
  rw [strictTransformCloseds_eq_support f]
  change ((vanishingIdeal C).strictTransform Z).support.preimage _ = _
  rw [← support_comap, comap_strictTransform_skip h hZ, support_comap,
    Hironaka.Sequence.support_vanishingIdeal_eq]

omit [Flat h] in
/-- The square of a skip: `π_X ∘ (inv π_Y ≫ blowUpMap) = h`. -/
theorem π_skip {Z : X.IdealSheafData} [IsIso (Z.comap h).blowUpπ] (y : Y) :
    IdealSheafData.blowUpπ Z ((inv (Z.comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h Z) y) = h y := by
  have hcomm : (inv (Z.comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h Z) ≫
      IdealSheafData.blowUpπ Z =
      h := by
    rw [Category.assoc, blowUpMap_π, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  exact congrArg (fun g : Y ⟶ X => g y) hcomm

/-- The skip: *across an empty blow-up of `X` the refinement persists*. `Y`'s family is
unchanged, `X`'s becomes `blowUpPieces`; the old pieces' strict transforms pull back to the
pieces (`preimage_strictTransformCloseds_skip`), the new pieces have empty preimage (they lie
over the centre, which `h` misses). -/
theorem refinesAlongW_skip {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (hρ : Φ'.RefinesAlongW h ρ Φ) {S : Finset (Finset ℕ)}
    [IsIso ((Φ.centerOf S).comap h).blowUpπ] (hZ : (Φ.centerOf S).comap h = ⊤) :
    Φ'.RefinesAlongW
      (inv ((Φ.centerOf S).comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S)) ρ
      (Φ.blowUpPieces S m) := by
  classical
  have hmiss : ∀ y : Y, h y ∉ (Φ.centerOf S).support := fun y hy => by
    have hmem : y ∈ ((Φ.centerOf S).comap h).support :=
      (mem_support_comap_iff' _ h y).mpr hy
    rw [hZ, (support_eq_bot_iff _).mpr rfl, ← SetLike.mem_coe, Closeds.coe_bot] at hmem
    exact hmem
  refine ⟨fun c hc => (hρ.lt c hc).trans_le (Nat.le_add_right _ _), fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, hρ.disjoint⟩
  · rw [Φ.blowUpPieces_a_of_lt S (hρ.lt c hc)]
    exact hρ.a_eq c hc
  · rw [Φ.blowUpPieces_piece_of_lt S (hρ.lt c hc), preimage_strictTransformCloseds_skip h f hZ]
    exact hρ.piece_le c hc
  · change c < Φ.nextComp + S.card at hc
    by_cases hlt : c < Φ.nextComp
    · rw [Φ.blowUpPieces_piece_of_lt S hlt, preimage_strictTransformCloseds_skip h f hZ]
      exact hρ.preimage_eq c hlt
    · have hfe : ((Finset.range Φ'.nextComp).filter fun c' => ρ c' = c) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun c' hc' hρc =>
          absurd (hρc ▸ hρ.lt c' (Finset.mem_range.mp hc')) hlt
      rw [hfe, Finset.sup_empty]
      apply Closeds.ext
      rw [Closeds.coe_bot]
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      change
          (inv ((Φ.centerOf S).comap h).blowUpπ ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S))
              y ∈
        (Φ.blowUpPieces S m).piece c at hy
      rw [Φ.mem_blowUpPieces_piece_of_le (not_lt.mp hlt)] at hy
      obtain ⟨P, hP, -, hyP⟩ := hy
      rw [π_skip] at hyP
      exact hmiss y (Φ.faceSet_le_support_centerOf hP hyP)

/-- Across a skip the member transport persists: the member of a child on `Y` is the pull-back of
the strict transform of the member of its parent. -/
theorem totalTransform_component_memberOf_blowUpPieces_skip (hρ : Φ'.RefinesAlongW h ρ Φ)
    (hlab : ∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
      (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h)
    {S : Finset (Finset ℕ)} [IsIso ((Φ.centerOf S).comap h).blowUpπ]
    (hZ : (Φ.centerOf S).comap h = ⊤) (c' : ℕ) (hc' : c' < Φ'.nextComp)
    (hlt : ρ c' < (Φ.blowUpPieces S m).nextComp) :
    E'.component (Φ'.memberOf e' c' hc') =
      ((E.totalTransform (Φ.centerOf S)).component
        ((Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
          (ρ c') hlt)).comap
        (inv ((Φ.centerOf S).comap h).blowUpπ ≫
            Scheme.Hom.blowUpMap h (Φ.centerOf S)) := by
  have hm : (Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
      (ρ c') hlt =
      (toLex (Sum.inl (Φ.memberOf e (ρ c') (hρ.lt c' hc'))) : E.ι ⊕ₗ PUnit.{u + 1}) := by
    refine (extendIso e).injective ?_
    change extendIso e ((extendIso e).symm ⟨(Φ.blowUpPieces S m).label (ρ c'), _⟩) =
      extendIso e (toLex (Sum.inl (Φ.memberOf e (ρ c') (hρ.lt c' hc'))))
    rw [OrderIso.apply_symm_apply, extendIso_inl]
    refine Fin.ext ?_
    change (Φ.blowUpPieces S m).label (ρ c') =
      ((e (Φ.memberOf e (ρ c') (hρ.lt c' hc')) : Fin Φ.nextLabel) : ℕ)
    rw [Φ.blowUpPieces_label_of_lt S (hρ.lt c' hc'), Φ.coe_apply_memberOf]
  rw [hm]
  change E'.component (Φ'.memberOf e' c' hc') =
    ((E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).strictTransform (Φ.centerOf S)).comap _
  rw [comap_strictTransform_skip h hZ, hlab c' hc']

end Skip

/-- Deleting the empty blow-ups commutes with the transport of the base along an equality
(`pullback_eqToHom_comp` of `Hironaka/Scheme/BlowUpSequence/Pullback.lean` under `eraseEmpty`). -/
theorem eraseEmpty_pullback_eqToHom_comp (S : BlowUpSequence X) {Y' : Scheme.{u}} (e : Y' = Y)
    (h : Y ⟶ X) :
    HEq (S.pullback (eqToHom e ≫ h)).eraseEmpty (S.pullback h).eraseEmpty := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

/-! ### The fold -/

section Fold

variable {k k' : Type u} [Field k] [PerfectField k] [Field k'] [PerfectField k']

/-- The second clause of [Kol07, 34.1] along a run: *the chain run with skips on a family of `Y`
refining along a flat `h` realises the pull-back of the realisation with the empty blow-ups
deleted*, by one induction on the run. At a step with a face of `Y` over the centre, the
argument of `realizeAux_pullback_of_surjective` (the centre of `Y` is the pull-back of the centre
of `X`, the transported families refine again, `eraseEmpty_cons_of_ne_top` keeps the cell); at a
skip, the pulled-back centre is `⊤`, `eraseEmpty_cons_of_eq_top` deletes the cell and carries the
tail back along the inverse of the trivial blow-up of `Y`, and the refinement persists along
`inv π_Y ≫ blowUpMap` (`refinesAlongW_skip`). -/
theorem realizeAux_pullback_eraseEmpty (L : List (Finset (Finset ℕ))) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
      (g : Y ⟶ Spec (CommRingCat.of k')) [Smooth g] [QuasiCompact g] (h : Y ⟶ X) [Flat h],
      ∀ (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel},
      E.IsSnc → Φ.Realizes E e → ∀ {n m : ℕ} (hV : Φ.IsValid n m),
      (∃ n' ≤ n, SmoothOfRelativeDimension n' f) → ∀ {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' →
      ∀ (Φ' : PieceFamily Y) {E' : DivisorFamily Y} {e' : E'.ι ≃o Fin Φ'.nextLabel} {ρ : ℕ → ℕ}
      (hρ : Φ'.RefinesAlongW h ρ Φ), E'.IsSnc → Φ'.Realizes E' e' →
      (∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
        (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h) →
      ∀ (hV' : Φ'.IsValid n m), (∃ n' ≤ n, SmoothOfRelativeDimension n' g) →
      MonomialState.IsChainE ρ (Φ'.toState n m hV') (Φ.toState n m hV) L →
      realizeAux Φ' m (MonomialState.chainRunE ρ (Φ'.toState n m hV') (Φ.toState n m hV) L) =
        ((realizeAux Φ m L).pullback h).eraseEmpty := by
  induction L with
  | nil =>
    intro X Y f _ _ g _ _ h _ Φ E e _ _ n m hV _ st' _ Φ' E' e' ρ _ _ _ _ hV' _ _
    rfl
  | cons S L ih =>
    intro X Y f _ _ g _ _ h _ Φ E e hE hΦ n m hV hn st' hrun Φ' E' e' ρ hρ hE' hΦ' hlab hV'
      hn' hchain
    obtain ⟨n₀, hn₀n, hsm₀⟩ := hn
    obtain ⟨n₁, hn₁n, hsm₁⟩ := hn'
    cases hrun with
    | cons r hr hrn hne hL =>
      -- the data at the next stage on `X`
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        (Φ.toState n m hV).isCenter_choice r
      have hE₁ := totalTransform_isSnc f E _ hE
        (Φ.hasSncWith_centerOf hE hΦ hS)
      have hΦ₁ := Φ.realizes_blowUpPieces f hE hΦ hS
      have hV₁ := Φ.valid_blowUpPieces f hE hΦ hS
      have hst₁ := Φ.toState_blowUpPieces f hE hΦ hV₁ hS
      have hrun₁ : MonomialState.IsRun ((Φ.blowUpPieces _ m).toState n m hV₁) L st' := by
        rw [hst₁]
        exact hL
      have hsmZ : Smooth ((Φ.centerOf _).subschemeι ≫ f) := Φ.smooth_centerOf f hE hΦ hS
      have hsm₀' := smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n₀
        (Φ.centerOf ((Φ.toState n m hV).choice r))
      have hsmooth₀ : Smooth ((Φ.centerOf ((Φ.toState n m hV).choice r)).blowUpπ ≫ f) :=
        SmoothOfRelativeDimension.smooth n₀ _
      have hLNX : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      have hproperX := blowUp.isProper_π (Φ.centerOf ((Φ.toState n m hV).choice r))
      have hflat₁ :
          Flat (Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))) :=
        flat_blowUpMap h _
      cases hchain with
      | skip _ hno hnext =>
        -- an empty blow-up of `Y`
        have hZ : (Φ.centerOf ((Φ.toState n m hV).choice r)).comap h = ⊤ :=
          comap_centerOf_eq_top hρ hS.1 hno
        have hiso := isIso_blowUpπ_of_eq_top hZ
        have hρ₁ := refinesAlongW_skip (m := m) h f hρ hZ
        have hchain₁ : MonomialState.IsChainE ρ (Φ'.toState n m hV')
            ((Φ.blowUpPieces _ m).toState n m hV₁) L := by
          rw [hst₁]
          exact hnext
        have hIH := ih ((Φ.centerOf _).blowUpπ ≫ f) g
          (inv ((Φ.centerOf ((Φ.toState n m hV).choice r)).comap h).blowUpπ ≫
            Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r)))
          (Φ.blowUpPieces _ m) hE₁ hΦ₁ hV₁ ⟨n₀, hn₀n, hsm₀'⟩ hrun₁ Φ' hρ₁ hE' hΦ'
          (fun c' hc' => totalTransform_component_memberOf_blowUpPieces_skip h hρ hlab hZ c' hc' _)
          hV' ⟨n₁, hn₁n, hsm₁⟩ hchain₁
        rw [MonomialState.chainRunE_cons_of_eq_empty _ _ _ _ hno, ← hst₁, hIH]
        change _ = (BlowUpSequence.cons Y ((Φ.centerOf _).comap h)
          ((realizeAux (Φ.blowUpPieces _ m) m L).pullback
            (Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))))).eraseEmpty
        rw [eraseEmpty_cons_of_eq_top _ hZ,
          ← eraseEmpty_pullback_of_flat_surjective _ _
            (surjective_of_isIso _),
          ← pullback_comp]
      | step _ hne' hY hnext =>
        -- a blow-up of `Y` along the faces over the center of `X`
        set S' : Finset (Finset ℕ) :=
          (Φ'.toState n m hV').nerve.filter fun Q => Q.image ρ ∈ (Φ.toState n m hV).choice r
          with hS'def
        have hS'S : ∀ Q ∈ S', Q.image ρ ∈ (Φ.toState n m hV).choice r := fun Q hQ =>
          (Finset.mem_filter.mp hQ).2
        have hlift : ∀ P ∈ (Φ.toState n m hV).choice r, ∀ y : Y, h y ∈ Φ.faceSet P →
            ∃ Q ∈ S', y ∈ Φ'.faceSet Q := by
          intro P hP y hy
          obtain ⟨Q, hQ, hQP, hyQ⟩ := hρ.exists_image_eq (hS.1 hP) hy
          exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, hQP ▸ hP⟩, hyQ⟩
        have hc := centerOf_eq_comap hE hΦ hE' hρ hΦ' hlab hS hY hS'S hlift
        have hZ : (Φ.centerOf ((Φ.toState n m hV).choice r)).comap h ≠ ⊤ :=
          comap_centerOf_ne_top hρ hne'
        -- the data at the next stage on `Y`
        have hE'₁ := totalTransform_isSnc g E' _ hE'
          (Φ'.hasSncWith_centerOf hE' hΦ' hY)
        have hΦ'₁ := Φ'.realizes_blowUpPieces g hE' hΦ' hY
        have hV'₁ := Φ'.valid_blowUpPieces g hE' hΦ' hY
        have hst'₁ := Φ'.toState_blowUpPieces g hE' hΦ' hV'₁ hY
        have hsmZ' : Smooth ((Φ'.centerOf S').subschemeι ≫ g) := Φ'.smooth_centerOf g hE' hΦ' hY
        have hsm₁' := smoothOfRelativeDimension_blowUpπ_comp_of_smooth g n₁
          (Φ'.centerOf S')
        have hsmooth₁ : Smooth ((Φ'.centerOf S').blowUpπ ≫ g) :=
          SmoothOfRelativeDimension.smooth n₁ _
        have hLNY : IsLocallyNoetherian Y := g.isLocallyNoetherian_of_field
        have hproperY := blowUp.isProper_π (Φ'.centerOf S')
        have hρ₁ := blowUpPieces_refinesAlongW f g hρ hS hY hS'S hlift hc
        have hchain₁ : MonomialState.IsChainE
            (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S'
              ((Φ.toState n m hV).choice r))
            ((Φ'.blowUpPieces S' m).toState n m hV'₁) ((Φ.blowUpPieces _ m).toState n m hV₁) L := by
          rw [hst'₁, hst₁]
          exact hnext
        have hIH := ih ((Φ.centerOf _).blowUpπ ≫ f) ((Φ'.centerOf S').blowUpπ ≫ g)
          (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
            Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r)))
          (Φ.blowUpPieces _ m) hE₁ hΦ₁ hV₁ ⟨n₀, hn₀n, hsm₀'⟩ hrun₁ (Φ'.blowUpPieces S' m) hρ₁
          hE'₁ hΦ'₁
          (fun c'' hc'' => totalTransform_component_memberOf_blowUpPieces hρ hlab hc hc'' _)
          hV'₁ ⟨n₁, hn₁n, hsm₁'⟩ hchain₁
        -- assemble
        rw [MonomialState.chainRunE_cons_of_ne_empty _ _ _ _
          (Finset.nonempty_iff_ne_empty.mp hne')]
        change BlowUpSequence.cons Y (Φ'.centerOf S')
          (realizeAux (Φ'.blowUpPieces S' m) m
            (MonomialState.chainRunE
              (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S'
                ((Φ.toState n m hV).choice r))
              ((Φ'.toState n m hV').blowUp S') ((Φ.toState n m hV).blowUp _) L)) =
          (BlowUpSequence.cons Y ((Φ.centerOf _).comap h)
            ((realizeAux (Φ.blowUpPieces _ m) m L).pullback
              (Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))))).eraseEmpty
        rw [eraseEmpty_cons_of_ne_top _ hZ, ← hst'₁, ← hst₁]
        refine cons_congr hc ?_
        rw [hIH]
        exact eraseEmpty_pullback_eqToHom_comp _ (congrArg Scheme.IdealSheafData.blowUp hc) _

end Fold

/-! ### The statement for a smooth morphism -/

section

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  [QuasiCompact f] [Smooth h] [QuasiCompact (h ≫ f)]

include f in
/-- The second clause of [Kol07, 34.1] for the geometric Step 3: for a smooth `h`, *the geometric
Step 3 on `Y` is the pull-back of the geometric Step 3 on `X` with the empty blow-ups deleted*.
The run on `Y` is the chain run with skips of the run on `X` (`step3_chainE` on
`refines_toState`, `sub_restrictState` and `Rel.refl`, combining `step3_restrict` and
`step3_refine` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/`) and the chain run realises the
deleted pull-back (`realizeAux_pullback_eraseEmpty` with `Y`'s structure morphism `h ≫ f`). -/
theorem realize_pullback_eraseEmpty (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' (h ≫ f)) (hρ : Φ'.RefinesAlong h ρ Φ)
    (hΦ' : Φ'.Realizes (E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)))
    (hV' : Φ'.IsValid n m) :
    Φ'.realize n m hV' = ((Φ.realize n m hV).pullback h).eraseEmpty := by
  have hE' : (E.comap h).IsSnc := isSnc_comap_of_smooth f h hE
  have hR := refines_toState hρ hV hV'
  have hsub := Φ.sub_restrictState h hV
  obtain ⟨hchain, hrun⟩ :=
    MonomialState.step3_chainE hR (MonomialState.Rel.refl _) hsub (fun _ _ => rfl)
  have hlab := component_comap_memberOf (e := e) hρ
  change realizeAux Φ' m (MonomialState.step3 (Φ'.toState n m hV')).2 =
    ((realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).pullback h).eraseEmpty
  rw [hrun]
  exact realizeAux_pullback_eraseEmpty _ f (h ≫ f) h Φ hE hΦ hV hn
    (MonomialState.step3_isRun _) Φ' hρ.toW hE' hΦ' hlab hV' hn' hchain

end

end Hironaka.Monomial.PieceFamily
