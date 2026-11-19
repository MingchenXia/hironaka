/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Refinement
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.ChainRun
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Local
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Kernel
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Refine
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.TotalTransformOnCentre
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The pull-back of the realised Step 3 along a smooth surjection

For a smooth `h : Y ⟶ X` and a piece family `Φ'` of `Y` refining `Φ` along `h`
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean`), the geometric Step 3 on `Y` is
the pull-back of the geometric Step 3 on `X`: the first clause of [Kol07, 34.1], "`B` commutes with
every smooth surjection", for the third step of `BMO_{n,m}`. The centres of the two runs correspond
step by step, Kollár's choice on `Y` being the `ρ`-preimage of the choice on `X`
(`Refines.choice_eq` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Refine.lean`), and

* `centerOf_eq_comap`: *the centre of the preimage faces is the pull-back of the centre*. At a
  point `y` over `x ∈ Z_P` the unique face of `Y`'s centre through `y` maps onto `P`, and a
  child's reduced stalk is the pulled-back parent's (`stalkIdeal_vanishingIdeal_piece` on both
  sides). This is the statement of [Kol07, 30.1] that the centres of a pulled-back blow-up
  sequence are the preimages of the centres, here for the centres of Step 3;

so that the two blow-ups are the same blow-up of `Y`, and the transported families refine again
along the induced morphism of blow-ups (`blowUpPieces_refinesAlong`, the geometric counterpart
of `Refines.blowUp`). The fold `realizeAux_pullback_of_surjective` is then one induction along
the run on `X`, and `realize_pullback_of_surjective` is the statement for `realize`. Not in the
sources beyond Kollár's one sentence. The general case, `h` not surjective, is
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackErase.lean`; the result is used in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Functorial.lean` and, through
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothStep3.lean`, in the smooth functoriality
of `BMO_{n,m}`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal
  Scheme.IdealSheafData Scheme IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {X Y : Scheme.{u}} {Φ : PieceFamily X} {h : Y ⟶ X} {ρ : ℕ → ℕ} {Φ' : PieceFamily Y}
  {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel} {E' : DivisorFamily Y}
  {e' : E'.ι ≃o Fin Φ'.nextLabel}

/-! ### Members of children and parents -/

/-- The member of a child is the pull-back of the member of its parent, and so its `E'`-component
(`E' = E.comap h`) is the pull-back of the parent's `E`-component: the label-matching hypothesis of
the general fold in the pulled-back case. -/
theorem component_comap_memberOf (hρ : Φ'.RefinesAlong h ρ Φ) (c' : ℕ)
    (hc' : c' < Φ'.nextComp) :
    (E.comap h).component (Φ'.memberOf (E := E.comap h)
        (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) c' hc') =
      (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h := by
  have hm : Φ'.memberOf (E := E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) c' hc' =
      Φ.memberOf e (ρ c') (hρ.lt c' hc') := by
    apply (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)).injective
    apply Fin.ext
    refine (Φ'.coe_apply_memberOf (E := E.comap h)
      (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) c' hc').trans ?_
    change Φ'.label c' = ((e (Φ.memberOf e (ρ c') (hρ.lt c' hc')) : Fin Φ.nextLabel) : ℕ)
    rw [Φ.coe_apply_memberOf, hρ.label_eq c' hc']
  exact congrArg (fun j => (E.comap h).component j) hm

/-- The reduced stalk of a child at a point is the pull-back of the reduced stalk of its parent. -/
theorem stalkIdeal_vanishingIdeal_piece_comap (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    (hE' : E'.IsSnc) (hρ : Φ'.RefinesAlongW h ρ Φ) (hΦ' : Φ'.Realizes E' e')
    (hlab : ∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
      (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h) {c' : ℕ}
    (hc' : c' < Φ'.nextComp) {y : Y} (hy : y ∈ Φ'.piece c') :
    (vanishingIdeal (Φ'.piece c')).stalkIdeal y =
      ((vanishingIdeal (Φ.piece (ρ c'))).stalkIdeal (h y)).map (h.stalkMap y).hom := by
  rw [Φ'.stalkIdeal_vanishingIdeal_piece hE' hΦ' hc' hy, hlab c' hc', stalkIdeal_comap,
    Φ.stalkIdeal_vanishingIdeal_piece hE hΦ (hρ.lt c' hc') (hρ.mem_piece_of_mem hc' hy)]

/-! ### The center of the preimage faces is the pull-back of the center -/

variable {n m : ℕ}

/-- *The centre of the faces of `Y` mapping into a centre `S` of `X` is the pull-back of the centre
of `S`*, provided every point over a face of `S` lies on a face of the `Y`-centre ([Kol07, 30.1]:
the centres of the pull-back are the inverse images of the centres). At a point `y` over
`x ∈ Z_P` the unique face of the `Y`-centre through `y` maps onto `P` (the faces of a centre are
pairwise disjoint), the two centres have the stalks of the ideals of these faces, and a child's
reduced stalk is the pulled-back parent's. -/
theorem centerOf_eq_comap (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hE' : E'.IsSnc)
    (hρ : Φ'.RefinesAlongW h ρ Φ) (hΦ' : Φ'.Realizes E' e')
    (hlab : ∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
      (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h)
    {hV : Φ.IsValid n m} {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S)
    {hV' : Φ'.IsValid n m} {S' : Finset (Finset ℕ)} (hS' : (Φ'.toState n m hV').IsCenter S')
    (hS'S : ∀ Q ∈ S', Q.image ρ ∈ S)
    (hlift : ∀ P ∈ S, ∀ y : Y, h y ∈ Φ.faceSet P → ∃ Q ∈ S', y ∈ Φ'.faceSet Q) :
    Φ'.centerOf S' = (Φ.centerOf S).comap h := by
  classical
  refine ext_stalkIdeal fun y => ?_
  rw [stalkIdeal_comap]
  by_cases hx : h y ∈ (Φ.centerOf S).support
  · obtain ⟨P, hP, hxP⟩ := (Φ.mem_support_centerOf_iff S _).mp hx
    obtain ⟨Q, hQ, hyQ⟩ := hlift P hP y hxP
    have hQr : Q ⊆ Finset.range Φ'.nextComp := (Φ'.mem_nerve.mp (hS'.1 hQ)).1
    -- the face of `Y`'s center through `y` maps onto `P`
    have hQP : Q.image ρ = P :=
      Φ.eq_of_mem_faceSet_of_isCenter hS (hS'S Q hQ) hP (hρ.mem_faceSet_image hQr hyQ) hxP
    rw [Φ'.stalkIdeal_centerOf_eq_faceIdeal hS' hQ hyQ,
      Φ.stalkIdeal_centerOf_eq_faceIdeal hS hP hxP, ← hQP]
    unfold faceIdeal
    rw [Hironaka.Sequence.stalkIdeal_biSup_finset, Hironaka.Sequence.stalkIdeal_biSup_finset,
      Finset.iSup_finset_image]
    simp only [Ideal.map_iSup]
    refine iSup_congr fun c' => iSup_congr fun hc' => ?_
    exact stalkIdeal_vanishingIdeal_piece_comap hE hΦ hE' hρ hΦ' hlab
      (Finset.mem_range.mp (hQr hc'))
      (Φ'.mem_faceSet.mp hyQ c' hc')
  · -- off the center: no face of `Y`'s center passes through `y`
    have hy : y ∉ (Φ'.centerOf S').support := fun hy => by
      obtain ⟨Q, hQ, hyQ⟩ := (Φ'.mem_support_centerOf_iff S' y).mp hy
      have hQr : Q ⊆ Finset.range Φ'.nextComp := (Φ'.mem_nerve.mp (hS'.1 hQ)).1
      exact hx (Φ.faceSet_le_support_centerOf (hS'S Q hQ) (hρ.mem_faceSet_image hQr hyQ))
    rw [stalkIdeal_eq_top_of_notMem_support _ hy, stalkIdeal_eq_top_of_notMem_support _ hx,
      Ideal.map_top]

/-! ### The transported families refine again -/

/-- The exponent sum of a face is preserved by the parent map. -/
theorem RefinesAlongW.total_image (hρ : Φ'.RefinesAlongW h ρ Φ) {Q : Finset ℕ}
    (hQ : Q ∈ Φ'.nerve) :
    Φ.total (Q.image ρ) = Φ'.total Q := by
  classical
  obtain ⟨hQr, -, hQb⟩ := Φ'.mem_nerve.mp hQ
  obtain ⟨y, hy⟩ := Closeds.coe_nonempty.mpr hQb
  rw [total, total, Finset.sum_image (hρ.injOn_of_mem_faceSet hQr hy)]
  exact Finset.sum_congr rfl fun c' hc' => hρ.a_eq c' (Finset.mem_range.mp (hQr hc'))

/-- Transport of a strict transform along an equality of centers. -/
theorem strictTransform_comap_eqToHom {D D' : Y.IdealSheafData} (e : D' = D)
    (J : Y.IdealSheafData) :
    (J.strictTransform D).comap (eqToHom (congrArg Scheme.IdealSheafData.blowUp e)) =
        J.strictTransform D' := by
  subst e
  simp

section Step

variable {k k' : Type u} [Field k] [Field k'] (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] (g : Y ⟶ Spec (CommRingCat.of k')) [LocallyOfFiniteType g] [Flat h]

/-- Transport of the exceptional divisor along an equality of centers. -/
theorem exceptionalDivisor_comap_eqToHom {D D' : Y.IdealSheafData} (e : D' = D) :
    D.exceptionalDivisor.comap (eqToHom (congrArg Scheme.IdealSheafData.blowUp e)) =
        D'.exceptionalDivisor := by
  subst e
  simp

include f g in
/-- *The transported families refine again*, the geometric counterpart of `Refines.blowUp`: after
blowing up the centre `S` on `X` and the centre `S'` of the faces mapping into `S` on `Y` (the
same blow-up of `Y`, `centerOf_eq_comap`), the transported family of `Y` refines the transported
family of `X` along the induced morphism of blow-ups, with `extendComp` as the parent map. Old
children go to old parents (the strict transform of a child lies in the pull-back of the strict
transform of the parent, and the pull-back of a strict transform along a flat morphism is the
strict transform of the pull-back, `strictTransform_comap_of_flat` of
`Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`); the new piece `F_Q = π⁻¹(Z_Q)` of a face `Q`
goes to the new piece `F_{ρ(Q)}`, whose pull-back is the union of the `F_Q` over `Q` mapping onto
the same face. -/
theorem blowUpPieces_refinesAlongW (hρ : Φ'.RefinesAlongW h ρ Φ) {hV : Φ.IsValid n m}
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {hV' : Φ'.IsValid n m}
    {S' : Finset (Finset ℕ)} (hS' : (Φ'.toState n m hV').IsCenter S')
    (hS'S : ∀ Q ∈ S', Q.image ρ ∈ S)
    (hlift : ∀ P ∈ S, ∀ y : Y, h y ∈ Φ.faceSet P → ∃ Q ∈ S', y ∈ Φ'.faceSet Q)
    (hc : Φ'.centerOf S' = (Φ.centerOf S).comap h) :
    (Φ'.blowUpPieces S' m).RefinesAlongW
      (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S))
      (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S)
      (Φ.blowUpPieces S m) := by
  classical
  have hLNX : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hLNY : IsLocallyNoetherian Y := g.isLocallyNoetherian_of_field
  -- the commutative square `π_X ∘ h₁ = h ∘ π_Y`
  have hsq : ∀ y' : (Φ'.centerOf S').blowUp,
      IdealSheafData.blowUpπ (Φ.centerOf S)
        ((eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
            (Φ.centerOf S)) y') =
        h (IdealSheafData.blowUpπ (Φ'.centerOf S') y') := by
    intro y'
    have hcomm : (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
        (Φ.centerOf S)) ≫
        IdealSheafData.blowUpπ (Φ.centerOf S) = IdealSheafData.blowUpπ (Φ'.centerOf S') ≫ h := by
      rw [Category.assoc]
      rw [blowUpMap_π]
      rw [← Category.assoc, eqToHom_comp_blowUpπ hc]
    have := congrArg (fun g : (Φ'.centerOf S').blowUp ⟶ X => g y') hcomm
    exact this
  -- the support of the center of `Y` is the preimage of the support of the center of `X`
  have hsupp : ∀ y : Y, y ∈ (Φ'.centerOf S').support ↔ h y ∈ (Φ.centerOf S).support := by
    intro y
    rw [hc]
    exact mem_support_comap_iff' _ h y
  -- the parent map on the new components
  have hext_lt : ∀ c', c' < Φ'.nextComp →
      MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c' = ρ c' :=
    fun c' hc' => MonomialState.extendComp_of_lt ρ _ _ S' S hc'
  have hext_new : ∀ Q ∈ S',
      MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S (Φ'.newComp S' Q) =
        Φ.newComp S (Q.image ρ) :=
    fun Q hQ => MonomialState.extendComp_newComp ρ _ _ S' S hQ
  have hnew : ∀ c', Φ'.nextComp ≤ c' → c' < Φ'.nextComp + S'.card →
      ∃ Q ∈ S', Φ'.newComp S' Q = c' :=
    fun c' h1 h2 => MonomialState.exists_newComp_eq (Φ'.toState n m hV') S' h1 h2
  have hnewX : ∀ c, Φ.nextComp ≤ c → c < Φ.nextComp + S.card → ∃ P ∈ S, Φ.newComp S P = c :=
    fun c h1 h2 => MonomialState.exists_newComp_eq (Φ.toState n m hV) S h1 h2
  have hQr : ∀ Q ∈ S', Q ⊆ Finset.range Φ'.nextComp := fun Q hQ => (Φ'.mem_nerve.mp (hS'.1 hQ)).1
  -- the preimage of a face of the center of `X` is the union of the faces of `Y` over it
  have hface : ∀ P ∈ S, ∀ y : Y,
      h y ∈ Φ.faceSet P ↔ ∃ Q ∈ S', Q.image ρ = P ∧ y ∈ Φ'.faceSet Q := by
    intro P hP y
    constructor
    · intro hy
      obtain ⟨Q, hQ, hyQ⟩ := hlift P hP y hy
      exact ⟨Q, hQ, Φ.eq_of_mem_faceSet_of_isCenter hS (hS'S Q hQ) hP
        (hρ.mem_faceSet_image (hQr Q hQ) hyQ) hy, hyQ⟩
    · rintro ⟨Q, hQ, rfl, hyQ⟩
      exact hρ.mem_faceSet_image (hQr Q hQ) hyQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `lt`
    intro c' hc'
    change c' < Φ'.nextComp + S'.card at hc'
    change _ < Φ.nextComp + S.card
    by_cases hlt : c' < Φ'.nextComp
    · rw [hext_lt c' hlt]
      exact (hρ.lt c' hlt).trans_le (Nat.le_add_right _ _)
    · obtain ⟨Q, hQ, rfl⟩ := hnew c' (not_lt.mp hlt) hc'
      rw [hext_new Q hQ]
      exact (Φ.toState n m hV).newComp_lt (hS'S Q hQ)
  · -- exponents
    intro c' hc'
    change c' < Φ'.nextComp + S'.card at hc'
    by_cases hlt : c' < Φ'.nextComp
    · rw [hext_lt c' hlt, Φ.blowUpPieces_a_of_lt S (hρ.lt c' hlt), Φ'.blowUpPieces_a_of_lt S' hlt]
      exact hρ.a_eq c' hlt
    · obtain ⟨Q, hQ, rfl⟩ := hnew c' (not_lt.mp hlt) hc'
      rw [hext_new Q hQ, Φ.blowUpPieces_a_newComp S (hS'S Q hQ), Φ'.blowUpPieces_a_newComp S' hQ,
        hρ.total_image (hS'.1 hQ)]
  · -- a child lies over its parent
    intro c' hc'
    change c' < Φ'.nextComp + S'.card at hc'
    by_cases hlt : c' < Φ'.nextComp
    · rw [hext_lt c' hlt, Φ'.blowUpPieces_piece_of_lt S' hlt,
        Φ.blowUpPieces_piece_of_lt S (hρ.lt c' hlt)]
      intro y' hy'
      change y' ∈ closure ((IdealSheafData.blowUpπ (Φ'.centerOf S')) ⁻¹'
        ((Φ'.piece c' : Set Y) \ ((Φ'.centerOf S').support : Set Y))) at hy'
      change (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
          (Φ.centerOf S)) y' ∈
        closure ((IdealSheafData.blowUpπ (Φ.centerOf S)) ⁻¹'
          ((Φ.piece (ρ c') : Set X) \ ((Φ.centerOf S).support : Set X)))
      have hsub : (IdealSheafData.blowUpπ (Φ'.centerOf S')) ⁻¹'
          ((Φ'.piece c' : Set Y) \ ((Φ'.centerOf S').support : Set Y)) ⊆
          (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
              (Φ.centerOf S)) ⁻¹'
            ((IdealSheafData.blowUpπ (Φ.centerOf S)) ⁻¹'
              ((Φ.piece (ρ c') : Set X) \ ((Φ.centerOf S).support : Set X))) := by
        intro y'' hy''
        obtain ⟨h1, h2⟩ := hy''
        refine ⟨?_, ?_⟩
        · change IdealSheafData.blowUpπ (Φ.centerOf S)
            ((eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
                (Φ.centerOf S)) y'')
                ∈
              Φ.piece (ρ c')
          rw [hsq]
          exact hρ.mem_piece_of_mem hlt h1
        · change IdealSheafData.blowUpπ (Φ.centerOf S)
            ((eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
                (Φ.centerOf S)) y'')
                ∉
              (Φ.centerOf S).support
          rw [hsq]
          exact fun hmem => h2 ((hsupp _).mpr hmem)
      exact (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
        Scheme.Hom.blowUpMap h (Φ.centerOf S)).continuous.closure_preimage_subset _
          (closure_mono hsub hy')
    · obtain ⟨Q, hQ, rfl⟩ := hnew c' (not_lt.mp hlt) hc'
      rw [hext_new Q hQ, Φ'.blowUpPieces_piece_newComp S' hQ,
        Φ.blowUpPieces_piece_newComp S (hS'S Q hQ)]
      intro y' hy'
      change IdealSheafData.blowUpπ (Φ.centerOf S)
        ((eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
            (Φ.centerOf S)) y') ∈
          Φ.faceSet (Q.image ρ)
      rw [hsq]
      exact hρ.mem_faceSet_image (hQr Q hQ) hy'
  · -- the pull-back of a piece is the union of its children
    intro c hcN
    change c < Φ.nextComp + S.card at hcN
    by_cases hlt : c < Φ.nextComp
    · -- an old piece: strict transforms
      rw [Φ.blowUpPieces_piece_of_lt S hlt]
      -- the children are the old children of `c`
      have hfilter : ((Finset.range (Φ'.blowUpPieces S' m).nextComp).filter fun c' =>
          MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c' = c) =
          (Finset.range Φ'.nextComp).filter fun c' => ρ c' = c := by
        ext c'
        simp only [Finset.mem_filter, Finset.mem_range, Φ'.blowUpPieces_nextComp]
        constructor
        · rintro ⟨hc', hρc⟩
          by_cases hlt' : c' < Φ'.nextComp
          · exact ⟨hlt', by rwa [hext_lt c' hlt'] at hρc⟩
          · exfalso
            obtain ⟨Q, hQ, rfl⟩ := hnew c' (not_lt.mp hlt') hc'
            rw [hext_new Q hQ] at hρc
            exact absurd (hρc ▸ Nat.le_add_right Φ.nextComp _ : Φ.nextComp ≤ c) (not_le.mpr hlt)
        · rintro ⟨hc', hρc⟩
          exact ⟨hc'.trans_le (Nat.le_add_right _ _), by rw [hext_lt c' hc']; exact hρc⟩
      rw [hfilter]
      -- the pull-back of the strict transform is the strict transform of the pull-back
      have hst : (strictTransformCloseds (Φ.centerOf S) (Φ.piece c)).preimage
          (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
              Scheme.Hom.blowUpMap h (Φ.centerOf S)).continuous =
          (((vanishingIdeal (Φ.piece c)).comap h).strictTransform (Φ'.centerOf S')).support := by
        rw [strictTransformCloseds_eq_support f]
        change (((vanishingIdeal (Φ.piece c)).strictTransform (Φ.centerOf S)).support.preimage
          (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
              Scheme.Hom.blowUpMap h (Φ.centerOf S)).continuous) = _
        rw [← Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.comap_comp,
          ← strictTransform_comap_of_flat h (Φ.centerOf S),
          strictTransform_comap_eqToHom hc]
      rw [hst]
      apply Closeds.ext
      rw [Hironaka.Sequence.coe_support_strictTransform, Scheme.IdealSheafData.support_comap,
        Hironaka.Sequence.support_vanishingIdeal_eq, hρ.preimage_eq c hlt, Closeds.coe_finset_sup,
        Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_eq_iSup]
      simp only [Set.iSup_eq_iUnion, Function.comp_apply, Set.preimage_iUnion, Set.iUnion_sdiff]
      rw [Finset.closure_biUnion]
      refine Set.iUnion₂_congr fun c' hc' => ?_
      rw [Φ'.blowUpPieces_piece_of_lt S' (Finset.mem_range.mp (Finset.mem_filter.mp hc').1)]
      change _ = closure ((IdealSheafData.blowUpπ (Φ'.centerOf S')) ⁻¹' ((Φ'.piece c' : Set Y) \
        ((Φ'.centerOf S').support : Set Y)))
      rw [Set.preimage_sdiff]
    · -- a new piece `F_P`: the union of the `F_Q`, `Q` over `P`
      obtain ⟨P, hP, rfl⟩ := hnewX c (not_lt.mp hlt) hcN
      rw [Φ.blowUpPieces_piece_newComp S hP]
      apply Closeds.ext
      ext y'
      rw [SetLike.mem_coe, SetLike.mem_coe, mem_finset_sup_iff]
      change IdealSheafData.blowUpπ (Φ.centerOf S)
        ((eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h
            (Φ.centerOf S)) y') ∈
          Φ.faceSet P ↔ _
      rw [hsq, hface P hP]
      constructor
      · rintro ⟨Q, hQ, hQP, hyQ⟩
        refine ⟨Φ'.newComp S' Q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          ((Φ'.toState n m hV').newComp_lt hQ), ?_⟩, ?_⟩
        · rw [hext_new Q hQ, hQP]
        · rw [Φ'.blowUpPieces_piece_newComp S' hQ]
          exact hyQ
      · rintro ⟨c', hc', hy'⟩
        obtain ⟨hc'r, hρc⟩ := Finset.mem_filter.mp hc'
        have hc'k : c' < Φ'.nextComp + S'.card := Finset.mem_range.mp hc'r
        by_cases hlt' : c' < Φ'.nextComp
        · exfalso
          rw [hext_lt c' hlt'] at hρc
          exact absurd (hρc ▸ hρ.lt c' hlt') (not_lt.mpr (Nat.le_add_right _ _))
        · obtain ⟨Q, hQ, rfl⟩ := hnew c' (not_lt.mp hlt') hc'k
          rw [hext_new Q hQ] at hρc
          rw [Φ'.blowUpPieces_piece_newComp S' hQ] at hy'
          exact ⟨Q, hQ, (Φ.toState n m hV).newComp_injOn S (hS'S Q hQ) hP hρc, hy'⟩
  · -- children of one parent are disjoint
    intro c₁ c₂ hc₁ hc₂ hne hρeq
    change c₁ < Φ'.nextComp + S'.card at hc₁
    change c₂ < Φ'.nextComp + S'.card at hc₂
    rw [disjoint_iff_inf_le]
    intro y' hy'
    rw [← SetLike.mem_coe, Closeds.coe_inf] at hy'
    obtain ⟨h1, h2⟩ := hy'
    exfalso
    by_cases hlt₁ : c₁ < Φ'.nextComp
    · by_cases hlt₂ : c₂ < Φ'.nextComp
      · -- two old children: their images lie on two disjoint children
        rw [hext_lt c₁ hlt₁, hext_lt c₂ hlt₂] at hρeq
        have hd := hρ.disjoint c₁ c₂ hlt₁ hlt₂ hne hρeq
        have hmem : IdealSheafData.blowUpπ (Φ'.centerOf S') y' ∈ Φ'.piece c₁ ⊓ Φ'.piece c₂ := by
          rw [← SetLike.mem_coe, Closeds.coe_inf]
          exact ⟨Φ'.π_mem_piece_of_mem_blowUpPieces_piece g hlt₁ h1,
            Φ'.π_mem_piece_of_mem_blowUpPieces_piece g hlt₂ h2⟩
        have h0 : IdealSheafData.blowUpπ (Φ'.centerOf S') y' ∈ (⊥ : Closeds Y) :=
            (disjoint_iff_inf_le.mp hd) hmem
        rw [← SetLike.mem_coe, Closeds.coe_bot] at h0
        exact h0
      · -- an old and a new child have parents of different kinds
        obtain ⟨Q, hQ, rfl⟩ := hnew c₂ (not_lt.mp hlt₂) hc₂
        rw [hext_lt c₁ hlt₁, hext_new Q hQ] at hρeq
        exact absurd (hρeq ▸ hρ.lt c₁ hlt₁) (not_lt.mpr (Nat.le_add_right _ _))
    · by_cases hlt₂ : c₂ < Φ'.nextComp
      · obtain ⟨Q, hQ, rfl⟩ := hnew c₁ (not_lt.mp hlt₁) hc₁
        rw [hext_new Q hQ, hext_lt c₂ hlt₂] at hρeq
        exact absurd (hρeq ▸ hρ.lt c₂ hlt₂) (not_lt.mpr (Nat.le_add_right _ _))
      · -- two new children over one face: the faces pass through a common point
        obtain ⟨Q₁, hQ₁, rfl⟩ := hnew c₁ (not_lt.mp hlt₁) hc₁
        obtain ⟨Q₂, hQ₂, rfl⟩ := hnew c₂ (not_lt.mp hlt₂) hc₂
        rw [hext_new Q₁ hQ₁, hext_new Q₂ hQ₂] at hρeq
        rw [Φ'.blowUpPieces_piece_newComp S' hQ₁] at h1
        rw [Φ'.blowUpPieces_piece_newComp S' hQ₂] at h2
        exact hne (congrArg (Φ'.newComp S') (Φ'.eq_of_mem_faceSet_of_isCenter hS' hQ₁ hQ₂ h1 h2))

include f g in
/-- The transported families refine again, with the labels: `blowUpPieces_refinesAlongW` and the
two label clauses (both families gain exactly one label). -/
theorem blowUpPieces_refinesAlong (hρ : Φ'.RefinesAlong h ρ Φ) {hV : Φ.IsValid n m}
    {S : Finset (Finset ℕ)} (hS : (Φ.toState n m hV).IsCenter S) {hV' : Φ'.IsValid n m}
    {S' : Finset (Finset ℕ)} (hS' : (Φ'.toState n m hV').IsCenter S')
    (hS'S : ∀ Q ∈ S', Q.image ρ ∈ S)
    (hlift : ∀ P ∈ S, ∀ y : Y, h y ∈ Φ.faceSet P → ∃ Q ∈ S', y ∈ Φ'.faceSet Q)
    (hc : Φ'.centerOf S' = (Φ.centerOf S).comap h) :
    (Φ'.blowUpPieces S' m).RefinesAlong
      (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S))
      (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S)
      (Φ.blowUpPieces S m) := by
  have hW := blowUpPieces_refinesAlongW f g hρ.toW hS hS' hS'S hlift hc
  refine ⟨?_, hW.lt, ?_, hW.a_eq, hW.piece_le, hW.preimage_eq, hW.disjoint⟩
  · change Φ'.nextLabel + 1 = Φ.nextLabel + 1
    rw [hρ.nextLabel_eq]
  · intro c' hc'
    change c' < Φ'.nextComp + S'.card at hc'
    by_cases hlt : c' < Φ'.nextComp
    · rw [MonomialState.extendComp_of_lt ρ _ _ S' S hlt,
        Φ.blowUpPieces_label_of_lt S (hρ.lt c' hlt), Φ'.blowUpPieces_label_of_lt S' hlt]
      exact hρ.label_eq c' hlt
    · obtain ⟨Q, hQ, rfl⟩ : ∃ Q ∈ S', Φ'.newComp S' Q = c' :=
        MonomialState.exists_newComp_eq (Φ'.toState n m hV') S' (not_lt.mp hlt) hc'
      have hext : MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S
          (Φ'.newComp S' Q) = Φ.newComp S (Q.image ρ) :=
        MonomialState.extendComp_newComp ρ _ _ S' S hQ
      rw [hext, Φ.blowUpPieces_label_newComp S, Φ'.blowUpPieces_label_newComp S']
      exact hρ.nextLabel_eq.symm

/-- The member of a transported child is the pull-back of the member of its transported parent:
an old child's member is the strict transform of its member (`strictTransform_comap_of_flat`), a
new child's member is the exceptional divisor (`exceptionalDivisor_comap`). -/
theorem totalTransform_component_memberOf_blowUpPieces (hρ : Φ'.RefinesAlongW h ρ Φ)
    (hlab : ∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
      (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h)
    {hV : Φ.IsValid n m} {S : Finset (Finset ℕ)} {hV' : Φ'.IsValid n m} {S' : Finset (Finset ℕ)}
    (hc : Φ'.centerOf S' = (Φ.centerOf S).comap h) {c'' : ℕ}
    (hc'' : c'' < (Φ'.blowUpPieces S' m).nextComp)
    (hlt : MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c'' <
      (Φ.blowUpPieces S m).nextComp) :
    (E'.totalTransform (Φ'.centerOf S')).component
        ((Φ'.blowUpPieces S' m).memberOf (E := E'.totalTransform (Φ'.centerOf S')) (extendIso e')
          c'' hc'') =
      ((E.totalTransform (Φ.centerOf S)).component
        ((Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
          (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c'') hlt)).comap
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
            Scheme.Hom.blowUpMap h (Φ.centerOf S)) := by
  classical
  change c'' < Φ'.nextComp + S'.card at hc''
  by_cases hlt' : c'' < Φ'.nextComp
  · -- an old child
    have hm' : (Φ'.blowUpPieces S' m).memberOf (E := E'.totalTransform (Φ'.centerOf S'))
        (extendIso e') c'' hc'' =
        (toLex (Sum.inl (Φ'.memberOf e' c'' hlt')) : E'.ι ⊕ₗ PUnit.{u + 1}) := by
      refine (extendIso e').injective ?_
      change extendIso e' ((extendIso e').symm ⟨(Φ'.blowUpPieces S' m).label c'', _⟩) =
        extendIso e' (toLex (Sum.inl (Φ'.memberOf e' c'' hlt')))
      rw [OrderIso.apply_symm_apply, extendIso_inl]
      refine Fin.ext ?_
      change (Φ'.blowUpPieces S' m).label c'' = ((e' (Φ'.memberOf e' c'' hlt') : Fin _) : ℕ)
      rw [Φ'.coe_apply_memberOf]
      exact Φ'.blowUpPieces_label_of_lt S' hlt'
    have hm : (Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c'') hlt =
        (toLex (Sum.inl (Φ.memberOf e (ρ c'') (hρ.lt c'' hlt'))) : E.ι ⊕ₗ PUnit.{u + 1}) := by
      refine (extendIso e).injective ?_
      change extendIso e ((extendIso e).symm ⟨(Φ.blowUpPieces S m).label
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c''), _⟩) =
        extendIso e (toLex (Sum.inl (Φ.memberOf e (ρ c'') (hρ.lt c'' hlt'))))
      rw [OrderIso.apply_symm_apply, extendIso_inl]
      refine Fin.ext ?_
      change (Φ.blowUpPieces S m).label
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S c'') =
        ((e (Φ.memberOf e (ρ c'') (hρ.lt c'' hlt')) : Fin _) : ℕ)
      rw [MonomialState.extendComp_of_lt ρ _ _ S' S hlt', Φ.blowUpPieces_label_of_lt S
        (hρ.lt c'' hlt'), Φ.coe_apply_memberOf]
    rw [hm', hm]
    change (E'.component (Φ'.memberOf e' c'' hlt')).strictTransform (Φ'.centerOf S') =
      ((E.component (Φ.memberOf e (ρ c'') (hρ.lt c'' hlt'))).strictTransform (Φ.centerOf S)).comap
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S))
    rw [hlab c'' hlt', Scheme.IdealSheafData.comap_comp,
      ← strictTransform_comap_of_flat h (Φ.centerOf S),
      strictTransform_comap_eqToHom hc]
  · -- a new child
    obtain ⟨Q, hQ, rfl⟩ := MonomialState.exists_newComp_eq (Φ'.toState n m hV') S'
      (not_lt.mp hlt') hc''
    have hm' : (Φ'.blowUpPieces S' m).memberOf (E := E'.totalTransform (Φ'.centerOf S'))
        (extendIso e') ((Φ'.toState n m hV').newComp S' Q) hc'' =
        (toLex (Sum.inr PUnit.unit) : E'.ι ⊕ₗ PUnit.{u + 1}) := by
      refine (extendIso e').injective ?_
      change extendIso e' ((extendIso e').symm ⟨(Φ'.blowUpPieces S' m).label
        ((Φ'.toState n m hV').newComp S' Q), _⟩) = extendIso e' (toLex (Sum.inr PUnit.unit))
      rw [OrderIso.apply_symm_apply, extendIso_inr]
      refine Fin.ext ?_
      change (Φ'.blowUpPieces S' m).label (Φ'.newComp S' Q) = Φ'.nextLabel
      exact Φ'.blowUpPieces_label_newComp S' Q
    have hm : (Φ.blowUpPieces S m).memberOf (E := E.totalTransform (Φ.centerOf S)) (extendIso e)
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S
          ((Φ'.toState n m hV').newComp S' Q)) hlt =
        (toLex (Sum.inr PUnit.unit) : E.ι ⊕ₗ PUnit.{u + 1}) := by
      refine (extendIso e).injective ?_
      change extendIso e ((extendIso e).symm ⟨(Φ.blowUpPieces S m).label
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S
          ((Φ'.toState n m hV').newComp S' Q)), _⟩) = extendIso e (toLex (Sum.inr PUnit.unit))
      rw [OrderIso.apply_symm_apply, extendIso_inr]
      refine Fin.ext ?_
      change (Φ.blowUpPieces S m).label
        (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S' S
          ((Φ'.toState n m hV').newComp S' Q)) = Φ.nextLabel
      rw [MonomialState.extendComp_newComp ρ _ _ S' S hQ]
      exact Φ.blowUpPieces_label_newComp S _
    rw [hm', hm]
    change (Φ'.centerOf S').exceptionalDivisor = (Φ.centerOf S).exceptionalDivisor.comap
      (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫ Scheme.Hom.blowUpMap h (Φ.centerOf S))
    rw [Scheme.IdealSheafData.comap_comp,
      ← exceptionalDivisor_comap h (Φ.centerOf S),
      exceptionalDivisor_comap_eqToHom hc]

end Step

/-! ### The fold: the run on `Y` is the pull-back of the run on `X` -/

section Fold

variable {k k' : Type u} [Field k] [PerfectField k] [Field k'] [PerfectField k']

/-- *Along a run on `X`, the chain run on a family of `Y` refining along a flat surjection `h`
realises the pull-back of the realisation*, by one induction on the run: the centre of `Y` is the
pull-back of the centre of `X` (`centerOf_eq_comap`), the transported families refine again along
the induced morphism of blow-ups (`blowUpPieces_refinesAlong`), which is again a flat surjection,
and `pullback_eqToHom_comp` of `Hironaka/Scheme/BlowUpSequence/Pullback.lean` identifies the tails.
The general form, `h` flat with the snc of the pulled-back boundary as a hypothesis. -/
theorem realizeAux_pullback_of_surjective (L : List (Finset (Finset ℕ))) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
      (g : Y ⟶ Spec (CommRingCat.of k')) [Smooth g] [QuasiCompact g] (h : Y ⟶ X) [Flat h],
      Function.Surjective h →
      ∀ (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel},
      E.IsSnc → Φ.Realizes E e → ∀ {n m : ℕ} (hV : Φ.IsValid n m),
      (∃ n' ≤ n, SmoothOfRelativeDimension n' f) → ∀ {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' →
      ∀ (Φ' : PieceFamily Y) {E' : DivisorFamily Y} {e' : E'.ι ≃o Fin Φ'.nextLabel} {ρ : ℕ → ℕ}
      (hρ : Φ'.RefinesAlongW h ρ Φ), E'.IsSnc → Φ'.Realizes E' e' →
      (∀ c' (hc' : c' < Φ'.nextComp), E'.component (Φ'.memberOf e' c' hc') =
        (E.component (Φ.memberOf e (ρ c') (hρ.lt c' hc'))).comap h) →
      ∀ (hV' : Φ'.IsValid n m), (∃ n' ≤ n, SmoothOfRelativeDimension n' g) →
      MonomialState.Refines ρ (Φ'.toState n m hV') (Φ.toState n m hV) →
      realizeAux Φ' m (MonomialState.chainRun ρ (Φ'.toState n m hV') (Φ.toState n m hV) L) =
        (realizeAux Φ m L).pullback h := by
  induction L with
  | nil =>
    intro X Y f _ _ g _ _ h _ _ Φ E e _ _ n m hV _ st' _ Φ' E' e' ρ _ _ _ _ hV' _ _
    rfl
  | cons S L ih =>
    intro X Y f _ _ g _ _ h _ hs Φ E e hE hΦ n m hV hn st' hrun Φ' E' e' ρ hρ hE' hΦ' hlab hV'
      hn' hR
    obtain ⟨n₀, hn₀n, hsm₀⟩ := hn
    obtain ⟨n₁, hn₁n, hsm₁⟩ := hn'
    cases hrun with
    | cons r hr hrn hne hL =>
      set S' : Finset (Finset ℕ) :=
        (Φ'.toState n m hV').nerve.filter fun Q => Q.image ρ ∈ (Φ.toState n m hV).choice r
        with hS'def
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        (Φ.toState n m hV).isCenter_choice r
      have hS'eq : S' = (Φ'.toState n m hV').choice r := (hR.choice_eq r).symm
      have hS' : (Φ'.toState n m hV').IsCenter S' := by
        rw [hS'eq]
        exact (Φ'.toState n m hV').isCenter_choice r
      have hS'S : ∀ Q ∈ S', Q.image ρ ∈ (Φ.toState n m hV).choice r := fun Q hQ =>
        (Finset.mem_filter.mp hQ).2
      have hpre : ∀ Q ∈ (Φ'.toState n m hV').nerve, Q.image ρ ∈ (Φ.toState n m hV).choice r →
          Q ∈ S' := fun Q hQ hQS => Finset.mem_filter.mpr ⟨hQ, hQS⟩
      have hlift : ∀ P ∈ (Φ.toState n m hV).choice r, ∀ y : Y, h y ∈ Φ.faceSet P →
          ∃ Q ∈ S', y ∈ Φ'.faceSet Q := by
        intro P hP y hy
        obtain ⟨Q, hQ, hQP, hyQ⟩ := hρ.exists_image_eq (hS.1 hP) hy
        exact ⟨Q, hpre Q hQ (hQP ▸ hP), hyQ⟩
      have hc := centerOf_eq_comap hE hΦ hE' hρ hΦ' hlab hS hS' hS'S hlift
      have hSY : S' ⊆ (Φ'.toState n m hV').nerve := Finset.filter_subset _ _
      have hSL : (Φ.toState n m hV).choice r = S'.image (Finset.image ρ) := by
        rw [hS'eq]
        exact hR.choice_image r
      -- the data at the next stage on `X`
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
      -- the data at the next stage on `Y`
      have hE'₁ := totalTransform_isSnc g E' _ hE'
        (Φ'.hasSncWith_centerOf hE' hΦ' hS')
      have hΦ'₁ := Φ'.realizes_blowUpPieces g hE' hΦ' hS'
      have hV'₁ := Φ'.valid_blowUpPieces g hE' hΦ' hS'
      have hst'₁ := Φ'.toState_blowUpPieces g hE' hΦ' hV'₁ hS'
      have hsmZ' : Smooth ((Φ'.centerOf S').subschemeι ≫ g) := Φ'.smooth_centerOf g hE' hΦ' hS'
      have hsm₁' := smoothOfRelativeDimension_blowUpπ_comp_of_smooth g n₁
        (Φ'.centerOf S')
      have hsmooth₁ : Smooth ((Φ'.centerOf S').blowUpπ ≫ g) :=
        SmoothOfRelativeDimension.smooth n₁ _
      have hLNY : IsLocallyNoetherian Y := g.isLocallyNoetherian_of_field
      have hproperY := blowUp.isProper_π (Φ'.centerOf S')
      -- the induced morphism of blow-ups: flat and surjective
      have hflat₁ :
          Flat (Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))) :=
        flat_blowUpMap h _
      have hs₁ : Function.Surjective (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
          Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))) := by
        intro x'
        obtain ⟨y₁, hy₁⟩ := surjective_blowUpMap h hs _ x'
        obtain ⟨y₂, hy₂⟩ :=
          surjective_of_isIso (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc)) y₁
        refine ⟨y₂, ?_⟩
        change Scheme.Hom.blowUpMap h _ (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) y₂) = x'
        rw [hy₂, hy₁]
      have hρ₁ := blowUpPieces_refinesAlongW f g hρ hS hS' hS'S hlift hc
      have hR₁ : MonomialState.Refines
          (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S'
            ((Φ.toState n m hV).choice r))
          ((Φ'.blowUpPieces S' m).toState n m hV'₁) ((Φ.blowUpPieces _ m).toState n m hV₁) := by
        rw [hst'₁, hst₁]
        exact hR.blowUp hSY hSL hpre
      have hIH := ih ((Φ.centerOf _).blowUpπ ≫ f) ((Φ'.centerOf S').blowUpπ ≫ g)
        (eqToHom (congrArg Scheme.IdealSheafData.blowUp hc) ≫
          Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r)))
        hs₁ (Φ.blowUpPieces _ m) hE₁ hΦ₁ hV₁ ⟨n₀, hn₀n, hsm₀'⟩ hrun₁ (Φ'.blowUpPieces S' m) hρ₁
        hE'₁ hΦ'₁
        (fun c'' hc'' => totalTransform_component_memberOf_blowUpPieces hρ hlab hc hc'' _)
        hV'₁ ⟨n₁, hn₁n, hsm₁'⟩ hR₁
      -- assemble
      change BlowUpSequence.cons Y (Φ'.centerOf S')
        (realizeAux (Φ'.blowUpPieces S' m) m
          (MonomialState.chainRun
            (MonomialState.extendComp ρ (Φ'.toState n m hV') (Φ.toState n m hV) S'
              ((Φ.toState n m hV).choice r))
            ((Φ'.toState n m hV').blowUp S') ((Φ.toState n m hV).blowUp _) L)) =
        BlowUpSequence.cons Y ((Φ.centerOf _).comap h)
          ((realizeAux (Φ.blowUpPieces _ m) m L).pullback
            (Scheme.Hom.blowUpMap h (Φ.centerOf ((Φ.toState n m hV).choice r))))
      rw [← hst'₁, ← hst₁]
      refine cons_congr hc ?_
      rw [hIH]
      exact pullback_eqToHom_comp _ (congrArg Scheme.IdealSheafData.blowUp hc) _

end Fold

/-! ### The statement for a smooth surjection -/

section

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  [QuasiCompact f] [Smooth h] [QuasiCompact (h ≫ f)]

include f in
/-- The first clause of [Kol07, 34.1] for the geometric Step 3: for a smooth surjection `h`, *the
geometric Step 3 on `Y` is the pull-back of the geometric Step 3 on `X`*. The run on `Y` is the
chain run of the run on `X` (`step3_chain` of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean` on `refines_toState_of_surjective`)
and the chain run realises the pull-back (`realizeAux_pullback_of_surjective` with `Y`'s structure
morphism `h ≫ f`). -/
theorem realize_pullback_of_surjective (hs : Function.Surjective h) (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m) (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (hn' : ∃ n' ≤ n, SmoothOfRelativeDimension n' (h ≫ f)) (hρ : Φ'.RefinesAlong h ρ Φ)
    (hΦ' : Φ'.Realizes (E.comap h) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)))
    (hV' : Φ'.IsValid n m) :
    Φ'.realize n m hV' = (Φ.realize n m hV).pullback h := by
  have hE' : (E.comap h).IsSnc := isSnc_comap_of_smooth f h hE
  have hR := refines_toState_of_surjective hρ hs hV hV'
  obtain ⟨-, hrun, -⟩ := MonomialState.step3_chain hR
  have hlab := component_comap_memberOf (e := e) hρ
  change realizeAux Φ' m (MonomialState.step3 (Φ'.toState n m hV')).2 =
    (realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).pullback h
  rw [hrun]
  exact realizeAux_pullback_of_surjective _ f (h ≫ f) h hs Φ hE hΦ hV hn
    (MonomialState.step3_isRun _) Φ' hρ.toW hE' hΦ' hlab hV' hn' hR

end

end Hironaka.Monomial.PieceFamily
