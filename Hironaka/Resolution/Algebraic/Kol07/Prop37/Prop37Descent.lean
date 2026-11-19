/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Setting
import Hironaka.Scheme.BlowUp.GlueIdealSheaf
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Descent of blow-up sequences along an open cover: the recursion of the proof of Proposition 37

The proof of [Kol07, Proposition 37] descends the blow-up sequence `B(X')` on the disjoint union
`X' = ∐ᵢ Uᵢ` of a finite affine open cover (`coverScheme` of
`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean`, with `g = coverDesc : X' → X` and
the two projections `τ₁, τ₂ : X'' = X' ×_X X' → X'`) to a blow-up sequence on `X`. This module
proves the parts of the argument that concern sequences as such, without the order condition of
[Kol07, Definition 66], which `Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Local.lean` adds
stage by stage.

* **The compatibility (37.1).** Since `B` commutes with the smooth surjections `τᵢ`, and `X''`
  carries the pullback data of `X'` along both (`coverPairTriple_isPullbackOf_fst/_snd`),
  `τ₁^* B(X') = B(X'') = τ₂^* B(X')` as whole sequences
  (`OrderSeqAssignment.pullback_coverFst_eq_pullback_coverSnd`); for the first center this is
  `τ₁^*(Z₀') = τ₂^*(Z₀')`, read off by `cons` injectivity (`center_zero_comap_eq`).
* **(37.1) is (37.2) on the pieces.** The kernel pair `X' ×_X X'` is covered by the open pieces
  `Uᵢ ×_X Uⱼ` (Mathlib's `Scheme.Pullback.openCoverOfLeftRight` of the two `Sigma.ι` covers), the
  piece `Uᵢ ×_X Uⱼ → X' ×_X X'` being `pullback.map` along the two inclusions
  (`Triple.piecePairMap`). An ideal sheaf on `X''` is determined by its restrictions to the pieces
  (`ext_of_openCover`), and so is a blow-up sequence (`eq_of_pullback_of_covers`, on a nonempty
  index type; for the empty cover `X''` is empty and `τ₁ = τ₂` outright). Hence
  `τ₁^* D = τ₂^* D` iff `D|_{Uᵢ}` and `D|_{Uⱼ}` agree on every `Uᵢ ×_X Uⱼ`
  (`Triple.comap_coverFst_eq_comap_coverSnd_iff`), and `τ₁^* S = τ₂^* S` iff the restrictions
  `S|_{Uᵢ}` **agree on the overlaps** (`Triple.pullback_coverFst_eq_pullback_coverSnd_iff`; the
  predicate `BlowUpSequence.AgreeOnOverlaps`).
* **Gluing the first center.** Compatible ideal sheaves on the members of an open cover glue
  (`IdealSheafData.glue`, `glue_comap`): the glued `Z₀` satisfies `g^* Z₀ = Z₀'`, checked piece by
  piece (`Triple.exists_comap_coverDesc_eq`); `g^*` is injective because the pieces cover `X`
  (`Triple.comap_coverDesc_injective`).
* **The recursion.** "We can repeat the above argument … and eventually get the whole blow-up
  sequence for `X`", in the form of a family: a family of blow-up sequences `S i` on a covering
  family of open immersions `ι i : W i → X` agreeing on the overlaps is the family of pullbacks of
  one sequence `S₀` on `X` (`exists_pullback_eq_of_agreeOnOverlaps`). The proof is an induction on
  the common length: the first centers `D i` agree on the overlaps (`cons` injectivity) and glue
  to `Z₀` with `Z₀|_{W i} = D i`; the tails, transported to `blowUp (W i) (Z₀|_{W i})` along that
  equality (`cons_eq_cons_pullback_eqToHom`), form a family on the **lifted** covering family
  `blowUpMap (ι i) Z₀ : blowUp (W i) (Z₀|_{W i}) → Z₀.blowUp` (open immersions; covering, by
  the cartesian square of the blow-up maps), and they agree on the lifted overlaps because the
  overlap of two lifted pieces is the blow-up of the overlap of the pieces
  (`isPullback_blowUpMap_of_isPullback`, the base-change squares pasted), so that the hypothesis
  on the tails transports along the identification (`pullback_injective_of_isIso`,
  `pullback_eqToHom_heq`). The induction hypothesis descends the tails to `S₁` on `Z₀.blowUp`,
  and `S₀ := cons X Z₀ S₁`. Kollár's form on the affine cover
  (`Triple.exists_pullback_coverDesc_eq`) is the family form for the pieces `Uᵢ` composed with the
  previous item, the descended sequence
  pulling back to the given one on `X'` by locality on the cover `Sigma.ι`; when `X` is empty
  (`X'` too, no pieces), `g` is a morphism between initial objects and the descent is the pullback
  along its inverse. Uniqueness is the injectivity of pullback along a surjective flat morphism
  (`Triple.pullback_coverDesc_injective`; "if `h` is surjective then `h^* B` determines `B`
  uniquely", [Kol07, 30.1]).
* **No empty blow-ups.** The centers of `g^* S` are the inverse images of the centers of `S`
  under the stage lifts (`center_pullback`) and `comap ⊤ = ⊤` along any morphism, so an empty
  center of `S` would be an empty center of `g^* S` (`NoEmptyCenters.of_pullback`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Transport lemmas for the recursion -/

/-- Pulling a sequence back along an `eqToHom` is a transport of its base: heterogeneously it is
the sequence itself. -/
theorem pullback_eqToHom_heq (S : BlowUpSequence X) {X' : Scheme.{u}} (e : X' = X) :
    HEq (S.pullback (eqToHom e)) S := by
  subst e
  rw [eqToHom_refl, pullback_id]

/-- Pullback along an isomorphism is injective on sequences: the inverse pulls back to the
inverse (`pullback_comp`, `pullback_id`). -/
theorem pullback_injective_of_isIso {S S' : BlowUpSequence X} (e : Y ⟶ X) [IsIso e]
    (h : S.pullback e = S'.pullback e) : S = S' := by
  have key : ∀ S : BlowUpSequence X, S = (S.pullback e).pullback (inv e) := fun S => by
    rw [← pullback_comp, IsIso.inv_hom_id, pullback_id]
  rw [key S, key S', h]

/-- A sequence of length `0` is the empty sequence. -/
theorem eq_nil_of_length_eq_zero {S : BlowUpSequence X} (h : S.length = 0) : S = nil X := by
  cases S with
  | nil => rfl
  | cons _ D r => exact absurd h (Nat.succ_ne_zero _)

/-- A sequence of length `n + 1` is a `cons` with a tail of length `n`. -/
theorem exists_eq_cons_of_length_eq_succ {S : BlowUpSequence X} {n : ℕ} (h : S.length = n + 1) :
    ∃ (D : X.IdealSheafData) (r : BlowUpSequence D.blowUp), r.length = n ∧ S = cons X D r := by
  cases S with
  | nil => exact absurd h (Nat.zero_ne_add_one _)
  | cons _ D r => exact ⟨D, r, Nat.succ.inj h, rfl⟩

/-- The transported tail of `cons_inj` is heterogeneously equal to the tail. -/
theorem heq_of_transport_eq {D D' : X.IdealSheafData} (e : D = D') {r : BlowUpSequence D.blowUp}
    {r' : BlowUpSequence D'.blowUp} (h : (e ▸ r : BlowUpSequence D'.blowUp) = r') :
    HEq r r' := by
  subst e
  exact heq_of_eq h

/-- Rewriting the center of a `cons` along an equality of ideal sheaves: the tail is transported
by pullback along the `eqToHom` of the blow-ups. -/
theorem cons_eq_cons_pullback_eqToHom {D D' : X.IdealSheafData} (e : D = D')
    (r : BlowUpSequence D'.blowUp) :
    cons X D' r = cons X D (r.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp e))) := by
  subst e
  rw [eqToHom_refl, pullback_id]

/-! ### The first center of (37.1) -/

/-- Equal pullbacks of a `cons` along `τ₁, τ₂` have equal inverse images of the first center (the
compatibility (37.1) of the proof of [Kol07, Proposition 37]): `cons` injectivity. -/
theorem center_zero_comap_eq {Z : Scheme.{u}} (τ₁ τ₂ : Z ⟶ Y) (D : Y.IdealSheafData)
    (rest : BlowUpSequence D.blowUp)
    (h : (cons Y D rest).pullback τ₁ = (cons Y D rest).pullback τ₂) : D.comap τ₁ = D.comap τ₂ :=
  (cons_inj h).1

/-! ### No empty blow-ups -/

/-- A sequence whose pullback along `g` has no empty centers has none (the empty blow-up
convention of [Kol07, 32] descends): the center of the pullback at stage `i` is the inverse image
of the center of `S` under the stage lift, and the inverse image of `⊤` is `⊤`. -/
theorem NoEmptyCenters.of_pullback (g : Y ⟶ X) {S : BlowUpSequence X}
    (h : (S.pullback g).NoEmptyCenters) : S.NoEmptyCenters := by
  intro i hi
  apply h (S.pullbackCenterIdx g i)
  change (S.pullback g).center _ = ⊤
  rw [center_pullback, show S.center i = ⊤ from hi, Scheme.IdealSheafData.comap_top]

/-! ### The descent recursion, for sequences -/

/-- The open cover of `X` by a covering family of open immersions `ι i : W i ⟶ X` (Mathlib's
`Cover.mkOfCovers`); a named definition so that the gluing of ideal sheaves can be applied to a
family without unfolding the cover's fields. -/
noncomputable def familyCover {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) : X.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers σ W ι hcov

/-- Gluing of ideal sheaves for a covering family of open immersions: ideal sheaves on the
members agreeing on the pairwise fibre products glue to an ideal sheaf on `X` restricting to
them. -/
theorem exists_comap_eq_of_agree {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (D : ∀ i, (W i).IdealSheafData)
    (compat : ∀ i j, (D i).comap (pullback.fst (ι i) (ι j)) =
      (D j).comap (pullback.snd (ι i) (ι j))) :
    ∃ Z : X.IdealSheafData, ∀ i, Z.comap (ι i) = D i := by
  have compat' : Scheme.IdealSheafData.GlueCompat (familyCover ι hcov) D := compat
  have key := Scheme.IdealSheafData.glue_comap (𝒰 := familyCover ι hcov) D compat'
  exact ⟨_, key⟩

/-- The lifted covering family: the `blowUpMap (ι i) Z₀ : blowUp (W i) (Z₀|_{W i}) → Z₀.blowUp`
cover the blow-up when the `ι i` cover `X`; a point over the range of `ι i` comes from
`blowUp (W i) (Z₀|_{W i})` (`exists_blowUpMap_eq`, the cartesian square of the blow-up maps). -/
theorem exists_blowUpMap_eq_of_covers {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x) (Z₀ : X.IdealSheafData) (z) :
    ∃ i w, Scheme.Hom.blowUpMap (ι i) Z₀ w = z := by
  obtain ⟨i, y, hy⟩ := hcov (Z₀.blowUpπ z)
  obtain ⟨w, hw⟩ := Remark33.exists_blowUpMap_eq (ι i) Z₀ z y hy.symm
  exact ⟨i, w, hw⟩

/-- The tails of two `cons` sequences with restricted first centres, agreeing on the overlap
`W i ×_X W j`, agree after pullback to the blow-up of the overlap along the restricted centre — the
tail of the hypothesis (`cons_inj`), transported along the equality of the two restrictions of
the centre to the overlap (`heq_of_transport_eq`, `pullback_eqToHom_heq`). -/
theorem pullback_blowUpMap_fst_eq_of_agree {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    (Z₀ : X.IdealSheafData) (r : ∀ i, BlowUpSequence (Z₀.comap (ι i)).blowUp)
    (hc : AgreeOnOverlaps ι fun i => cons (W i) (Z₀.comap (ι i)) (r i)) (i j : σ) :
    (r i).pullback (Scheme.Hom.blowUpMap (pullback.fst (ι i) (ι j)) (Z₀.comap (ι i))) =
      (r j).pullback (eqToHom
          (congrArg (Scheme.IdealSheafData.blowUp (X := Limits.pullback (ι i) (ι j)))
        (comap_comap_eq_of_comm Z₀ (ι j) (ι i) _ _ pullback.condition)) ≫
        Scheme.Hom.blowUpMap (pullback.snd (ι i) (ι j)) (Z₀.comap (ι j))) := by
  have h : (cons (W i) (Z₀.comap (ι i)) (r i)).pullback (pullback.fst (ι i) (ι j)) =
      (cons (W j) (Z₀.comap (ι j)) (r j)).pullback (pullback.snd (ι i) (ι j)) := hc i j
  rw [pullback_comp]
  obtain ⟨e, he⟩ := cons_inj h
  apply eq_of_heq
  exact HEq.trans (heq_of_transport_eq e he) (pullback_eqToHom_heq _ _).symm

/-- The tails of a family of `cons` sequences with a common (restricted) first center agreeing on
the overlaps agree on the lifted overlaps: the overlap of two lifted pieces is the blow-up of the
overlap of the pieces (`isPullback_blowUpMap_of_isPullback`, the base-change squares pasted),
along which identification (`pullback_injective_of_isIso`) the hypothesis on the tails transports
(`pullback_blowUpMap_fst_eq_of_agree`). -/
theorem agreeOnOverlaps_blowUpMap {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] (Z₀ : X.IdealSheafData)
    (r : ∀ i, BlowUpSequence (Z₀.comap (ι i)).blowUp)
    (hc : AgreeOnOverlaps ι fun i => cons (W i) (Z₀.comap (ι i)) (r i)) :
    AgreeOnOverlaps (fun i => Scheme.Hom.blowUpMap (ι i) Z₀) r := by
  intro i j
  beta_reduce
  have H := isPullback_blowUpMap_of_isPullback
    (IsPullback.of_hasPullback (ι i) (ι j)) Z₀
  apply pullback_injective_of_isIso H.isoPullback.hom
  rw [← pullback_comp, ← pullback_comp, H.isoPullback_hom_fst, H.isoPullback_hom_snd]
  exact pullback_blowUpMap_fst_eq_of_agree ι Z₀ r hc i j

/-- The recursion of the proof of [Kol07, Proposition 37] on the common length `n` of the family:
a family of sequences on a covering family of open immersions, agreeing on the overlaps, is the
family of pullbacks of one sequence. -/
theorem exists_pullback_eq_of_agreeOnOverlaps_aux (n : ℕ) :
    ∀ {X : Scheme.{u}} {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
      [∀ i, IsOpenImmersion (ι i)], (∀ x, ∃ i w, ι i w = x) →
      ∀ (S : ∀ i, BlowUpSequence (W i)), (∀ i, (S i).length = n) → AgreeOnOverlaps ι S →
      ∃ S₀ : BlowUpSequence X, ∀ i, S₀.pullback (ι i) = S i := by
  induction n with
  | zero =>
    intro X σ W ι _ _ S hn _
    exact ⟨nil X, fun i => (eq_nil_of_length_eq_zero (hn i)).symm⟩
  | succ n ih =>
    intro X σ W ι _ hcov S hn hc
    choose D r hr hS using fun i => exists_eq_cons_of_length_eq_succ (hn i)
    -- the first centers glue: (37.2) for them is `cons` injectivity applied to the hypothesis
    obtain ⟨Z₀, hZ⟩ := exists_comap_eq_of_agree ι hcov D fun i j => by
      have h := hc i j
      rw [hS i, hS j] at h
      exact (cons_inj h).1
    -- the tails, transported to the blow-ups of the restricted glued centre
    obtain ⟨r', hS'⟩ : ∃ r' : ∀ i, BlowUpSequence (Z₀.comap (ι i)).blowUp,
        ∀ i, S i = cons (W i) (Z₀.comap (ι i)) (r' i) :=
      ⟨fun i => (r i).pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp (hZ i))),
        fun i => (hS i).trans (cons_eq_cons_pullback_eqToHom (hZ i) (r i))⟩
    have hr' : ∀ i, (r' i).length = n := fun i =>
      Nat.succ.inj ((congrArg BlowUpSequence.length (hS' i)).symm.trans (hn i))
    have hc' : AgreeOnOverlaps ι fun i => cons (W i) (Z₀.comap (ι i)) (r' i) := by
      intro i j
      have h := hc i j
      rwa [hS' i, hS' j] at h
    obtain ⟨S₁, hS₁⟩ := ih (fun i => Scheme.Hom.blowUpMap
        (ι i) Z₀) (exists_blowUpMap_eq_of_covers ι hcov Z₀)
      r' hr' (agreeOnOverlaps_blowUpMap ι Z₀ r' hc')
    refine ⟨cons X Z₀ S₁, fun i => ?_⟩
    rw [hS' i]
    exact congrArg (cons (W i) (Z₀.comap (ι i))) (hS₁ i)

/-- "We can repeat the above argument … and eventually get the whole blow-up sequence for `X`"
(the proof of [Kol07, Proposition 37]): a family of blow-up sequences on a covering family of open
immersions agreeing on the overlaps is the family of pullbacks of one blow-up sequence on `X`.
The members have a common length when the index type is nonempty (`length_pullback` on the
overlaps); when it is empty the conclusion is vacuous. -/
theorem exists_pullback_eq_of_agreeOnOverlaps {σ : Type u} {W : σ → Scheme.{u}}
    (ι : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (ι i)] (hcov : ∀ x, ∃ i w, ι i w = x)
    (S : ∀ i, BlowUpSequence (W i)) (hc : AgreeOnOverlaps ι S) :
    ∃ S₀ : BlowUpSequence X, ∀ i, S₀.pullback (ι i) = S i := by
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨i₀⟩⟩
  · exact ⟨nil X, fun i => (hσ.false i).elim⟩
  · refine exists_pullback_eq_of_agreeOnOverlaps_aux (S i₀).length ι hcov S (fun i => ?_) hc
    have h := congrArg BlowUpSequence.length (hc i i₀)
    rwa [length_pullback, length_pullback] at h

end Hironaka.Sequence

namespace Hironaka

variable {k : Type u} [Field k]

/-! ### The descent datum (37.1) for whole sequences -/

/-- "Since `B` commutes with the `τᵢ`" (the proof of [Kol07, Proposition 37]): for a functor on
the affine class commuting with smooth surjections, `τ₁^* B(X') = B(X'') = τ₂^* B(X')`, because
`X''` carries the pullback data of `X'` along both projections
(`coverPairTriple_isPullbackOf_fst/_snd`) and both are smooth surjections. -/
theorem OrderSeqAssignment.pullback_coverFst_eq_pullback_coverSnd {m : ℕ} [PerfectField k]
    (B : OrderSeqAssignment k m Triple.IsAffineScheme) (hB : B.CommutesWithSmoothSurjections)
    (T : Triple k) :
    (B.seq T.coverTriple (Triple.isAffine_coverTriple T)).pullback T.coverFst =
      (B.seq T.coverTriple (Triple.isAffine_coverTriple T)).pullback T.coverSnd := by
  have : @Smooth T.coverPairTriple.X.left T.coverTriple.X.left T.coverFst :=
    Triple.smooth_coverFst T
  have : @Smooth T.coverPairTriple.X.left T.coverTriple.X.left T.coverSnd :=
    Triple.smooth_coverSnd T
  have h₁ := hB T.coverTriple T.coverPairTriple T.coverFst (Triple.surjective_coverFst T)
    (Triple.coverPairTriple_isPullbackOf_fst T) (Triple.isAffine_coverTriple T)
    (Triple.isAffine_coverPairTriple T)
  have h₂ := hB T.coverTriple T.coverPairTriple T.coverSnd (Triple.surjective_coverSnd T)
    (Triple.coverPairTriple_isPullbackOf_snd T) (Triple.isAffine_coverTriple T)
    (Triple.isAffine_coverPairTriple T)
  exact h₁.symm.trans h₂

/-- The descent datum (37.1) for marked functors. -/
theorem OrderGeSeqAssignment.pullback_coverFst_eq_pullback_coverSnd [PerfectField k]
    (B : OrderGeSeqAssignment k MarkedTriple.IsAffineScheme) (hB : B.CommutesWithSmoothSurjections)
    (T : MarkedTriple k) :
    (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)).pullback T.toTriple.coverFst =
      (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)).pullback
        T.toTriple.coverSnd := by
  have : @Smooth T.coverPairTriple.X.left T.coverTriple.X.left T.toTriple.coverFst :=
    Triple.smooth_coverFst T.toTriple
  have : @Smooth T.coverPairTriple.X.left T.coverTriple.X.left T.toTriple.coverSnd :=
    Triple.smooth_coverSnd T.toTriple
  have hA : T.coverPairTriple.IsAffineScheme := Triple.isAffine_coverPair T.toTriple
  have h₁ := hB T.coverTriple T.coverPairTriple T.toTriple.coverFst
    (Triple.surjective_coverFst T.toTriple) (MarkedTriple.coverPairTriple_isPullbackOf_fst T)
    (MarkedTriple.isAffine_coverTriple T) hA
  have h₂ := hB T.coverTriple T.coverPairTriple T.toTriple.coverSnd
    (Triple.surjective_coverSnd T.toTriple) (MarkedTriple.coverPairTriple_isPullbackOf_snd T)
    (MarkedTriple.isAffine_coverTriple T) hA
  exact h₁.symm.trans h₂

/-! ### The kernel pair and its pieces -/

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

open Scheme

variable (T : Triple k)

/-- The piece `Uᵢ ×_X Uⱼ` of the kernel pair `X' ×_X X'` (Kollár's `X'' = ∐_{i ≤ j} Uᵢ ∩ Uⱼ` in the
proof of [Kol07, Proposition 37]): the map induced by the two inclusions `Uᵢ, Uⱼ → X'`. -/
noncomputable def piecePairMap (i j : T.affineCover.I₀) :
    Limits.pullback (T.affineCover.f i) (T.affineCover.f j) ⟶ T.coverPair :=
  Limits.pullback.map _ _ _ _ (Sigma.ι (fun i => T.affineCover.X i) i)
    (Sigma.ι (fun i => T.affineCover.X i) j) (𝟙 T.X.left)
    (by rw [Category.comp_id, ι_comp_coverDesc]) (by rw [Category.comp_id, ι_comp_coverDesc])

/-- The piece map followed by `τ₁` is the first projection of the piece followed by the inclusion
of `Uᵢ`. -/
theorem piecePairMap_comp_coverFst (i j : T.affineCover.I₀) :
    T.piecePairMap i j ≫ T.coverFst =
      pullback.fst (T.affineCover.f i) (T.affineCover.f j) ≫
        Sigma.ι (fun i => T.affineCover.X i) i :=
  pullback.lift_fst _ _ _

/-- The piece map followed by `τ₂` is the second projection of the piece followed by the inclusion
of `Uⱼ`. -/
theorem piecePairMap_comp_coverSnd (i j : T.affineCover.I₀) :
    T.piecePairMap i j ≫ T.coverSnd =
      pullback.snd (T.affineCover.f i) (T.affineCover.f j) ≫
        Sigma.ι (fun i => T.affineCover.X i) j :=
  pullback.lift_snd _ _ _

/-- The open cover of the kernel pair `X' ×_X X'` by the pieces `Uᵢ ×_X Uⱼ` (Mathlib's cover of a
fibre product by the fibre products of the members of covers of the two factors), indexed by
pairs. -/
noncomputable abbrev coverPairCover : T.coverPair.OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover fun i => T.affineCover.X i)
    (sigmaOpenCover fun i => T.affineCover.X i) T.coverDesc T.coverDesc

/-- The member `(i, j)` of the pieces cover, written out: Mathlib's `pullback.map` along the two
inclusions `Uᵢ, Uⱼ → X'` over `𝟙 X`, from the piece computed with `Sigma.ι ≫ g` (definitionally
`T.coverPairCover.f (i, j)`; the explicit form keeps the source scheme syntactic for rewriting). -/
noncomputable abbrev coverPairPiece (i j : T.affineCover.I₀) :
    Limits.pullback (Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc)
      (Sigma.ι (fun i => T.affineCover.X i) j ≫ T.coverDesc) ⟶ T.coverPair :=
  Limits.pullback.map _ _ _ _ (Sigma.ι (fun i => T.affineCover.X i) i)
    (Sigma.ι (fun i => T.affineCover.X i) j) (𝟙 T.X.left) (Category.comp_id _) (Category.comp_id _)

/-- The member `(i, j)` of the pieces cover is the piece map. -/
theorem coverPairCover_f (i j : T.affineCover.I₀) :
    T.coverPairCover.f (i, j) = T.coverPairPiece i j :=
  rfl

/-- The piece map followed by `τ₁`: the first projection of the piece followed by the inclusion of
`Uᵢ`. -/
theorem coverPairPiece_comp_coverFst (i j : T.affineCover.I₀) :
    T.coverPairPiece i j ≫ T.coverFst =
      pullback.fst (Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc)
        (Sigma.ι (fun i => T.affineCover.X i) j ≫ T.coverDesc) ≫
        Sigma.ι (fun i => T.affineCover.X i) i :=
  pullback.lift_fst _ _ _

/-- The piece map followed by `τ₂`. -/
theorem coverPairPiece_comp_coverSnd (i j : T.affineCover.I₀) :
    T.coverPairPiece i j ≫ T.coverSnd =
      pullback.snd (Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc)
        (Sigma.ι (fun i => T.affineCover.X i) j ≫ T.coverDesc) ≫
        Sigma.ι (fun i => T.affineCover.X i) j :=
  pullback.lift_snd _ _ _

/-- The piece `Uᵢ ×_X Uⱼ` computed with `Sigma.ι ≫ g` and the one computed with the member maps
(`ι_comp_coverDesc`) are identified by `pullback.congrHom`; the first projections correspond. -/
theorem fst_eq_congrHom_comp_fst (i j : T.affineCover.I₀) :
    pullback.fst (Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc)
        (Sigma.ι (fun i => T.affineCover.X i) j ≫ T.coverDesc) =
      (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom ≫
        pullback.fst (T.affineCover.f i) (T.affineCover.f j) := by
  rw [pullback.congrHom_hom]
  exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm

/-- The second projections of the two computations of the piece correspond. -/
theorem snd_eq_congrHom_comp_snd (i j : T.affineCover.I₀) :
    pullback.snd (Sigma.ι (fun i => T.affineCover.X i) i ≫ T.coverDesc)
        (Sigma.ι (fun i => T.affineCover.X i) j ≫ T.coverDesc) =
      (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom ≫
        pullback.snd (T.affineCover.f i) (T.affineCover.f j) := by
  rw [pullback.congrHom_hom]
  exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

/-- The restriction of `τ₁^* D` to the piece `(i, j)` is the restriction of `D|_{Uᵢ}` to
`Uᵢ ×_X Uⱼ`, transported along the identification of the piece. -/
theorem comap_coverFst_comap_coverPairPiece (D : T.coverScheme.IdealSheafData)
    (i j : T.affineCover.I₀) :
    (D.comap T.coverFst).comap (T.coverPairPiece i j) =
      ((D.comap (Sigma.ι (fun i => T.affineCover.X i) i)).comap
        (pullback.fst (T.affineCover.f i) (T.affineCover.f j))).comap
        (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, coverPairPiece_comp_coverFst,
    Scheme.IdealSheafData.comap_comp, fst_eq_congrHom_comp_fst, Scheme.IdealSheafData.comap_comp]

/-- The restriction of `τ₂^* D` to the piece `(i, j)`. -/
theorem comap_coverSnd_comap_coverPairPiece (D : T.coverScheme.IdealSheafData)
    (i j : T.affineCover.I₀) :
    (D.comap T.coverSnd).comap (T.coverPairPiece i j) =
      ((D.comap (Sigma.ι (fun i => T.affineCover.X i) j)).comap
        (pullback.snd (T.affineCover.f i) (T.affineCover.f j))).comap
        (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, coverPairPiece_comp_coverSnd,
    Scheme.IdealSheafData.comap_comp, snd_eq_congrHom_comp_snd, Scheme.IdealSheafData.comap_comp]

/-- (37.1) is (37.2) for ideal sheaves (the proof of [Kol07, Proposition 37]): for an ideal sheaf
on `X' = ∐ Uᵢ`, its two pullbacks to `X' ×_X X'` agree iff, for all `i, j`, its restrictions to
`Uᵢ` and `Uⱼ` agree on `Uᵢ ×_X Uⱼ`, the pieces covering the kernel pair. -/
theorem comap_coverFst_eq_comap_coverSnd_iff (D : T.coverScheme.IdealSheafData) :
    D.comap T.coverFst = D.comap T.coverSnd ↔
      ∀ i j, (D.comap (Sigma.ι (fun i => T.affineCover.X i) i)).comap
          (pullback.fst (T.affineCover.f i) (T.affineCover.f j)) =
        (D.comap (Sigma.ι (fun i => T.affineCover.X i) j)).comap
          (pullback.snd (T.affineCover.f i) (T.affineCover.f j)) := by
  constructor
  · intro h i j
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      ← piecePairMap_comp_coverFst, ← piecePairMap_comp_coverSnd,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h]
  · intro h
    refine Scheme.IdealSheafData.ext_of_openCover T.coverPairCover fun ij => ?_
    refine (comap_coverFst_comap_coverPairPiece T D ij.1 ij.2).trans ?_
    rw [h ij.1 ij.2]
    exact (comap_coverSnd_comap_coverPairPiece T D ij.1 ij.2).symm

/-- When the affine cover has no members, `X'` is empty. -/
theorem isEmpty_coverScheme [IsEmpty T.affineCover.I₀] : IsEmpty T.coverScheme :=
  Function.isEmpty (sigmaMk (fun i => T.affineCover.X i)).symm

/-- When the affine cover has no members, so is the kernel pair. -/
theorem isEmpty_coverPair [IsEmpty T.affineCover.I₀] : IsEmpty T.coverPair :=
  have := isEmpty_coverScheme T
  Function.isEmpty (fun p => T.coverFst p)

/-- When the affine cover has no members the two projections of the (empty) kernel pair agree. -/
theorem coverFst_eq_coverSnd [IsEmpty T.affineCover.I₀] : T.coverFst = T.coverSnd :=
  have := isEmpty_coverPair T
  (isInitialOfIsEmpty (X := T.coverPair)).hom_ext _ _

/-- The pullback of `τ₁^* S` to the piece `(i, j)` is the pullback of `S|_{Uᵢ}` to
`Uᵢ ×_X Uⱼ`, transported along the identification of the piece. -/
theorem pullback_coverFst_pullback_coverPairPiece (S : BlowUpSequence T.coverScheme)
    (i j : T.affineCover.I₀) :
    (S.pullback T.coverFst).pullback (T.coverPairPiece i j) =
      ((S.pullback (Sigma.ι (fun i => T.affineCover.X i) i)).pullback
        (pullback.fst (T.affineCover.f i) (T.affineCover.f j))).pullback
        (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom := by
  rw [← pullback_comp, coverPairPiece_comp_coverFst,
    pullback_comp, fst_eq_congrHom_comp_fst, pullback_comp]

/-- The pullback of `τ₂^* S` to the piece `(i, j)`. -/
theorem pullback_coverSnd_pullback_coverPairPiece (S : BlowUpSequence T.coverScheme)
    (i j : T.affineCover.I₀) :
    (S.pullback T.coverSnd).pullback (T.coverPairPiece i j) =
      ((S.pullback (Sigma.ι (fun i => T.affineCover.X i) j)).pullback
        (pullback.snd (T.affineCover.f i) (T.affineCover.f j))).pullback
        (pullback.congrHom (ι_comp_coverDesc T i) (ι_comp_coverDesc T j)).hom := by
  rw [← pullback_comp, coverPairPiece_comp_coverSnd,
    pullback_comp, snd_eq_congrHom_comp_snd, pullback_comp]

/-- (37.1) is (37.2) for sequences: a sequence on `X' = ∐ Uᵢ` has equal pullbacks along `τ₁, τ₂`
iff its restrictions to the `Uᵢ` agree on the overlaps `Uᵢ ×_X Uⱼ`; the pieces cover the kernel
pair and sequences are determined by their pullbacks to a nonempty covering family
(`eq_of_pullback_of_covers`); with no pieces, `τ₁ = τ₂`. -/
theorem pullback_coverFst_eq_pullback_coverSnd_iff (S : BlowUpSequence T.coverScheme) :
    S.pullback T.coverFst = S.pullback T.coverSnd ↔
      BlowUpSequence.AgreeOnOverlaps T.affineCover.f
        (fun i => S.pullback (Sigma.ι (fun i => T.affineCover.X i) i)) := by
  constructor
  · intro h i j
    change (S.pullback _).pullback _ = (S.pullback _).pullback _
    rw [← pullback_comp, ← pullback_comp,
      ← piecePairMap_comp_coverFst, ← piecePairMap_comp_coverSnd,
      pullback_comp, pullback_comp, h]
  · intro hc
    rcases isEmpty_or_nonempty T.affineCover.I₀ with hσ | hσ
    · rw [coverFst_eq_coverSnd]
    · have : ∀ ij : T.affineCover.I₀ × T.affineCover.I₀, IsOpenImmersion (T.coverPairCover.f ij) :=
        fun ij => T.coverPairCover.map_prop ij
      refine eq_of_pullback_of_covers (σ := T.affineCover.I₀ × T.affineCover.I₀)
        _ _ T.coverPairCover.f (fun y => T.coverPairCover.exists_eq y) fun ij => ?_
      have h : (S.pullback (Sigma.ι (fun i => T.affineCover.X i) ij.1)).pullback
          (pullback.fst (T.affineCover.f ij.1) (T.affineCover.f ij.2)) =
        (S.pullback (Sigma.ι (fun i => T.affineCover.X i) ij.2)).pullback
          (pullback.snd (T.affineCover.f ij.1) (T.affineCover.f ij.2)) := hc ij.1 ij.2
      refine (pullback_coverFst_pullback_coverPairPiece T S ij.1 ij.2).trans ?_
      rw [h]
      exact (pullback_coverSnd_pullback_coverPairPiece T S ij.1 ij.2).symm

/-! ### Gluing the first center -/

/-- The restriction to the piece `Uᵢ` of the inverse image along `g` is the inverse image along
the member map `Uᵢ → X`. -/
theorem comap_coverDesc_comap_ι (Z : T.X.left.IdealSheafData) (i : T.affineCover.I₀) :
    (Z.comap T.coverDesc).comap (Sigma.ι (fun i => T.affineCover.X i) i) =
      Z.comap (T.affineCover.f i) := by
  rw [← Scheme.IdealSheafData.comap_comp, ι_comp_coverDesc]

/-- "The subschemes `Z₀ᵢ' ⊂ Uᵢ` glue together to a subscheme `Z₀ ⊂ X`" (the proof of
[Kol07, Proposition 37]): an ideal sheaf on `X'` with agreeing pullbacks to `X''` is the inverse
image of an ideal sheaf on `X`; the gluing of ideal sheaves along the affine cover, the
compatibility being (37.2); `g^* Z₀ = D` is checked on the pieces of `X'`. -/
theorem exists_comap_coverDesc_eq (D : T.coverScheme.IdealSheafData)
    (h : D.comap T.coverFst = D.comap T.coverSnd) :
    ∃ Z : T.X.left.IdealSheafData, Z.comap T.coverDesc = D := by
  have compat : Scheme.IdealSheafData.GlueCompat T.affineCover
      (fun i => D.comap (Sigma.ι (fun i => T.affineCover.X i) i)) :=
    (comap_coverFst_eq_comap_coverSnd_iff T D).1 h
  refine ⟨Scheme.IdealSheafData.glue _ compat, ?_⟩
  refine Scheme.IdealSheafData.ext_of_openCover (sigmaOpenCover fun i => T.affineCover.X i)
    fun i => ?_
  exact (comap_coverDesc_comap_ι T _ i).trans (Scheme.IdealSheafData.glue_comap _ compat i)

/-- The glued ideal sheaf is unique: inverse image along `g` is injective, the pieces covering
`X`. -/
theorem comap_coverDesc_injective :
    Function.Injective (fun Z : T.X.left.IdealSheafData => Z.comap T.coverDesc) := by
  intro Z Z' h
  refine Scheme.IdealSheafData.ext_of_openCover T.affineCover fun i => ?_
  rw [← comap_coverDesc_comap_ι, ← comap_coverDesc_comap_ι]
  exact congrArg (fun J : T.coverScheme.IdealSheafData =>
    J.comap (Sigma.ι (fun i => T.affineCover.X i) i)) h

/-! ### The descent along the affine cover, and uniqueness -/

/-- When the affine cover has no members, `X` is empty. -/
theorem isEmpty_of_isEmpty_affineCover [IsEmpty T.affineCover.I₀] : IsEmpty T.X.left :=
  ⟨fun x => (T.affineCover.exists_eq x).elim fun i _ => (IsEmpty.false i).elim⟩

/-- Kollár's form of the descent on the affine cover (the proof of [Kol07, Proposition 37]): a
blow-up sequence on `X'` with `τ₁^* S' = τ₂^* S'` descends to `X`, that is, it is `g^* S` for a
sequence `S` on `X`. The restrictions to the pieces agree on the overlaps
(`pullback_coverFst_eq_pullback_coverSnd_iff`), the family form of the recursion descends them
to `S`, and `g^* S = S'` on the cover `Sigma.ι` of `X'` (`eq_of_pullback_of_covers`). With no
pieces, `X` and `X'` are empty, `g` is a morphism of initial objects, and `S` is the pullback of
`S'` along its inverse. -/
theorem exists_pullback_coverDesc_eq (S' : BlowUpSequence T.coverScheme)
    (h : S'.pullback T.coverFst = S'.pullback T.coverSnd) :
    ∃ S : BlowUpSequence T.X.left, S.pullback T.coverDesc = S' := by
  rcases isEmpty_or_nonempty T.affineCover.I₀ with hσ | hσ
  · have := isEmpty_coverScheme T
    have := isEmpty_of_isEmpty_affineCover T
    have hX : IsInitial T.X.left := isInitialOfIsEmpty
    have hX' : IsInitial T.coverScheme := isInitialOfIsEmpty
    refine ⟨S'.pullback (hX.to T.coverScheme), ?_⟩
    rw [← pullback_comp, hX'.hom_ext (T.coverDesc ≫ hX.to T.coverScheme) (𝟙 _),
      pullback_id]
  · obtain ⟨S, hS⟩ := Hironaka.Sequence.exists_pullback_eq_of_agreeOnOverlaps T.affineCover.f
      (fun x => T.affineCover.exists_eq x) _
      ((pullback_coverFst_eq_pullback_coverSnd_iff T S').1 h)
    refine ⟨S, eq_of_pullback_of_covers (σ := T.affineCover.I₀) _ _
      (Sigma.ι fun i => T.affineCover.X i)
      (fun y => (sigmaOpenCover fun i => T.affineCover.X i).exists_eq y) fun i => ?_⟩
    rw [← pullback_comp, ι_comp_coverDesc, hS]

/-- "If `h` is surjective then `h^* B` determines `B` uniquely" [Kol07, 30.1], the uniqueness in
Proposition 37: pullback along the smooth (hence flat) surjection `g : X' → X` is injective on
sequences (`pullback_injective_of_surjective`). -/
theorem pullback_coverDesc_injective :
    Function.Injective (fun S : BlowUpSequence T.X.left => S.pullback T.coverDesc) := by
  have : Smooth T.coverDesc := smooth_coverDesc T
  intro S S' h
  exact pullback_injective_of_surjective T.coverDesc (surjective_coverDesc T) h

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

end Hironaka
