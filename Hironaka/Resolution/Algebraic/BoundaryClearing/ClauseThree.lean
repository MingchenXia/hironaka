/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Parameter
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Assembly
import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyTuned
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.EqNilMarked
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.BlowUpSequence.TrivialCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (3) of Lemma 102

The last paragraph of the proof of [Kol07, Lemma 102]: if `O_X/I = τ_*(O_{E^j}/J)` with `J`
nonzero on every irreducible component of `E^j`, then every local equation of `E^j` is an element
of order `1` of `I`, so `max-ord I = 1` and `W(I) = W_1(I) = I`; no component of `E^j` is selected,
so `Z_{-1} = ∅` and `I_0 = I`; and `I|_{E^j} = J`. Hence
`BD_{n,1,j}(X, I, E) = τ_* BMO_{n−1,1}(E^j, J, 1, (E − E^j)|_{E^j})`.

* `Zminus1_eq_top_of_eq_map`: at a generic point `η = τ(x)` of a component of `E^j` where `I` has
  order `≥ 1`, the stalk ideal of the smooth divisor `E^j` is the maximal ideal
  (`stalkIdeal_eq_maximalIdeal_of_mem_genericPoints`) and `E^j ⊆ I` (`I ⊇ ker τ`), so `I_η` is that
  maximal ideal too; pulling back along `τ` (`stalkIdeal_comap`, `I.comap τ = J` and
  `E^j.comap τ = 0`) gives `J_x = 0`, against `J` nonzero everywhere. So no component of `E^j` is
  selected: `Z_{-1}` is the unit ideal.
* `tuned_one`: `W_{s(1)}(I) = I` (`W_tuningParam_one`), so the tuned triple is `(X, I, E)`.
* `eq_pushforward_of_quotient`: above the mark (`max-ord I = 1`) the value of `BD_{n,1,j}` is the
  output of `Output.lean` for the tuned triple with its empty blow-ups deleted; its first center
  `Z_{-1}|_S` is the unit ideal, so the restricted marked triple is the pull-back of
  `hypersurfaceTriple = (E^j, J, 1, ((E − E^j)|_{E^j}).append ⊤)` along the isomorphism
  `π_S : blowUp E^j ⊤ → E^j` (`markedTransform_of_eq_top`, `totalTransform_of_eq_top`,
  `comap_map_of_isClosedImmersion`), `B` commutes with that smooth surjection (the first bullet of
  [Kol07, 34.1]), the deleted first blow-up transports the tail along `π_X⁻¹`
  (`eraseEmpty_cons_of_eq_top`), and the push-forward/pull-back exchange along the square
  `blowUp E^j ⊤ → blowUp X ⊤` over `E^j → X` (`pullback_pushforward_of_isPullback`; the square is a
  pull-back since its vertical maps are isomorphisms) cancels `π_X⁻¹` against `π_X`. Below the mark
  `I = O_X`, hence `J = O_{E^j}`, and both sides are empty (`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`,
  `pushforward_nil`).

Kollár's `(E − E^j)|_{E^j}` carries no empty member; the appended `⊤` is the exceptional member of
the trivial blow-up in this library's total-transform convention (`Assembly.lean`). Used by
`Hironaka/Resolution/Algebraic/OrderReduction/ClosedEmbedding.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Scheme
  Scheme.Hom Hironaka IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Local

namespace Hironaka.BD

variable {k : Type u} [Field k]

/-- The tuned triple at the mark `1` is the triple itself (Kollár's `W(I) = W_1(I) = I` in the proof
of [Kol07, Lemma 102]; `s(1) = 1` and `W_tuningParam_one`). -/
theorem tuned_one (T : Triple k) : T.tuned 1 le_rfl = T := by
  have key : ∀ (I' : T.X.left.IdealSheafData) (hI' : IsNonzeroEverywhere I') (_ : I' = T.I),
      ({ T with I := I', isNonzeroEverywhere := hI' } : Triple k) = T := by
    rintro I' hI' rfl
    rfl
  exact key _ _ (W_tuningParam_one (T.X.left ↘ Spec (.of k)) T.I)

variable [CharZero k] (T : Triple k) {j : ℕ} (hj : j < Fintype.card T.E.ι)
  (J : (T.E.nth ⟨j, hj⟩).subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J)

/-- The scheme of the marked triple of clause (3) is `E^j`. -/
theorem hypersurfaceTriple_X : (hypersurfaceTriple T hj J hJ).X.left =
    (T.E.nth ⟨j, hj⟩).subscheme :=
  rfl

/-- Its ideal is `J`. -/
theorem hypersurfaceTriple_I : (hypersurfaceTriple T hj J hJ).I = J :=
  rfl

/-- Its mark is `1`. -/
theorem hypersurfaceTriple_m : (hypersurfaceTriple T hj J hJ).m = 1 :=
  rfl

/-- Its family is `(E − E^j)|_{E^j}` followed by an empty member. -/
theorem hypersurfaceTriple_E :
    (hypersurfaceTriple T hj J hJ).E =
      ((T.E.erase (pos T hj)).comap (T.E.nth ⟨j, hj⟩).subschemeι).append ⊤ :=
  rfl

variable (hIJ : T.I = J.map (T.E.nth ⟨j, hj⟩).subschemeι)

include hJ hIJ in
/-- No component of `E^j` is selected, `Z_{-1}` is the unit ideal (Kollár: `J` nonzero on every
irreducible component of `E^j` gives `Z_{-1} = ∅`, the proof of [Kol07, Lemma 102]). -/
theorem Zminus1_eq_top_of_eq_map : Zminus1 T.I 1 (T.E.nth ⟨j, hj⟩) = ⊤ := by
  have := T.smooth
  have : Smooth ((T.E.nth ⟨j, hj⟩).subschemeι ≫ (T.X.left ↘ Spec (.of k))) :=
    smooth_component T (pos T hj)
  have hempty : IsEmpty {η : T.X.left // η ∈ (T.E.nth ⟨j, hj⟩).support.genericPoints ∧
      ((1 : ℕ) : ℕ∞) ≤ T.I.ord η} := by
    refine ⟨fun ⟨η, hη, hord⟩ => ?_⟩
    have hηD : η ∈ ((T.E.nth ⟨j, hj⟩).support : Set T.X.left) := hη.1
    rw [← Scheme.IdealSheafData.range_subschemeι] at hηD
    obtain ⟨x, rfl⟩ := hηD
    have hmax := stalkIdeal_eq_maximalIdeal_of_mem_genericPoints (T.X.left ↘ Spec (.of k))
      (T.E.nth ⟨j, hj⟩) hη
    have hle : T.E.nth ⟨j, hj⟩ ≤ T.I := by
      have h1 : (T.E.nth ⟨j, hj⟩).subschemeι.ker ≤ J.map (T.E.nth ⟨j, hj⟩).subschemeι := by
        rw [← Scheme.IdealSheafData.map_bot]
        exact Scheme.IdealSheafData.map_mono _ bot_le
      rwa [Scheme.IdealSheafData.ker_subschemeι, ← hIJ] at h1
    have hIη : T.I.stalkIdeal ((T.E.nth ⟨j, hj⟩).subschemeι x) ≤ maximalIdeal _ :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        ((one_le_ord_iff _ _).mp (by simpa using hord))
    have hEq : T.I.stalkIdeal ((T.E.nth ⟨j, hj⟩).subschemeι x) =
        (T.E.nth ⟨j, hj⟩).stalkIdeal ((T.E.nth ⟨j, hj⟩).subschemeι x) :=
      le_antisymm (by rw [hmax]; exact hIη) (stalkIdeal_mono hle _)
    have hJx : J.stalkIdeal x = ⊥ := by
      have e1 : J = T.I.comap (T.E.nth ⟨j, hj⟩).subschemeι := by
        rw [hIJ, comap_map_of_isClosedImmersion]
      have e2 : (T.E.nth ⟨j, hj⟩).comap (T.E.nth ⟨j, hj⟩).subschemeι = ⊥ := by
        have h := comap_map_of_isClosedImmersion (T.E.nth ⟨j, hj⟩).subschemeι ⊥
        rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at h
      rw [e1, stalkIdeal_comap, hEq, ← stalkIdeal_comap, e2]
      obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
      rw [stalkIdeal_eq_map_germ _ U hxU]
      simp [Scheme.IdealSheafData.ideal_bot]
    exact hJ x hJx
  unfold Zminus1
  rw [iSup_of_empty, vanishingIdeal_bot]

include hIJ in
/-- Clause (3) of [Kol07, Lemma 102]: if `J ⊂ O_{E^j}` is nonzero on every irreducible component of
`E^j` and `τ_*(O_{E^j}/J) = O_X/I`, then `BD_{n,1,j}(X, I, E) = τ_* B(E^j, J, 1, (E − E^j)|_{E^j})`
(the family with the appended empty member); `max-ord I ≤ 1` is derived
(`maxOrd_le_one_of_eq_map`), and at `max-ord I = 0` both sides are empty. -/
theorem eq_pushforward_of_quotient {n : ℕ} (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam 1 → Dom T')
    (hB : B.CommutesWithSmoothSurjections) :
    (dataFunctor n 1 j le_rfl B hDom).seq T (bdClass_one_of_eq_map T hj J hIJ hn) =
      BlowUpSequence.pushforward (Y := (T.E.nth ⟨j, hj⟩).subscheme)
        (B.seq (hypersurfaceTriple T hj J hJ)
          (hDom _ (hasDimLE_hypersurfaceTriple T hj J hJ hn) tuningParam_one.symm))
        (T.E.nth ⟨j, hj⟩).subschemeι := by
  have hT : Triple.BDClass n 1 j T := bdClass_one_of_eq_map T hj J hIJ hn
  by_cases h : T.I.maxOrd = ((1 : ℕ) : ℕ∞)
  · rw [dataFunctor_seq_of_maxOrd_eq n 1 j le_rfl B hDom T hT h]
    obtain ⟨hn', hI', hmax', hj'⟩ : Domain n (tuningParam 1) j (T.tuned 1 le_rfl) :=
      domain_tuned le_rfl hT h
    have hRm : (restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj) hI' hmax').m =
      tuningParam 1 := rfl
    have hHm : (hypersurfaceTriple T hj J hJ).m = tuningParam 1 := tuningParam_one.symm
    -- the whole goal in the `component (pos T hj)` form of `E^j` (instances see through `pos`,
    -- not through `nth`)
    change (cons T.X.left
        ((centerS (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj)).map
          (T.E.component (pos T hj)).subschemeι)
        (BlowUpSequence.pushforward
          (Y := (centerS (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj)).blowUp)
          (B.seq (restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj) hI' hmax')
            (hDom _ (hasDimLE_restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj)
              hI' hmax' hn') hRm))
          (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι
            (centerS (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj))))).eraseEmpty =
      BlowUpSequence.pushforward (Y := (T.E.component (pos T hj)).subscheme)
        (B.seq (hypersurfaceTriple T hj J hJ)
          (hDom _ (hasDimLE_hypersurfaceTriple T hj J hJ hn) hHm))
        (T.E.component (pos T hj)).subschemeι
    set Z := centerS (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj) with hZdef
    have hZ : Z = ⊤ := by
      rw [hZdef]
      change (Zminus1 (T.tuned 1 le_rfl).I (tuningParam 1)
        ((T.tuned 1 le_rfl).E.component (pos T hj))).comap _ = ⊤
      rw [show (T.tuned 1 le_rfl).I = T.I from W_tuningParam_one _ _, tuningParam_one,
        show Zminus1 T.I 1 ((T.tuned 1 le_rfl).E.component (pos T hj)) = ⊤ from
          Zminus1_eq_top_of_eq_map T hj J hJ hIJ,
        comap_top]
    have hZmap : Z.map (T.E.component (pos T hj)).subschemeι = ⊤ := by rw [hZ, map_top]
    have hπS : IsIso Z.blowUpπ :=
      isIso_blowUpπ_of_eq_top hZ
    have hπX : IsIso (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ :=
      isIso_blowUpπ_of_eq_top hZmap
    have : Smooth Z.blowUpπ := inferInstance
    have : Smooth (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ :=
        inferInstance
    have : Flat Z.blowUpπ := inferInstance
    have hpb : (restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj) hI'
        hmax').IsPullbackOf (hypersurfaceTriple T hj J hJ)
          Z.blowUpπ := by
      refine ⟨⟨rfl, ?_, ?_⟩, tuningParam_one⟩
      · change ((T.tuned 1 le_rfl).I.comap
          (T.E.component (pos T hj)).subschemeι).markedTransform Z (tuningParam 1) =
          J.comap Z.blowUpπ
        rw [markedTransform_of_eq_top _ _ hZ]
        congr 1
        rw [show (T.tuned 1 le_rfl).I = T.I from W_tuningParam_one _ _, hIJ]
        exact comap_map_of_isClosedImmersion _ J
      · change (((T.tuned 1 le_rfl).E.erase (pos T hj)).comap
            (T.E.component (pos T hj)).subschemeι).totalTransform Z =
          ((((T.E.erase (pos T hj)).comap (T.E.nth ⟨j, hj⟩).subschemeι).append ⊤).comap
            Z.blowUpπ)
        exact totalTransform_of_eq_top _ hZ
    set R := restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1) (pos T hj) hI' hmax' with hRdef
    set H := hypersurfaceTriple T hj J hJ with hHdef
    set hR : Dom R := hDom R (hasDimLE_restrictedTriple (T.tuned 1 le_rfl) (tuningParam 1)
      (pos T hj) hI' hmax' hn') hRm with hRdef'
    set hH : Dom H := hDom H (hasDimLE_hypersurfaceTriple T hj J hJ hn) hHm with hHdef'
    -- `B`'s value on the hypersurface triple, at the canonical type (`H.X.left` is `E^j` only up to
    -- unfolding, which instance search does not do)
    set Q : BlowUpSequence (T.E.component (pos T hj)).subscheme := B.seq H hH with hQdef
    have hQne : Q.NoEmptyCenters := B.noEmptyCenters H hH
    have hcomm : B.seq R hR = Q.pullback Z.blowUpπ :=
      @hB H R Z.blowUpπ
        ‹Smooth Z.blowUpπ›
        (surjective_of_isIso Z.blowUpπ) hpb hH hR
    have hQ : (Q.pullback Z.blowUpπ).eraseEmpty =
        Q.pullback Z.blowUpπ := by
      rw [eraseEmpty_pullback_of_flat_surjective _ _ (surjective_of_isIso _),
        (eraseEmpty_eq_self_iff _).mpr hQne]
    -- the exchange of push-forward and pull-back along the square of the two trivial blow-ups
    have hex : (Q.pushforward (T.E.component (pos T hj)).subschemeι).pullback
          (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ =
        (Q.pullback Z.blowUpπ).pushforward
          (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z) :=
      pullback_pushforward_of_isPullback Q (T.E.component (pos T hj)).subschemeι
        (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ
        (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)
        Z.blowUpπ
        (IsPullback.of_vert_isIso ⟨pushforwardBlowUp_π (T.E.component (pos T hj)).subschemeι Z⟩)
    have hinv : ∀ S : BlowUpSequence T.X.left,
        (S.pullback (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ).pullback
          (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) = S :=
              fun S => by
      rw [← pullback_comp, IsIso.inv_hom_id, pullback_id]
    calc _ = (BlowUpSequence.pushforward (Y := Z.blowUp)
          (B.seq R hR)
            (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)).eraseEmpty.pullback
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) :=
          eraseEmpty_cons_of_eq_top _ hZmap
      _ = (BlowUpSequence.pushforward (Y := Z.blowUp)
          (B.seq R hR).eraseEmpty
            (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)).pullback
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) :=
          congrArg (fun s => BlowUpSequence.pullback s
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ))
            (eraseEmpty_pushforward (Y := Z.blowUp)
              (B.seq R hR) (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z))
      _ = ((Q.pullback Z.blowUpπ).eraseEmpty.pushforward
            (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)).pullback
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) :=
          congrArg (fun s : BlowUpSequence R.X.left =>
            (BlowUpSequence.pushforward (Y := Z.blowUp)
              s.eraseEmpty (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)).pullback
              (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ)) hcomm
      _ = ((Q.pullback Z.blowUpπ).pushforward
            (pushforwardBlowUp (T.E.component (pos T hj)).subschemeι Z)).pullback
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) := by
          rw [hQ]
      _ = ((Q.pushforward (T.E.component (pos T hj)).subschemeι).pullback
            (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ).pullback
            (inv (Z.map (T.E.component (pos T hj)).subschemeι).blowUpπ) := by
          rw [hex]
      _ = Q.pushforward (T.E.component (pos T hj)).subschemeι := hinv _
  · have hl : T.I.maxOrd < ((1 : ℕ) : ℕ∞) := lt_of_le_of_ne hT.2.1 h
    rw [dataFunctor_seq_of_maxOrd_lt n 1 j le_rfl B hDom T hT hl]
    have hItop : T.I = ⊤ := by
      have h0 : T.I.maxOrd = 0 := Order.lt_one_iff.mp (by simpa using hl)
      exact eq_top_of_maxOrd_le_zero T.I (by simp [h0])
    have hJtop : J = ⊤ := by
      have h1 := comap_map_of_isClosedImmersion (T.E.nth ⟨j, hj⟩).subschemeι J
      rw [← hIJ, hItop, comap_top] at h1
      exact h1.symm
    subst hJtop
    have hnil : ∀ hH : Dom (hypersurfaceTriple T hj ⊤ hJ),
        B.seq (hypersurfaceTriple T hj ⊤ hJ) hH = BlowUpSequence.nil _ := fun hH =>
      eq_nil_of_isOrderGeSeq_of_maxOrd_lt _ (B.isOrderGeSeq _ hH) (B.noEmptyCenters _ hH)
        (by
          change (⊤ : (T.E.nth ⟨j, hj⟩).subscheme.IdealSheafData).maxOrd < ((1 : ℕ) : ℕ∞)
          refine lt_of_le_of_lt (b := 0)
            ((maxOrd_le_iff (⊤ : (T.E.nth ⟨j, hj⟩).subscheme.IdealSheafData)).mpr fun x => ?_)
            (by simp)
          exact (Scheme.IdealSheafData.ord_top x).le)
    rw [hnil]
    exact (pushforward_nil _).symm

end Hironaka.BD
