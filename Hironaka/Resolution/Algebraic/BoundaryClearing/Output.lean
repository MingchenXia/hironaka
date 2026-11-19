/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Restriction
public import Hironaka.Scheme.BlowUpSequence.Functor
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.Kol07.RefineIrreducible
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.Snc.LiftHypersurface
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The full family, the functor `BD_{n,m,j}` and clause (1)

The proof of [Kol07, Lemma 102], continued: since `S = E^j`, every blow-up center is a smooth
subvariety of the birational transform of `E^j`, so the sequence is of order `m` for the FULL
boundary `E`, not only for `E − E^j`; the functor is
`BD_{n,m,j}(X, I, E) := τ_* BMO_{n−1,m}(S, I_0|_S, m, E_S) ∘ π_{-1}`; and by [Kol07, Corollary 85]
the output `Π_r : X_r → X` has `Π_r^{-1}_*(E^j)` disjoint from `cosupp(I_r, m)`.

**The full family.** Along a smooth blow-up sequence of order `m` starting with `(X, I, E − E^j)`
whose centers lie in the birational transforms of `E^j`, every center has simple normal crossings
with the total transform of the FULL `E` (`IsOrderSeq.hasSncWith_totalTransformSeq_of_isEraseOf`):
by induction along the sequence, carrying the relation that the total transform of `E − E^j` is
the total transform of `E` with the birational transform of `E^j` deleted
(`IsEraseOf.isEraseOf_totalTransform`, `Hironaka/Scheme/Snc/EraseFamily.lean`), the one-step content
being `IsEraseOf.hasSncWith_of_le`: some of the `E^i` are allowed to contain the center
([Kol07, Definition 24, (4)]). Hence the output `rawSeq` is a smooth blow-up sequence of order `m`
starting with `(X, I, E)` (`isOrderSeq_rawSeq`). Kollár states this in one sentence; the induction
is not in the sources.

**The functor.** `BD.functor n m j B hDom` is `rawSeq` with its empty blow-ups deleted
([Kol07, 32]; `OrderSeqAssignment.ofEraseEmpty`, `Hironaka/Scheme/BlowUpSequence/Functor.lean`; the
order condition survives deletion, `IsOrderSeq.eraseEmpty`), a smooth blow-up sequence functor of
order `m` on Lemma 102's standing class `Domain n m j`; `exists_functor` is the same in existential
form.

**Clause (1).** [Kol07, Corollary 89] for the pushed-forward sequence
(`cosupp_markedTransformSeq_pushforward_inter_eq_iInter`,
`Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`, the `j = 0` term of the intersection): a point
of the birational transform of `E^j` at the last stage where the marked transform of `I` has order
`≥ m` is a point where the marked transform of `I|_S` along the composite sequence on `S`, the final
marked ideal of `B` on the restricted marked triple, has order `≥ m`; clause (1) of [Kol07, Theorem
69] for `B` says that ideal has `max-ord < m`. Marked and weak transforms of `I` agree along the
sequence ([Kol07, Remark 67]), and the points of the birational transform of `E^j` are the image of
the last stage inclusion (`ker_pushforwardStageHom`,
`Hironaka/Scheme/BlowUpSequence/Pushforward.lean`).

Used by `FunctorialityPullback.lean` and `Assembly.lean`, and outside this directory by
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP1Step21.lean` and `HironakaExamples/Dimension1.lean`
(`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP1Step22Core.lean` imports it without using it).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme
  IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence DivisorFamily

namespace Hironaka.BD

variable {k : Type u} [Field k]

section Bridge

variable [CharZero k]

/-- Along a smooth blow-up sequence of order `m` starting with `(X, I, F)`, where `F` is `E` with
`E^j` deleted, whose centers lie in the birational transforms of `E^j`, every center has simple
normal crossings with the total transform of `E` ([Kol07, Definition 24, (4)]; the proof of
[Kol07, Lemma 102]): by induction along the sequence, at the first step
`IsEraseOf.hasSncWith_of_le`; the total transform of `F` is the total transform of `E` with the
birational transform of `E^j` deleted (`IsEraseOf.isEraseOf_totalTransform`), which is snc
(`AlgebraicGeometry.totalTransform_isSnc`). -/
theorem IsOrderSeq.hasSncWith_totalTransformSeq_of_isEraseOf {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {B : BlowUpSequence X}
    {I : X.IdealSheafData} {F E : DivisorFamily X} {σ : F.ι → E.ι} {j : E.ι} {m : ℕ}
    (hrel : IsEraseOf F E σ j) (hE : E.IsSnc) (hB : B.IsOrderSeq f I F m)
    (hZ : ∀ i : Fin B.length, B.strictTransformSeq (E.component j) i.castSucc ≤ B.center i)
    (i : Fin B.length) : (B.totalTransformSeq E i.castSucc).HasSncWith (B.center i) := by
  induction B with
  | nil Y => exact i.elim0
  | cons Y D rest ih =>
    obtain ⟨⟨hD, hsnc, -⟩, ht⟩ := (isOrderSeq_cons_iff f I F m D rest).1 hB
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hED : E.HasSncWith D := hrel.hasSncWith_of_le f hE (hZ ⟨0, Nat.succ_pos _⟩) hsnc
    rcases i with ⟨_ | i, hi⟩
    · exact hED
    · have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
        have := hD
        exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      exact ih (D.blowUpπ ≫ f) (hrel.isEraseOf_totalTransform D)
        (totalTransform_isSnc f E D hE hED) ht
        (fun i' => hZ ⟨i'.val + 1, Nat.succ_lt_succ i'.isLt⟩) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end Bridge

section EraseEmptyBridge

variable [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- Deleting an empty first blow-up whose tail has no empty blow-ups ([Kol07, 32]) carries the tail
back along the inverse of the isomorphism `blowUpπ X ⊤` (`eraseEmpty_cons_top`); the final weak
transform and the final strict transform of the result are the pull-backs of the tail's along the
last stage isomorphism (`IsOrderSeq.weakTransformSeq_pullback`, `strictTransformSeq_pullback`), so
a disjointness of the final cosupport from a final strict transform transfers. -/
theorem disjoint_eraseEmpty_cons_of_eq_top {D : X.IdealSheafData}
    (rest : BlowUpSequence D.blowUp) (hD : D = ⊤) {I J : X.IdealSheafData}
    {E : DivisorFamily X} {m : ℕ} (hS : (cons X D rest).IsOrderSeq f I E m)
    (hrest : rest.NoEmptyCenters)
    (h : Disjoint {x | (m : ℕ∞) ≤ ((cons X D rest).weakTransformSeq I (Fin.last _)).ord x}
      (((cons X D rest).strictTransformSeq J (Fin.last _)).support : Set _)) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((cons X D rest).eraseEmpty.weakTransformSeq I (Fin.last _)).ord x}
      (((cons X D rest).eraseEmpty.strictTransformSeq J (Fin.last _)).support : Set _) := by
  subst hD
  rw [eraseEmpty_cons_top, (eraseEmpty_eq_self_iff rest).mpr hrest]
  obtain ⟨⟨hD, -, -⟩, ht⟩ := (isOrderSeq_cons_iff f I E m ⊤ rest).1 hS
  rw [weakTransform_top_left] at ht
  have hπ : SmoothOfRelativeDimension n ((⊤ : X.IdealSheafData).blowUpπ ≫ f) := by
    have := hD
    exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n ⊤
  have hπiso : IsIso (⊤ : X.IdealSheafData).blowUpπ :=
    blowUp.isIso_π_of_isInvertible _ Scheme.IdealSheafData.isInvertible_top
  set e : X ⟶ (⊤ : X.IdealSheafData).blowUp := inv (⊤ : X.IdealSheafData).blowUpπ with hedef
  have he : IsIso e := inferInstanceAs (IsIso (inv (⊤ : X.IdealSheafData).blowUpπ))
  have he0 : SmoothOfRelativeDimension 0 e := inferInstance
  have hef : Flat e := inferInstance
  have hI' : (I.comap (⊤ : X.IdealSheafData).blowUpπ).comap e = I := by
    rw [← Scheme.IdealSheafData.comap_comp, hedef, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have hJ' : (J.comap (⊤ : X.IdealSheafData).blowUpπ).comap e = J := by
    rw [← Scheme.IdealSheafData.comap_comp, hedef, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have hw := IsOrderSeq.weakTransformSeq_pullback ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n e (d :=
      0) ht
      (Fin.last _)
  have hs := strictTransformSeq_pullback rest e (J.comap
      (⊤ : X.IdealSheafData).blowUpπ) (Fin.last _)
  rw [hI'] at hw
  rw [hJ'] at hs
  rw [← pullbackStageIdx_last rest e, hw, hs, Set.disjoint_left]
  intro x hx hxJ
  have hiso : IsIso (rest.pullbackStageHom e (Fin.last _)) :=
    isIso_pullbackStageHom_of_isIso rest e _
  change (m : ℕ∞) ≤ _ at hx
  rw [ord_comap_of_isIso] at hx
  rw [SetLike.mem_coe, mem_support_comap_iff_apply] at hxJ
  have hx' : rest.pullbackStageHom e (Fin.last _) x ∈
      {x | (m : ℕ∞) ≤ ((cons X ⊤ rest).weakTransformSeq I (Fin.last _)).ord x} := by
    change (m : ℕ∞) ≤ (rest.weakTransformSeq (I.weakTransform ⊤) (Fin.last _)).ord _
    rw [weakTransform_top_left]
    exact hx
  have hxJ' : rest.pullbackStageHom e (Fin.last _) x ∈
      ((cons X ⊤ rest).strictTransformSeq J (Fin.last _)).support := by
    change _ ∈ (rest.strictTransformSeq (J.strictTransform ⊤) (Fin.last _)).support
    rw [strictTransform_top_left]
    exact hxJ
  exact Set.disjoint_left.mp h hx' hxJ'

end EraseEmptyBridge

section Output

variable [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
  (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)
  {n : ℕ} (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')

/-- The output is a smooth blow-up sequence of order `m` starting with `(X, I, E)` (Kollár: "we in
fact get a blow-up sequence of order `m`" for the full boundary, the proof of [Kol07, Lemma 102]):
the order-`m` sequence for `(X, I, E − E^j)` (`isOrderSeq_rawSeq_erase`), whose centers lie in the
birational transforms of `E^j` (`strictTransformSeq_le_center_rawSeq`), through
`IsOrderSeq.hasSncWith_totalTransformSeq_of_isEraseOf`. -/
theorem isOrderSeq_rawSeq :
    (rawSeq T m j hI hmax hn B hDom).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m := by
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have h := isOrderSeq_rawSeq_erase T m j hI hmax hn B hDom
  refine ⟨h.1, fun i => ⟨?_, (h.2 i).2⟩⟩
  exact IsOrderSeq.hasSncWith_totalTransformSeq_of_isEraseOf (T.X.left ↘ Spec (.of k)) n₀
    (isEraseOf_erase T.E j) T.isSnc h
    (strictTransformSeq_le_center_rawSeq T m j hI hmax hn B hDom) i

/-- If `B` satisfies clause (1) of [Kol07, Theorem 69], the final cosupport `cosupp(I_r, m)` of the
output is disjoint from the birational transform `(Π_r)^{-1}_* E^j` (clause (1) of
[Kol07, Lemma 102]; [Kol07, Corollary 89] for the push-forward; [Kol07, Remark 67]): a point of that
birational transform is the image of a point `y` of the last stage of the composite sequence on `S`
(`ker_pushforwardStageHom`); by the `j = 0` term of Corollary 89, `ord I_r ≥ m` there forces
`ord ≥ m` for the final marked ideal of `B` on the restricted marked triple at `y`, which has
`max-ord < m`. -/
theorem disjoint_cosupp_rawSeq
    (hB : ∀ (T' : MarkedTriple k) (hT' : Dom T'), (B.endTriple T' hT').I.maxOrd < (T'.m : ℕ∞)) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((rawSeq T m j hI hmax hn B hDom).weakTransformSeq T.I (Fin.last _)).ord x}
      (((rawSeq T m j hI hmax hn B hDom).strictTransformSeq (T.E.component j)
        (Fin.last _)).support : Set _) := by
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  set f := T.X.left ↘ Spec (.of k) with hfdef
  set S := T.E.component j with hSdef
  set R := restrictedTriple T m j hI hmax with hRdef
  set hR : Dom R := hDom _ (hasDimLE_restrictedTriple T m j hI hmax hn) rfl with hRdef'
  let TS : BlowUpSequence S.subscheme := cons S.subscheme (centerS T m j) (B.seq R hR)
  have hord : (TS.pushforward S.subschemeι).IsOrderSeq f T.I (T.E.erase j) m :=
    isOrderSeq_rawSeq_erase T m j hI hmax hn B hDom
  have hge : (TS.pushforward S.subschemeι).IsOrderGeSeq f T.I m (T.E.erase j) :=
    (isOrderGeSeq_iff_isOrderSeq f n₀ hmax).mpr hord
  have hid := cosupp_markedTransformSeq_pushforward_inter_eq_iInter f n₀ S T.I (T.E.erase j) m TS
    (isSmoothDivisor_component T j) hge (Fin.last _)
  have hlt : (B.endTriple R hR).I.maxOrd < (m : ℕ∞) := hB R hR
  have hidx : TS.pushforwardStageIdx S.subschemeι (Fin.last _) =
      Fin.last (TS.pushforward S.subschemeι).length :=
    Fin.ext (by simp [length_pushforward])
  have hci := isClosedImmersion_pushforwardStageHom TS S.subschemeι (Fin.last _)
  change Disjoint
    {x | (m : ℕ∞) ≤ ((TS.pushforward S.subschemeι).weakTransformSeq T.I (Fin.last _)).ord x}
    (((TS.pushforward S.subschemeι).strictTransformSeq S (Fin.last _)).support : Set _)
  rw [← hidx, Set.disjoint_left]
  intro x hx hxS
  -- `x` is the image of a point `y` of the last stage of the composite sequence on `S`
  have hker := ker_pushforwardStageHom TS S.subschemeι (Fin.last _)
  rw [Scheme.IdealSheafData.ker_subschemeι] at hker
  have hxS' : x ∈ (TS.pushforwardStageHom S.subschemeι (Fin.last _)).ker.support := by
    rw [hker]; exact hxS
  obtain ⟨y, rfl⟩ := exists_eq_of_mem_support_ker _ hxS'
  -- Corollary 89's `j = 0` term at `y`
  have hy : y ∈ {y : TS.stage (Fin.last _) | (m : ℕ∞) ≤
      ((TS.pushforward S.subschemeι).markedTransformSeq T.I m
        (TS.pushforwardStageIdx S.subschemeι (Fin.last _))).ord
          (TS.pushforwardStageHom S.subschemeι (Fin.last _) y)} := by
    change (m : ℕ∞) ≤ _
    rw [IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n₀ hord]
    exact hx
  rw [hid] at hy
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    exact absurd hlt (by simp)
  have h0 := Set.mem_iInter₂.mp hy 0 hm0
  -- the final marked ideal of the composite on `S` is the final marked ideal of `B` on `R`
  change ((m - 0 : ℕ) : ℕ∞) ≤ ((B.endTriple R hR).I).ord y at h0
  rw [Nat.sub_zero] at h0
  exact absurd (h0.trans (le_maxOrd _ y)) (not_le.mpr hlt)

/-- Clause (1) of [Kol07, Lemma 102] for the output with its empty blow-ups deleted ([Kol07, 32]),
the form `BDData.disjoint_cosupp` takes. Only `π_{-1}` can be empty (`center_rawSeq_ne_top_of_pos`):
if its center is nonempty nothing is deleted (`eraseEmpty_eq_self_iff`); if it is empty,
`disjoint_eraseEmpty_cons_of_eq_top` transports `disjoint_cosupp_rawSeq` along the isomorphism
carrying the tail back to `X`. -/
theorem disjoint_cosupp_eraseEmpty_rawSeq
    (hB : ∀ (T' : MarkedTriple k) (hT' : Dom T'), (B.endTriple T' hT').I.maxOrd < (T'.m : ℕ∞)) :
    Disjoint
      {x | (m : ℕ∞) ≤ ((rawSeq T m j hI hmax hn B hDom).eraseEmpty.weakTransformSeq T.I
        (Fin.last _)).ord x}
      (((rawSeq T m j hI hmax hn B hDom).eraseEmpty.strictTransformSeq (T.E.component j)
        (Fin.last _)).support : Set _) := by
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have hraw := disjoint_cosupp_rawSeq T m j hI hmax hn B hDom hB
  have hord := isOrderSeq_rawSeq_erase T m j hI hmax hn B hDom
  have htail : (tailSeq T m j hI hmax hn B hDom).NoEmptyCenters := fun i hi =>
    center_rawSeq_ne_top_of_pos T m j hI hmax hn B hDom
      ⟨i.val + 1, show i.val + 1 < (rawSeq T m j hI hmax hn B hDom).length from
        Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _) hi
  by_cases hZ : (centerS T m j).map (T.E.component j).subschemeι = ⊤
  · rw [rawSeq_eq] at hraw hord ⊢
    exact disjoint_eraseEmpty_cons_of_eq_top (T.X.left ↘ Spec (.of k)) n₀ _ hZ hord htail hraw
  · have hne : (rawSeq T m j hI hmax hn B hDom).NoEmptyCenters := fun i => by
      rcases i with ⟨_ | i, hi⟩
      · exact hZ
      · exact center_rawSeq_ne_top_of_pos T m j hI hmax hn B hDom ⟨i + 1, hi⟩ (Nat.succ_pos i)
    rw [(eraseEmpty_eq_self_iff _).mpr hne]
    exact hraw

end Output

section Functor

variable [CharZero k] (n m j : ℕ) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
  (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')

/-- **The boundary-clearing functor `BD_{n,m,j}`** on the standing class `Domain n m j` of
[Kol07, Lemma 102] (`I` D-balanced with `max-ord I = m`, `dim X ≤ n`), for a marked functor `B` of
the shape of [Kol07, Theorem 69] in dimensions `≤ n − 1` and mark `m` (the inductive hypothesis
`BMO_{n−1,m}`): the output `rawSeq` for the `j`-th member of `E` (positions as in
`DivisorFamily.nth`) with its empty blow-ups deleted ([Kol07, 32]), a smooth blow-up sequence
functor of order `m`
(`isOrderSeq_rawSeq`, `IsOrderSeq.eraseEmpty`). The extension to `BDClass n m j` by tuning is
`Assembly.lean`. -/
noncomputable def functor : OrderSeqAssignment k m (Domain n m j) :=
  OrderSeqAssignment.ofEraseEmpty
    (fun T hT => rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B hDom)
    (fun T hT => by
      obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
      exact IsOrderSeq.eraseEmpty (T.X.left ↘ Spec (.of k)) n₀
        (isOrderSeq_rawSeq T m _ hT.2.1 hT.2.2.1 hT.1 B hDom))

/-- The value of `BD_{n,m,j}` is the output with its empty blow-ups deleted. -/
theorem functor_seq (T : Triple k) (hT : Domain n m j T) :
    (functor n m j B hDom).seq T hT =
      (rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
        hDom).eraseEmpty :=
  rfl

/-- There is a smooth blow-up sequence functor of order `m` on `Domain n m j` whose value is the
output with its empty blow-ups deleted: `BD.functor`, in existential form. -/
theorem exists_functor :
    ∃ F : OrderSeqAssignment k m (Domain n m j), ∀ (T : Triple k) (hT : Domain n m j T),
      F.seq T hT = (rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
        hDom).eraseEmpty :=
  ⟨functor n m j B hDom, fun _ _ => rfl⟩

end Functor

end Hironaka.BD
