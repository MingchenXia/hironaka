/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.Pushforward
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Balanced.GoingUpChain
import Hironaka.Resolution.Algebraic.Kol07.Corollary89
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.BlowUpSequence.Truncate
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.LiftHypersurface
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The going-up theorem for D-balanced ideals

Kollár's going-up theorem [Kol07, Theorem 84]: for a D-balanced ideal `I` with `max-ord I = m` on
a smooth variety `X` and a smooth hypersurface `S ⊆ X`, the push-forward to `X` of a smooth blow-up
sequence of order `≥ m` for `(S, I|_S, m)` is a smooth blow-up sequence of order `m` for `(X, I)`.
Its proof [Kol07, 90] is by induction on the length: assuming the statement for sequences of
length `< r`, Corollary 89 for the prefix `Π_{r−1}` and the D-balanced property give
`cosupp(J_{r−1}, m) ⊆ cosupp(I_{r−1}, m)`, so the last blow-up also has order `≥ m`.

This module proves the theorem with the boundary `E` of [Kol07, Corollary 85] carried along
(`IsDBalanced.isOrderSeq_pushforward`) and in the printed form at `E = ∅`
(`IsDBalanced.isOrderSeq_pushforward_of_not_subset_cosupp`). The induction is run as a strong
induction on the stage index: the clauses at the stages `< l` make the prefix `B.take l` a sequence
of order `≥ m` (`isOrderGeSeq_take_of_forall_lt`, `Hironaka/Scheme/BlowUpSequence/Truncate.lean`),
to which Corollary 89 applies, and the results are carried from the prefix to stage `l` along the
truncation lemmas. Together with the going-down theorem this gives the one-to-one correspondence of
Corollary 85 between order reduction on `X` and on a hypersurface of maximal contact.

Two groups of auxiliary lemmas are proved on the way:

* Corollary 89 read on the push-forward (`cosupp_markedTransformSeq_pushforward_inter_eq_iInter`).
  `Hironaka/Resolution/Algebraic/Kol07/Corollary89.lean` states Corollary 89 on the restriction
  `Π|_S = B.pullback ι` with the stage lifts `B.pullbackStageHom ι i`; for `B = T.pushforward ι` the
  restriction is `T` itself (`pullback_pushforward`) and the lifts are the stage inclusions
  `T.pushforwardStageHom ι i` (`pullbackStageHom_pushforward_heq_mk`, by induction with the
  transport of `pullbackStageHom` along `eqToHom`-composites), so the two sets of Corollary 89 are
  transported pointwise to the stages of `T`.
* The simple normal crossing lemmas along a sequence (`E_j + H_j` is snc, `E_j|_{H_j} = (E|_H)_j`)
  in prefix form, with the normal crossing hypothesis only at the stages `< j`
  (`isSnc_totalTransformSeq_append_of_forall_lt`,
  `totalTransformSeq_comap_pullbackStageHom_of_forall_lt`), the form the induction uses.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.Hom
  IdealSheafData BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Congruences along an equality of sequences and of morphisms -/

theorem stage_congr {S₁ S₂ : BlowUpSequence X} (e : S₁ = S₂) (n : ℕ) (h₁ : n < S₁.length + 1)
    (h₂ : n < S₂.length + 1) : S₁.stage ⟨n, h₁⟩ = S₂.stage ⟨n, h₂⟩ := by
  subst e
  rfl

theorem markedTransformSeq_congr_heq {S₁ S₂ : BlowUpSequence X} (e : S₁ = S₂)
    (J : X.IdealSheafData) (c n : ℕ) (h₁ : n < S₁.length + 1) (h₂ : n < S₂.length + 1) :
    HEq (S₁.markedTransformSeq J c ⟨n, h₁⟩) (S₂.markedTransformSeq J c ⟨n, h₂⟩) := by
  subst e
  rfl

theorem pullbackStageHom_congr_heq {S₁ S₂ : BlowUpSequence X} (e : S₁ = S₂) (h : Y ⟶ X) (n : ℕ)
    (h₁ : n < S₁.length + 1) (h₂ : n < S₂.length + 1) :
    HEq (S₁.pullbackStageHom h ⟨n, h₁⟩) (S₂.pullbackStageHom h ⟨n, h₂⟩) := by
  subst e
  rfl

/-- The stage lifts of a pullback depend only on the pulled-back morphism. -/
theorem pullbackStageHom_congr_hom (S : BlowUpSequence X) {h h' : Y ⟶ X} (e : h = h')
    (i : Fin (S.length + 1)) : HEq (S.pullbackStageHom h i) (S.pullbackStageHom h' i) := by
  subst e
  rfl

/-- Transport of the stage lifts along an `eqToHom` on the source (the stage-lift form of
`pullback_eqToHom_comp`). -/
theorem pullbackStageHom_eqToHom_comp (S : BlowUpSequence X) {Y' : Scheme.{u}} (e : Y' = Y)
    (h : Y ⟶ X) (i : Fin (S.length + 1)) :
    HEq (S.pullbackStageHom (eqToHom e ≫ h) i) (S.pullbackStageHom h i) := by
  subst e
  exact pullbackStageHom_congr_hom S (by simp) i

/-! ### The embeddings of the pushforward are the stage lifts of its restriction -/

/-- On the push-forward `B = T.pushforward j` along a closed immersion [Kol07, 30.3], the stage
lift `B.pullbackStageHom j n : (B.pullback j)_n ⟶ B_n` of the restriction [Kol07, 30.2] is the
stage inclusion `T.pushforwardStageHom j n : T_n ⟶ B_n`; heterogeneously, as `B.pullback j = T`
holds only propositionally. -/
theorem pullbackStageHom_pushforward_heq_mk (T : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (n : ℕ) (hn : n < (T.pushforward j).length + 1) (hn' : n < T.length + 1) :
    HEq ((T.pushforward j).pullbackStageHom j ⟨n, hn⟩) (T.pushforwardStageHom j ⟨n, hn'⟩) := by
  induction T generalizing X n with
  | nil _ => rfl
  | cons Y Z rest ih =>
    cases n with
    | zero => rfl
    | succ n =>
      -- LHS: `(rest.pushforward ι₁).pullbackStageHom (blowUpMap j (Z.map j)) ⟨n, _⟩`
      -- RHS: `rest.pushforwardStageHom ι₁ ⟨n, _⟩`, with `ι₁ = pushforwardBlowUp j Z`
      have hn₁ : n < (rest.pushforward (pushforwardBlowUp j Z)).length + 1 :=
        Nat.lt_of_succ_lt_succ hn
      have h1 := pullbackStageHom_eqToHom_comp (rest.pushforward (pushforwardBlowUp j Z))
        (congrArg Scheme.IdealSheafData.blowUp (comap_map_of_isClosedImmersion j Z).symm)
        (Scheme.Hom.blowUpMap j (Z.map j)) ⟨n, hn₁⟩
      have h2 := ih (pushforwardBlowUp j Z) n hn₁ (Nat.lt_of_succ_lt_succ hn')
      exact h1.symm.trans h2

/-! ### Corollary 89 on the push-forward -/

section Cor89Pushforward

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (S I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)
  (T : BlowUpSequence S.subscheme)

/-- The centers of a push-forward along `S.subschemeι` lie in the strict transforms of `S`
(`strictTransformSeq_le_center_pushforward` with `ker S.subschemeι = S`). -/
theorem strictTransformSeq_le_center_pushforward_subschemeι
    (i : Fin (T.pushforward S.subschemeι).length) :
    (T.pushforward S.subschemeι).strictTransformSeq S i.castSucc ≤
      (T.pushforward S.subschemeι).center i := by
  obtain ⟨i', rfl⟩ : ∃ i' : Fin T.length, i = T.pushforwardCenterIdx S.subschemeι i' :=
    ⟨Fin.cast (length_pushforward T S.subschemeι) i, Fin.ext rfl⟩
  have := strictTransformSeq_le_center_pushforward T S.subschemeι i'
  rwa [ker_subschemeι] at this

include n in
/-- [Kol07, Corollary 89] for the push-forward `Π = T.pushforward S.subschemeι`, read on the
stages of `T` through the embeddings `T.pushforwardStageHom`, as the first line of [Kol07, 90]
uses it: the restricted sequence `Π|_S` is `T` and its stage lifts are the stage inclusions
(`pullbackStageHom_pushforward_heq_mk`); the two sets of Corollary 89 are transported pointwise
along the equality of stages. -/
theorem cosupp_markedTransformSeq_pushforward_inter_eq_iInter (hS : IsSmoothDivisor S)
    (h : (T.pushforward S.subschemeι).IsOrderGeSeq f I m E) (i : Fin (T.length + 1)) :
    {y : T.stage i | (m : ℕ∞) ≤ ((T.pushforward S.subschemeι).markedTransformSeq I m
        (T.pushforwardStageIdx S.subschemeι i)).ord (T.pushforwardStageHom S.subschemeι i y)} =
      ⋂ j < m, {y | ((m - j : ℕ) : ℕ∞) ≤ (T.markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j) i).ord y} := by
  obtain ⟨n', hn'⟩ := i
  have hnB : n' < (T.pushforward S.subschemeι).length + 1 := by
    rw [length_pushforward]; exact hn'
  have h89 := cosupp_markedTransformSeq_inter_eq_iInter f n (T.pushforward S.subschemeι) S I E m
    hS h (strictTransformSeq_le_center_pushforward_subschemeι S T) ⟨n', hnB⟩
  have e : (T.pushforward S.subschemeι).pullback S.subschemeι = T := pullback_pushforward T _
  have hnP : n' < ((T.pushforward S.subschemeι).pullback S.subschemeι).length + 1 := by
    rw [e]; exact hn'
  have es : ((T.pushforward S.subschemeι).pullback S.subschemeι).stage ⟨n', hnP⟩ =
      T.stage ⟨n', hn'⟩ := stage_congr e n' hnP hn'
  have hφ := pullbackStageHom_pushforward_heq_mk T S.subschemeι n' hnB hn'
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  set y' : ((T.pushforward S.subschemeι).pullback S.subschemeι).stage ⟨n', hnP⟩ :=
    cast (congrArg (fun S : Scheme.{u} => (S : Type u)) es.symm) y with hy'
  have hyy' : cast (congrArg (fun S : Scheme.{u} => (S : Type u)) es) y' = y := by
    rw [hy', cast_cast, cast_eq]
  have h89y := Set.ext_iff.mp h89 y'
  simp only [Set.mem_ofPred_eq, Set.mem_iInter] at h89y
  -- the left side: the embeddings agree
  have hL : (T.pushforward S.subschemeι).pullbackStageHom S.subschemeι ⟨n', hnB⟩ y' =
      T.pushforwardStageHom S.subschemeι ⟨n', hn'⟩ y := by
    have := apply_cast_of_heq es rfl hφ y'
    rw [hyy'] at this
    rw [this]
    rfl
  -- the right side: the marked transforms of the restricted sequence are those of `T`
  have hR : ∀ j, (((T.pushforward S.subschemeι).pullback S.subschemeι).markedTransformSeq
      ((I.derivativeIter f j).comap S.subschemeι) (m - j)
      ((T.pushforward S.subschemeι).pullbackStageIdx S.subschemeι ⟨n', hnB⟩)).ord y' =
      (T.markedTransformSeq ((I.derivativeIter f j).comap S.subschemeι) (m - j) ⟨n', hn'⟩).ord y :=
    fun j => by
      have := ord_cast_of_heq es (markedTransformSeq_congr_heq e ((I.derivativeIter f j).comap
        S.subschemeι) (m - j) n' hnP hn') y'
      rw [hyy'] at this
      exact this.symm
  rw [← hL]
  refine h89y.trans ?_
  exact forall_congr' fun j => forall_congr' fun _ => by rw [hR j]

end Cor89Pushforward

/-! ### More congruences along equalities of schemes and sequences -/

theorem totalTransformSeq_congr_heq {S₁ S₂ : BlowUpSequence X} (e : S₁ = S₂)
    (E : DivisorFamily X) (n : ℕ) (h₁ : n < S₁.length + 1) (h₂ : n < S₂.length + 1) :
    HEq (S₁.totalTransformSeq E ⟨n, h₁⟩) (S₂.totalTransformSeq E ⟨n, h₂⟩) := by
  subst e
  rfl

/-- `comap` of a family along heterogeneously equal morphisms (equal sources). -/
theorem comap_congr_heq {A B Y : Scheme.{u}} (e : A = B) {φ : A ⟶ Y} {φ' : B ⟶ Y} (h : HEq φ φ')
    (F : DivisorFamily Y) : HEq (F.comap φ) (F.comap φ') := by
  subst e
  cases h
  rfl

/-- The maximal order of heterogeneously equal ideal sheaves. -/
theorem maxOrd_of_heq {A B : Scheme.{u}} (e : A = B) {J : A.IdealSheafData} {J' : B.IdealSheafData}
    (h : HEq J J') : J'.maxOrd = J.maxOrd := by
  subst e
  cases h
  rfl

/-! ### Simple normal crossings along a sequence, in prefix form -/

section PrefixSnc

variable {k : Type u} [Field k] [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]

/-- `isSnc_totalTransformSeq_append_mk` with the normal crossing hypothesis only at the stages
`< j`: `E_j + H_j` is snc as soon as the centers before `j` have simple normal crossings with the
`E_i`; the same induction, using one clause per step. -/
theorem isSnc_totalTransformSeq_append_of_forall_lt (S : BlowUpSequence X) (J : X.IdealSheafData)
    (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : (E.append J).IsSnc) (j : ℕ)
    (hsnc : ∀ i : Fin S.length, i.val < j →
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (hj : j < S.length + 1) :
    ((S.totalTransformSeq E ⟨j, hj⟩).append (S.strictTransformSeq J ⟨j, hj⟩)).IsSnc := by
  induction S generalizing j with
  | nil X => exact hE
  | cons X D rest ih =>
    cases j with
    | zero => exact hE
    | succ j =>
      obtain ⟨hD, hsm'⟩ := (isSmooth_cons_iff f D rest).1 hsm
      have hb : (E.append J).HasSncWith D :=
        hasSncWith_append_of_le f hE (hsnc ⟨0, Nat.zero_lt_succ _⟩ (Nat.succ_pos _))
          (hZ ⟨0, Nat.zero_lt_succ _⟩)
      have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
      exact ih (D.blowUpπ ≫ f) (J.strictTransform D) (E.totalTransform D) hsm'
        (isSnc_totalTransform_append_of_hasSncWith f hE hb) j
        (fun ⟨i, hi⟩ hij => hsnc ⟨i + 1, Nat.succ_lt_succ hi⟩ (Nat.succ_lt_succ hij))
        (fun ⟨i, hi⟩ => hZ ⟨i + 1, Nat.succ_lt_succ hi⟩) (Nat.lt_of_succ_lt_succ hj)

/-- `totalTransformSeq_comap_pullbackStageHom_mk` with the normal crossing hypothesis only at the
stages `< j`: `E_j|_{H_j} = (E|_H)_j`; the same induction. -/
theorem totalTransformSeq_comap_pullbackStageHom_of_forall_lt (S : BlowUpSequence X) (g : Y ⟶ X)
    [IsClosedImmersion g] (E : DivisorFamily X) (hsm : S.IsSmooth f) (hE : (E.append g.ker).IsSnc)
    (j : ℕ)
    (hsnc : ∀ i : Fin S.length, i.val < j →
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq g.ker i.castSucc ≤ S.center i)
    (hj : j < S.length + 1) :
    (S.totalTransformSeq E ⟨j, hj⟩).comap (S.pullbackStageHom g ⟨j, hj⟩) =
      (S.pullback g).totalTransformSeq (E.comap g) (S.pullbackStageIdx g ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨hD, hsm'⟩ := (isSmooth_cons_iff f D rest).1 hsm
      have hb : (E.append g.ker).HasSncWith D :=
        hasSncWith_append_of_le f hE (hsnc ⟨0, Nat.zero_lt_succ _⟩ (Nat.succ_pos _))
          (hZ ⟨0, Nat.zero_lt_succ _⟩)
      have hci : IsClosedImmersion (Scheme.Hom.blowUpMap g D) :=
        isClosedImmersion_blowUpMap_of_isClosedImmersion g D
      have hπ : Smooth (D.blowUpπ ≫ f) := smooth_blowUpπ_comp_of_smooth' f D
      have hE' : ((E.totalTransform D).append (Scheme.Hom.blowUpMap g D).ker).IsSnc := by
        rw [ker_blowUpMap_of_isClosedImmersion]
        exact isSnc_totalTransform_append_of_hasSncWith f hE hb
      have hZ' : ∀ i : Fin rest.length,
          rest.strictTransformSeq (Scheme.Hom.blowUpMap g D).ker i.castSucc ≤ rest.center i := by
        rintro ⟨i, hi⟩
        rw [ker_blowUpMap_of_isClosedImmersion]
        exact hZ ⟨i + 1, Nat.succ_lt_succ hi⟩
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap g D) (E.totalTransform D) hsm' hE' j
        (fun ⟨i, hi⟩ hij => hsnc ⟨i + 1, Nat.succ_lt_succ hi⟩ (Nat.succ_lt_succ hij)) hZ'
        (Nat.lt_of_succ_lt_succ hj)
      rw [← totalTransform_comap_blowUpMap_of_hasSncWith f g hb (hZ ⟨0, Nat.zero_lt_succ _⟩)]
        at this
      exact this

end PrefixSnc

/-! ### The induction of Kollár's item 90, and Theorem 84 as printed -/

section Engine

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (S I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)
  (T : BlowUpSequence S.subscheme)

include n in
/-- **The going-up theorem** [Kol07, Theorem 84] with the boundary `E` of [Kol07, Corollary 85]
carried along: for a D-balanced `I` with `max-ord I = m`, a smooth hypersurface `S` with `E + S`
snc, and a smooth blow-up sequence `T` of order `≥ m` for `(S, I|_S, m, E|_S)`, the push-forward
`B = T.pushforward ι` is a smooth blow-up sequence of order `m` for `(X, I, E)`.

The proof is the induction of [Kol07, 90]. `B` is smooth (`IsSmooth.pushforward`); its normal
crossing and order clauses are proved at every stage `l` by strong induction on `l`, the clauses at
the stages `< l` making the prefix `B.take l` a sequence of order `≥ m`
(`isOrderGeSeq_take_of_forall_lt`). At stage `l`, with the stage inclusion `g = j_l : S_l ↪ X_l`:
the order clause follows from `max-ord I_l ≤ m` (Lemma 61 iterated along the prefix) and
`cosupp(J_l, m) ⊆ j_l^{-1} cosupp(I_l, m)`, the latter from Corollary 89 on the prefix `T.take l`
(whose push-forward is `B.take l`) and the D-balanced property
(`cosupp_markedTransformSeq_subset_iInter`), carried to stage `l` of `T` and `B` along the
truncation lemmas; the normal crossing clause lifts the simple normal crossings of `Z_l` with
`(E|_S)_l` in `S_l` to `E_l` in `X_l`, using `E_l + S_l` snc and `E_l|_{S_l} = (E|_S)_l` from the
prefix forms of the snc lemmas. Finally Remark 67 (`max-ord I = m`) turns order `≥ m` into
order `m`. -/
theorem IsDBalanced.isOrderSeq_pushforward (hI : I.IsDBalanced f m) (hmax : I.maxOrd = m)
    (hS : IsSmoothDivisor S) (hE : (E.append S).IsSnc)
    (hT : T.IsOrderGeSeq (S.subschemeι ≫ f) (I.comap S.subschemeι) m (E.comap S.subschemeι)) :
    (T.pushforward S.subschemeι).IsOrderSeq f I E m := by
  have hsf : Smooth f := SmoothOfRelativeDimension.smooth n f
  set ι := S.subschemeι with hιdef
  set B := T.pushforward ι with hBdef
  have hsmB : B.IsSmooth f := IsSmooth.pushforward f ι hT.1
  have hZS : ∀ i : Fin B.length, B.strictTransformSeq S i.castSucc ≤ B.center i :=
    strictTransformSeq_le_center_pushforward_subschemeι S T
  have hker : ι.ker = S := ker_subschemeι S
  have hlen : B.length = T.length := length_pushforward T ι
  -- the clauses, by strong induction on the stage index
  have key : ∀ l : ℕ, ∀ i : Fin B.length, i.val < l →
      (B.totalTransformSeq E i.castSucc).HasSncWith (B.center i) ∧
        (B.markedTransformSeq I m i.castSucc).LeOrdAlong (B.center i).support (m : ℕ∞) := by
    intro l
    induction l with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ l ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | hil
      · exact ih i hlt
      -- the step: `i = l`
      obtain ⟨l', hlB⟩ := i
      simp only at hil
      subst hil
      have hlT : l' < T.length := hlen ▸ hlB
      have hlB1 : l' < B.length + 1 := Nat.lt_succ_of_lt hlB
      have hlT1 : l' < T.length + 1 := Nat.lt_succ_of_lt hlT
      have hsncP : ∀ i' : Fin B.length, i'.val < l' →
          (B.totalTransformSeq E i'.castSucc).HasSncWith (B.center i') := fun i' hi' => (ih i'
            hi').1
      have hP : (B.take l').IsOrderGeSeq f I m E :=
        isOrderGeSeq_take_of_forall_lt f I m E B hsmB l' ih
      -- the stage inclusion `g = j_l`
      set g := T.pushforwardStageHom ι ⟨l', hlT1⟩ with hgdef
      have hgci : IsClosedImmersion g := isClosedImmersion_pushforwardStageHom T ι ⟨l', hlT1⟩
      have hgker : g.ker = B.strictTransformSeq S ⟨l', hlB1⟩ := by
        have := ker_pushforwardStageHom_mk T ι l' hlT1
        rw [hker] at this
        exact this
      have hcenter : B.center ⟨l', hlB⟩ = (T.center ⟨l', hlT⟩).map g :=
        center_pushforward_mk T ι l' hlT
      have hregl : ∀ x : B.stage ⟨l', hlB1⟩,
          IsRegularLocalRing ((B.stage ⟨l', hlB1⟩).presheaf.stalk x) := fun x => by
        have := IsSmooth.smooth_stageMap' hsmB ⟨l', hlB1⟩
        exact isRegularLocalRing_stalk (B.stageMap ⟨l', hlB1⟩ ≫ f) x
      -- (i) `E_l + S_l` snc, from the prefix clauses
      have hEl : ((B.totalTransformSeq E ⟨l', hlB1⟩).append
          (B.strictTransformSeq S ⟨l', hlB1⟩)).IsSnc :=
        isSnc_totalTransformSeq_append_of_forall_lt f B S E hsmB hE l' hsncP hZS hlB1
      -- (ii) `E_l|_{S_l} = (E|_S)_l`, from the prefix clauses, transported to `g` and `T`
      have e : B.pullback ι = T := pullback_pushforward T ι
      have hnP : l' < (B.pullback ι).length + 1 := by rw [e]; exact hlT1
      have es : (B.pullback ι).stage ⟨l', hnP⟩ = T.stage ⟨l', hlT1⟩ := stage_congr e l' hnP hlT1
      have hφ : HEq (B.pullbackStageHom ι ⟨l', hlB1⟩) g :=
        pullbackStageHom_pushforward_heq_mk T ι l' hlB1 hlT1
      have hres := totalTransformSeq_comap_pullbackStageHom_of_forall_lt f B ι E hsmB
        (by rw [hker]; exact hE) l' hsncP (by rw [hker]; exact hZS) hlB1
      have hres' : (B.totalTransformSeq E ⟨l', hlB1⟩).comap g =
          T.totalTransformSeq (E.comap ι) ⟨l', hlT1⟩ := by
        have h1 := comap_congr_heq es hφ (B.totalTransformSeq E ⟨l', hlB1⟩)
        have h2 := totalTransformSeq_congr_heq e (E.comap ι) l' hnP hlT1
        exact eq_of_heq (h1.symm.trans ((heq_of_eq hres).trans h2))
      -- (iii) the normal crossing clause: lift `Z_l`'s snc with `(E|_S)_l` to `E_l`
      have hsnc_l : (B.totalTransformSeq E ⟨l', hlB1⟩).HasSncWith (B.center ⟨l', hlB⟩) := by
        have hEl' : ((B.totalTransformSeq E ⟨l', hlB1⟩).append g.ker).IsSnc := by
          rw [hgker]; exact hEl
        have hle : g.ker ≤ B.center ⟨l', hlB⟩ := by rw [hgker]; exact hZS ⟨l', hlB⟩
        have hZ' : ((B.totalTransformSeq E ⟨l', hlB1⟩).comap g).HasSncWith
            ((B.center ⟨l', hlB⟩).comap g) := by
          rw [hres', hcenter, comap_map_of_isClosedImmersion]
          exact (hT.2 ⟨l', hlT⟩).1
        exact HasSncWith.of_append
          (hasSncWith_append_of_comap_of_isClosedImmersion g hregl hEl' hle hZ')
      -- (iv) the order clause, from `max-ord I_l ≤ m` and
      -- `cosupp(J_l, m) ⊆ j_l⁻¹ cosupp(I_l, m)`
      have hlP1 : l' < (B.take l').length + 1 := by
        rw [length_take_of_le B hlB.le]; exact Nat.lt_succ_self l'
      have hmaxl : (B.markedTransformSeq I m ⟨l', hlB1⟩).maxOrd ≤ m := by
        rw [maxOrd_of_heq (stage_take_mk B l' l' hlP1 hlB1)
          (markedTransformSeq_take_heq_mk B I m l' l' hlP1 hlB1)]
        exact maxOrd_markedTransformSeq_le f n hmax.le hP ⟨l', hlP1⟩
      have hsub : ∀ y : T.stage ⟨l', hlT1⟩,
          (m : ℕ∞) ≤ (T.markedTransformSeq (I.comap ι) m ⟨l', hlT1⟩).ord y →
            (m : ℕ∞) ≤ (B.markedTransformSeq I m ⟨l', hlB1⟩).ord (g y) := by
        intro y hy
        set T' := T.take l' with hT'def
        have hlT'1 : l' < T'.length + 1 := by
          rw [hT'def, length_take_of_le T hlT.le]; exact Nat.lt_succ_self l'
        have hT' : T'.IsOrderGeSeq (ι ≫ f) (I.comap ι) m (E.comap ι) :=
          isOrderGeSeq_take (ι ≫ f) (I.comap ι) m (E.comap ι) hT l'
        have eP : T'.pushforward ι = B.take l' := by rw [hT'def, pushforward_take]
        have hPT : (T'.pushforward ι).IsOrderGeSeq f I m E := by rw [eP]; exact hP
        have esT : T'.stage ⟨l', hlT'1⟩ = T.stage ⟨l', hlT1⟩ := stage_take_mk T l' l' hlT'1 hlT1
        set y' : T'.stage ⟨l', hlT'1⟩ :=
          cast (congrArg (fun S : Scheme.{u} => (S : Type u)) esT.symm) y with hy'
        have hyy' : cast (congrArg (fun S : Scheme.{u} => (S : Type u)) esT) y' = y := by
          rw [hy', cast_cast, cast_eq]
        have hy'' : (m : ℕ∞) ≤ (T'.markedTransformSeq (I.comap ι) m ⟨l', hlT'1⟩).ord y' := by
          have := ord_cast_of_heq esT
            (markedTransformSeq_take_heq_mk T (I.comap ι) m l' l' hlT'1 hlT1) y'
          rw [hyy'] at this
          rwa [this] at hy
        have hg := cosupp_markedTransformSeq_subset_iInter f n S I m T' hI hS hT' ⟨l', hlT'1⟩ hy''
        have hc := cosupp_markedTransformSeq_pushforward_inter_eq_iInter f n S I E m T' hS hPT
          ⟨l', hlT'1⟩
        have hmem : y' ∈ {y : T'.stage ⟨l', hlT'1⟩ | (m : ℕ∞) ≤
            ((T'.pushforward ι).markedTransformSeq I m (T'.pushforwardStageIdx ι ⟨l', hlT'1⟩)).ord
              (T'.pushforwardStageHom ι ⟨l', hlT'1⟩ y)} := by
          rw [hc]; exact hg
        simp only [Set.mem_ofPred_eq] at hmem
        have hlP1' : l' < (T'.pushforward ι).length + 1 := by rw [eP]; exact hlP1
        have eS1 : (T'.pushforward ι).stage ⟨l', hlP1'⟩ = (B.take l').stage ⟨l', hlP1⟩ :=
          stage_congr eP l' hlP1' hlP1
        have eS2 : (B.take l').stage ⟨l', hlP1⟩ = B.stage ⟨l', hlB1⟩ := stage_take_mk B l' l' hlP1
          hlB1
        have hmt : HEq ((T'.pushforward ι).markedTransformSeq I m ⟨l', hlP1'⟩)
            (B.markedTransformSeq I m ⟨l', hlB1⟩) :=
          (markedTransformSeq_congr_heq eP I m l' hlP1' hlP1).trans
            (markedTransformSeq_take_heq_mk B I m l' l' hlP1 hlB1)
        have hφ' : HEq (T'.pushforwardStageHom ι ⟨l', hlT'1⟩) g :=
          pushforwardStageHom_take_heq_mk T ι l' l' hlT'1 hlT1
        have hpt := apply_cast_of_heq esT (eS1.trans eS2) hφ' y'
        rw [hyy'] at hpt
        rw [hpt, ord_cast_of_heq (eS1.trans eS2) hmt]
        exact hmem
      have hord_l : (B.markedTransformSeq I m ⟨l', hlB1⟩).LeOrdAlong
          (B.center ⟨l', hlB⟩).support (m : ℕ∞) := by
        have := ordAlongEq_map_of_cosupp_subset g (B.markedTransformSeq I m ⟨l', hlB1⟩)
          (T.markedTransformSeq (I.comap ι) m ⟨l', hlT1⟩) (T.center ⟨l', hlT⟩) hmaxl
          (hT.2 ⟨l', hlT⟩).2 hsub
        rw [← hcenter] at this
        exact fun η hη => (this η hη).ge
      exact ⟨hsnc_l, hord_l⟩
  have hB : B.IsOrderGeSeq f I m E := ⟨hsmB, fun i => key (i.val + 1) i (Nat.lt_succ_self _)⟩
  exact (isOrderGeSeq_iff_isOrderSeq f n hmax).mp hB

include n in
/-- **Kollár's Theorem 84** [Kol07, Theorem 84] as printed: the going-up theorem at `E = ∅`
(`E + S = S` alone is snc for a smooth hypersurface, `isSnc_append_empty_of_isSmoothDivisor`;
`∅|_S = ∅`, `empty_comap`). The hypothesis `_hSc`, that `S` is not contained in
`cosupp(I, m)`, is part of Kollár's statement of Theorem 84 and is kept so that the theorem reads
as printed; the proof does not need it, because it goes through
`IsDBalanced.isOrderSeq_pushforward`, whose Corollary 89 rests on the sheaf-level form of
Lemma 62, which holds with no nonvanishing hypothesis on the restriction `I|_S`. -/
theorem IsDBalanced.isOrderSeq_pushforward_of_not_subset_cosupp (hI : I.IsDBalanced f m)
    (hmax : I.maxOrd = m) (hS : IsSmoothDivisor S)
    (_hSc : ¬ ((S.support : Set X) ⊆ {x | (m : ℕ∞) ≤ I.ord x}))
    (hT : T.IsOrderGeSeq (S.subschemeι ≫ f) (I.comap S.subschemeι) m
      (DivisorFamily.empty S.subscheme)) :
    (T.pushforward S.subschemeι).IsOrderSeq f I (DivisorFamily.empty X) m := by
  have hsf : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine IsDBalanced.isOrderSeq_pushforward f n S I (DivisorFamily.empty X) m T hI hmax hS
    (isSnc_append_empty_of_isSmoothDivisor
      (fun x => isRegularLocalRing_stalk f x) hS) ?_
  rw [empty_comap]
  exact hT

end Engine

end Hironaka.Sequence
