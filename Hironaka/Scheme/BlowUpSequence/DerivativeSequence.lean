/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 76 and Corollary 77 along a smooth blow-up sequence

[Kol07, Theorem 76 and Corollary 77] for a smooth blow-up sequence `S` of order `≥ m` starting
with `(X, I, m, E)` and `j ≤ m`: with `J_0 = D^j(I)` and `J_{i+1} = (π_i)_*^{-1}(J_i, m − j)` (the
marked recursion started at the derivative ideal, `S.markedTransformSeq (I.derivativeIter f j)
(m - j)`) one has `J_i ⊆ D^j(I_i)` at every stage, every `(π_i)_*^{-1}(J_i, m − j)` is defined
(`F_{i+1}^{m−j} ∣ π_i^* J_i`), and `S` is a smooth blow-up sequence of order `≥ m − j` starting
with `(X, D^j(I), m − j, E)`.

**The joint induction.** Kollár deduces Corollary 77 from Theorem 76, but the transform along the
sequence in Theorem 76 is only defined once the order inequality of Corollary 77 is known at each
stage; the two are therefore proved together, as in [Wlo05, Lemma 2.6.4]. Theorem 76's inclusion
is proved by induction on the sequence `S`: for `nil`, `J_0 = D^j(I)`; for `cons X D rest`, the
first stage is the one-blow-up inclusion `π_*^{-1}(D^j(I), m − j) ⊆ D^j(π_*^{-1}(I, m))`
(`markedTransform_derivativeIter_le`, `Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`, on
`B_D X`, which is the stage after the first blow-up definitionally), the marked recursion is
monotone in its starting ideal (`markedTransformSeq_mono`), and the tail is a sequence of order `≥
m` for the transformed data (`isOrderGeSeq_cons_iff`) to which the induction hypothesis applies. The
order inequality of Corollary 77 is then read off at every stage: `ord_{Z_i} J_i ≥ ord_{Z_i}
D^j(I_i) ≥ m − j` (a smaller ideal has a larger order; [Kol07, Lemma 74 (3)]). The one-stage
inductive step is stated separately for one blow-up (`derivSeq_step`), and the stagewise
divisibility follows from Corollary 77 through `pow_dvd_comap_of_leOrdAlong` at each stage
(`exceptionalAt_pow_dvd_comap_step_of_leOrdAlong`, by induction on `S`, the `eqToHom` of the first
step disappearing after a case split on the tail).

Kollár's warning that the transform depends on the whole sequence [Kol07, Warning 63] is why the
statements are made for the recursion `markedTransformSeq` and not for the composite `Π`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The marked recursion is monotone in its starting ideal -/

section Mono

/-- The controlled transform is monotone in the ideal (the colon and the inverse image are). -/
theorem controlledTransformAlong_mono_left {B : Scheme.{u}} (π : B ⟶ X) (F : B.IdealSheafData)
    {J J' : X.IdealSheafData} (h : J ≤ J') (c : ℕ) :
    J.controlledTransformAlong π F c ≤ J'.controlledTransformAlong π F c :=
  colon_mono_left _ _ _ (comap_mono π h)

/-- Kollár's marked transform `π_*^{-1}(J, c)` is monotone in `J`. -/
theorem markedTransform_mono (D : X.IdealSheafData) {J J' : X.IdealSheafData} (h : J ≤ J')
    (c : ℕ) : J.markedTransform D c ≤ J'.markedTransform D c :=
  controlledTransformAlong_mono_left _ _ h c

/-- The marked recursion along a sequence is monotone in its starting ideal (used in the proof of
[Kol07, Corollary 77]). -/
theorem markedTransformSeq_mono (S : BlowUpSequence X) {J J' : X.IdealSheafData} (h : J ≤ J')
    (c : ℕ) (i : Fin (S.length + 1)) :
    S.markedTransformSeq J c i ≤ S.markedTransformSeq J' c i := by
  induction S with
  | nil Y => exact h
  | cons Y D rest ih =>
    rcases i with ⟨_ | i, hi⟩
    · exact h
    · exact ih (markedTransform_mono D h c) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end Mono

/-! ### The inductive step at one stage -/

section Step

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)]
  (I : X.IdealSheafData)

include f n

/-- The inductive step of [Kol07, Corollary 77] (compare the proof of [Wlo05, Lemma 2.6.4]): for
one smooth blow-up with `ord_Z I ≥ m` and `j ≤ m`, an ideal `J ⊆ D^j(I)` has `ord_Z J ≥ m − j` and
`π_*^{-1}(J, m − j) ⊆ D^j(π_*^{-1}(I, m))`. -/
theorem derivSeq_step {m : ℕ} (hm : I.LeOrdAlong Z.support (m : ℕ∞)) {j : ℕ} (hj : j ≤ m)
    {J : X.IdealSheafData} (hJ : J ≤ I.derivativeIter f j) :
    J.LeOrdAlong Z.support ((m - j : ℕ) : ℕ∞) ∧
      J.markedTransform Z (m - j) ≤ (I.markedTransform Z m).derivativeIter
          (Z.blowUpπ ≫ f) j :=
  ⟨fun η hη => (leOrdAlong_derivativeIter f n Z I hm hj η hη).trans (ord_anti hJ η),
    (markedTransform_mono Z hJ (m - j)).trans (markedTransform_derivativeIter_le f n Z I hm hj)⟩

end Step

/-! ### Theorem 76 and Corollary 77 along the sequence -/

section Sequence

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

include n

/-- [Kol07, Theorem 76] along the sequence (compare [Wlo05, Lemma 2.6.4]): `J_i ⊆ D^j(I_i)` at
every stage of a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, for `j ≤ m`.
Induction on the sequence: the first stage is the one-blow-up Theorem 76
(`markedTransform_derivativeIter_le`), the marked recursion is monotone in its starting ideal,
and the tail is a sequence of order `≥ m` for the transformed data. -/
theorem markedTransformSeq_derivativeIter_le (h : S.IsOrderGeSeq f I m E) {j : ℕ} (hj : j ≤ m)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I.derivativeIter f j) (m - j) i ≤
      (S.markedTransformSeq I m i).derivativeIter (S.stageMap i ≫ f) j := by
  induction S with
  | nil Y =>
    change I.derivativeIter f j ≤ I.derivativeIter (𝟙 Y ≫ f) j
    rw [Category.id_comp]
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · change I.derivativeIter f j ≤ I.derivativeIter (𝟙 Y ≫ f) j
      rw [Category.id_comp]
    · change rest.markedTransformSeq ((I.derivativeIter f j).markedTransform D (m - j)) (m - j)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≤
        (rest.markedTransformSeq (I.markedTransform D m) m
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩).derivativeIter
            ((rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f) j
      rw [Category.assoc]
      exact (markedTransformSeq_mono rest (markedTransform_derivativeIter_le f n D I hm hj) (m - j)
        _).trans (ih (D.blowUpπ ≫ f) (I.markedTransform D m)
            (E.totalTransform D) ht
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-- [Kol07, Corollary 77]: a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`
is one of order `≥ m − j` starting with `(X, D^j(I), m − j, E)`: the smoothness and normal
crossing conditions do not mention the ideal, and `ord_{Z_i} J_i ≥ m − j` because
`J_i ⊆ D^j(I_i)` (`markedTransformSeq_derivativeIter_le`) and `ord_{Z_i} D^j(I_i) ≥ m − j`
(`leOrdAlong_derivativeIter`). -/
theorem isOrderGeSeq_derivativeIter (h : S.IsOrderGeSeq f I m E) {j : ℕ} (hj : j ≤ m) :
    S.IsOrderGeSeq f (I.derivativeIter f j) (m - j) E := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, fun η hη => ?_⟩⟩
  have _ := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h.1 i.castSucc
  exact (leOrdAlong_derivativeIter (S.stageMap i.castSucc ≫ f) n (S.center i) _
    (IsOrderGeSeq.leOrdAlong h i) hj η hη).trans
    (ord_anti (markedTransformSeq_derivativeIter_le f n S I E m h hj i.castSucc) η)

/-- `pow_dvd_comap_of_leOrdAlong` at every stage of a smooth sequence: an ideal of order `≥ c`
along the center `Z_i` has `F_{i+1}^c ∣ π_i^* K`. By induction on the sequence; at the first stage
of a `cons` the step is `blowUpπ` once the tail's constructor is known. -/
theorem exceptionalAt_pow_dvd_comap_step_of_leOrdAlong (h : S.IsSmooth f) (i : Fin S.length)
    (K : (S.stage i.castSucc).IdealSheafData) {c : ℕ}
    (hK : K.LeOrdAlong (S.center i).support (c : ℕ∞)) :
    S.exceptionalAt i ^ c ∣ K.comap (S.step i) := by
  induction S with
  | nil Y => exact i.elim0
  | cons Y D rest ih =>
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · cases rest with
      | nil =>
        change (D.comap ((cons Y D (nil _)).step ⟨0, hi⟩)) ^ c ∣
          K.comap ((cons Y D (nil _)).step ⟨0, hi⟩)
        rw [step_cons_nil_zero]
        exact pow_dvd_comap_of_leOrdAlong f n D K hK
      | cons _ D' rest' =>
        change (D.comap ((cons Y D (cons _ D' rest')).step ⟨0, hi⟩)) ^ c ∣
          K.comap ((cons Y D (cons _ D' rest')).step ⟨0, hi⟩)
        rw [step_cons_cons_zero]
        exact pow_dvd_comap_of_leOrdAlong f n D K hK
    · exact ih (D.blowUpπ ≫ f) ht ⟨i, Nat.lt_of_succ_lt_succ hi⟩ K hK

/-- The marked transform `(π_i)_*^{-1}(J_i, m − j)` of the derivative sequence is defined at every
stage in the sense of [Kol07, Definition 60] (`F_{i+1}^{m−j}` divides `π_i^* J_i`), because
`ord_{Z_i} J_i ≥ m − j` ([Kol07, Corollary 77]). -/
theorem exceptionalAt_pow_dvd_comap_step_derivativeIter (h : S.IsOrderGeSeq f I m E) {j : ℕ}
    (hj : j ≤ m) (i : Fin S.length) :
    S.exceptionalAt i ^ (m - j) ∣
      (S.markedTransformSeq (I.derivativeIter f j) (m - j) i.castSucc).comap (S.step i) :=
  exceptionalAt_pow_dvd_comap_step_of_leOrdAlong f n S h.1 i _
    (IsOrderGeSeq.leOrdAlong (isOrderGeSeq_derivativeIter f n S I E m h hj) i)

end Sequence

end AlgebraicGeometry
