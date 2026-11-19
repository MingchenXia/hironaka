/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Kol07.Theorem88BlowUp
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.LogDerivativeSequence
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Theorem88Basic
import Hironaka.Scheme.BlowUpSequence.TransformDerivative
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 88 along a blow-up sequence

[Kol07, Theorem 88]: for a smooth blow-up sequence `Π : X_r → ⋯ → X` of order `≥ m` with every
center `Z_i ⊆ S_i`, `S` a smooth hypersurface with strict transforms `S_i`, and `s ≤ m`, at every
stage `D^s Π_*^{-1}(I, m) = ∑_{j ≤ s} D^{s−j}(−log S_i) Π_*^{-1}(D^j I, m − j)` (88.1). This is
the form in which the derivatives of the transform of a marked ideal are controlled in the
going-up theorem for D-balanced ideals (`Hironaka/Resolution/Algebraic/Kol07/Corollary89.lean`).

**The induction on the sequence** (Kollár's (88.3)): peel the first blow-up `π : X_1 → X` with
center `Z ⊆ S`. The tail is a sequence of order `≥ m` for `(X_1, π_*^{-1}(I, m), E_1)` with the
hypersurface `S_1 = π_*^{-1}S`, a smooth hypersurface (`isSmoothDivisor_strictTransform_of_le`),
so the induction hypothesis gives (88.1) for the tail with the ideals `D^j π_*^{-1}(I, m)`. By the
one-blow-up case (`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`),
`D^j π_*^{-1}(I, m) = ∑_{l ≤ j} D^{j−l}(−log S_1) π_*^{-1}(D^l I, m − l)`; the marked transform
along the tail of this sum lies in the sum of the marked transforms (`markedTransformSeq_iSup_le`,
the marks being defined by the order bounds), each of which lies in
`D^{j−l}(−log S_i) Π_*^{-1}(D^l I, m − l)` by (87.3) along the sequence
(`markedTransformSeq_logDerivativeIter_le`), and
`D^{s−j}(−log S_i) D^{j−l}(−log S_i) = D^{s−l}(−log S_i)` (the composition rule); `D(−log S_i)`
of a sum lies in the sum (`logDerivativeIter_iSup_le`). The reverse inclusion is Theorem 76 for
the first blow-up and monotonicity. Stage `0` and the empty sequence are (88.1) on `X` itself:
the `j = s` summand is `D^s I`, the others lie in it.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace Ideal

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- `D(−log J)` of a sum lies in the sum of the `D(−log J)`s. -/
theorem logDerivative_iSup_le {ι : Sort*} (J : Ideal A) (K : ι → Ideal A) :
    logDerivative k J (⨆ i, K i) ≤ ⨆ i, logDerivative k J (K i) := by
  refine logDerivative_le_iff.mpr ⟨iSup_mono fun i => le_logDerivative J (K i), fun δ hδ x hx => ?_⟩
  induction hx using Submodule.iSup_induction' with
  | mem i x hx => exact Ideal.mem_iSup_of_mem i (derivation_apply_mem_logDerivative hδ hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

/-- `D^t(−log J)` of a sum lies in the sum of the `D^t(−log J)`s. -/
theorem logDerivativeIter_iSup_le {ι : Sort*} (J : Ideal A) (t : ℕ) (K : ι → Ideal A) :
    logDerivativeIter k J t (⨆ i, K i) ≤ ⨆ i, logDerivativeIter k J t (K i) := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [logDerivativeIter_succ]
    exact (logDerivative_mono ih).trans ((logDerivative_iSup_le J _).trans
      (iSup_mono fun i => le_of_eq (logDerivativeIter_succ J t (K i)).symm))

end Ideal

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

section LogSup

variable (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (S : X.IdealSheafData)

/-- `D^t(−log S)` of a sum of ideal sheaves lies in the sum (checked on stalks). -/
theorem logDerivativeIter_iSup_le {ι : Sort*} (t : ℕ) (K : ι → X.IdealSheafData) :
    S.logDerivativeIter f t (⨆ i, K i) ≤ ⨆ i, S.logDerivativeIter f t (K i) := by
  refine Scheme.IdealSheafData.le_of_stalkIdeal_le fun x => ?_
  let _ := f.stalkAlgebra x
  rw [stalkIdeal_iSup', stalkIdeal_logDerivativeIter f S _ t x]
  simp only [stalkIdeal_logDerivativeIter f S _ t x]
  rw [stalkIdeal_iSup']
  exact Ideal.logDerivativeIter_iSup_le _ t _

end LogSup

section Sum

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (B : BlowUpSequence X)

include n in
/-- The marked transform of a sum along a sequence lies in the sum of the marked transforms when
every summand has order `≥ c` along every center (so that the marked transforms are defined in the
sense of [Kol07, Definition 60]); `markedTransform_iSup_le` at every stage. -/
theorem markedTransformSeq_iSup_le (h : B.IsSmooth f) (K : ℕ → X.IdealSheafData) (s c : ℕ)
    (hK : ∀ j ≤ s, ∀ i : Fin B.length,
      (B.markedTransformSeq (K j) c i.castSucc).LeOrdAlong (B.center i).support (c : ℕ∞))
    (i : Fin (B.length + 1)) :
    B.markedTransformSeq (⨆ j ≤ s, K j) c i ≤ ⨆ j ≤ s, B.markedTransformSeq (K j) c i := by
  induction B with
  | nil Y => exact le_rfl
  | cons Y D rest ih =>
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | i, hi⟩
    · exact le_rfl
    · change rest.markedTransformSeq ((⨆ j ≤ s, K j).markedTransform D c) c
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≤
        ⨆ j ≤ s, rest.markedTransformSeq ((K j).markedTransform D c) c
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      have h0 : ∀ j ≤ s, D.exceptionalDivisor ^ c ∣ (K j).comap D.blowUpπ :=
          fun j hj =>
        pow_dvd_comap_of_leOrdAlong f n D (K j) (hK j hj ⟨0, Nat.succ_pos _⟩)
      refine (markedTransformSeq_mono rest (markedTransform_iSup_le D K s c h0) c _).trans ?_
      exact ih (D.blowUpπ ≫ f) ht (fun j => (K j).markedTransform D c)
        (fun j hj i₀ => hK j hj i₀.succ) _

omit [CharZero k] in
/-- `IsOrderGeSeq` is antitone in the ideal (the order is antitone, the marked transform
monotone). -/
theorem IsOrderGeSeq.of_le {I J : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
    (h : B.IsOrderGeSeq f I m E) (hJ : J ≤ I) : B.IsOrderGeSeq f J m E :=
  ⟨h.1, fun i => ⟨(h.2 i).1, fun η hη =>
    ((h.2 i).2 η hη).trans (ord_anti (markedTransformSeq_mono B hJ m i.castSucc) η)⟩⟩

end Sum

section Sequence

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (B : BlowUpSequence X) (S I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

omit [CharZero k] in
/-- (88.1) on `X` itself (the empty sequence, or stage `0`): the `j = s` summand is `D^s I` and
the others lie in it (`logDerivativeIter_le_derivativeIter` and [Kol07, Lemma 74 (1)]). -/
theorem derivativeIter_eq_iSup_logDerivativeIter (s : ℕ) :
    I.derivativeIter f s =
      ⨆ j ≤ s, S.logDerivativeIter f (s - j) (I.derivativeIter f j) := by
  refine le_antisymm (le_iSup₂_of_le s le_rfl ?_) (iSup₂_le fun j hj => ?_)
  · rw [Nat.sub_self, logDerivativeIter_zero]
  · refine (logDerivativeIter_le_derivativeIter f S _ (s - j)).trans ?_
    rw [derivativeIter_derivativeIter, Nat.sub_add_cancel hj]

include n in
/-- [Kol07, Theorem 88]: (88.1) at every stage of a smooth blow-up sequence of order `≥ m` whose
centers lie in the strict transforms of the smooth hypersurface `S`. -/
theorem derivativeIter_markedTransformSeq_eq_iSup (hS : IsSmoothDivisor S)
    (h : B.IsOrderGeSeq f I m E)
    (hZS : ∀ i : Fin B.length, B.strictTransformSeq S i.castSucc ≤ B.center i) {s : ℕ}
    (hs : s ≤ m) (i : Fin (B.length + 1)) :
    (B.markedTransformSeq I m i).derivativeIter (B.stageMap i ≫ f) s =
      ⨆ j ≤ s, (B.strictTransformSeq S i).logDerivativeIter (B.stageMap i ≫ f) (s - j)
        (B.markedTransformSeq (I.derivativeIter f j) (m - j) i) := by
  induction B with
  | nil Y =>
    change I.derivativeIter (𝟙 Y ≫ f) s =
      ⨆ j ≤ s, S.logDerivativeIter (𝟙 Y ≫ f) (s - j) (I.derivativeIter f j)
    rw [Category.id_comp]
    exact derivativeIter_eq_iSup_logDerivativeIter f S I s
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have _ := hD
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hSD : S ≤ D := hZS ⟨0, Nat.succ_pos _⟩
    -- the strict transform of `S` is a smooth hypersurface
    have hS₁ : IsSmoothDivisor (S.strictTransform D) :=
      Scheme.IdealSheafData.isSmoothDivisor_strictTransform_of_le f n D hD S hS hSD
    have hZS₁ : ∀ i : Fin rest.length,
        rest.strictTransformSeq (S.strictTransform D) i.castSucc ≤ rest.center i :=
      fun i => hZS i.succ
    rcases i with ⟨_ | i, hi⟩
    · change I.derivativeIter (𝟙 Y ≫ f) s =
        ⨆ j ≤ s, S.logDerivativeIter (𝟙 Y ≫ f) (s - j) (I.derivativeIter f j)
      rw [Category.id_comp]
      exact derivativeIter_eq_iSup_logDerivativeIter f S I s
    · change (rest.markedTransformSeq (I.markedTransform D m) m
            ⟨i, Nat.lt_of_succ_lt_succ hi⟩).derivativeIter
          ((rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f) s =
        ⨆ j ≤ s, (rest.strictTransformSeq (S.strictTransform D)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩).logDerivativeIter
          ((rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f) (s - j)
          (rest.markedTransformSeq ((I.derivativeIter f j).markedTransform D (m - j)) (m - j)
            ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      rw [Category.assoc, ih (D.blowUpπ ≫ f) (S.strictTransform D)
          (I.markedTransform D m)
        (E.totalTransform D) hS₁ ht hZS₁ ⟨i, Nat.lt_of_succ_lt_succ hi⟩]
      -- the tail is a sequence of order `≥ m − l` for `π_*^{-1}(D^l I, m − l)` (Theorem 76)
      have hM : ∀ l ≤ s, rest.IsOrderGeSeq (D.blowUpπ ≫ f)
          ((I.derivativeIter f l).markedTransform D (m - l)) (m - l) (E.totalTransform D) :=
        fun l hl => IsOrderGeSeq.of_le (D.blowUpπ ≫ f) rest
          (isOrderGeSeq_derivativeIter (D.blowUpπ ≫ f) n rest (I.markedTransform D m)
            (E.totalTransform D) m ht (hl.trans hs))
          (markedTransform_derivativeIter_le f n D I hm (hl.trans hs))
      have hsm := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) ht.1
        (⟨i, Nat.lt_of_succ_lt_succ hi⟩ : Fin (rest.length + 1))
      have hsm' : Smooth (rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ ≫ f)
          :=
        SmoothOfRelativeDimension.smooth n _
      have hft : LocallyOfFiniteType
          (rest.stageMap ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ ≫ f) := inferInstance
      refine le_antisymm (iSup₂_le fun j hj => ?_) (iSup₂_le fun l hl => ?_)
      · -- `⊆`: (88.1) for the first blow-up, the sum along the tail, (87.3) along the sequence,
        -- and the composition rule
        rw [derivativeIter_markedTransform_eq_iSup f n D S I hS hSD hm (hj.trans hs)]
        refine (logDerivativeIter_mono _ _ _
          (markedTransformSeq_iSup_le (D.blowUpπ ≫ f) n rest ht.1 _ j
              (m - j) ?_ _)).trans ?_
        · intro l hl i₀
          have h1 := IsOrderGeSeq.leOrdAlong (isOrderGeSeq_derivativeIter
              (D.blowUpπ ≫ f) n rest
            _ _ (m - l) (hM l (hl.trans hj)) (Nat.sub_le_sub_right (hj.trans hs) l)) i₀
          rw [show m - l - (j - l) = m - j by omega] at h1
          exact fun η hη => (h1 η hη).trans (ord_anti (markedTransformSeq_mono rest
            (logDerivativeIter_le_derivativeIter (D.blowUpπ ≫ f) _ _ (j - l))
                (m - j) _) η)
        refine (logDerivativeIter_iSup_le _ _ _ _).trans (iSup_le fun l =>
          (logDerivativeIter_iSup_le _ _ _ _).trans (iSup_le fun hl => ?_))
        have h436 := markedTransformSeq_logDerivativeIter_le (D.blowUpπ ≫ f) n rest
          (S.strictTransform D) ((I.derivativeIter f l).markedTransform D (m - l))
          (E.totalTransform D) (m - l) (hM l (hl.trans hj)) (Nat.sub_le_sub_right (hj.trans hs) l)
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩
        rw [show m - l - (j - l) = m - j by omega] at h436
        refine (logDerivativeIter_mono _ _ _ h436).trans ?_
        rw [logDerivativeIter_logDerivativeIter, show s - j + (j - l) = s - l by omega]
        exact le_iSup₂_of_le l (hl.trans hj) le_rfl
      · -- `⊇`: Theorem 76 for the first blow-up and monotonicity
        exact le_iSup₂_of_le l hl (logDerivativeIter_mono _ _ _ (markedTransformSeq_mono rest
          (markedTransform_derivativeIter_le f n D I hm (hl.trans hs)) (m - l) _))

end Sequence

end Hironaka.Sequence
