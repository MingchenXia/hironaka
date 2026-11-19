/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Properties
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 88: the parts that need no coordinates

[Kol07, Theorem 88] describes the derivatives `D^s Π_*^{-1}(I, m)` of the transform of a marked
ideal along a smooth blow-up sequence of order `≥ m` whose centers lie in the transforms of a
smooth hypersurface `S`, as the sum (88.1) of logarithmic derivatives along `S_r` of the transforms
of the derivatives `D^j I`. This module collects the parts of its proof that need no coordinates;
the chart computation is in `Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean` and the
induction along the sequence in `Hironaka/Resolution/Algebraic/Kol07/Theorem88Sequence.lean`.

* **The inclusion `⊇`.** "Using (76) we obtain … thus the right-hand side of (88.1) is contained in
  the left-hand side": at every stage of a smooth blow-up sequence of order `≥ m`, for
  `j ≤ s ≤ m` and any closed `S`,
  `D^{s−j}(−log S_i) Π_*^{-1}(D^j I, m − j) ⊆ D^{s−j} Π_*^{-1}(D^j I, m − j)`, which lies in
  `D^{s−j} D^j Π_*^{-1}(I, m) = D^s Π_*^{-1}(I, m)` (`logDerivativeIter_le_derivativeIter`,
  `markedTransformSeq_derivativeIter_le` with the monotonicity of `D^{s−j}`, and
  `D^a D^b = D^{a+b}`, [Kol07, Lemma 74 (1)];
  `logDerivativeIter_markedTransformSeq_le_derivativeIter`).
* **Off the hypersurface.** At a point `q ∉ S'` the logarithmic derivatives are the derivatives,
  `(D^r(−log S')(K))_q = (D^r K)_q`: the stalk formulas with `(S')_q = 𝒪_q`
  (`stalkIdeal_eq_top_of_notMem_support`) and `Ideal.logDerivative_top`
  (`stalkIdeal_logDerivativeIter_of_notMem_support`). This is what makes the charts missing the
  strict transform of `S` harmless in Kollár's proof.
* **The marked transform of a sum.** For marked transforms of the same mark `c` that are defined
  (`F^c ∣ π^* K_j` for every summand), `π_*^{-1}(∑ K_j, c) ⊆ ∑ π_*^{-1}(K_j, c)`:
  `π^* K_j = F^c · π_*^{-1}(K_j, c)` for each `j` (`pow_mul_colon_of_dvd`), so
  `π^*(∑ K_j) = F^c · ∑ π_*^{-1}(K_j, c)`, and the colon by the invertible `F^c` recovers the sum
  (`colon_pow_eq_of_mul_eq`); `markedTransform_iSup_le`, in fact an equality. Kollár uses it to
  push the transform inside the sum in the inductive step of the proof.
* **The composition rule** for logarithmic derivatives,
  `D^a(−log S) ∘ D^b(−log S) = D^{a+b}(−log S)` (`logDerivativeIter_logDerivativeIter`,
  `Function.iterate_add_apply`), the analogue of
  [Kol07, Lemma 74 (1)], used at the end of the proof.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace Ideal

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- At ring level (`logDerivative_top` iterated): along the unit ideal the iterated logarithmic
derivatives are the iterated derivatives. -/
theorem logDerivativeIter_top (r : ℕ) (I : Ideal A) :
    logDerivativeIter k ⊤ r I = derivativeIter k r I := by
  induction r with
  | zero => rw [logDerivativeIter_zero, derivativeIter_zero]
  | succ r ih => rw [logDerivativeIter_succ, derivativeIter_succ, ih, logDerivative_top]

end Ideal

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The composition rule for logarithmic derivatives -/

/-- The composition rule `D^a(−log S)(D^b(−log S)(K)) = D^{a+b}(−log S)(K)`, the analogue of
[Kol07, Lemma 74 (1)] for logarithmic derivatives, used at the end of the proof of
[Kol07, Theorem 88]. -/
theorem logDerivativeIter_logDerivativeIter (f : X ⟶ Spec (.of k)) (S K : X.IdealSheafData)
    (a b : ℕ) :
    S.logDerivativeIter f a (S.logDerivativeIter f b K) = S.logDerivativeIter f (a + b) K :=
  (Function.iterate_add_apply _ a b K).symm

/-! ### The marked transform of a sum -/

section Sum

variable (Z : X.IdealSheafData)

/-- Multiplication of ideal sheaves distributes over suprema (sectionwise `Submodule.mul_iSup`). -/
theorem mul_iSup' {ι : Sort*} (I : X.IdealSheafData) (J : ι → X.IdealSheafData) :
    I * (⨆ i, J i) = ⨆ i, I * J i := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  change I.ideal U * (⨆ i, J i).ideal U = (⨆ i, I * J i).ideal U
  rw [ideal_iSup', ideal_iSup', iSup_apply, iSup_apply]
  exact Submodule.mul_iSup _ _

/-- For marked transforms of the same mark `c` that are defined, the marked transform of a sum
lies in the sum of the marked transforms (in fact equals it): each `π^* K_j` is
`F^c · π_*^{-1}(K_j, c)`, so `π^*(⨆ K_j) = F^c · ⨆ π_*^{-1}(K_j, c)` and the colon by the
invertible `F^c` recovers `⨆ π_*^{-1}(K_j, c)`. Used in the inductive step of the proof of
[Kol07, Theorem 88]. -/
theorem markedTransform_iSup_le (K : ℕ → X.IdealSheafData) (s c : ℕ)
    (hK : ∀ j ≤ s, Z.exceptionalDivisor ^ c ∣ (K j).comap Z.blowUpπ) :
    (⨆ j ≤ s, K j).markedTransform Z c ≤ ⨆ j ≤ s, (K j).markedTransform Z c := by
  have hF : Z.exceptionalDivisor.IsInvertible := blowUp.isInvertible_comap_π Z
  have hmul : ∀ j ≤ s, (K j).comap Z.blowUpπ =
      Z.exceptionalDivisor ^ c * (K j).markedTransform Z c :=
    fun j hj => (pow_mul_colon_of_dvd (I := (K j).comap Z.blowUpπ)
        Z.exceptionalDivisor c
      (hK j hj)).symm
  have hsum : (⨆ j ≤ s, K j).comap Z.blowUpπ =
      Z.exceptionalDivisor ^ c * ⨆ j ≤ s, (K j).markedTransform Z c := by
    rw [comap_iSup, mul_iSup']
    refine iSup_congr fun j => ?_
    rw [comap_iSup, mul_iSup']
    exact iSup_congr fun hj => hmul j hj
  change ((⨆ j ≤ s, K j).comap Z.blowUpπ).colon
      (Z.exceptionalDivisor ^ c) ≤ _
  rw [hsum, colon_pow_eq_of_mul_eq _ hF c _ rfl]

end Sum

/-! ### Off the hypersurface the logarithmic derivatives are the derivatives -/

section OffHypersurface

variable (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (S K : X.IdealSheafData)

/-- Off the hypersurface the logarithmic derivative is the derivative, at the level of stalks. -/
theorem stalkIdeal_logDerivative_of_notMem_support {q : X} (hq : q ∉ S.support) :
    (S.logDerivative f K).stalkIdeal q = (K.derivative f).stalkIdeal q := by
  let _ := f.stalkAlgebra q
  rw [stalkIdeal_logDerivative f S K q, stalkIdeal_derivative f K q,
    stalkIdeal_eq_top_of_notMem_support S hq, Ideal.logDerivative_top]

/-- Off the hypersurface the iterated logarithmic derivatives are the iterated derivatives,
`(D^r(−log S)(K))_q = (D^r K)_q` (the charts missing the strict transform of `S` in the proof of
[Kol07, Theorem 88]). -/
theorem stalkIdeal_logDerivativeIter_of_notMem_support (r : ℕ) {q : X} (hq : q ∉ S.support) :
    (S.logDerivativeIter f r K).stalkIdeal q = (K.derivativeIter f r).stalkIdeal q := by
  let _ := f.stalkAlgebra q
  rw [stalkIdeal_logDerivativeIter f S K r q, stalkIdeal_derivativeIter f r K q,
    stalkIdeal_eq_top_of_notMem_support S hq, Ideal.logDerivativeIter_top]

end OffHypersurface

/-! ### The inclusion `⊇` of (88.1) along the sequence -/

section Supset

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (B : BlowUpSequence X) (S I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

include n

/-- "Using (76) we obtain … the right-hand side of (88.1) is contained in the left-hand side"
(the proof of [Kol07, Theorem 88]): every summand of the right-hand side of (88.1) lies in the
left-hand side, at every stage, for every closed `S`:
`D^{s−j}(−log S_i) J_i^{(j)} ⊆ D^{s−j} J_i^{(j)} ⊆ D^{s−j} D^j I_i = D^s I_i`. -/
theorem logDerivativeIter_markedTransformSeq_le_derivativeIter (h : B.IsOrderGeSeq f I m E)
    {s j : ℕ} (hj : j ≤ s) (hs : s ≤ m) (i : Fin (B.length + 1)) :
    (B.strictTransformSeq S i).logDerivativeIter (B.stageMap i ≫ f) (s - j)
        (B.markedTransformSeq (I.derivativeIter f j) (m - j) i) ≤
      (B.markedTransformSeq I m i).derivativeIter (B.stageMap i ≫ f) s := by
  have h1 := logDerivativeIter_le_derivativeIter (B.stageMap i ≫ f) (B.strictTransformSeq S i)
    (B.markedTransformSeq (I.derivativeIter f j) (m - j) i) (s - j)
  have h2 := derivativeIter_mono (B.stageMap i ≫ f) (s - j)
    (markedTransformSeq_derivativeIter_le f n B I E m h (hj.trans hs) i)
  refine h1.trans (h2.trans ?_)
  rw [derivativeIter_derivativeIter, Nat.sub_add_cancel hj]

end Supset

end AlgebraicGeometry
