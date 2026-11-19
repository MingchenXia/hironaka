/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Kol07.Theorem88Sequence
import Hironaka.Resolution.Algebraic.MaximalContact.Basic
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicQuotient
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicSheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Corollary 89: the cosupport of the transform on the hypersurface of centers

Kollár's Corollary 89 [Kol07, Corollary 89]: with the notation of [Kol07, Theorem 88], a smooth
blow-up sequence of order `≥ m` for `(X, I, m)` and a smooth hypersurface `S` whose strict
transforms `S_i` contain the centers,

  `S_r ∩ cosupp Π_*^{-1}(I, m) = ⋂_{j < m} cosupp (Π|_{S_r})_*^{-1}((D^j I)|_S, m − j)`.

* **Logarithmic derivatives restrict, along a closed immersion.** Kollár's (87.1)
  [Kol07, 87], `(D^r(−log S)(I))|_S = D^r(I|_S)`, is proved in
  `Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean` along the inclusion `V(S) ↪ X`; the
  same stalkwise argument (the stalk map of a closed immersion is surjective with kernel the stalk
  of its kernel ideal sheaf, and the stalk of a smooth scheme is formally smooth over `k`) gives it
  along any closed immersion `g : Y ⟶ X` with the hypersurface `ker g`
  (`logDerivativeIter_comap_of_isClosedImmersion`). The stage embeddings `S_i ↪ X_i` of the
  restricted sequence are such closed immersions, with kernel `S_i`.
* **Kollár's (89.1).** Theorem 88 at stage `i`, restricted along `S_i ↪ X_i`: `comap` commutes
  with the sum, (87.1) turns `D^{s−j}(−log S_i)` into `D^{s−j}` on `S_i`, and the restriction of
  the marked transform `Π_*^{-1}(D^j I, m − j)` is the marked transform of the restricted data
  along the restricted sequence, [Kol07, Lemma 62] iterated
  (`IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom`) on the sequence of order `≥ m − j` for
  `(D^j I, m − j)` [Kol07, Corollary 77]. The structure morphisms of the restricted stage agree by
  `pullbackStageHom_stageMap`.
* **Kollár's (89.2) and (89.3).** A marking-one cosupport is a support (`one_le_ord_iff`) and
  supports pull back (`support_comap`); the cosupport of a sum is the intersection of the
  cosupports ([Kol07, Definition 59 (4)]) because the stalk of a sum is the sum of the stalks and
  `⨆ ≤ 𝔪^c` iff each summand is.
* **Corollary 89.** For `m ≥ 1`, (89.1) at `s = m − 1`: the left cosupport is
  `cosupp (Π_*^{-1}(I, m), m)` pulled back to `S_i` (`cosupp(I, m) = cosupp(D^{m−1} I, 1)`,
  [Kol07, Lemma 74 (3)], `coe_support_MC` at the stage `X_i`), the right one is the intersection
  of the `cosupp (J_j, m − j)`, `j ≤ m − 1` (Lemma 74 (3) at the mark `m − j` on the restricted
  stage `S_i`, smooth of relative dimension `n − 1` over `k`). For `m = 0` both sides are the
  whole space.

Corollary 89 is the input of the going-up theorem for D-balanced ideals
(`Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`), where it is read on a pushed-forward sequence.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Cosupports of a restriction and of a sum -/

section Cosupp

/-- A marking-one cosupport is the support, and the support of a restriction is the preimage of
the support (Kollár's (89.2), [Kol07, Corollary 89]). -/
theorem cosupp_one_comap {Y : Scheme.{u}} (g : Y ⟶ X) (A : X.IdealSheafData) :
    {y : Y | (1 : ℕ∞) ≤ (A.comap g).ord y} = g ⁻¹' {x : X | (1 : ℕ∞) ≤ A.ord x} := by
  ext y
  change (1 : ℕ∞) ≤ (A.comap g).ord y ↔ (1 : ℕ∞) ≤ A.ord (g y)
  rw [IdealSheafData.one_le_ord_iff, IdealSheafData.one_le_ord_iff, IdealSheafData.support_comap]
  exact Iff.rfl

/-- The cosupport of a sum is the intersection of the cosupports ([Kol07, Definition 59 (4)]
iterated, as in Kollár's (89.3)): the stalk of the sum is the sum of the stalks, and it lies in
`𝔪^c` iff every summand does. -/
theorem cosupp_iSup_eq_iInter {ι : Sort*} (A : ι → X.IdealSheafData) (c : ℕ) :
    {x : X | (c : ℕ∞) ≤ (⨆ i, A i).ord x} = ⋂ i, {x : X | (c : ℕ∞) ≤ (A i).ord x} := by
  ext x
  rw [Set.mem_iInter]
  change (c : ℕ∞) ≤ (⨆ i, A i).ord x ↔ ∀ i, (c : ℕ∞) ≤ (A i).ord x
  simp only [IdealSheafData.le_ord_iff, IdealSheafData.stalkIdeal_iSup', iSup_le_iff]

end Cosupp

/-! ### Restriction of logarithmic derivatives along a closed immersion -/

section LogRestrict

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

include n

/-- Kollár's (87.1) [Kol07, 87] along any closed immersion `g : Y ⟶ X` with hypersurface `ker g`
(`logDerivativeIter_comap_subschemeι` is the case `g = S.subschemeι`):
`(D^r(−log (ker g))(I))|_Y = D^r(I|_Y)`. Stalkwise: the stalk map of a closed immersion is
surjective with kernel the stalk of `ker g` (`ker_stalkMap_of_isClosedImmersion`), and the stalk
of a smooth scheme is formally smooth over `k`. -/
theorem logDerivativeIter_comap_of_isClosedImmersion {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsClosedImmersion g] (I : X.IdealSheafData) (r : ℕ) :
    (g.ker.logDerivativeIter f r I).comap g = (I.comap g).derivativeIter (g ≫ f) r := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine Scheme.IdealSheafData.ext_stalkIdeal fun y => ?_
  let _ := f.stalkAlgebra (g y)
  let _ := (g ≫ f).stalkAlgebra y
  have hfs : Algebra.FormallySmooth k (X.presheaf.stalk (g y)) :=
    formallySmooth_stalk f n _
  have hψ : Function.Surjective (g.stalkMap y).hom := g.stalkMap_surjective y
  have hker : RingHom.ker (g.stalkMap y).hom = g.ker.stalkIdeal (g y) :=
    ker_stalkMap_of_isClosedImmersion g y
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_derivativeIter,
      IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_logDerivativeIter,
    ← hker]
  exact Ideal.logDerivativeIter_map_of_surjective' (g.stalkMap y).hom
    (fun c => RingHom.congr_fun (Scheme.Hom.stalkMap_comp_algebraMap_stalkAlgebra f g y) c) hψ r _

end LogRestrict

/-! ### Kollár's (89.1) and Corollary 89 -/

section Sequence

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (B : BlowUpSequence X) (S I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

include n

/-- Kollár's (89.1) in the proof of [Kol07, Corollary 89]: Theorem 88 at stage `i`, restricted
along `S_i ↪ X_i`; (87.1) for the logarithmic derivatives, [Kol07, Lemma 62] iterated for the
marked transforms, on the sequence of order `≥ m − j` for `(D^j I, m − j)`. -/
theorem derivativeIter_comap_pullbackStageHom_eq_iSup (hS : IsSmoothDivisor S)
    (h : B.IsOrderGeSeq f I m E)
    (hZS : ∀ i : Fin B.length, B.strictTransformSeq S i.castSucc ≤ B.center i) {s : ℕ}
    (hs : s ≤ m) (i : Fin (B.length + 1)) :
    ((B.markedTransformSeq I m i).derivativeIter (B.stageMap i ≫ f) s).comap
        (B.pullbackStageHom S.subschemeι i) =
      ⨆ j ≤ s, ((B.pullback S.subschemeι).markedTransformSeq
          ((I.derivativeIter f j).comap S.subschemeι) (m - j)
          (B.pullbackStageIdx S.subschemeι i)).derivativeIter
        ((B.pullback S.subschemeι).stageMap (B.pullbackStageIdx S.subschemeι i) ≫
          (S.subschemeι ≫ f)) (s - j) := by
  have hsm : B.IsSmooth f := h.1
  have hstage : SmoothOfRelativeDimension n (B.stageMap i ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap (n := n) hsm i
  have hci := isClosedImmersion_pullbackStageHom B S.subschemeι i
  have hker : (B.pullbackStageHom S.subschemeι i).ker = B.strictTransformSeq S i := by
    rw [ker_pullbackStageHom, IdealSheafData.ker_subschemeι]
  rw [derivativeIter_markedTransformSeq_eq_iSup f n B S I E m hS h hZS hs i,
      IdealSheafData.comap_iSup]
  refine iSup_congr fun j => ?_
  rw [IdealSheafData.comap_iSup]
  refine iSup_congr fun hj => ?_
  rw [← hker, logDerivativeIter_comap_of_isClosedImmersion (B.stageMap i ≫ f) n
    (B.pullbackStageHom S.subschemeι i) _ (s - j),
    ← IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom f n S.subschemeι
      (isOrderGeSeq_derivativeIter f n B I E m h (hj.trans hs)) i,
    ← Category.assoc, pullbackStageHom_stageMap, Category.assoc]

/-- **Kollár's Corollary 89** [Kol07, Corollary 89] at every stage: (89.1) at `s = m − 1`, the
cosupports taken by `cosupp_one_comap`, `cosupp_iSup_eq_iInter` and [Kol07, Lemma 74 (3)] at the
marks `m` (on `X_i`) and `m − j` (on `S_i`); for `m = 0` both sides are the whole space. -/
theorem cosupp_markedTransformSeq_inter_eq_iInter (hS : IsSmoothDivisor S)
    (h : B.IsOrderGeSeq f I m E)
    (hZS : ∀ i : Fin B.length, B.strictTransformSeq S i.castSucc ≤ B.center i)
    (i : Fin (B.length + 1)) :
    {y : (B.pullback S.subschemeι).stage (B.pullbackStageIdx S.subschemeι i) |
        (m : ℕ∞) ≤ (B.markedTransformSeq I m i).ord (B.pullbackStageHom S.subschemeι i y)} =
      ⋂ j < m, {y | ((m - j : ℕ) : ℕ∞) ≤ ((B.pullback S.subschemeι).markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j)
        (B.pullbackStageIdx S.subschemeι i)).ord y} := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · ext y
    simp
  have hm1 : 1 ≤ m := hm
  have hsm : B.IsSmooth f := h.1
  have hsf : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hstage : SmoothOfRelativeDimension n (B.stageMap i ≫ f) :=
    IsSmooth.smoothOfRelativeDimension_stageMap (n := n) hsm i
  have hSf : SmoothOfRelativeDimension (n - 1) (S.subschemeι ≫ f) :=
    smoothOfRelativeDimension_of_isSmoothDivisor f n S hS
  have hrestr : (B.pullback S.subschemeι).IsSmooth (S.subschemeι ≫ f) :=
    isSmooth_pullback_of_strictTransformSeq_le B S f hZS hsm
  have hstage' : SmoothOfRelativeDimension (n - 1)
      ((B.pullback S.subschemeι).stageMap (B.pullbackStageIdx S.subschemeι i) ≫
        (S.subschemeι ≫ f)) :=
    IsSmooth.smoothOfRelativeDimension_stageMap (n := n - 1) hrestr _
  have h891 := derivativeIter_comap_pullbackStageHom_eq_iSup f n B S I E m hS h hZS
    (Nat.sub_le m 1) i
  ext y
  rw [Set.mem_iInter₂]
  change (m : ℕ∞) ≤ (B.markedTransformSeq I m i).ord (B.pullbackStageHom S.subschemeι i y) ↔
    ∀ j, j < m → ((m - j : ℕ) : ℕ∞) ≤ ((B.pullback S.subschemeι).markedTransformSeq
      ((I.derivativeIter f j).comap S.subschemeι) (m - j)
      (B.pullbackStageIdx S.subschemeι i)).ord y
  -- the left side: `m ≤ ord_{ι y} I_i` iff `ι y ∈ V(D^{m−1} I_i)` (74.3) iff
  -- `y ∈ V((D^{m−1} I_i)|_{S_i})`
  have hL : (m : ℕ∞) ≤ (B.markedTransformSeq I m i).ord (B.pullbackStageHom S.subschemeι i y) ↔
      ((1 : ℕ) : ℕ∞) ≤ (((B.markedTransformSeq I m i).derivativeIter (B.stageMap i ≫ f)
        (m - 1)).comap (B.pullbackStageHom S.subschemeι i)).ord y := by
    rw [Nat.cast_one, IdealSheafData.one_le_ord_iff, IdealSheafData.support_comap]
    exact (IdealSheafData.mem_support_MC_iff (B.stageMap i ≫ f) n (B.markedTransformSeq I m i) hm1
      (B.pullbackStageHom S.subschemeι i y)).symm
  -- (89.1) at `s = m − 1`, read at `y` through the cosupport of the sum
  have key : ((1 : ℕ) : ℕ∞) ≤ (((B.markedTransformSeq I m i).derivativeIter (B.stageMap i ≫ f)
        (m - 1)).comap (B.pullbackStageHom S.subschemeι i)).ord y ↔
      ∀ j, j ≤ m - 1 → ((1 : ℕ) : ℕ∞) ≤ (((B.pullback S.subschemeι).markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j)
        (B.pullbackStageIdx S.subschemeι i)).derivativeIter
        ((B.pullback S.subschemeι).stageMap (B.pullbackStageIdx S.subschemeι i) ≫
          (S.subschemeι ≫ f)) (m - 1 - j)).ord y := by
    rw [h891]
    simp only [IdealSheafData.le_ord_iff, IdealSheafData.stalkIdeal_iSup', iSup_le_iff]
  -- the right side, summand by summand: 74.3 at the mark `m − j` on `S_i`
  have hR : ∀ j, j < m → (((m - j : ℕ) : ℕ∞) ≤ ((B.pullback S.subschemeι).markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j)
        (B.pullbackStageIdx S.subschemeι i)).ord y ↔
      ((1 : ℕ) : ℕ∞) ≤ (((B.pullback S.subschemeι).markedTransformSeq
        ((I.derivativeIter f j).comap S.subschemeι) (m - j)
        (B.pullbackStageIdx S.subschemeι i)).derivativeIter
        ((B.pullback S.subschemeι).stageMap (B.pullbackStageIdx S.subschemeι i) ≫
          (S.subschemeι ≫ f)) (m - 1 - j)).ord y) := fun j hj => by
    have hmj : 1 ≤ m - j := Nat.sub_pos_of_lt hj
    rw [Nat.cast_one, IdealSheafData.one_le_ord_iff, Nat.sub_right_comm]
    exact (IdealSheafData.mem_support_MC_iff ((B.pullback S.subschemeι).stageMap
      (B.pullbackStageIdx S.subschemeι i) ≫ (S.subschemeι ≫ f)) (n - 1) _ hmj y).symm
  rw [hL, key]
  constructor
  · intro H j hj
    exact (hR j hj).mpr (H j ((Nat.lt_iff_le_pred hm).mp hj))
  · intro H j hj
    have hj' : j < m := (Nat.lt_iff_le_pred hm).mpr hj
    exact (hR j hj').mp (H j hj')

end Sequence

end Hironaka.Sequence
