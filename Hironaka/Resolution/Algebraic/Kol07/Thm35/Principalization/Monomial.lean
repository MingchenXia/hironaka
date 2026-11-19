/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial
import Hironaka.Resolution.Algebraic.Kol07.MarkedProduct
import Hironaka.Resolution.Algebraic.Snc.MonomialComponents
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (2) of Theorem 35: the pull-back of the ideal is monomial

From the proof of the principalization theorem [Kol07, 72]: by construction `Π^*_{(X,I,E)} I` is
`I_r · 𝒪_{X_r}(F)` for an effective divisor `F` supported on the total transform of `∑ E^i`; here
`I_r = 𝒪_{X_r}` since `max-ord I_r < 1`, and `F` is a simple normal crossing divisor, so
`Π^*_{(X,I,E)} I` is a monomial ideal "which can be written down explicitly": with
`F_j ⊂ X_{j+1}` the exceptional divisor of the `j`th step,
`Π^*_{(X,I,E)} I = 𝒪_{X_r}(−∑_{j=s}^{r−1} Π^*_{r,j+1} F_j)`. Two theorems:

* `BMO_one_comap_composite_eq_prod`, the explicit formula on the `BMO_1` part (Kollár's sum over
  `j = s, …, r − 1`): the marked transform of [Kol07, Definition 60] iterated along the sequence
  (`comap_composite_eq_markedTransformSeq_last_mul_prod`) with the exact division at each mark-`1`
  step (`F_{j+1} ∣ π_j^* I_j`, from the order condition of [Kol07, Definition 66] through
  `pow_dvd_comap_of_leOrdAlong`) and `I_r = 𝒪` from [Kol07, Theorem 69 (1)] (`max-ord I_r < 1`,
  `dimFreeBMO_maxOrd_lt`);
* `BP_isIdealOfSncDivisor`, clause (2) of [Kol07, Theorem 35] as `IsIdealOfSncDivisor (Π^* I)`:
  the disjoining part enters only through `π^* I` (the ideal of the disjoined triple), the `BMO_1`
  part is the explicit product, which is the ideal sheaf of an effective divisor supported on a
  simple normal crossing family (`isIdealOfSncDivisor_prod_comap_exceptionalAt`), and the property
  is carried across the two isomorphisms of the definition, the cast of `concat` and the deletion
  of the empty blow-ups, by `IsIdealOfSncDivisor.comap_of_smooth`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Hironaka Scheme.BlowUpSequence
  Hironaka.Stage

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- "`Π^*_{(X,I,E)} I = 𝒪_{X_r}(−∑_{j=s}^{r−1} Π^*_{r,j+1} F_j)`" [Kol07, 72]: along the `BMO_1`
part, the order reduction functor for marked ideals at mark `1` on any marked triple of mark `1`,
the pull-back of the ideal to the end result is the product of the exceptional divisors of the
steps pulled back along the later steps; `I_r = 𝒪` since `max-ord I_r < 1`. -/
theorem BMO_one_comap_composite_eq_prod (T : MarkedTriple k) (hT : T.BMOClassFree 1) :
    T.I.comap ((BMO_m 1 k).seq T hT).composite =
      ∏ j : Fin ((BMO_m 1 k).seq T hT).length,
        (((BMO_m 1 k).seq T hT).exceptionalAt j).comap
          (((BMO_m 1 k).seq T hT).stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) := by
  have hseq := (BMO_m 1 k).isOrderGeSeq T hT
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hm : T.m = 1 := hT.2
  -- the marked transform is an exact quotient at every step: `F_{j+1}^m ∣ π_j^* I_j` (the order
  -- condition of Definition 66)
  have hdvd : ∀ i : Fin ((BMO_m 1 k).seq T hT).length,
      ((BMO_m 1 k).seq T hT).exceptionalAt i ^ T.m ∣
        (((BMO_m 1 k).seq T hT).markedTransformSeq T.I T.m i.castSucc).comap
          (((BMO_m 1 k).seq T hT).step i) :=
    fun i => exceptionalAt_pow_dvd_comap_step_of_leOrdAlong (T.X.left ↘ Spec (.of k)) n _ hseq.1 i _
      (IsOrderGeSeq.leOrdAlong hseq i)
  -- `I_r = 𝒪`: Theorem 69 (1) at mark `1`
  have hmax : ((BMO_m 1 k).seq T hT).markedTransformSeq T.I T.m (Fin.last _) = ⊤ := by
    have h1 : (((BMO_m 1 k).seq T hT).markedTransformSeq T.I T.m (Fin.last _)).maxOrd < 1 := by
      have h := dimFreeBMO_maxOrd_lt stage0 1 T hT
      rw [Nat.cast_one] at h
      exact h
    exact Hironaka.BD.eq_top_of_maxOrd_le_zero _
      ((Order.lt_one_iff.mp h1).le.trans Nat.cast_zero.symm.le)
  have h := comap_composite_eq_markedTransformSeq_last_mul_prod _ T.I T.m hdvd
  rw [hmax, ← one_eq_top, one_mul] at h
  rw [h]
  exact Finset.prod_congr rfl fun j _ => by rw [hm, pow_one]

/-- Clause (2) of [Kol07, Theorem 35]: the pull-back of `I` along `BP T` is the ideal sheaf of an
effective divisor supported on a simple normal crossing family. The disjoining part contributes
only `π^* I`, the ideal of the disjoined triple on which the `BMO_1` part runs [Kol07, 72], and the
pull-back along the `BMO_1` part is the explicit product `∏_j Π_{r,j+1}^* F_j` of
`BMO_one_comap_composite_eq_prod`, the ideal sheaf of an snc divisor by
`isIdealOfSncDivisor_prod_comap_exceptionalAt`; the two isomorphisms in the definition (the cast of
the concatenation and the deletion of the empty blow-ups) transport the property
(`IsIdealOfSncDivisor.comap_of_smooth`). -/
theorem BP_isIdealOfSncDivisor (T : Triple k) :
    IsIdealOfSncDivisor (T.I.comap (BP T).composite) := by
  set dT := disjoinedTriple T with hdT
  set S₀ := disjoinSeq T.E with hS₀
  set R := (BMO_m 1 k).seq ⟨dT, 1⟩ ⟨le_rfl, rfl⟩ with hR
  have hRseq : R.IsOrderGeSeq (dT.X.left ↘ Spec (.of k)) dT.I 1 dT.E :=
    (BMO_m 1 k).isOrderGeSeq ⟨dT, 1⟩ ⟨le_rfl, rfl⟩
  obtain ⟨n, hn⟩ := dT.smoothOfRelativeDimension
  -- the explicit product on the end result of the `BMO_1` part is the ideal of an snc divisor
  have hK : IsIdealOfSncDivisor (∏ j : Fin R.length,
      (R.exceptionalAt j).comap (R.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))) :=
    isIdealOfSncDivisor_prod_comap_exceptionalAt ⟨dT, 1⟩ R hRseq
  have hprod : dT.I.comap R.composite = ∏ j : Fin R.length,
      (R.exceptionalAt j).comap (R.stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) :=
    BMO_one_comap_composite_eq_prod ⟨dT, 1⟩ ⟨le_rfl, rfl⟩
  -- `Π^* I` on the concatenation, then on the erased sequence
  have e := composite_concat S₀ R
  have hSR : T.I.comap (S₀.concat R).composite =
      (∏ j : Fin R.length,
        (R.exceptionalAt j).comap (R.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))).comap
        (eqToHom (last_concat S₀ R)) := by
    rw [e, comap_comp, comap_comp]
    change (dT.I.comap R.composite).comap (eqToHom (last_concat S₀ R)) = _
    rw [hprod]
    rfl
  have hBP : T.I.comap (BP T).composite =
      ((∏ j : Fin R.length,
        (R.exceptionalAt j).comap (R.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))).comap
          (eqToHom (last_concat S₀ R))).comap (S₀.concat R).eraseEmptyLastHom := by
    change T.I.comap (S₀.concat R).eraseEmpty.composite = _
    rw [← eraseEmptyLastHom_comp_composite, comap_comp, hSR]
  rw [hBP]
  -- the smooth structure maps of the end results
  have hsmR : Smooth (R.composite ≫ (dT.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := n) hRseq.1 (Fin.last _)
  have hsmε : Smooth (eqToHom (last_concat S₀ R)) := Hironaka.BD.smooth_eqToHom _
  have hsmSR : Smooth (eqToHom (last_concat S₀ R) ≫ R.composite ≫ (dT.X.left ↘ Spec (.of k))) :=
    MorphismProperty.comp_mem _ _ _ hsmε hsmR
  exact @IsIdealOfSncDivisor.comap_of_smooth k _ _ _ _ _ hsmSR (S₀.concat R).eraseEmptyLastHom
    inferInstance _
    (@IsIdealOfSncDivisor.comap_of_smooth k _ _ _ _ (R.composite ≫ (dT.X.left ↘ Spec (.of k))) hsmR
      (eqToHom (last_concat S₀ R)) hsmε _ hK)

end Hironaka.Sequence
