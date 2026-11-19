/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step2Separation
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.IdealSheaf.Order.Smooth
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The round parameters under smooth surjective pull-back

The first clause of [Kol07, 34.1] ("`B` commutes with every smooth surjection `h`") for the loop
variables of Steps 1 and 2 of the proof of [Kol07, Theorem 107]: the round order
`d = max-ord N(I)` (`roundOrder`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`) and the separation
order `s = max-ord_{cosupp(I, m)} N(I)` (`sepOrder`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`) of a marked triple are
unchanged by a smooth surjective pull-back. The split pulls back (`N(h^* I) = h^* N(I)`,
`nonmonomialPart_comap`), the order of a smooth pull-back at a point is the order at the image
(`ord_comap_of_smooth`), and a surjection preserves maxima (`maxOrd_comap_of_surjective`,
`maxOrdAlong_comap_preimage_of_surjective`). Consequently the loops of Steps 1 and 2 on `Y` run in
step with those on `X` (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/LoopFunctorial.lean`).
Not in the sources as such.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData

namespace Hironaka.BMO

section MaxOrd

variable {X Y : Scheme.{u}}

/-- The maximal order of a smooth surjective pull-back is the maximal order
(`maxOrd_comap_le_of_smooth` and `maxOrd_le_maxOrd_comap_of_surjective`). -/
theorem maxOrd_comap_of_surjective (J : X.IdealSheafData) (h : Y ⟶ X) [Smooth h]
    (hs : Function.Surjective h) : (J.comap h).maxOrd = J.maxOrd :=
  le_antisymm (Hironaka.BO.maxOrd_comap_le_of_smooth h J)
    (Hironaka.BO.maxOrd_le_maxOrd_comap_of_surjective h hs J)

/-- The maximal order of a smooth surjective pull-back along the preimage of a set is the maximal
order along the set. -/
theorem maxOrdAlong_comap_preimage_of_surjective (J : X.IdealSheafData) (h : Y ⟶ X) [Smooth h]
    (hs : Function.Surjective h) (Z : Set X) :
    (J.comap h).maxOrdAlong (h ⁻¹' Z) = J.maxOrdAlong Z := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.maxOrdAlong_le_iff]
    intro y hy
    rw [Scheme.IdealSheafData.ord_comap_of_smooth]
    exact Scheme.IdealSheafData.le_maxOrdAlong (I := J) hy
  · rw [Scheme.IdealSheafData.maxOrdAlong_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hs x
    rw [← Scheme.IdealSheafData.ord_comap_of_smooth J h y]
    exact Scheme.IdealSheafData.le_maxOrdAlong (I := J.comap h) (show y ∈ h ⁻¹' Z from hx)

end MaxOrd

section Parameters

variable {k : Type u} [Field k] [CharZero k]

/-- The round parameter `d = max-ord N(I)` of Step 1 is preserved by smooth surjective pull-back:
the split pulls back (`nonmonomialPart_comap`) and a surjection preserves the maximal order. -/
theorem roundOrder_of_isPullbackOf (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) : roundOrder T' = roundOrder T := by
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap h :=
    nonmonomialPart_comap T.toTriple h hp.1
  unfold roundOrder
  rw [hN, maxOrd_comap_of_surjective _ h hs]

/-- The separation parameter `s` of Step 2 is preserved by smooth surjective pull-back: the
cosupport and the nonmonomial part pull back. -/
theorem sepOrder_of_isPullbackOf (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) : sepOrder T' = sepOrder T := by
  obtain ⟨hpb, hm⟩ := hp
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap h :=
    nonmonomialPart_comap T.toTriple h hpb
  have hset : {y | (T'.m : ℕ∞) ≤ T'.I.ord y} = h ⁻¹' {x | (T.m : ℕ∞) ≤ T.I.ord x} := by
    ext y
    change ((T'.m : ℕ∞) ≤ T'.I.ord y) ↔ ((T.m : ℕ∞) ≤ T.I.ord (h y))
    rw [hm, hpb.2.1, Scheme.IdealSheafData.ord_comap_of_smooth]
  unfold sepOrder
  rw [hN, hset, maxOrdAlong_comap_preimage_of_surjective _ h hs]

end Parameters

end Hironaka.BMO
