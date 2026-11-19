/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.MaximalContact.Restrict
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Hypersurfaces of maximal contact under smooth pull-back

The remark closing [Kol07, Theorem 103, Step 2.3], that "the functoriality package is local" (with
[Kol07, 34.1]): for a smooth `h : Y → X`, `h⁻¹(H)` is a smooth hypersurface of maximal contact for
`h^*I`. The maximal contact comes from `MC(h^*I) = h^*MC(I)` ([Kol07, Lemma 74 (4)],
`MC_comap_of_smooth`), and the smooth divisor pulls back to a smooth divisor: the one-member
family `(∅, H)` is simple normal crossing, its inverse image is simple normal crossing
(`isSnc_comap_of_smooth`), and the members of a simple normal crossing family are smooth divisors
(`isSmoothDivisor_of_snc_data`).

Both statements are used in Step 3 of the proof of [Kol07, Theorem 103], the globalization
(`Hironaka/Resolution/Algebraic/OrderReduction/Step3Globalization.lean`, `Step3Clauses.lean`,
`Step3Cover.lean`), where the functor is pulled back along smooth morphisms.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- The inverse image of a hypersurface of maximal contact (in the static sense of
[Kol07, Theorem 80 (1)]) under a smooth morphism is one for the pulled-back ideal, since `MC`
commutes with smooth pull-back ([Kol07, Lemma 74 (4)]). -/
theorem isMaximalContact_comap_of_smooth (h : Y ⟶ X) [Smooth h] {I : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (hle : IsMaximalContact f I m H) :
    IsMaximalContact (h ≫ f) (I.comap h) m (H.comap h) := by
  unfold IsMaximalContact at hle ⊢
  rw [MC_comap_of_smooth f n h I m]
  exact comap_mono h hle

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Snc

open AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The inverse image of a smooth divisor under a smooth morphism of smooth `k`-schemes is a smooth
divisor. -/
theorem isSmoothDivisor_comap_of_smooth [CharZero k] (f : X ⟶ Spec (.of k)) [Smooth f] (h : Y ⟶ X)
    [Smooth h]
    {H : X.IdealSheafData} (hH : IsSmoothDivisor H) : IsSmoothDivisor (H.comap h) := by
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk f x
  have hsnc : (((DivisorFamily.empty X).append H).comap h).IsSnc :=
    isSnc_comap_of_smooth f h (isSnc_append_empty_of_isSmoothDivisor hreg hH)
  have hregY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := fun y =>
    isRegularLocalRing_stalk (h ≫ f) y
  exact isSmoothDivisor_of_snc_data (((DivisorFamily.empty X).append H).comap h).component hsnc.1
    (fun y => hsnc.2 y) hregY (toLex (Sum.inr PUnit.unit))

end Hironaka.Snc
