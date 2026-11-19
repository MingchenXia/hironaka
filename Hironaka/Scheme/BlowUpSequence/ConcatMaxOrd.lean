/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The final maximal order along a concatenation

`weakTransformSeq_concat_last` (`Hironaka/Scheme/BlowUpSequence/ConcatApi.lean`) identifies the
final weak transform along `S.concat T` with the final weak transform along `T` of the final weak
transform along `S`, up to the identification `eqToHom (last_concat S T)` of the last stages. The
maximal order does not see that identification (`maxOrd_comap_eqToHom`), so the two maximal orders
agree (`maxOrd_weakTransformSeq_concat_last`). This is what the maximal contact case of the proof of
Theorem 103 needs to read the conclusion `max-ord I_r < m` for the boundary-clearing sequence
followed by the restriction to the hypersurface from the latter alone [Kol07, 104, Step 2.2].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

/-- The maximal order of an ideal sheaf is unchanged by the inverse image along the
identification of two equal schemes. -/
theorem maxOrd_comap_eqToHom {X Y : Scheme.{u}} (h : X = Y) (J : Y.IdealSheafData) :
    (J.comap (eqToHom h)).maxOrd = J.maxOrd := by
  subst h
  rw [eqToHom_refl, Scheme.IdealSheafData.comap_id]

/-- The maximal order of the final weak transform along a concatenation is that along the second
part of the weak transform along the first (the `eqToHom` of `last_concat` does not change
`max-ord`). -/
theorem maxOrd_weakTransformSeq_concat_last {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (J : X.IdealSheafData) :
    ((S.concat T).weakTransformSeq J (Fin.last _)).maxOrd =
      (T.weakTransformSeq (S.weakTransformSeq J (Fin.last _)) (Fin.last _)).maxOrd := by
  rw [weakTransformSeq_concat_last]
  exact maxOrd_comap_eqToHom (last_concat S T) _

end AlgebraicGeometry
