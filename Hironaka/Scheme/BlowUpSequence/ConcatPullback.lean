/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pulling back a concatenation

The pullback of a concatenation is the concatenation of the pullbacks,
`h^*(S · T) = (h^*S) · (h_r^* T)`, where `h_r` is the lift of `h` to the last stage
(`pullbackLastHom`: `pullbackStageHom` of `Hironaka/Scheme/BlowUpSequence/Pullback.lean` at the last
index, typed at `S.last` through the identification `pullbackStageIdx_last` of the last indices).
This is the bookkeeping behind
[Kol07, 104, Step 2.3]: the functoriality of a sequence assembled from rounds follows from the
functoriality of each round, with the pullback of [Kol07, 30.1].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The lift of `h` to the last stage of the pulled-back sequence [Kol07, 30.1], typed at the last
stages (`pullbackStageHom` at the last index through the identification `pullbackStageIdx_last`). -/
noncomputable def Scheme.BlowUpSequence.pullbackLastHom (S : BlowUpSequence X)
    (h : Y ⟶ X) : (S.pullback h).last ⟶ S.last :=
  eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm) ≫
    S.pullbackStageHom h (Fin.last _)

/-- The lift at the last stage of the empty sequence is `h`. -/
theorem pullbackLastHom_nil (h : Y ⟶ X) : (nil X).pullbackLastHom h = h := by
  have key : ∀ p : Y = Y, eqToHom p ≫ h = h := fun p => by rw [eqToHom_refl, Category.id_comp]
  exact key _

/-- The lift at the last stage of a `cons` is the tail's lift along `blowUpMap h D`
(definitional). -/
theorem pullbackLastHom_cons (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (h : Y ⟶ X) : (cons X D rest).pullbackLastHom h = rest.pullbackLastHom (Scheme.Hom.blowUpMap h
        D) :=
  rfl

/-- The pullback of a concatenation is the concatenation of the pullbacks, the second along the
lift of `h` to the last stage [Kol07, 30.1 and Definition 29]. -/
theorem pullback_concat : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    {Y : Scheme.{u}} (h : Y ⟶ X),
    (S.concat T).pullback h = (S.pullback h).concat (T.pullback (S.pullbackLastHom h))
  | _, nil _, T, _, h =>
    (congrArg (fun g => T.pullback g) (pullbackLastHom_nil h)).symm
  | _, cons _ D rest, T, _, h => by
    change cons _ (D.comap h) ((rest.concat T).pullback (Scheme.Hom.blowUpMap h D)) =
      cons _ (D.comap h) ((rest.pullback (Scheme.Hom.blowUpMap h D)).concat
        (T.pullback ((cons _ D rest).pullbackLastHom h)))
    rw [pullback_concat rest T (Scheme.Hom.blowUpMap h D)]
    rfl

end AlgebraicGeometry
