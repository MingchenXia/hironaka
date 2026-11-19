/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquivBridge
import Hironaka.Resolution.Algebraic.Tuning.Corollary101
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Maximal contact is unchanged by tuning: `MC_s(W_s(I)) = MC_m(I)`

Step 2.2 of [Kol07, 104] (the amplified Step 2 of the proof of Theorem 103) replaces `I` by `W(I)`,
so that `I` may be assumed MC-invariant, and does "not pick a new hypersurface of maximal contact"
but uses only the birational transforms `H_{r(s)}` of the old ones — the Warning of [Kol07, 104]:
after a blow-up one should "stick with the birational transforms of the old ones". The old
hypersurface stays one of maximal contact for the tuned ideal because tuning does not change the
maximal-contact ideal: [Kol07, Proposition 99 (4)], `MC_s(W_s(I)) = W_1(I) = MC_m(I)` for
`m = max-ord I ≥ 1` and `s ≥ 1`. This is `RegularCoords.MC_W` of `Hironaka.Local` at the stalk of
every closed point, lifted to the sheaf exactly as
`Hironaka.Resolution.Algebraic.Tuning.Corollary101` lifts Proposition 99 (5) (`isMCInvariant_W`):
the stalks of `MC` and of `W` are their counterparts in regular coordinates (`stalkIdeal_MC`,
`stalkIdeal_W`), and an equality of ideal sheaves on a Jacobson scheme is checked at the closed
points (`le_of_forall_stalkIdeal_le_of_isClosed`). -/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

open IsLocalRing

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (m : ℕ)

include n in
/-- [Kol07, Proposition 99 (4)]: for `m = max-ord I ≥ 1` and `s ≥ 1`, `MC_s(W_s(I)) = MC_m(I)`;
`RegularCoords.MC_W` at every closed point. -/
theorem MC_W (hI : I.maxOrd = m) (hm : 1 ≤ m) {s : ℕ} (hs : 1 ≤ s) :
    MC f (W f I m s) s = MC f I m := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have key : ∀ p : X, IsClosed ({p} : Set X) →
      (MC f (W f I m s) s).stalkIdeal p = (MC f I m).stalkIdeal p := by
    intro p hp
    let _ := f.stalkAlgebra p
    let _ := f.stalkAlgebraRat p
    have := isRegularLocalRing_stalk f p
    obtain ⟨d, c, hk, hs'⟩ := exists_regularCoords_stalk_of_isAlgebraic f n p
      (isAlgebraic_residueField_of_isClosed f n hp)
    have hIp := ord_stalkIdeal_le_of_maxOrd_eq I m hI p
    rw [stalkIdeal_MC f n (W f I m s) s p c hk hs', stalkIdeal_W f n I m s p c hk hs',
      stalkIdeal_MC f n I m p c hk hs']
    exact c.MC_W hm hIp hs
  exact le_antisymm (le_of_forall_stalkIdeal_le_of_isClosed fun p hp => (key p hp).le)
    (le_of_forall_stalkIdeal_le_of_isClosed fun p hp => (key p hp).ge)

include n in
/-- At the tuning parameter `s = s(m)` (`tuningParam`): the tuned ideal `W_{s(m)}(I)` has the
maximal-contact ideal of `I`. -/
theorem MC_W_tuningParam (hI : I.maxOrd = m) (hm : 1 ≤ m) :
    MC f (W f I m (tuningParam m)) (tuningParam m) = MC f I m :=
  MC_W f n I m hI hm (one_le_tuningParam m)

include n in
/-- "We do not pick a new hypersurface of maximal contact" (Step 2.2 of [Kol07, 104], and its
Warning): a hypersurface of maximal contact for `(I, m)` is one for the tuned `(W_{s(m)}(I), s(m))`.
-/
theorem isMaximalContact_W_tuningParam (hI : I.maxOrd = m) (hm : 1 ≤ m) {H : X.IdealSheafData}
    (hle : IsMaximalContact f I m H) :
    IsMaximalContact f (W f I m (tuningParam m)) (tuningParam m) H := by
  unfold IsMaximalContact at hle ⊢
  rwa [MC_W_tuningParam f n I m hI hm]

end AlgebraicGeometry.Scheme.IdealSheafData
