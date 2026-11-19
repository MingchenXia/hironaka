import Hironaka.Resolution.HironakaG8P1ArcTower
import Hironaka.Resolution.HironakaG8LocalHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Port P1 for the relations of the (B') induction (G8B lane, run 0080)

Blueprint: `hironaka-g8-p1-normalized-order.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §2, port P1.

BM08 Theorem 6.1 for different carriers of equal dimension (`HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv`)
for the relations G11B's `ClassFunctorialFor` is instantiated with:

* `normalized_order_eq_of_projEquiv` — lane G8's `ProjEquiv` (BM97's `s(i,ii)`), `SameCarrierDim`;
* **`normalized_order_eq_of_locWPEquiv`** — lane G8's local relation `LocWPEquiv` (the `Eqv` of the (B') plan);
* **`towerOrdAgree_of_projEquiv`** — with a common mark, the ordinary orders agree on the cosupport along every common
  multiple test blowup (lane G8's `TowerOrdAgree`, now for carriers that differ): the input of G8's entries E1–E3.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1NormalizedOrder

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8ProjEquiv
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)

noncomputable section

section General

variable {n : ℕ} {X : CMfd.{u} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **BM08 Theorem 6.1 for `s(i,ii)`-equivalence, carriers of equal dimension** (they may differ). -/
theorem normalized_order_eq_of_projEquiv (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp) :
    B.d * ordinaryTraceOrder A.N A.ideal x = A.d * ordinaryTraceOrder B.N B.ideal x := by
  have hxB : x ∈ B.cosupp := h.wEquiv.cosupp_eq ▸ hx
  exact HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv A B hA hB x hx hxB h.projectionTest_wEquiv hdim

/-- **BM08 Theorem 6.1 for the local relation `LocWPEquiv`, carriers of equal dimension** (port P1). -/
theorem normalized_order_eq_of_locWPEquiv (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp) :
    B.d * ordinaryTraceOrder A.N A.ideal x = A.d * ordinaryTraceOrder B.N B.ideal x :=
  normalized_order_eq_of_projEquiv (LocEquiv.projEquiv h) hA hB hdim hx

end General

section Tower

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **Equal orders along towers for carriers of equal dimension**: `s(i,ii)`-equivalent marked ideals with the same mark
and the same carrier dimensions on the cosupport have equal ordinary orders on the cosupport along every common multiple
test blowup (lane G8's `TowerOrdAgree`, without `B.N = A.N`). -/
theorem towerOrdAgree_of_projEquiv (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) : TowerOrdAgree A B := by
  intro Y T hT y hy
  have rA := record_towerHistory_refl A T
  have rB : record (withBoundary B A.E) (towerHistory (.refl : History X A.E X A.E) T) = geoTransformAlong B T :=
    (record_towerHistory_refl (withBoundary B A.E) T).trans
      (congrArg (fun M => geoTransformAlong M T) (withBoundary_eq h.E_eq))
  have hH : IsTest A (towerHistory (.refl : History X A.E X A.E) T) := (isTest_towerHistory_refl_iff A T).mpr hT
  have hP := h.record (towerHistory (.refl : History X A.E X A.E) T) hH (noExc_towerHistory .refl noExc_refl T)
  rw [rA, rB] at hP
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hT
  have hdimT := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed h.wEquiv
    hdim T hT
  have hAT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT
  have hBT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
  have h1 := normalized_order_eq_of_projEquiv hP hAT hBT hdimT hy
  rw [d_geoTransformAlong, d_geoTransformAlong, hd] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

end Tower

end

end Hironaka.HironakaG8P1NormalizedOrder
