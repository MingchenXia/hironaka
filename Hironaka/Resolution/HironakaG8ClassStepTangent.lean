import Hironaka.Resolution.HironakaG8ClassStepHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Case T of (O<) and the composition of (O<) from its cases (G8C lane, run 0080, round 5; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-tangent.tex`.  Notes: this lane's `REPORT-r5.md`; lane G11B's
`FALLBACK-DECISION-ANALYSIS.md` §2 (Lemma M, Case N, Case T); inbox I-1417, I-1422 (+ C-0001) for the shapes agreed with lane G8B.

The pointwise order comparison (O<) (`HironakaG8ClassStepHistory.OrdAgreeBelowAt`) at a cosupport point `x` of two equivalent
marked ideals splits into three cases (G11B §2): order `= d` (lane G8B's Lemma M (i)); order `> d` with a member through `x` tangent
to the carrier (Case T, BM08 Step I.B with that member cut: `J = 𝔞 + 𝓘_H^d`); order `> d` with no tangent member (lane G8B's
Case N, with the directrix (T') making tangency symmetric).  This module proves the order-arithmetic parts, pointwise:

* **`mem_cosupport_sumIdeal_idealPow_iff`**: the `ℰ`-term `𝓘_H^d` of a member tangent to the carrier does not change the
  cosupports of the marks `e ≤ 2d` at the point (the last step of Case T);
* **`ordAgreeBelowAt_of_tangent_sumIdeal`**: Case T modulo the order equality of the cut pair `J_P`, `J_Q` (the domain P1 for
  Step I.B with one member cut — not proved here, see `REPORT-r5.md`);
* **`ordAgreeBelowAt_of_not_mem_cosupport_succ`**: the order-`= d` case (both orders equal the mark);
* **`ordAgreeBelowAt_of_cases`**: (O<) at `x` from the conclusions at `x` of Lemma M (i), the directrix (T'), Case N and Case T,
  in exactly the shapes agreed on I-1422 (pure logic; each input is an explicit hypothesis at the point).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ClassStepTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.MarkedIdeals Hironaka.BlowupTowers
open Hironaka.HironakaG8ClassStepHistory (OrdAgreeBelowAt)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (hol_of_isCoherent)

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The `ℰ`-term of a tangent member does not change the orders below `2d`**: if the ideal of `H` vanishes to order `≥ 2`
along `N` at `x` (the carrier is tangent to `H` at `x`), then for every mark `e ≤ 2d` the cosupports of `𝔞 + 𝓘_H^d` and of `𝔞`
at `x` agree. -/
theorem mem_cosupport_sumIdeal_idealPow_iff {N H : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {d : ℕ} {x : M}
    (hx : x ∈ cosupport n N (vanishingIdeal (n := n) H) 2) {e : ℕ} (he : e ≤ 2 * d) :
    x ∈ cosupport n N (sumIdeal 𝔞 (idealPow (vanishingIdeal (n := n) H) d)) e ↔ x ∈ cosupport n N 𝔞 e := by
  rw [IdealOrderArithmetic.cosupport_sumIdeal h𝔞 (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) e]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact cosupport_anti he (IdealOrderArithmetic.cosupport_subset_cosupport_idealPow 2 d hx)

universe u

section Point

variable {X : CMfd.{u} n}

/-- **Case T modulo the cut pair** (lane G11B's Case T, last step): if a member `H` through `x` is tangent to BOTH carriers at
`x` (its ideal vanishes to order `≥ 2` along them) and the cut pairs `J_P = P.ideal + 𝓘_H^d`, `J_Q = Q.ideal + 𝓘_H^d` (same mark
`d`) have the same cosupports of every mark `e ≤ 2d` at `x`, then (O<) holds at `x`. -/
theorem ordAgreeBelowAt_of_tangent_sumIdeal {P Q : MarkedIdeal n X} (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) {H : Set X} {x : X} (hTP : x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2)
    (hTQ : x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2)
    (hJ : ∀ e ≤ 2 * P.d, x ∈ cosupport n P.N (sumIdeal P.ideal (idealPow (vanishingIdeal (n := n) H) P.d)) e ↔
      x ∈ cosupport n Q.N (sumIdeal Q.ideal (idealPow (vanishingIdeal (n := n) H) P.d)) e) :
    OrdAgreeBelowAt P Q x := by
  intro e he
  rw [← mem_cosupport_sumIdeal_idealPow_iff (hol_of_isCoherent hIP) hTP he,
    ← mem_cosupport_sumIdeal_idealPow_iff (hol_of_isCoherent hIQ) hTQ he]
  exact hJ e he

/-- **The order-`= d` case**: at a common cosupport point where neither order exceeds the mark, (O<) holds (both orders equal
the mark). -/
theorem ordAgreeBelowAt_of_not_mem_cosupport_succ {P Q : MarkedIdeal n X} (hd : Q.d = P.d) {x : X}
    (hxP : x ∈ P.cosupp) (hxQ : x ∈ Q.cosupp) (hP : x ∉ cosupport n P.N P.ideal (P.d + 1))
    (hQ : x ∉ cosupport n Q.N Q.ideal (P.d + 1)) : OrdAgreeBelowAt P Q x := by
  intro e _
  by_cases hed : e ≤ P.d
  · have hedQ : e ≤ Q.d := by omega
    exact ⟨fun _ => cosupport_anti hedQ hxQ, fun _ => cosupport_anti hed hxP⟩
  · have hed' : P.d + 1 ≤ e := by omega
    exact ⟨fun h => absurd (cosupport_anti hed' h) hP, fun h => absurd (cosupport_anti hed' h) hQ⟩

/-- **(O<) from its cases** (the composition agreed on I-1422 C-0001), at one point `x` of both cosupports (same mark):
* `hMi` — lane G8B's Lemma M (i) at `x`: the order exceeds the mark for one iff for the other;
* `hT'` — lane G8B's directrix (T') at `x`: if the order of `P` exceeds the mark, each member through `x` is tangent to `P.N`
  iff it is tangent to `Q.N` (order form);
* `hN` — lane G8B's Case N at `x`: if no member through `x` is tangent to either carrier, all cosupports at `x` agree;
* `hT` — Case T at `x`: if some member through `x` is tangent to both carriers, (O<) holds.
Each is the conclusion at `x` of a theorem with the standing hypotheses of `HironakaG8ClassStepHistory.ordAgreeBelowAt_stage`'s
`hO`; this lemma is the case split (pure logic). -/
theorem ordAgreeBelowAt_of_cases {P Q : MarkedIdeal n X} (hd : Q.d = P.d) {x : X} (hxP : x ∈ P.cosupp)
    (hxQ : x ∈ Q.cosupp)
    (hMi : x ∈ cosupport n P.N P.ideal (P.d + 1) ↔ x ∈ cosupport n Q.N Q.ideal (P.d + 1))
    (hT' : x ∈ cosupport n P.N P.ideal (P.d + 1) → ∀ H ∈ P.E, x ∈ H →
      (x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2 ↔ x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2))
    (hN : (∀ H ∈ P.E, x ∈ H → x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2 ∧
      x ∉ cosupport n Q.N (vanishingIdeal (n := n) H) 2) →
        ∀ e, x ∈ cosupport n P.N P.ideal e ↔ x ∈ cosupport n Q.N Q.ideal e)
    (hT : ∀ H ∈ P.E, x ∈ H → x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2 →
      x ∈ cosupport n Q.N (vanishingIdeal (n := n) H) 2 → OrdAgreeBelowAt P Q x) :
    OrdAgreeBelowAt P Q x := by
  by_cases hs : x ∈ cosupport n P.N P.ideal (P.d + 1)
  · by_cases hcase : ∃ H ∈ P.E, x ∈ H ∧ x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2
    · obtain ⟨H, hH, hxH, hTP⟩ := hcase
      exact hT H hH hxH hTP ((hT' hs H hH hxH).mp hTP)
    · have hcase' : ∀ H ∈ P.E, x ∈ H → x ∉ cosupport n P.N (vanishingIdeal (n := n) H) 2 :=
        fun H hH hxH hTP => hcase ⟨H, hH, hxH, hTP⟩
      have hall := hN fun H hH hxH => ⟨hcase' H hH hxH, fun hTQ => hcase' H hH hxH ((hT' hs H hH hxH).mpr hTQ)⟩
      exact fun e _ => hall e
  · exact ordAgreeBelowAt_of_not_mem_cosupport_succ hd hxP hxQ hs (fun h => hs (hMi.mpr h))

end Point

end

end Hironaka.HironakaG8ClassStepTangent
