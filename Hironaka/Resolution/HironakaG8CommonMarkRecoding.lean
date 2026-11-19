import Hironaka.Resolution.HironakaG8ProjEquiv
import Hironaka.Resolution.HironakaG8LogHistoryPrefixes

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Common-multiple mark recodings along mixed histories (G8 lane, run 0080, round 2; G8-3H-D03)

Blueprint: `hironaka-g8-resume-common-mark-recoding.tex`.

Two marked ideals `M₁`, `M₂` with positive marks `d₁`, `d₂` and the same boundary are compared by recoding both to a
common multiple `L` of the marks: `Mᵢ ↦ Mᵢ^{eᵢ}`, `eᵢ = L / dᵢ` (whole powers of the ORIGINAL ideals, `powerMarked`).  This
module proves, from the original whole-power transport along the genuine mixed histories
(`HironakaActualMixedTestPowerNormalization.original_power_normalization`):

* **the recoding dictionary at every prefix** (`RecodingDictionary`, `recodingDictionary_allPrefixes`): the tests of
  `M` and `M^e` agree, the record of `M^e` is restricted-equivalent on the proper carrier to the `e`-th power of the record
  of `M` (whole ideals), the carrier, boundary and cosupport are retained, the mark is `d e`, the ordinary order of the
  record of `M^e` is `e` times that of the record of `M` on the proper carrier, and the clocks (boundary length, dimension)
  are those of the history;
* **`two_mark_common_multiple_recoding`** (D03): for two explicit positive marks and any positive common multiple `L`,
  both recodings have the SAME mark `L` (`dᵢ eᵢ = L`, `eᵢ ≥ 1`), keep carrier and boundary, are mixed-test equivalent to
  the originals, and carry the recoding dictionary at every prefix of every common test history;
* **the normalized relation becomes an equality after recoding**: `common_multiple_recoding_order_eq` (mixed-test
  equivalent, same carrier: along every common test history, at every cosupport point, the ordinary orders of the two
  recoded records agree), `common_multiple_recoding_order_eq_of_projEquiv` (the same for `s(i,ii)` along histories
  without exceptional actions), and the cosupports agree; `recoded_order_eq_of_normalized`, `recoded_order_arith`.

Helpers: `ordinaryTraceOrder_eq_of_restrictEquiv`, `ordinaryTraceOrder_record_powerMarked`,
`recodingDictionary_of_isTest`.  Sorry-free.  Universe `0`.  Import discipline: no import of
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CommonMarkRecoding

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.NonmonomialOrderLocal (nmOrd nmOrd_congr)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordGe_ordinaryTraceMarked_eq_cosupport)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_cosupp
  powerMarked_isInvDomain)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8MixedOrderInvariance (ordinaryTraceOrder_idealPow
  mixedEquiv_normalizedOrder_record)
open Hironaka.HironakaG8ProjEquiv
open Hironaka.HironakaG8LogHistoryPrefixes (allPrefixes_mono isTest_allPrefixes)

noncomputable section

/-! ### Orders of records of powers -/

section Order

variable {m : ℕ} {Y : CMfd.{0} m}

/-- **Restricted-equivalent marked ideals have the same ordinary orders** (coherent ideals). -/
theorem ordinaryTraceOrder_eq_of_restrictEquiv {P Q : MarkedIdeal m Y} (h : RestrictEquiv P Q)
    (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent) (y : Y) :
    ordinaryTraceOrder P.N P.ideal y = ordinaryTraceOrder Q.N Q.ideal y := by
  unfold ordinaryTraceOrder
  refine nmOrd_congr fun q => ?_
  rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ hP, ordGe_ordinaryTraceMarked_eq_cosupport _ _ hQ, ← h.N_eq]
  exact ⟨fun hy => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.ge q hy,
    fun hy => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.le q hy⟩

end Order

section Recoding

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The order of the record of a power** along a test history: `e` times the order of the record, on the proper
carrier. -/
theorem ordinaryTraceOrder_record_powerMarked {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ}
    (he : 1 ≤ e) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F) (hH : IsTest M H) {y : Y}
    (hy : y ∈ (record M H).N) :
    ordinaryTraceOrder (record (powerMarked M e) H).N (record (powerMarked M e) H).ideal y =
      e * ordinaryTraceOrder (record M H).N (record M H).ideal y := by
  obtain ⟨ht, hr⟩ := original_power_normalization M hM e he H hH
  have hd := record_isInvDomain M hM H hH
  have hp := record_isInvDomain (powerMarked M e) (powerMarked_isInvDomain M hM he) H ht
  rw [ordinaryTraceOrder_eq_of_restrictEquiv hr hp.isWellFormed.isCoherent
    (GermIdealPullbackCalculus.isCoherent_idealPow hd.isWellFormed.isCoherent e) y]
  exact ordinaryTraceOrder_idealPow hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent
    hd.isNonzeroAlongAt he hy

/-- **The recoding dictionary** of `M ↦ M^e` at a history `P`: tests, whole restricted power relation on the proper
carrier, retained carrier/boundary/cosupport, mark `d e`, orders scaled by `e`, clocks. -/
def RecodingDictionary (M : MarkedIdeal n X) (e : ℕ) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)}
    (P : History X M.E Y F) : Prop :=
  IsTest M P ∧ IsTest (powerMarked M e) P ∧
    RestrictEquiv (record (powerMarked M e) P) (powerMarked (record M P) e) ∧
    (record (powerMarked M e) P).N = (record M P).N ∧ (record (powerMarked M e) P).E = (record M P).E ∧
    (record (powerMarked M e) P).d = M.d * e ∧ (record (powerMarked M e) P).cosupp = (record M P).cosupp ∧
    (∀ y ∈ (record M P).N, ordinaryTraceOrder (record (powerMarked M e) P).N (record (powerMarked M e) P).ideal y =
      e * ordinaryTraceOrder (record M P).N (record M P).ideal y) ∧
    (record M P).E.length = M.E.length + length P ∧ m = n + projections P

theorem recodingDictionary_of_isTest {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (P : History X M.E Y F) (hP : IsTest M P) :
    RecodingDictionary M e P := by
  obtain ⟨ht, hr⟩ := original_power_normalization M hM e he P hP
  have hd := record_isInvDomain M hM P hP
  exact ⟨hP, ht, hr, rfl, rfl, rfl, hr.cosupp_eq.trans (powerMarked_cosupp (record M P) hd he),
    fun y hy => ordinaryTraceOrder_record_powerMarked M hM he P hP hy, (history_clocks M P).2,
    (history_clocks M P).1⟩

/-- **The recoding dictionary at every prefix** of every test history. -/
theorem recodingDictionary_allPrefixes {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F) (hH : IsTest M H) :
    AllPrefixes (fun {_ _ _} P => RecodingDictionary M e P) H :=
  allPrefixes_mono (fun Q hQ => recodingDictionary_of_isTest M hM he Q hQ) H (isTest_allPrefixes M H hH)

/-- **G8-3H-D03: common-multiple mark recodings for two explicit positive marks.**  For `M₁`, `M₂` in the native domain
with the same boundary, and a positive common multiple `L` of their marks, `eᵢ = L / dᵢ`: both recodings have the same
mark `L`, keep carrier and boundary, are mixed-test equivalent to the originals, and along every common test history the
recoding dictionaries hold at every prefix. -/
theorem two_mark_common_multiple_recoding {k₁ k₂ : ℕ} (M₁ M₂ : MarkedIdeal n X) (h₁ : IsInvDomain k₁ M₁)
    (h₂ : IsInvDomain k₂ M₂) (hE : M₂.E = M₁.E) {L : ℕ} (hL : 0 < L) (hL₁ : M₁.d ∣ L) (hL₂ : M₂.d ∣ L) :
    1 ≤ L / M₁.d ∧ 1 ≤ L / M₂.d ∧ M₁.d * (L / M₁.d) = L ∧ M₂.d * (L / M₂.d) = L ∧
      (powerMarked M₁ (L / M₁.d)).d = L ∧ (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)).d = L ∧
      (powerMarked M₁ (L / M₁.d)).N = M₁.N ∧ (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)).N = M₂.N ∧
      (powerMarked M₁ (L / M₁.d)).E = M₁.E ∧ (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)).E = M₁.E ∧
      MixedEquiv M₁ (powerMarked M₁ (L / M₁.d)) ∧
      MixedEquiv (withBoundary M₂ M₁.E) (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) ∧
      ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M₁.E Y F), IsTest M₁ H →
        IsTest (withBoundary M₂ M₁.E) H →
        AllPrefixes (fun {_ _ _} P => RecodingDictionary M₁ (L / M₁.d) P) H ∧
          AllPrefixes (fun {_ _ _} P => RecodingDictionary (withBoundary M₂ M₁.E) (L / M₂.d) P) H := by
  have h₂' : IsInvDomain k₂ (withBoundary M₂ M₁.E) := (withBoundary_eq hE).symm ▸ h₂
  have hd₁ : 0 < M₁.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₁.one_le_d
  have hd₂ : 0 < M₂.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₂.one_le_d
  have hm₁ : M₁.d * (L / M₁.d) = L := Nat.mul_div_cancel' hL₁
  have hm₂ : M₂.d * (L / M₂.d) = L := Nat.mul_div_cancel' hL₂
  have he₁ : 1 ≤ L / M₁.d := Nat.div_pos (Nat.le_of_dvd hL hL₁) hd₁
  have he₂ : 1 ≤ L / M₂.d := Nat.div_pos (Nat.le_of_dvd hL hL₂) hd₂
  refine ⟨he₁, he₂, hm₁, hm₂, hm₁, hm₂, rfl, rfl, rfl, rfl, mixedEquiv_powerMarked M₁ h₁ he₁,
    mixedEquiv_powerMarked (withBoundary M₂ M₁.E) h₂' he₂, fun H hH₁ hH₂ => ⟨?_, ?_⟩⟩
  · exact recodingDictionary_allPrefixes M₁ h₁ he₁ H hH₁
  · exact recodingDictionary_allPrefixes (withBoundary M₂ M₁.E) h₂' he₂ H hH₂

/-- Arithmetic of the normalization: `d₂ a = d₁ b` and `d₁ e₁ = d₂ e₂ = L > 0` give `e₁ a = e₂ b`. -/
theorem recoded_order_arith {d₁ d₂ e₁ e₂ L a b : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (h₁ : d₁ * e₁ = L)
    (h₂ : d₂ * e₂ = L) (h : d₂ * a = d₁ * b) : e₁ * a = e₂ * b := by
  have hpos : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc d₁ * d₂ * (e₁ * a) = (d₁ * e₁) * (d₂ * a) := by ring
    _ = (d₁ * e₁) * (d₁ * b) := by rw [h]
    _ = (d₂ * e₂) * (d₁ * b) := by rw [h₁, h₂]
    _ = d₁ * d₂ * (e₂ * b) := by ring

/-- **After common-mark recoding the normalized relation is an equality**, from a normalized order relation at a
point of the common cosupport of the records. -/
theorem recoded_order_eq_of_normalized {k₁ k₂ : ℕ} {M₁ M₂ : MarkedIdeal n X} (h₁ : IsInvDomain k₁ M₁)
    (h₂ : IsInvDomain k₂ M₂) (hE : M₂.E = M₁.E) {L : ℕ} (hL : 0 < L) (hL₁ : M₁.d ∣ L) (hL₂ : M₂.d ∣ L)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M₁.E Y F) (hH : IsTest M₁ H)
    (hHB : IsTest (withBoundary M₂ M₁.E) H) {y : Y} (hyN : y ∈ (record M₁ H).N)
    (hyNB : y ∈ (record (withBoundary M₂ M₁.E) H).N)
    (hn : M₂.d * ordinaryTraceOrder (record M₁ H).N (record M₁ H).ideal y =
      M₁.d * ordinaryTraceOrder (record (withBoundary M₂ M₁.E) H).N (record (withBoundary M₂ M₁.E) H).ideal y) :
    ordinaryTraceOrder (record (powerMarked M₁ (L / M₁.d)) H).N (record (powerMarked M₁ (L / M₁.d)) H).ideal y =
      ordinaryTraceOrder (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).N
        (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).ideal y := by
  have h₂' : IsInvDomain k₂ (withBoundary M₂ M₁.E) := (withBoundary_eq hE).symm ▸ h₂
  have hd₁ : 0 < M₁.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₁.one_le_d
  have hd₂ : 0 < M₂.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₂.one_le_d
  have he₁ : 1 ≤ L / M₁.d := Nat.div_pos (Nat.le_of_dvd hL hL₁) hd₁
  have he₂ : 1 ≤ L / M₂.d := Nat.div_pos (Nat.le_of_dvd hL hL₂) hd₂
  rw [ordinaryTraceOrder_record_powerMarked M₁ h₁ he₁ H hH hyN,
    ordinaryTraceOrder_record_powerMarked (withBoundary M₂ M₁.E) h₂' he₂ H hHB hyNB]
  exact recoded_order_arith hd₁ hd₂ (Nat.mul_div_cancel' hL₁) (Nat.mul_div_cancel' hL₂) hn

/-- **After common-mark recoding the normalized relation is an equality** (mixed-test equivalent, same carrier): along
every common test history, at every cosupport point, the ordinary orders of the two recoded records agree, and so do
their cosupports. -/
theorem common_multiple_recoding_order_eq {k₁ k₂ : ℕ} {M₁ M₂ : MarkedIdeal n X} (h : MixedEquiv M₁ M₂)
    (h₁ : IsInvDomain k₁ M₁) (h₂ : IsInvDomain k₂ M₂) (hN : M₂.N = M₁.N) {L : ℕ} (hL : 0 < L) (hL₁ : M₁.d ∣ L)
    (hL₂ : M₂.d ∣ L) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M₁.E Y F) (hH : IsTest M₁ H)
    {y : Y} (hy : y ∈ (record M₁ H).cosupp) :
    ordinaryTraceOrder (record (powerMarked M₁ (L / M₁.d)) H).N (record (powerMarked M₁ (L / M₁.d)) H).ideal y =
      ordinaryTraceOrder (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).N
        (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).ideal y ∧
    (record (powerMarked M₁ (L / M₁.d)) H).cosupp =
      (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).cosupp := by
  have h₂' : IsInvDomain k₂ (withBoundary M₂ M₁.E) := (withBoundary_eq h.E_eq).symm ▸ h₂
  have hd₁ : 0 < M₁.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₁.one_le_d
  have hd₂ : 0 < M₂.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₂.one_le_d
  have he₁ : 1 ≤ L / M₁.d := Nat.div_pos (Nat.le_of_dvd hL hL₁) hd₁
  have he₂ : 1 ≤ L / M₂.d := Nat.div_pos (Nat.le_of_dvd hL hL₂) hd₂
  have hHB : IsTest (withBoundary M₂ M₁.E) H := (h.isTest_iff H).mp hH
  have hcos := h.cosupp_eq H hH
  have hyB : y ∈ (record (withBoundary M₂ M₁.E) H).cosupp := hcos ▸ hy
  refine ⟨recoded_order_eq_of_normalized h₁ h₂ h.E_eq hL hL₁ hL₂ H hH hHB ((record M₁ H).cosupp_subset_N hy)
    ((record (withBoundary M₂ M₁.E) H).cosupp_subset_N hyB) (mixedEquiv_normalizedOrder_record h h₁ h₂ hN H hH hy), ?_⟩
  rw [(recodingDictionary_of_isTest M₁ h₁ he₁ H hH).2.2.2.2.2.2.1,
    (recodingDictionary_of_isTest (withBoundary M₂ M₁.E) h₂' he₂ H hHB).2.2.2.2.2.2.1]
  exact hcos

/-- **The same for `s(i,ii)`** along every common test history without exceptional actions. -/
theorem common_multiple_recoding_order_eq_of_projEquiv {k₁ k₂ : ℕ} {M₁ M₂ : MarkedIdeal n X} (h : ProjEquiv M₁ M₂)
    (h₁ : IsInvDomain k₁ M₁) (h₂ : IsInvDomain k₂ M₂) (hN : M₂.N = M₁.N) {L : ℕ} (hL : 0 < L) (hL₁ : M₁.d ∣ L)
    (hL₂ : M₂.d ∣ L) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M₁.E Y F) (hH : IsTest M₁ H)
    (hnH : NoExc H) {y : Y} (hy : y ∈ (record M₁ H).cosupp) :
    ordinaryTraceOrder (record (powerMarked M₁ (L / M₁.d)) H).N (record (powerMarked M₁ (L / M₁.d)) H).ideal y =
      ordinaryTraceOrder (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).N
        (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).ideal y ∧
    (record (powerMarked M₁ (L / M₁.d)) H).cosupp =
      (record (powerMarked (withBoundary M₂ M₁.E) (L / M₂.d)) H).cosupp := by
  have h₂' : IsInvDomain k₂ (withBoundary M₂ M₁.E) := (withBoundary_eq h.E_eq).symm ▸ h₂
  have hd₁ : 0 < M₁.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₁.one_le_d
  have hd₂ : 0 < M₂.d := Nat.lt_of_lt_of_le Nat.zero_lt_one h₂.one_le_d
  have he₁ : 1 ≤ L / M₁.d := Nat.div_pos (Nat.le_of_dvd hL hL₁) hd₁
  have he₂ : 1 ≤ L / M₂.d := Nat.div_pos (Nat.le_of_dvd hL hL₂) hd₂
  have hHB : IsTest (withBoundary M₂ M₁.E) H := ((h.2 H hnH).1).mp hH
  have hcos := (h.2 H hnH).2 hH
  have hyB : y ∈ (record (withBoundary M₂ M₁.E) H).cosupp := hcos ▸ hy
  refine ⟨recoded_order_eq_of_normalized h₁ h₂ h.E_eq hL hL₁ hL₂ H hH hHB ((record M₁ H).cosupp_subset_N hy)
    ((record (withBoundary M₂ M₁.E) H).cosupp_subset_N hyB)
    (projEquiv_normalizedOrder_record h h₁ h₂ hN H hH hnH hy), ?_⟩
  rw [(recodingDictionary_of_isTest M₁ h₁ he₁ H hH).2.2.2.2.2.2.1,
    (recodingDictionary_of_isTest (withBoundary M₂ M₁.E) h₂' he₂ H hHB).2.2.2.2.2.2.1]
  exact hcos

end Recoding

end

end Hironaka.HironakaG8CommonMarkRecoding
