import Hironaka.Resolution.HironakaG8LogClosureHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Every-prefix logarithmic dictionary along mixed test histories (G8 lane, run 0080; leaves G8-3H-C10, C11)

Blueprint: `hironaka-g8-resume-log-history-prefixes.tex`.

For a marked ideal `M` in the native domain, `k < d` and a test history `H` of `M`
(`HironakaActualMixedTestPowerNormalization.History`: admissible blowups, projections, exceptional blowups), EVERY
prefix `Q` of `H` (`AllPrefixes`, including `refl`) carries (`log_history_dictionary`):

* `Q` is a test history of `M`, of every `𝔪_j = rawLogMarked M j` (`j ≤ d`) and of `𝓒^k(M)`;
* `(𝔪_j)_Q ⊆ (M_Q)_j` and `𝓒^k(M)_Q ⊆ 𝓒^k(M_Q)` on the current carrier (literal carrier, full boundary list, mark);
* `cosupp 𝓒^k(M)_Q = cosupp M_Q = cosupp 𝓒^k(M_Q)`;
* the clocks: the boundary list has length `|E| + |Q|` and the dimension is `n + #projections`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogHistoryPrefixes

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.RestrictedIdealWeight Hironaka.ResolutionInvariantSpec
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaActualMixedTestPowerNormalization
  Hironaka.HironakaG8LogMixedHistory
  Hironaka.HironakaG8LogClosureHistory

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n} {E : List (Set X)}

/-- `AllPrefixes` is monotone in the predicate. -/
theorem allPrefixes_mono {P R : ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)}, History X E Y F → Prop}
    (h : ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (Q : History X E Y F), P Q → R Q) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X E Y F), AllPrefixes P H → AllPrefixes R H
  | _, _, _, .refl, hP => h _ hP
  | _, _, _, .controlled H _ _ _, hP => ⟨h _ hP.1, allPrefixes_mono h H hP.2⟩
  | _, _, _, .projection H, hP => ⟨h _ hP.1, allPrefixes_mono h H hP.2⟩
  | _, _, _, .exceptional H _ _ _ _ _, hP => ⟨h _ hP.1, allPrefixes_mono h H hP.2⟩

/-- Every prefix of a test history is a test history. -/
theorem isTest_allPrefixes (M : MarkedIdeal n X) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F), IsTest M H →
      AllPrefixes (fun {_mm} {_YY} {_GG} Q => IsTest M Q) H
  | _, _, _, .refl, h => h
  | _, _, _, .controlled H _ _ _, h => ⟨h, isTest_allPrefixes M H h.1⟩
  | _, _, _, .projection H, h => ⟨h, isTest_allPrefixes M H h⟩
  | _, _, _, .exceptional H _ _ _ _ _, h => ⟨h, isTest_allPrefixes M H h⟩

/-- **The every-prefix logarithmic dictionary** (BM08 Corollaries 3.4--3.5, Theorem 3.10, Corollary 3.11,
logarithmic, along the genuine mixed test actions). -/
theorem log_history_dictionary (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F) (hH : IsTest M H) :
    AllPrefixes (fun {mm} {_YY} {_GG} Q =>
      IsTest M Q ∧ IsTest (bmFiniteSum (rawLogMarked M) (k + 1)) Q ∧
      (∀ j ≤ M.d, IsTest (rawLogMarked M j) Q ∧
        RestrictLe (record M Q).N (record (rawLogMarked M j) Q).ideal (rawLogMarked (record M Q) j).ideal) ∧
      RestrictLe (record M Q).N (record (bmFiniteSum (rawLogMarked M) (k + 1)) Q).ideal
        (bmFiniteSum (rawLogMarked (record M Q)) (k + 1)).ideal ∧
      (record (bmFiniteSum (rawLogMarked M) (k + 1)) Q).cosupp = (record M Q).cosupp ∧
      (bmFiniteSum (rawLogMarked (record M Q)) (k + 1)).cosupp = (record M Q).cosupp ∧
      (record M Q).E.length = M.E.length + length Q ∧ mm = n + projections Q) H := by
  refine allPrefixes_mono (P := fun {_mm} {_YY} {_GG} Q => IsTest M Q) ?_ H (isTest_allPrefixes M H hH)
  intro m' Y' F' Q hQ
  exact ⟨hQ, (mixed_logClosure_isTest_iff M hM hk Q).mpr hQ, fun j hj => mixed_rawLogMarked_le M hM hj Q hQ,
    (mixed_logClosure_le M hM hk Q hQ).2.2.2, (mixed_logClosure_cosupp M hM hk Q hQ).1,
    (mixed_logClosure_cosupp M hM hk Q hQ).2, (history_clocks M Q).2, (history_clocks M Q).1⟩

end

end Hironaka.HironakaG8LogHistoryPrefixes
