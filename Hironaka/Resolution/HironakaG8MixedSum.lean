import Hironaka.Resolution.HironakaG8MixedEquiv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Common-mark sums along mixed test histories; stability of mixed-test equivalence under sums (G8 lane, run 0080 r2)

Blueprint: `hironaka-g8-resume-mixed-sum.tex`.

For a finite family `Q i = (N, E, 𝔞_i, d_i)` (`i < m`, one carrier, one boundary) in the native domain, the common-mark
sum `∑ Q = (∑_i 𝔞_i^{L/d_i}, L)` (`L = lcm d_i`, `HironakaActualIteratedLogMarkedFamily.bmFiniteSum`; BM08 §3, the
"intersection" of marked ideals) satisfies, along the genuine mixed histories (admissible blowups, products with a line,
exceptional blowups):

* `mixed_finSum_le_sum`: `(∑ Q)_H ⊆ ∑_i ((Q i)_H)^{L/d_i}` on the current carrier, at every common test history;
* **`mixed_finSum_cosupp`**: `cosupp (∑ Q)_H = carrier ∩ ⋂_i cosupp (Q i)_H` at every common test history;
* **`mixed_finSum_isTest_iff`**: `H` is a test history of `∑ Q` iff it is one of every `Q i`;
* **`MixedEquiv.finSum`**: if `Q i ~ Q' i` for every `i < m` (carriers may differ, marks may differ), then
  `∑ Q ~ ∑ Q'`;
* `mixedEquiv_of_restrictEquiv`: restricted-equivalent marked ideals (field (7) of a resolution invariant) are
  mixed-test equivalent.

The general form of `HironakaG8LogClosureHistory` (there for the log family `𝔪_j`); the controlled step is
`HironakaG8LogFiniteSumTransform.restrictLe_colonAlong_finSum_le` (with Hadamard along the carrier for each summand),
the reverse cut uses the `i`-th term `(Q i)^{L/d_i} ⊆ ∑ Q`, monotone transforms and the original power normalization.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8MixedSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.HomogenizedGlueing
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold Hironaka.DerivativeIdealAlongTransform
  Hironaka.ResolutionInvariantSpec
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaActualProjectionTestRecord
  Hironaka.HironakaActualPowerBoundaryExponents
  Hironaka.HironakaActualMixedTestPowerNormalization
  Hironaka.HironakaG8LogControlledMarked
  Hironaka.HironakaG8LogFiniteSumCut
  Hironaka.HironakaG8LogFiniteSumTransform
  Hironaka.HironakaG8LogMixedHistory
  Hironaka.HironakaG8LogClosureHistory
  Hironaka.HironakaG8MixedEquiv
open scoped ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-- **A family on one carrier with one boundary**: `i ↦ (N, E, A i, d i)`. -/
def fam (N : Set X) (E : List (Set X)) (A : ℕ → GermIdeal n X) (d : ℕ → ℕ) (i : ℕ) : MarkedIdeal n X :=
  ⟨N, E, A i, d i⟩

section Sum

variable (N : Set X) (E : List (Set X)) (A : ℕ → GermIdeal n X) (d : ℕ → ℕ) (m : ℕ)

/-- **The transform of a common-mark sum stays inside the common-mark sum of the transforms** along every common test
history. -/
theorem mixed_finSum_le_sum {r : ℕ} (hm : 0 < m) (hQ : ∀ i < m, IsInvDomain r (fam N E A d i))
    (hhol : ∀ i x g, (A i).mem x g → HolomorphicAt n g x) :
    ∀ {p : ℕ} {Y : CMfd.{0} p} {F : List (Set Y)} (H : History X E Y F), (∀ i < m, IsTest (fam N E A d i) H) →
      RestrictLe (carrier N H) (record (bmFiniteSum (fam N E A d) m) H).ideal
        (finSumIdeal (fun i => idealPow (record (fam N E A d i) H).ideal
          (bmCommonMark (fam N E A d) m / d i)) m)
  | _, _, _, .refl, _ => by
    refine restrictLe_refl ?_
    intro y g hg
    exact hg.1
  | _, _, _, .controlled H C π hπ, hH => by
    have ih := mixed_finSum_le_sum hm hQ hhol H fun i hi => (hH i hi).1
    have hdi : ∀ i < m, (record (fam N E A d i) H).IsWellFormed := fun i hi =>
      (record_isInvDomain (fam N E A d i) (hQ i hi) H (hH i hi).1).isWellFormed
    have hAhol : ∀ i < m, ∀ y g, (record (fam N E A d i) H).ideal.mem y g → HolomorphicAt _ g y := fun i hi _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hdi i hi).isCoherent hg
    obtain ⟨-, hspec⟩ := bmCommonMark_spec (fam N E A d) m fun i hi => (hQ i hi).one_le_d
    have hle : ∀ i < m, RestrictLe (carrier N H) (record (fam N E A d i) H).ideal
        (idealPow (vanishingIdeal (n := _) C) (d i)) := fun i hi => by
      have hC : (record (fam N E A d i) H).IsAdmissibleCentre C := (hH i hi).2
      exact HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport (hdi i hi).isCoherent
        (hdi i hi).isClosedSubmanifold_N hC.1 hC.subset_N hC.2.1
    have hcl : IsClosed (carrier N H) := (hdi 0 hm).isClosedSubmanifold_N.1
    have h2 := restrictLe_colonAlong_finSum_le (A := fun i => (record (fam N E A d i) H).ideal)
      (d := d) (k := fun i => bmCommonMark (fam N E A d) m / d i) hπ hcl hAhol hle (fun i hi => (hspec i hi).2.2)
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (fam N E A d i) H).ideal
        (bmCommonMark (fam N E A d) m / d i)) m).mem y g → HolomorphicAt _ g y :=
      fun _ _ hg => hg.1
    exact restrictLe_trans (restrictLe_colonAlong_of_restrictLe (restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hcl hq) hShol ih)) h2
  | _, _, _, @History.projection _ _ _ m₀ Y₀ _ H, hH => by
    have ih := mixed_finSum_le_sum hm hQ hhol H hH
    have hAhol : ∀ i < m, ∀ y g, (record (fam N E A d i) H).ideal.mem y g → HolomorphicAt m₀ g y := fun i hi _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        (record_isInvDomain (fam N E A d i) (hQ i hi) H (hH i hi)).isWellFormed.isCoherent hg
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (fam N E A d i) H).ideal
        (bmCommonMark (fam N E A d) m / d i)) m).mem y g → HolomorphicAt m₀ g y :=
      fun _ _ hg => hg.1
    have hφ := ProductComplexManifold.contMDiff_fst (n := m₀) (m := 1) (X := Y₀) (Y := ComplexModel 1)
    refine restrictLe_trans (restrictLe_pullback_of_restrictLe hφ (fun q hq => hq) hShol ih) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le (A := fun i => (record (fam N E A d i) H).ideal) hφ ?_
      (k := fun i => bmCommonMark (fam N E A d) m / d i) (m := m) hg
    · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)
    · exact fun i => wholeIdeal_hol N (hhol i) (d i) H
  | _, _, _, @History.exceptional _ _ _ m₀ _ F₀ H i j _ _ π hπ, hH => by
    have ih := mixed_finSum_le_sum hm hQ hhol H hH
    have hdi : (record (fam N E A d 0) H).IsWellFormed :=
      (record_isInvDomain (fam N E A d 0) (hQ 0 hm) H (hH 0 hm)).isWellFormed
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (fam N E A d i) H).ideal
        (bmCommonMark (fam N E A d) m / d i)) m).mem y g → HolomorphicAt m₀ g y :=
      fun _ _ hg => hg.1
    refine restrictLe_trans (restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hdi.isClosedSubmanifold_N.1 hq)
      hShol ih) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le (A := fun i => (record (fam N E A d i) H).ideal) hπ.contMDiff ?_
      (k := fun i => bmCommonMark (fam N E A d) m / d i) (m := m) hg
    · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)
    · exact fun i => wholeIdeal_hol N (hhol i) (d i) H

/-- **The cut of a common-mark sum along a common test history is the intersection of the cuts.** -/
theorem mixed_finSum_cosupp {r : ℕ} (hm : 0 < m) (hQ : ∀ i < m, IsInvDomain r (fam N E A d i))
    (hhol : ∀ i x g, (A i).mem x g → HolomorphicAt n g x) {p : ℕ} {Y : CMfd.{0} p} {F : List (Set Y)}
    (H : History X E Y F) (hH : ∀ i < m, IsTest (fam N E A d i) H) :
    (record (bmFiniteSum (fam N E A d) m) H).cosupp =
      {y | y ∈ carrier N H ∧ ∀ i < m, y ∈ (record (fam N E A d i) H).cosupp} := by
  have hRd : ∀ i < m, IsInvDomain (r + projections H) (record (fam N E A d i) H) := fun i hi =>
    record_isInvDomain (fam N E A d i) (hQ i hi) H (hH i hi)
  obtain ⟨-, hspec⟩ := bmCommonMark_spec (fam N E A d) m fun i hi => (hQ i hi).one_le_d
  have hNcl : IsClosed N := (hQ 0 hm).isWellFormed.isClosedSubmanifold_N.1
  refine Subset.antisymm ?_ ?_
  · intro y hy
    refine ⟨hy.1, fun i hi => ?_⟩
    obtain ⟨-, he, hmul⟩ := hspec i hi
    have hmul' : d i * (bmCommonMark (fam N E A d) m / d i) = bmCommonMark (fam N E A d) m := hmul
    have he1 : 1 ≤ bmCommonMark (fam N E A d) m / d i := he
    have hShol : ∀ x g, (bmFiniteSum (fam N E A d) m).ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => hg.1
    have hbase : RestrictLe N (idealPow (A i) (bmCommonMark (fam N E A d) m / d i))
        (bmFiniteSum (fam N E A d) m).ideal := by
      intro x _ g hg
      refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_
        (GermIdealOrder.holomorphicAt_of_mem_idealPow hg))
      show (finSumIdeal (fun i => idealPow (fam N E A d i).ideal
        (bmCommonMark (fam N E A d) m / (fam N E A d i).d)) m).mem x g
      exact mem_finSumIdeal_of_mem (J := fun i => idealPow (fam N E A d i).ideal
        (bmCommonMark (fam N E A d) m / (fam N E A d i).d)) hi hg
        (GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
    have hmono := wholeIdeal_mono (E := E) hNcl hShol (bmCommonMark (fam N E A d) m) hbase H
    have hpow := (original_power_normalization (fam N E A d i) (hQ i hi)
      (bmCommonMark (fam N E A d) m / d i) he1 H (hH i hi)).2
    have hcos : (record (powerMarked (fam N E A d i) (bmCommonMark (fam N E A d) m / d i)) H).cosupp =
        (record (fam N E A d i) H).cosupp :=
      hpow.cosupp_eq.trans (powerMarked_cosupp (record (fam N E A d i) H) (hRd i hi) he1)
    have h1 := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hmono _ hy
    rw [← hcos]
    show y ∈ cosupport p (carrier N H) (wholeIdeal N (idealPow (A i)
      (bmCommonMark (fam N E A d) m / d i)) (d i * (bmCommonMark (fam N E A d) m / d i)) H)
      (d i * (bmCommonMark (fam N E A d) m / d i))
    rw [hmul']
    exact h1
  · intro y hy
    have hRhol : ∀ i < m, ∀ x g, (record (fam N E A d i) H).ideal.mem x g → HolomorphicAt p g x := fun i hi _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hRd i hi).isWellFormed.isCoherent hg
    have e2 := cosupp_bmFiniteSum (fam (carrier N H) F (fun i => (record (fam N E A d i) H).ideal) d) m
      (hRd 0 hm).isWellFormed.isClosedSubmanifold_N.2 (fun _ _ => rfl) (fun i hi => (hQ i hi).one_le_d) hRhol
    have hy' : y ∈ (bmFiniteSum (fam (carrier N H) F (fun i => (record (fam N E A d i) H).ideal) d) m).cosupp := by
      rw [e2]
      exact hy
    exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
      (mixed_finSum_le_sum N E A d m hm hQ hhol H hH) _ hy'

/-- **The tests of a common-mark sum are the common tests of the summands.** -/
theorem mixed_finSum_isTest_iff {r : ℕ} (hm : 0 < m) (hQ : ∀ i < m, IsInvDomain r (fam N E A d i))
    (hhol : ∀ i x g, (A i).mem x g → HolomorphicAt n g x) :
    ∀ {p : ℕ} {Y : CMfd.{0} p} {F : List (Set Y)} (H : History X E Y F),
      IsTest (bmFiniteSum (fam N E A d) m) H ↔ ∀ i < m, IsTest (fam N E A d i) H
  | _, _, _, .refl => ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  | _, _, _, .controlled H C π hπ => by
    have ih := mixed_finSum_isTest_iff hm hQ hhol H
    constructor
    · rintro ⟨h1, h2⟩
      have hH := ih.mp h1
      have hc := mixed_finSum_cosupp N E A d m hm hQ hhol H hH
      intro i hi
      refine ⟨hH i hi, h2.1, fun c hc' => ?_, h2.2.2⟩
      have h3 := h2.2.1 hc'
      rw [hc] at h3
      exact h3.2 i hi
    · intro h
      have hH : ∀ i < m, IsTest (fam N E A d i) H := fun i hi => (h i hi).1
      refine ⟨ih.mpr hH, (h 0 hm).2.1, fun c hc' => ?_, (h 0 hm).2.2.2⟩
      rw [mixed_finSum_cosupp N E A d m hm hQ hhol H hH]
      exact ⟨(h 0 hm).2.subset_N hc', fun i hi => (h i hi).2.2.1 hc'⟩
  | _, _, _, .projection H => mixed_finSum_isTest_iff hm hQ hhol H
  | _, _, _, .exceptional H _ _ _ _ _ => mixed_finSum_isTest_iff hm hQ hhol H

end Sum

/-! ### Stability of mixed-test equivalence under common-mark sums -/

/-- **Sums of equivalent families are equivalent**: if `(N, E, A i, d i) ~ (N', E, A' i, d' i)` for every `i < m`
(carriers and marks may differ), then the common-mark sums are mixed-test equivalent. -/
theorem MixedEquiv.finSum {N N' : Set X} {E : List (Set X)} {A A' : ℕ → GermIdeal n X} {d d' : ℕ → ℕ} {m r r' : ℕ}
    (hm : 0 < m) (hQ : ∀ i < m, IsInvDomain r (fam N E A d i)) (hQ' : ∀ i < m, IsInvDomain r' (fam N' E A' d' i))
    (hhol : ∀ i x g, (A i).mem x g → HolomorphicAt n g x) (hhol' : ∀ i x g, (A' i).mem x g → HolomorphicAt n g x)
    (h : ∀ i < m, MixedEquiv (fam N E A d i) (fam N' E A' d' i)) :
    MixedEquiv (bmFiniteSum (fam N E A d) m) (bmFiniteSum (fam N' E A' d') m) := by
  refine MixedEquiv.of_cosupp rfl fun H h1 h2 => ?_
  have hH := (mixed_finSum_isTest_iff N E A d m hm hQ hhol H).mp h1
  have hH' := (mixed_finSum_isTest_iff N' E A' d' m hm hQ' hhol' H).mp h2
  show (record (bmFiniteSum (fam N E A d) m) H).cosupp = (record (bmFiniteSum (fam N' E A' d') m) H).cosupp
  rw [mixed_finSum_cosupp N E A d m hm hQ hhol H hH, mixed_finSum_cosupp N' E A' d' m hm hQ' hhol' H hH']
  have hc : ∀ i < m, (record (fam N E A d i) H).cosupp = (record (fam N' E A' d' i) H).cosupp := fun i hi =>
    (h i hi).cosupp_eq H (hH i hi)
  ext y
  constructor
  · rintro ⟨-, hall⟩
    refine ⟨?_, fun i hi => hc i hi ▸ hall i hi⟩
    exact (record (fam N' E A' d' 0) H).cosupp_subset_N (hc 0 hm ▸ hall 0 hm)
  · rintro ⟨-, hall⟩
    refine ⟨?_, fun i hi => (hc i hi).symm ▸ hall i hi⟩
    exact (record (fam N E A d 0) H).cosupp_subset_N ((hc 0 hm).symm ▸ hall 0 hm)

/-! ### Restricted equivalence implies mixed-test equivalence -/

/-- **Restricted-equivalent marked ideals are mixed-test equivalent** (same carrier, boundary and mark, the ideals equal
on the carrier): their records along every mixed history are restricted-equivalent (`wholeIdeal_mono` both ways), so
the cuts agree. -/
theorem mixedEquiv_of_restrictEquiv {M M' : MarkedIdeal n X} (h : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv M M') (hN : IsClosed M.N)
    (hhol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x) (hhol' : ∀ x g, M'.ideal.mem x g → HolomorphicAt n g x) :
    MixedEquiv M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hN', hE', hd', hle, hge⟩ := h
  change N = N' at hN'
  change E = E' at hE'
  change d = d' at hd'
  subst hN' hE' hd'
  refine MixedEquiv.of_cosupp rfl fun H _ _ => ?_
  have h1 := wholeIdeal_mono (E := E) hN hhol' d hle H
  have h2 := wholeIdeal_mono (E := E) hN hhol d hge H
  exact Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h2 d)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h1 d)

end

end Hironaka.HironakaG8MixedSum
