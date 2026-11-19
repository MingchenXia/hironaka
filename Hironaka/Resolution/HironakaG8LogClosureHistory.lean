import Hironaka.Resolution.HironakaG8LogMixedHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The logarithmic closure has the same mixed tests and cuts (G8 lane, run 0080; leaf G8-3H-C11)

Blueprint: `hironaka-g8-resume-log-closure-history.tex`.

For a marked ideal `M = (X, N, E, 𝔞, d)` in the native domain and `k < d`, let
`𝓒^k(M) = bmFiniteSum (rawLogMarked M) (k + 1) = (∑_{j ≤ k} (𝓓_{N,E}^j 𝔞)^{L/(d-j)}, L)` (BM08 §3.4).  Along the genuine
mixed test histories `HironakaActualMixedTestPowerNormalization.History` (admissible blowups, projections,
exceptional blowups) this module proves (BM08 Theorem 3.10 and Corollary 3.11, logarithmic):

* `mixed_logClosure_isTest_iff`: a history is a test history of `𝓒^k(M)` iff it is one of `M`;
* `mixed_logClosure_cosupp`: at every test history `H`,
  `cosupp 𝓒^k(M)_H = cosupp M_H = cosupp 𝓒^k(M_H)`;
* `mixed_logClosure_le`: `𝓒^k(M)_H ⊆ 𝓒^k(M_H)` on the current carrier.

Route: along `H` the transform of the common-mark sum stays inside the common-mark sum of the transforms
(`mixed_logClosure_le_sum`: the controlled step is `HironakaG8LogFiniteSumTransform.restrictLe_colonAlong_finSum_le`,
the ordinary pullbacks satisfy `pullback_finSumIdeal_le`); each summand obeys the log inclusion of
`HironakaG8LogMixedHistory.mixed_rawLogMarked_le`; the reverse cut uses the zeroth term `M^{L/d} ⊆ 𝓒^k(M)`, the
monotonicity of transforms (`wholeIdeal_mono`) and the original power normalization
(`HironakaActualMixedTestPowerNormalization.original_power_normalization`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogClosureHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.HomogenizedGlueing
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold Hironaka.DerivativeIdealAlongTransform
  Hironaka.ResolutionInvariantSpec
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaActualProjectionTestRecord
  Hironaka.HironakaActualPowerBoundaryExponents
  Hironaka.HironakaActualMixedTestPowerNormalization
  Hironaka.HironakaG8LogControlledInclusion
  Hironaka.HironakaG8LogControlledMarked
  Hironaka.HironakaG8LogFiniteSumCut
  Hironaka.HironakaG8LogFiniteSumTransform
  Hironaka.HironakaG8LogMixedHistory
open scoped ProductComplexManifold

noncomputable section

/-! ### Ordinary pullbacks of common-mark sums -/

section Pullback

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel p) M'] [IsComplexManifold p M']
  {φ : M' → M} {z : M'}

/-- A holomorphic combination at `φ z` composes to a holomorphic combination at `z` (any dimensions). -/
theorem isInSpanAt_comp' (hφ : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ φ)
    {S : (M → ℂ) → Prop} {b : M → ℂ} (hb : IsInSpanAt (n := n) S (φ z) b) :
    IsInSpanAt (n := p) (fun t => ∃ s, S s ∧ t = fun q => s (φ q)) z (fun q => b (φ q)) := by
  obtain ⟨hbhol, K, s, c, hs, hc, hsum⟩ := hb
  refine ⟨hbhol.comp_contMDiff (Eventually.of_forall fun q => hφ q), K, fun i q => s i (φ q),
    fun i q => c i (φ q), fun i => ⟨s i, hs i, rfl⟩,
    fun i => (hc i).comp_contMDiff (Eventually.of_forall fun q => hφ q), ?_⟩
  filter_upwards [(hφ z).continuousAt.eventually hsum] with q hq
  exact hq

/-- `φ^*(A^k) ⊆ (φ^*A)^k`, germwise. -/
theorem pullback_idealPow_le (hφ : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ φ)
    {A : GermIdeal n M} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) :
    ∀ k b, (idealPow A k).mem (φ z) b → (idealPow (GermIdeal.pullback (m := p) φ A) k).mem z (b ∘ φ)
  | 0, b, hb => (show HolomorphicAt n b (φ z) from hb).comp_contMDiff (Eventually.of_forall fun q => hφ q)
  | k + 1, b, hb => by
    have hb' : IsInSpanAt (n := n) (fun t => ∃ a c, (idealPow A k).mem (φ z) a ∧ A.mem (φ z) c ∧ t = a * c)
        (φ z) b := hb
    show IsInSpanAt (n := p) (fun t => ∃ a c, (idealPow (GermIdeal.pullback (m := p) φ A) k).mem z a ∧
      (GermIdeal.pullback (m := p) φ A).mem z c ∧ t = a * c) z (b ∘ φ)
    refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) (isInSpanAt_comp' hφ hb')
    obtain ⟨_, ⟨a, c, ha, hc, rfl⟩, rfl⟩ := hs
    have hahol : HolomorphicAt n a (φ z) := GermIdealOrder.holomorphicAt_of_mem_idealPow ha
    have hchol := hA _ _ hc
    have h2 := pullback_idealPow_le hφ hA k a ha
    have h3 : (GermIdeal.pullback (m := p) φ A).mem z (c ∘ φ) := by
      show IsInSpanAt (n := p) (fun s => ∃ a, A.mem (φ z) a ∧ s = a ∘ φ) z (c ∘ φ)
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨c, hc, rfl⟩
        (hchol.comp_contMDiff (Eventually.of_forall fun q => hφ q))
    exact IdealOrderArithmetic.mul_mem_mul h2 h3
      ((hahol.comp_contMDiff (Eventually.of_forall fun q => hφ q)).mul
        (hchol.comp_contMDiff (Eventually.of_forall fun q => hφ q)))

/-- **The pullback of a common-mark sum lies in the common-mark sum of the pullbacks**, germwise. -/
theorem pullback_finSumIdeal_le (hφ : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ φ)
    {A : ℕ → GermIdeal n M} (hA : ∀ i x g, (A i).mem x g → HolomorphicAt n g x) {k : ℕ → ℕ} {m : ℕ}
    {g : M' → ℂ} (hg : (GermIdeal.pullback (m := p) φ (finSumIdeal (fun i => idealPow (A i) (k i)) m)).mem z g) :
    (finSumIdeal (fun i => idealPow (GermIdeal.pullback (m := p) φ (A i)) (k i)) m).mem z g := by
  have hg' : IsInSpanAt (n := p)
      (fun s => ∃ a, (finSumIdeal (fun i => idealPow (A i) (k i)) m).mem (φ z) a ∧ s = a ∘ φ) z g := hg
  show IsInSpanAt (n := p)
    (fun s => ∃ i, i < m ∧ (idealPow (GermIdeal.pullback (m := p) φ (A i)) (k i)).mem z s) z g
  refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) hg'
  obtain ⟨a, ha, rfl⟩ := hs
  have ha' : IsInSpanAt (n := n) (fun t => ∃ i, i < m ∧ (idealPow (A i) (k i)).mem (φ z) t) (φ z) a := ha
  refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => ?_) (isInSpanAt_comp' hφ ha')
  obtain ⟨b, ⟨i, hi, hb⟩, rfl⟩ := ht
  have h1 := pullback_idealPow_le hφ (hA i) (k i) b hb
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨i, hi, h1⟩ (GermIdealOrder.holomorphicAt_of_mem_idealPow h1)

end Pullback

/-! ### Transforms along histories are monotone -/

section Monotone

variable {n : ℕ} {X : CMfd.{0} n} {E : List (Set X)}

/-- The carriers along a history are closed. -/
theorem carrier_isClosed {N : Set X} (hN : IsClosed N) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X E Y F), IsClosed (carrier N H)
  | _, _, _, .refl => hN
  | _, _, _, .controlled _ _ _ _ => isClosed_closure
  | _, _, _, @History.projection _ _ _ m₀ Y₀ _ H =>
    (carrier_isClosed hN H).preimage
      (ProductComplexManifold.contMDiff_fst (n := m₀) (m := 1) (X := Y₀) (Y := ComplexModel 1)).continuous
  | _, _, _, .exceptional _ _ _ _ _ _ => isClosed_closure

/-- The ideals along a history consist of holomorphic germs. -/
theorem wholeIdeal_hol (N : Set X) {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) (d : ℕ) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X E Y F) (y : Y) (g : Y → ℂ),
      (wholeIdeal N A d H).mem y g → HolomorphicAt m g y
  | _, _, _, .refl, y, g, hg => hA y g hg
  | _, _, _, .controlled _ _ _ _, _, _, hg => hg.1
  | _, _, _, .projection _, _, _, hg => hg.1
  | _, _, _, .exceptional _ _ _ _ _ _, _, _, hg => hg.1

/-- **Transforms along a history preserve restricted inclusions** (same carrier, boundary and mark). -/
theorem wholeIdeal_mono {N : Set X} (hN : IsClosed N) {A B : GermIdeal n X}
    (hB : ∀ x g, B.mem x g → HolomorphicAt n g x) (d : ℕ) (h : RestrictLe N A B) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X E Y F),
      RestrictLe (carrier N H) (wholeIdeal N A d H) (wholeIdeal N B d H)
  | _, _, _, .refl => h
  | _, _, _, .controlled H C π hπ => by
    show RestrictLe (geoStrictTransform π C (carrier N H))
      (colonAlong _ (geoStrictTransform π C (carrier N H)) (GermIdeal.pullback π (wholeIdeal N A d H))
        (idealPow (GermIdeal.pullback π (vanishingIdeal C)) d))
      (colonAlong _ (geoStrictTransform π C (carrier N H)) (GermIdeal.pullback π (wholeIdeal N B d H))
        (idealPow (GermIdeal.pullback π (vanishingIdeal C)) d))
    exact restrictLe_colonAlong_of_restrictLe (restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous (carrier_isClosed hN H) hq)
      (wholeIdeal_hol N hB d H) (wholeIdeal_mono hN hB d h H))
  | _, _, _, @History.projection _ _ _ m₀ Y₀ _ H => by
    show RestrictLe ((Prod.fst : projectionAmbient Y₀ → Y₀) ⁻¹' carrier N H)
      (GermIdeal.pullback (m := m₀ + 1) (Prod.fst : projectionAmbient Y₀ → Y₀) (wholeIdeal N A d H))
      (GermIdeal.pullback (m := m₀ + 1) (Prod.fst : projectionAmbient Y₀ → Y₀) (wholeIdeal N B d H))
    exact restrictLe_pullback_of_restrictLe
      (ProductComplexManifold.contMDiff_fst (n := m₀) (m := 1) (X := Y₀) (Y := ComplexModel 1))
      (fun q hq => hq) (wholeIdeal_hol N hB d H) (wholeIdeal_mono hN hB d h H)
  | _, _, _, @History.exceptional _ _ _ m₀ _ F₀ H i j _ _ π hπ => by
    show RestrictLe (geoStrictTransform π (F₀.get i ∩ F₀.get j) (carrier N H))
      (GermIdeal.pullback (m := m₀) π (wholeIdeal N A d H)) (GermIdeal.pullback (m := m₀) π (wholeIdeal N B d H))
    exact restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous (carrier_isClosed hN H) hq)
      (wholeIdeal_hol N hB d H) (wholeIdeal_mono hN hB d h H)

end Monotone

/-! ### The logarithmic closure along mixed test histories -/

section Closure

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The transform of the logarithmic closure stays inside the common-mark sum of the transforms**: along every test
history `H` of `M`, `𝓒^k(M)_H ⊆ ∑_{i ≤ k} ((𝔪_i)_H)^{L/(d-i)}` on the current carrier. -/
theorem mixed_logClosure_le_sum (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F), IsTest M H →
      RestrictLe (record M H).N (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).ideal
        (finSumIdeal (fun i => idealPow (record (rawLogMarked M i) H).ideal
          (bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i))) (k + 1))
  | _, _, _, .refl, _ => by
    refine restrictLe_refl ?_
    intro y g hg
    exact hg.1
  | _, _, _, .controlled H C π hπ, hH => by
    have ih := mixed_logClosure_le_sum M hM hk H hH.1
    have hd := (record_isInvDomain M hM H hH.1).isWellFormed
    have hC : (record M H).IsAdmissibleCentre C := hH.2
    have h𝔞hol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
    have hAhol : ∀ i, ∀ y g, (record (rawLogMarked M i) H).ideal.mem y g → HolomorphicAt _ g y := fun i =>
      wholeIdeal_hol M.N (holomorphicAt_of_mem_logIter h𝔞hol i) (M.d - i) H
    obtain ⟨-, hspec⟩ := bmCommonMark_spec (rawLogMarked M) (k + 1) (rawLogMarked_d_pos M hk)
    have hle : ∀ i < k + 1, RestrictLe (record M H).N (record (rawLogMarked M i) H).ideal
        (idealPow (vanishingIdeal (n := _) C) (M.d - i)) := fun i hi =>
      restrictLe_trans (mixed_rawLogMarked_le M hM (j := i) (by omega) H hH.1).2
        (restrictLe_rawLogMarked_idealPow (record M H) hd hC (i := i) (by show i ≤ M.d; omega))
    have h2 := restrictLe_colonAlong_finSum_le (A := fun i => (record (rawLogMarked M i) H).ideal)
      (d := fun i => M.d - i) (k := fun i => bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i)) hπ
      hd.isClosedSubmanifold_N.1 (fun i _ => hAhol i) hle (fun i hi => (hspec i hi).2.2)
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (rawLogMarked M i) H).ideal
        (bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i))) (k + 1)).mem y g → HolomorphicAt _ g y :=
      fun _ _ hg => hg.1
    refine restrictLe_trans (restrictLe_colonAlong_of_restrictLe (restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hd.isClosedSubmanifold_N.1 hq)
      hShol ih)) ?_
    exact h2
  | _, _, _, @History.projection _ _ _ m₀ Y₀ _ H, hH => by
    have ih := mixed_logClosure_le_sum M hM hk H hH
    have h𝔞hol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
    have hAhol : ∀ i, ∀ y g, (record (rawLogMarked M i) H).ideal.mem y g → HolomorphicAt m₀ g y := fun i =>
      wholeIdeal_hol M.N (holomorphicAt_of_mem_logIter h𝔞hol i) (M.d - i) H
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (rawLogMarked M i) H).ideal
        (bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i))) (k + 1)).mem y g → HolomorphicAt m₀ g y :=
      fun _ _ hg => hg.1
    have hφ := ProductComplexManifold.contMDiff_fst (n := m₀) (m := 1) (X := Y₀) (Y := ComplexModel 1)
    refine restrictLe_trans (restrictLe_pullback_of_restrictLe hφ (fun q hq => hq) hShol ih) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le hφ hAhol (k := fun i => bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i))
      (m := k + 1) hg
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)
  | _, _, _, @History.exceptional _ _ _ m₀ _ F₀ H i j _ _ π hπ, hH => by
    have ih := mixed_logClosure_le_sum M hM hk H hH
    have hd := (record_isInvDomain M hM H hH).isWellFormed
    have h𝔞hol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
    have hAhol : ∀ i, ∀ y g, (record (rawLogMarked M i) H).ideal.mem y g → HolomorphicAt m₀ g y := fun i =>
      wholeIdeal_hol M.N (holomorphicAt_of_mem_logIter h𝔞hol i) (M.d - i) H
    have hShol : ∀ y g, (finSumIdeal (fun i => idealPow (record (rawLogMarked M i) H).ideal
        (bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i))) (k + 1)).mem y g → HolomorphicAt m₀ g y :=
      fun _ _ hg => hg.1
    refine restrictLe_trans (restrictLe_pullback_of_restrictLe hπ.contMDiff
      (fun q hq => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hd.isClosedSubmanifold_N.1 hq)
      hShol ih) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le hπ.contMDiff hAhol
      (k := fun i => bmCommonMark (rawLogMarked M) (k + 1) / (M.d - i)) (m := k + 1) hg
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)

/-- **The transform of the logarithmic closure lies in the logarithmic closure of the transform**: along every test
history `H` of `M` and for `k < d`, `𝓒^k(M)_H ⊆ 𝓒^k(M_H)` on the current carrier (same carrier, boundary and mark). -/
theorem mixed_logClosure_le (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F) (hH : IsTest M H) :
    (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).N = (bmFiniteSum (rawLogMarked (record M H)) (k + 1)).N ∧
      (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).E = (bmFiniteSum (rawLogMarked (record M H)) (k + 1)).E ∧
      (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).d = (bmFiniteSum (rawLogMarked (record M H)) (k + 1)).d ∧
      RestrictLe (record M H).N (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).ideal
        (bmFiniteSum (rawLogMarked (record M H)) (k + 1)).ideal := by
  refine ⟨rfl, rfl, rfl, restrictLe_trans (mixed_logClosure_le_sum M hM hk H hH) ?_⟩
  have hd := (record_isInvDomain M hM H hH).isWellFormed
  have hRhol : ∀ x g, (record M H).ideal.mem x g → HolomorphicAt m g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg
  refine restrictLe_finSumIdeal (fun i _ x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
    fun i hi => ?_
  exact MarkedIdealOperationsAlong.restrictLe_idealPow (holomorphicAt_of_mem_logIter (A := (record M H).ideal)
    hRhol i) (mixed_rawLogMarked_le M hM (j := i) (by omega) H hH).2 _

/-- **The same cuts** (BM08 Theorem 3.10, logarithmic, along mixed test histories): for `k < d` and every test
history `H` of `M`, `cosupp 𝓒^k(M)_H = cosupp M_H` and `cosupp 𝓒^k(M_H) = cosupp M_H`. -/
theorem mixed_logClosure_cosupp (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d)
    {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F) (hH : IsTest M H) :
    (record (bmFiniteSum (rawLogMarked M) (k + 1)) H).cosupp = (record M H).cosupp ∧
      (bmFiniteSum (rawLogMarked (record M H)) (k + 1)).cosupp = (record M H).cosupp := by
  have hRd := record_isInvDomain M hM H hH
  have hd := hRd.isWellFormed
  have hRhol : ∀ x g, (record M H).ideal.mem x g → HolomorphicAt m g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg
  have e2 := cosupp_bmFiniteSum_rawLogMarked (record M H) hd.isClosedSubmanifold_N hRhol hk
  refine ⟨Subset.antisymm ?_ ?_, e2⟩
  · obtain ⟨-, hspec⟩ := bmCommonMark_spec (rawLogMarked M) (k + 1) (rawLogMarked_d_pos M hk)
    obtain ⟨-, he, hmul⟩ := hspec 0 (Nat.succ_pos k)
    have hmul' : M.d * (bmCommonMark (rawLogMarked M) (k + 1) / M.d) = bmCommonMark (rawLogMarked M) (k + 1) :=
      hmul
    have he1 : 1 ≤ bmCommonMark (rawLogMarked M) (k + 1) / M.d := he
    have hShol : ∀ x g, (bmFiniteSum (rawLogMarked M) (k + 1)).ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => hg.1
    have hbase : RestrictLe M.N (idealPow M.ideal (bmCommonMark (rawLogMarked M) (k + 1) / M.d))
        (bmFiniteSum (rawLogMarked M) (k + 1)).ideal := by
      intro x _ g hg
      refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_
        (GermIdealOrder.holomorphicAt_of_mem_idealPow hg))
      show (finSumIdeal (fun i => idealPow (rawLogMarked M i).ideal
        (bmCommonMark (rawLogMarked M) (k + 1) / (rawLogMarked M i).d)) (k + 1)).mem x g
      exact mem_finSumIdeal_of_mem (J := fun i => idealPow (rawLogMarked M i).ideal
        (bmCommonMark (rawLogMarked M) (k + 1) / (rawLogMarked M i).d)) (Nat.succ_pos k) hg
        (GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
    have hmono := wholeIdeal_mono (E := M.E) hM.isWellFormed.isClosedSubmanifold_N.1 hShol
      (bmCommonMark (rawLogMarked M) (k + 1)) hbase H
    have hpow := (original_power_normalization M hM (bmCommonMark (rawLogMarked M) (k + 1) / M.d) he1 H hH).2
    have hcos : (record (powerMarked M (bmCommonMark (rawLogMarked M) (k + 1) / M.d)) H).cosupp =
        (record M H).cosupp :=
      hpow.cosupp_eq.trans (powerMarked_cosupp (record M H) hRd he1)
    intro x hx
    have h1 := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hmono _ hx
    rw [← hcos]
    show x ∈ cosupport m (carrier M.N H) (wholeIdeal M.N (idealPow M.ideal
      (bmCommonMark (rawLogMarked M) (k + 1) / M.d)) (M.d * (bmCommonMark (rawLogMarked M) (k + 1) / M.d)) H)
      (M.d * (bmCommonMark (rawLogMarked M) (k + 1) / M.d))
    rw [hmul']
    exact h1
  · rw [← e2]
    exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe (mixed_logClosure_le M hM hk H hH).2.2.2 _

/-- **The same mixed tests** (BM08 Corollary 3.11, logarithmic, for the genuine mixed test actions): for `k < d`, a
history is a test history of `𝓒^k(M)` iff it is a test history of `M`. -/
theorem mixed_logClosure_isTest_iff (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F),
      IsTest (bmFiniteSum (rawLogMarked M) (k + 1)) H ↔ IsTest M H
  | _, _, _, .refl => Iff.rfl
  | _, _, _, .controlled H C π hπ => by
    constructor
    · rintro ⟨h1, h2⟩
      have hH := (mixed_logClosure_isTest_iff M hM hk H).mp h1
      refine ⟨hH, ?_⟩
      have hc := (mixed_logClosure_cosupp M hM hk H hH).1
      unfold MarkedIdeals.MarkedIdeal.IsAdmissibleCentre at h2 ⊢
      rw [hc] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨(mixed_logClosure_isTest_iff M hM hk H).mpr h1, ?_⟩
      have hc := (mixed_logClosure_cosupp M hM hk H h1).1
      unfold MarkedIdeals.MarkedIdeal.IsAdmissibleCentre at h2 ⊢
      rw [hc]
      exact h2
  | _, _, _, .projection H => mixed_logClosure_isTest_iff M hM hk H
  | _, _, _, .exceptional H _ _ _ _ _ => mixed_logClosure_isTest_iff M hM hk H

end Closure

end

end Hironaka.HironakaG8LogClosureHistory
