import Hironaka.Resolution.HironakaG8LogFiniteSumTransform
import Hironaka.Resolution.HironakaActualMixedTestPowerNormalization
import Hironaka.Resolution.HironakaG8ExceptionalCentreChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Logarithmic derivative inclusions along mixed test histories (G8 lane, run 0080; leaf G8-3H-C10)

Blueprint: `hironaka-g8-resume-log-mixed-history.tex`.

`HironakaActualMixedTestPowerNormalization.History` records the genuine mixed test actions of Bierstone--Milman
2008, §2 (admissible ("controlled") blowups, projections `Y × ℂ → Y` with the new horizontal divisor, and blowups
along intersections of two boundary members ("exceptional"), with ordinary pullbacks for the last two), and
`record M H` is the transform of the marked ideal `M` along `H` (the actual whole ideals, carriers, full boundary
lists and the original mark).  For a marked ideal in the native domain (`IsInvDomain`) and `j ≤ d`, along every
test history `H` of `M` (`mixed_rawLogMarked_le`; BM08 Corollaries 3.4, 3.5, logarithmic):

* `H` is a test history of `𝔪_j = rawLogMarked M j` (every controlled centre is admissible for the transform of
  `𝔪_j`);
* the transform of `𝔪_j` along `H` and `rawLogMarked` of the transform of `M` have the same carrier, boundary and
  mark `d - j` (`record_rawLogMarked_meta`, definitional), and on the carrier
  `record (rawLogMarked M j) H ⊆ rawLogMarked (record M H) j`.

Each action: controlled — the controlled log inclusion (`HironakaG8LogControlledMarked.geoTransform_rawLogMarked_le`);
projection — the projection log equality (`HironakaActualProjectionNativeLogIdeal.projection_native_logIdeal_iterate_eq`,
leaf G8-3H-C04); exceptional — the exceptional log equality
(`HironakaG8ExceptionalCentreChart.exceptional_logIdeal_iterate_eq`, leaf G8-3H-C05); and restricted inclusions pass
through pullbacks and colons.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogMixedHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold Hironaka.DerivativeIdealAlongTransform
  Hironaka.ResolutionInvariantSpec
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaActualProjectionTestRecord
  Hironaka.HironakaActualProjectionNativeLogIdeal
  Hironaka.HironakaActualMixedTestPowerNormalization
  Hironaka.HironakaG8ExceptionalCentreChart
  Hironaka.HironakaG8LogControlledInclusion
  Hironaka.HironakaG8LogControlledMarked
  Hironaka.HironakaG8LogFiniteSumCut
open scoped ProductComplexManifold

noncomputable section

/-! ### Restricted inclusions through pullbacks -/

section Pullback

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel m) M'] [IsComplexManifold m M']

/-- **Restricted inclusions pull back**: if `φ` maps `W'` into `W` and `A|_W ⊆ B|_W` (`B` holomorphic germs), then
`φ^*A|_{W'} ⊆ φ^*B|_{W'}` (any holomorphic `φ`, any dimensions). -/
theorem restrictLe_pullback_of_restrictLe {φ : M' → M}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ φ) {W : Set M} {W' : Set M'}
    (hW : ∀ p ∈ W', φ p ∈ W) {A B : GermIdeal n M} (hB : ∀ x g, B.mem x g → HolomorphicAt n g x)
    (h : RestrictLe W A B) :
    RestrictLe W' (GermIdeal.pullback (m := m) φ A) (GermIdeal.pullback (m := m) φ B) := by
  intro z hz g hg
  have hg' : IsInSpanAt (n := m) (fun s => ∃ a, A.mem (φ z) a ∧ s = a ∘ φ) z g := hg
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hg')
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨K, t, c, ht, hc, hsum⟩ := h (φ z) (hW z hz) a ha
  refine ⟨K, fun i => t i ∘ φ, fun i => c i ∘ φ, fun i => ?_, fun i => ?_, ?_⟩
  · show IsInSpanAt (n := m) (fun s => ∃ a, B.mem (φ z) a ∧ s = a ∘ φ) z (t i ∘ φ)
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨t i, ht i, rfl⟩
      ((hB _ _ (ht i)).comp_contMDiff (Eventually.of_forall fun p => hφ p))
  · exact (hc i).comp_contMDiff (Eventually.of_forall fun p => hφ p)
  · filter_upwards [(hφ z).continuousAt.eventually hsum] with p hp hpW'
    exact hp (hW p hpW')

end Pullback

/-! ### Mixed test histories -/

section Mixed

variable {n : ℕ} {X : CMfd.{0} n}

/-- Along every history the transform of `𝔪_j` and `rawLogMarked` of the transform have the same carrier, boundary
and mark `d - j`. -/
theorem record_rawLogMarked_meta (M : MarkedIdeal n X) (j : ℕ) {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)}
    (H : History X M.E Y F) :
    (record (rawLogMarked M j) H).N = (rawLogMarked (record M H) j).N ∧
      (record (rawLogMarked M j) H).E = (rawLogMarked (record M H) j).E ∧
      (record (rawLogMarked M j) H).d = (rawLogMarked (record M H) j).d ∧
      (rawLogMarked (record M H) j).d = M.d - j :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Logarithmic derivative inclusions along mixed test histories** (BM08 Corollaries 3.4--3.5, logarithmic, for
the genuine mixed test actions): for `M` in the native domain and `j ≤ d`, every test history `H` of `M` is a test
history of `𝔪_j = rawLogMarked M j`, and on the current carrier
`record 𝔪_j H ⊆ rawLogMarked (record M H) j`. -/
theorem mixed_rawLogMarked_le (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M) {j : ℕ} (hj : j ≤ M.d) :
    ∀ {m : ℕ} {Y : CMfd.{0} m} {F : List (Set Y)} (H : History X M.E Y F), IsTest M H →
      IsTest (rawLogMarked M j) H ∧
        RestrictLe (record M H).N (record (rawLogMarked M j) H).ideal (rawLogMarked (record M H) j).ideal
  | _, _, _, .refl, _ => by
    have h𝔞hol : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
    exact ⟨trivial, restrictLe_refl (holomorphicAt_of_mem_logIter h𝔞hol j)⟩
  | _, _, _, .controlled H C π hπ, hH => by
    obtain ⟨ht, hle⟩ := mixed_rawLogMarked_le M hM hj H hH.1
    have hd := (record_isInvDomain M hM H hH.1).isWellFormed
    have hRhol : ∀ x g, (record M H).ideal.mem x g → HolomorphicAt _ g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg
    have hBhol := holomorphicAt_of_mem_logIter (N := (record M H).N) (E := (record M H).E) hRhol j
    have hC : (record M H).IsAdmissibleCentre C := hH.2
    have hCj : (record (rawLogMarked M j) H).IsAdmissibleCentre C := by
      refine ⟨hC.1, fun x hx => ?_, hC.2.2⟩
      have h2 := cosupp_subset_cosupp_rawLogMarked (record M H) hRhol hj (hC.2.1 hx)
      exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hle _ h2
    refine ⟨⟨ht, hCj⟩, ?_⟩
    obtain ⟨-, -, -, -, h4⟩ := geoTransform_rawLogMarked_le (record M H) hd hC hπ hj
    show RestrictLe (geoStrictTransform π C (record M H).N)
      ((record (rawLogMarked M j) H).geoTransform C π).ideal (rawLogMarked ((record M H).geoTransform C π) j).ideal
    refine restrictLe_trans (restrictLe_colonAlong_of_restrictLe
      (restrictLe_pullback_of_restrictLe hπ.contMDiff
        (fun p hp => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hd.isClosedSubmanifold_N.1 hp)
        hBhol hle)) h4
  | _, _, _, @History.projection _ _ _ m₀ Y₀ F₀ H, hH => by
    obtain ⟨ht, hle⟩ := mixed_rawLogMarked_le M hM hj H hH
    have hd := (record_isInvDomain M hM H hH).isWellFormed
    have hRhol : ∀ x g, (record M H).ideal.mem x g → HolomorphicAt m₀ g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg
    have hBhol := holomorphicAt_of_mem_logIter (N := (record M H).N) (E := (record M H).E) hRhol j
    refine ⟨ht, ?_⟩
    have h1 : RestrictLe ((Prod.fst : projectionAmbient Y₀ → Y₀) ⁻¹' (record M H).N)
        (GermIdeal.pullback (m := m₀ + 1) (Prod.fst : projectionAmbient Y₀ → Y₀) (record (rawLogMarked M j) H).ideal)
        (GermIdeal.pullback (m := m₀ + 1) (Prod.fst : projectionAmbient Y₀ → Y₀)
          ((logDerivIdealAlong (record M H).N (record M H).E)^[j] (record M H).ideal)) :=
      restrictLe_pullback_of_restrictLe
        (ProductComplexManifold.contMDiff_fst (n := m₀) (m := 1) (X := Y₀) (Y := ComplexModel 1))
        (fun p hp => hp) hBhol hle
    rw [projection_native_logIdeal_iterate_eq (record M H).ideal hd.isCoherent hd.isClosedSubmanifold_N
      hd.isSNCDivisor hd.isTransverse j] at h1
    exact h1
  | _, _, _, @History.exceptional _ _ _ m₀ Y₀ F₀ H i i' hii' Z π hπ, hH => by
    obtain ⟨ht, hle⟩ := mixed_rawLogMarked_le M hM hj H hH
    have hd := (record_isInvDomain M hM H hH).isWellFormed
    have hRhol : ∀ x g, (record M H).ideal.mem x g → HolomorphicAt m₀ g x := fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isCoherent hg
    have hBhol := holomorphicAt_of_mem_logIter (N := (record M H).N) (E := (record M H).E) hRhol j
    refine ⟨ht, ?_⟩
    have h1 : RestrictLe (geoStrictTransform π (F₀.get i ∩ F₀.get i') (record M H).N)
        (GermIdeal.pullback (m := m₀) π (record (rawLogMarked M j) H).ideal)
        (GermIdeal.pullback (m := m₀) π ((logDerivIdealAlong (record M H).N (record M H).E)^[j] (record M H).ideal)) :=
      restrictLe_pullback_of_restrictLe hπ.contMDiff
        (fun p hp => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hd.isClosedSubmanifold_N.1 hp)
        hBhol hle
    rw [exceptional_logIdeal_iterate_eq (record M H).ideal hRhol (record M H).N (record M H).E
      hd.isClosedSubmanifold_N hd.isSNCDivisor hd.isTransverse i i' π hπ j] at h1
    exact h1

end Mixed

end

end Hironaka.HironakaG8LogMixedHistory
