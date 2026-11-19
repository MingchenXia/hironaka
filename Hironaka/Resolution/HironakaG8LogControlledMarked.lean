import Hironaka.Resolution.HironakaG8LogControlledInclusion
import Hironaka.Resolution.HironakaActualIteratedLogMarkedFamily
import Hironaka.Blowup.SimultaneousNormalCrossings

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The controlled logarithmic inclusion for marked ideals (G8 lane, run 0080; leaf G8-3H-C06)

Blueprint: `hironaka-g8-resume-log-controlled-marked.tex`.

For a marked ideal `𝔪 = (X, N, E, 𝔞, d)` and `j ≤ d`, the `j`-th logarithmic derivative marked ideal is
`HironakaActualIteratedLogMarkedFamily.rawLogMarked 𝔪 j = (X, N, E, 𝓓_{N,E}^j 𝔞, d - j)` (BM08 §3.2, the
logarithmic derivatives of the whole ambient representative along the carrier `N` and EVERY member of `E`).
For an admissible centre `C` and the blowup `π` along `C` (`MarkedIdeal.geoTransform`):

  `[rawLogMarked 𝔪 j]' ⊆ rawLogMarked 𝔪' j` on `N'`,

with the same carrier `N'`, the same transformed boundary `strict E ++ [π⁻¹C]` and the same mark `d - j`
(`geoTransform_rawLogMarked_le`).  This is the controlled-transform inclusion with mark decrement of BM08
Lemma 3.3 (Włodarczyk 2005, Lemma `le:inclusions`) in the logarithmic form; it is
`HironakaG8LogControlledInclusion.restrictLe_colonAlong_logIter` with `μ = d - j`, `r = j`, the hypothesis
`𝔞|_N ⊆ 𝓘_C^d|_N` coming from `C ⊆ cosupp 𝔪` (Hadamard along `N`), and the simultaneous normal crossings of
`C ⊆ N` and `E` from `SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings`.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogControlledMarked

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.BlowupStrictSubmanifold
open Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient
  Hironaka.RestrictedIdealWeight Hironaka.RelativePrincipalizationSpan
  Hironaka.BlowupSNCTransform Hironaka.SimultaneousNormalCrossings
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaG8LogControlledInclusion
  Hironaka.DerivativeIdealAlongTransform

noncomputable section

/-! ### Carrier saturation and colons along the carrier -/

section Carrier

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A restricted inclusion `A|_W ⊆ A'|_W` gives the inclusion of the colons along `W` (at the points of `W`). -/
theorem restrictLe_colonAlong_of_restrictLe {W : Set M} {A A' L : GermIdeal n M} (h : RestrictLe W A A') :
    RestrictLe W (colonAlong n W A L) (colonAlong n W A' L) := by
  intro x hx g hg
  refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_ hg.1)
  exact ⟨hg.1, fun ℓ hℓ => ⟨(hg.2 ℓ hℓ).1, IsInSpanOnAt.trans (fun s hs => h x hx s hs) (hg.2 ℓ hℓ).2⟩⟩

/-- An ideal of holomorphic germs is restricted-contained in its carrier saturation. -/
theorem restrictLe_restrictOn {W : Set M} {B : GermIdeal n M} (hB : ∀ x g, B.mem x g → HolomorphicAt n g x) :
    RestrictLe W B (restrictOn n W B) := fun x _ g hg =>
  IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self
    ⟨hB x g hg, IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg (hB x g hg))⟩ (hB x g hg))

/-- On a set `W'` mapped into the carrier `W`, the pullback of the carrier saturation of `B` is restricted-contained
in the pullback of `B`. -/
theorem restrictLe_pullback_restrictOn {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
    [IsComplexManifold n M'] {φ : M' → M} (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    {W : Set M} {W' : Set M'} (hW : ∀ p ∈ W', φ p ∈ W) {B : GermIdeal n M}
    (hB : ∀ x g, B.mem x g → HolomorphicAt n g x) :
    RestrictLe W' (GermIdeal.pullback (m := n) φ (restrictOn n W B)) (GermIdeal.pullback (m := n) φ B) := by
  intro z _ g hg
  have hg' : IsInSpanAt (n := n) (fun s => ∃ a, (restrictOn n W B).mem (φ z) a ∧ s = a ∘ φ) z g := hg
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hg')
  rintro s ⟨a, ⟨-, K, t, c, ht, hc, hsum⟩, rfl⟩
  refine ⟨K, fun i => t i ∘ φ, fun i => c i ∘ φ, fun i => ?_, fun i => ?_, ?_⟩
  · show IsInSpanAt (n := n) (fun s => ∃ a, B.mem (φ z) a ∧ s = a ∘ φ) z (t i ∘ φ)
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨t i, ht i, rfl⟩
      ((hB _ _ (ht i)).comp_contMDiff (Eventually.of_forall fun p => hφ p))
  · exact (hc i).comp_contMDiff (Eventually.of_forall fun p => hφ p)
  · filter_upwards [(hφ z).continuousAt.eventually hsum] with p hp hpW'
    exact hp (hW p hpW')

end Carrier

/-! ### The marked forms -/

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} {π : Y → X}

/-- **Controlled log inclusion with mark decrement, adapted form**: for a marked ideal with `N` a closed
submanifold and coherent ideal, closed boundary members, an admissible centre `C` with simultaneous normal crossings
of `C`, `N`, `E` at the points of `C`, and `j ≤ d`, the transform of `rawLogMarked 𝔪 j` and `rawLogMarked` of the
transform have the same carrier, boundary and mark `d - j`, and on the carrier
`[rawLogMarked 𝔪 j]'.ideal ⊆ (rawLogMarked 𝔪' j).ideal`. -/
theorem geoTransform_rawLogMarked_le_of_adapted (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hEc : ∀ H ∈ 𝔪.E, IsClosed H) (hC : 𝔪.IsAdmissibleCentre C)
    (hAd : ∀ x ∈ C, IsAdaptedAt n C 𝔪.N 𝔪.E x) (hπ : IsBlowupAlong n C π) {j : ℕ} (hj : j ≤ 𝔪.d) :
    ((rawLogMarked 𝔪 j).geoTransform C π).N = (rawLogMarked (𝔪.geoTransform C π) j).N ∧
      ((rawLogMarked 𝔪 j).geoTransform C π).E = (rawLogMarked (𝔪.geoTransform C π) j).E ∧
      ((rawLogMarked 𝔪 j).geoTransform C π).d = 𝔪.d - j ∧ (rawLogMarked (𝔪.geoTransform C π) j).d = 𝔪.d - j ∧
      RestrictLe (geoStrictTransform π C 𝔪.N) ((rawLogMarked 𝔪 j).geoTransform C π).ideal
        (rawLogMarked (𝔪.geoTransform C π) j).ideal := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hle : RestrictLe 𝔪.N 𝔪.ideal (idealPow (vanishingIdeal (n := n) C) (𝔪.d - j + j)) := by
    rw [Nat.sub_add_cancel hj]
    exact HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hN hC.1
      hC.subset_N hC.2.1
  have h := restrictLe_colonAlong_logIter hπ hN.1 hEc (fun x hx _ => hAd x hx) h𝔞hol j (𝔪.d - j) hle
  rw [Nat.sub_add_cancel hj] at h
  exact h

/-- **Controlled log inclusion with mark decrement** (BM08 Lemma 3.3, logarithmic; Włodarczyk 2005,
Lemma `le:inclusions`): for a well-formed marked ideal `𝔪 = (X, N, E, 𝔞, d)`, an admissible centre `C`, the blowup
`π` along `C` and `j ≤ d`, the transform of the `j`-th log derivative marked ideal `(X, N, E, 𝓓_{N,E}^j 𝔞, d - j)` and
the `j`-th log derivative marked ideal of the transform `𝔪'` have the same carrier `N'`, the same boundary
`strict E ++ [π⁻¹C]` and the same mark `d - j`, and on `N'` the ideal of the first is contained in that of the
second. -/
theorem geoTransform_rawLogMarked_le (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {j : ℕ} (hj : j ≤ 𝔪.d) :
    ((rawLogMarked 𝔪 j).geoTransform C π).N = (rawLogMarked (𝔪.geoTransform C π) j).N ∧
      ((rawLogMarked 𝔪 j).geoTransform C π).E = (rawLogMarked (𝔪.geoTransform C π) j).E ∧
      ((rawLogMarked 𝔪 j).geoTransform C π).d = 𝔪.d - j ∧ (rawLogMarked (𝔪.geoTransform C π) j).d = 𝔪.d - j ∧
      RestrictLe (geoStrictTransform π C 𝔪.N) ((rawLogMarked 𝔪 j).geoTransform C π).ideal
        (rawLogMarked (𝔪.geoTransform C π) j).ideal :=
  geoTransform_rawLogMarked_le_of_adapted 𝔪 h𝔪.isClosedSubmanifold_N h𝔪.isCoherent h𝔪.isSNCDivisor.1 hC
    (fun _ hx => isAdaptedAt_of_hasNormalCrossings (pos_of_isBlowupAlong hπ hx) hC.subset_N h𝔪.isSNCDivisor
      h𝔪.isTransverse hC.2.2 hx) hπ hj

/-- **Carrier-saturated form, adapted hypotheses**: the same inclusion for the carrier-saturated log derivative
marked ideals `carrierLogMarked 𝔪 j = (X, N, E, 𝓓_{N,E}^j 𝔞 + 𝓘_N, d - j)` (proper-carrier ideals). -/
theorem geoTransform_carrierLogMarked_le_of_adapted (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hEc : ∀ H ∈ 𝔪.E, IsClosed H) (hC : 𝔪.IsAdmissibleCentre C)
    (hAd : ∀ x ∈ C, IsAdaptedAt n C 𝔪.N 𝔪.E x) (hπ : IsBlowupAlong n C π) {j : ℕ} (hj : j ≤ 𝔪.d) :
    ((carrierLogMarked 𝔪 j).geoTransform C π).N = (carrierLogMarked (𝔪.geoTransform C π) j).N ∧
      ((carrierLogMarked 𝔪 j).geoTransform C π).E = (carrierLogMarked (𝔪.geoTransform C π) j).E ∧
      ((carrierLogMarked 𝔪 j).geoTransform C π).d = 𝔪.d - j ∧
      (carrierLogMarked (𝔪.geoTransform C π) j).d = 𝔪.d - j ∧
      RestrictLe (geoStrictTransform π C 𝔪.N) ((carrierLogMarked 𝔪 j).geoTransform C π).ideal
        (carrierLogMarked (𝔪.geoTransform C π) j).ideal := by
  obtain ⟨-, -, -, -, hraw⟩ := geoTransform_rawLogMarked_le_of_adapted 𝔪 hN h𝔞 hEc hC hAd hπ hj
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have hπs := hπ.contMDiff
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have h1 : RestrictLe (geoStrictTransform π C 𝔪.N)
      (GermIdeal.pullback (m := n) π (restrictOn n 𝔪.N (rawIter 𝔪.N 𝔪.E 𝔪.ideal j)))
      (GermIdeal.pullback (m := n) π (rawIter 𝔪.N 𝔪.E 𝔪.ideal j)) :=
    restrictLe_pullback_restrictOn hπs
      (fun p hp => geoStrictTransform_subset_preimage hπs.continuous hN.1 hp)
      (holomorphicAt_of_mem_logIter h𝔞hol j)
  refine restrictLe_trans (restrictLe_colonAlong_of_restrictLe h1) (restrictLe_trans hraw ?_)
  refine restrictLe_restrictOn ?_
  refine holomorphicAt_of_mem_logIter ?_ j
  exact fun _ _ hg => hg.1

/-- **Carrier-saturated form** for a well-formed marked ideal and an admissible centre. -/
theorem geoTransform_carrierLogMarked_le (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {j : ℕ} (hj : j ≤ 𝔪.d) :
    ((carrierLogMarked 𝔪 j).geoTransform C π).N = (carrierLogMarked (𝔪.geoTransform C π) j).N ∧
      ((carrierLogMarked 𝔪 j).geoTransform C π).E = (carrierLogMarked (𝔪.geoTransform C π) j).E ∧
      ((carrierLogMarked 𝔪 j).geoTransform C π).d = 𝔪.d - j ∧
      (carrierLogMarked (𝔪.geoTransform C π) j).d = 𝔪.d - j ∧
      RestrictLe (geoStrictTransform π C 𝔪.N) ((carrierLogMarked 𝔪 j).geoTransform C π).ideal
        (carrierLogMarked (𝔪.geoTransform C π) j).ideal :=
  geoTransform_carrierLogMarked_le_of_adapted 𝔪 h𝔪.isClosedSubmanifold_N h𝔪.isCoherent h𝔪.isSNCDivisor.1 hC
    (fun _ hx => isAdaptedAt_of_hasNormalCrossings (pos_of_isBlowupAlong hπ hx) hC.subset_N h𝔪.isSNCDivisor
      h𝔪.isTransverse hC.2.2 hx) hπ hj

end

end Hironaka.HironakaG8LogControlledMarked
