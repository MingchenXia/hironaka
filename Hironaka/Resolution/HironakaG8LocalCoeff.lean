import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Resolution.HironakaG8CoeffClass
import Hironaka.Resolution.HironakaG8LogClosureHistory
import Hironaka.Resolution.HironakaG8LogDerivEtale

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient ideal is locally equivalent to the marked ideal (G8 lane, run 0080, round 4; (B') port P3, local form)

Blueprint: `hironaka-g8-resume-local-coefficient.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P3),
§6 ("modules 10–12 need ... P3 (local)").

`HironakaG8CoeffClass` proves BM08 Corollary 3.11 for an empty boundary GLOBALLY (`MixedEquiv M (coeffMarkedAlong M)`).
The (B') induction compares marked ideals on open subsets of later stages (masks, tangent opens, overlaps), so it needs the
LOCAL relation `HironakaG8LocalHistory.LocWPEquiv`.  This module proves it by the coinduction principle
`HironakaG8LocalStable.LocEquiv.of_isLocStable`, applied to the **sandwich relation**:

* `closureIdeal P L = ∑_{i<d} (𝒟_{N,E}^i 𝔞)^{L/(d-i)}` (the logarithmic closure of `P = (N, E, 𝔞, d)` at a common multiple
  `L` of the marks `d - i`);
* `Sandwich P Q`: `P` in the native domain, `Q` on the same carrier and boundary with mark `L = d e`, and on the carrier
  `𝔞^e ⊆ Q ⊆ closureIdeal P L`;
* `Sandwich.cosupp_eq`: sandwiched marked ideals have the same cosupport (BM08 Lemma 3.9);
* **`isLocStable_sandwich`**: the relation is stable under one admissible blowup (power transform, Giraud's lemma for the
  logarithmic derivatives `HironakaG8LogControlledMarked.geoTransform_rawLogMarked_le`, transforms of common-mark sums
  `HironakaG8LogFiniteSumTransform.restrictLe_colonAlong_finSum_le`), one product with a line
  (`HironakaActualProjectionNativeLogIdeal.projection_native_logIdeal_iterate_eq`) and one open restriction
  (`pullback_val_rawIter`, from `HironakaG8LogDerivEtale.pullback_logDerivIdealAlong_of_localInverse`);
* **`locEquiv_of_sandwich`**; applications: **`locEquiv_logClosure`** (`P ≈ 𝓒^{d-1}(P)`, any boundary; BM08 Thm 3.10 /
  Cor 3.11, logarithmic, local) and **`locEquiv_coeffMarkedAlong_of_nil`** (`P ≈ coeffMarkedAlong P` for `E = []`; BM08
  Cor 3.11 / §8.1, local), with the `LocWPEquiv` forms.

Sorry-free.  Universe `0` (the logarithmic families are stated for `CMfd.{0}`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LocalCoeff

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism RelativePrincipalizationSpan
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.IdealWeightPowers (idealPow)
open Hironaka.GermIdealOrder (cosupport)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.RestrictedIdealQuotient (colonAlong)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.CoefficientIdeal (msum sumExp mul_sumExp)
open Hironaka.HomogenizedIdealAlong (coeffMarkedAlong derivMarkedAlong)
open Hironaka.DerivativeIdealAlong (iterDerivIdealAlong)
open Hironaka.HironakaActualIntrinsicLogDerivativeFrame (logDerivIdealAlong)
open Hironaka.HironakaActualIteratedLogMarkedFamily (rawIter rawLogMarked bmCommonMark bmFiniteSum
  bmCommonMark_spec)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal
  projection_test_isInvDomain)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked)
open Hironaka.HironakaActualOriginalPowerTransform (original_power_transform)
open Hironaka.HironakaG8LogControlledInclusion (holomorphicAt_of_mem_logIter)
open Hironaka.HironakaG8LogFiniteSumTransform (finSumIdeal_congr mem_finSumIdeal_of_mem
  restrictLe_finSumIdeal restrictLe_colonAlong_finSum_le restrictLe_rawLogMarked_idealPow)
open Hironaka.HironakaG8LogFiniteSumCut (cosupport_finSumIdeal cosupp_subset_cosupp_rawLogMarked)
open Hironaka.HironakaG8LogControlledMarked (geoTransform_rawLogMarked_le
  restrictLe_colonAlong_of_restrictLe)
open Hironaka.HironakaG8LogMixedHistory (restrictLe_pullback_of_restrictLe)
open Hironaka.HironakaG8LogClosureHistory (pullback_finSumIdeal_le)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform)
open scoped ProductComplexManifold

noncomputable section

/-! ### The sandwich relation -/

section Sandwich

variable {m : ℕ} {Y : CMfd.{0} m}

/-- **The logarithmic closure ideal at a common mark `L`**: `∑_{i<d} (𝒟_{N,E}^i 𝔞)^{L/(d-i)}`. -/
def closureIdeal (P : MarkedIdeal m Y) (L : ℕ) : GermIdeal m Y :=
  finSumIdeal (fun i => idealPow (rawIter P.N P.E P.ideal i) (L / (P.d - i))) P.d

/-- **The sandwich relation**: `P` in the native domain; `Q` on the same carrier and boundary, with mark `L = d e` a common
multiple of the marks `d - i` (`i < d`), and on the carrier `𝔞^e ⊆ Q ⊆ closureIdeal P L`. -/
structure Sandwich (P Q : MarkedIdeal m Y) : Prop where
  inv : ∃ r, IsInvDomain r P
  N_eq : Q.N = P.N
  E_eq : Q.E = P.E
  d_pos : 0 < Q.d
  dvd : ∀ i < P.d, P.d - i ∣ Q.d
  hol : ∀ x g, Q.ideal.mem x g → HolomorphicAt m g x
  lower : ∃ e, Q.d = P.d * e ∧ RestrictLe P.N (idealPow P.ideal e) Q.ideal
  upper : RestrictLe P.N Q.ideal (closureIdeal P Q.d)

theorem hol_of_isInvDomain {r : ℕ} {P : MarkedIdeal m Y} (hP : IsInvDomain r P) :
    ∀ x g, P.ideal.mem x g → HolomorphicAt m g x := fun _ _ hg =>
  GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg

theorem closureIdeal_hol (P : MarkedIdeal m Y) (L : ℕ) :
    ∀ x g, (closureIdeal P L).mem x g → HolomorphicAt m g x := fun _ _ hg => hg.1

/-- **Sandwiched marked ideals have the same cosupport** (BM08 Lemma 3.9). -/
theorem Sandwich.cosupp_eq {P Q : MarkedIdeal m Y} (h : Sandwich P Q) : P.cosupp = Q.cosupp := by
  obtain ⟨r, hP⟩ := h.inv
  obtain ⟨e, hL, hlow⟩ := h.lower
  have hd := hP.one_le_d
  have hN := hP.isWellFormed.isClosedSubmanifold_N.2
  have hIhol := hol_of_isInvDomain hP
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · have := h.d_pos
      rw [hL, h0, Nat.mul_zero] at this
      exact absurd this (lt_irrefl 0)
    · exact h0
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ cosupport m P.N (closureIdeal P Q.d) Q.d := by
      unfold closureIdeal
      rw [cosupport_finSumIdeal (fun i x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
      refine ⟨P.cosupp_subset_N hx, fun i hi => ?_⟩
      obtain ⟨k, hk⟩ := h.dvd i hi
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · have := h.d_pos
          rw [hk, h0, Nat.mul_zero] at this
          exact absurd this (lt_irrefl 0)
        · exact h0
      have hdiv : Q.d / (P.d - i) = k := by
        rw [hk]
        exact Nat.mul_div_cancel_left k (by omega)
      rw [hdiv]
      have h1 := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN
        (holomorphicAt_of_mem_logIter (N := P.N) (E := P.E) hIhol i) hk1 (P.d - i)
      rw [← hk] at h1
      change x ∈ cosupport m P.N (idealPow ((logDerivIdealAlong P.N P.E)^[i] P.ideal) k) Q.d
      rw [h1]
      exact cosupp_subset_cosupp_rawLogMarked P hIhol (by omega) hx
    have h2 := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.upper Q.d hx'
    show x ∈ cosupport m Q.N Q.ideal Q.d
    rw [h.N_eq]
    exact h2
  · intro x hx
    have hx' : x ∈ cosupport m P.N Q.ideal Q.d := by
      have := hx
      unfold MarkedIdeals.MarkedIdeal.cosupp at this
      rw [h.N_eq] at this
      exact this
    have h1 := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hlow Q.d hx'
    rw [hL, MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN hIhol he P.d] at h1
    exact h1

end Sandwich

/-! ### Logarithmic derivatives on open subsets -/

section Restrict

variable {m : ℕ} {Y : CMfd.{0} m}

/-- **Iterated logarithmic derivatives commute with restriction to an open subset.** -/
theorem pullback_val_rawIter (U : Opens Y) (N : Set Y) (E : List (Set Y)) {A : GermIdeal m Y}
    (hA : ∀ x g, A.mem x g → HolomorphicAt m g x) :
    ∀ i, GermIdeal.pullback (m := m) (Subtype.val : U → Y) (rawIter N E A i) =
      rawIter (X := CMfd.of (n := m) U) ((Subtype.val : U → Y) ⁻¹' N) (E.map ((Subtype.val : U → Y) ⁻¹' ·))
        (GermIdeal.pullback (m := m) (Subtype.val : U → Y) A) i
  | 0 => rfl
  | i + 1 => by
    show GermIdeal.pullback (m := m) (Subtype.val : U → Y) ((logDerivIdealAlong N E)^[i + 1] A) =
      (logDerivIdealAlong (M := CMfd.of (n := m) U) ((Subtype.val : U → Y) ⁻¹' N)
        (E.map ((Subtype.val : U → Y) ⁻¹' ·)))^[i + 1] (GermIdeal.pullback (m := m) (Subtype.val : U → Y) A)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have ih := pullback_val_rawIter U N E hA i
    change GermIdeal.pullback (m := m) (Subtype.val : U → Y) (logDerivIdealAlong N E (rawIter N E A i)) =
      logDerivIdealAlong (M := CMfd.of (n := m) U) ((Subtype.val : U → Y) ⁻¹' N)
        (E.map ((Subtype.val : U → Y) ⁻¹' ·))
        (rawIter (X := CMfd.of (n := m) U) ((Subtype.val : U → Y) ⁻¹' N) (E.map ((Subtype.val : U → Y) ⁻¹' ·))
          (GermIdeal.pullback (m := m) (Subtype.val : U → Y) A) i)
    rw [← ih]
    exact HironakaG8LogDerivEtale.pullback_logDerivIdealAlong_of_localInverse
      (fun y => ⟨DerivativeIdealAlongEtale.openInv U y, DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
      (holomorphicAt_of_mem_logIter hA i)

end Restrict

/-! ### Stability under the local test actions -/

section Stable

variable {m : ℕ} {Y : CMfd.{0} m}

theorem Sandwich.one_le_e {P Q : MarkedIdeal m Y} (h : Sandwich P Q) {e : ℕ} (hL : Q.d = P.d * e) : 1 ≤ e := by
  rcases Nat.eq_zero_or_pos e with h0 | h0
  · have := h.d_pos
    rw [hL, h0, Nat.mul_zero] at this
    exact absurd this (lt_irrefl 0)
  · exact h0

/-- **One admissible blowup** (power transform; Giraud's lemma for logarithmic derivatives; transforms of common-mark
sums). -/
theorem sandwich_geoTransform {P Q : MarkedIdeal m Y} (h : Sandwich P Q) {C : Set Y} {Z : CMfd.{0} m} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hC : P.IsAdmissibleCentre C) :
    Sandwich (P.geoTransform C π) (Q.geoTransform C π) := by
  obtain ⟨r, hP⟩ := h.inv
  have hwf := hP.isWellFormed
  have hNc : IsClosed P.N := hwf.isClosedSubmanifold_N.1
  have hIhol := hol_of_isInvDomain hP
  obtain ⟨e, hL, hlow⟩ := h.lower
  have he := h.one_le_e hL
  have hT : IsGeoTestTower P (.step .refl C π hπ) := ⟨trivial, hC⟩
  have hP' : IsInvDomain r (P.geoTransform C π) :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hP (.step .refl C π hπ) hT
  have hI'hol := hol_of_isInvDomain hP'
  have hNQ : Q.N = P.N := h.N_eq
  have hsub : ∀ q ∈ geoStrictTransform π C P.N, π q ∈ P.N := fun q hq =>
    BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hq
  refine ⟨⟨r, hP'⟩, ?_, ?_, h.d_pos, h.dvd, fun _ _ hg => hg.1, ⟨e, hL, ?_⟩, ?_⟩
  · show geoStrictTransform π C Q.N = geoStrictTransform π C P.N
    rw [hNQ]
  · show Q.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] = P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    rw [h.E_eq]
  · have hpow := (original_power_transform P hP e he (.step .refl C π hπ) hT).2
    have h1 : RestrictLe (geoStrictTransform π C P.N) (idealPow (P.geoTransform C π).ideal e)
        ((powerMarked P e).geoTransform C π).ideal := hpow.ge
    have h2 : RestrictLe (geoStrictTransform π C P.N) ((powerMarked P e).geoTransform C π).ideal
        (Q.geoTransform C π).ideal := by
      show RestrictLe (geoStrictTransform π C P.N)
        (colonAlong m (geoStrictTransform π C P.N) (GermIdeal.pullback π (idealPow P.ideal e))
          (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) (P.d * e)))
        (colonAlong m (geoStrictTransform π C Q.N) (GermIdeal.pullback π Q.ideal)
          (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) Q.d))
      rw [hNQ, hL]
      exact restrictLe_colonAlong_of_restrictLe (restrictLe_pullback_of_restrictLe hπ.contMDiff hsub h.hol hlow)
    exact DerivativeIdealAlongTransform.restrictLe_trans h1 h2
  · show RestrictLe (geoStrictTransform π C P.N)
      (colonAlong m (geoStrictTransform π C Q.N) (GermIdeal.pullback π Q.ideal)
        (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) Q.d))
      (closureIdeal (P.geoTransform C π) Q.d)
    rw [hNQ]
    have h1 : RestrictLe (geoStrictTransform π C P.N)
        (colonAlong m (geoStrictTransform π C P.N) (GermIdeal.pullback π Q.ideal)
          (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) Q.d))
        (colonAlong m (geoStrictTransform π C P.N) (GermIdeal.pullback π (closureIdeal P Q.d))
          (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) Q.d)) :=
      restrictLe_colonAlong_of_restrictLe
        (restrictLe_pullback_of_restrictLe hπ.contMDiff hsub (closureIdeal_hol P Q.d) h.upper)
    have h2 := restrictLe_colonAlong_finSum_le hπ hNc (A := fun i => rawIter P.N P.E P.ideal i)
      (d := fun i => P.d - i) (k := fun i => Q.d / (P.d - i)) (m := P.d) (L := Q.d)
      (fun i _ => holomorphicAt_of_mem_logIter (N := P.N) (E := P.E) hIhol i)
      (fun i hi => restrictLe_rawLogMarked_idealPow P hwf hC (by omega : i ≤ P.d))
      (fun i hi => Nat.mul_div_cancel' (h.dvd i hi))
    have h3 : RestrictLe (geoStrictTransform π C P.N)
        (finSumIdeal (fun i => idealPow (colonAlong m (geoStrictTransform π C P.N)
          (GermIdeal.pullback π (rawIter P.N P.E P.ideal i))
          (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) (P.d - i))) (Q.d / (P.d - i))) P.d)
        (closureIdeal (P.geoTransform C π) Q.d) := by
      unfold closureIdeal
      refine restrictLe_finSumIdeal (fun i _ x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
        fun i hi => ?_
      have h4 := (geoTransform_rawLogMarked_le P hwf hC hπ (j := i) (by omega)).2.2.2.2
      exact MarkedIdealOperationsAlong.restrictLe_idealPow
        (holomorphicAt_of_mem_logIter (N := (P.geoTransform C π).N) (E := (P.geoTransform C π).E) hI'hol i) h4 _
    exact DerivativeIdealAlongTransform.restrictLe_trans h1 (DerivativeIdealAlongTransform.restrictLe_trans h2 h3)

/-- **One product with a line** (the projection log equality). -/
theorem sandwich_projectionTest {P Q : MarkedIdeal m Y} (h : Sandwich P Q) :
    Sandwich (projectionTest P) (projectionTest Q) := by
  obtain ⟨r, hP⟩ := h.inv
  have hwf := hP.isWellFormed
  have hIhol := hol_of_isInvDomain hP
  obtain ⟨e, hL, hlow⟩ := h.lower
  have hφ := ProductComplexManifold.contMDiff_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hNQ : Q.N = P.N := h.N_eq
  refine ⟨⟨r + 1, projection_test_isInvDomain P hP⟩, ?_, ?_, h.d_pos, h.dvd, fun _ _ hg => hg.1, ⟨e, hL, ?_⟩, ?_⟩
  · show (Prod.fst : projectionAmbient Y → Y) ⁻¹' Q.N = (Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N
    rw [hNQ]
  · show Q.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
      P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]
    rw [h.E_eq]
  · show RestrictLe ((Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N)
      (idealPow (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) P.ideal) e)
      (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) Q.ideal)
    rw [← HironakaActualNonregularCoefficientNaturality.pullback_idealPow hφ (fun hg => hIhol _ _ hg) e]
    exact restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) h.hol hlow
  · show RestrictLe ((Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N)
      (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) Q.ideal)
      (closureIdeal (projectionTest P) Q.d)
    refine DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) (closureIdeal_hol P Q.d) h.upper) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le hφ (A := fun i => (logDerivIdealAlong P.N P.E)^[i] P.ideal)
      (fun i => holomorphicAt_of_mem_logIter (N := P.N) (E := P.E) hIhol i)
      (k := fun i => Q.d / (P.d - i)) (m := P.d) hg
    have heq : finSumIdeal (fun i => idealPow (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y)
        ((logDerivIdealAlong P.N P.E)^[i] P.ideal)) (Q.d / (P.d - i))) P.d = closureIdeal (projectionTest P) Q.d := by
      unfold closureIdeal
      refine finSumIdeal_congr fun i _ => ?_
      rw [HironakaActualProjectionNativeLogIdeal.projection_native_logIdeal_iterate_eq P.ideal hwf.isCoherent
        hwf.isClosedSubmanifold_N hwf.isSNCDivisor hwf.isTransverse i]
      rfl
    rw [heq] at h1
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)

/-- **One restriction to an open subset.** -/
theorem sandwich_pullback_val {P Q : MarkedIdeal m Y} (h : Sandwich P Q) (U : Opens Y) :
    Sandwich (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
      (MarkedIdeal.pullback (Subtype.val : U → Y) Q) := by
  obtain ⟨r, hP⟩ := h.inv
  have hIhol := hol_of_isInvDomain hP
  obtain ⟨e, hL, hlow⟩ := h.lower
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ (Subtype.val : U → Y) := contMDiff_subtype_val
  refine ⟨⟨r, InvDomainTowerAlong.isInvDomain_pullback_val U hP⟩, ?_, ?_, h.d_pos, h.dvd,
    fun _ _ hg => hg.1, ⟨e, hL, ?_⟩, ?_⟩
  · show (Subtype.val : U → Y) ⁻¹' Q.N = (Subtype.val : U → Y) ⁻¹' P.N
    rw [h.N_eq]
  · show Q.E.map ((Subtype.val : U → Y) ⁻¹' ·) = P.E.map ((Subtype.val : U → Y) ⁻¹' ·)
    rw [h.E_eq]
  · show RestrictLe ((Subtype.val : U → Y) ⁻¹' P.N)
      (idealPow (GermIdeal.pullback (m := m) (Subtype.val : U → Y) P.ideal) e)
      (GermIdeal.pullback (m := m) (Subtype.val : U → Y) Q.ideal)
    rw [← HironakaActualNonregularCoefficientNaturality.pullback_idealPow hval (fun hg => hIhol _ _ hg) e]
    exact restrictLe_pullback_of_restrictLe hval (fun _ hp => hp) h.hol hlow
  · show RestrictLe ((Subtype.val : U → Y) ⁻¹' P.N)
      (GermIdeal.pullback (m := m) (Subtype.val : U → Y) Q.ideal)
      (closureIdeal (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P) Q.d)
    refine DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hval (fun _ hp => hp) (closureIdeal_hol P Q.d) h.upper) ?_
    intro z _ g hg
    have h1 := pullback_finSumIdeal_le hval (A := fun i => rawIter P.N P.E P.ideal i)
      (fun i => holomorphicAt_of_mem_logIter (N := P.N) (E := P.E) hIhol i)
      (k := fun i => Q.d / (P.d - i)) (m := P.d) hg
    have heq : finSumIdeal (fun i => idealPow (GermIdeal.pullback (m := m) (Subtype.val : U → Y)
        (rawIter P.N P.E P.ideal i)) (Q.d / (P.d - i))) P.d =
        closureIdeal (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P) Q.d := by
      unfold closureIdeal
      refine finSumIdeal_congr fun i _ => ?_
      rw [pullback_val_rawIter U P.N P.E hIhol i]
      rfl
    rw [heq] at h1
    exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)

/-- **The sandwich relation is stable under the local test actions** (blowups, products with a line, open
restrictions). -/
theorem isLocStable_sandwich (κ : Kinds) :
    IsLocStable.{0} κ (fun {m} {Y} P Q => Sandwich (m := m) (Y := Y) P Q) where
  E_eq h := h.E_eq
  cosupp_eq h := h.cosupp_eq
  controlled h _ _ _ hπ hC := sandwich_geoTransform h hπ hC
  projection _ _ _ _ _ h := sandwich_projectionTest h
  restrict h U := sandwich_pullback_val h U

end Stable

/-! ### Applications -/

section Apply

variable {n : ℕ} {X : CMfd.{0} n} {κ : Kinds}

/-- **Sandwiched marked ideals are locally equivalent** (kinds without exceptional blowups). -/
theorem locEquiv_of_sandwich (hexc : κ.exc = false) {P Q : MarkedIdeal n X} (h : Sandwich P Q) : LocEquiv κ P Q :=
  LocEquiv.of_isLocStable (isLocStable_sandwich κ) hexc h

/-- The logarithmic closure `𝓒^{d-1}(P) = bmFiniteSum (rawLogMarked P) d` is sandwiched. -/
theorem sandwich_logClosure {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) :
    Sandwich P (bmFiniteSum (rawLogMarked P) P.d) := by
  have hd := hP.one_le_d
  have hpos : ∀ i < P.d, 0 < (rawLogMarked P i).d := fun i hi => by
    show 0 < P.d - i
    omega
  obtain ⟨hL, hspec⟩ := bmCommonMark_spec (rawLogMarked P) P.d hpos
  refine ⟨⟨r, hP⟩, rfl, rfl, hL, fun i hi => (hspec i hi).1, fun _ _ hg => hg.1,
    ⟨bmCommonMark (rawLogMarked P) P.d / P.d, (hspec 0 (by omega)).2.2.symm, ?_⟩, ?_⟩
  · intro x _ g hg
    refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_
      (GermIdealOrder.holomorphicAt_of_mem_idealPow hg))
    exact mem_finSumIdeal_of_mem (J := fun i => idealPow (rawLogMarked P i).ideal
      (bmCommonMark (rawLogMarked P) P.d / (rawLogMarked P i).d)) (i := 0) (by omega) hg
      (GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
  · exact DerivativeIdealAlongTransform.restrictLe_refl (fun _ _ hg => hg.1)

/-- **A marked ideal of the native domain is locally equivalent to its logarithmic closure** (BM08 Theorem 3.10 /
Corollary 3.11, logarithmic, with local test transformations; any boundary). -/
theorem locEquiv_logClosure (hexc : κ.exc = false) {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) :
    LocEquiv κ P (bmFiniteSum (rawLogMarked P) P.d) :=
  locEquiv_of_sandwich hexc (sandwich_logClosure P hP)

/-- The coefficient ideal of a marked ideal with empty boundary is sandwiched. -/
theorem sandwich_coeffMarkedAlong_of_nil {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) (hE : P.E = []) :
    Sandwich P (coeffMarkedAlong P) := by
  have hd := hP.one_le_d
  have hprod : 0 < (Finset.range P.d).prod (fun j => P.d - j) :=
    Finset.prod_pos fun j hj => by
      have := Finset.mem_range.mp hj
      omega
  have hmul : ∀ i < P.d, (P.d - i) * sumExp (fun j => P.d - j) P.d i = (Finset.range P.d).prod (fun j => P.d - j) :=
    fun i hi => mul_sumExp (fun j => P.d - j) hi
  have hdiv : ∀ i < P.d, sumExp (fun j => P.d - j) P.d i = (Finset.range P.d).prod (fun j => P.d - j) / (P.d - i) :=
    fun i hi => by
      rw [← hmul i hi]
      exact (Nat.mul_div_cancel_left _ (by omega)).symm
  refine ⟨⟨r, hP⟩, rfl, rfl, hprod, fun i hi => ⟨_, (hmul i hi).symm⟩, fun _ _ hg => hg.1,
    ⟨sumExp (fun j => P.d - j) P.d 0, (hmul 0 (by omega)).symm, ?_⟩, ?_⟩
  · intro x _ g hg
    refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_
      (GermIdealOrder.holomorphicAt_of_mem_idealPow hg))
    exact mem_finSumIdeal_of_mem (J := fun i => idealPow (iterDerivIdealAlong P.N P.ideal i)
      (sumExp (fun j => P.d - j) P.d i)) (i := 0) (by omega) hg (GermIdealOrder.holomorphicAt_of_mem_idealPow hg)
  · show RestrictLe P.N (finSumIdeal (fun i => idealPow (iterDerivIdealAlong P.N P.ideal i)
      (sumExp (fun j => P.d - j) P.d i)) P.d) (closureIdeal P ((Finset.range P.d).prod (fun j => P.d - j)))
    have heq : finSumIdeal (fun i => idealPow (iterDerivIdealAlong P.N P.ideal i)
        (sumExp (fun j => P.d - j) P.d i)) P.d = closureIdeal P ((Finset.range P.d).prod (fun j => P.d - j)) := by
      unfold closureIdeal
      refine finSumIdeal_congr fun i hi => ?_
      rw [hE, HironakaG8CoeffClass.rawIter_nil, hdiv i hi]
    rw [heq]
    exact DerivativeIdealAlongTransform.restrictLe_refl (fun _ _ hg => hg.1)

/-- **BM08 Corollary 3.11 for an empty boundary, local form**: a marked ideal of the native domain with `E = []` is
locally equivalent to its coefficient ideal along the carrier (kinds without exceptional blowups). -/
theorem locEquiv_coeffMarkedAlong_of_nil (hexc : κ.exc = false) {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P)
    (hE : P.E = []) : LocEquiv κ P (coeffMarkedAlong P) :=
  locEquiv_of_sandwich hexc (sandwich_coeffMarkedAlong_of_nil P hP hE)

/-- **The `LocWPEquiv` form** (the relation of the (B') induction). -/
theorem locWPEquiv_coeffMarkedAlong_of_nil {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) (hE : P.E = []) :
    LocWPEquiv P (coeffMarkedAlong P) :=
  locEquiv_coeffMarkedAlong_of_nil rfl P hP hE

/-- **The `LocWPEquiv` form of the logarithmic closure.** -/
theorem locWPEquiv_logClosure {r : ℕ} (P : MarkedIdeal n X) (hP : IsInvDomain r P) :
    LocWPEquiv P (bmFiniteSum (rawLogMarked P) P.d) :=
  locEquiv_logClosure rfl P hP

end Apply

end

end Hironaka.HironakaG8LocalCoeff
