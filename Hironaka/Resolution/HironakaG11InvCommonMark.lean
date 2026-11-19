import Hironaka.Resolution.HironakaG8MixedEquiv
import Hironaka.Resolution.HironakaG11InvTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Common-mark normalization of window records (G11 route step (3c))

Blueprint: `hironaka-g11-inv-common-mark.tex`.  Route notes: `work/hironaka-resume-20261111/G11B/INVARIANT-ENTRY-CHECK.md`
(§2, §7) and `ROUTE-r2.md` §2.

The first entry of `CanonicalCentres.canonicalInvariant` is a RAW order, so values of records with different marks are not
comparable (`HironakaG8MixedOrderInvariance.canonicalInvariant_fst_powerMarked_two_ne`).  Before any comparison of the
window records of two overlapping windows, every record is replaced by a power with ONE common mark `D`:
`(𝔞, d) ↦ (𝔞^{D/d}, D)` (`HironakaActualPowerBoundaryExponents.powerMarked`).  The equivalence `(𝔞, d) ~ (𝔞^k, kd)` in
Bierstone–Milman's sense is lane G8's `HironakaG8MixedEquiv.mixedEquiv_powerMarked` (Włodarczyk 2005, §2: `(𝓘, μ) ≃
(𝓘^k, kμ)`; BM08 Lemma 3.7(1)).  This module adds the corollaries the gluing of windows needs:

* **weak form of (3c)**: `wEquiv_powerMarked` (`(𝔞, d) ≃ (𝔞^e, de)` in Włodarczyk's sense, `MarkedIdealEquivalence.WEquiv`),
  `wEquiv_projectionTest_powerMarked` (after a product with a line);
* **normalization to a common mark**: `powerMarked_div_d`, `one_le_div_of_dvd`, `mixedEquiv_normalize`,
  **`MixedEquiv.normalize`** (two equivalent records with marks dividing `D` become equivalent records of the SAME mark
  `D`), `wEquiv_normalize`; a finite family of marks: `dvd_prodMark`, `prodMark_pos` (`D = ∏ d_i`);
* **transport**: `pullback_powerMarked` (pullback along a holomorphic map commutes with the power, coherent ideal),
  `restrictEquiv_powerMarked`, **`restrictEquiv_pullback_powerMarked`** (records that are `RestrictEquiv` after transport
  stay so after normalization: the hypothesis of `HironakaG11InvTransport.inv_eq_on_overlap`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvCommonMark

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  RelativePrincipalizationSpan IdealWeightPowers
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaActualProjectionTestRecord (projectionTest)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.MarkedIdealOperationsAlong (restrictLe_idealPow)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)

noncomputable section

variable {n : ℕ}

/-! ### (3c) in Włodarczyk's sense -/

section Weak

variable {X : CMfd.{u} n}

/-- The mark of a power. -/
@[simp] theorem powerMarked_d (M : MarkedIdeal n X) (e : ℕ) : (powerMarked M e).d = M.d * e := rfl

/-- **`(𝔞, d) ≃ (𝔞^e, de)`** in Włodarczyk's sense (`WEquiv`; `e ≥ 1`, native domain). -/
theorem wEquiv_powerMarked {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e) :
    WEquiv M (powerMarked M e) :=
  (mixedEquiv_powerMarked M hM he).wEquiv

/-- **The same after one product with a line** (the input of the normalized order detection
`HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv`). -/
theorem wEquiv_projectionTest_powerMarked {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ}
    (he : 1 ≤ e) : WEquiv (projectionTest M) (projectionTest (powerMarked M e)) :=
  (mixedEquiv_powerMarked M hM he).projectionTest_wEquiv

end Weak

/-! ### Normalization to a common mark -/

section Normalize

variable {X : CMfd.{u} n}

/-- If `d ∣ D` and `0 < D` then `1 ≤ D / d`. -/
theorem one_le_div_of_dvd {d D : ℕ} (hD : 0 < D) (h : d ∣ D) : 1 ≤ D / d := by
  obtain ⟨c, rfl⟩ := h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at hD
  · rw [Nat.mul_div_cancel_left c hd]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at hD
    · exact hc

/-- **The normalized record has the common mark** `D` (`d ∣ D`). -/
theorem powerMarked_div_d (M : MarkedIdeal n X) {D : ℕ} (h : M.d ∣ D) : (powerMarked M (D / M.d)).d = D :=
  Nat.mul_div_cancel' h

/-- **Normalization**: `M ~ M^{D/d}` and the latter has mark `D` (`d ∣ D`, `0 < D`, native domain). -/
theorem mixedEquiv_normalize {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {D : ℕ} (hD : 0 < D)
    (h : M.d ∣ D) : MixedEquiv M (powerMarked M (D / M.d)) ∧ (powerMarked M (D / M.d)).d = D :=
  ⟨mixedEquiv_powerMarked M hM (one_le_div_of_dvd hD h), powerMarked_div_d M h⟩

/-- **Two equivalent records become equivalent records of one common mark**: if `M ~ M'` and both marks divide
`D > 0`, then `M^{D/d} ~ M'^{D/d'}`, both of mark `D`. -/
theorem MixedEquiv.normalize {k k' : ℕ} {M M' : MarkedIdeal n X} (h : MixedEquiv M M') (hM : IsInvDomain k M)
    (hM' : IsInvDomain k' M') {D : ℕ} (hD : 0 < D) (h₁ : M.d ∣ D) (h₂ : M'.d ∣ D) :
    MixedEquiv (powerMarked M (D / M.d)) (powerMarked M' (D / M'.d)) ∧
      (powerMarked M (D / M.d)).d = D ∧ (powerMarked M' (D / M'.d)).d = D :=
  ⟨((mixedEquiv_normalize M hM hD h₁).1.symm.trans h).trans (mixedEquiv_normalize M' hM' hD h₂).1,
    powerMarked_div_d M h₁, powerMarked_div_d M' h₂⟩

/-- The weak form: `M ≃ M^{D/d}` in Włodarczyk's sense. -/
theorem wEquiv_normalize {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {D : ℕ} (hD : 0 < D)
    (h : M.d ∣ D) : WEquiv M (powerMarked M (D / M.d)) :=
  (mixedEquiv_normalize M hM hD h).1.wEquiv

/-- **A common mark for a finite family of marks**: every mark divides the product. -/
theorem dvd_prodMark {ι : Type*} [Fintype ι] (d : ι → ℕ) (i : ι) : d i ∣ ∏ j, d j :=
  Finset.dvd_prod_of_mem d (Finset.mem_univ i)

/-- The product of positive marks is positive. -/
theorem prodMark_pos {ι : Type*} [Fintype ι] (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i) : 0 < ∏ j, d j :=
  Finset.prod_pos fun i _ => hd i

end Normalize

/-! ### Transport along holomorphic maps and restricted equivalence -/

section Transport

open Hironaka.MarkedIdealBiholomorphism

variable {X X' : CMfd.{u} n}

/-- **Pullback commutes with the power** (holomorphic map, coherent ideal). -/
theorem pullback_powerMarked {φ : X' → X} (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (e : ℕ) :
    MarkedIdeal.pullback φ (powerMarked M e) = powerMarked (MarkedIdeal.pullback φ M) e := by
  show (⟨φ ⁻¹' M.N, M.E.map (φ ⁻¹' ·), GermIdeal.pullback (m := n) φ (idealPow M.ideal e), M.d * e⟩ :
      MarkedIdeal n X') = ⟨φ ⁻¹' M.N, M.E.map (φ ⁻¹' ·), idealPow (GermIdeal.pullback (m := n) φ M.ideal) e, M.d * e⟩
  rw [BlowupExceptionalDivisor.pullback_idealPow hφ hM e]

/-- **Restricted equivalence passes to powers.** -/
theorem restrictEquiv_powerMarked {M M' : MarkedIdeal n X} (h : RestrictEquiv M M')
    (hM : ∀ x g, M.ideal.mem x g → HolomorphicAt n g x) (hM' : ∀ x g, M'.ideal.mem x g → HolomorphicAt n g x)
    (e : ℕ) : RestrictEquiv (powerMarked M e) (powerMarked M' e) where
  N_eq := h.N_eq
  E_eq := h.E_eq
  d_eq := by show M.d * e = M'.d * e; rw [h.d_eq]
  le := restrictLe_idealPow hM' h.le e
  ge := restrictLe_idealPow hM h.ge e

/-- **Records that are restricted-equivalent after transport stay so after normalization**: if
`RestrictEquiv (Φ^* M) M'` then `RestrictEquiv (Φ^*(M^e)) (M'^e)` (holomorphic `Φ`, coherent ideals) -- the hypothesis of
`HironakaG11InvTransport.inv_eq_on_overlap` for the normalized records. -/
theorem restrictEquiv_pullback_powerMarked {φ : X' → X}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ) {M : MarkedIdeal n X} {M' : MarkedIdeal n X'}
    (hM : M.ideal.IsCoherent) (hM' : M'.ideal.IsCoherent) (h : RestrictEquiv (MarkedIdeal.pullback φ M) M') (e : ℕ) :
    RestrictEquiv (MarkedIdeal.pullback φ (powerMarked M e)) (powerMarked M' e) := by
  rw [pullback_powerMarked hφ M hM e]
  refine restrictEquiv_powerMarked h (fun x g hg => ?_) (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hM' hg) e
  exact GermIdeal.IsCoherent.holomorphicAt_mem
    (GermIdealPullbackCalculus.isCoherent_pullback hφ hM) hg

end Transport

end

end Hironaka.HironakaG11InvCommonMark
