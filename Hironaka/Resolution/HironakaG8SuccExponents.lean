import Hironaka.Resolution.HironakaG8PowContact
import Hironaka.Resolution.HironakaG8SumExponents
import Hironaka.Resolution.HironakaG8StageExponents
import Hironaka.Resolution.HironakaG8BornExponents
import Hironaka.Resolution.HironakaG8LocalExcSum
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc
import Hironaka.Resolution.HironakaG11InvBMLowerTailSucc

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents of Bierstone--Milman's lower ideals at the levels `s + 1` (G8 lane, run 0080, round 7)

Blueprint: `hironaka-g8-resume-succ-exponents.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §6c (module 6 `TangentIndepBM`, item (iv)
`ExpAgree` at the levels `s + 1`); `work/hironaka-resume-20261111/G8/REPORT-r7.md`.

At the level `s + 1` the lower ideal of lane G11B's family on the carrier `N_i` (the strict transform of the hypersurface of
maximal contact of the tangent direction `u_i`) is the same-mark sum `𝒞 + ℰ_S`, with `𝒞` the transformed coefficient ideal and
`ℰ_S = ∑_{H' ∈ S} 𝓘_{H'}^δ`.  Its exponent along a member `H` at `y` is computed from those of the summands.  The comparison of
the two carriers rests on **the zero set of `𝒞` lying in both carriers near `y`** (`HironakaG8PowContact`):

* if `𝒞` vanishes identically along `N₁` near `y`, then `N₁ ⊆ N₂` near `y`, and the carriers coincide (filling);
* otherwise the exponents `c` of `𝒞` along the two carriers agree (level `0`); if `c = 0` both exponents vanish; if `c ≥ 1` then
  `𝒞` vanishes on `N_i ∩ H` near `y`, so `N₁ ∩ H = N₂ ∩ H` near `y`, the `ℰ`-term is divisible by `𝓘_H` along both carriers or
  along neither (it is iff `N_i ∩ H ⊆ ⋂ S` near `y`); when it is, the exponents are `c` for `c < δ`, and for `c ≥ δ` the common
  trace `N₁ ∩ H = N₂ ∩ H` lies in both cosupports, where the orders of the two lower ideals agree (an input `hord`, discharged
  for lane G11B's lower ideals by BM08 Theorem 6.1).

* **`isDivNearAlong_sumIdeal_iff_of_contact`**, **`divExpAlong_sumIdeal_eq_of_contact`** (the generic comparison);
* `mem_of_mem_cosupport_one_exceptionalTermBM`, `mem_cosupport_exceptionalTermBM` (the zero set of `ℰ_S` is `⋂ S`, and `ℰ_S` has
  order `≥ e` there).

Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8SuccExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.DivisorExponentAlong
  Hironaka.GermIdealOrder Hironaka.HironakaG8DomainExponents
  Hironaka.HironakaG8SumExponents Hironaka.IdealWeightPowers
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.HironakaG11InvBMLower (exceptionalTermBM)

noncomputable section

variable {n : ℕ} {Y : CMfd.{0} n}

/-! ### Carriers coinciding near a point -/

section Carrier

/-- **Carriers that coincide near `x` have the same divisibility predicates** (any ideal). -/
theorem isDivNearAlong_congr_of_eventually_iff {N N' : Set Y} (𝔞 : GermIdeal n Y) (H : Set Y) {x : Y}
    (h : ∀ᶠ w in 𝓝 x, w ∈ N ↔ w ∈ N') (e : ℕ) : IsDivNearAlong n N 𝔞 H e x ↔ IsDivNearAlong n N' 𝔞 H e x := by
  unfold IsDivNearAlong
  constructor
  · intro h1
    filter_upwards [h1, h, h.eventually_nhds] with z hz hzN hzN' hzN₂ hzH
    exact (mem_cosupport_congr hzN').mp (hz (hzN.mpr hzN₂) hzH)
  · intro h1
    filter_upwards [h1, h, h.eventually_nhds] with z hz hzN hzN' hzN₁ hzH
    exact (mem_cosupport_congr hzN').mpr (hz (hzN.mp hzN₁) hzH)

/-- At a point of the cosupport of order `1`, every germ of the ideal vanishes. -/
theorem forall_eq_zero_of_mem_cosupport_one {N : Set Y} {𝔞 : GermIdeal n Y} {z : Y} (hz : z ∈ cosupport n N 𝔞 1) :
    ∀ g, 𝔞.mem z g → g z = 0 := fun _ hg =>
  HironakaG8PowContact.apply_eq_zero_of_mem_cosupport_of_mem le_rfl hz hg

end Carrier

/-! ### The `ℰ`-term -/

section ETerm

/-- **The zero set of `ℰ_S` along any carrier lies in every member of `S`** (closed members). -/
theorem mem_of_mem_cosupport_one_exceptionalTermBM {N : Set Y} {S : List (Set Y)} (hS : ∀ H ∈ S, IsClosed H) {e : ℕ}
    {z : Y} (hz : z ∈ cosupport n N (exceptionalTermBM (n := n) S e) 1) : ∀ H ∈ S, z ∈ H := by
  intro H hH
  by_contra hzH
  obtain ⟨i, hi, hiH⟩ := List.mem_iff_getElem.mp hH
  have hget : S.getD i ∅ = H := by rw [List.getD_eq_getElem _ _ hi, hiH]
  have h1 : (vanishingIdeal (n := n) H).mem z (fun _ => (1 : ℂ)) :=
    ⟨holomorphicAt_const 1, by
      filter_upwards [(hS H hH).isOpen_compl.mem_nhds hzH] with y hy hyH
      exact absurd hyH hy⟩
  have hpow := MonomialPart.pow_mem_idealPow h1 (holomorphicAt_const 1) e
  simp only [one_pow] at hpow
  rw [← hget] at hpow
  have hmem : (exceptionalTermBM (n := n) S e).mem z (fun _ => (1 : ℂ)) :=
    InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ j, j < S.length ∧ (idealPow (vanishingIdeal (n := n) (S.getD j ∅)) e).mem z s)
      ⟨i, hi, hpow⟩ (holomorphicAt_const 1)
  exact one_ne_zero (forall_eq_zero_of_mem_cosupport_one hz _ hmem)

/-- **On `N ∩ ⋂ S` the `ℰ`-term has order `≥ e` along `N`.** -/
theorem mem_cosupport_exceptionalTermBM {N : Set Y} {S : List (Set Y)} {e : ℕ} {z : Y} (hzN : z ∈ N)
    (hzS : ∀ H ∈ S, z ∈ H) : z ∈ cosupport n N (exceptionalTermBM (n := n) S e) e := by
  refine (CoefficientIdeal.mem_cosupport_finSumIdeal
    (fun i _ x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)).mpr ⟨hzN, fun i hi => ⟨hzN, fun g hg => ?_⟩⟩
  have hzi : z ∈ S.getD i ∅ := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hzS _ (List.getElem_mem hi)
  exact ⟨g, DivisorExponent.mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hzi hg,
    Eventually.of_forall fun _ _ => rfl⟩

end ETerm

/-! ### The generic comparison -/

section Generic

variable {N₁ N₂ H A : Set Y} {𝒞 ℰ : GermIdeal n Y} {δ : ℕ} {y : Y}

/-- **Exponents of `𝒞 + ℰ` along two carriers whose common zero set of `𝒞` lies in both** (the generic form of the level
`s + 1` comparison): see the module docstring for the case analysis. -/
theorem isDivNearAlong_sumIdeal_iff_of_contact (h𝒞 : 𝒞.IsCoherent) (hℰ : ∀ x g, ℰ.mem x g → HolomorphicAt n g x)
    (hℰ1₁ : ∀ z, z ∈ cosupport n N₁ ℰ 1 → z ∈ A) (hℰ1₂ : ∀ z, z ∈ cosupport n N₂ ℰ 1 → z ∈ A)
    (hℰδ₁ : ∀ z, z ∈ N₁ → z ∈ A → z ∈ cosupport n N₁ ℰ δ) (hℰδ₂ : ∀ z, z ∈ N₂ → z ∈ A → z ∈ cosupport n N₂ ℰ δ)
    (hyH : y ∈ H) {r₁ r₂ : Y → Y} (hr₁ : IsLocalRetraction n N₁ r₁ y) (hr₂ : IsLocalRetraction n N₂ r₂ y)
    (hz₁ : ∀ᶠ z in 𝓝 y, z ∈ N₂ → (∀ g, 𝒞.mem z g → g z = 0) → z ∈ N₁)
    (hz₂ : ∀ᶠ z in 𝓝 y, z ∈ N₁ → (∀ g, 𝒞.mem z g → g z = 0) → z ∈ N₂)
    (hfill₁ : (∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ N₂) → ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ N₁)
    (hfill₂ : (∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ N₁) → ∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ N₂)
    (h0 : IsNonzeroAlongAt N₁ 𝒞 y → IsNonzeroAlongAt N₂ 𝒞 y → divExpAlong n N₁ 𝒞 H y = divExpAlong n N₂ 𝒞 H y)
    (hord : IsNonzeroAlongAt N₁ 𝒞 y → IsNonzeroAlongAt N₂ 𝒞 y → ∀ᶠ z in 𝓝 y,
      z ∈ cosupport n N₁ (sumIdeal 𝒞 ℰ) δ → z ∈ cosupport n N₂ (sumIdeal 𝒞 ℰ) δ →
        ∀ e, (z ∈ cosupport n N₁ (sumIdeal 𝒞 ℰ) e ↔ z ∈ cosupport n N₂ (sumIdeal 𝒞 ℰ) e))
    (e : ℕ) : IsDivNearAlong n N₁ (sumIdeal 𝒞 ℰ) H e y ↔ IsDivNearAlong n N₂ (sumIdeal 𝒞 ℰ) H e y := by
  have h𝒞h : ∀ x g, 𝒞.mem x g → HolomorphicAt n g x := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝒞
  have hK : ∀ (N : Set Y) (e : ℕ), IsDivNearAlong n N (sumIdeal 𝒞 ℰ) H e y ↔
      IsDivNearAlong n N 𝒞 H e y ∧ IsDivNearAlong n N ℰ H e y := fun _ e => isDivNearAlong_sumIdeal_iff h𝒞h hℰ e y
  -- `𝒞` vanishing identically along one carrier: the carriers coincide
  by_cases hn₁ : IsNonzeroAlongAt N₁ 𝒞 y
  swap
  · have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝒞 hn₁
    have h12 : ∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ N₂ := by
      filter_upwards [hev, hz₂] with z hz hz2 hzN
      exact hz2 hzN fun g hg => (hz g hg).self_of_nhds hzN
    have hiff : ∀ᶠ z in 𝓝 y, z ∈ N₁ ↔ z ∈ N₂ := (h12.and (hfill₁ h12)).mono fun z h => ⟨h.1, h.2⟩
    exact isDivNearAlong_congr_of_eventually_iff _ H hiff e
  by_cases hn₂ : IsNonzeroAlongAt N₂ 𝒞 y
  swap
  · have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝒞 hn₂
    have h21 : ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ N₁ := by
      filter_upwards [hev, hz₁] with z hz hz1 hzN
      exact hz1 hzN fun g hg => (hz g hg).self_of_nhds hzN
    have hiff : ∀ᶠ z in 𝓝 y, z ∈ N₁ ↔ z ∈ N₂ := ((hfill₂ h21).and h21).mono fun z h => ⟨h.1, h.2⟩
    exact isDivNearAlong_congr_of_eventually_iff _ H hiff e
  -- both nonzero along: the exponents `c` of `𝒞` agree
  have hc := h0 hn₁ hn₂
  have hD₁ : ∀ e, IsDivNearAlong n N₁ 𝒞 H e y ↔ e ≤ divExpAlong n N₁ 𝒞 H y := fun e =>
    isDivNearAlong_iff_le_divExpAlong hr₁ hyH hn₁ h𝒞h
  have hD₂ : ∀ e, IsDivNearAlong n N₂ 𝒞 H e y ↔ e ≤ divExpAlong n N₁ 𝒞 H y := fun e => by
    rw [hc]
    exact isDivNearAlong_iff_le_divExpAlong hr₂ hyH hn₂ h𝒞h
  set c := divExpAlong n N₁ 𝒞 H y with hcdef
  have hzero : ∀ (N : Set Y), IsDivNearAlong n N (sumIdeal 𝒞 ℰ) H 0 y := fun N =>
    (hK N 0).mpr ⟨isDivNearAlong_zero h𝒞h y, isDivNearAlong_zero hℰ y⟩
  rcases Nat.eq_zero_or_pos c with hc0 | hc1
  · -- `c = 0`: both exponents vanish
    rw [hK, hK, hD₁, hD₂, hc0]
    constructor
    · rintro ⟨he, -⟩
      obtain rfl : e = 0 := by omega
      exact ⟨le_rfl, isDivNearAlong_zero hℰ y⟩
    · rintro ⟨he, -⟩
      obtain rfl : e = 0 := by omega
      exact ⟨le_rfl, isDivNearAlong_zero hℰ y⟩
  -- `c ≥ 1`: `𝒞` vanishes on `N_i ∩ H` near `y`, hence `N₁ ∩ H = N₂ ∩ H` near `y`
  have Z₁₂ : ∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ H → z ∈ N₂ := by
    filter_upwards [(hD₁ 1).mpr hc1, hz₂] with z h1 h2 hzN hzH
    exact h2 hzN (forall_eq_zero_of_mem_cosupport_one (h1 hzN hzH))
  have Z₂₁ : ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ H → z ∈ N₁ := by
    filter_upwards [(hD₂ 1).mpr hc1, hz₁] with z h1 h2 hzN hzH
    exact h2 hzN (forall_eq_zero_of_mem_cosupport_one (h1 hzN hzH))
  -- divisibility of the `ℰ`-term
  have hF1 : ∀ (N : Set Y), (∀ z, z ∈ cosupport n N ℰ 1 → z ∈ A) → ∀ e, 1 ≤ e →
      IsDivNearAlong n N ℰ H e y → ∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → z ∈ A := by
    intro N hN e he h
    filter_upwards [h.mono he] with z hz hzN hzH
    exact hN z (hz hzN hzH)
  have hFδ : ∀ (N : Set Y), (∀ z, z ∈ N → z ∈ A → z ∈ cosupport n N ℰ δ) →
      (∀ᶠ z in 𝓝 y, z ∈ N → z ∈ H → z ∈ A) → ∀ e, e ≤ δ → IsDivNearAlong n N ℰ H e y := by
    intro N hN hA e he
    filter_upwards [hA] with z hz hzN hzH
    exact cosupport_anti he (hN z hzN (hz hzN hzH))
  by_cases hA₁ : ∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ H → z ∈ A
  · have hA₂ : ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ H → z ∈ A := by
      filter_upwards [hA₁, Z₂₁] with z hz hZ hzN hzH
      exact hz (hZ hzN hzH) hzH
    by_cases hcδ : c < δ
    · -- `c < δ`: both exponents are `c`
      rw [hK, hK, hD₁, hD₂]
      constructor
      · rintro ⟨he, -⟩
        exact ⟨he, hFδ N₂ hℰδ₂ hA₂ e (by omega)⟩
      · rintro ⟨he, -⟩
        exact ⟨he, hFδ N₁ hℰδ₁ hA₁ e (by omega)⟩
    · -- `c ≥ δ`: the common trace lies in both cosupports, where the orders agree
      have hK₁δ : IsDivNearAlong n N₁ (sumIdeal 𝒞 ℰ) H δ y :=
        (hK N₁ δ).mpr ⟨(hD₁ δ).mpr (by omega), hFδ N₁ hℰδ₁ hA₁ δ le_rfl⟩
      have hK₂δ : IsDivNearAlong n N₂ (sumIdeal 𝒞 ℰ) H δ y :=
        (hK N₂ δ).mpr ⟨(hD₂ δ).mpr (by omega), hFδ N₂ hℰδ₂ hA₂ δ le_rfl⟩
      have hO := hord hn₁ hn₂
      constructor
      · intro h1
        filter_upwards [h1, hK₁δ, hK₂δ, Z₂₁, hO] with z hz1 hzδ1 hzδ2 hzZ hzO hzN₂ hzH
        have hzN₁ := hzZ hzN₂ hzH
        exact (hzO (hzδ1 hzN₁ hzH) (hzδ2 hzN₂ hzH) e).mp (hz1 hzN₁ hzH)
      · intro h2
        filter_upwards [h2, hK₁δ, hK₂δ, Z₁₂, hO] with z hz2 hzδ1 hzδ2 hzZ hzO hzN₁ hzH
        have hzN₂ := hzZ hzN₁ hzH
        exact (hzO (hzδ1 hzN₁ hzH) (hzδ2 hzN₂ hzH) e).mpr (hz2 hzN₂ hzH)
  · -- the `ℰ`-term is divisible by `𝓘_H` along neither carrier: both exponents vanish
    have hA₂ : ¬ ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ H → z ∈ A := by
      intro h
      apply hA₁
      filter_upwards [h, Z₁₂] with z hz hZ hzN hzH
      exact hz (hZ hzN hzH) hzH
    constructor
    · intro h1
      rcases Nat.eq_zero_or_pos e with rfl | he
      · exact hzero N₂
      · exact absurd (hF1 N₁ hℰ1₁ e he ((hK N₁ e).mp h1).2) hA₁
    · intro h2
      rcases Nat.eq_zero_or_pos e with rfl | he
      · exact hzero N₁
      · exact absurd (hF1 N₂ hℰ1₂ e he ((hK N₂ e).mp h2).2) hA₂

/-- **The exponents of `𝒞 + ℰ` along the two carriers agree** (`divExpAlong` form). -/
theorem divExpAlong_sumIdeal_eq_of_contact (h𝒞 : 𝒞.IsCoherent) (hℰ : ∀ x g, ℰ.mem x g → HolomorphicAt n g x)
    (hℰ1₁ : ∀ z, z ∈ cosupport n N₁ ℰ 1 → z ∈ A) (hℰ1₂ : ∀ z, z ∈ cosupport n N₂ ℰ 1 → z ∈ A)
    (hℰδ₁ : ∀ z, z ∈ N₁ → z ∈ A → z ∈ cosupport n N₁ ℰ δ) (hℰδ₂ : ∀ z, z ∈ N₂ → z ∈ A → z ∈ cosupport n N₂ ℰ δ)
    (hyH : y ∈ H) {r₁ r₂ : Y → Y} (hr₁ : IsLocalRetraction n N₁ r₁ y) (hr₂ : IsLocalRetraction n N₂ r₂ y)
    (hz₁ : ∀ᶠ z in 𝓝 y, z ∈ N₂ → (∀ g, 𝒞.mem z g → g z = 0) → z ∈ N₁)
    (hz₂ : ∀ᶠ z in 𝓝 y, z ∈ N₁ → (∀ g, 𝒞.mem z g → g z = 0) → z ∈ N₂)
    (hfill₁ : (∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ N₂) → ∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ N₁)
    (hfill₂ : (∀ᶠ z in 𝓝 y, z ∈ N₂ → z ∈ N₁) → ∀ᶠ z in 𝓝 y, z ∈ N₁ → z ∈ N₂)
    (h0 : IsNonzeroAlongAt N₁ 𝒞 y → IsNonzeroAlongAt N₂ 𝒞 y → divExpAlong n N₁ 𝒞 H y = divExpAlong n N₂ 𝒞 H y)
    (hord : IsNonzeroAlongAt N₁ 𝒞 y → IsNonzeroAlongAt N₂ 𝒞 y → ∀ᶠ z in 𝓝 y,
      z ∈ cosupport n N₁ (sumIdeal 𝒞 ℰ) δ → z ∈ cosupport n N₂ (sumIdeal 𝒞 ℰ) δ →
        ∀ e, (z ∈ cosupport n N₁ (sumIdeal 𝒞 ℰ) e ↔ z ∈ cosupport n N₂ (sumIdeal 𝒞 ℰ) e)) :
    divExpAlong n N₁ (sumIdeal 𝒞 ℰ) H y = divExpAlong n N₂ (sumIdeal 𝒞 ℰ) H y :=
  HironakaG8MixedBoundaryExponents.divExpAlong_congr fun e =>
    isDivNearAlong_sumIdeal_iff_of_contact h𝒞 hℰ hℰ1₁ hℰ1₂ hℰδ₁ hℰδ₂ hyH hr₁ hr₂ hz₁ hz₂ hfill₁ hfill₂ h0 hord e

end Generic

/-! ### Lane G11B's lower ideals at a stage -/

section Stage

open Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.TangentDirectionAlong
  Hironaka.CoefficientIdealRestriction Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMStage Hironaka.HironakaG8LocalHistory
  Hironaka.MarkedIdealBiholomorphism Hironaka.HironakaG8LocalContact
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.ResolutionInvariantSpec (IsInvDomain DimLE)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)
open Hironaka.HironakaG11InvBMTangentIndep (lowerIdealWBM)
open Hironaka.HomogenizedGlueingTower (strictAlong)

variable {X : CMfd.{0} n} {𝔍 : MarkedIdeal n X} {Y₀ : CMfd.{0} n}

/-- **Level `0`, pointwise at a stage point**: at a point over `U ∩ U'` where both lower coefficient ideals are nonzero along
their carriers, their boundary exponents agree (the pointwise form of `HironakaG8StageExponents.expAgree_stage_contactCoeffBM_two`,
same proof). -/
theorem expAgreeAt_stage_contactCoeffBM_two (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀) {p : Y₀} (hpU : T₀.proj p ∈ U) (hpU' : T₀.proj p ∈ U')
    (nz1 : IsNonzeroAlongAt (contactCoeffBM 𝔍 u T₀).N (contactCoeffBM 𝔍 u T₀).ideal p)
    (nz2 : IsNonzeroAlongAt (contactCoeffBM 𝔍 u' T₀).N (contactCoeffBM 𝔍 u' T₀).ideal p) :
    ExpAgreeAt (contactCoeffBM 𝔍 u T₀) (contactCoeffBM 𝔍 u' T₀) p := by
  let W : Opens X := ⟨U ∩ U', hu.isOpen.inter hu'.isOpen⟩
  have hWU : (W : Set X) ⊆ U := inter_subset_left
  have hWU' : (W : Set X) ⊆ U' := inter_subset_right
  have huW : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (W : Set X) u := IsTangentDirectionAlong.mono_open hu W.isOpen hWU
  have hu'W : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (W : Set X) u' :=
    IsTangentDirectionAlong.mono_open hu' W.isOpen hWU'
  obtain ⟨hwfA, hwfB, hAB, hdim⟩ := HironakaG8StageExponents.base_contact_two h𝔍 hd hu hu' W hWU hWU'
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W huW T₀ hT₀
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM h𝔍 hd W hu'W T₀ hT₀
  have hdA : 1 ≤ (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}))).d :=
    ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have hkey := expAgreeAt_geoTransformAlong_of_domain hAB hwfA hwfB hdA rfl hdim
    (fun x _ _ _ => expAgreeAt_of_E_nil rfl x) (restrict W T₀) hTs
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have hcL : (contactCoeffBM 𝔍 u T₀).ideal.IsCoherent := hcTc
  have hcL' : (contactCoeffBM 𝔍 u' T₀).ideal.IsCoherent := hcTc
  have hholL := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL
  have hholL' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL'
  have hpV : p ∈ openPreimage T₀ W := ⟨hpU, hpU'⟩
  rw [← expAgreeAt_pullback_val_iff hholL hholL' (openPreimage T₀ W) ⟨p, hpV⟩]
  intro H hH hy hyH
  have hyA := hRE.cosupp_eq ▸ hy
  have hyAN := MarkedIdeal.cosupp_subset_N _ hyA
  have hcosAB := (hAB.geoTransformAlong (restrict W T₀) hTs).cosupp_eq_base
  have hyBN := MarkedIdeal.cosupp_subset_N _ (hcosAB ▸ hyA)
  have nzA := (isNonzeroAlongAt_iff_of_restrictEquiv hRE hyAN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz1)
  have nzB := (isNonzeroAlongAt_iff_of_restrictEquiv hRE' hyBN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL' (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz2)
  exact expAgreeAt_of_restrictEquiv hRE hRE' (hkey _ hyA nzA nzB) H hH hy hyH

/-- The carriers of the lower coefficient ideals lie in the stage carrier. -/
theorem contactCoeffBM_N_subset (w : X → ℂ) (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).N ⊆ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N := by
  rw [HomogenizedGlueingTower.N_geoTransformAlong]
  exact HironakaG8PowContact.strictAlong_mono inter_subset_left T₀

/-- **The two carriers have the same dimension at the cosupport points over `U ∩ U'`** (lane G8 r5,
`HironakaG8LocalContactStage.sameCarrierDim_stage_contactCoeffBM_two`, read at the stage). -/
theorem regularAtDim_contactCoeffBM_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀) {z : Y₀} (hzU : T₀.proj z ∈ U) (hzU' : T₀.proj z ∈ U')
    (hz : z ∈ cosupport n (contactCoeffBM 𝔍 u T₀).N (contactCoeffBM 𝔍 u T₀).ideal (contactCoeffBM 𝔍 u T₀).d) (j : ℕ) :
    RegularAtDim (n := n) (contactCoeffBM 𝔍 u T₀).N z j ↔ RegularAtDim (n := n) (contactCoeffBM 𝔍 u' T₀).N z j := by
  let W : Opens X := ⟨U ∩ U', hu.isOpen.inter hu'.isOpen⟩
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have h𝒞h := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (show (contactCoeffBM 𝔍 u T₀).ideal.IsCoherent from hcTc)
  have hsd := HironakaG8LocalContactStage.sameCarrierDim_stage_contactCoeffBM_two h𝔍 hd
    (U := ⟨U, hu.isOpen⟩) (U' := ⟨U', hu'.isOpen⟩) hu hu' T₀ hT₀ W inter_subset_left inter_subset_right
  have hzW : z ∈ openPreimage T₀ W := ⟨hzU, hzU'⟩
  have hzcW : (⟨z, hzW⟩ : openPreimage T₀ W) ∈
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (contactCoeffBM 𝔍 u T₀)).cosupp := by
    rw [cosupp_pullback_val _ h𝒞h (openPreimage T₀ W)]
    exact hz
  have h1 : RegularAtDim (n := n) ((Subtype.val : openPreimage T₀ W → Y₀) ⁻¹' (contactCoeffBM 𝔍 u T₀).N) ⟨z, hzW⟩ j ↔
      RegularAtDim (n := n) ((Subtype.val : openPreimage T₀ W → Y₀) ⁻¹' (contactCoeffBM 𝔍 u' T₀).N) ⟨z, hzW⟩ j :=
    hsd _ hzcW j
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff] at h1
  exact h1

/-- **Level `s + 1` on an open `O` of the stage, given the agreement of the orders on the common cosupport near the points
where the coefficient ideal is nonzero along both carriers** (`hord`; discharged by `ord_stage_lowerIdealWBM_succ`). -/
theorem expAgree_stage_lowerIdealWBM_succ_of_ord (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀) (S : List (Set Y₀)) (hS : ∀ H ∈ S, IsClosed H) (s : ℕ)
    (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U) (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') {k k' : ℕ}
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S)))
    (hdom' : IsInvDomain k' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)))
    (hord : ∀ p ∈ O, p ∈ (contactCoeffBM 𝔍 u T₀).N → p ∈ (contactCoeffBM 𝔍 u' T₀).N →
      IsNonzeroAlongAt (contactCoeffBM 𝔍 u T₀).N (contactCoeffBM 𝔍 u T₀).ideal p →
      IsNonzeroAlongAt (contactCoeffBM 𝔍 u' T₀).N (contactCoeffBM 𝔍 u T₀).ideal p →
      ∀ᶠ z in 𝓝 p, z ∈ (lowerIdealWBM 𝔍 (s + 1) u T₀ S).cosupp → z ∈ (lowerIdealWBM 𝔍 (s + 1) u' T₀ S).cosupp →
        ∀ e, (z ∈ cosupport n (contactCoeffBM 𝔍 u T₀).N (lowerIdealWBM 𝔍 (s + 1) u T₀ S).ideal e ↔
          z ∈ cosupport n (contactCoeffBM 𝔍 u' T₀).N (lowerIdealWBM 𝔍 (s + 1) u T₀ S).ideal e)) :
    ExpAgree (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)) := by
  -- the data
  set c₁ := contactCoeffBM 𝔍 u T₀ with hc₁
  set c₂ := contactCoeffBM 𝔍 u' T₀ with hc₂
  set 𝒞 := c₁.ideal with h𝒞def
  set δ := c₁.d with hδdef
  set ℰ := exceptionalTermBM (n := n) S δ with hℰdef
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have h𝒞 : 𝒞.IsCoherent := hcTc
  have h𝒞h := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝒞
  have hℰh : ∀ x g, ℰ.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hKh : ∀ x g, (sumIdeal 𝒞 ℰ).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hδ : 1 ≤ δ := by
    rw [hδdef, contactCoeffBM_d]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : O → Y₀) := contMDiff_subtype_val
  set 𝒞' := GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) 𝒞 with h𝒞'def
  set ℰ' := GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) ℰ with hℰ'def
  have hpb : GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (sumIdeal 𝒞 ℰ) = sumIdeal 𝒞' ℰ' :=
    MarkedIdealOperationsTransform.pullback_sumIdeal hval h𝒞h hℰh
  have hcosO : ∀ (N : Set Y₀) (I : GermIdeal n Y₀), (∀ x g, I.mem x g → HolomorphicAt n g x) → ∀ e,
      cosupport n ((Subtype.val : O → Y₀) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) I) e =
        (Subtype.val : O → Y₀) ⁻¹' cosupport n N I e :=
    fun N I hI e => cosupp_pullback_val (⟨N, [], I, e⟩ : MarkedIdeal n Y₀) hI O
  intro H hH p hp hpH
  show divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' c₁.N) (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (sumIdeal 𝒞 ℰ))
      H p = divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' c₂.N)
        (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (sumIdeal 𝒞 ℰ)) H p
  rw [hpb]
  -- the point at the stage
  have hpc : (p : Y₀) ∈ cosupport n c₁.N (sumIdeal 𝒞 ℰ) δ := by
    have h1 : p ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' c₁.N)
        (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (sumIdeal 𝒞 ℰ)) δ := hp
    rw [hcosO _ _ hKh] at h1
    exact h1
  have hpc0 : (p : Y₀) ∈ cosupport n c₁.N 𝒞 δ := by
    have h1 := hpc
    rw [IdealOrderArithmetic.cosupport_sumIdeal h𝒞h hℰh δ] at h1
    exact h1.1
  have hpN₁ : (p : Y₀) ∈ c₁.N := hpc.1
  have hpNT : (p : Y₀) ∈ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N := contactCoeffBM_N_subset u T₀ hpN₁
  have hz1 := HironakaG8PowContact.eventually_mem_contact_of_forall_eq_zero h𝔍 hd hu T₀ hT₀ hpNT (hOU p.2)
  have hz2 := HironakaG8PowContact.eventually_mem_contact_of_forall_eq_zero h𝔍 hd hu' T₀ hT₀ hpNT (hOU' p.2)
  have hpN₂ : (p : Y₀) ∈ c₂.N := hz2.self_of_nhds hpNT fun g hg =>
    HironakaG8PowContact.apply_eq_zero_of_mem_cosupport_of_mem hδ hpc0 hg
  have hpN₂' : p ∈ (Subtype.val : O → Y₀) ⁻¹' c₂.N := hpN₂
  -- germs of `𝒞` give germs of `𝒞'`
  have hcomp : ∀ (q : O) g, 𝒞.mem (q : Y₀) g → 𝒞'.mem q (g ∘ Subtype.val) := fun q g hg =>
    RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ b, 𝒞.mem q.1 b ∧ s = b ∘ Subtype.val) ⟨g, hg, rfl⟩
        ((holomorphicAt_comp_val_iff O).mpr (h𝒞h _ _ hg)))
  have hzO : ∀ {w w' : X → ℂ}, (∀ᶠ z in 𝓝 (p : Y₀), z ∈ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N →
      (∀ g, (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal.mem z g → g z = 0) → z ∈ (contactCoeffBM 𝔍 w T₀).N) →
      ∀ᶠ q in 𝓝 p, q ∈ (Subtype.val : O → Y₀) ⁻¹' (contactCoeffBM 𝔍 w' T₀).N → (∀ g, 𝒞'.mem q g → g q = 0) →
        q ∈ (Subtype.val : O → Y₀) ⁻¹' (contactCoeffBM 𝔍 w T₀).N := by
    intro w w' h
    filter_upwards [continuous_subtype_val.continuousAt.eventually h] with q hq hqN hq0
    exact hq (contactCoeffBM_N_subset w' T₀ hqN) fun g hg => hq0 _ (hcomp q g hg)
  -- carriers, retractions, dimensions
  have hN₁ : IsClosedSubmanifold n ((Subtype.val : O → Y₀) ⁻¹' c₁.N) := hdom.isWellFormed.isClosedSubmanifold_N
  have hN₂ : IsClosedSubmanifold n ((Subtype.val : O → Y₀) ⁻¹' c₂.N) := hdom'.isWellFormed.isClosedSubmanifold_N
  obtain ⟨k₁, hk₁⟩ := hN₁.2 p hpN₁
  obtain ⟨k₂, hk₂⟩ := hN₂.2 p hpN₂'
  obtain ⟨r₁, hr₁⟩ := exists_isLocalRetraction hk₁
  obtain ⟨r₂, hr₂⟩ := exists_isLocalRetraction hk₂
  have hdimp : ∀ j, RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' c₁.N) p j ↔
      RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' c₂.N) p j := by
    intro j
    rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff]
    exact regularAtDim_contactCoeffBM_iff h𝔍 hd hu hu' T₀ hT₀ (hOU p.2) (hOU' p.2) hpc0 j
  have hfill : ∀ {N N' : Set O}, IsClosedSubmanifold n N → IsClosedSubmanifold n N' →
      (∀ j, RegularAtDim (n := n) N p j ↔ RegularAtDim (n := n) N' p j) → p ∈ N' →
      (∀ᶠ q in 𝓝 p, q ∈ N → q ∈ N') → ∀ᶠ q in 𝓝 p, q ∈ N' → q ∈ N := by
    intro N N' hN hN' hj hpN' h
    obtain ⟨j, hj'⟩ := hN'.2 p hpN'
    exact CodimOneSupport.eventually_mem_of_locDimGE
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN) hj' h
      (AnalyticDimensionBasics.locDimGE_of_regularAtDim ((hj j).mpr hj'))
  -- the level-`0` agreement at `p`
  have h0 : IsNonzeroAlongAt ((Subtype.val : O → Y₀) ⁻¹' c₁.N) 𝒞' p →
      IsNonzeroAlongAt ((Subtype.val : O → Y₀) ⁻¹' c₂.N) 𝒞' p →
      divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' c₁.N) 𝒞' H p =
        divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' c₂.N) 𝒞' H p := by
    intro nz1 nz2
    have hA := expAgreeAt_stage_contactCoeffBM_two h𝔍 hd hu hu' T₀ hT₀ (hOU p.2) (hOU' p.2)
      ((isNonzeroAlongAt_pullback_val_iff h𝒞 O p).mp nz1) ((isNonzeroAlongAt_pullback_val_iff h𝒞 O p).mp nz2)
    have hA' := (expAgreeAt_pullback_val_iff (P := c₁) (Q := c₂) h𝒞h h𝒞h O p).mpr hA
    have hp0 : p ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) c₁).cosupp := by
      rw [cosupp_pullback_val c₁ h𝒞h O]
      exact hpc0
    exact hA' H hH hp0 hpH
  -- the orders on the common cosupport
  have hord' : IsNonzeroAlongAt ((Subtype.val : O → Y₀) ⁻¹' c₁.N) 𝒞' p →
      IsNonzeroAlongAt ((Subtype.val : O → Y₀) ⁻¹' c₂.N) 𝒞' p → ∀ᶠ q in 𝓝 p,
        q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' c₁.N) (sumIdeal 𝒞' ℰ') δ →
        q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' c₂.N) (sumIdeal 𝒞' ℰ') δ → ∀ e,
          (q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' c₁.N) (sumIdeal 𝒞' ℰ') e ↔
            q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' c₂.N) (sumIdeal 𝒞' ℰ') e) := by
    intro nz1 nz2
    have h := hord p p.2 hpN₁ hpN₂ ((isNonzeroAlongAt_pullback_val_iff h𝒞 O p).mp nz1)
      ((isNonzeroAlongAt_pullback_val_iff h𝒞 O p).mp nz2)
    filter_upwards [continuous_subtype_val.continuousAt.eventually h] with q hq hq1 hq2 e
    rw [← hpb, hcosO _ _ hKh] at hq1 hq2
    rw [← hpb, hcosO _ _ hKh, hcosO _ _ hKh]
    exact hq hq1 hq2 e
  -- the `ℰ`-term
  have hScl := hS
  have hℰ1 : ∀ (N : Set Y₀) (q : O), q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' N) ℰ' 1 →
      q ∈ (Subtype.val : O → Y₀) ⁻¹' {x | ∀ H ∈ S, x ∈ H} := by
    intro N q hq
    rw [hcosO _ _ hℰh] at hq
    exact mem_of_mem_cosupport_one_exceptionalTermBM hScl hq
  have hℰδ : ∀ (N : Set Y₀) (q : O), q ∈ (Subtype.val : O → Y₀) ⁻¹' N →
      q ∈ (Subtype.val : O → Y₀) ⁻¹' {x | ∀ H ∈ S, x ∈ H} → q ∈ cosupport n ((Subtype.val : O → Y₀) ⁻¹' N) ℰ' δ := by
    intro N q hqN hqS
    rw [hcosO _ _ hℰh]
    exact mem_cosupport_exceptionalTermBM hqN hqS
  exact divExpAlong_sumIdeal_eq_of_contact (GermIdealPullbackCalculus.isCoherent_pullback hval h𝒞)
    (fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1)
    (hℰ1 c₁.N) (hℰ1 c₂.N) (hℰδ c₁.N) (hℰδ c₂.N) hpH hr₁ hr₂ (hzO hz1) (hzO hz2)
    (hfill hN₁ hN₂ hdimp hpN₂') (hfill hN₂ hN₁ (fun j => (hdimp j).symm) hpN₁) h0 hord'

/-- **The orders of the two lower ideals of level `s + 1` agree on their common cosupport near every stage point over
`U ∩ U'` at which the coefficient ideal is nonzero along both carriers** (BM08 Theorem 6.1, lane G8B's
`HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv`, on an open where both lower coefficient ideals are in the native
domain: there the lower ideals of level `s + 1` are `LocWPEquiv` by `HironakaG8LocalExcSum.locEquiv_sumIdeal`). -/
theorem ord_stage_lowerIdealWBM_succ (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u')
    (T₀ : BlowupTower X Y₀) (hT₀b : IsGeoTestTower (StepOneValue.barMarked 𝔍) T₀) (S : List (Set Y₀))
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : S ≠ []) (s : ℕ) {p : Y₀} (hpU : T₀.proj p ∈ U)
    (hpU' : T₀.proj p ∈ U') (hpN₁ : p ∈ (contactCoeffBM 𝔍 u T₀).N) (hpN₂ : p ∈ (contactCoeffBM 𝔍 u' T₀).N)
    (nz1 : IsNonzeroAlongAt (contactCoeffBM 𝔍 u T₀).N (contactCoeffBM 𝔍 u T₀).ideal p)
    (nz2 : IsNonzeroAlongAt (contactCoeffBM 𝔍 u' T₀).N (contactCoeffBM 𝔍 u T₀).ideal p) :
    ∀ᶠ z in 𝓝 p, z ∈ (lowerIdealWBM 𝔍 (s + 1) u T₀ S).cosupp → z ∈ (lowerIdealWBM 𝔍 (s + 1) u' T₀ S).cosupp →
      ∀ e, (z ∈ cosupport n (contactCoeffBM 𝔍 u T₀).N (lowerIdealWBM 𝔍 (s + 1) u T₀ S).ideal e ↔
        z ∈ cosupport n (contactCoeffBM 𝔍 u' T₀).N (lowerIdealWBM 𝔍 (s + 1) u T₀ S).ideal e) := by
  set c₁ := contactCoeffBM 𝔍 u T₀ with hc₁
  set c₂ := contactCoeffBM 𝔍 u' T₀ with hc₂
  set 𝒞 := c₁.ideal with h𝒞def
  set δ := c₁.d with hδdef
  set ℰ := exceptionalTermBM (n := n) S δ with hℰdef
  have hT₀ : IsGeoTestTower 𝔍 T₀ := isGeoTestTower_of_barMarked h𝔍 hd T₀ hT₀b
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := isGeoTestTower_coeffEmptyBM h𝔍 hd T₀ (isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  obtain ⟨-, hcTc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  have h𝒞 : 𝒞.IsCoherent := hcTc
  have h𝒞h := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝒞
  have hℰ : ℰ.IsCoherent := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS δ
  have hℰh : ∀ x g, ℰ.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hKh : ∀ x g, (sumIdeal 𝒞 ℰ).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hδ : 1 ≤ δ := by
    rw [hδdef, contactCoeffBM_d]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have hk : DimLE n 𝔍.N n := fun x hx => by
    obtain ⟨j, hj⟩ := h𝔍.isClosedSubmanifold_N.2 x hx
    exact ⟨j, BlowupStrictSubmanifold.le_of_regularAtDim_subset hj
      (AnalyticIrreducibleComponents.regularAtDim_univ x) (subset_univ _), hj⟩
  let UO : Opens X := ⟨U, hu.isOpen⟩
  let UO' : Opens X := ⟨U', hu'.isOpen⟩
  let W : Opens X := ⟨U ∩ U', hu.isOpen.inter hu'.isOpen⟩
  let W' : Opens Y₀ := openPreimage T₀ W
  have hpW' : p ∈ W' := ⟨hpU, hpU'⟩
  have hwf : ∀ (V : Opens Y₀), (V : Set Y₀) ⊆ W' →
      ((MarkedIdeal.pullback (Subtype.val : V → Y₀) c₁).IsWellFormed ∧
        DimLE n (MarkedIdeal.pullback (Subtype.val : V → Y₀) c₁).N (n - 1)) ∧
      ((MarkedIdeal.pullback (Subtype.val : V → Y₀) c₂).IsWellFormed ∧
        DimLE n (MarkedIdeal.pullback (Subtype.val : V → Y₀) c₂).N (n - 1)) := fun V hV =>
    ⟨HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd UO hu T₀ hk hT₀b V
        fun _ hz => (hV hz).1,
      HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd UO' hu' T₀ hk hT₀b V
        fun _ hz => (hV hz).2⟩
  have hval : ∀ (V : Opens Y₀), ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → Y₀) :=
    fun _ => contMDiff_subtype_val
  have hcohV : ∀ (V : Opens Y₀), (GermIdeal.pullback (m := n) (Subtype.val : V → Y₀) 𝒞).IsCoherent := fun V =>
    GermIdealPullbackCalculus.isCoherent_pullback (hval V) h𝒞
  -- the domain opens of the two lower coefficient ideals on `W'`
  obtain ⟨⟨hwf₁, -⟩, ⟨hwf₂, -⟩⟩ := hwf W' subset_rfl
  set D₁ := domOpen (Y := CMfd.of (n := n) W') (MarkedIdeal.pullback (Subtype.val : W' → Y₀) c₁) hwf₁.isClosedSubmanifold_N with hD₁
  set D₂ := domOpen (Y := CMfd.of (n := n) W') (MarkedIdeal.pullback (Subtype.val : W' → Y₀) c₂) hwf₂.isClosedSubmanifold_N with hD₂
  have hdom₁ : ∀ r : W', (r : Y₀) ∈ c₁.N → (r ∈ D₁ ↔ IsNonzeroAlongAt c₁.N 𝒞 r) := fun r hr =>
    (mem_domOpen_iff (Y := CMfd.of (n := n) W') hwf₁.isClosedSubmanifold_N (hcohV W') hδ hr).trans (isNonzeroAlongAt_pullback_val_iff h𝒞 W' r)
  have hdom₂ : ∀ r : W', (r : Y₀) ∈ c₂.N → (r ∈ D₂ ↔ IsNonzeroAlongAt c₂.N 𝒞 r) := fun r hr =>
    (mem_domOpen_iff (Y := CMfd.of (n := n) W') hwf₂.isClosedSubmanifold_N (hcohV W') hδ hr).trans (isNonzeroAlongAt_pullback_val_iff h𝒞 W' r)
  let O'' : Opens Y₀ := ⟨Subtype.val '' (D₁ : Set W') ∩ Subtype.val '' (D₂ : Set W'),
    (W'.isOpen.isOpenMap_subtype_val _ D₁.isOpen).inter (W'.isOpen.isOpenMap_subtype_val _ D₂.isOpen)⟩
  have hpO'' : p ∈ O'' := ⟨⟨⟨p, hpW'⟩, (hdom₁ ⟨p, hpW'⟩ hpN₁).mpr nz1, rfl⟩, ⟨⟨p, hpW'⟩, (hdom₂ ⟨p, hpW'⟩ hpN₂).mpr nz2, rfl⟩⟩
  have hO''W : O'' ≤ W' := by
    rintro z ⟨⟨r, -, rfl⟩, -⟩
    exact r.2
  -- the lower coefficient ideals on `O''` are in the native domain
  obtain ⟨⟨hwfO₁, hdimO₁⟩, ⟨hwfO₂, hdimO₂⟩⟩ := hwf O'' hO''W
  have hA₁ : IsInvDomain (n - 1) (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁) := by
    refine ⟨hwfO₁, hdimO₁, hδ, fun q hq => ?_⟩
    obtain ⟨⟨r, hrD, hrq⟩, -⟩ := q.2
    have hrN : (r : Y₀) ∈ c₁.N := by rw [hrq]; exact hq
    have h1 := (hdom₁ r hrN).mp hrD
    rw [hrq] at h1
    exact (isNonzeroAlongAt_pullback_val_iff h𝒞 O'' q).mpr h1
  have hA₂ : IsInvDomain (n - 1) (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂) := by
    refine ⟨hwfO₂, hdimO₂, hδ, fun q hq => ?_⟩
    obtain ⟨-, ⟨r, hrD, hrq⟩⟩ := q.2
    have hrN : (r : Y₀) ∈ c₂.N := by rw [hrq]; exact hq
    have h1 := (hdom₂ r hrN).mp hrD
    rw [hrq] at h1
    exact (isNonzeroAlongAt_pullback_val_iff h𝒞 O'' q).mpr h1
  -- `LocWPEquiv` of the lower ideals of levels `0` and `s + 1` on `O''`
  have hLV := HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM_two h𝔍 hd UO T₀ hT₀ (U' := UO') hu hu' W
    inter_subset_left inter_subset_right
  have hLO := HironakaG8LocalTransport.locWPEquiv_restrict_of_le (A := c₁) (B := c₂) h𝒞 h𝒞 hO''W hLV
  set S'' := S.map ((Subtype.val : O'' → Y₀) ⁻¹' ·) with hS''def
  have hS'' : ∀ H ∈ S'', IsClosedSubmanifold n H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hS H₀ hH₀) O''
  have hpb : GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ) =
      sumIdeal (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) 𝒞) (exceptionalTermBM (n := n) S'' δ) := by
    rw [MarkedIdealOperationsTransform.pullback_sumIdeal (hval O'') h𝒞h hℰh,
      HironakaG11InvBMExceptionalTerm.pullback_val_exceptionalTermBM O'' hS hSne δ]
  have hB₁ : MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S) =
      ⟨(MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁).N, (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁).E,
        sumIdeal (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁).ideal
          (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S''.getD i ∅))
            (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁).d) S''.length),
        (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₁).d⟩ := by
    show (⟨_, _, GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ), _⟩ : MarkedIdeal n O'') = _
    rw [hpb]
    rfl
  have hB₂ : MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S) =
      ⟨(MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂).N, (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂).E,
        sumIdeal (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂).ideal
          (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S''.getD i ∅))
            (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂).d) S''.length),
        (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) c₂).d⟩ := by
    show (⟨_, _, GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ), _⟩ : MarkedIdeal n O'') = _
    rw [hpb]
    rfl
  have hLB : LocWPEquiv (X := CMfd.of (n := n) O'')
      (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S))
      (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)) := by
    rw [hB₁, hB₂]
    exact HironakaG8LocalExcSum.locEquiv_sumIdeal rfl hLO hA₁ hA₂ rfl hS''
  -- the lower ideals of level `s + 1` on `O''` are in the native domain
  have hcohB : (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ)).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback (hval O'') (RestrictedIdealExtension.isCoherent_sumIdeal h𝒞 hℰ)
  have hle : (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) 𝒞).Le
      (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ)) := by
    rw [hpb]
    exact RestrictedIdealExtension.le_sumIdeal_left (hcohV O'')
  have hBdom : ∀ {w : X → ℂ}, IsInvDomain (n - 1) (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (contactCoeffBM 𝔍 w T₀)) →
      IsInvDomain (n - 1) (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) w T₀ S)) := by
    intro w hA
    refine ⟨⟨hA.isWellFormed.isClosedSubmanifold_N, hcohB, hA.isWellFormed.isSNCDivisor, hA.isWellFormed.isTransverse⟩,
      hA.dimLE, hA.one_le_d, fun q hq => ?_⟩
    obtain ⟨g, hg, hfreq⟩ := hA.isNonzeroAlongAt q hq
    exact ⟨g, hle q g hg, hfreq⟩
  have hBd₁ := hBdom hA₁
  have hBd₂ := hBdom hA₂
  -- carriers of the same dimension on the cosupport
  have hcosV : ∀ (V : Opens Y₀) (N : Set Y₀) (I : GermIdeal n Y₀), (∀ x g, I.mem x g → HolomorphicAt n g x) → ∀ e,
      cosupport n ((Subtype.val : V → Y₀) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : V → Y₀) I) e =
        (Subtype.val : V → Y₀) ⁻¹' cosupport n N I e :=
    fun V N I hI e => cosupp_pullback_val (⟨N, [], I, e⟩ : MarkedIdeal n Y₀) hI V
  have hdimB : SameCarrierDim (X := CMfd.of (n := n) O'')
      (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S))
      (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)) := by
    intro q hq j
    have hq' : (q : Y₀) ∈ cosupport n c₁.N (sumIdeal 𝒞 ℰ) δ := by
      have h1 : q ∈ cosupport n ((Subtype.val : O'' → Y₀) ⁻¹' c₁.N)
          (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ)) δ := hq
      rw [hcosV _ _ _ hKh] at h1
      exact h1
    rw [IdealOrderArithmetic.cosupport_sumIdeal h𝒞h hℰh δ] at hq'
    have hqW := hO''W q.2
    show RegularAtDim (n := n) ((Subtype.val : O'' → Y₀) ⁻¹' c₁.N) q j ↔
      RegularAtDim (n := n) ((Subtype.val : O'' → Y₀) ⁻¹' c₂.N) q j
    rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff]
    exact regularAtDim_contactCoeffBM_iff h𝔍 hd hu hu' T₀ hT₀ hqW.1 hqW.2 hq'.1 j
  -- BM08 Theorem 6.1 on `O''`, read at the stage
  filter_upwards [O''.isOpen.mem_nhds hpO''] with z hzO hz1 hz2 e
  set q : O'' := ⟨z, hzO⟩ with hqdef
  have hq1 : q ∈ (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S)).cosupp := by
    rw [cosupp_pullback_val _ hKh O'']
    exact hz1
  have hq2 : q ∈ (MarkedIdeal.pullback (Subtype.val : O'' → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)).cosupp := by
    rw [cosupp_pullback_val _ hKh O'']
    exact hz2
  have hP1 := HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv _ _ hBd₁ hBd₂ q hq1 hq2
    hLB.projEquiv.projectionTest_wEquiv hdimB
  have hP1' : δ * _ = δ * _ := hP1
  have hord := Nat.eq_of_mul_eq_mul_left (show 0 < δ by omega) hP1'
  have iff₁ := HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n) O'')
    hBd₁.isWellFormed.isClosedSubmanifold_N hBd₁.isWellFormed.isCoherent hBd₁.isNonzeroAlongAt
    hq1.1 e
  have iff₂ := HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n) O'')
    hBd₂.isWellFormed.isClosedSubmanifold_N hBd₂.isWellFormed.isCoherent hBd₂.isNonzeroAlongAt
    hq2.1 e
  have h1 : q ∈ cosupport n ((Subtype.val : O'' → Y₀) ⁻¹' c₁.N)
      (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ)) e ↔
      q ∈ cosupport n ((Subtype.val : O'' → Y₀) ⁻¹' c₂.N)
      (GermIdeal.pullback (m := n) (Subtype.val : O'' → Y₀) (sumIdeal 𝒞 ℰ)) e :=
    iff₁.trans (by rw [hord]; exact iff₂.symm)
  rw [hcosV _ _ _ hKh, hcosV _ _ _ hKh] at h1
  exact h1

/-- **Level `s + 1`: the boundary exponents of the two lower ideals agree on every open `O` of the stage over `U ∩ U'` on which
both are in the native domain** (any list `S` of closed submanifolds, `S ≠ []`; item (iv) of lane G11B's module 6 at the levels
`s + 1`, in the form consumed by `ClassFunctorialFor.inv_eq`). -/
theorem expAgree_stage_lowerIdealWBM_succ_of_isInvDomain (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {U U' : Set X}
    {u u' : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u') (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (StepOneValue.barMarked 𝔍) T₀) (S : List (Set Y₀)) (hS : ∀ H ∈ S, IsClosedSubmanifold n H)
    (hSne : S ≠ []) (s : ℕ) (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U)
    (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') {k k' : ℕ}
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S)))
    (hdom' : IsInvDomain k' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S))) :
    ExpAgree (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ S))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ S)) :=
  expAgree_stage_lowerIdealWBM_succ_of_ord h𝔍 hd hu hu' T₀ (isGeoTestTower_of_barMarked h𝔍 hd T₀ hT₀) S
    (fun H hH => (hS H hH).1) s O hOU hOU' hdom hdom' fun _p hp hpN₁ hpN₂ nz1 nz2 =>
      ord_stage_lowerIdealWBM_succ h𝔍 hd hu hu' T₀ hT₀ S hS hSne s (hOU hp) (hOU' hp) hpN₁ hpN₂ nz1 nz2

/-- **The instance of lane G11B's `TangentIndepBM`** (`S` = the original members through an anchor `a` of level `s + 1`). -/
theorem expAgree_stage_lowerIdealWBM_succ_throughMembers (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    {U U' : Set X} {u u' : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    (hu' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' u') (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (StepOneValue.barMarked 𝔍) T₀) (a : Y₀) {s : ℕ} (hl : StepOneValue.level 𝔍 T₀ a = s + 1)
    (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U) (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') {k k' : ℕ}
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 (s + 1) u T₀ (throughMembers 𝔍 T₀ a))))
    (hdom' : IsInvDomain k' (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 (s + 1) u' T₀ (throughMembers 𝔍 T₀ a)))) :
    ExpAgree (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u T₀ (throughMembers 𝔍 T₀ a)))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) u' T₀ (throughMembers 𝔍 T₀ a))) :=
  expAgree_stage_lowerIdealWBM_succ_of_isInvDomain h𝔍 hd hu hu' T₀ hT₀ (throughMembers 𝔍 T₀ a)
    (HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ a)
    (HironakaG11InvBMLowerTailSucc.throughMembers_ne_nil 𝔍 T₀ hl) s O hOU hOU' hdom hdom'

end Stage

end

end Hironaka.HironakaG8SuccExponents
