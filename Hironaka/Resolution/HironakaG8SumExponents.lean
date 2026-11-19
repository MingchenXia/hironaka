import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.Resolution.HironakaG11InvBMTangentIndep

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents of same-mark sums and of equal carriers (G8 lane, run 0080, round 6; level `s + 1` of (B') port P6)

Blueprint: `hironaka-g8-resume-sum-exponents.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P6: "the
`ℰ`-sum has exponent 0 along born members") and §6c (module 6, item (iv) at the levels `s + 1`).

The lower ideal of level `s + 1` of lane G11B's family is the same-mark sum `𝒞 + ℰ_S` on the carrier of `𝒞`.  Its exponent along
a member `H` at `x` is computed from the divisibility predicates of the summands:

* **`isDivNearAlong_sumIdeal_iff`**: `𝔞 + 𝔟 ⊆ 𝓘_H^e` along `N` near `x` iff both summands are (`cosupp` of a same-mark sum is
  the intersection);
* **`divExpAlong_sumIdeal_congr`**: the exponents of two sums on two carriers agree if the divisibility predicates of the
  summands agree for every `e`;
* **`divExpAlong_sumIdeal_eq_zero`**: if one summand is not divisible by `𝓘_H` along `N` near `x`, the sum has exponent `0`;
* **`divExpAlong_congr_of_eventually_iff`**: carriers that coincide near `x` give the same exponents (any ideal);
* for lane G11B's lower ideals (`HironakaG11InvBMTangentIndep.lowerIdealWBM`): **`expAgreeAt_lowerIdealWBM_of_eventually_N`**
  (two tangent functions whose carriers coincide near the point: every level) and
  **`expAgreeAt_lowerIdealWBM_succ_of_not_isDivNearAlong`** (level `s + 1`, where the `ℰ`-term is not divisible by `𝓘_H` along
  either carrier — the situation of BM's "the `ℰ`-sum has exponent `0` along born members").

NOT proved here (see `work/hironaka-resume-20261111/G8/REPORT-r6.md`): the agreement at level `s + 1` in general.  The `ℰ`-term
CAN be divisible by `𝓘_H` along a carrier (when `S = {H'}` and the carrier meets `H` inside `H'`, e.g. a hypersurface of maximal
contact equal to an original member), so the exponent of the sum is `min(c, ε_i)` with `ε_i` depending on the carrier.

Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8SumExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.DivisorExponentAlong
  Hironaka.GermIdealOrder Hironaka.HironakaG8DomainExponents
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.HironakaG11InvBMTangentIndep (lowerIdealWBM)
open Hironaka.HironakaG11InvBMLower (contactCoeffBM exceptionalTermBM)

noncomputable section

variable {n : ℕ} {Y : CMfd.{0} n}

/-! ### Same-mark sums -/

section Sum

variable {N H : Set Y} {𝔞 𝔟 : GermIdeal n Y}

/-- **Divisibility of a same-mark sum**: `𝔞 + 𝔟 ⊆ 𝓘_H^e` along `N` near `x` iff both summands are. -/
theorem isDivNearAlong_sumIdeal_iff (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) (e : ℕ) (x : Y) :
    IsDivNearAlong n N (sumIdeal 𝔞 𝔟) H e x ↔ IsDivNearAlong n N 𝔞 H e x ∧ IsDivNearAlong n N 𝔟 H e x := by
  unfold IsDivNearAlong
  rw [IdealOrderArithmetic.cosupport_sumIdeal h𝔞 h𝔟 e, ← Filter.eventually_and]
  refine eventually_congr (Eventually.of_forall fun z => ?_)
  simp only [mem_inter_iff]
  exact ⟨fun h => ⟨fun h1 h2 => (h h1 h2).1, fun h1 h2 => (h h1 h2).2⟩, fun h h1 h2 => ⟨h.1 h1 h2, h.2 h1 h2⟩⟩

/-- **If one summand is not divisible by `𝓘_H` along `N` near `x`, the sum has exponent `0`.** -/
theorem divExpAlong_sumIdeal_eq_zero (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) {x : Y} (h : ¬ IsDivNearAlong n N 𝔟 H 1 x) :
    divExpAlong n N (sumIdeal 𝔞 𝔟) H x = 0 := by
  classical
  have h1 : ¬ IsDivNearAlong n N (sumIdeal 𝔞 𝔟) H (0 + 1) x := fun h' =>
    h ((isDivNearAlong_sumIdeal_iff h𝔞 h𝔟 1 x).mp h').2
  have hex : ∃ e, ¬ IsDivNearAlong n N (sumIdeal 𝔞 𝔟) H (e + 1) x := ⟨0, h1⟩
  unfold divExpAlong
  rw [dif_pos hex]
  exact (Nat.find_eq_zero hex).mpr h1

/-- **Exponents of two sums on two carriers agree** if the divisibility predicates of the summands agree for every `e`. -/
theorem divExpAlong_sumIdeal_congr {N' : Set Y} {𝔞' 𝔟' : GermIdeal n Y} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) (h𝔞' : ∀ x g, 𝔞'.mem x g → HolomorphicAt n g x)
    (h𝔟' : ∀ x g, 𝔟'.mem x g → HolomorphicAt n g x) {x : Y}
    (ha : ∀ e, IsDivNearAlong n N 𝔞 H e x ↔ IsDivNearAlong n N' 𝔞' H e x)
    (hb : ∀ e, IsDivNearAlong n N 𝔟 H e x ↔ IsDivNearAlong n N' 𝔟' H e x) :
    divExpAlong n N (sumIdeal 𝔞 𝔟) H x = divExpAlong n N' (sumIdeal 𝔞' 𝔟') H x := by
  refine HironakaG8MixedBoundaryExponents.divExpAlong_congr fun e => ?_
  rw [isDivNearAlong_sumIdeal_iff h𝔞 h𝔟, isDivNearAlong_sumIdeal_iff h𝔞' h𝔟', ha e, hb e]

end Sum

/-! ### Carriers that coincide near a point -/

section Carrier

/-- **The cosupports along two carriers that coincide near `z` agree at `z`.** -/
theorem mem_cosupport_congr {N N' : Set Y} {𝔞 : GermIdeal n Y} {e : ℕ} {z : Y} (h : ∀ᶠ w in 𝓝 z, w ∈ N ↔ w ∈ N') :
    z ∈ cosupport n N 𝔞 e ↔ z ∈ cosupport n N' 𝔞 e := by
  have hv : ∀ g, VanishesToOrderOn n N z e g ↔ VanishesToOrderOn n N' z e g := by
    intro g
    constructor
    · rintro ⟨k, hk, hgk⟩
      exact ⟨k, hk, by filter_upwards [hgk, h] with w hw hw' hwN using hw (hw'.mpr hwN)⟩
    · rintro ⟨k, hk, hgk⟩
      exact ⟨k, hk, by filter_upwards [hgk, h] with w hw hw' hwN using hw (hw'.mp hwN)⟩
  show z ∈ N ∧ OrderGE n N 𝔞 z e ↔ z ∈ N' ∧ OrderGE n N' 𝔞 z e
  rw [h.self_of_nhds]
  exact and_congr_right fun _ => forall_congr' fun g => imp_congr_right fun _ => hv g

/-- **Carriers that coincide near `x` give the same exponents** (any ideal). -/
theorem divExpAlong_congr_of_eventually_iff {N N' : Set Y} (𝔞 : GermIdeal n Y) (H : Set Y) {x : Y}
    (h : ∀ᶠ w in 𝓝 x, w ∈ N ↔ w ∈ N') : divExpAlong n N 𝔞 H x = divExpAlong n N' 𝔞 H x := by
  refine HironakaG8MixedBoundaryExponents.divExpAlong_congr fun e => ?_
  unfold IsDivNearAlong
  constructor
  · intro h1
    filter_upwards [h1, h, h.eventually_nhds] with z hz hzN hzN' hzN₂ hzH
    exact (mem_cosupport_congr hzN').mp (hz (hzN.mpr hzN₂) hzH)
  · intro h1
    filter_upwards [h1, h, h.eventually_nhds] with z hz hzN hzN' hzN₁ hzH
    exact (mem_cosupport_congr hzN').mpr (hz (hzN.mp hzN₁) hzH)

end Carrier

/-! ### Lane G11B's lower ideals -/

section Lower

variable {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{0} n}

/-- **Two tangent functions whose carriers coincide near `y` give the same exponents at `y`** (every level). -/
theorem expAgreeAt_lowerIdealWBM_of_eventually_N (s : ℕ) (w w' : X → ℂ) (T₀ : BlowupTower X Y₀) (S : List (Set Y₀))
    {y : Y₀} (h : ∀ᶠ z in 𝓝 y, z ∈ (lowerIdealWBM 𝔍 s w T₀ S).N ↔ z ∈ (lowerIdealWBM 𝔍 s w' T₀ S).N) :
    ExpAgreeAt (lowerIdealWBM 𝔍 s w T₀ S) (lowerIdealWBM 𝔍 s w' T₀ S) y := by
  intro H _ _ _
  obtain ⟨hI, -, -⟩ := HironakaG11InvBMTangentIndep.lowerIdealWBM_ideal_eq 𝔍 s w w' T₀ S
  rw [hI]
  exact divExpAlong_congr_of_eventually_iff _ H h

/-- **Level `s + 1` where the `ℰ`-term is not divisible by `𝓘_H` along either carrier**: both exponents vanish. -/
theorem expAgreeAt_lowerIdealWBM_succ_of_not_isDivNearAlong (s : ℕ) (w w' : X → ℂ) (T₀ : BlowupTower X Y₀)
    (S : List (Set Y₀)) (hcoh : (contactCoeffBM 𝔍 w T₀).ideal.IsCoherent)
    (hE : (exceptionalTermBM (n := n) S (contactCoeffBM 𝔍 w T₀).d).IsCoherent) {y : Y₀}
    (h : ∀ H ∈ (lowerIdealWBM 𝔍 (s + 1) w T₀ S).E, y ∈ H →
      ¬ IsDivNearAlong n (contactCoeffBM 𝔍 w T₀).N (exceptionalTermBM S (contactCoeffBM 𝔍 w T₀).d) H 1 y ∧
      ¬ IsDivNearAlong n (contactCoeffBM 𝔍 w' T₀).N (exceptionalTermBM S (contactCoeffBM 𝔍 w T₀).d) H 1 y) :
    ExpAgreeAt (lowerIdealWBM 𝔍 (s + 1) w T₀ S) (lowerIdealWBM 𝔍 (s + 1) w' T₀ S) y := by
  intro H hH _ hyH
  have h𝔞 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh
  have h𝔟 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hE
  obtain ⟨h1, h2⟩ := h H hH hyH
  show divExpAlong n (contactCoeffBM 𝔍 w T₀).N
      (sumIdeal (contactCoeffBM 𝔍 w T₀).ideal (exceptionalTermBM S (contactCoeffBM 𝔍 w T₀).d)) H y =
    divExpAlong n (contactCoeffBM 𝔍 w' T₀).N
      (sumIdeal (contactCoeffBM 𝔍 w' T₀).ideal (exceptionalTermBM S (contactCoeffBM 𝔍 w' T₀).d)) H y
  have hI : (contactCoeffBM 𝔍 w' T₀).ideal = (contactCoeffBM 𝔍 w T₀).ideal := rfl
  have hd : (contactCoeffBM 𝔍 w' T₀).d = (contactCoeffBM 𝔍 w T₀).d := rfl
  rw [hI, hd, divExpAlong_sumIdeal_eq_zero h𝔞 h𝔟 h1, divExpAlong_sumIdeal_eq_zero h𝔞 h𝔟 h2]

end Lower

end

end Hironaka.HironakaG8SumExponents
