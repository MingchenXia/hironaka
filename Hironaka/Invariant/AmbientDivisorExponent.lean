/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponent
import Hironaka.Invariant.CompanionReduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Ambient divisor exponents and a cosupport witness

This module restores the ambient neighbourhood-divisibility and exponent
calculus needed by genuine divisor powers and actual residual extraction.
The definitions, statements and proofs are preserved from the original
formalization, with only the canonical namespace renaming. Declarations
already present in the existing divisor-exponent module are reused.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DivisorExponent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail
  Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates
  Hironaka.HadamardBridge Hironaka.HadamardBridgeAlong
  Hironaka.IdealOrderArithmetic Hironaka.GiraudAlong
  Hironaka.OrderMultiplicativity Hironaka.GermOrderProduct
  Hironaka.HolomorphicAnalytic

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

section Exponent

variable {𝔞 : GermIdeal n M} {H : Set M}

variable (n) in
/-- **`𝔞 ⊆ 𝓘_H^e` near `x`, in cosupport form**: near `x`, the points of `H` lie in `cosupp(𝔞, e)`. -/
def IsDivNear (𝔞 : GermIdeal n M) (H : Set M) (e : ℕ) (x : M) : Prop :=
  ∀ᶠ z in 𝓝 x, z ∈ H → z ∈ cosupport n univ 𝔞 e

theorem isDivNear_zero (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) : IsDivNear n 𝔞 H 0 x :=
  Eventually.of_forall fun z _ => by rw [cosupport_zero h𝔞]; exact mem_univ z

theorem IsDivNear.mono {e e' : ℕ} {x : M} (h : IsDivNear n 𝔞 H e x) (he : e' ≤ e) : IsDivNear n 𝔞 H e' x :=
  Filter.Eventually.mono h fun _ hz hzH => cosupport_anti he (hz hzH)

/-- Divisibility near `x` holds near every point close to `x`. -/
theorem IsDivNear.eventually {e : ℕ} {x : M} (h : IsDivNear n 𝔞 H e x) : ∀ᶠ y in 𝓝 x, IsDivNear n 𝔞 H e y :=
  Filter.Eventually.eventually_nhds h

/-- Off a closed set `H`, every divisibility holds. -/
theorem isDivNear_of_notMem (hH : IsClosed H) {x : M} (hx : x ∉ H) (e : ℕ) : IsDivNear n 𝔞 H e x := by
  filter_upwards [hH.isOpen_compl.mem_nhds hx] with z hz hzH
  exact absurd hzH hz

/-- If the generators of a coherent ideal lie in `𝓘_H^e` at `x`, then `IsDivNear 𝔞 H e x`. -/
theorem isDivNear_of_generators {U : Set M} (hUo : IsOpen U) {x : M} (hxU : x ∈ U) {K : ℕ} {s : Fin K → M → ℂ}
    (hgen : ∀ y ∈ U, ∀ g, 𝔞.mem y g ↔ IsInSpanAt (n := n) (· ∈ range s) y g) {e : ℕ}
    (hs : ∀ i, (idealPow (vanishingIdeal (n := n) H) e).mem x (s i)) : IsDivNear n 𝔞 H e x := by
  filter_upwards [hUo.mem_nhds hxU, eventually_all.mpr fun i => eventually_mem_idealPow_vanishingIdeal (hs i)]
    with z hzU hz hzH
  refine ⟨mem_univ z, fun f hf => IsInSpanAt.vanishesToOrderOn ((hgen z hzU f).mp hf) ?_⟩
  rintro _ ⟨i, rfl⟩
  exact vanishesToOrderOn_of_mem (mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hzH (hz i))

/-- **Divisibility near `x` is divisibility of the stalk**: for `𝔞` coherent and `H` a submanifold at `x`,
`IsDivNear 𝔞 H e x ↔ 𝔞_x ⊆ (𝓘_H^e)_x`. -/
theorem isDivNear_iff (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k) {e : ℕ} :
    IsDivNear n 𝔞 H e x ↔ ∀ g, 𝔞.mem x g → (idealPow (vanishingIdeal (n := n) H) e).mem x g := by
  constructor
  · intro h g hg
    refine mem_idealPow_vanishingIdeal_of_eventually hH
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) ?_
    filter_upwards [h, eventually_mem_of_isCoherent h𝔞 hg] with z hz hgz hzH
    exact mem_idealPow_of_vanishesToOrderOn_univ ((hz hzH).2 g hgz)
  · intro h
    obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
    refine isDivNear_of_generators hUo hxU hgen fun i => h _ ((hgen x hxU _).mpr ?_)
    exact isInSpanAt_of_eq_mul ⟨i, rfl⟩
      (holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hxU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm)

/-- **Identity principle along `H`**: for `𝔞` coherent and `H` a submanifold at `x`, if points `y ∈ H` with
`IsDivNear 𝔞 H e y` accumulate at `x`, then `IsDivNear 𝔞 H e x`. -/
theorem isDivNear_of_frequently (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k)
    {e : ℕ} (h : ∃ᶠ y in 𝓝 x, y ∈ H ∧ IsDivNear n 𝔞 H e y) : IsDivNear n 𝔞 H e x := by
  obtain ⟨U, hUo, hxU, K, s, hs, hgen⟩ := h𝔞 x
  have hshol : ∀ i, ∀ z ∈ U, HolomorphicAt n (s i) z := fun i _ hz =>
    holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hz
  have hmem : ∀ i, ∀ z ∈ U, 𝔞.mem z (s i) := fun i z hz => (hgen z hz (s i)).mpr
    (isInSpanAt_of_eq_mul ⟨i, rfl⟩ (hshol i z hz) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  refine isDivNear_of_generators hUo hxU hgen fun i => ?_
  refine mem_idealPow_vanishingIdeal_of_frequently hH (hshol i x hxU) ?_
  have hU' : ∀ᶠ y in 𝓝 x, y ∈ U := hUo.mem_nhds hxU
  refine (h.and_eventually (Filter.Eventually.eventually_nhds hU')).mono ?_
  rintro y ⟨⟨hyH, hyd⟩, hyU⟩
  refine ⟨hyH, ?_⟩
  filter_upwards [hyd, hyU] with z hz hzU hzH
  exact mem_idealPow_of_vanishesToOrderOn_univ ((hz hzH).2 (s i) (hmem i z hzU))

variable (n) in
/-- **The exponent of `𝔞` along `H` at `x`**: the largest `e` with `IsDivNear 𝔞 H e x` (`0` if there is none, or if
every `e` works). -/
noncomputable def divExp (𝔞 : GermIdeal n M) (H : Set M) (x : M) : ℕ := by
  classical
  exact if h : ∃ e, ¬ IsDivNear n 𝔞 H (e + 1) x then Nat.find h else 0

/-- `𝔞_x` contains a germ that does not vanish near `x`. -/
def IsNonzeroAt (𝔞 : GermIdeal n M) (x : M) : Prop :=
  ∃ g, 𝔞.mem x g ∧ ∃ᶠ y in 𝓝 x, g y ≠ 0

/-- **The exponent is finite**: at a point `x ∈ H` where `𝔞_x` contains a germ not vanishing near `x`, some
`IsDivNear 𝔞 H e x` fails. -/
theorem exists_not_isDivNear (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) : ∃ e, ¬ IsDivNear n 𝔞 H (e + 1) x := by
  obtain ⟨g, hg, hgne⟩ := hne
  obtain ⟨q, hq⟩ := exists_notMem_idealPow_of_frequently (h𝔞 x g hg) hgne
  refine ⟨q, fun hd => hq ?_⟩
  have h1 := (hd.self_of_nhds hx).2 g hg
  exact (idealPow_le_of_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) (Nat.le_succ q)) x g
    (mem_idealPow_of_vanishesToOrderOn_univ h1)

theorem isDivNear_divExp (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (x : M) :
    IsDivNear n 𝔞 H (divExp n 𝔞 H x) x := by
  classical
  unfold divExp
  split_ifs with h
  · rcases hm : Nat.find h with _ | m
    · exact isDivNear_zero h𝔞 x
    · have := Nat.find_min h (show m < Nat.find h by omega)
      push Not at this
      exact this
  · exact isDivNear_zero h𝔞 x

theorem not_isDivNear_divExp_succ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) : ¬ IsDivNear n 𝔞 H (divExp n 𝔞 H x + 1) x := by
  classical
  have h := exists_not_isDivNear h𝔞 hx hne
  unfold divExp
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **The exponent characterizes divisibility**: `IsDivNear 𝔞 H e x ↔ e ≤ divExp 𝔞 H x`. -/
theorem isDivNear_iff_le_divExp (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {x : M} (hx : x ∈ H)
    (hne : IsNonzeroAt 𝔞 x) {e : ℕ} : IsDivNear n 𝔞 H e x ↔ e ≤ divExp n 𝔞 H x := by
  refine ⟨fun hd => ?_, fun he => (isDivNear_divExp h𝔞 x).mono he⟩
  by_contra hlt
  exact not_isDivNear_divExp_succ h𝔞 hx hne (hd.mono (by omega))

/-- **The exponent is locally constant on `H`** (`hir:divisor-exponent`): for `𝔞` coherent, nonzero at every point
near `x`, and `H` a submanifold at `x`, `divExp 𝔞 H y = divExp 𝔞 H x` for `y ∈ H` near `x`. -/
theorem eventually_divExp_eq (h𝔞 : 𝔞.IsCoherent) {x : M} {k : ℕ} (hH : RegularAtDim (n := n) H x k)
    (hne : ∀ᶠ y in 𝓝 x, IsNonzeroAt 𝔞 y) :
    ∀ᶠ y in 𝓝 x, y ∈ H → divExp n 𝔞 H y = divExp n 𝔞 H x := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  set e := divExp n 𝔞 H x
  have hxH : x ∈ H := hH.2.1
  have h1 : ∀ᶠ y in 𝓝 x, IsDivNear n 𝔞 H e y := (isDivNear_divExp hhol x).eventually
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ H → ¬ IsDivNear n 𝔞 H (e + 1) y := by
    by_contra hc
    rw [Filter.not_eventually] at hc
    exact not_isDivNear_divExp_succ hhol hxH hne.self_of_nhds
      (isDivNear_of_frequently h𝔞 hH (hc.mono fun y hy => by push Not at hy; exact hy))
  filter_upwards [h1, h2, hne] with y hy1 hy2 hyne hyH
  have hle : e ≤ divExp n 𝔞 H y := (isDivNear_iff_le_divExp hhol hyH hyne).mp hy1
  have hlt : ¬ e + 1 ≤ divExp n 𝔞 H y := fun h => hy2 hyH ((isDivNear_iff_le_divExp hhol hyH hyne).mpr h)
  omega

end Exponent


end

end Hironaka.DivisorExponent

namespace Hironaka.CompanionReduction

open Hironaka.HolomorphicIdealSheaves
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.OrderMultiplicativity Hironaka.GermOrderProduct

universe u

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A germ outside `cosupp(𝔞, q)` (`N = M`) has a germ of `𝔞` outside `𝔪_x^q`. -/
theorem exists_notMem_idealPow_of_notMem_cosupport {𝔞 : GermIdeal n M} {x : M} {q : ℕ}
    (hx : x ∉ cosupport n univ 𝔞 q) : ∃ g, 𝔞.mem x g ∧ ¬ (idealPow (pointIdeal n x) q).mem x g := by
  by_contra! hall
  exact hx ⟨mem_univ x, fun g hg => vanishesToOrderOn_of_mem (hall g hg)⟩

end

end Hironaka.CompanionReduction
