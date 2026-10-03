/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicAnalytic
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The order of a product of holomorphic germs: `ord_x(fg) = ord_x f + ord_x g`

Sources: Włodarczyk 2005 Step 2a and Bierstone--Milman 2008 §5, Step II.B (the companion ideal: on the cosupport of
`(𝔟𝔠, d)` with `ord 𝔟 ≤ o`, the cosupport condition passes to `(𝔠, d - o)`).

## Main results

* `exists_apply_diag_ne_zero_both`: two nonzero symmetric continuous multilinear maps on `ℂⁿ` have a
  common direction `y` on which both diagonals `Φ(y, …, y)`, `Ψ(y, …, y)` are nonzero (polarization and
  the identity theorem for the polynomial functions `y ↦ Φ(y, …, y)`).
* `mem_idealPow_of_mul_mem` (**cancellation**): if `f g ∈ 𝔪_x^{a+b}` and `g ∉ 𝔪_x^{b+1}`, then
  `f ∈ 𝔪_x^a`; equivalently `ord_x(fg) ≤ ord_x f + ord_x g`.  Proof: restrict to a line `t ↦ p + t y`
  through `p = e x` in a common good direction `y`; the one-variable orders add (`analyticOrderAt_mul`).
* `mul_notMem_idealPow`: `f ∉ 𝔪_x^{a+1}`, `g ∉ 𝔪_x^{b+1}` ⟹ `f g ∉ 𝔪_x^{a+b+1}`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GermOrderProduct

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.OrderTaylor Hironaka.HolomorphicTaylorTail Hironaka.IdealOrderArithmetic Hironaka.HolomorphicAnalytic Hironaka.OrderMultiplicativity

noncomputable section

/-! ### A common good direction for two homogeneous polynomials -/

section Direction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The diagonal `y ↦ Φ(y, …, y)` of a continuous multilinear map is analytic everywhere. -/
theorem analyticOnNhd_diag {k : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) :
    AnalyticOnNhd ℂ (fun y : E => Φ (fun _ => y)) univ := by
  intro y _
  have hL : AnalyticAt ℂ
      (ContinuousLinearMap.pi fun _ : Fin k => ContinuousLinearMap.id ℂ E) y :=
    ContinuousLinearMap.analyticAt _ y
  exact Φ.analyticAt.comp hL

/-- A nonzero symmetric continuous multilinear map is nonzero somewhere on the diagonal
(polarization, `OrderMultiplicativity.eq_zero_of_symmetric_of_apply_diag`). -/
theorem exists_apply_diag_ne_zero {k : ℕ} {Φ : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ}
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (m : Fin k → E), Φ (m ∘ σ) = Φ m) (hΦ : Φ ≠ 0) :
    ∃ y : E, Φ (fun _ => y) ≠ 0 := by
  by_contra! h
  exact hΦ (eq_zero_of_symmetric_of_apply_diag k Φ hsym h)

/-- **A common good direction**: two nonzero symmetric continuous multilinear maps have a common
vector on which both diagonals are nonzero. -/
theorem exists_apply_diag_ne_zero_both {k l : ℕ}
    {Φ : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ}
    {Ψ : ContinuousMultilinearMap ℂ (fun _ : Fin l => E) ℂ}
    (hΦs : ∀ (σ : Equiv.Perm (Fin k)) (m : Fin k → E), Φ (m ∘ σ) = Φ m) (hΦ : Φ ≠ 0)
    (hΨs : ∀ (σ : Equiv.Perm (Fin l)) (m : Fin l → E), Ψ (m ∘ σ) = Ψ m) (hΨ : Ψ ≠ 0) :
    ∃ y : E, Φ (fun _ => y) ≠ 0 ∧ Ψ (fun _ => y) ≠ 0 := by
  obtain ⟨y₁, hy₁⟩ := exists_apply_diag_ne_zero hΦs hΦ
  obtain ⟨y₂, hy₂⟩ := exists_apply_diag_ne_zero hΨs hΨ
  by_contra! h
  -- `Ψ ∘ diag` vanishes on the open set `{Φ ∘ diag ≠ 0}`, a neighbourhood of `y₁`
  have hopen : IsOpen {y : E | Φ (fun _ => y) ≠ 0} :=
    isOpen_ne_fun (Φ.cont.comp (continuous_pi fun _ => continuous_id)) continuous_const
  have hloc : (fun y : E => Ψ (fun _ => y)) =ᶠ[𝓝 y₁] 0 :=
    eventually_of_mem (hopen.mem_nhds hy₁) fun y hy => h y hy
  have hzero := (analyticOnNhd_diag Ψ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ y₁) hloc
  exact hy₂ (hzero (mem_univ y₂))

end Direction

/-! ### Orders of products of holomorphic germs -/

section Germs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Along a line through `p` in a direction `y`, a function whose derivatives of order `< q` vanish at `p`
has order `≥ q` at `t = 0`. -/
theorem natCast_le_analyticOrderAt_line {G : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) {p : ComplexModel n} (hp : p ∈ U) (y : ComplexModel n)
    {q : ℕ} (hlow : ∀ i < q, iteratedFDeriv ℂ i G p = 0) :
    (q : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => G (p + t • y)) 0 := by
  have hφan : AnalyticAt ℂ (fun t : ℂ => G (p + t • y)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => p + t • y) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have : AnalyticAt ℂ G (p + (0 : ℂ) • y) := by simpa using hG p hp
    exact AnalyticAt.comp (g := G) (f := fun t : ℂ => p + t • y) this hlin
  have hGcd : ContDiffOn ℂ ∞ G U := hG.contDiffOn hU.uniqueDiffOn
  refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hφan).mpr fun i hi => ?_
  rw [iteratedDeriv_comp_line hU hGcd hp y i, hlow i hi]
  rfl

/-- Along a line through `p` in a direction `y` with `D^a G(p)(y, …, y) ≠ 0`, a function whose
derivatives of order `< a` vanish at `p` has order exactly `a` at `t = 0`. -/
theorem analyticOrderAt_line_eq {G : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) {p : ComplexModel n} (hp : p ∈ U) {y : ComplexModel n}
    {a : ℕ} (hlow : ∀ i < a, iteratedFDeriv ℂ i G p = 0)
    (hy : iteratedFDeriv ℂ a G p (fun _ => y) ≠ 0) :
    analyticOrderAt (fun t : ℂ => G (p + t • y)) 0 = a := by
  have hφan : AnalyticAt ℂ (fun t : ℂ => G (p + t • y)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => p + t • y) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have : AnalyticAt ℂ G (p + (0 : ℂ) • y) := by simpa using hG p hp
    exact AnalyticAt.comp (g := G) (f := fun t : ℂ => p + t • y) this hlin
  have hGcd : ContDiffOn ℂ ∞ G U := hG.contDiffOn hU.uniqueDiffOn
  have h1 : (a : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => G (p + t • y)) 0 :=
    natCast_le_analyticOrderAt_line hU hG hp y hlow
  have h2 : ¬ ((a + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun t : ℂ => G (p + t • y)) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hφan]
    intro hall
    exact hy (by rw [← iteratedDeriv_comp_line hU hGcd hp y a]; exact hall a (Nat.lt_succ_self a))
  refine le_antisymm ?_ h1
  by_contra hlt
  exact h2 (Order.add_one_le_of_lt (lt_of_not_ge hlt))

/-- The least `j` with a nonzero `j`-th derivative, below a bound `q` when some derivative of order
`< q` is nonzero. -/
theorem exists_least_ne_zero {G : ComplexModel n → ℂ} {p : ComplexModel n} {q : ℕ}
    (h : ∃ j < q, iteratedFDeriv ℂ j G p ≠ 0) :
    ∃ a < q, (∀ i < a, iteratedFDeriv ℂ i G p = 0) ∧ iteratedFDeriv ℂ a G p ≠ 0 := by
  classical
  have hex : ∃ j, iteratedFDeriv ℂ j G p ≠ 0 := by
    obtain ⟨j, -, hj⟩ := h
    exact ⟨j, hj⟩
  refine ⟨Nat.find hex, ?_, fun i hi => by simpa using Nat.find_min hex hi, Nat.find_spec hex⟩
  obtain ⟨j, hj, hjne⟩ := h
  exact lt_of_le_of_lt (Nat.find_min' hex hjne) hj

/-- **Cancellation of orders** (`ord_x(fg) ≤ ord_x f + ord_x g`): if `f g ∈ 𝔪_x^{a+b}` and
`g ∉ 𝔪_x^{b+1}`, then `f ∈ 𝔪_x^a`. -/
theorem mem_idealPow_of_mul_mem {x : M} {f g : M → ℂ} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) {a b : ℕ}
    (hgb : ¬ (idealPow (pointIdeal n x) (b + 1)).mem x g)
    (h : (idealPow (pointIdeal n x) (a + b)).mem x (fun p => f p * g p)) :
    (idealPow (pointIdeal n x) a).mem x f := by
  set e := complexChartAt (n := n) x
  set p := e.val x
  set F : ComplexModel n → ℂ := f ∘ e.val.symm
  set G : ComplexModel n → ℂ := g ∘ e.val.symm
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨U₁, hU₁, hU₁o, hpU₁⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hf)
  obtain ⟨U₂, hU₂, hU₂o, hpU₂⟩ := eventually_nhds_iff.mp (eventually_differentiableAt_comp_symm e hxe hg)
  set U := U₁ ∩ U₂
  have hUo : IsOpen U := hU₁o.inter hU₂o
  have hpU : p ∈ U := ⟨hpU₁, hpU₂⟩
  have hFan : AnalyticOnNhd ℂ F U :=
    analyticOnNhd_of_differentiableOn hUo fun z hz => (hU₁ z hz.1).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G U :=
    analyticOnNhd_of_differentiableOn hUo fun z hz => (hU₂ z hz.2).differentiableWithinAt
  have hFG : AnalyticOnNhd ℂ (fun z => F z * G z) U := fun z hz => (hFan z hz).mul (hGan z hz)
  have hfg : HolomorphicAt n (fun p => f p * g p) x := hf.mul hg
  have hcharFG := (mem_idealPow_pointIdeal_iff_iteratedFDeriv hfg (a + b)).mp h
  by_contra hfa
  rw [mem_idealPow_pointIdeal_iff_iteratedFDeriv hf] at hfa
  rw [mem_idealPow_pointIdeal_iff_iteratedFDeriv hg] at hgb
  push Not at hfa hgb
  obtain ⟨a', ha'a, hlowF, hF⟩ := exists_least_ne_zero hfa
  obtain ⟨b', hb'b, hlowG, hG⟩ := exists_least_ne_zero hgb
  -- a common direction
  obtain ⟨y, hyF, hyG⟩ := exists_apply_diag_ne_zero_both
    (fun σ m => ((hFan p hpU).contDiffAt).iteratedFDeriv_comp_perm m σ) hF
    (fun σ m => ((hGan p hpU).contDiffAt).iteratedFDeriv_comp_perm m σ) hG
  have hφ := analyticOrderAt_line_eq hUo hFan hpU hlowF hyF
  have hψ := analyticOrderAt_line_eq hUo hGan hpU hlowG hyG
  have hφan : AnalyticAt ℂ (fun t : ℂ => F (p + t • y)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => p + t • y) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have : AnalyticAt ℂ F (p + (0 : ℂ) • y) := by simpa using hFan p hpU
    exact AnalyticAt.comp (g := F) (f := fun t : ℂ => p + t • y) this hlin
  have hψan : AnalyticAt ℂ (fun t : ℂ => G (p + t • y)) 0 := by
    have hlin : AnalyticAt ℂ (fun t : ℂ => p + t • y) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have : AnalyticAt ℂ G (p + (0 : ℂ) • y) := by simpa using hGan p hpU
    exact AnalyticAt.comp (g := G) (f := fun t : ℂ => p + t • y) this hlin
  have hprod : analyticOrderAt ((fun t : ℂ => F (p + t • y)) * fun t : ℂ => G (p + t • y)) 0 =
      (a' : ℕ∞) + b' := by
    rw [analyticOrderAt_mul hφan hψan, hφ, hψ]
  have hle : ((a + b : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun t : ℂ => (fun z => F z * G z) (p + t • y)) 0 :=
    natCast_le_analyticOrderAt_line hUo hFG hpU y fun i hi => hcharFG i hi
  have heq : (fun t : ℂ => (fun z => F z * G z) (p + t • y)) =
      (fun t : ℂ => F (p + t • y)) * fun t : ℂ => G (p + t • y) := rfl
  rw [heq, hprod] at hle
  have : a + b ≤ a' + b' := by exact_mod_cast hle
  omega

/-- **Orders add**: if `f ∉ 𝔪_x^{a+1}` and `g ∉ 𝔪_x^{b+1}`, then `f g ∉ 𝔪_x^{a+b+1}`. -/
theorem mul_notMem_idealPow {x : M} {f g : M → ℂ} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    {a b : ℕ} (hfa : ¬ (idealPow (pointIdeal n x) (a + 1)).mem x f)
    (hgb : ¬ (idealPow (pointIdeal n x) (b + 1)).mem x g) :
    ¬ (idealPow (pointIdeal n x) (a + b + 1)).mem x (fun p => f p * g p) := by
  intro h
  rw [show a + b + 1 = (a + 1) + b by omega] at h
  exact hfa (mem_idealPow_of_mul_mem hf hg hgb h)

/-! ### Cosupports of products (`N = M`) -/

/-- Membership in `𝔪_x^q` gives vanishing to order `q` along any set. -/
theorem vanishesToOrderOn_of_mem {N : Set M} {x : M} {q : ℕ} {g : M → ℂ}
    (hg : (idealPow (pointIdeal n x) q).mem x g) : VanishesToOrderOn n N x q g :=
  ⟨g, hg, Eventually.of_forall fun _ _ => rfl⟩

end Germs

end

end Hironaka.GermOrderProduct
