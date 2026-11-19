import Hironaka.Analytic.ThetaPshConvexCombination
import Hironaka.Analytic.GlobalDiagonalScaling
import Hironaka.Analytic.KahlerCurrentPerturbation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ambient current `Q_M` of Copy-4 `sec:ambient`

Source: Copy-4, `sec:ambient`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1721-1750`),
where the ambient current of the principalization proof is the convex combination

  `Q_M = (1 - L/M) T_M + (L/M) R ∈ α`,   `φ_{Q_M} = (1 - L/M) U_M + (L/M) Φ_R`,

of a regularization `T_M = θ + ddᶜU_M ≥ -(c₀/M) ω` — whose lower bound is
*negative*, so it is not a Kähler current — and a Kähler current
`R = θ + ddᶜΦ_R ≥ δ_R ω` whose polar set is `E_nK(α)`.  The three facts the
manuscript extracts from this are `eq:QM-positivity`, `eq:phiQ-lower`, and
`φ_{Q_M} = -∞` on the polar set of `R`.  All three are proved here.

**What this module does and does not contain.**  `T_M` comes from
`lem:regularization` and `R` from `sec:nK`; both are open targets of this
project (`Hironaka.QuantitativeRegularization`,
`Hironaka.KahlerCurrentRegularization`).  Nothing here names them, weakens them,
or assumes a regularization theorem: every statement below takes *arbitrary*
potentials with the stated one-sided bounds and proves the quantitative
consequence.  That consequence is the whole content of `sec:ambient`, and it is
independent of how the two inputs are produced.

The engine is convexity of `PSH(X, ·)` *in the form as well as in the potential*:
`u ∈ PSH(X, θ₁)` and `v ∈ PSH(X, θ₂)` give
`t u + (1-t) v ∈ PSH(X, t θ₁ + (1-t) θ₂)`.  Its substance —
the `ThetaPlurisubharmonic` half — is **already proved** in the workspace, as
`Hironaka.GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul` (`s a + r b` is
`(s α + r β)`-PSH for `s, r > 0`), whose conclusion at `s = t`, `r = 1-t` is
definitionally `convexComb t u v`;
`isThetaPshPotential_convexComb_forms` below only adds the local-nondegeneracy
half, taken verbatim from
`Hironaka.ThetaPshConvexCombination.isThetaPshPotential_convexComb` (which covers
one fixed `θ` only).  Specialised to `θ₁ = θ - a ω` and `θ₂ = θ - b ω` with
`a, b` real of **either sign**, the combined lower bound is `t a + (1-t) b`;
`eq:QM-positivity` is the arithmetic of that one number.

Everything here is sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Hironaka.AmbientConvexCurrent

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.NumericalRestrictedVolumeScaffold ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Convexity in the form -/

/-- **`PSH` is convex in the form as well as in the potential**, for genuine
`θ`-PSH *potentials*: if `u` is `θ₁`-PSH and `v` is `θ₂`-PSH then `t u + (1-t) v`
is `(t θ₁ + (1-t) θ₂)`-PSH.

Both halves are reuse.  The `ThetaPlurisubharmonic` half is
`GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul` at `s = t`, `r = 1-t`
(whose conclusion is definitionally `convexComb t u v`); the local-nondegeneracy
half is the one from `ThetaPshConvexCombination.isThetaPshPotential_convexComb`,
which is where the pole set of the combination is shown to be locally
pluripolar. -/
theorem isThetaPshPotential_convexComb_forms {θ₁ θ₂ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ₁.val u)
    (hv : IsThetaPshPotential θ₂.val v) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsThetaPshPotential (t • θ₁ + (1 - t) • θ₂).val (convexComb t u v) := by
  refine ⟨GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul ht0 (by linarith) hu.1 hv.1, ?_⟩
  apply locallyNondegenerate_of_poles_pluripolar (n := n)
  exact (manifoldLocallyPluripolar_union
    (quasiPsh_poles_manifoldLocallyPluripolar hu.quasiPshPotential)
    (quasiPsh_poles_manifoldLocallyPluripolar hv.quasiPshPotential)).mono
    (poles_convexComb_subset ht0 ht1 u v)

/-! ### The combined Kähler lower bound -/

/-- The convex combination of two shifted backgrounds is the background shifted
by the convex combination of the shifts.  No sign restriction on `a`, `b`. -/
theorem smul_sub_add_smul_sub (θ w : ClosedRealOneOneForm n M) (t a b : ℝ) :
    t • (θ - a • w) + (1 - t) • (θ - b • w)
      = θ - (t * a + (1 - t) * b) • w := by
  apply ClosedRealOneOneForm.ext
  intro e z
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul]
  module

/-- **The combined lower bound.**  If `θ + ddᶜu ≥ a ω` and `θ + ddᶜv ≥ b ω` —
with `a` and `b` real of either sign, so that neither current need be Kähler —
then the convex combination satisfies `θ + ddᶜ(t u + (1-t) v) ≥ (t a + (1-t) b) ω`. -/
theorem isThetaPshPotential_convexComb_sub_smul {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) {u v : M → EReal} {a b t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu : IsThetaPshPotential (θ - a • omega.form).val u)
    (hv : IsThetaPshPotential (θ - b • omega.form).val v) :
    IsThetaPshPotential (θ - (t * a + (1 - t) * b) • omega.form).val
      (convexComb t u v) := by
  have h := isThetaPshPotential_convexComb_forms hu hv ht0 ht1
  rwa [smul_sub_add_smul_sub] at h

/-- A strictly positive combined lower bound makes the combination a Kähler
current in the class of `θ`. -/
def kahlerCurrentOfSubSmul {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) {w : M → EReal}
    (hw : IsThetaPshPotential (θ - c • omega.form).val w) :
    KahlerCurrent (RealBottChern.ofRepresentative θ) where
  representative := θ
  represents := rfl
  potential := w
  lowerBound := KahlerBackground.smul hc omega
  strictlyPsh := by rw [KahlerBackground.smul_form]; exact hw

@[simp] theorem kahlerCurrentOfSubSmul_potential {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) {w : M → EReal}
    (hw : IsThetaPshPotential (θ - c • omega.form).val w) :
    (kahlerCurrentOfSubSmul omega hc hw).potential = w := rfl

/-! ### `eq:QM-positivity` -/

/-- **`eq:QM-positivity`.**  With `T_M ≥ -(c₀/M) ω` and `R ≥ δ_R ω`, the ambient
current `Q_M = (1 - L/M) T_M + (L/M) R` satisfies

  `Q_M ≥ ((L δ_R - c₀ + L c₀ / M) / M) ω ≥ ε₀ ω`,   `ε₀ = (L δ_R - c₀) / M > 0`,

exactly the two displayed inequalities of Copy-4 `eq:QM-positivity` — the first
constant is the sharper one and, as in the manuscript, `ε₀` names the second.
The hypothesis `c₀ < L δ_R` is Copy-4's `eq:constants`. -/
theorem isThetaPshPotential_ambient {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground n M) {U Φ : M → EReal} {c₀ δR L lev : ℝ}
    (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hlev : L < lev) (hconst : c₀ < L * δR)
    (hU : IsThetaPshPotential (θ + (c₀ / lev) • omega.form).val U)
    (hΦ : IsThetaPshPotential (θ - δR • omega.form).val Φ) :
    (L * δR - c₀) / lev ≤ (L * δR - c₀ + L * c₀ / lev) / lev ∧
      0 < (L * δR - c₀ + L * c₀ / lev) / lev ∧
      IsThetaPshPotential
        (θ - ((L * δR - c₀ + L * c₀ / lev) / lev) • omega.form).val
        (convexComb (1 - L / lev) U Φ) := by
  have hlev0 : 0 < lev := lt_trans hL hlev
  have hratio : L / lev < 1 := (div_lt_one hlev0).mpr hlev
  have hratio0 : 0 < L / lev := by positivity
  have ht0 : 0 < 1 - L / lev := by linarith
  have ht1 : 1 - L / lev < 1 := by linarith
  have hfirst : 0 < (L * δR - c₀) / lev := by
    apply div_pos (by linarith) hlev0
  have hextra : 0 ≤ L * c₀ / lev := by positivity
  have hle : (L * δR - c₀) / lev ≤ (L * δR - c₀ + L * c₀ / lev) / lev := by
    gcongr
    linarith
  refine ⟨hle, lt_of_lt_of_le hfirst hle, ?_⟩
  have hU' : IsThetaPshPotential (θ - (-(c₀ / lev)) • omega.form).val U := by
    rwa [neg_smul, sub_neg_eq_add]
  have h := isThetaPshPotential_convexComb_sub_smul omega ht0 ht1 hU' hΦ
  have harith : (1 - L / lev) * (-(c₀ / lev)) + (1 - (1 - L / lev)) * δR
      = (L * δR - c₀ + L * c₀ / lev) / lev := by
    field_simp
    ring
  rwa [harith] at h

/-! ### `eq:phiQ-lower` and the polar set -/

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A finite additive shift of each argument passes through the convex
combination with the convex combination of the shifts. -/
theorem convexComb_add_coe {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (f g : M → EReal) (C₁ C₂ : ℝ) (x : M) :
    convexComb t (fun y => f y + (C₁ : EReal)) (fun y => g y + (C₂ : EReal)) x
      = convexComb t f g x + ((t * C₁ + (1 - t) * C₂ : ℝ) : EReal) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  simp only [convexComb]
  rw [coe_mul_add_coe ht0, coe_mul_add_coe ht1', EReal.coe_add]
  abel

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **`eq:phiQ-lower`.**  A local lower bound `u ≥ f + O(1)` for each summand
gives the convex combination the convex combination of the lower bounds, again
up to `O(1)`; the new constant is `t C₁ + (1-t) C₂`.  This is the shape in which
Copy-4 combines `eq:def-TM` and `eq:PhiR-lower` into `eq:phiQ-lower`. -/
theorem convexComb_lower_bound {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {u v f g : M → EReal} {S : Set M} {C₁ C₂ : ℝ}
    (hu : ∀ y ∈ S, f y ≤ u y + (C₁ : EReal))
    (hv : ∀ y ∈ S, g y ≤ v y + (C₂ : EReal)) :
    ∀ y ∈ S, convexComb t f g y
      ≤ convexComb t u v y + ((t * C₁ + (1 - t) * C₂ : ℝ) : EReal) := by
  intro y hy
  rw [← convexComb_add_coe ht0 ht1 u v C₁ C₂ y]
  simp only [convexComb_apply]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hu y hy) (EReal.coe_nonneg.mpr ht0.le))
    (mul_le_mul_of_nonneg_left (hv y hy) (EReal.coe_nonneg.mpr (by linarith)))

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **The polar set of the ambient current contains that of `R`.**  A pole of the
second summand is a pole of the combination: `⊥` absorbs the sum.  This is
Copy-4's "`φ_{Q_M} = -∞` at every point of `V`", since the polar set of `R` is
`E_nK(α) ⊇ V`. -/
theorem poleSet_subset_poleSet_convexComb {t : ℝ} (ht1 : t < 1)
    (u v : M → EReal) : poleSet v ⊆ poleSet (convexComb t u v) := by
  have ht1' : 0 < 1 - t := by linarith
  intro x hx
  show convexComb t u v x = ⊥
  rw [convexComb_apply, (show v x = ⊥ from hx), EReal.coe_mul_bot_of_pos ht1',
    EReal.add_bot]

end

end Hironaka.AmbientConvexCurrent
