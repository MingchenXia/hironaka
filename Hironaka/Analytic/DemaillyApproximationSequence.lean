import Hironaka.Analytic.DemaillyChartBranchLimit
import Hironaka.Analytic.DemaillySymmetricGluingLimit
import Hironaka.Analytic.QuantitativeRegularizationFixedCover

set_option autoImplicit false

/-!
# Demailly's decreasing approximation on a compact Kähler manifold: clauses (ii) and (iv)

Demailly 1992 (`bou02-volume:2.6`; `Hironaka.Demailly1992AlgebraicApproximation`) asks, for a
`α`-PSH potential `ψ` on a compact Kähler manifold, approximants `ψ_k` that
(i) have analytic singularities, (ii) decrease to `ψ` everywhere, and (iv) are
`(α + δ_k ω)`-PSH potentials with `δ_k → 0`.  This module constructs Demailly's sequence
explicitly and proves (ii) and (iv) for it; clause (i) is a statement about the same explicit
functions and is the remaining part of programme `TN.3.3.DEMPROVE`.

The construction (Copy-4 `lem:regularization`, Steps 1--3, with Demailly's monotonicity
device):

* the fixed chart cover `F : FixedChartCover d Z` of TN-CLASSICAL
  (`QuantitativeRegularizationFixedCover.exists_fixedChartCover`): charts `e_j`, Bergman balls
  `B_j = ball c_j β_j`, a cut-off cover with `0 ≤ χ_j ≤ 1`, and an overlap constant `C_B`;
* potentials `ρ_j` of `α` on the potential balls, chosen ONCE (before `m`);
* the chart Bergman branches `b_{m,j} = F.branch ρ ψ m j = m⁻¹ log K_{B_j, e^{-mΨ_j}} ∘ e_j - ρ_j ∘ e_j`;
* the `M_δ`-glued function `φ_m = DemaillySymmetricGluingLimit.glued` (`δ_m = 1/(2m)`,
  `A_m = (C_B + 1)/m`);
* `ψ_k = φ_{2^k} + E 2^{-k}` (`seq`), with `E = 2(D + 1/4)` and `D` the doubling constant of the
  cover (`exists_doublingConst`, from Demailly's subadditivity `K_{2m} ≤ C K_m²`).

Main results:

* `antitone_seq` — clause (ii-a): `k ↦ ψ_k(x)` is nonincreasing at every `x`
  (`DemaillySymmetricGluingLimit.antitone_glued_dyadic` fed with
  `DemaillyChartBranchLimit.exists_chartBergmanBranch_two_mul_le`);
* `iInf_seq` — clause (ii-b): `⨅ k, ψ_k(x) = ψ(x)` at every `x`, poles included
  (`DemaillySymmetricGluingLimit.tendsto_glued_dyadic` fed with
  `DemaillyChartBranchLimit.tendsto_chartBergmanBranch` and `χ_j ≤ 1`);
* `isThetaPshPotential_seq` — clause (iv): `ψ_k` is an `(α + δ_k ω)`-PSH potential with
  `δ_k = (C_B + 1) C_χ / 2^k` (`DemaillySymmetricGluing.isThetaPshPotential_rglue`);
* `exists_decreasingApproximation` — the statement of
  `Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation` without
  clause (i), for every compact Kähler `Z` (dimension `0` included, no connectedness).
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.DemaillyApproximationSequence

open Hironaka.PositiveClasses
open Hironaka.QuantitativeRegularizationChartBranch
open Hironaka.QuantitativeRegularizationMaxGluing
open Hironaka.QuantitativeRegularizationFixedCover
open Hironaka.DemaillySymmetricGluing
open Hironaka.DemaillySymmetricGluingLimit
open Hironaka.DemaillyChartBranchLimit

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **The doubling constant of a fixed chart cover**: one `D ≥ 0`, depending on the cover alone,
with `b_{2m,j} ≤ b_{m,j} + D/m` on `V_j` for every form, every potentials `ρ_j` of it on the
potential balls, every weight and every `m ≥ 1`. -/
theorem exists_doublingConst (F : FixedChartCover d Z) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ζ : SmoothRealForm d Z 2) (φ : Z → EReal), ThetaPlurisubharmonic ζ φ →
      ∀ ρ : F.t → ComplexModel d → ℝ,
      (∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
        F.branch ρ φ (2 * m) j y ≤ F.branch ρ φ m j y + ((D / (m : ℝ) : ℝ) : EReal) := by
  classical
  have hex : ∀ j : F.t, ∃ D : ℝ, ∀ (ζ : SmoothRealForm d Z 2) (φ : Z → EReal),
      ThetaPlurisubharmonic ζ φ →
      ∀ (e : ComplexChart d Z) (Ω : Set (ComplexModel d)) (ρ : ComplexModel d → ℝ),
      IsSmoothLocalPotential ζ e Ω ρ → ball (F.center j) (F.bergmanRadius j) ⊆ Ω →
      ∀ m : ℕ, 1 ≤ m → ∀ x ∈ chartPatch e (ball (F.center j) (F.bergmanRadius j)),
        chartBergmanBranch e (ball (F.center j) (F.bergmanRadius j)) ρ φ (2 * m) x ≤
          chartBergmanBranch e (ball (F.center j) (F.bergmanRadius j)) ρ φ m x +
            ((D / (m : ℝ) : ℝ) : EReal) := fun j =>
    exists_chartBergmanBranch_two_mul_le (F.center j) (F.bergmanRadius_pos j)
  choose D hD using hex
  refine ⟨∑ j, max (D j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _,
    fun ζ φ hφ ρ hρ m hm j y hy => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hball : ball (F.center j) (F.bergmanRadius j) ⊆ ball (F.center j) (F.potentialRadius j) :=
    ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  refine (hD j ζ φ hφ (F.chart j) _ (ρ j) (hρ j) hball m hm y
    (F.V_subset_chartPatch j hy)).trans ?_
  have hle : D j ≤ ∑ j, max (D j) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (D j) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ j))
  unfold FixedChartCover.branch
  gcongr

/-- **Demailly's approximating sequence** `ψ_k = φ_{2^k} + E 2^{-k}`, with `φ_m` the
`M_δ`-glued chart Bergman branches of `F` at level `m`. -/
def seq (F : FixedChartCover d Z) (ρ : F.t → ComplexModel d → ℝ) (φ : Z → EReal) (E : ℝ)
    (k : ℕ) (y : Z) : EReal :=
  glued F.cover F.CB (fun m => F.branch ρ φ m) (2 ^ k) y + ((E * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal)

/-- **Clause (ii-a): the sequence decreases**, for `E = 2(D + 1/4)` with `D` a doubling
constant of the cover. -/
theorem antitone_seq (F : FixedChartCover d Z) {D : ℝ}
    {φ : Z → EReal} {ρ : F.t → ComplexModel d → ℝ}
    (hdouble : ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
      F.branch ρ φ (2 * m) j y ≤ F.branch ρ φ m j y + ((D / (m : ℝ) : ℝ) : EReal)) (y : Z) :
    Antitone fun k => seq F ρ φ (2 * (D + 1 / 4)) k y :=
  antitone_glued_dyadic F.cover F.CB_nonneg hdouble y

/-- The sequence converges to `φ` at every point (poles included). -/
theorem tendsto_seq (F : FixedChartCover d Z) {ζ : SmoothRealForm d Z 2} {φ : Z → EReal}
    (hφ : ThetaPlurisubharmonic ζ φ) {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    (E : ℝ) (y : Z) :
    Tendsto (fun k => seq F ρ φ E k y) atTop (𝓝 (φ y)) := by
  refine tendsto_glued_dyadic F.cover F.CB_nonneg F.χ_le_one (fun j x hx => ?_) y
  exact tendsto_chartBergmanBranch hφ (hρ j)
    (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le) (F.V_subset_chartPatch j hx)

/-- **Clause (ii-b): the infimum of the sequence is `φ`**, at every point. -/
theorem iInf_seq (F : FixedChartCover d Z) {D : ℝ} {ζ : SmoothRealForm d Z 2} {φ : Z → EReal}
    (hφ : ThetaPlurisubharmonic ζ φ) {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    (hdouble : ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ F.cover.V j,
      F.branch ρ φ (2 * m) j y ≤ F.branch ρ φ m j y + ((D / (m : ℝ) : ℝ) : EReal)) (y : Z) :
    ⨅ k, seq F ρ φ (2 * (D + 1 / 4)) k y = φ y :=
  tendsto_nhds_unique (tendsto_atTop_iInf (antitone_seq F hdouble y))
    (tendsto_seq F hφ hρ _ y)

/-- **Clause (iv): the curvature loss.**  With `C_χ > 0` such that every `ddᶜχ_j + C_χ ω` is
semipositive, `ψ_k` is an `(α + δ_k ω)`-PSH potential for `δ_k = (C_B + 1)/2^k · C_χ`. -/
theorem isThetaPshPotential_seq (hd : 0 < d) (F : FixedChartCover d Z)
    (omega : KahlerBackground d Z) {Cχ : ℝ}
    (hCχ : ∀ j, (ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j)
      + Cχ • omega.form).val.IsSemipositive)
    {α : ClosedRealOneOneForm d Z} {φ : Z → EReal} (hφ : IsThetaPshPotential α.val φ)
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α.val (F.chart j) (ball (F.center j) (F.potentialRadius j))
      (ρ j)) (E : ℝ) (k : ℕ) :
    IsThetaPshPotential (α + ((F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ) • omega.form).val
      (seq F ρ φ E k) := by
  have hm : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hm
  obtain ⟨hb, hcomp, hnd, -⟩ := F.branch_spec hd hρ hφ hm
  set m : ℕ := 2 ^ k with hmdef
  set A : ℝ := (F.CB + 1) / (m : ℝ) with hAdef
  set δ : ℝ := 1 / (2 * (m : ℝ)) with hδdef
  have hδ : 0 < δ := by positivity
  have hA0 : 0 ≤ A := by have := F.CB_nonneg; positivity
  have hA : F.CB / (m : ℝ) + δ ≤ A := by
    have hgap : A - (F.CB / (m : ℝ) + δ) = 1 / (2 * (m : ℝ)) := by
      rw [hAdef, hδdef]
      field_simp
      ring
    have : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
    linarith
  have h := isThetaPshPotential_rglue F.cover omega α (F.branch ρ φ m) hδ hA0 hA hb hcomp hCχ hnd
  exact h.add_const _

/-- **Demailly 1992, clauses (ii) and (iv)**, in positive dimension: the statement of
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation` without
clause (i), realised by `seq` on a fixed chart cover. -/
theorem exists_decreasingApproximation_of_pos [CompactSpace Z] (hd : 0 < d)
    (omega : KahlerBackground d Z) (α : ClosedRealOneOneForm d Z) (ψ : Z → EReal)
    (hψ : IsThetaPshPotential α.val ψ) :
    ∃ (F : FixedChartCover d Z) (ρ : F.t → ComplexModel d → ℝ) (E : ℝ) (delta : ℕ → ℝ),
      (∀ x, Antitone fun k => seq F ρ ψ E k x) ∧ (∀ x, ⨅ k, seq F ρ ψ E k x = ψ x) ∧
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (α + delta k • omega.form).val (seq F ρ ψ E k) := by
  obtain ⟨F⟩ := exists_fixedChartCover (Z := Z) hd
  obtain ⟨ρ, hρ⟩ := F.exists_potentials α
  obtain ⟨D, -, hD⟩ := exists_doublingConst F
  have hdouble := hD α.val ψ hψ.1 ρ hρ
  obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun j => ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j))
  refine ⟨F, ρ, 2 * (D + 1 / 4), fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ,
    fun x => antitone_seq F hdouble x, fun x => iInf_seq F hψ.1 hρ hdouble x,
    fun k => ?_, ?_, fun k => isThetaPshPotential_seq hd F omega hsemi hψ hρ _ k⟩
  · have := F.CB_nonneg
    positivity
  · have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    have h2 := h1.const_mul ((F.CB + 1) * Cχ)
    rw [mul_zero] at h2
    refine h2.congr fun k => ?_
    push_cast
    field_simp

/-- **Demailly 1992, clauses (ii) and (iv)**, on every compact Kähler manifold (no
connectedness, dimension `0` included): the statement of
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation` with clause (i)
removed. -/
theorem exists_decreasingApproximation [CompactSpace Z] (omega : KahlerBackground d Z)
    (α : ClosedRealOneOneForm d Z) (ψ : Z → EReal) (hψ : IsThetaPshPotential α.val ψ) :
    ∃ (psiSeq : ℕ → Z → EReal) (delta : ℕ → ℝ),
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = ψ x) ∧
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (α + delta k • omega.form).val (psiSeq k) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun _ => ψ, fun _ => 0, fun x => antitone_const, fun x => iInf_const,
      fun _ => le_rfl, tendsto_const_nhds, fun k => ?_⟩
    simpa only [zero_smul, add_zero] using hψ
  · obtain ⟨F, ρ, E, delta, h1, h2, h3, h4, h5⟩ :=
      exists_decreasingApproximation_of_pos hd omega α ψ hψ
    exact ⟨seq F ρ ψ E, delta, h1, h2, h3, h4, h5⟩

end

end Hironaka.DemaillyApproximationSequence
