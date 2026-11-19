import Hironaka.Analytic.DemaillySymmetricGluing

set_option autoImplicit false

/-!
# The `M_δ`-glued approximations: monotonicity and convergence from branch data

Demailly's approximation theorem (`bou02-volume:2.6`, clause (ii)) asks the global approximants
to DECREASE to `φ`.  Copy-4's `lem:regularization` glues, for each `m`, local branches `b_{m,j}` on a
fixed cover with Demailly's regularized maximum (`DemaillySymmetricGluing.rglue`, with
`δ_m = 1/(2m)` and `A_m = (C_B + 1)/m` as in `exists_regularization_of_branches_rmax`).  This module
shows that the two local facts proved for Bergman weights in
`Hironaka.BergmanWeightConvergence` pass through the gluing:

* `glued_two_mul_le`: if `b_{2m,j} ≤ b_{m,j} + D/m` on `V_j` (the doubling inequality,
  `BergmanWeightConvergence.bergmanWeight_two_mul_le` in a chart), then
  `φ_{2m} ≤ φ_m + (D + 1/4)/m` everywhere;
* `antitone_glued_dyadic`: hence `φ_{2^k} + 2(D + 1/4) 2^{-k}` is nonincreasing in `k`;
* `tendsto_glued`: if `b_{m,j}(y) → φ(y)` at every `y ∈ V_j` (pointwise convergence,
  `BergmanWeightConvergence.tendsto_bergmanWeight` in a chart), then `φ_m(y) → φ(y)` everywhere
  (the cut-offs are assumed bounded above by a constant `K`; Copy-4 has `0 ≤ χ_j ≤ 1`).

The proofs use only `max ≤ M_δ ≤ max + δ`, monotonicity of `M_δ`, `χ_j ≥ 0` and `A_{2m} ≤ A_m`:
the active index sets of `φ_{2m}` and `φ_m` at a point are the same, since the cover is fixed.
Together with `DemaillySymmetricGluing.isThetaPshPotential_rglue` (curvature loss `c/m`) this is the
manifold form of Demailly's clause (ii), modulo the branch data on the fixed cover.
-/

open Set Filter
open scoped Topology

namespace Hironaka.DemaillySymmetricGluingLimit


open Hironaka.SymmetricRegularizedMaxPsh
open Hironaka.QuantitativeRegularizationMaxGluing
open Hironaka.DemaillySymmetricGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {ι : Type*} [Fintype ι] (P : CutoffCover n M ι)

/-- The `m`-th glued approximation, with `δ_m = 1/(2m)` and `A_m = (C_B + 1)/m`. -/
def glued (CB : ℝ) (b : ℕ → ι → M → EReal) (m : ℕ) (y : M) : EReal :=
  rglue P (1 / (2 * (m : ℝ))) (b m) ((CB + 1) / (m : ℝ)) y

theorem branch_add_coe_le {b : ι → M → EReal} {A A' : ℝ} (hA' : A' ≤ A) {j : ι} {y : M}
    {e : EReal} (h : e ≤ b j y) : e + ((A' * P.χ j y : ℝ) : EReal) ≤ P.branch b A j y := by
  unfold CutoffCover.branch
  gcongr
  exact P.χ_nonneg j y

/-- **Doubling passes through the gluing.** -/
theorem glued_two_mul_le {CB D : ℝ} (hCB : 0 ≤ CB) {b : ℕ → ι → M → EReal} {m : ℕ}
    (hm : 1 ≤ m)
    (hdouble : ∀ j, ∀ y ∈ P.V j, b (2 * m) j y ≤ b m j y + ((D / (m : ℝ) : ℝ) : EReal))
    (y : M) :
    glued P CB b (2 * m) y ≤ glued P CB b m y + (((D + 1 / 4) / (m : ℝ) : ℝ) : EReal) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  set g := glued P CB b m y with hgdef
  have hδ' : (0 : ℝ) < 1 / (2 * ((2 * m : ℕ) : ℝ)) := by rw [hcast]; positivity
  have hAA : (CB + 1) / ((2 * m : ℕ) : ℝ) ≤ (CB + 1) / (m : ℝ) := by
    rw [hcast]
    exact div_le_div_of_nonneg_left (by linarith) hmpos (by linarith)
  have hδ : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  -- every entry of the finer glue is below `g + D/m`
  have hentry : ∀ j ∈ activeSet P y,
      P.branch (b (2 * m)) ((CB + 1) / ((2 * m : ℕ) : ℝ)) j y ≤
        g + ((D / (m : ℝ) : ℝ) : EReal) := by
    intro j hj
    have hyV : y ∈ P.V j := (mem_activeSet P).mp hj
    have h1 : P.branch (b (2 * m)) ((CB + 1) / ((2 * m : ℕ) : ℝ)) j y ≤
        P.branch (b m) ((CB + 1) / (m : ℝ)) j y + ((D / (m : ℝ) : ℝ) : EReal) := by
      unfold CutoffCover.branch
      calc b (2 * m) j y + (((CB + 1) / ((2 * m : ℕ) : ℝ) * P.χ j y : ℝ) : EReal)
          ≤ (b m j y + ((D / (m : ℝ) : ℝ) : EReal)) +
              (((CB + 1) / (m : ℝ) * P.χ j y : ℝ) : EReal) := by
            gcongr
            · exact hdouble j y hyV
            · exact P.χ_nonneg j y
        _ = b m j y + (((CB + 1) / (m : ℝ) * P.χ j y : ℝ) : EReal) +
              ((D / (m : ℝ) : ℝ) : EReal) := by
            rw [add_assoc, add_comm ((D / (m : ℝ) : ℝ) : EReal), ← add_assoc]
    refine h1.trans ?_
    gcongr
    exact branch_le_rglue P hδ (b m) _ hyV
  by_cases hgtop : g = ⊤
  · rw [hgtop, EReal.top_add_coe]
    exact le_top
  by_cases hgbot : g = ⊥
  · have hbot : ∀ j ∈ activeSet P y,
        P.branch (b (2 * m)) ((CB + 1) / ((2 * m : ℕ) : ℝ)) j y = ⊥ := fun j hj => by
      have := hentry j hj
      rw [hgbot, EReal.bot_add, le_bot_iff] at this
      exact this
    have : glued P CB b (2 * m) y = ⊥ := ermax_of_bot hbot
    rw [this]
    exact bot_le
  · set g' : ℝ := g.toReal with hg'def
    have hgg : g = (g' : EReal) := (EReal.coe_toReal hgtop hgbot).symm
    have hle := ermax_le hδ' (S := activeSet P y)
      (t := fun j => P.branch (b (2 * m)) ((CB + 1) / ((2 * m : ℕ) : ℝ)) j y)
      (c := g' + D / (m : ℝ)) fun j hj => by
        have := hentry j hj
        rw [hgg, ← EReal.coe_add] at this
        exact this
    refine hle.trans (le_of_eq ?_)
    rw [hgg, ← EReal.coe_add, EReal.coe_eq_coe_iff, hcast]
    field_simp
    ring

/-- **Demailly's decreasing sequence, glued**: `φ_{2^k} + 2(D + 1/4) 2^{-k}` is nonincreasing. -/
theorem antitone_glued_dyadic {CB D : ℝ} (hCB : 0 ≤ CB) {b : ℕ → ι → M → EReal}
    (hdouble : ∀ m : ℕ, 1 ≤ m → ∀ j, ∀ y ∈ P.V j,
      b (2 * m) j y ≤ b m j y + ((D / (m : ℝ) : ℝ) : EReal)) (y : M) :
    Antitone fun k : ℕ =>
      glued P CB b (2 ^ k) y + ((2 * (D + 1 / 4) * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h := glued_two_mul_le P hCB hk1 (hdouble (2 ^ k) hk1) y
  have hpow : (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) := by ring
  rw [hpow] at h
  have hcastk : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcastk] at h
  calc glued P CB b (2 ^ (k + 1)) y + ((2 * (D + 1 / 4) * ((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : EReal)
      ≤ (glued P CB b (2 ^ k) y + (((D + 1 / 4) / (2 : ℝ) ^ k : ℝ) : EReal)) +
          ((2 * (D + 1 / 4) * ((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : EReal) := by gcongr
    _ = glued P CB b (2 ^ k) y + ((2 * (D + 1 / 4) * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
        congr 2
        rw [pow_succ]
        field_simp
        ring

/-- **The glued approximations converge pointwise** to the common limit of the branches. -/
theorem tendsto_glued {CB K : ℝ} (hCB : 0 ≤ CB) (hχK : ∀ j y, P.χ j y ≤ K)
    {b : ℕ → ι → M → EReal} {φ : M → EReal}
    (hconv : ∀ j, ∀ y ∈ P.V j, Tendsto (fun m => b m j y) atTop (𝓝 (φ y))) (y : M) :
    Tendsto (fun m => glued P CB b m y) atTop (𝓝 (φ y)) := by
  obtain ⟨l, hl⟩ := P.cover y
  have hyl : y ∈ P.V l := P.U_subset_V l hl
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [(hconv l y hyl).eventually (lt_mem_nhds ha), eventually_ge_atTop 1]
      with m hm hm1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    exact hm.trans_le (le_rglue P (by positivity) (b m) (by positivity) hyl)
  · obtain ⟨a', ha', ha'a⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    obtain ⟨a'', ha'a'', ha''a⟩ := EReal.lt_iff_exists_real_btwn.mp ha'a
    rw [EReal.coe_lt_coe_iff] at ha'a''
    have hev : ∀ᶠ m in atTop, ∀ j ∈ activeSet P y, b m j y < (a' : EReal) :=
      (Filter.eventually_all_finset _).mpr fun j hj =>
        (hconv j y ((mem_activeSet P).mp hj)).eventually (gt_mem_nhds ha')
    have hsmall : Tendsto (fun m : ℕ => (CB + 1) / (m : ℝ) * K + 1 / (2 * (m : ℝ)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => ((m : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have := (h1.const_mul ((CB + 1) * K)).add (h1.const_mul (1 / 2))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      field_simp
    filter_upwards [hev, hsmall.eventually (gt_mem_nhds (sub_pos.mpr ha'a'')),
      eventually_ge_atTop 1] with m hm hε hm1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hle := ermax_le (δ := 1 / (2 * (m : ℝ))) (by positivity)
      (t := fun j => P.branch (b m) ((CB + 1) / (m : ℝ)) j y)
      (c := a' + (CB + 1) / (m : ℝ) * K) fun j hj => by
        show b m j y + (((CB + 1) / (m : ℝ) * P.χ j y : ℝ) : EReal) ≤ _
        rw [EReal.coe_add]
        exact add_le_add (hm j hj).le (EReal.coe_le_coe_iff.mpr
          (mul_le_mul_of_nonneg_left (hχK j y) (by positivity)))
    refine hle.trans_lt (lt_trans ?_ ha''a)
    rw [EReal.coe_lt_coe_iff]
    linarith

/-- The dyadic sequence of `antitone_glued_dyadic` converges to the same limit. -/
theorem tendsto_glued_dyadic {CB K E : ℝ} (hCB : 0 ≤ CB) (hχK : ∀ j y, P.χ j y ≤ K)
    {b : ℕ → ι → M → EReal} {φ : M → EReal}
    (hconv : ∀ j, ∀ y ∈ P.V j, Tendsto (fun m => b m j y) atTop (𝓝 (φ y))) (y : M) :
    Tendsto (fun k : ℕ => glued P CB b (2 ^ k) y + ((E * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal))
      atTop (𝓝 (φ y)) := by
  have hφ := (tendsto_glued P hCB hχK hconv y).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  have hc : Tendsto (fun k : ℕ => ((E * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal)) atTop
      (𝓝 ((0 : ℝ) : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    have := (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul E
    simpa using this
  have hadd := (EReal.continuousAt_add (p := (φ y, ((0 : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))).tendsto.comp
      (hφ.prodMk_nhds hc)
  have h0 : φ y + ((0 : ℝ) : EReal) = φ y := by rw [EReal.coe_zero, add_zero]
  rw [h0] at hadd
  exact hadd

end

end Hironaka.DemaillySymmetricGluingLimit
