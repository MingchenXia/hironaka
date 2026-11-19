import Hironaka.Analytic.QuantitativeRegularizationBergmanOverlap

set_option autoImplicit false

/-!
# The overlap constant fixed by the cover alone, before the weight

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationBergmanOverlap.bergmanSup_le_of_pointExtension` proves
`eq:reg-overlap` for a *given* cut-off `θ` and a *given* weight `ϕ`, with a constant
`pointExtensionConst d r Mθ R S` that does not mention `ϕ`.  Copy-4 needs more than
that: it fixes the cover `U_j ⋐ V_j ⋐ B_j ⋐ B_j⁺` and the constant `C_B` **once and
for all**, and only afterwards chooses the background form `ζ` and the potential `φ`.
No module assembled that before, and only one of the
two directions `j ≤ l`, `l ≤ j` was available.

This module supplies both, at the level of coordinate balls:

* `exists_cutoff_ball` — a smooth cut-off equal to `1` on `closedBall c ρ`, supported
  inside `ball c β`, with `|θ| ≤ 1` and a *finite* bound on `‖dθ‖`.  The gradient
  bound is what enters the overlap constant, and mathlib's `ContDiffBump` supplies
  the function; the bound itself is compactness of the support.
* `exists_overlapConst_ball` — for a pair of balls `ball c β`, `ball c' β'` with
  compact closure in `D`, ONE constant `C > 0`, depending only on `d` and the radii,
  such that the one-sided comparison holds for EVERY admissible weight `ϕ` and every
  `x ∈ ball c (ρ/2) ∩ ball c' β'`.  The order of quantifiers is the point: `C` is
  chosen before `ϕ`.
* `exists_overlapConst_ball_pair` — the two-sided statement with a single constant,
  which is `eq:reg-overlap` in the form Copy-4 uses.
* `exists_overlapConst_ball_pair_log` — the same in the logarithmic normalization,
  `|ψ_j - ψ_l| ≤ C_B` before dividing by `m`.

**Scope.**  As everywhere upstream, `ϕ` is a *smooth* psh weight bounded below on `D`;
the passage to `ϕ = m Ψ` with `Ψ` singular (the main remaining gap of the chain) is untouched
here.  Nothing in this module is a restatement: the weight is
universally quantified after the constant, which none of the existing statements does.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.BergmanOverlapFixedCover

noncomputable section

open BergmanSupWeight
open QuantitativeRegularizationPointExtension
open QuantitativeRegularizationBergmanOverlap

variable {d : ℕ}

/-! ### A cut-off on a ball, with every datum the comparison consumes -/

/-- **A smooth cut-off on a ball, with a gradient bound.**  Equal to `1` on
`closedBall c ρ`, supported in `ball c β`, values in `[-1,1]`, and `‖dθ‖ ≤ Mθ` for a
finite `Mθ`.  These are exactly the hypotheses `hθ, hθcs, hθ1, hθle, hts, hMθ` of
`QuantitativeRegularizationBergmanOverlap.bergmanSup_le_of_pointExtension`. -/
theorem exists_cutoff_ball (c : ComplexModel d) {ρ β : ℝ} (hρ : 0 < ρ) (hρβ : ρ < β) :
    ∃ (θ : ComplexModel d → ℝ) (Mθ : ℝ), ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      (∀ z ∈ closedBall c ρ, θ z = 1) ∧ (∀ z, |θ z| ≤ 1) ∧
      tsupport θ ⊆ ball c β ∧ ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ := by
  have hmid : ρ < (ρ + β) / 2 := by linarith
  let f : ContDiffBump c := ⟨ρ, (ρ + β) / 2, hρ, hmid⟩
  have htsupp : tsupport (f : ComplexModel d → ℝ) = closedBall c ((ρ + β) / 2) :=
    f.tsupport_eq
  have hcs : HasCompactSupport (f : ComplexModel d → ℝ) := by
    rw [HasCompactSupport, htsupp]
    exact isCompact_closedBall _ _
  have hcd : ContDiff ℝ ∞ (f : ComplexModel d → ℝ) := f.contDiff
  obtain ⟨M, hM⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous
    (hcd.continuous_fderiv (by simp))
  refine ⟨f, M, hcd, hcs, fun z hz => f.one_of_mem_closedBall hz, fun z => ?_, ?_, hM⟩
  · exact abs_le.mpr ⟨le_trans (by norm_num) f.nonneg, f.le_one⟩
  · rw [htsupp]
    intro z hz
    have : dist z c ≤ (ρ + β) / 2 := by simpa [mem_closedBall] using hz
    exact mem_ball.mpr (lt_of_le_of_lt this (by linarith))

/-! ### The constant chosen before the weight -/

/-- **One overlap constant for every weight** (Copy-4, `lem:regularization`, Step 2).
For a pair of coordinate balls with compact closure inside `D`, a single `C > 0`,
depending only on the dimension and the radii, controls the Bergman sup-weight of
`ball c β` by that of `ball c' β'` at every point of `ball c (ρ/2) ∩ ball c' β'`,
simultaneously for **every** smooth psh weight `ϕ` bounded below on `D`.

The constant is quantified before the weight; this is the property Copy-4 needs when
it fixes the cover before choosing the background form `ζ`. -/
theorem exists_overlapConst_ball (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    (c c' : ComplexModel d) {ρ β β' : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ < β) (hcD : closedBall c β ⊆ D)
    (hβ' : 0 < β') (hcD' : closedBall c' β' ⊆ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ϕ : ComplexModel d → ℝ), ContDiffOn ℝ ∞ ϕ D →
        (∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) →
        ∀ Bϕ : ℝ, (∀ z ∈ D, -Bϕ ≤ ϕ z) →
        ∀ x, x ∈ ball c (ρ / 2) → x ∈ ball c' β' →
          bergmanSup (ball c β) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
            ENNReal.ofReal C *
              bergmanSup (ball c' β') (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := by
  obtain ⟨θ, Mθ, hθ, hθcs, hθ1, hθle, hts, hMθ⟩ := exists_cutoff_ball c hρ hρβ
  have hr : (0:ℝ) < ρ / 2 := by linarith
  refine ⟨pointExtensionConst d (ρ / 2) Mθ (2 * β') (‖c'‖ + β'),
    pointExtensionConst_pos hr, ?_⟩
  intro ϕ hϕ hϕL Bϕ hBϕ x hxc hxc'
  -- `ϕ` is bounded above on the compact closure of the second ball
  have hK : IsCompact (closedBall c' β') := isCompact_closedBall _ _
  have hKne : (closedBall c' β').Nonempty := ⟨c', mem_closedBall_self hβ'.le⟩
  obtain ⟨z₀, -, hmax⟩ := hK.exists_isMaxOn hKne (hϕ.continuousOn.mono hcD')
  -- the cut-off is `1` on the ball of radius `ρ/2` around `x`
  have hθ1x : ∀ z ∈ ball x (ρ / 2), θ z = 1 := by
    intro z hz
    refine hθ1 z (mem_closedBall.mpr ?_)
    have h1 : dist z x < ρ / 2 := mem_ball.mp hz
    have h2 : dist x c < ρ / 2 := mem_ball.mp hxc
    calc dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ ≤ ρ := by linarith
  exact bergmanSup_le_of_pointExtension hd hDo hDc hDb hϕ hϕL hBϕ x hr hθ hθcs hθ1x
    hθle isOpen_ball hts (hts.trans ((ball_subset_closedBall).trans hcD)) hMθ
    isOpen_ball ball_subset_closedBall hK hcD' hxc'
    (B := ϕ z₀) (fun z hz => hmax (ball_subset_closedBall hz))
    (fun z hz => by
      have h1 : dist z c' < β' := mem_ball.mp hz
      have h2 : dist x c' < β' := mem_ball.mp hxc'
      have : ‖z - x‖ = dist z x := (dist_eq_norm z x).symm
      rw [this]
      calc dist z x ≤ dist z c' + dist c' x := dist_triangle _ _ _
        _ ≤ 2 * β' := by rw [dist_comm c' x]; linarith)
    (fun z hz => by
      have h1 : dist z c' < β' := mem_ball.mp hz
      have : ‖z‖ ≤ ‖c'‖ + ‖z - c'‖ := by
        simpa using norm_le_norm_add_norm_sub' z c'
      rw [← dist_eq_norm] at this
      linarith)

/-- **The two-sided overlap comparison with a single constant** — `eq:reg-overlap` in
the form Copy-4 uses: both directions, with the
constant fixed before the weight. -/
theorem exists_overlapConst_ball_pair (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    (c c' : ComplexModel d) {ρ β ρ' β' : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ < β) (hcD : closedBall c β ⊆ D)
    (hρ' : 0 < ρ') (hρβ' : ρ' < β') (hcD' : closedBall c' β' ⊆ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ϕ : ComplexModel d → ℝ), ContDiffOn ℝ ∞ ϕ D →
        (∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) →
        ∀ Bϕ : ℝ, (∀ z ∈ D, -Bϕ ≤ ϕ z) →
        ∀ x, x ∈ ball c (ρ / 2) → x ∈ ball c' (ρ' / 2) →
          bergmanSup (ball c β) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
              ENNReal.ofReal C *
                bergmanSup (ball c' β') (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ∧
          bergmanSup (ball c' β') (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
              ENNReal.ofReal C *
                bergmanSup (ball c β) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := by
  have hβ : (0:ℝ) < β := lt_trans hρ hρβ
  have hβ'pos : (0:ℝ) < β' := lt_trans hρ' hρβ'
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_overlapConst_ball hd hDo hDc hDb c c' hρ hρβ hcD hβ'pos hcD'
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_overlapConst_ball hd hDo hDc hDb c' c hρ' hρβ' hcD' hβ hcD
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro ϕ hϕ hϕL Bϕ hBϕ x hxc hxc'
  have hxβ : x ∈ ball c β :=
    ball_subset_ball (by linarith) hxc
  have hxβ' : x ∈ ball c' β' :=
    ball_subset_ball (by linarith) hxc'
  refine ⟨(h₁ ϕ hϕ hϕL Bϕ hBϕ x hxc hxβ').trans ?_,
    (h₂ ϕ hϕ hϕL Bϕ hBϕ x hxc' hxβ).trans ?_⟩
  · gcongr
    exact le_max_left _ _
  · gcongr
    exact le_max_right _ _

/-- **The logarithmic normalization.**  Both Bergman logs differ by at most the one
constant `log C`, uniformly in the weight.  Dividing by `m` (with `ϕ = m Ψ`) this is
Copy-4's `|ψ_{j,m} - ψ_{l,m}| ≤ C_B / m`. -/
theorem exists_overlapConst_ball_pair_log (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    (c c' : ComplexModel d) {ρ β ρ' β' : ℝ}
    (hρ : 0 < ρ) (hρβ : ρ < β) (hcD : closedBall c β ⊆ D)
    (hρ' : 0 < ρ') (hρβ' : ρ' < β') (hcD' : closedBall c' β' ⊆ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ϕ : ComplexModel d → ℝ), ContDiffOn ℝ ∞ ϕ D →
        (∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) →
        ∀ Bϕ : ℝ, (∀ z ∈ D, -Bϕ ≤ ϕ z) →
        ∀ x, x ∈ ball c (ρ / 2) → x ∈ ball c' (ρ' / 2) →
          bergmanLog (ball c β) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
              bergmanLog (ball c' β') (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x
                + (Real.log C : EReal) ∧
          bergmanLog (ball c' β') (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
              bergmanLog (ball c β) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x
                + (Real.log C : EReal) := by
  obtain ⟨C, hC, h⟩ :=
    exists_overlapConst_ball_pair hd hDo hDc hDb c c' hρ hρβ hcD hρ' hρβ' hcD'
  refine ⟨C, hC, ?_⟩
  intro ϕ hϕ hϕL Bϕ hBϕ x hxc hxc'
  obtain ⟨hle₁, hle₂⟩ := h ϕ hϕ hϕL Bϕ hBϕ x hxc hxc'
  have key : ∀ {A B : ℝ≥0∞}, A ≤ ENNReal.ofReal C * B →
      ENNReal.log A ≤ ENNReal.log B + (Real.log C : EReal) := by
    intro A B hAB
    calc ENNReal.log A ≤ ENNReal.log (ENNReal.ofReal C * B) := ENNReal.log_monotone hAB
      _ = (Real.log C : EReal) + ENNReal.log B := by
          rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC]
      _ = ENNReal.log B + (Real.log C : EReal) := add_comm _ _
  exact ⟨key hle₁, key hle₂⟩


/-! ### A finite cover, one constant -/

/-- **The cover fixed before the weight** (Copy-4, `lem:regularization`, Step 2).
Given a *finite* family of coordinate balls `ball (c i) (β i)`, each with compact
closure in `D` and each carrying its inner radius `ρ i`, there is ONE constant
`C > 0`, depending only on the dimension and the family, such that for **every**
smooth psh weight `ϕ` bounded below on `D`, every pair of indices and every point in
the intersection of the two inner half-balls, the two Bergman sup-weights are
comparable with that constant.

This is Copy-4's `C_B`: chosen from the cover alone, before `ζ` and before `φ`.
Taking `i = j` is harmless, and the statement is symmetric in `i, j` by construction. -/
theorem exists_overlapConst_finite (hd : 0 < d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D)
    {ι : Type*} [Finite ι] (c : ι → ComplexModel d) (ρ β : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hρβ : ∀ i, ρ i < β i)
    (hcD : ∀ i, closedBall (c i) (β i) ⊆ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ϕ : ComplexModel d → ℝ), ContDiffOn ℝ ∞ ϕ D →
        (∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) →
        ∀ Bϕ : ℝ, (∀ z ∈ D, -Bϕ ≤ ϕ z) →
        ∀ (i j : ι) (x : ComplexModel d), x ∈ ball (c i) (ρ i / 2) →
          x ∈ ball (c j) (ρ j / 2) →
          bergmanSup (ball (c i) (β i)) (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
            ENNReal.ofReal C *
              bergmanSup (ball (c j) (β j))
                (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := by
  classical
  -- one constant per ordered pair
  have hpair : ∀ p : ι × ι, ∃ C : ℝ, 0 < C ∧
      ∀ (ϕ : ComplexModel d → ℝ), ContDiffOn ℝ ∞ ϕ D →
        (∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) →
        ∀ Bϕ : ℝ, (∀ z ∈ D, -Bϕ ≤ ϕ z) →
        ∀ x : ComplexModel d, x ∈ ball (c p.1) (ρ p.1 / 2) →
          x ∈ ball (c p.2) (β p.2) →
          bergmanSup (ball (c p.1) (β p.1))
              (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x ≤
            ENNReal.ofReal C *
              bergmanSup (ball (c p.2) (β p.2))
                (fun z => ENNReal.ofReal (Real.exp (-ϕ z))) x := fun p =>
    exists_overlapConst_ball hd hDo hDc hDb (c p.1) (c p.2) (hρ p.1) (hρβ p.1)
      (hcD p.1) (lt_trans (hρ p.2) (hρβ p.2)) (hcD p.2)
  choose Cp hCp hCple using hpair
  -- a finite family of reals is bounded above
  obtain ⟨M, hM⟩ := (Set.finite_range Cp).bddAbove
  refine ⟨max 1 M, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro ϕ hϕ hϕL Bϕ hBϕ i j x hxi hxj
  have hxjβ : x ∈ ball (c j) (β j) :=
    ball_subset_ball (by have := hρβ j; have := hρ j; linarith) hxj
  refine (hCple (i, j) ϕ hϕ hϕL Bϕ hBϕ x hxi hxjβ).trans ?_
  gcongr
  exact le_trans (hM (Set.mem_range_self (i, j))) (le_max_right _ _)

end

end Hironaka.BergmanOverlapFixedCover
