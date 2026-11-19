import Hironaka.Analytic.LocalDDbar
import Hironaka.Analytic.LocalPotentialIndependence

set_option autoImplicit false

/-!
# Local potentials on a ball of prescribed radius

The local solvability results of `Pending/DolbeaultLemma.lean` and
`Pending/LocalDDbar.lean` produce a primitive on *some* neighbourhood `W` of a
point, obtained from the compactness/openness bookkeeping of the proof.  That is
enough for a single point, but not for Demailly's regularization theorem, where
a compact Kähler manifold is covered by finitely many coordinate balls whose
radii must be fixed **before** the form `ζ` to be resolved is chosen: otherwise
the resulting constants depend on `ζ` and the regularization estimate is
circular.

This file re-runs the same proofs keeping track of the radius.  The shrinkage in
the Dolbeault induction is uniform in the form — each of the `n` elimination
steps replaces a coordinate polydisc of radius `s` by one of radius `s / 3` —
so the output radius is an explicit function of `n` and of the input radius
alone:

* `dolbeaultRadius n r = r / ((n + 1) * 3 ^ n)`;
* `ddcRadius n r = dolbeaultRadius n (r / 2) = r / (2 * (n + 1) * 3 ^ n)`.

Main results:

* `exists_dbar_primitive_polydisc` — the `∂̄`-primitive on a coordinate polydisc
  shrunk by the explicit factor `3 ^ n`;
* `exists_dbar_primitive_ball` — its Euclidean-ball form, with radius
  `dolbeaultRadius n r`;
* `exists_twoForm_primitive_ball` — a globally smooth real one-form primitive of
  a closed two-form on the concentric ball of half the radius (the radial
  homotopy of the cut-off form, which is available on all of a star-shaped ball);
* `exists_smooth_ddc_potential_ball` — a globally smooth `ddᶜ`-potential of a
  smooth closed real `(1,1)`-form on `ball x₀ (ddcRadius n r)`;
* `hasFDerivAt_radialOnePotential` — the Poincaré lemma in degree one: a closed
  real one-form on a ball has a primitive on the *whole* ball;
* `exists_holomorphic_re_eq_ball` — a pluriharmonic function on `ball x₀ r` is the
  real part of a holomorphic function on `ball x₀ (r / 2)`.

The pluriharmonic conjugate is *not* obtained from the Dolbeault lemma: `∂̄∂̄u = 0`
holds for every `u`, so solving `∂̄f = ∂̄u` gives an `f` which is only determined
up to a holomorphic summand and carries no information.  Pluriharmonicity enters
instead as closedness of the real one-form `dᶜu`, whose primitive `ψ` makes
`u + iψ` satisfy the Cauchy–Riemann equations; that is why the degree-one
Poincaré lemma is proved here.

Working with coordinate polydiscs rather than balls is what keeps the
bookkeeping light: the polydisc of radius `s` is exactly the domain produced by
the cutoff step, so the induction closes on its own shape, and the two
comparisons `ball x₀ s ⊆ polydisc x₀ s` and `polydisc x₀ s ⊆ ball x₀ r`
(for `n * s < r`) are applied only once, at the very end.
-/

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace Hironaka.PrescribedBall

open CauchyGreen LocalPotentials

noncomputable section

variable {n : ℕ}

/-! ### Coordinate polydiscs -/

/-- The open coordinate polydisc of radius `s` centred at `x₀`: every coordinate
is within `s` of the corresponding coordinate of the centre. -/
def polydisc (x₀ : ComplexModel n) (s : ℝ) : Set (ComplexModel n) :=
  {z | ∀ k, ‖z k - x₀ k‖ < s}

theorem mem_polydisc_iff {x₀ z : ComplexModel n} {s : ℝ} :
    z ∈ polydisc x₀ s ↔ ∀ k, ‖z k - x₀ k‖ < s := Iff.rfl

theorem coord_lt_of_mem_polydisc {x₀ z : ComplexModel n} {s : ℝ}
    (hz : z ∈ polydisc x₀ s) (k : Fin n) : ‖z k - x₀ k‖ < s := hz k

theorem isOpen_polydisc (x₀ : ComplexModel n) (s : ℝ) : IsOpen (polydisc x₀ s) := by
  simp only [polydisc, ofPred_forall]
  exact isOpen_iInter_of_finite fun k ↦ isOpen_lt
    (continuous_norm.comp ((EuclideanSpace.proj k :
      ComplexModel n →L[ℂ] ℂ).continuous.sub continuous_const)) continuous_const

theorem polydisc_mono {x₀ : ComplexModel n} {s t : ℝ} (h : s ≤ t) :
    polydisc x₀ s ⊆ polydisc x₀ t := fun _ hz k ↦ lt_of_lt_of_le (hz k) h

theorem mem_polydisc_self {x₀ : ComplexModel n} {s : ℝ} (hs : 0 < s) :
    x₀ ∈ polydisc x₀ s := fun _ ↦ by simpa using hs

/-- A Euclidean ball is contained in the coordinate polydisc of the same radius. -/
theorem ball_subset_polydisc (x₀ : ComplexModel n) (s : ℝ) :
    ball x₀ s ⊆ polydisc x₀ s := by
  intro z hz k
  rw [mem_ball, dist_eq_norm] at hz
  calc ‖z k - x₀ k‖ = ‖(z - x₀) k‖ := by simp
    _ ≤ ‖z - x₀‖ := PiLp.norm_apply_le _ _
    _ < s := hz

/-- A coordinate polydisc of radius `s` sits inside any Euclidean ball of radius
larger than `n * s`. -/
theorem polydisc_subset_ball {x₀ : ComplexModel n} {s r : ℝ} (hs : 0 ≤ s)
    (h : (n : ℝ) * s < r) : polydisc x₀ s ⊆ ball x₀ r := by
  intro z hz
  rw [mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (norm_sub_le_of_coord_le x₀ hs fun k ↦ (hz k).le) h

/-! ### The quantitative Dolbeault lemma -/

/-- Inductive form of the Dolbeault lemma with an explicit radius: if the
coefficients with index at least `k` vanish on the polydisc of radius `s`, then a
smooth `∂̄`-primitive exists on the polydisc of radius `s / 3 ^ k`.  Each
elimination step costs exactly one factor of `3`, independently of the form. -/
theorem exists_dbar_primitive_polydisc_aux (k : ℕ) :
    ∀ (x₀ : ComplexModel n) (s : ℝ), 0 < s → ∀ a : Fin n → ComplexModel n → ℂ,
      (∀ i, ContDiffOn ℝ ∞ (a i) (polydisc x₀ s)) → IsDbarClosedOn a (polydisc x₀ s) →
      (∀ i : Fin n, k ≤ i.val → ∀ x ∈ polydisc x₀ s, a i x = 0) →
      ∃ f : ComplexModel n → ℂ, ContDiff ℝ ∞ f ∧
        ∀ i, ∀ x ∈ polydisc x₀ (s / 3 ^ k), dbarDir (basisVec i) f x = a i x := by
  induction k with
  | zero =>
    intro x₀ s _ a _ _ hzero
    refine ⟨fun _ ↦ 0, contDiff_const, fun i x hx ↦ ?_⟩
    rw [dbarDir_const, hzero i (Nat.zero_le _) x (by simpa using hx)]
  | succ k ih =>
    intro x₀ s hs a ha hclosed hzero
    have hshrink : s / 3 ^ (k + 1) ≤ s / 3 ^ k := by
      apply div_le_div_of_nonneg_left hs.le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
    by_cases hk : k < n
    swap
    · obtain ⟨f, hf, hfeq⟩ := ih x₀ s hs a ha hclosed fun i hi ↦ absurd i.isLt (by omega)
      exact ⟨f, hf, fun i x hx ↦ hfeq i x (polydisc_mono hshrink hx)⟩
    let j : Fin n := ⟨k, hk⟩
    set U : Set (ComplexModel n) := polydisc x₀ s with hU_def
    have hU : IsOpen U := isOpen_polydisc x₀ s
    set r : ℝ := s / 3 with hr_def
    have hr : 0 < r := by rw [hr_def]; positivity
    set χ := polydiscCutoff x₀ hr with hχ_def
    set V : Set (ComplexModel n) := polydisc x₀ r with hV_def
    have hVU : V ⊆ U := polydisc_mono (by rw [hr_def]; linarith)
    have hpoly : ∀ z : ComplexModel n, (∀ k, ‖z k - x₀ k‖ ≤ 2 * r) → z ∈ U := by
      intro z hz k
      have h := hz k
      rw [hr_def] at h
      linarith
    have hsuppU : tsupport χ ⊆ U := fun z hz ↦
      hpoly z (tsupport_polydiscCutoff_subset x₀ hr hz)
    set b : ComplexModel n → ℂ := fun z ↦ χ z • a j z with hb_def
    have hb : ContDiff ℝ ∞ b := LocalPotentials.contDiff_smul_of_tsupport_subset hU
      (contDiff_polydiscCutoff x₀ hr) hsuppU (ha j)
    have hbc : HasCompactSupport b := (hasCompactSupport_polydiscCutoff x₀ hr).smul_right
    have hej : basisVec j ≠ (0 : ComplexModel n) := by simp [basisVec]
    set g := cauchyGreen (basisVec j) b with hg_def
    have hg : ContDiff ℝ ∞ g := contDiff_cauchyGreen hb hbc hej
    have hdg (i : Fin n) : ContDiff ℝ ∞ (dbarDir (basisVec i) g) := by
      have hD := hg.fderiv_right (m := ∞) (by simp)
      show ContDiff ℝ ∞ (fun x ↦ (fderiv ℝ g x (basisVec i) +
        I * fderiv ℝ g x (I • basisVec i)) / 2)
      exact ((hD.clm_apply contDiff_const).add
        (contDiff_const.mul (hD.clm_apply contDiff_const))).div_const _
    set a' : Fin n → ComplexModel n → ℂ :=
      fun i z ↦ a i z - dbarDir (basisVec i) g z with ha'_def
    have hadiff (i : Fin n) {x : ComplexModel n} (hx : x ∈ U) :
        DifferentiableAt ℝ (a i) x :=
      ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have ha' : ∀ i, ContDiffOn ℝ ∞ (a' i) V := fun i ↦
      ((ha i).mono hVU).sub (hdg i).contDiffOn
    have hclosed' : IsDbarClosedOn a' V := by
      intro i l x hx
      simp only [ha'_def]
      rw [dbarDir_sub (hadiff l (hVU hx)) ((hdg l).differentiable (by simp) x),
        dbarDir_sub (hadiff i (hVU hx)) ((hdg i).differentiable (by simp) x),
        hclosed i l x (hVU hx), dbarDir_dbarDir_comm (hg.contDiffAt.of_le (by norm_cast))]
    have hzero' : ∀ i : Fin n, k ≤ i.val → ∀ x ∈ V, a' i x = 0 := by
      intro i hi x hx
      simp only [ha'_def]
      rcases hi.eq_or_lt with hij | hij
      · have hij' : i = j := Fin.ext hij.symm
        subst hij'
        rw [show dbarDir (basisVec j) g x = b x from
          dbarDir_cauchyGreen (hb.of_le (by simp)) hbc hej x]
        simp only [hb_def, hχ_def,
          polydiscCutoff_eq_one x₀ hr (fun k ↦ (coord_lt_of_mem_polydisc hx k).le),
          one_smul, sub_self]
      · rw [hzero i hij x (hVU hx), dbarDir_cauchyGreen_comm (hb.of_le (by simp)) hbc hej]
        have hne : i ≠ j := fun h ↦ by
          rw [h] at hij
          exact lt_irrefl _ hij
        have hvanish : ∀ w : ℂ, dbarDir (basisVec i) b (x - w • basisVec j) = 0 := by
          intro w
          set y := x - w • basisVec j with hy_def
          have hyi : y i = x i := by simp [hy_def, basisVec, hne]
          by_cases hy : y ∈ tsupport χ
          · have hyU := hsuppU hy
            have hbeq : b = fun z ↦ (χ z : ℂ) * a j z := funext fun z ↦ Complex.real_smul
            rw [hbeq, dbarDir_ofReal_mul ((contDiff_polydiscCutoff x₀ hr).differentiable
              (by simp) y) (hadiff j hyU)]
            rw [dbarDir_polydiscCutoff_eq_zero x₀ hr
                (by rw [hyi]; exact coord_lt_of_mem_polydisc hx i),
              hclosed i j y hyU]
            have hev : a i =ᶠ[𝓝 y] fun _ ↦ 0 := by
              filter_upwards [hU.mem_nhds hyU] with z hz
              exact hzero i hij z hz
            rw [dbarDir_congr hev, dbarDir_const]
            ring
          · have hev : b =ᶠ[𝓝 y] fun _ ↦ 0 := by
              filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
              simp [hb_def, image_eq_zero_of_notMem_tsupport hz]
            rw [dbarDir_congr hev, dbarDir_const]
        simp [cauchyGreen, hvanish]
    obtain ⟨f', hf', hf'eq⟩ := ih x₀ r hr a' ha' hclosed' hzero'
    have hrad : s / 3 ^ (k + 1) = r / 3 ^ k := by
      rw [hr_def, pow_succ]
      ring
    refine ⟨fun z ↦ f' z + g z, hf'.add hg, fun i x hx ↦ ?_⟩
    rw [hrad] at hx
    rw [dbarDir_add (hf'.differentiable (by simp) x) (hg.differentiable (by simp) x),
      hf'eq i x hx]
    simp [ha'_def]

/-- **Dolbeault lemma on a prescribed polydisc.**  A smooth `∂̄`-closed
`(0,1)`-form on the coordinate polydisc of radius `s` has a smooth
`∂̄`-primitive on the concentric polydisc of radius `s / 3 ^ n`. -/
theorem exists_dbar_primitive_polydisc {x₀ : ComplexModel n} {s : ℝ} (hs : 0 < s)
    (a : Fin n → ComplexModel n → ℂ) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (polydisc x₀ s))
    (hclosed : IsDbarClosedOn a (polydisc x₀ s)) :
    ∃ f : ComplexModel n → ℂ, ContDiff ℝ ∞ f ∧
      ∀ i, ∀ x ∈ polydisc x₀ (s / 3 ^ n), dbarDir (basisVec i) f x = a i x :=
  exists_dbar_primitive_polydisc_aux n x₀ s hs a ha hclosed fun i hi ↦ absurd i.isLt (by omega)

/-- The explicit radius on which the Dolbeault primitive of a form given on
`ball x₀ r` is produced.  It depends only on the dimension and on `r`. -/
def dolbeaultRadius (n : ℕ) (r : ℝ) : ℝ := r / ((n + 1) * 3 ^ n)

theorem dolbeaultRadius_pos {r : ℝ} (hr : 0 < r) : 0 < dolbeaultRadius n r := by
  rw [dolbeaultRadius]; positivity

theorem dolbeaultRadius_le {r : ℝ} (hr : 0 ≤ r) : dolbeaultRadius n r ≤ r := by
  rw [dolbeaultRadius, div_le_iff₀ (by positivity)]
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * 3 ^ n := by nlinarith
  linarith [mul_le_mul_of_nonneg_left h1 hr]

/-- **Quantitative local Dolbeault lemma.**  A smooth `∂̄`-closed `(0,1)`-form on
`ball x₀ r` has a globally smooth `∂̄`-primitive on `ball x₀ (dolbeaultRadius n r)`,
a ball whose radius is an explicit function of `n` and `r` only — in particular
it does not depend on the form. -/
theorem exists_dbar_primitive_ball {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (a : Fin n → ComplexModel n → ℂ) (ha : ∀ i, ContDiffOn ℝ ∞ (a i) (ball x₀ r))
    (hclosed : IsDbarClosedOn a (ball x₀ r)) :
    ∃ f : ComplexModel n → ℂ, ContDiff ℝ ∞ f ∧
      ∀ i, ∀ x ∈ ball x₀ (dolbeaultRadius n r), dbarDir (basisVec i) f x = a i x := by
  set s : ℝ := r / (n + 1) with hs_def
  have hs : 0 < s := by rw [hs_def]; positivity
  have hsub : polydisc x₀ s ⊆ ball x₀ r := by
    refine polydisc_subset_ball hs.le ?_
    rw [hs_def]
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [show (n : ℝ) * (r / (n + 1)) = r * (n / (n + 1)) by field_simp]
    have : (n : ℝ) / (n + 1) < 1 := by
      rw [div_lt_one hn]; linarith
    nlinarith
  obtain ⟨f, hf, hfeq⟩ := exists_dbar_primitive_polydisc hs a
    (fun i ↦ (ha i).mono hsub) (fun i l x hx ↦ hclosed i l x (hsub hx))
  refine ⟨f, hf, fun i x hx ↦ hfeq i x (ball_subset_polydisc x₀ _ ?_)⟩
  rw [show s / 3 ^ n = dolbeaultRadius n r by rw [hs_def, dolbeaultRadius, div_div]]
  exact hx

/-! ### A one-form primitive on a ball of prescribed radius -/

/-- **Poincaré lemma for two-forms with a prescribed radius.**  A smooth closed
two-form on `ball x₀ r` has a globally smooth one-form primitive on the
concentric ball of radius `r / 2`.  The form is cut off by a bump equal to one on
`closedBall x₀ (r / 2)` and supported in `closedBall x₀ (3 * r / 4)`; the radial
homotopy primitive of the cut-off form works on the whole star-shaped ball
`ball x₀ (r / 2)`, so no further shrinking is needed. -/
theorem exists_twoForm_primitive_ball [Nontrivial (ComplexModel n)]
    {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a (ball x₀ r)) (hclosed : ∀ y ∈ ball x₀ r, extDeriv a y = 0) :
    ∃ S : ComplexModel n → (ComplexModel n) [⋀^Fin 1]→L[ℝ] ℝ,
      ContDiff ℝ ∞ S ∧ ∀ x ∈ ball x₀ (r / 2), extDeriv S x = a x := by
  let χ : ContDiffBump x₀ := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  set b : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ := fun y ↦ χ y • a y with hb_def
  have hsupp : tsupport χ ⊆ ball x₀ r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by simp only [χ]; linarith)
  have hb : ContDiff ℝ ∞ b :=
    LocalPotentials.contDiff_smul_of_tsupport_subset isOpen_ball χ.contDiff hsupp ha
  have heq : EqOn b a (ball x₀ (r / 2)) := fun y hy ↦ by
    simp [hb_def, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hsmall : ball x₀ (r / 2) ⊆ ball x₀ r := ball_subset_ball (by linarith)
  refine ⟨radialTwoFormPrimitive b x₀, contDiff_radialTwoFormPrimitive b x₀ hb, fun x hx ↦ ?_⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ ball x₀ (r / 2) := fun t ht ↦
    (convex_ball x₀ (r / 2)).add_smul_sub_mem (mem_ball_self (by positivity)) hx ht
  rw [extDeriv_radialTwoFormPrimitive_of_closed_segment b x₀ x hb fun t ht ↦ ?_]
  · exact heq hx
  · have hev : b =ᶠ[𝓝 (x₀ + t • (x - x₀))] a :=
      eventually_of_mem (isOpen_ball.mem_nhds (hseg t ht)) heq
    rw [hev.extDeriv_eq]
    exact hclosed _ (hsmall (hseg t ht))

/-! ### The `ddᶜ` lemma on a ball of prescribed radius -/

/-- The explicit radius on which a `ddᶜ`-potential of a form given on
`ball x₀ r` is produced.  It depends only on the dimension and on `r`. -/
def ddcRadius (n : ℕ) (r : ℝ) : ℝ := dolbeaultRadius n (r / 2)

theorem ddcRadius_eq (n : ℕ) (r : ℝ) : ddcRadius n r = r / (2 * ((n + 1) * 3 ^ n)) := by
  rw [ddcRadius, dolbeaultRadius, div_div]

theorem ddcRadius_pos {r : ℝ} (hr : 0 < r) : 0 < ddcRadius n r :=
  dolbeaultRadius_pos (by positivity)

theorem ddcRadius_le_half {r : ℝ} (hr : 0 ≤ r) : ddcRadius n r ≤ r / 2 :=
  dolbeaultRadius_le (by positivity)

/-- **Quantitative local `ddᶜ` lemma.**  A smooth closed real `(1,1)`-form on
`ball x₀ r` has a globally smooth potential for the normalized `ddᶜ` on
`ball x₀ (ddcRadius n r)`, a ball whose radius is an explicit function of `n` and
`r` only.  This is the prescribed-radius form of
`LocalPotentials.exists_smooth_local_ddc_potential_of_ne_zero`, needed so that a
finite cover of a compact Kähler manifold by such balls can be chosen before the
form to be resolved. -/
theorem exists_smooth_ddc_potential_ball (hn : n ≠ 0)
    {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a (ball x₀ r)) (hclosed : ∀ z ∈ ball x₀ r, extDeriv a z = 0)
    (h11 : ∀ z ∈ ball x₀ r, IsOneOne (a z)) :
    ∃ ρ : ComplexModel n → ℝ, ContDiff ℝ ∞ ρ ∧
      EqOn (smoothDDC ρ) a (ball x₀ (ddcRadius n r)) := by
  have : Nontrivial (ComplexModel n) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    infer_instance
  obtain ⟨S, hS, hSa⟩ := exists_twoForm_primitive_ball hr a ha hclosed
  have hhalf : (0 : ℝ) < r / 2 := by positivity
  have hWsub : ball x₀ (ddcRadius n r) ⊆ ball x₀ (r / 2) :=
    ball_subset_ball (ddcRadius_le_half hr.le)
  have hSd : Differentiable ℝ S := hS.differentiable (by simp)
  set β : Fin n → ComplexModel n → ℂ := fun i y ↦ zeroOnePart (S y) (basisVec i) with hβ_def
  have hβ (i : Fin n) : ContDiff ℝ ∞ (β i) := by
    have h := (zeroOnePartCLM (basisVec i)).contDiff.comp hS
    simpa [hβ_def, Function.comp_def, zeroOnePartCLM_apply] using h
  have hβclosed : IsDbarClosedOn β (ball x₀ (r / 2)) := by
    intro i l x hx
    refine dbarDir_zeroOnePart_comm (hSd x) ?_ _ _
    rw [hSa x hx]
    exact h11 x (ball_subset_ball (by linarith) hx)
  obtain ⟨f, hf, hfβ⟩ :=
    exists_dbar_primitive_ball hhalf β (fun i ↦ (hβ i).contDiffOn) hβclosed
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  set u : ComplexModel n → ℝ := fun y ↦ (f y).re with hu
  set w : ComplexModel n → ℝ := fun y ↦ (f y).im with hw
  have hudiff : ContDiff ℝ ∞ u := reCLM.contDiff.comp hf
  have hwdiff : ContDiff ℝ ∞ w := imCLM.contDiff.comp hf
  -- Real parts of `∂̄ f = S^{0,1}`: `S = du - dw ∘ J` on the small ball.
  have hre : ∀ y ∈ ball x₀ (ddcRadius n r), ∀ v,
      S y ![v] = fderiv ℝ u y v - fderiv ℝ w y (I • v) := by
    intro y hy v
    have h := congrArg Complex.re (dbarDir_eq_zeroOnePart (fun i ↦ hfβ i y hy) v)
    rw [zeroOnePart_re] at h
    have hu' : fderiv ℝ u y = reCLM.comp (fderiv ℝ f y) :=
      (reCLM.hasFDerivAt.comp y (hfd y).hasFDerivAt).fderiv
    have hw' : fderiv ℝ w y = imCLM.comp (fderiv ℝ f y) :=
      (imCLM.hasFDerivAt.comp y (hfd y).hasFDerivAt).fderiv
    rw [hu', hw']
    simp [dbarDir] at h
    simp
    linarith
  set ω₀ : ComplexModel n → (ComplexModel n) [⋀^Fin 0]→L[ℝ] ℝ := fun y ↦
    ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0) (u y) with hω₀_def
  have hω₀ : ContDiff ℝ ∞ ω₀ :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (ComplexModel n) ℝ (Fin 0)).contDiff.comp
      hudiff
  set R := extDeriv ω₀ with hR_def
  have hR : ContDiff ℝ ∞ R := by
    have h :=
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).contDiff.comp
        (hω₀.fderiv_right (m := ∞) le_rfl)
    convert h using 1
    funext y
    simp [hR_def, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  have hRapply (y v : ComplexModel n) : R y ![v] = fderiv ℝ u y v := by
    simp [hR_def, hω₀_def, extDeriv_constOfIsEmpty]
  refine ⟨fun y ↦ 4 * Real.pi * w y, contDiff_const.mul hwdiff, fun x hx ↦ ?_⟩
  have hdc :
      smoothDc (fun y ↦ 4 * Real.pi * w y) =ᶠ[𝓝 x] fun y ↦ S y + (-1 : ℝ) • R y := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    have hρ : fderiv ℝ (fun y ↦ 4 * Real.pi * w y) y = (4 * Real.pi) • fderiv ℝ w y :=
      fderiv_const_mul (hwdiff.differentiable (by simp) y) _
    rw [smoothDc_apply, hρ]
    rw [hv]
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      hRapply, hre y hy]
    simp
    field_simp [Real.pi_ne_zero]
    ring
  change extDeriv (smoothDc _) x = a x
  have hRd : DifferentiableAt ℝ (fun y ↦ (-1 : ℝ) • R y) x :=
    ((hR.differentiable (by simp) x).const_smul (-1 : ℝ) :)
  rw [hdc.extDeriv_eq, extDeriv_fun_add (hSd x) hRd]
  change extDeriv S x + extDeriv ((-1 : ℝ) • R) x = a x
  rw [extDeriv_smul, extDeriv_extDeriv_apply hω₀.contDiffAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top),
    hSa x (hWsub hx)]
  simp

/-! ### The Poincaré lemma in degree one -/

/-- Differentiating a field of linear functionals commutes with evaluation at a
fixed vector. -/
theorem fderiv_clm_eval {F : ComplexModel n → (ComplexModel n →L[ℝ] ℝ)}
    (hF : Differentiable ℝ F) (y a b : ComplexModel n) :
    fderiv ℝ (fun z ↦ F z b) y a = fderiv ℝ F y a b := by
  rw [fderiv_clm_apply (hF y) (differentiableAt_const b)]
  simp

/-- The radial primitive of a real one-form `τ`, written as a field of linear
functionals: `ψ(x) = ∫₀¹ τ(x₀ + t(x - x₀))(x - x₀) dt`. -/
def radialOnePotential (τ : ComplexModel n → (ComplexModel n →L[ℝ] ℝ))
    (x₀ : ComplexModel n) : ComplexModel n → ℝ :=
  fun x ↦ ∫ t in (0 : ℝ)..1, τ (x₀ + t • (x - x₀)) (x - x₀)

theorem contDiff_radialOnePotential {τ : ComplexModel n → (ComplexModel n →L[ℝ] ℝ)}
    (hτ : ContDiff ℝ ∞ τ) (x₀ : ComplexModel n) :
    ContDiff ℝ ∞ (radialOnePotential τ x₀) :=
  contDiff_intervalIntegral_of_contDiff
    (G := fun x t ↦ τ (x₀ + t • (x - x₀)) (x - x₀))
    ((hτ.comp (by fun_prop)).clm_apply (by fun_prop)) 0 1

set_option maxHeartbeats 1000000 in
/-- **Poincaré lemma in degree one.**  If `τ` is a smooth field of linear
functionals whose derivative is symmetric along the segment from `x₀` to `x` —
the coordinate form of `dτ = 0` — then its radial primitive has derivative
`τ x` at `x`.  No shrinking of the domain occurs: the conclusion holds at every
point whose segment to the centre carries the closedness hypothesis. -/
theorem hasFDerivAt_radialOnePotential {τ : ComplexModel n → (ComplexModel n →L[ℝ] ℝ)}
    (hτ : ContDiff ℝ ∞ τ) (x₀ x : ComplexModel n)
    (hsymm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p q : ComplexModel n,
      fderiv ℝ τ (x₀ + t • (x - x₀)) p q = fderiv ℝ τ (x₀ + t • (x - x₀)) q p) :
    HasFDerivAt (radialOnePotential τ x₀) (τ x) x := by
  have hτd : Differentiable ℝ τ := hτ.differentiable (by simp)
  have hDτ : ContDiff ℝ ∞ (fderiv ℝ τ) := hτ.fderiv_right (m := ∞) (by simp)
  have hpt : ContDiff ℝ ∞ (fun p : ComplexModel n × ℝ ↦ x₀ + p.2 • (p.1 - x₀)) := by fun_prop
  set G : ComplexModel n → ℝ → ℝ :=
    fun z t ↦ τ (x₀ + t • (z - x₀)) (z - x₀) with hG_def
  set G' : ComplexModel n → ℝ → (ComplexModel n →L[ℝ] ℝ) := fun z t ↦
    (ContinuousLinearMap.apply ℝ ℝ (z - x₀)).comp
        (t • fderiv ℝ τ (x₀ + t • (z - x₀))) + τ (x₀ + t • (z - x₀)) with hG'_def
  have hsub : ContDiff ℝ ∞ (fun p : ComplexModel n × ℝ ↦ p.1 - x₀) := by fun_prop
  have hGcd : ContDiff ℝ ∞ (Function.uncurry G) := (hτ.comp hpt).clm_apply hsub
  have hGc : Continuous (Function.uncurry G) := hGcd.continuous
  have hG'cd : ContDiff ℝ ∞ (Function.uncurry G') :=
      by
    show ContDiff ℝ ∞ fun p : ComplexModel n × ℝ ↦
      (ContinuousLinearMap.apply ℝ ℝ (p.1 - x₀)).comp
          (p.2 • fderiv ℝ τ (x₀ + p.2 • (p.1 - x₀))) + τ (x₀ + p.2 • (p.1 - x₀))
    refine ContDiff.add (ContDiff.clm_comp ?_ ?_) (hτ.comp hpt)
    · have happ : ContDiff ℝ ∞ (fun w : ComplexModel n ↦
          ContinuousLinearMap.apply ℝ ℝ (E := ComplexModel n) w) := by
        have hlin : ContDiff ℝ ∞
            ⇑(ContinuousLinearMap.apply ℝ ℝ (E := ComplexModel n)) :=
          ContinuousLinearMap.contDiff _
        exact hlin
      exact happ.comp hsub
    · exact contDiff_snd.smul (hDτ.comp hpt)
  have hG'c : Continuous (Function.uncurry G') := hG'cd.continuous
  have hderiv : ∀ z t, HasFDerivAt (fun q ↦ G q t) (G' z t) z := by
    intro z t
    have hy : HasFDerivAt (fun q : ComplexModel n ↦ x₀ + t • (q - x₀))
        (t • ContinuousLinearMap.id ℝ (ComplexModel n)) z := by
      simpa using (((hasFDerivAt_id z).sub_const x₀).const_smul t).const_add x₀
    have hc := (hτd (x₀ + t • (z - x₀))).hasFDerivAt.comp z hy
    have hq : HasFDerivAt (fun q : ComplexModel n ↦ q - x₀)
        (ContinuousLinearMap.id ℝ (ComplexModel n)) z := (hasFDerivAt_id z).sub_const x₀
    have heq : (τ (x₀ + t • (z - x₀))).comp (ContinuousLinearMap.id ℝ (ComplexModel n))
        + ((fderiv ℝ τ (x₀ + t • (z - x₀))).comp
            (t • ContinuousLinearMap.id ℝ (ComplexModel n))).flip (z - x₀) = G' z t := by
      ext v
      simp [hG'_def]
      ring
    rw [← heq]
    exact hc.clm_apply hq
  have hcont : Continuous fun t ↦ G' x t :=
    hG'c.comp (continuous_const.prodMk continuous_id)
  have hint : (∫ t in (0 : ℝ)..1, G' x t) = τ x := by
    ext v
    rw [ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable _ _)]
    have hFT : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ s * τ (x₀ + s • (x - x₀)) v) (G' x t v) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hp : HasDerivAt (fun s : ℝ ↦ x₀ + s • (x - x₀)) (x - x₀) t := by
        simpa using ((hasDerivAt_id t).smul_const (x - x₀)).const_add x₀
      have hcomp : HasDerivAt (fun s : ℝ ↦ τ (x₀ + s • (x - x₀)))
          (fderiv ℝ τ (x₀ + t • (x - x₀)) (x - x₀)) t :=
        (hτd (x₀ + t • (x - x₀))).hasFDerivAt.comp_hasDerivAt t hp
      have hτv : HasDerivAt (fun s : ℝ ↦ τ (x₀ + s • (x - x₀)) v)
          (fderiv ℝ τ (x₀ + t • (x - x₀)) (x - x₀) v) t := by
        simpa using hcomp.clm_apply (hasDerivAt_const t v)
      have h2 : HasDerivAt (fun s : ℝ ↦ s * τ (x₀ + s • (x - x₀)) v)
          (1 * τ (x₀ + t • (x - x₀)) v
            + t * fderiv ℝ τ (x₀ + t • (x - x₀)) (x - x₀) v) t :=
        (hasDerivAt_id t).mul hτv
      have hval : G' x t v =
          1 * τ (x₀ + t • (x - x₀)) v
            + t * fderiv ℝ τ (x₀ + t • (x - x₀)) (x - x₀) v := by
        simp only [hG'_def, add_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, smul_apply, ContinuousLinearMap.apply_apply,
          smul_eq_mul, one_mul]
        rw [hsymm t ht v (x - x₀)]
        ring
      rw [hval]
      exact h2
    have hIv : Continuous fun t : ℝ ↦ G' x t v := by
      have := (ContinuousLinearMap.apply ℝ ℝ (E := ComplexModel n) v).continuous.comp hcont
      exact this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFT (hIv.intervalIntegrable _ _)]
    simp
  have hmain := hasFDerivAt_intervalIntegral_of_jointly_continuous hGc hG'c hderiv x 0 1
  rw [hint] at hmain
  exact hmain

/-! ### The pluriharmonic conjugate on a ball of prescribed radius -/

/-- **Pluriharmonic conjugate on a prescribed ball.**  A smooth function `u` on
`ball x₀ r` whose complex Hessian vanishes (`smoothDDC u = 0`) is, on the
concentric ball of half the radius, the real part of a holomorphic function.

The holomorphic function is `g = u + iψ`, where `ψ` is the radial primitive of the
real one-form `dᶜu` (up to the normalizing constant), which is closed precisely
because `ddᶜu = 0`.  Holomorphy is stated as the Cauchy–Riemann equations
`∂̄_v g = 0` in every direction `v`, together with global smoothness; this is the
converse of `PluriharmonicLogNorm.smoothDDC_re_comp_eq_zero`. -/
theorem exists_holomorphic_re_eq_ball {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (u : ComplexModel n → ℝ) (hu : ContDiffOn ℝ ∞ u (ball x₀ r))
    (hph : ∀ z ∈ ball x₀ r, smoothDDC u z = 0) :
    ∃ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g ∧
      (∀ z ∈ ball x₀ (r / 2), ∀ v, dbarDir v g z = 0) ∧
      (∀ z ∈ ball x₀ (r / 2), (g z).re = u z) := by
  have hhalf : ball x₀ (r / 2) ⊆ ball x₀ r := ball_subset_ball (by linarith)
  -- Make `u` globally smooth without changing it on `ball x₀ (r / 2)`.
  let χ : ContDiffBump x₀ := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hsupp : tsupport χ ⊆ ball x₀ r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by simp only [χ]; linarith)
  set v : ComplexModel n → ℝ := fun y ↦ χ y • u y with hv_def
  have hvc : ContDiff ℝ ∞ v :=
    LocalPotentials.contDiff_smul_of_tsupport_subset isOpen_ball χ.contDiff hsupp hu
  have hveq : EqOn v u (ball x₀ (r / 2)) := fun y hy ↦ by
    simp [hv_def, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hDv : ContDiff ℝ ∞ (fderiv ℝ v) := hvc.fderiv_right (m := ∞) (by simp)
  have hDvd : Differentiable ℝ (fderiv ℝ v) := hDv.differentiable (by simp)
  have hddc : ∀ z ∈ ball x₀ (r / 2), smoothDDC v z = 0 := by
    intro z hz
    rw [smoothDDC_congr (g := u)
      (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hveq)]
    exact hph z (hhalf hz)
  -- The one-form `-dv ∘ J`, i.e. `4π dᶜv`.
  set τ : ComplexModel n → (ComplexModel n →L[ℝ] ℝ) :=
    fun y ↦ (-(fderiv ℝ v y)).comp (modelComplexStructure n) with hτ_def
  have hτ : ContDiff ℝ ∞ τ := hDv.neg.clm_comp contDiff_const
  have hτd : Differentiable ℝ τ := hτ.differentiable (by simp)
  have hτapply : ∀ y w : ComplexModel n, τ y w = -fderiv ℝ v y (I • w) := fun y w ↦ by
    simp [hτ_def]
  have hHess : ∀ y a b : ComplexModel n,
      fderiv ℝ τ y a b = -realHessian v y a (I • b) := by
    intro y a b
    rw [← fderiv_clm_eval hτd y a b,
      show (fun z ↦ τ z b) = fun z ↦ -fderiv ℝ v z (I • b) from funext fun z ↦ hτapply z b,
      fderiv_fun_neg]
    simp only [neg_apply]
    rw [fderiv_clm_eval hDvd y a (I • b), realHessian_eq_fderiv]
  have hτsymm : ∀ y ∈ ball x₀ (r / 2), ∀ p q : ComplexModel n,
      fderiv ℝ τ y p q = fderiv ℝ τ y q p := by
    intro y hy p q
    have h2 : ContDiffAt ℝ 2 v y := hvc.contDiffAt.of_le (by norm_cast)
    have h0 : (0 : ℝ) =
        (realHessian v y p (I • q) - realHessian v y q (I • p)) / (4 * Real.pi) := by
      rw [← smoothDDC_apply_eq_realHessian h2 q p, hddc y hy]
      simp
    have hpi : (4 : ℝ) * Real.pi ≠ 0 := by positivity
    have hsym : realHessian v y p (I • q) = realHessian v y q (I • p) := by
      field_simp at h0
      linarith
    rw [hHess, hHess, hsym]
  -- The primitive of `τ`, valid on all of `ball x₀ (r / 2)`.
  have hψd : ∀ x ∈ ball x₀ (r / 2),
      HasFDerivAt (radialOnePotential τ x₀) (τ x) x := by
    intro x hx
    refine hasFDerivAt_radialOnePotential hτ x₀ x fun t ht p q ↦ hτsymm _ ?_ p q
    exact (convex_ball x₀ (r / 2)).add_smul_sub_mem (mem_ball_self (by positivity)) hx ht
  set ψ : ComplexModel n → ℝ := radialOnePotential τ x₀ with hψ_def
  have hψc : ContDiff ℝ ∞ ψ := contDiff_radialOnePotential hτ x₀
  refine ⟨fun z ↦ (v z : ℂ) + I * (ψ z : ℂ),
    (ofRealCLM.contDiff.comp hvc).add (contDiff_const.mul (ofRealCLM.contDiff.comp hψc)),
    fun z hz w ↦ ?_, fun z hz ↦ ?_⟩
  · have hd1 : HasFDerivAt (fun y ↦ ((v y : ℂ))) (ofRealCLM.comp (fderiv ℝ v z)) z :=
      ofRealCLM.hasFDerivAt.comp z (hvc.differentiable (by simp) z).hasFDerivAt
    have hd2 : HasFDerivAt (fun y ↦ ((ψ y : ℂ))) (ofRealCLM.comp (τ z)) z :=
      ofRealCLM.hasFDerivAt.comp z (hψd z hz)
    have hd : HasFDerivAt (fun y ↦ ((v y : ℂ)) + I * (ψ y : ℂ))
        (ofRealCLM.comp (fderiv ℝ v z) + I • (ofRealCLM.comp (τ z))) z :=
      hd1.add (hd2.const_mul I)
    rw [dbarDir, hd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ofRealCLM_apply, smul_eq_mul]
    rw [hτapply z w, hτapply z (I • w)]
    simp only [smul_smul, I_mul_I, neg_one_smul, map_neg, neg_neg, Complex.ofReal_neg]
    ring_nf
    rw [I_sq]
    ring
  · simp [hveq hz]

end

end Hironaka.PrescribedBall
