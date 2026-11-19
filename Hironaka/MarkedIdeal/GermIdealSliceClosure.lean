import Hironaka.Analytic.TorusCoefficients
import Hironaka.Analytic.NilpotentShiftClosure
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

/-!
# Membership in a germ ideal from extensions off nearby slices

This module is the algebraic half of the proof of strong openness for increasing sequences
(`Hironaka.StrongOpennessRegularRoute`).  It replaces the standard bases and Galligo's division
estimate of Hiep's proof (`hiep14-weighted-lct:proof-ii`) by Krull's intersection theorem.

Let `J` be an ideal of holomorphic germs at `p ∈ ℂ^{m+1}` and let `f` be holomorphic on a
polydisc `Δ(p, s')`.  Suppose there are
* nonzero `t_k → 0` with `|t_k| < s/2`, and
* functions `F_k ∈ J` holomorphic on `Δ(p, s')` that agree with `f` on the slice
  `z_last = p_last + t_k`,
* with `|t_k| · |F_k| ≤ δ_k → 0` on the torus of radius `s < s'`.

Then `f ∈ J`, provided Krull's intersection theorem holds for germ ideals
(`GermKrullIntersection`).  These are exactly the data produced by Hiep's Lemma 2.1 through
the Ohsawa--Takegoshi extension from the slice `z_last = p_last + t_k`.

The proof.  Write `F_k - f = (z_last - p_last - t_k) g_k`, where `g_k` is the difference
quotient in the last variable.  It is holomorphic in that variable, and on the torus
`|t_k g_k| ≤ (δ_k + |t_k| sup |f|) / (s/2) → 0`.  Fix `K`.  Taylor coefficients (torus
coefficients, `Hironaka.TorusCoefficients`) in the box `[0, K)^{m+1}` form a
finite-dimensional space.  In it `J` spans a subspace `U`, multiplication by
`z_last - p_last` is a nilpotent operator `T` preserving `U`, and

  `T (t_k a(g_k)) - t_k (t_k a(g_k)) + t_k a(f) = t_k a(F_k) ∈ U`.

The nilpotent-shift lemma `mem_of_nilpotent_shift_relation` gives `a(f) ∈ U`.  So for every
`K` some `h ∈ J` has the same coefficients as `f` below `K`, and Krull's theorem puts `f` in
`J`.
-/

open Set Filter MeasureTheory Complex
open scoped Real Topology

namespace Hironaka

noncomputable section

variable {m : ℕ}

/-- The open polydisc of centre `p` and radius `r` in `ℂ^{m+1}`. -/
def openPolydisc (p : EuclideanSpace ℂ (Fin (m + 1))) (r : ℝ) :
    Set (EuclideanSpace ℂ (Fin (m + 1))) :=
  {z | ∀ i, ‖z i - p i‖ < r}

/-- An ideal of holomorphic germs at `p`, presented as a predicate on functions: it contains
`0`, is closed under sums and under multiplication by functions complex differentiable near `p`,
contains only functions holomorphic near `p`, and depends only on germs at `p`. -/
structure IsHolomorphicGermIdeal (p : EuclideanSpace ℂ (Fin (m + 1)))
    (J : (EuclideanSpace ℂ (Fin (m + 1)) → ℂ) → Prop) : Prop where
  zero_mem : J 0
  add_mem : ∀ {h₁ h₂}, J h₁ → J h₂ → J (h₁ + h₂)
  mul_mem : ∀ {a h : EuclideanSpace ℂ (Fin (m + 1)) → ℂ},
    (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ a z) → J h → J (fun z => a z * h z)
  holomorphic : ∀ {h}, J h → ∃ V, IsOpen V ∧ p ∈ V ∧ DifferentiableOn ℂ h V
  congr : ∀ {h h'}, J h → h' =ᶠ[𝓝 p] h → J h'

/-- **Krull's intersection theorem for ideals of holomorphic germs** at a point of
`ℂ^{m+1}`.  If `f` is holomorphic on a polydisc `Δ(p, s')` and, for every `K`, some
`h ∈ J` holomorphic on `Δ(p, s')` has the same torus coefficients as `f` on the torus of
radius `s < s'` for all multi-indices in `[0, K)^{m+1}`, then `f ∈ J`.

By Cauchy's formula those coefficients are `(2π)^{m+1} s^{|α|}` times the Taylor
coefficients at `p`.  So the hypothesis says `f - h ∈ ((z_i - p_i)^K)_i ⊆ 𝔪^K` for every `K`, and the
conclusion is Krull's theorem `⋂_K (J + 𝔪^K) = J` in the Noetherian local ring
`𝒪_{ℂ^{m+1}, p}` (Rückert's basis theorem).

It is proved as `germKrullIntersection` in `Hironaka.StrongOpennessFromOhsawaTakegoshi`. -/
def GermKrullIntersection (m : ℕ) : Prop :=
  ∀ (p : EuclideanSpace ℂ (Fin (m + 1))) (J : (EuclideanSpace ℂ (Fin (m + 1)) → ℂ) → Prop),
    IsHolomorphicGermIdeal p J → ∀ s s' : ℝ, 0 < s → s < s' →
    ∀ f : EuclideanSpace ℂ (Fin (m + 1)) → ℂ, DifferentiableOn ℂ f (openPolydisc p s') →
    (∀ K : ℕ, ∃ h, J h ∧ DifferentiableOn ℂ h (openPolydisc p s') ∧
      ∀ α : Fin (m + 1) → ℕ, (∀ i, α i < K) →
        torusCoeff p s (fun i => (α i : ℤ)) f = torusCoeff p s (fun i => (α i : ℤ)) h) →
    J f

/-! ### Geometry of the polydisc and the torus -/

theorem isOpen_openPolydisc (p : EuclideanSpace ℂ (Fin (m + 1))) (r : ℝ) :
    IsOpen (openPolydisc p r) := by
  have : openPolydisc p r = ⋂ i, {z : EuclideanSpace ℂ (Fin (m + 1)) | ‖z i - p i‖ < r} := by
    ext z; simp [openPolydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const

theorem torusPoint_mem_openPolydisc {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s < s') (θ : Fin (m + 1) → ℝ) :
    torusPoint p s θ ∈ openPolydisc p s' := fun i => by
  rw [norm_torusPoint_sub p hs]; exact hss'

theorem torusLastLine_mem_openPolydisc {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s < s') (θ' : Fin m → ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < s') :
    torusLastLine p s θ' ζ ∈ openPolydisc p s' := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [torusLastLine] using hζ
  · simpa [torusLastLine, norm_exp_ofReal_mul_I, abs_of_nonneg hs] using hss'

theorem differentiableOn_torusLastLine_comp {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s < s') {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (hq : DifferentiableOn ℂ q (openPolydisc p s')) (θ' : Fin m → ℝ) :
    DifferentiableOn ℂ (fun ζ => q (torusLastLine p s θ' ζ)) (Metric.ball 0 s') :=
  hq.comp (differentiable_torusLastLine p s θ').differentiableOn fun _ hζ =>
    torusLastLine_mem_openPolydisc hs hss' θ' (mem_ball_zero_iff.mp hζ)

theorem continuousOnTorus_of_differentiableOn {p : EuclideanSpace ℂ (Fin (m + 1))}
    {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (hq : DifferentiableOn ℂ q (openPolydisc p s')) : ContinuousOnTorus p s q :=
  hq.continuousOn.comp_continuous (continuous_torusPoint p s)
    (torusPoint_mem_openPolydisc hs hss')

theorem torusPoint_eq_torusLastLine (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ)
    (θ : Fin (m + 1) → ℝ) :
    torusPoint p s θ = torusLastLine p s (Fin.init θ) ((s : ℂ) * exp (θ (Fin.last m) * I)) := by
  conv_lhs => rw [← Fin.snoc_init_self θ]
  exact torusPoint_snoc p s _ _

/-! ### The coefficient space in the box `[0, K)^{m+1}` -/

/-- Lowering the last index of a multi-index in the box by one. -/
def lowerLast {K : ℕ} (α : Fin (m + 1) → Fin K) :
    Fin (m + 1) → Fin K :=
  Function.update α (Fin.last m)
    ⟨α (Fin.last m) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (α _).isLt⟩

/-- Multiplication by `z_last - p_last` on torus coefficients in the box: shift the last index
up by one, times `s`. -/
def lastShift (K : ℕ) (s : ℝ) :
    ((Fin (m + 1) → Fin K) → ℂ) →ₗ[ℂ] ((Fin (m + 1) → Fin K) → ℂ) where
  toFun a α := if h : (α (Fin.last m) : ℕ) = 0 then 0 else (s : ℂ) * a (lowerLast α)
  map_add' a b := by
    funext α
    by_cases h : (α (Fin.last m) : ℕ) = 0 <;> simp [h, mul_add]
  map_smul' c a := by
    funext α
    by_cases h : (α (Fin.last m) : ℕ) = 0 <;> simp [h]
    ring

theorem lastShift_pow_apply_eq_zero (K : ℕ) (s : ℝ) :
    ∀ (j : ℕ) (a : (Fin (m + 1) → Fin K) → ℂ) (α : Fin (m + 1) → Fin K),
      (α (Fin.last m) : ℕ) < j → ((lastShift K s) ^ j) a α = 0 := by
  intro j
  induction j with
  | zero => intro a α h; omega
  | succ j ih =>
      intro a α h
      rw [pow_succ', Module.End.mul_apply]
      change (if h : (α (Fin.last m) : ℕ) = 0 then 0
        else (s : ℂ) * ((lastShift K s ^ j) a) (lowerLast α)) = 0
      split_ifs with h0
      · rfl
      · rw [ih a _ (by simp [lowerLast]; omega), mul_zero]

theorem lastShift_pow_eq_zero (K : ℕ) (s : ℝ) : (lastShift (m := m) K s) ^ K = 0 := by
  refine LinearMap.ext fun a => funext fun α => ?_
  simpa using lastShift_pow_apply_eq_zero K s K a α (α (Fin.last m)).isLt

/-- The torus coefficients of `q` in the box `[0, K)^{m+1}`. -/
def boxCoeffs (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (K : ℕ)
    (q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) : (Fin (m + 1) → Fin K) → ℂ :=
  fun α => torusCoeff p s (fun i => ((α i : ℕ) : ℤ)) q

/-- Multiplication by `z_last - p_last` acts on box coefficients as `lastShift`, for
functions holomorphic in the last variable along the torus. -/
theorem boxCoeffs_mul_last {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ} (hs : 0 < s)
    (hss' : s < s') (K : ℕ) {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (hq : ∀ θ' : Fin m → ℝ, DifferentiableOn ℂ (fun ζ => q (torusLastLine p s θ' ζ))
      (Metric.ball 0 s')) :
    boxCoeffs p s K (fun z => (z (Fin.last m) - p (Fin.last m)) * q z) =
      lastShift K s (boxCoeffs p s K q) := by
  funext α
  simp only [boxCoeffs]
  rw [torusCoeff_mul_last]
  change _ = if h : (α (Fin.last m) : ℕ) = 0 then 0
    else (s : ℂ) * torusCoeff p s (fun i => ((lowerLast α i : ℕ) : ℤ)) q
  split_ifs with h0
  · rw [torusCoeff_eq_zero_of_last_neg hs hss' hq (by simp [h0]), mul_zero]
  · congr 2
    funext i
    by_cases hi : i = Fin.last m
    · subst hi; simp [lowerLast]; omega
    · simp [lowerLast, hi]

/-! ### The difference quotient in the last variable -/

/-- `z` with its last coordinate replaced by `p_last + ζ`. -/
def replaceLast (p z : EuclideanSpace ℂ (Fin (m + 1))) (ζ : ℂ) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp z) (Fin.last m) (p (Fin.last m) + ζ))

theorem replaceLast_torusLastLine (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ)
    (θ' : Fin m → ℝ) (ζ ζ₂ : ℂ) :
    replaceLast p (torusLastLine p s θ' ζ) ζ₂ = torusLastLine p s θ' ζ₂ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replaceLast, torusLastLine]
  · simp [replaceLast, torusLastLine, Fin.castSucc_ne_last]

theorem torusLastLine_last (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (θ' : Fin m → ℝ)
    (ζ : ℂ) : torusLastLine p s θ' ζ (Fin.last m) - p (Fin.last m) = ζ := by
  simp [torusLastLine]

/-- The difference quotient of `H` in the last variable at `z_last = p_last + t`. -/
def lastSlope (H : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) (p : EuclideanSpace ℂ (Fin (m + 1)))
    (t : ℂ) (z : EuclideanSpace ℂ (Fin (m + 1))) : ℂ :=
  dslope (fun ζ => H (replaceLast p z ζ)) t (z (Fin.last m) - p (Fin.last m))

theorem lastSlope_torusLastLine (H : EuclideanSpace ℂ (Fin (m + 1)) → ℂ)
    (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (t : ℂ) (θ' : Fin m → ℝ) (ζ : ℂ) :
    lastSlope H p t (torusLastLine p s θ' ζ) =
      dslope (fun ζ₂ => H (torusLastLine p s θ' ζ₂)) t ζ := by
  simp only [lastSlope, replaceLast_torusLastLine, torusLastLine_last]

theorem lastSlope_differentiableOn_lines {H : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') {t : ℂ}
    (ht : ‖t‖ < s') (hH : DifferentiableOn ℂ H (openPolydisc p s')) (θ' : Fin m → ℝ) :
    DifferentiableOn ℂ (fun ζ => lastSlope H p t (torusLastLine p s θ' ζ))
      (Metric.ball 0 s') := by
  simp_rw [lastSlope_torusLastLine]
  exact (Complex.differentiableOn_dslope
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht))).mpr
    (differentiableOn_torusLastLine_comp hs hss' hH θ')

/-- On the torus, `H = (z_last - p_last - t) · lastSlope H p t` when `H` vanishes on the
slice `z_last = p_last + t` along the torus lines. -/
theorem eq_mul_lastSlope_of_slice {H : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    {p : EuclideanSpace ℂ (Fin (m + 1))} {s : ℝ} {t : ℂ}
    (hH0 : ∀ θ' : Fin m → ℝ, H (torusLastLine p s θ' t) = 0) (θ : Fin (m + 1) → ℝ) :
    H (torusPoint p s θ) = ((torusPoint p s θ (Fin.last m) - p (Fin.last m)) - t) *
      lastSlope H p t (torusPoint p s θ) := by
  rw [torusPoint_eq_torusLastLine, lastSlope_torusLastLine, torusLastLine_last]
  have h := sub_smul_dslope (fun ζ₂ => H (torusLastLine p s (Fin.init θ) ζ₂)) t
    ((s : ℂ) * exp (θ (Fin.last m) * I))
  simp only [smul_eq_mul, hH0, sub_zero] at h
  exact h.symm

theorem norm_torusPoint_last_sub {p : EuclideanSpace ℂ (Fin (m + 1))} {s : ℝ} (hs : 0 ≤ s)
    {t : ℂ} (ht : ‖t‖ < s / 2) (θ : Fin (m + 1) → ℝ) :
    s / 2 ≤ ‖(torusPoint p s θ (Fin.last m) - p (Fin.last m)) - t‖ := by
  have h1 := norm_torusPoint_sub p hs θ (Fin.last m)
  have h2 := norm_sub_norm_le (torusPoint p s θ (Fin.last m) - p (Fin.last m)) t
  linarith

theorem torusCoeff_zero (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α 0 = 0 := by
  have e : (0 : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) =
      fun z => (0 : ℂ) * (0 : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) z := by
    funext z; simp
  rw [e, torusCoeff_const_mul, zero_mul]

/-- The closed polydisc is compact. -/
theorem isCompact_closedPolydisc (p : EuclideanSpace ℂ (Fin (m + 1))) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact {z : EuclideanSpace ℂ (Fin (m + 1)) | ∀ i, ‖z i - p i‖ ≤ r} := by
  have hclosed : IsClosed {z : EuclideanSpace ℂ (Fin (m + 1)) | ∀ i, ‖z i - p i‖ ≤ r} := by
    have : {z : EuclideanSpace ℂ (Fin (m + 1)) | ∀ i, ‖z i - p i‖ ≤ r} =
        ⋂ i, {z | ‖z i - p i‖ ≤ r} := by ext z; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  refine (isCompact_closedBall p (Real.sqrt (m + 1) * r)).of_isClosed_subset hclosed ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(z - p) i‖ ^ 2 ≤ (m + 1) * r ^ 2 := by
    calc ∑ i, ‖(z - p) i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), r ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := hz i
            simp only [PiLp.sub_apply]
            exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = (m + 1) * r ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(z - p) i‖ ^ 2) ≤ Real.sqrt ((m + 1) * r ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (m + 1) * r := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr]

/-- **Membership from extensions off nearby slices.**  The algebraic half of strong openness:
see the module docstring. -/
theorem germIdeal_mem_of_slice_extensions (hK : GermKrullIntersection m)
    {p : EuclideanSpace ℂ (Fin (m + 1))} {J : (EuclideanSpace ℂ (Fin (m + 1)) → ℂ) → Prop}
    (hJ : IsHolomorphicGermIdeal p J) {s s' : ℝ} (hs : 0 < s) (hss' : s < s')
    {f : EuclideanSpace ℂ (Fin (m + 1)) → ℂ} (hf : DifferentiableOn ℂ f (openPolydisc p s'))
    (t : ℕ → ℂ) (ht0 : ∀ k, t k ≠ 0) (hts : ∀ k, ‖t k‖ < s / 2)
    (ht : Tendsto t atTop (𝓝 0))
    (F : ℕ → EuclideanSpace ℂ (Fin (m + 1)) → ℂ) (hFJ : ∀ k, J (F k))
    (hFhol : ∀ k, DifferentiableOn ℂ (F k) (openPolydisc p s'))
    (hslice : ∀ k, ∀ z ∈ openPolydisc p s', z (Fin.last m) = p (Fin.last m) + t k →
      F k z = f z)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ k θ, ‖t k‖ * ‖F k (torusPoint p s θ)‖ ≤ δ k) : J f := by
  refine hK p J hJ s s' hs hss' f hf fun K => ?_
  have hs0 : 0 ≤ s := hs.le
  have hcont : ∀ {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ},
      DifferentiableOn ℂ q (openPolydisc p s') → ContinuousOnTorus p s q :=
    fun hq => continuousOnTorus_of_differentiableOn hs0 hss' hq
  -- The subspace spanned by `J` in the box coefficients.
  let U : Submodule ℂ ((Fin (m + 1) → Fin K) → ℂ) :=
    { carrier := boxCoeffs p s K '' {q | J q ∧ DifferentiableOn ℂ q (openPolydisc p s')}
      add_mem' := by
        rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
        exact ⟨q₁ + q₂, ⟨hJ.add_mem hq₁.1 hq₂.1, hq₁.2.add hq₂.2⟩,
          funext fun α => torusCoeff_add (hcont hq₁.2) (hcont hq₂.2) _⟩
      zero_mem' :=
        ⟨0, ⟨hJ.zero_mem, differentiableOn_const 0⟩, funext fun α => torusCoeff_zero p s _⟩
      smul_mem' := by
        rintro c _ ⟨q, hq, rfl⟩
        exact ⟨fun z => c * q z,
          ⟨hJ.mul_mem (Eventually.of_forall fun _ => differentiableAt_const c) hq.1,
            (differentiableOn_const c).mul hq.2⟩,
          funext fun α => torusCoeff_const_mul c q _⟩ }
  have hlastdiff : Differentiable ℂ
      (fun z : EuclideanSpace ℂ (Fin (m + 1)) => z (Fin.last m) - p (Fin.last m)) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiable).sub_const _
  have hTU : ∀ u ∈ U, lastShift K s u ∈ U := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨fun z => (z (Fin.last m) - p (Fin.last m)) * q z,
      ⟨hJ.mul_mem (Eventually.of_forall fun z => hlastdiff z) hq.1,
        hlastdiff.differentiableOn.mul hq.2⟩, ?_⟩
    exact boxCoeffs_mul_last hs hss' K (differentiableOn_torusLastLine_comp hs0 hss' hq.2)
  -- The difference quotients.
  set g : ℕ → EuclideanSpace ℂ (Fin (m + 1)) → ℂ := fun k => lastSlope (F k - f) p (t k)
    with hg
  have hts' : ∀ k, ‖t k‖ < s' := fun k => (hts k).trans (by linarith)
  have hH0 : ∀ k (θ' : Fin m → ℝ), (F k - f) (torusLastLine p s θ' (t k)) = 0 := by
    intro k θ'
    simp only [Pi.sub_apply]
    rw [hslice k _ (torusLastLine_mem_openPolydisc hs0 hss' θ' (hts' k))
      (by linear_combination torusLastLine_last p s θ' (t k)), sub_self]
  have hrel : ∀ k θ, (F k - f) (torusPoint p s θ) =
      ((torusPoint p s θ (Fin.last m) - p (Fin.last m)) - t k) * g k (torusPoint p s θ) :=
    fun k => eq_mul_lastSlope_of_slice (hH0 k)
  have hden : ∀ k θ, (torusPoint p s θ (Fin.last m) - p (Fin.last m)) - t k ≠ 0 := by
    intro k θ h
    have := norm_torusPoint_last_sub (p := p) hs0 (hts k) θ
    rw [h, norm_zero] at this
    linarith
  have hgcont : ∀ k, ContinuousOnTorus p s (g k) := by
    intro k
    have hHc : ContinuousOnTorus p s (F k - f) := hcont ((hFhol k).sub hf)
    have heq : (fun θ => g k (torusPoint p s θ)) = fun θ =>
        (F k - f) (torusPoint p s θ) /
          ((torusPoint p s θ (Fin.last m) - p (Fin.last m)) - t k) := by
      funext θ
      rw [hrel k θ, mul_div_cancel_left₀ _ (hden k θ)]
    unfold ContinuousOnTorus
    rw [heq]
    refine hHc.div ?_ (hden k)
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).continuous.comp
      (continuous_torusPoint p s)).sub continuous_const |>.sub continuous_const
  have hglines : ∀ k (θ' : Fin m → ℝ), DifferentiableOn ℂ
      (fun ζ => g k (torusLastLine p s θ' ζ)) (Metric.ball 0 s') :=
    fun k => lastSlope_differentiableOn_lines hs0 hss' (hts' k) ((hFhol k).sub hf)
  -- The coefficient relation.
  have hlastcont : ContinuousOnTorus p s
      (fun z : EuclideanSpace ℂ (Fin (m + 1)) => z (Fin.last m) - p (Fin.last m)) :=
    hlastdiff.continuous.comp (continuous_torusPoint p s)
  have hcoeff : ∀ k, boxCoeffs p s K (F k) - boxCoeffs p s K f =
      lastShift K s (boxCoeffs p s K (g k)) - t k • boxCoeffs p s K (g k) := by
    intro k
    funext α
    have e1 : torusCoeff p s (fun i => ((α i : ℕ) : ℤ)) (F k - f) =
        torusCoeff p s (fun i => ((α i : ℕ) : ℤ))
          ((fun z => (z (Fin.last m) - p (Fin.last m)) * g k z) +
            fun z => (-t k) * g k z) :=
      torusCoeff_congr (fun θ => by simp only [Pi.add_apply]; rw [hrel k θ]; ring) _
    rw [torusCoeff_add
      (show ContinuousOnTorus p s fun z => (z (Fin.last m) - p (Fin.last m)) * g k z from
        hlastcont.mul (hgcont k))
      (show ContinuousOnTorus p s fun z => (-t k) * g k z from
        continuous_const.mul (hgcont k)),
      torusCoeff_const_mul, torusCoeff_sub (hcont (hFhol k)) (hcont hf)] at e1
    have e2 := congrFun (boxCoeffs_mul_last hs hss' K (hglines k)) α
    simp only [boxCoeffs] at e2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, boxCoeffs]
    rw [e1, e2]
    ring
  -- The small vectors.
  obtain ⟨M, hM⟩ := (isCompact_closedPolydisc p hs0).exists_bound_of_continuousOn
    (hf.continuousOn.mono fun z hz i => lt_of_le_of_lt (hz i) hss')
  have hMθ : ∀ θ, ‖f (torusPoint p s θ)‖ ≤ M := fun θ =>
    hM _ fun i => (norm_torusPoint_sub p hs0 θ i).le
  set Y : ℕ → (Fin (m + 1) → Fin K) → ℂ := fun k => t k • boxCoeffs p s K (g k) with hY
  have hYlim : Tendsto Y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro α
    have hbd : ∀ k, ‖Y k α‖ ≤ (2 * π) ^ (m + 1) * ((δ k + ‖t k‖ * M) / (s / 2)) := by
      intro k
      have : Y k α = torusCoeff p s (fun i => ((α i : ℕ) : ℤ)) (fun z => t k * g k z) := by
        simp [hY, boxCoeffs, torusCoeff_const_mul]
      rw [this]
      refine norm_torusCoeff_le (fun θ => ?_) _
      have hr := hrel k θ
      have hn : ‖(F k - f) (torusPoint p s θ)‖ = ‖(torusPoint p s θ (Fin.last m) -
          p (Fin.last m)) - t k‖ * ‖g k (torusPoint p s θ)‖ := by rw [hr, norm_mul]
      have hlow := norm_torusPoint_last_sub (p := p) hs0 (hts k) θ
      have hsub : ‖(F k - f) (torusPoint p s θ)‖ ≤
          ‖F k (torusPoint p s θ)‖ + ‖f (torusPoint p s θ)‖ := norm_sub_le _ _
      rw [norm_mul, le_div_iff₀ (by positivity)]
      have hgn := norm_nonneg (g k (torusPoint p s θ))
      have htn := norm_nonneg (t k)
      nlinarith [hbound k θ, hMθ θ, mul_le_mul_of_nonneg_left hlow (mul_nonneg htn hgn)]
    have hlim : Tendsto (fun k => (2 * π) ^ (m + 1) * ((δ k + ‖t k‖ * M) / (s / 2)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => δ k + ‖t k‖ * M) atTop (𝓝 0) := by
        simpa using hδ.add (ht.norm.mul_const M)
      simpa using (h1.div_const (s / 2)).const_mul ((2 * π) ^ (m + 1))
    exact squeeze_zero_norm hbd hlim
  -- The nilpotent-shift lemma.
  have hx : boxCoeffs p s K f ∈ U := by
    refine mem_of_nilpotent_shift_relation U (lastShift K s) hTU (lastShift_pow_eq_zero K s)
      (boxCoeffs p s K f) t Y ht0 hYlim fun k => ?_
    have hFk : boxCoeffs p s K (F k) ∈ U := ⟨F k, ⟨hFJ k, hFhol k⟩, rfl⟩
    have : lastShift K s (Y k) - t k • Y k + t k • boxCoeffs p s K f =
        t k • boxCoeffs p s K (F k) := by
      have hc := hcoeff k
      simp only [hY, map_smul]
      rw [eq_sub_iff_add_eq] at hc
      rw [← hc]
      simp only [smul_add, smul_sub, smul_smul]
      abel
    rw [this]
    exact U.smul_mem _ hFk
  obtain ⟨h, ⟨hhJ, hhhol⟩, hhf⟩ := hx
  refine ⟨h, hhJ, hhhol, fun α hα => ?_⟩
  exact (congrFun hhf fun i => ⟨α i, hα i⟩).symm

end

end Hironaka
