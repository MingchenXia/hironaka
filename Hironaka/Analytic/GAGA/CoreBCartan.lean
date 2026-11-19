import Hironaka.Analytic.GAGA.CoreBCousin
import Hironaka.Analytic.GAGA.CoreBMatrix

/-!
# Cartan's matrix lemma near the identity

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), step M2.3 of the
plan in `blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core2.tex`).
Source for the mathematics: H. Cartan's lemma on holomorphic matrices
(Gunning--Rossi, *Analytic functions of several complex variables*, VI.E;
Grauert--Remmert, *Theory of Stein spaces*, III §1), proved by Newton iteration.

Let `C_k ⊆ ℂ` be compact, `L(z) = Re(θ z_i)`, and consider the open slab
`slab C r = {z : z_k ∈ U_r(C_k), |L z - t| < δ}` together with its two sides
`leftSide C r = {z_k ∈ U_r(C_k), L z < t + δ}` and `rightSide C r = {z_k ∈ U_r(C_k), t - δ < L z}`
(`U_r` is the open `r`-neighbourhood). For every `ε > 0` there is `η > 0` such that every
holomorphic matrix `A` on `slab C ε` with `‖A - 1‖ ≤ η` (entrywise `ℓ¹` norm) factors as
`A = B' B''⁻¹` on `slab C (ε/2)`, with `B'` holomorphic and invertible on `leftSide C (ε/2)` and
`B''` holomorphic and invertible on `rightSide C (ε/2)` (`exists_factor_near_one`).

Proof (Newton iteration). Put `E₀ = A - 1`. Given `E_j` on `slab C r_j`, split it entrywise
by Cousin I with the bound uniform in the cutoffs (`exists_cousin_split_uniform`),
`E_j = E'_j - E''_j`, with `E'_j` on `leftSide C r_{j+1}`, `E''_j` on `rightSide C r_{j+1}`, both
of norm `≤ κ ‖E_j‖`. Then `(1 - E'_j)(1 + E_j)(1 + E''_j) = 1 + E_{j+1}` with
`E_{j+1} = -E'² + E'E'' - E''² - E'²E'' + E'E''²` quadratic in `E_j`, so `‖E_j‖ ≤ η 2^{-j}`.
The radii `r_j = ε/2 + ε 2^{-j-1}` decrease to `ε/2`. The products
`P'_j = (1 - E'_{j-1}) ⋯ (1 - E'_0)` and `P''_j = (1 + E''_0) ⋯ (1 + E''_{j-1})` converge uniformly
on the sides of radius `ε/2` to holomorphic matrices close to `1` (Weierstrass, entrywise), and
`P'_j A P''_j = 1 + E_j → 1`. Hence `B'_∞ A B''_∞ = 1`, and `B' = B'_∞⁻¹`, `B'' = B''_∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace Hironaka.Analytic.GAGA.Core.Cartan

open Mat Cousin

noncomputable section

variable {n : ℕ}

/-! ### The slab and its two sides -/

/-- The open slab `{z : z_k ∈ U_r(C_k) ∀ k, |Re(θ z_i) - t| < δ}`. -/
def slab (C : Fin n → Set ℂ) (r : ℝ) (i : Fin n) (θ : ℂ) (t δ : ℝ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (∀ k, z k ∈ thickening r (C k)) ∧ |(θ * z i).re - t| < δ}

/-- The left side `{z : z_k ∈ U_r(C_k) ∀ k, Re(θ z_i) < t + δ}`. -/
def leftSide (C : Fin n → Set ℂ) (r : ℝ) (i : Fin n) (θ : ℂ) (t δ : ℝ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (∀ k, z k ∈ thickening r (C k)) ∧ (θ * z i).re < t + δ}

/-- The right side `{z : z_k ∈ U_r(C_k) ∀ k, t - δ < Re(θ z_i)}`. -/
def rightSide (C : Fin n → Set ℂ) (r : ℝ) (i : Fin n) (θ : ℂ) (t δ : ℝ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (∀ k, z k ∈ thickening r (C k)) ∧ t - δ < (θ * z i).re}

section Sets

variable (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (t δ : ℝ)

theorem continuous_linForm : Continuous fun z : EuclideanSpace ℂ (Fin n) => (θ * z i).re :=
  continuous_re.comp (continuous_const.mul (continuous_coord i))

theorem isOpen_thickening_pi (r : ℝ) :
    IsOpen {z : EuclideanSpace ℂ (Fin n) | ∀ k, z k ∈ thickening r (C k)} := by
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun k => isOpen_thickening.preimage (continuous_coord k)

theorem isOpen_slab (r : ℝ) : IsOpen (slab C r i θ t δ) :=
  (isOpen_thickening_pi C r).inter
    (isOpen_lt (continuous_abs.comp ((continuous_linForm i θ).sub continuous_const))
      continuous_const)

theorem isOpen_leftSide (r : ℝ) : IsOpen (leftSide C r i θ t δ) :=
  (isOpen_thickening_pi C r).inter (isOpen_lt (continuous_linForm i θ) continuous_const)

theorem isOpen_rightSide (r : ℝ) : IsOpen (rightSide C r i θ t δ) :=
  (isOpen_thickening_pi C r).inter (isOpen_lt continuous_const (continuous_linForm i θ))

theorem slab_eq_inter (r : ℝ) :
    slab C r i θ t δ = leftSide C r i θ t δ ∩ rightSide C r i θ t δ := by
  ext z
  simp only [slab, leftSide, rightSide, mem_inter_iff, mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨⟨h, by linarith⟩, ⟨h, by linarith⟩⟩
  · rintro ⟨⟨h, h1⟩, ⟨-, h2⟩⟩
    exact ⟨h, by linarith, by linarith⟩

variable {C i θ t δ}

theorem slab_mono {r r' : ℝ} (h : r ≤ r') : slab C r i θ t δ ⊆ slab C r' i θ t δ :=
  fun _ hz => ⟨fun k => thickening_mono h _ (hz.1 k), hz.2⟩

theorem leftSide_mono {r r' : ℝ} (h : r ≤ r') : leftSide C r i θ t δ ⊆ leftSide C r' i θ t δ :=
  fun _ hz => ⟨fun k => thickening_mono h _ (hz.1 k), hz.2⟩

theorem rightSide_mono {r r' : ℝ} (h : r ≤ r') :
    rightSide C r i θ t δ ⊆ rightSide C r' i θ t δ :=
  fun _ hz => ⟨fun k => thickening_mono h _ (hz.1 k), hz.2⟩

end Sets

/-! ### Estimates for one Newton step -/

section Estimates

variable {m : Type} [Fintype m] [DecidableEq m]

/-- The new error after one step: `(1 - a)(1 + a - b)(1 + b) = 1 + newtonErr a b`. -/
def newtonErr (a b : Matrix m m ℂ) : Matrix m m ℂ :=
  -(a * a) + a * b - b * b - a * a * b + a * b * b

theorem newton_identity (a b : Matrix m m ℂ) :
    (1 - a) * (1 + (a - b)) * (1 + b) = 1 + newtonErr a b := by
  simp only [newtonErr]
  noncomm_ring

theorem mnorm_newtonErr_le {a b : Matrix m m ℂ} {x : ℝ} (ha : mnorm a ≤ x) (hb : mnorm b ≤ x)
    (hx : x ≤ 1) : mnorm (newtonErr a b) ≤ 5 * x ^ 2 := by
  have hx0 : 0 ≤ x := (mnorm_nonneg a).trans ha
  have h2 : ∀ c d : Matrix m m ℂ, mnorm c ≤ x → mnorm d ≤ x → mnorm (c * d) ≤ x ^ 2 :=
    fun c d hc hd => (mnorm_mul_le c d).trans (by
      rw [sq]; exact mul_le_mul hc hd (mnorm_nonneg _) hx0)
  have h3 : ∀ c d e : Matrix m m ℂ, mnorm c ≤ x → mnorm d ≤ x → mnorm e ≤ x →
      mnorm (c * d * e) ≤ x ^ 2 := by
    intro c d e hc hd he
    have h1 : mnorm (c * d) * mnorm e ≤ x ^ 2 * x :=
      mul_le_mul (h2 c d hc hd) he (mnorm_nonneg _) (sq_nonneg x)
    have h1' : x ^ 2 * x ≤ x ^ 2 := by nlinarith [sq_nonneg x]
    exact (mnorm_mul_le _ _).trans (h1.trans h1')
  have e : newtonErr a b = -(a * a) + a * b + -(b * b) + -(a * a * b) + a * b * b := by
    simp only [newtonErr]
    abel
  rw [e]
  have s1 := mnorm_add_le (-(a * a) + a * b + -(b * b) + -(a * a * b)) (a * b * b)
  have s2 := mnorm_add_le (-(a * a) + a * b + -(b * b)) (-(a * a * b))
  have s3 := mnorm_add_le (-(a * a) + a * b) (-(b * b))
  have s4 := mnorm_add_le (-(a * a)) (a * b)
  rw [mnorm_neg] at s2 s3 s4
  have t1 := h2 a a ha ha
  have t2 := h2 a b ha hb
  have t3 := h2 b b hb hb
  have t4 := h3 a a b ha ha hb
  have t5 := h3 a b b ha hb hb
  linarith

end Estimates

/-! ### Convergent products -/

section Products

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {m : Type} [Fintype m] [DecidableEq m]

/-- A sequence of holomorphic matrices near `1` with geometrically small increments converges
locally uniformly to a holomorphic invertible matrix. -/
theorem exists_limit_of_increments {S : Set X} (hS : IsOpen S) {P : ℕ → X → Matrix m m ℂ}
    (hPh : ∀ j, MatHolOn (P j) S) (hP0 : ∀ z, P 0 z = 1) {c : ℝ}
    (hinc : ∀ j, ∀ z ∈ S, mnorm (P (j + 1) z - P j z) ≤ c * (1 / 2) ^ j)
    (hhalf : ∀ j, ∀ z ∈ S, mnorm (P j z - 1) ≤ 1 / 2) :
    ∃ B : X → Matrix m m ℂ, MatHolOn B S ∧ (∀ z ∈ S, (B z).det ≠ 0) ∧
      ∀ z ∈ S, Tendsto (fun N => P N z) atTop (𝓝 (B z)) := by
  have hsumm : Summable fun j : ℕ => c * (1 / 2) ^ j := summable_geometric_two.mul_left c
  have hunif : ∀ a b, TendstoUniformlyOn (fun N z => P N z a b)
      (fun z => (1 : Matrix m m ℂ) a b + ∑' j, (P (j + 1) z - P j z) a b) atTop S := by
    intro a b
    have hts := tendstoUniformlyOn_tsum_nat hsumm (f := fun j z => (P (j + 1) z - P j z) a b)
      (s := S) fun j z hz => (norm_entry_le_mnorm _ a b).trans (hinc j z hz)
    rw [Metric.tendstoUniformlyOn_iff] at hts ⊢
    intro e he
    filter_upwards [hts e he] with N hN z hz
    have htel : ∑ j ∈ Finset.range N, (P (j + 1) z - P j z) a b =
        P N z a b - (1 : Matrix m m ℂ) a b := by
      have := Finset.sum_range_sub (fun j => P j z a b) N
      simp only [hP0] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by simp [Matrix.sub_apply]
    have := hN z hz
    rw [htel] at this
    rw [dist_eq_norm] at this ⊢
    convert this using 2
    ring
  refine ⟨fun z => Matrix.of fun a b =>
    (1 : Matrix m m ℂ) a b + ∑' j, (P (j + 1) z - P j z) a b, ?_, ?_, ?_⟩
  · exact MatHolOn.of_tendstoUniformlyOn hS hPh fun a b => by simpa using hunif a b
  · have ht : ∀ z ∈ S, Tendsto (fun N => P N z) atTop (𝓝 (Matrix.of fun a b =>
        (1 : Matrix m m ℂ) a b + ∑' j, (P (j + 1) z - P j z) a b)) := fun z hz =>
      tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => by
        simpa using (hunif a b).tendsto_at hz
    intro z hz
    refine det_ne_zero_of_mnorm_sub_one_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ) / 2 < 1))
    exact le_of_tendsto ((continuous_mnorm.tendsto _).comp ((ht z hz).sub_const 1))
      (Eventually.of_forall fun N => hhalf N z hz)
  · intro z hz
    exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => by
      simpa using (hunif a b).tendsto_at hz

theorem mnorm_le_card_add_one {P : Matrix m m ℂ} (hP : mnorm (P - 1) ≤ 1 / 2) :
    mnorm P ≤ Fintype.card m + 1 := by
  have h := mnorm_add_le (P - 1) 1
  rw [sub_add_cancel, mnorm_one] at h
  linarith

/-- Convergence of the left products `P_{j+1} = (1 + F_j) P_j`. -/
theorem exists_limit_prod_left {S : Set X} (hS : IsOpen S) {F P : ℕ → X → Matrix m m ℂ}
    (hF : ∀ j, MatHolOn (F j) S) {c : ℝ} (hc8 : c ≤ 1 / 8)
    (hFb : ∀ j, ∀ z ∈ S, mnorm (F j z) ≤ c * (1 / 2) ^ j) (hP0 : ∀ z, P 0 z = 1)
    (hPs : ∀ j z, P (j + 1) z = (1 + F j z) * P j z) :
    ∃ B : X → Matrix m m ℂ, MatHolOn B S ∧ (∀ z ∈ S, (B z).det ≠ 0) ∧
      ∀ z ∈ S, Tendsto (fun N => P N z) atTop (𝓝 (B z)) := by
  have hpow : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
  have hPh : ∀ j, MatHolOn (P j) S := by
    intro j
    induction j with
    | zero => exact (MatHolOn.const 1 S).congr' fun z => (hP0 z).symm
    | succ j ih => exact (((MatHolOn.const 1 S).add (hF j)).mul ih).congr' fun z => (hPs j z).symm
  have hPb : ∀ j, ∀ z ∈ S, mnorm (P j z - 1) ≤ 4 * c * (1 - (1 / 2) ^ j) := by
    intro j
    induction j with
    | zero => intro z _; simp [hP0, mnorm_zero]
    | succ j ih =>
        intro z hz
        have hx := hFb j z hz
        have hc0 : 0 ≤ c := by
          have := (mnorm_nonneg _).trans hx
          exact nonneg_of_mul_nonneg_left this (hpow j)
        have hρ := ih z hz
        have hρ1 : mnorm (P j z - 1) ≤ 1 := by
          have : (1 : ℝ) - (1 / 2) ^ j ≤ 1 := by linarith [hpow j]
          nlinarith
        have heq : P (j + 1) z - 1 = (P j z - 1) + F j z * (P j z - 1) + F j z := by
          rw [hPs]
          noncomm_ring
        rw [heq]
        have s1 := mnorm_add_le ((P j z - 1) + F j z * (P j z - 1)) (F j z)
        have s2 := mnorm_add_le (P j z - 1) (F j z * (P j z - 1))
        have s3 := mnorm_mul_le (F j z) (P j z - 1)
        have s4 : mnorm (F j z) * mnorm (P j z - 1) ≤ c * (1 / 2) ^ j :=
          (mul_le_mul hx hρ1 (mnorm_nonneg _) (by positivity)).trans (le_of_eq (mul_one _))
        rw [pow_succ]
        linarith
  have hhalf : ∀ j, ∀ z ∈ S, mnorm (P j z - 1) ≤ 1 / 2 := by
    intro j z hz
    refine (hPb j z hz).trans ?_
    have hc0 : 0 ≤ c := by
      have := (mnorm_nonneg _).trans (hFb 0 z hz)
      simpa using this
    nlinarith [hpow j]
  refine exists_limit_of_increments hS hPh hP0 (c := c * (Fintype.card m + 1)) ?_ hhalf
  intro j z hz
  have heq : P (j + 1) z - P j z = F j z * P j z := by
    rw [hPs]
    noncomm_ring
  rw [heq]
  calc mnorm (F j z * P j z) ≤ mnorm (F j z) * mnorm (P j z) := mnorm_mul_le _ _
    _ ≤ (c * (1 / 2) ^ j) * (Fintype.card m + 1) :=
        mul_le_mul (hFb j z hz) (mnorm_le_card_add_one (hhalf j z hz)) (mnorm_nonneg _)
          ((mnorm_nonneg _).trans (hFb j z hz))
    _ = c * (Fintype.card m + 1) * (1 / 2) ^ j := by ring

/-- Convergence of the right products `P_{j+1} = P_j (1 + F_j)`. -/
theorem exists_limit_prod_right {S : Set X} (hS : IsOpen S) {F P : ℕ → X → Matrix m m ℂ}
    (hF : ∀ j, MatHolOn (F j) S) {c : ℝ} (hc8 : c ≤ 1 / 8)
    (hFb : ∀ j, ∀ z ∈ S, mnorm (F j z) ≤ c * (1 / 2) ^ j) (hP0 : ∀ z, P 0 z = 1)
    (hPs : ∀ j z, P (j + 1) z = P j z * (1 + F j z)) :
    ∃ B : X → Matrix m m ℂ, MatHolOn B S ∧ (∀ z ∈ S, (B z).det ≠ 0) ∧
      ∀ z ∈ S, Tendsto (fun N => P N z) atTop (𝓝 (B z)) := by
  have hpow : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
  have hPh : ∀ j, MatHolOn (P j) S := by
    intro j
    induction j with
    | zero => exact (MatHolOn.const 1 S).congr' fun z => (hP0 z).symm
    | succ j ih => exact (ih.mul ((MatHolOn.const 1 S).add (hF j))).congr' fun z => (hPs j z).symm
  have hPb : ∀ j, ∀ z ∈ S, mnorm (P j z - 1) ≤ 4 * c * (1 - (1 / 2) ^ j) := by
    intro j
    induction j with
    | zero => intro z _; simp [hP0, mnorm_zero]
    | succ j ih =>
        intro z hz
        have hx := hFb j z hz
        have hρ := ih z hz
        have hρ1 : mnorm (P j z - 1) ≤ 1 := by
          have : (1 : ℝ) - (1 / 2) ^ j ≤ 1 := by linarith [hpow j]
          have hc0 : 0 ≤ c := nonneg_of_mul_nonneg_left ((mnorm_nonneg _).trans hx) (hpow j)
          nlinarith
        have heq : P (j + 1) z - 1 = (P j z - 1) + (P j z - 1) * F j z + F j z := by
          rw [hPs]
          noncomm_ring
        rw [heq]
        have s1 := mnorm_add_le ((P j z - 1) + (P j z - 1) * F j z) (F j z)
        have s2 := mnorm_add_le (P j z - 1) ((P j z - 1) * F j z)
        have s3 := mnorm_mul_le (P j z - 1) (F j z)
        have s4 : mnorm (P j z - 1) * mnorm (F j z) ≤ c * (1 / 2) ^ j :=
          (mul_le_mul hρ1 hx (mnorm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
        rw [pow_succ]
        linarith
  have hhalf : ∀ j, ∀ z ∈ S, mnorm (P j z - 1) ≤ 1 / 2 := by
    intro j z hz
    refine (hPb j z hz).trans ?_
    have hc0 : 0 ≤ c := by
      have := (mnorm_nonneg _).trans (hFb 0 z hz)
      simpa using this
    nlinarith [hpow j]
  refine exists_limit_of_increments hS hPh hP0 (c := c * (Fintype.card m + 1)) ?_ hhalf
  intro j z hz
  have heq : P (j + 1) z - P j z = P j z * F j z := by
    rw [hPs]
    noncomm_ring
  rw [heq]
  calc mnorm (P j z * F j z) ≤ mnorm (P j z) * mnorm (F j z) := mnorm_mul_le _ _
    _ ≤ (Fintype.card m + 1) * (c * (1 / 2) ^ j) :=
        mul_le_mul (mnorm_le_card_add_one (hhalf j z hz)) (hFb j z hz) (mnorm_nonneg _)
          (by positivity)
    _ = c * (Fintype.card m + 1) * (1 / 2) ^ j := by ring

end Products

/-! ### The factorization -/

/-- **Cartan's matrix lemma near the identity.** Let `C_k ⊆ ℂ` be compact, `ε, δ > 0`. There
is `η > 0` such that every matrix `A`, holomorphic on the slab `slab C ε` around the slice
`{Re(θ z_i) = t}` with `‖A - 1‖ ≤ η` there, factors on `slab C (ε/2)` as `A = B' B''⁻¹` with
`B'` holomorphic and invertible on the left side `leftSide C (ε/2)` and `B''` holomorphic and
invertible on the right side `rightSide C (ε/2)`. -/
theorem exists_factor_near_one (i : Fin n) (θ : ℂ) (t : ℝ) {C : Fin n → Set ℂ}
    (hC : ∀ k, IsCompact (C k)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (m : Type) [Fintype m]
    [DecidableEq m] :
    ∃ η > 0, ∀ A : EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      MatHolOn A (slab C ε i θ t δ) → (∀ z ∈ slab C ε i θ t δ, mnorm (A z - 1) ≤ η) →
      ∃ B' B'' : EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
        MatHolOn B' (leftSide C (ε / 2) i θ t δ) ∧ MatHolOn B'' (rightSide C (ε / 2) i θ t δ) ∧
        (∀ z ∈ leftSide C (ε / 2) i θ t δ, (B' z).det ≠ 0) ∧
        (∀ z ∈ rightSide C (ε / 2) i θ t δ, (B'' z).det ≠ 0) ∧
        ∀ z ∈ slab C (ε / 2) i θ t δ, A z = B' z * (B'' z)⁻¹ := by
  classical
  -- the radii
  obtain ⟨r, ρ, hr0, hrρ, hρr, hrhalf, hρε⟩ : ∃ r ρ : ℕ → ℝ, r 0 = ε ∧ (∀ j, r (j + 1) < ρ j) ∧
      (∀ j, ρ j < r j) ∧ (∀ j, ε / 2 ≤ r j) ∧ ∀ j, ρ j ≤ ε := by
    have hpow : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ j := fun j => by positivity
    have hpow1 : ∀ j : ℕ, ((1 : ℝ) / 2) ^ j ≤ 1 := fun j =>
      pow_le_one₀ (by norm_num) (by norm_num)
    refine ⟨fun j => ε / 2 + ε / 2 * (1 / 2) ^ j, fun j => ε / 2 + 3 * ε / 8 * (1 / 2) ^ j,
      by simp, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [pow_succ]
      nlinarith [hpow j]
    · nlinarith [hpow j]
    · nlinarith [hpow j]
    · nlinarith [hpow1 j, hpow j]
  have hrpos : ∀ j, 0 < r j := fun j => lt_of_lt_of_le (by positivity) (hrhalf j)
  -- a ball containing all the cutoff supports
  obtain ⟨R, hR⟩ : ∃ R, ∀ k, cthickening ε (C k) ⊆ closedBall (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := (isCompact_iUnion fun k => (hC k).cthickening (r := ε)).isBounded
      |>.subset_closedBall 0
    exact ⟨R, fun k => (subset_iUnion (fun k => cthickening ε (C k)) k).trans hR⟩
  -- the cutoffs
  have hcut : ∀ (j : ℕ) (k : Fin n), ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ w, |ψ w| ≤ 1) ∧ (∀ w ∈ thickening (r (j + 1)) (C k), ψ w = 1) ∧
      tsupport ψ ⊆ cthickening (ρ j) (C k) :=
    fun j k => exists_cutoff_between (hC k) (hrpos (j + 1)).le (hrρ j)
  choose ψ hψ hψc hψ1 hψ11 hψs using hcut
  -- the Cousin constant
  obtain ⟨Cc, hCc0, hCc⟩ := exists_cousin_split_uniform i θ t δ hδ R
  obtain ⟨κ, hκ1, hκcard⟩ : ∃ κ : ℝ, 1 ≤ κ ∧
      ∀ x : ℝ, 0 ≤ x → (Fintype.card m * Fintype.card m : ℝ) * (Cc * x) ≤ κ * x := by
    refine ⟨(Fintype.card m : ℝ) * Fintype.card m * Cc + 1, ?_, fun x hx => ?_⟩
    · have : 0 ≤ (Fintype.card m : ℝ) * Fintype.card m * Cc := by positivity
      linarith
    · nlinarith
  have hκ0 : 0 < κ := by linarith
  obtain ⟨η₀, hη₀pos, hη₀a, hη₀b⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ 10 * κ ^ 2 * η₀ ≤ 1 ∧ 8 * κ * η₀ ≤ 1 := by
    refine ⟨min (1 / (10 * κ ^ 2)) (1 / (8 * κ)), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have h := min_le_left (1 / (10 * κ ^ 2)) (1 / (8 * κ))
      rw [le_div_iff₀ (by positivity)] at h
      linarith
    · have h := min_le_right (1 / (10 * κ ^ 2)) (1 / (8 * κ))
      rw [le_div_iff₀ (by positivity)] at h
      linarith
  refine ⟨η₀, hη₀pos, ?_⟩
  intro A hA hAη
  obtain ⟨η, hη0, hηpos, hηle, hηsucc, hηgeom, hηt⟩ : ∃ η : ℕ → ℝ, η 0 = η₀ ∧ (∀ j, 0 ≤ η j) ∧
      (∀ j, η j ≤ η₀) ∧ (∀ j, η (j + 1) = η j / 2) ∧ (∀ j, η j = η₀ * (1 / 2) ^ j) ∧
      Tendsto η atTop (𝓝 0) := by
    refine ⟨fun j => η₀ * (1 / 2) ^ j, by simp, fun j => by positivity, fun j => ?_,
      fun j => by simp only [pow_succ]; ring, fun j => rfl, ?_⟩
    · exact mul_le_of_le_one_right hη₀pos.le (pow_le_one₀ (by norm_num) (by norm_num))
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul η₀
  -- one Newton step
  have hstep : ∀ (j : ℕ) (E : EuclideanSpace ℂ (Fin n) → Matrix m m ℂ),
      ∃ E' E'' : EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
        (MatHolOn E (slab C (r j) i θ t δ) ∧
          ∀ z ∈ slab C (r j) i θ t δ, mnorm (E z) ≤ η j) →
        MatHolOn E' (leftSide C (r (j + 1)) i θ t δ) ∧
        MatHolOn E'' (rightSide C (r (j + 1)) i θ t δ) ∧ (∀ z, E z = E' z - E'' z) ∧
        (∀ z ∈ leftSide C (r (j + 1)) i θ t δ, mnorm (E' z) ≤ κ * η j) ∧
        (∀ z ∈ rightSide C (r (j + 1)) i θ t δ, mnorm (E'' z) ≤ κ * η j) := by
    intro j E
    by_cases hE : MatHolOn E (slab C (r j) i θ t δ) ∧
        ∀ z ∈ slab C (r j) i θ t δ, mnorm (E z) ≤ η j
    swap
    · exact ⟨E, E, fun h => absurd h hE⟩
    obtain ⟨hEh, hEb⟩ := hE
    have hsub : {z : EuclideanSpace ℂ (Fin n) | (∀ k, z k ∈ tsupport (ψ j k)) ∧
        |(θ * z i).re - t| < δ} ⊆ slab C (r j) i θ t δ := fun z hz =>
      ⟨fun k => cthickening_subset_thickening' (hrpos j) (hρr j) _ (hψs j k (hz.1 k)), hz.2⟩
    have hentry : ∀ a b, ∃ f' f'' : EuclideanSpace ℂ (Fin n) → ℂ,
        DifferentiableOn ℂ f' (leftSide C (r (j + 1)) i θ t δ) ∧
        DifferentiableOn ℂ f'' (rightSide C (r (j + 1)) i θ t δ) ∧
        (∀ z, E z a b = f' z - f'' z) ∧
        (∀ z ∈ leftSide C (r (j + 1)) i θ t δ, ‖f' z‖ ≤ Cc * η j) ∧
        (∀ z ∈ rightSide C (r (j + 1)) i θ t δ, ‖f'' z‖ ≤ Cc * η j) := by
      intro a b
      obtain ⟨f', f'', h1, h2, h3, h4, h5⟩ := hCc (ψ j) (hψ j) (hψc j) (hψ1 j)
        (fun k => (hψs j k).trans ((cthickening_mono (hρε j) _).trans (hR k)))
        (fun k => thickening (r (j + 1)) (C k)) (fun _ => isOpen_thickening) (hψ11 j)
        (slab C (r j) i θ t δ) (fun z => E z a b) (η j) (isOpen_slab C i θ t δ _) (hEh a b)
        hsub (fun z hz1 hz2 => (norm_entry_le_mnorm _ a b).trans (hEb z (hsub ⟨hz1, hz2⟩)))
        (hηpos j)
      exact ⟨f', f'', h1, h2, h3, fun z hz => h4 z hz.1 hz.2, fun z hz => h5 z hz.1 hz.2⟩
    choose f' f'' hf' hf'' hfeq hf'b hf''b using hentry
    refine ⟨fun z => Matrix.of fun a b => f' a b z, fun z => Matrix.of fun a b => f'' a b z,
      fun _ => ⟨fun a b => ?_, fun a b => ?_, fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩⟩
    · simpa using hf' a b
    · simpa using hf'' a b
    · ext a b
      simp [hfeq a b z]
    · exact (mnorm_le_of_forall_entry_le fun a b => by simpa using hf'b a b z hz).trans
        (hκcard _ (hηpos j))
    · exact (mnorm_le_of_forall_entry_le fun a b => by simpa using hf''b a b z hz).trans
        (hκcard _ (hηpos j))
  choose F' F'' hF using hstep
  -- the Newton sequence
  obtain ⟨Eseq, hEseq0, hEseqs⟩ : ∃ Eseq : ℕ → EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      Eseq 0 = (fun z => A z - 1) ∧
      ∀ j, Eseq (j + 1) = fun z => newtonErr (F' j (Eseq j) z) (F'' j (Eseq j) z) :=
    ⟨fun j => Nat.rec (motive := fun _ => EuclideanSpace ℂ (Fin n) → Matrix m m ℂ)
      (fun z => A z - 1) (fun j E z => newtonErr (F' j E z) (F'' j E z)) j, rfl, fun _ => rfl⟩
  have hinv : ∀ j, MatHolOn (Eseq j) (slab C (r j) i θ t δ) ∧
      ∀ z ∈ slab C (r j) i θ t δ, mnorm (Eseq j z) ≤ η j := by
    intro j
    induction j with
    | zero =>
        rw [hEseq0, hr0, hη0]
        exact ⟨hA.sub (MatHolOn.const _ _), hAη⟩
    | succ j ih =>
        obtain ⟨h1, h2, -, h4, h5⟩ := hF j (Eseq j) ih
        rw [hEseqs, slab_eq_inter]
        refine ⟨?_, fun z hz => ?_⟩
        · have g1 := h1.mono (inter_subset_left (s := leftSide C (r (j + 1)) i θ t δ)
            (t := rightSide C (r (j + 1)) i θ t δ))
          have g2 := h2.mono (inter_subset_right (s := leftSide C (r (j + 1)) i θ t δ)
            (t := rightSide C (r (j + 1)) i θ t δ))
          exact ((((g1.mul g1).neg.add (g1.mul g2)).sub (g2.mul g2)).sub
            ((g1.mul g1).mul g2)).add ((g1.mul g2).mul g2)
        · have hx : κ * η j ≤ 1 := by
            have := mul_le_mul_of_nonneg_left (hηle j) hκ0.le
            nlinarith
          refine (mnorm_newtonErr_le (h4 z hz.1) (h5 z hz.2) hx).trans ?_
          rw [hηsucc]
          have h10 : 10 * κ ^ 2 * η j ≤ 1 :=
            le_trans (mul_le_mul_of_nonneg_left (hηle j) (by positivity)) hη₀a
          have := mul_le_mul_of_nonneg_left h10 (hηpos j)
          nlinarith
  -- the factors of each step
  obtain ⟨E', hE'def⟩ : ∃ E' : ℕ → EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      ∀ j, E' j = F' j (Eseq j) := ⟨fun j => F' j (Eseq j), fun _ => rfl⟩
  obtain ⟨E'', hE''def⟩ : ∃ E'' : ℕ → EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      ∀ j, E'' j = F'' j (Eseq j) := ⟨fun j => F'' j (Eseq j), fun _ => rfl⟩
  have hE'h : ∀ j, MatHolOn (E' j) (leftSide C (r (j + 1)) i θ t δ) :=
    fun j => hE'def j ▸ (hF j (Eseq j) (hinv j)).1
  have hE''h : ∀ j, MatHolOn (E'' j) (rightSide C (r (j + 1)) i θ t δ) :=
    fun j => hE''def j ▸ (hF j (Eseq j) (hinv j)).2.1
  have hEsplit : ∀ j z, Eseq j z = E' j z - E'' j z := fun j => by
    rw [hE'def, hE''def]; exact (hF j (Eseq j) (hinv j)).2.2.1
  have hE'b : ∀ j, ∀ z ∈ leftSide C (r (j + 1)) i θ t δ, mnorm (E' j z) ≤ κ * η j :=
    fun j => hE'def j ▸ (hF j (Eseq j) (hinv j)).2.2.2.1
  have hE''b : ∀ j, ∀ z ∈ rightSide C (r (j + 1)) i θ t δ, mnorm (E'' j z) ≤ κ * η j :=
    fun j => hE''def j ▸ (hF j (Eseq j) (hinv j)).2.2.2.2
  have hEseqs' : ∀ j z, Eseq (j + 1) z = newtonErr (E' j z) (E'' j z) := fun j z => by
    rw [hEseqs, hE'def, hE''def]
  -- the partial products
  obtain ⟨Pl, hPl0, hPls⟩ : ∃ Pl : ℕ → EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      (∀ z, Pl 0 z = 1) ∧ ∀ j z, Pl (j + 1) z = (1 + -E' j z) * Pl j z :=
    ⟨fun j => Nat.rec (motive := fun _ => EuclideanSpace ℂ (Fin n) → Matrix m m ℂ) (fun _ => 1)
      (fun j P z => (1 + -E' j z) * P z) j, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨Pr, hPr0, hPrs⟩ : ∃ Pr : ℕ → EuclideanSpace ℂ (Fin n) → Matrix m m ℂ,
      (∀ z, Pr 0 z = 1) ∧ ∀ j z, Pr (j + 1) z = Pr j z * (1 + E'' j z) :=
    ⟨fun j => Nat.rec (motive := fun _ => EuclideanSpace ℂ (Fin n) → Matrix m m ℂ) (fun _ => 1)
      (fun j P z => P z * (1 + E'' j z)) j, fun _ => rfl, fun _ _ => rfl⟩
  have hprod : ∀ j z, Pl j z * A z * Pr j z = 1 + Eseq j z := by
    intro j
    induction j with
    | zero => intro z; rw [hPl0, hPr0, hEseq0]; noncomm_ring
    | succ j ih =>
        intro z
        rw [hPls, hPrs, hEseqs', ← newton_identity, ← hEsplit, ← ih]
        noncomm_ring
  -- the limits
  have hLsub : ∀ j, leftSide C (ε / 2) i θ t δ ⊆ leftSide C (r (j + 1)) i θ t δ :=
    fun j => leftSide_mono (hrhalf _)
  have hRsub : ∀ j, rightSide C (ε / 2) i θ t δ ⊆ rightSide C (r (j + 1)) i θ t δ :=
    fun j => rightSide_mono (hrhalf _)
  have hc8 : κ * η₀ ≤ 1 / 8 := by linarith
  obtain ⟨B', hB'h, hB'det, hB't⟩ := exists_limit_prod_left (isOpen_leftSide C i θ t δ _)
    (F := fun j z => -E' j z) (fun j => ((hE'h j).mono (hLsub j)).neg) hc8
    (fun j z hz => by
      rw [mnorm_neg, mul_assoc, ← hηgeom]
      exact hE'b j z (hLsub j hz)) hPl0 hPls
  obtain ⟨B'', hB''h, hB''det, hB''t⟩ := exists_limit_prod_right (isOpen_rightSide C i θ t δ _)
    (F := E'') (fun j => (hE''h j).mono (hRsub j)) hc8
    (fun j z hz => by
      rw [mul_assoc, ← hηgeom]
      exact hE''b j z (hRsub j hz)) hPr0 hPrs
  -- the identity `B' A B'' = 1`
  have hlim : ∀ z ∈ slab C (ε / 2) i θ t δ, B' z * A z * B'' z = 1 := by
    intro z hz
    have hz' := hz
    rw [slab_eq_inter] at hz'
    have h1 : Tendsto (fun N => Pl N z * A z * Pr N z) atTop (𝓝 (B' z * A z * B'' z)) :=
      ((hB't z hz'.1).mul tendsto_const_nhds).mul (hB''t z hz'.2)
    have h0 : Tendsto (fun N => Eseq N z) atTop (𝓝 0) := by
      refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
      exact squeeze_zero_norm (fun N => (norm_entry_le_mnorm _ a b).trans
        ((hinv N).2 z (slab_mono (hrhalf N) hz))) hηt
    have h2 : Tendsto (fun N => Pl N z * A z * Pr N z) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : Matrix m m ℂ))).add h0
      rw [add_zero] at this
      exact this.congr fun N => (hprod N z).symm
    exact tendsto_nhds_unique h1 h2
  -- conclusion
  refine ⟨fun z => (B' z)⁻¹, B'', hB'h.inv hB'det, hB''h, fun z hz => det_inv_ne_zero
    (hB'det z hz), hB''det, fun z hz => ?_⟩
  have hzL : z ∈ leftSide C (ε / 2) i θ t δ := by
    rw [slab_eq_inter] at hz
    exact hz.1
  exact eq_inv_mul_inv_of_mul_mul_eq_one (hlim z hz) (hB'det z hzL)

end

end Hironaka.Analytic.GAGA.Core.Cartan
