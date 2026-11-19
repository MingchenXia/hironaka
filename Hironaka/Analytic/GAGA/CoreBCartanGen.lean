import Hironaka.Analytic.GAGA.CoreBCartan
import Hironaka.Analytic.GAGA.CoreBRunge

/-!
# Cartan's matrix lemma for products of unipotent block matrices

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), step M2.3 of the
plan in `blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core2.tex`).

Let `Q = ∏ C_l` be a compact convex product set, split by the real hyperplane
`Re(θ z_i) = t` into `Q' = Q ∩ {Re(θ z_i) ≤ t}` and `Q'' = Q ∩ {Re(θ z_i) ≥ t}`, with face
`K = Q ∩ {Re(θ z_i) = t}`. For matrices `T` (`a × b`) and `S` (`b × a`) holomorphic near `K`, the
invertible matrix
`A = [[1, T], [0, 1]] · [[1, 0], [-S, 1]]`
factors near `K` as `A = B' B''⁻¹` with `B'` holomorphic invertible near `Q'` and `B''`
holomorphic invertible near `Q''` (`exists_factor_unipotent`). These are the matrices that occur
in the proof of Cartan's Theorem A on compact convex product sets (two systems of generators
`s'`, `s''` with `s'' = s' T`, `s' = s'' S` near `K`).

Proof. Approximate `T, S` on a compact convex product neighbourhood of `K` by polynomial
matrices `T̃, S̃` (`exists_mvPolynomial_approx`), and put `H = [[1, T̃], [0, 1]] [[1, 0], [-S̃, 1]]`,
an entire matrix of determinant `1` with explicit inverse. Then `H⁻¹ A - 1` is small near `K`,
so `H⁻¹ A = B'₀ B''₀⁻¹` by Newton's iteration (`exists_factor_near_one`), and
`A = (H B'₀) B''₀⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric Complex Matrix
open scoped Topology

namespace Hironaka.Analytic.GAGA.Core.Cartan

open Mat

noncomputable section

variable {n : ℕ}

/-! ### Polynomials are entire -/

theorem differentiable_eval_mvPolynomial (q : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ fun z : EuclideanSpace ℂ (Fin n) => MvPolynomial.eval (fun l => z l) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval_C]
      exact differentiable_const a
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p l hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul ((EuclideanSpace.proj l : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).differentiable)

/-! ### Unipotent block matrices -/

section Blocks

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The upper unipotent block matrix `[[1, T], [0, 1]]`. -/
def upperU (T : Matrix a b ℂ) : Matrix (a ⊕ b) (a ⊕ b) ℂ := fromBlocks 1 T 0 1

/-- The lower unipotent block matrix `[[1, 0], [S, 1]]`. -/
def lowerU (S : Matrix b a ℂ) : Matrix (a ⊕ b) (a ⊕ b) ℂ := fromBlocks 1 0 S 1

theorem upperU_mul_upperU (T T' : Matrix a b ℂ) : upperU T * upperU T' = upperU (T + T') := by
  simp [upperU, fromBlocks_multiply, add_comm]

theorem lowerU_mul_lowerU (S S' : Matrix b a ℂ) : lowerU S * lowerU S' = lowerU (S + S') := by
  simp [lowerU, fromBlocks_multiply, add_comm]

theorem upperU_zero : upperU (0 : Matrix a b ℂ) = 1 := by
  simp [upperU, fromBlocks_one]

theorem lowerU_zero : lowerU (0 : Matrix b a ℂ) = 1 := by
  simp [lowerU, fromBlocks_one]

theorem det_upperU (T : Matrix a b ℂ) : (upperU T).det = 1 := by
  simp [upperU]

theorem det_lowerU (S : Matrix b a ℂ) : (lowerU S).det = 1 := by
  simp [lowerU]

theorem mnorm_fromBlocks (A : Matrix a a ℂ) (B : Matrix a b ℂ) (C : Matrix b a ℂ)
    (D : Matrix b b ℂ) : mnorm (fromBlocks A B C D) = mnorm A + mnorm B + mnorm C + mnorm D := by
  simp only [mnorm, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

theorem mnorm_lowerU (S : Matrix b a ℂ) :
    mnorm (lowerU S) = Fintype.card a + mnorm S + Fintype.card b := by
  rw [lowerU, mnorm_fromBlocks, mnorm_one, mnorm_one, mnorm_zero]
  ring

/-- The key identity: `L(S̃) U(-T̃) U(T) L(-S) - 1 = [[0,0],[S̃ - S, 0]] + L(S̃) N L(-S)` with
`N = [[0, T - T̃], [0, 0]]`. -/
theorem approx_identity (T T' : Matrix a b ℂ) (S S' : Matrix b a ℂ) :
    lowerU S' * upperU (-T') * (upperU T * lowerU (-S)) - 1 =
      fromBlocks 0 0 (S' - S) 0 + lowerU S' * fromBlocks 0 (T - T') 0 0 * lowerU (-S) := by
  have h1 : upperU (-T') * upperU T = 1 + fromBlocks 0 (T - T') 0 0 := by
    rw [upperU_mul_upperU, upperU, ← fromBlocks_one, fromBlocks_add]
    congr 1 <;> simp; abel
  have h2 : lowerU S' * lowerU (-S) = 1 + fromBlocks 0 0 (S' - S) 0 := by
    rw [lowerU_mul_lowerU, lowerU, ← fromBlocks_one, fromBlocks_add]
    congr 1 <;> simp; abel
  calc lowerU S' * upperU (-T') * (upperU T * lowerU (-S)) - 1
      = lowerU S' * (upperU (-T') * upperU T) * lowerU (-S) - 1 := by noncomm_ring
    _ = lowerU S' * lowerU (-S) + lowerU S' * fromBlocks 0 (T - T') 0 0 * lowerU (-S) - 1 := by
        rw [h1]; noncomm_ring
    _ = _ := by rw [h2]; abel

theorem upperU_mul_lowerU_mul_inv (T : Matrix a b ℂ) (S : Matrix b a ℂ) :
    upperU T * lowerU (-S) * (lowerU S * upperU (-T)) = 1 := by
  calc upperU T * lowerU (-S) * (lowerU S * upperU (-T))
      = upperU T * (lowerU (-S) * lowerU S) * upperU (-T) := by noncomm_ring
    _ = 1 := by rw [lowerU_mul_lowerU, neg_add_cancel, lowerU_zero, Matrix.mul_one,
          upperU_mul_upperU, add_neg_cancel, upperU_zero]

theorem mnorm_approx_sub_one_le (T T' : Matrix a b ℂ) (S S' : Matrix b a ℂ) {e κ : ℝ}
    (hT : mnorm (T - T') ≤ e) (hS : mnorm (S' - S) ≤ e)
    (hSκ : Fintype.card a + mnorm S + Fintype.card b ≤ κ) :
    mnorm (lowerU S' * upperU (-T') * (upperU T * lowerU (-S)) - 1) ≤ e + (κ + e) * e * κ := by
  rw [approx_identity]
  have he : 0 ≤ e := (mnorm_nonneg _).trans hT
  have hN : mnorm (fromBlocks (0 : Matrix a a ℂ) (T - T') 0 (0 : Matrix b b ℂ)) ≤ e := by
    rw [mnorm_fromBlocks, mnorm_zero, mnorm_zero, mnorm_zero]
    linarith
  have hM : mnorm (fromBlocks (0 : Matrix a a ℂ) 0 (S' - S) (0 : Matrix b b ℂ)) ≤ e := by
    rw [mnorm_fromBlocks, mnorm_zero, mnorm_zero, mnorm_zero]
    linarith
  have hL1 : mnorm (lowerU S' : Matrix (a ⊕ b) (a ⊕ b) ℂ) ≤ κ + e := by
    rw [mnorm_lowerU]
    have := mnorm_add_le (S' - S) S
    rw [sub_add_cancel] at this
    linarith
  have hL2 : mnorm (lowerU (-S) : Matrix (a ⊕ b) (a ⊕ b) ℂ) ≤ κ := by
    rw [mnorm_lowerU, mnorm_neg]
    linarith
  have s1 := mnorm_add_le (fromBlocks (0 : Matrix a a ℂ) 0 (S' - S) (0 : Matrix b b ℂ))
    (lowerU S' * fromBlocks 0 (T - T') 0 0 * lowerU (-S))
  have s2 := mnorm_mul_le (lowerU S' * fromBlocks (0 : Matrix a a ℂ) (T - T') 0
    (0 : Matrix b b ℂ)) (lowerU (-S))
  have s3 := mnorm_mul_le (lowerU S' : Matrix (a ⊕ b) (a ⊕ b) ℂ)
    (fromBlocks (0 : Matrix a a ℂ) (T - T') 0 (0 : Matrix b b ℂ))
  have h4 : mnorm (lowerU S' : Matrix (a ⊕ b) (a ⊕ b) ℂ) *
      mnorm (fromBlocks (0 : Matrix a a ℂ) (T - T') 0 (0 : Matrix b b ℂ)) ≤ (κ + e) * e :=
    mul_le_mul hL1 hN (mnorm_nonneg _) ((mnorm_nonneg _).trans hL1)
  have h5 : mnorm (lowerU S' * fromBlocks (0 : Matrix a a ℂ) (T - T') 0 (0 : Matrix b b ℂ)) *
      mnorm (lowerU (-S) : Matrix (a ⊕ b) (a ⊕ b) ℂ) ≤ (κ + e) * e * κ :=
    mul_le_mul (s3.trans h4) hL2 (mnorm_nonneg _)
      (mul_nonneg ((mnorm_nonneg _).trans hL1) he)
  linarith

theorem matHolOn_upperU {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}
    {F : X → Matrix a b ℂ} (hF : MatHolOn F U) : MatHolOn (fun z => upperU (F z)) U := by
  intro x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [Cartan.upperU, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂] <;>
    first | exact differentiableOn_const _ | exact hF x y

theorem matHolOn_lowerU {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}
    {F : X → Matrix b a ℂ} (hF : MatHolOn F U) : MatHolOn (fun z => lowerU (F z)) U := by
  intro x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [Cartan.lowerU, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂] <;>
    first | exact differentiableOn_const _ | exact hF x y

end Blocks

/-! ### A closed slab inside an open neighbourhood of the face -/

/-- An open set containing the face `K = Q ∩ {Re(θ z_i) = t}` of a compact product set contains a
closed slab `{z_l ∈ cthickening ε (C_l), |Re(θ z_i) - t| ≤ ε}`. -/
theorem exists_closedSlab_subset (i : Fin n) (θ : ℂ) (t : ℝ) {C : Fin n → Set ℂ}
    (hC : ∀ l, IsCompact (C l)) {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (hKW : {z | (∀ l, z l ∈ C l) ∧ (θ * z i).re = t} ⊆ W) :
    ∃ ε > 0, {z : EuclideanSpace ℂ (Fin n) | (∀ l, z l ∈ cthickening ε (C l)) ∧
      |(θ * z i).re - t| ≤ ε} ⊆ W := by
  let V : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun m =>
    {z | (∀ l, z l ∈ cthickening (1 / ((m : ℝ) + 1)) (C l)) ∧
      |(θ * z i).re - t| ≤ 1 / ((m : ℝ) + 1)}
  have hLc := continuous_linForm (n := n) i θ
  have hVc : ∀ m, IsCompact (V m) := by
    intro m
    refine (Cousin.isCompact_coord_pi fun l => (hC l).cthickening).of_isClosed_subset ?_
      fun z hz => hz.1
    have h1 : IsClosed {z : EuclideanSpace ℂ (Fin n) |
        ∀ l, z l ∈ cthickening (1 / ((m : ℝ) + 1)) (C l)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun l => isClosed_cthickening.preimage (Cousin.continuous_coord l)
    exact h1.inter (isClosed_le (continuous_abs.comp (hLc.sub continuous_const))
      continuous_const)
  have hVd : Directed (· ⊇ ·) V := by
    refine directed_of_isDirected_le fun m m' hmm' => ?_
    have hle : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm' 1)
    intro z hz
    exact ⟨fun l => cthickening_mono hle _ (hz.1 l), hz.2.trans hle⟩
  have hVW : ∀ x ∈ ⋂ m, V m, W ∈ 𝓝 x := by
    intro x hx
    rw [mem_iInter] at hx
    refine hW.mem_nhds (hKW ⟨fun l => ?_, ?_⟩)
    · rw [← (hC l).isClosed.closure_eq, closure_eq_iInter_cthickening]
      simp only [mem_iInter]
      intro δ hδ
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      exact cthickening_mono hm.le _ ((hx m).1 l)
    · by_contra hne
      have hpos : 0 < |(θ * x i).re - t| := abs_pos.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact absurd (hx m).2 (not_le.2 hm)
  obtain ⟨m, hmW⟩ := exists_subset_nhds_of_isCompact hVd hVc hVW
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hmW⟩

/-- The closed slab `{z_l ∈ cthickening r (C_l), |Re(θ z_i) - t| ≤ δ}` is a compact convex
product set. -/
theorem exists_convex_closedSlab (i : Fin n) (θ : ℂ) (t : ℝ) {C : Fin n → Set ℂ}
    (hC : ∀ l, IsCompact (C l)) (hconv : ∀ l, Convex ℝ (C l)) (r δ : ℝ) :
    ∃ C' : Fin n → Set ℂ, (∀ l, IsCompact (C' l)) ∧ (∀ l, Convex ℝ (C' l)) ∧
      {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l} =
        {z | (∀ l, z l ∈ cthickening r (C l)) ∧ |(θ * z i).re - t| ≤ δ} := by
  classical
  refine ⟨fun l => if l = i then cthickening r (C i) ∩ {w | |(θ * w).re - t| ≤ δ}
    else cthickening r (C l), fun l => ?_, fun l => ?_, ?_⟩
  · by_cases hl : l = i
    · subst hl
      simp only [if_true]
      refine (hC l).cthickening.inter_right ?_
      exact isClosed_le (continuous_abs.comp ((continuous_re.comp
        (continuous_const.mul continuous_id)).sub continuous_const)) continuous_const
    · simp only [hl, if_false]
      exact (hC l).cthickening
  · by_cases hl : l = i
    · subst hl
      simp only [if_true]
      refine ((hconv l).cthickening _).inter ?_
      have : {w : ℂ | |(θ * w).re - t| ≤ δ} =
          {w : ℂ | (θ * w).re ≤ t + δ} ∩ {w : ℂ | t - δ ≤ (θ * w).re} := by
        ext w; simp only [mem_ofPred_eq, mem_inter_iff, abs_le]; constructor <;>
          rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [this]
      have hlin : IsLinearMap ℝ fun w : ℂ => (θ * w).re :=
        ⟨fun x y => by simp [mul_add], fun c x => by simp; ring⟩
      exact (convex_halfSpace_le hlin _).inter (convex_halfSpace_ge hlin _)
    · simp only [hl, if_false]
      exact (hconv l).cthickening _
  · ext z
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨fun l => ?_, ?_⟩
      · by_cases hl : l = i
        · subst hl; have := h l; simp only [if_true] at this; exact this.1
        · have := h l; simp only [hl, if_false] at this; exact this
      · have := h i; simp only [if_true] at this; exact this.2
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = i
      · subst hl; simp only [if_true]; exact ⟨h1 l, h2⟩
      · simp only [hl, if_false]; exact h1 l

/-! ### The factorization -/

/-- **Cartan's matrix lemma for unipotent products.** Let `Q = ∏ C_l` be a compact convex
product set and `K = Q ∩ {Re(θ z_i) = t}`. If `T`, `S` are holomorphic matrices on an open set
`W ⊇ K`, then there is `ε > 0` such that, on the slab `slab C ε` (contained in `W`),
`[[1, T], [0, 1]] [[1, 0], [-S, 1]] = B' B''⁻¹` with `B'` holomorphic and invertible on the left
side `leftSide C ε ⊇ Q ∩ {Re(θ z_i) ≤ t}` and `B''` holomorphic and invertible on the right side
`rightSide C ε ⊇ Q ∩ {Re(θ z_i) ≥ t}`. -/
theorem exists_factor_unipotent (i : Fin n) (θ : ℂ) (t : ℝ) {C : Fin n → Set ℂ}
    (hC : ∀ l, IsCompact (C l)) (hconv : ∀ l, Convex ℝ (C l)) (a b : Type) [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hKW : {z | (∀ l, z l ∈ C l) ∧ (θ * z i).re = t} ⊆ W)
    {T : EuclideanSpace ℂ (Fin n) → Matrix a b ℂ} {S : EuclideanSpace ℂ (Fin n) → Matrix b a ℂ}
    (hT : MatHolOn T W) (hS : MatHolOn S W) :
    ∃ ε > 0, slab C ε i θ t ε ⊆ W ∧
      ∃ B' B'' : EuclideanSpace ℂ (Fin n) → Matrix (a ⊕ b) (a ⊕ b) ℂ,
        MatHolOn B' (leftSide C ε i θ t ε) ∧ MatHolOn B'' (rightSide C ε i θ t ε) ∧
        (∀ z ∈ leftSide C ε i θ t ε, (B' z).det ≠ 0) ∧
        (∀ z ∈ rightSide C ε i θ t ε, (B'' z).det ≠ 0) ∧
        ∀ z ∈ slab C ε i θ t ε, upperU (T z) * lowerU (-S z) = B' z * (B'' z)⁻¹ := by
  classical
  obtain ⟨ε₀, hε₀, hslabW⟩ := exists_closedSlab_subset i θ t hC hW hKW
  set ε : ℝ := ε₀ / 2 with hεdef
  have hε : 0 < ε := by positivity
  -- the closed convex product neighbourhood
  obtain ⟨C', hC'c, hC'conv, hQ'eq⟩ := exists_convex_closedSlab i θ t hC hconv (2 * ε) ε
  have hQ'W : {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l} ⊆ W := by
    rw [hQ'eq]
    refine fun z hz => hslabW ⟨fun l => ?_, hz.2.trans (by linarith)⟩
    rw [show ε₀ = 2 * ε by rw [hεdef]; ring]
    exact hz.1 l
  have hslab2 : slab C (2 * ε) i θ t ε ⊆ {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l} := by
    rw [hQ'eq]
    exact fun z hz => ⟨fun l => thickening_subset_cthickening _ _ (hz.1 l), hz.2.le⟩
  -- the Newton constant
  obtain ⟨η, hη, hNewton⟩ := exists_factor_near_one i θ t hC (by positivity : 0 < 2 * ε) hε
    (a ⊕ b)
  -- bound for `S` on the compact neighbourhood
  have hQ'c : IsCompact {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l} :=
    Cousin.isCompact_coord_pi hC'c
  have hScont : ContinuousOn (fun z => mnorm (S z)) W := by
    have : ContinuousOn S W := continuousOn_pi.2 fun x => continuousOn_pi.2 fun y =>
      (hS x y).continuousOn
    exact continuous_mnorm.comp_continuousOn this
  obtain ⟨BS₀, hBS₀⟩ := hQ'c.exists_bound_of_continuousOn (hScont.mono hQ'W)
  set BS : ℝ := max BS₀ 0 with hBSdef
  have hBS0 : 0 ≤ BS := le_max_right _ _
  have hBS : ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l}, mnorm (S z) ≤ BS :=
    fun z hz => (le_abs_self _).trans ((hBS₀ z hz).trans (le_max_left _ _))
  set κ : ℝ := Fintype.card a + Fintype.card b + BS with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  set e : ℝ := min 1 (η / (1 + (κ + 1) * κ)) with hedef
  have he0 : 0 < e := lt_min one_pos (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heη : e + (κ + e) * e * κ ≤ η := by
    have h1 : e * (1 + (κ + 1) * κ) ≤ η := by
      have := min_le_right 1 (η / (1 + (κ + 1) * κ))
      rw [← hedef, le_div_iff₀ (by positivity)] at this
      exact this
    nlinarith [mul_nonneg he0.le hκ0]
  -- polynomial approximations of the entries
  set e' : ℝ := e / (Fintype.card a * Fintype.card b + 1) with he'def
  have he' : 0 < e' := by positivity
  have happT : ∀ x y, ∃ q : MvPolynomial (Fin n) ℂ, ∀ z : EuclideanSpace ℂ (Fin n),
      (∀ l, z l ∈ C' l) → ‖T z x y - MvPolynomial.eval (fun l => z l) q‖ < e' :=
    fun x y => Runge.exists_mvPolynomial_approx hC'c hC'conv hW hQ'W (hT x y) he'
  have happS : ∀ y x, ∃ q : MvPolynomial (Fin n) ℂ, ∀ z : EuclideanSpace ℂ (Fin n),
      (∀ l, z l ∈ C' l) → ‖S z y x - MvPolynomial.eval (fun l => z l) q‖ < e' :=
    fun y x => Runge.exists_mvPolynomial_approx hC'c hC'conv hW hQ'W (hS y x) he'
  choose qT hqT using happT
  choose qS hqS using happS
  set T' : EuclideanSpace ℂ (Fin n) → Matrix a b ℂ := fun z =>
    Matrix.of fun x y => MvPolynomial.eval (fun l => z l) (qT x y) with hT'def
  set S' : EuclideanSpace ℂ (Fin n) → Matrix b a ℂ := fun z =>
    Matrix.of fun y x => MvPolynomial.eval (fun l => z l) (qS y x) with hS'def
  have hcard : (Fintype.card a * Fintype.card b : ℝ) * e' ≤ e := by
    rw [he'def, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hcard' : (Fintype.card b * Fintype.card a : ℝ) * e' ≤ e := by
    rw [show (Fintype.card b * Fintype.card a : ℝ) = Fintype.card a * Fintype.card b by ring]
    exact hcard
  have hTe : ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l}, mnorm (T z - T' z) ≤ e :=
    fun z hz => (mnorm_le_of_forall_entry_le fun x y => by
      simpa [hT'def] using (hqT x y z hz).le).trans hcard
  have hSe : ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C' l}, mnorm (S' z - S z) ≤ e :=
    fun z hz => (mnorm_le_of_forall_entry_le fun y x => by
      rw [Matrix.sub_apply, norm_sub_rev]; simpa [hS'def] using (hqS y x z hz).le).trans hcard'
  have hT'h : MatHolOn T' univ := fun x y => by
    simpa [hT'def] using (differentiable_eval_mvPolynomial (qT x y)).differentiableOn
  have hS'h : MatHolOn S' univ := fun y x => by
    simpa [hS'def] using (differentiable_eval_mvPolynomial (qS y x)).differentiableOn
  -- the corrected matrix `H⁻¹ A`
  set A' : EuclideanSpace ℂ (Fin n) → Matrix (a ⊕ b) (a ⊕ b) ℂ := fun z =>
    lowerU (S' z) * upperU (-T' z) * (upperU (T z) * lowerU (-S z)) with hA'def
  have hA'h : MatHolOn A' W := by
    have h1 := matHolOn_lowerU (hS'h.mono (subset_univ W))
    have h2 := matHolOn_upperU (hT'h.mono (subset_univ W)).neg
    have h3 := matHolOn_upperU hT
    have h4 := matHolOn_lowerU hS.neg
    exact (h1.mul h2).mul (h3.mul h4)
  have hA'b : ∀ z ∈ slab C (2 * ε) i θ t ε, mnorm (A' z - 1) ≤ η := by
    intro z hz
    have hzQ := hslab2 hz
    exact (mnorm_approx_sub_one_le (T z) (T' z) (S z) (S' z) (hTe z hzQ) (hSe z hzQ)
      (by rw [hκdef]; linarith [hBS z hzQ])).trans heη
  obtain ⟨B'₀, B''₀, hB'h, hB''h, hB'd, hB''d, hfac⟩ := hNewton A'
    (hA'h.mono ((slab_mono (le_refl _)).trans (hslab2.trans hQ'W))) hA'b
  have h2ε : 2 * ε / 2 = ε := by ring
  rw [h2ε] at hB'h hB''h hB'd hB''d hfac
  refine ⟨ε, hε, fun z hz => hQ'W (hslab2 (slab_mono (by linarith) hz)), fun z =>
    upperU (T' z) * lowerU (-S' z) * B'₀ z, B''₀, ?_, hB''h, fun z hz => ?_, hB''d,
    fun z hz => ?_⟩
  · exact ((matHolOn_upperU (hT'h.mono (subset_univ _))).mul
      (matHolOn_lowerU (hS'h.mono (subset_univ _)).neg)).mul hB'h
  · rw [det_mul, det_mul, det_upperU, det_lowerU, one_mul, one_mul]
    exact hB'd z hz
  · have hA' := hfac z hz
    have hinv := upperU_mul_lowerU_mul_inv (T' z) (S' z)
    calc upperU (T z) * lowerU (-S z)
        = (upperU (T' z) * lowerU (-S' z) * (lowerU (S' z) * upperU (-T' z))) *
            (upperU (T z) * lowerU (-S z)) := by rw [hinv, Matrix.one_mul]
      _ = upperU (T' z) * lowerU (-S' z) * A' z := by simp only [hA'def]; noncomm_ring
      _ = upperU (T' z) * lowerU (-S' z) * B'₀ z * (B''₀ z)⁻¹ := by rw [hA']; noncomm_ring

end

end Hironaka.Analytic.GAGA.Core.Cartan
