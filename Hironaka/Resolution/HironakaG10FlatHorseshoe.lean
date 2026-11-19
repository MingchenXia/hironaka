import Hironaka.Resolution.HironakaG10FlatPresentationChange
import Hironaka.Resolution.HironakaG10FlatResolutionPkg

/-! # Horseshoe resolutions of extensions

Douady 1966, §7 n° 1 Prop. 3: if `0 → 𝓕' → 𝓕 → 𝓕'' → 0` is exact and `P'`, `P''` are free resolutions
of `𝓕'`, `𝓕''`, the **horseshoe** chain `R_k = P'_k ⊕ P''_k` with triangular differential
`[d'_k  φ_k; 0  d''_k]` (`d'_k φ_{k+1} + φ_k d''_{k+1} = 0`) is a resolution, privileged wherever `P'` and
`P''` are.

* `matExact_fromBlocks` (any ring): a triangular chain of two exact chains is exact.
* Germ and value matrices of block matrices (`germMat_fromBlocks`, `germMat_mul`, …).
* `liftCols`: columns that are germ combinations of the columns of `G` at `x` are `G Φ` near `x`, with
  `Φ` holomorphic near `x` (`liftCols_spec`).
* `hsPhi`: the off-diagonal blocks, built inductively near a point from `φ₀` (`hsPhi_spec`).
* `exactStartOn_hsFin`: the horseshoe chain (bases relabelled to `Fin`) is an exact start in every degree
  on an open set where `P'`, `P''` are and the identities hold.
* `splitBy_triMatrix`, **`splitBy_hsFin`**: its `B(K)`-complex is split wherever those of `P'` and `P''`
  are (`HironakaG10FlatSplitComplex.SplitBy.tri`).
BP: hironaka-g10-flat-horseshoe.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatHorseshoe
noncomputable section
open OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart HironakaG10FlatGermChain
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatSplitComplex HironakaG10FlatPrivilegedNbhd
  HironakaG10FlatResolutionPkg HironakaG10FlatTriangularExtension Matrix

/-! ## Triangular chains over a ring -/

section Alg
variable {S : Type*} [Ring S] {A0 A1 A2 C0 C1 C2 : Type*} [Fintype A1] [Fintype A2] [Fintype C1]
  [Fintype C2]

/-- **A triangular chain of two exact chains is exact.** -/
theorem matExact_fromBlocks {a1 : Matrix A0 A1 S} {h1 : Matrix A0 C1 S} {c1 : Matrix C0 C1 S}
    {a2 : Matrix A1 A2 S} {h2 : Matrix A1 C2 S} {c2 : Matrix C1 C2 S}
    (hφ : a1 * h2 + h1 * c2 = 0) (hA : MatExact a2 a1) (hC : MatExact c2 c1) :
    MatExact (fromBlocks a2 h2 0 c2) (fromBlocks a1 h1 0 c1) := by
  intro v hv
  rw [fromBlocks_mulVec, zero_mulVec, zero_add] at hv
  have e1 : a1 *ᵥ (v ∘ Sum.inl) + h1 *ᵥ (v ∘ Sum.inr) = 0 := by
    simpa using congrArg (· ∘ Sum.inl) hv
  have e2 : c1 *ᵥ (v ∘ Sum.inr) = 0 := by simpa using congrArg (· ∘ Sum.inr) hv
  obtain ⟨y', hy'⟩ := hC _ e2
  have hh : h1 * c2 = -(a1 * h2) := eq_neg_of_add_eq_zero_right hφ
  obtain ⟨x', hx'⟩ := hA (v ∘ Sum.inl - h2 *ᵥ y') (by
    rw [mulVec_sub, mulVec_mulVec, ← e1, ← hy', mulVec_mulVec, hh, neg_mulVec]
    abel)
  refine ⟨Sum.elim x' y', ?_⟩
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, hx', hy',
    sub_add_cancel, Sum.elim_comp_inl_inr]

end Alg

/-! ## Germ and value matrices -/

section Germ
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem germMat_fromBlocks {ι κ ι' κ' : Type*} (y : X) (a : ι → ι' → X → ℂ) (h : ι → κ' → X → ℂ)
    (c : κ → κ' → X → ℂ) :
    germMat y (fromBlocks a h 0 c : Matrix (ι ⊕ κ) (ι' ⊕ κ') (X → ℂ)) =
      fromBlocks (germMat y a) (germMat y h) 0 (germMat y c) := by
  refine Matrix.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact germAt_zero y
  · rfl

theorem germMat_mul {ι κ μ : Type*} [Fintype κ] {y : X} {F : ι → κ → X → ℂ} {G : κ → μ → X → ℂ}
    (hF : ∀ i j, HolAt (F i j) y) (hG : ∀ j k, HolAt (G j k) y) :
    germMat y F * germMat y G = germMat y (fun i k x => ∑ j, F i j x * G j k x) := by
  refine Matrix.ext fun i k => ?_
  simp only [Matrix.mul_apply, germMat, Matrix.of_apply]
  rw [germAt_sum _ fun j _ => (hF i j).mul (hG j k)]
  exact Finset.sum_congr rfl fun j _ => (germAt_mul (hF i j) (hG j k)).symm

theorem germMat_add {ι κ : Type*} {y : X} {F G : ι → κ → X → ℂ} (hF : ∀ i j, HolAt (F i j) y)
    (hG : ∀ i j, HolAt (G i j) y) :
    germMat y F + germMat y G = germMat y (fun i j x => F i j x + G i j x) := by
  refine Matrix.ext fun i j => ?_
  exact (germAt_add (hF i j) (hG i j)).symm

theorem germMat_eq_zero {ι κ : Type*} {y : X} {F : ι → κ → X → ℂ} (hF : ∀ i j, HolAt (F i j) y)
    (h : ∀ᶠ x in 𝓝 y, ∀ i j, F i j x = 0) : germMat y F = 0 := by
  refine Matrix.ext fun i j => ?_
  exact (germAt_eq_zero_iff (hF i j)).2 (h.mono fun x hx => hx i j)

/-- The matrix of values at `x`. -/
def valMat {ι κ : Type*} (x : X) (F : ι → κ → X → ℂ) : Matrix ι κ ℂ := Matrix.of fun i j => F i j x

theorem valMat_fromBlocks {ι κ ι' κ' : Type*} (x : X) (a : ι → ι' → X → ℂ) (h : ι → κ' → X → ℂ)
    (c : κ → κ' → X → ℂ) :
    valMat x (fromBlocks a h 0 c : Matrix (ι ⊕ κ) (ι' ⊕ κ') (X → ℂ)) =
      fromBlocks (valMat x a) (valMat x h) 0 (valMat x c) := by
  ext (i | i) (j | j) <;> rfl

end Germ

/-! ## Lifting columns near a point -/

section Lift
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {ι κ μ : Type*} [Fintype ι] [Fintype κ]
  [Fintype μ]

/-- A matrix `Φ` holomorphic near `x` with `G Φ = V` near `x`, if one exists (else `0`). -/
def liftCols (G : ι → κ → X → ℂ) (V : ι → μ → X → ℂ) (x : X) : κ → μ → X → ℂ :=
  haveI := Classical.propDecidable
  if h : ∃ Φ : κ → μ → X → ℂ, (∀ j k, HolAt (Φ j k) x) ∧
      ∀ᶠ y in 𝓝 x, ∀ i k, ∑ j, G i j y * Φ j k y = V i k y then h.choose else 0

theorem liftCols_spec {G : ι → κ → X → ℂ} {V : ι → μ → X → ℂ} {x : X}
    (h : ∀ k, IsCombinationAt (columns G) x (fun i => V i k)) :
    (∀ j k, HolAt (liftCols G V x j k) x) ∧
      ∀ᶠ y in 𝓝 x, ∀ i k, ∑ j, G i j y * liftCols G V x j k y = V i k y := by
  have hex : ∃ Φ : κ → μ → X → ℂ, (∀ j k, HolAt (Φ j k) x) ∧
      ∀ᶠ y in 𝓝 x, ∀ i k, ∑ j, G i j y * Φ j k y = V i k y := by
    choose c hc hcV using h
    refine ⟨fun j k => c k j, fun j k => hc k j, ?_⟩
    filter_upwards [eventually_all.2 fun k => eventually_all.2 fun i => hcV k i] with y hy i k
    rw [hy k i]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  unfold liftCols
  rw [dif_pos hex]
  exact hex.choose_spec

end Lift

/-! ## The off-diagonal blocks -/

section Phi
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r' r'' : ℕ → ℕ}
  (d' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ)
  (d'' : (k : ℕ) → Fin (r'' k) → Fin (r'' (k + 1)) → X → ℂ)
  (φ0 : Fin (r' 0) → Fin (r'' 1) → X → ℂ) (x : X)

/-- The off-diagonal blocks `φ_k : P''_{k+1} → P'_k` of the horseshoe, built near `x` from `φ₀`:
`d'_k φ_{k+1} = −φ_k d''_{k+1}`. -/
def hsPhi : (k : ℕ) → Fin (r' k) → Fin (r'' (k + 1)) → X → ℂ
  | 0 => φ0
  | k + 1 => liftCols (d' k) (fun i j y => -∑ l, hsPhi k i l y * d'' (k + 1) l j y) x

variable {d' d'' φ0 x}

/-- **The off-diagonal blocks exist near `x`**: if the first lifting problem is solvable, `P'` is
exact at `x` and `P''` composes to zero near `x`, every lifting problem is solvable. -/
theorem hsPhi_sol (hφ0 : ∀ i j, HolAt (φ0 i j) x) (hd'' : ∀ k i j, HolAt (d'' k i j) x)
    (hex' : ∀ k (a : Fin (r' (k + 1)) → X → ℂ), IsRelationAt (d' k) x a →
      IsCombinationAt (columns (d' (k + 1))) x a)
    (hc'' : ∀ k, ∀ᶠ y in 𝓝 x, ∀ i l, ∑ j, d'' k i j y * d'' (k + 1) j l y = 0)
    (h0 : ∀ j, IsCombinationAt (columns (d' 0)) x
      (fun i y => -∑ l, φ0 i l y * d'' 1 l j y)) :
    ∀ k, (∀ i j, HolAt (hsPhi d' d'' φ0 x k i j) x) ∧ ∀ j, IsCombinationAt (columns (d' k)) x
      (fun i y => -∑ l, hsPhi d' d'' φ0 x k i l y * d'' (k + 1) l j y) := by
  intro k
  induction k with
  | zero => exact ⟨hφ0, h0⟩
  | succ k ih =>
    obtain ⟨hhol, hsol⟩ := ih
    obtain ⟨hhol', hid⟩ := liftCols_spec hsol
    refine ⟨hhol', fun j => hex' k _ ⟨fun l => (HolAt.fintype_sum fun m =>
      (hhol' l m).mul (hd'' (k + 2) m j)).neg, fun i => ?_⟩⟩
    filter_upwards [hid, hc'' (k + 1)] with y hy hcy
    have e1 : ∀ m, ∑ l, d' k i l y * hsPhi d' d'' φ0 x (k + 1) l m y =
        -∑ n, hsPhi d' d'' φ0 x k i n y * d'' (k + 1) n m y := fun m => hy i m
    calc ∑ l, (-∑ m, hsPhi d' d'' φ0 x (k + 1) l m y * d'' (k + 2) m j y) * d' k i l y
        = -∑ m, (∑ l, d' k i l y * hsPhi d' d'' φ0 x (k + 1) l m y) * d'' (k + 2) m j y := by
          simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ n, hsPhi d' d'' φ0 x k i n y * ∑ m, d'' (k + 1) n m y * d'' (k + 2) m j y := by
          simp only [e1, neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := Finset.sum_eq_zero fun n _ => by rw [hcy n j, mul_zero]

/-- The horseshoe identities `d'_k φ_{k+1} + φ_k d''_{k+1} = 0` near `x`. -/
theorem hsPhi_spec (hφ0 : ∀ i j, HolAt (φ0 i j) x) (hd'' : ∀ k i j, HolAt (d'' k i j) x)
    (hex' : ∀ k (a : Fin (r' (k + 1)) → X → ℂ), IsRelationAt (d' k) x a →
      IsCombinationAt (columns (d' (k + 1))) x a)
    (hc'' : ∀ k, ∀ᶠ y in 𝓝 x, ∀ i l, ∑ j, d'' k i j y * d'' (k + 1) j l y = 0)
    (h0 : ∀ j, IsCombinationAt (columns (d' 0)) x
      (fun i y => -∑ l, φ0 i l y * d'' 1 l j y)) (k : ℕ) :
    (∀ i j, HolAt (hsPhi d' d'' φ0 x k i j) x) ∧
      ∀ᶠ y in 𝓝 x, ∀ i j, ∑ l, d' k i l y * hsPhi d' d'' φ0 x (k + 1) l j y +
        ∑ l, hsPhi d' d'' φ0 x k i l y * d'' (k + 1) l j y = 0 := by
  obtain ⟨hhol, hsol⟩ := hsPhi_sol hφ0 hd'' hex' hc'' h0 k
  refine ⟨hhol, ?_⟩
  filter_upwards [(liftCols_spec hsol).2] with y hy i j
  have := hy i j
  show ∑ l, d' k i l y * liftCols (d' k)
    (fun i j y => -∑ l, hsPhi d' d'' φ0 x k i l y * d'' (k + 1) l j y) x l j y + _ = 0
  rw [this, neg_add_cancel]

end Phi

/-! ## The horseshoe chain -/

section Chain
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r' r'' : ℕ → ℕ}
  {d' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ}
  {d'' : (k : ℕ) → Fin (r'' k) → Fin (r'' (k + 1)) → X → ℂ}
  {φ : (k : ℕ) → Fin (r' k) → Fin (r'' (k + 1)) → X → ℂ}

/-- The ranks `r' k + r'' k` of the horseshoe. -/
def hsRank (r' r'' : ℕ → ℕ) (k : ℕ) : ℕ := r' k + r'' k

/-- `Fin (r' k + r'' k) ≃ Fin (r' k) ⊕ Fin (r'' k)`. -/
def eH (r' r'' : ℕ → ℕ) (k : ℕ) : Fin (hsRank r' r'' k) ≃ Fin (r' k) ⊕ Fin (r'' k) :=
  finSumFinEquiv.symm

/-- The block `[d'_k  φ_k; 0  d''_k]`. -/
def hsBlock (d' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ)
    (d'' : (k : ℕ) → Fin (r'' k) → Fin (r'' (k + 1)) → X → ℂ)
    (φ : (k : ℕ) → Fin (r' k) → Fin (r'' (k + 1)) → X → ℂ) (k : ℕ) :
    Matrix (Fin (r' k) ⊕ Fin (r'' k)) (Fin (r' (k + 1)) ⊕ Fin (r'' (k + 1))) (X → ℂ) :=
  fromBlocks (d' k) (φ k) 0 (d'' k)

/-- **The horseshoe chain**, bases relabelled to `Fin`. -/
def hsFin (d' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ)
    (d'' : (k : ℕ) → Fin (r'' k) → Fin (r'' (k + 1)) → X → ℂ)
    (φ : (k : ℕ) → Fin (r' k) → Fin (r'' (k + 1)) → X → ℂ) (k : ℕ) :
    Fin (hsRank r' r'' k) → Fin (hsRank r' r'' (k + 1)) → X → ℂ :=
  fun i j => hsBlock d' d'' φ k (eH r' r'' k i) (eH r' r'' (k + 1) j)

theorem hsFin_hol {V : Set X} (hd' : ∀ k i j, DifferentiableOn ℂ (d' k i j) V)
    (hd'' : ∀ k i j, DifferentiableOn ℂ (d'' k i j) V) (hφ : ∀ k i j, DifferentiableOn ℂ (φ k i j) V)
    (k : ℕ) (i : Fin (hsRank r' r'' k)) (j : Fin (hsRank r' r'' (k + 1))) :
    DifferentiableOn ℂ (hsFin d' d'' φ k i j) V := by
  show DifferentiableOn ℂ (fromBlocks (d' k) (φ k) 0 (d'' k) (eH r' r'' k i) (eH r' r'' (k + 1) j)) V
  rcases eH r' r'' k i with i' | i' <;> rcases eH r' r'' (k + 1) j with j' | j'
  · exact hd' k i' j'
  · exact hφ k i' j'
  · exact differentiableOn_const (0 : ℂ)
  · exact hd'' k i' j'

/-- **The horseshoe chain is an exact start in every degree** on an open set where `P'`, `P''` are
exact starts in every degree and the horseshoe identities hold. -/
theorem exactStartOn_hsFin {V : Set X} (hV : IsOpen V) (hd' : ∀ k, ExactStartOn V (d' (k + 1)) (d' k))
    (hd'' : ∀ k, ExactStartOn V (d'' (k + 1)) (d'' k)) (hφ : ∀ k i j, DifferentiableOn ℂ (φ k i j) V)
    (hid : ∀ k, ∀ y ∈ V, ∀ i j, ∑ l, d' k i l y * φ (k + 1) l j y +
      ∑ l, φ k i l y * d'' (k + 1) l j y = 0) (k : ℕ) :
    ExactStartOn V (hsFin d' d'' φ (k + 1)) (hsFin d' d'' φ k) := by
  have hd'h : ∀ k i j, DifferentiableOn ℂ (d' k i j) V := fun k => (hd' k).holF
  have hd''h : ∀ k i j, DifferentiableOn ℂ (d'' k i j) V := fun k => (hd'' k).holF
  refine exactStartOn_of_matExact hV (hsFin_hol hd'h hd''h hφ k) (hsFin_hol hd'h hd''h hφ (k + 1))
    (fun i l y hy => ?_) (fun y hy => ?_)
  · have hz : valMat y (hsBlock d' d'' φ k) * valMat y (hsBlock d' d'' φ (k + 1)) = 0 := by
      rw [hsBlock, hsBlock, valMat_fromBlocks, valMat_fromBlocks, fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      have h1 : valMat y (d' k) * valMat y (d' (k + 1)) = 0 :=
        Matrix.ext fun i l => (hd' k).comp i l y hy
      have h2 : valMat y (d' k) * valMat y (φ (k + 1)) + valMat y (φ k) * valMat y (d'' (k + 1)) = 0 :=
        Matrix.ext fun i j => hid k y hy i j
      have h3 : valMat y (d'' k) * valMat y (d'' (k + 1)) = 0 :=
        Matrix.ext fun i l => (hd'' k).comp i l y hy
      rw [h1, h2, h3, fromBlocks_zero]
    have := congrFun (congrFun hz (eH r' r'' k i)) (eH r' r'' (k + 1 + 1) l)
    rw [Matrix.mul_apply] at this
    refine Eq.trans ?_ this
    exact Equiv.sum_comp (eH r' r'' (k + 1)) (fun j => valMat y (hsBlock d' d'' φ k) (eH r' r'' k i) j *
      valMat y (hsBlock d' d'' φ (k + 1)) j (eH r' r'' (k + 1 + 1) l))
  · have hol : ∀ {ι κ : Type} (F : ι → κ → X → ℂ), (∀ i j, DifferentiableOn ℂ (F i j) V) →
        ∀ i j, HolAt (F i j) y := fun F hF i j => holAt_of_differentiableOn hV (hF i j) hy
    have hg : ∀ k, germMat y (hsFin d' d'' φ k) = (fromBlocks (germMat y (d' k)) (germMat y (φ k)) 0
        (germMat y (d'' k))).submatrix (eH r' r'' k) (eH r' r'' (k + 1)) := fun k => by
      rw [← germMat_fromBlocks]
      rfl
    have hφg : germMat y (d' k) * germMat y (φ (k + 1)) + germMat y (φ k) * germMat y (d'' (k + 1)) = 0 := by
      rw [germMat_mul (hol _ (hd'h k)) (hol _ (hφ (k + 1))), germMat_mul (hol _ (hφ k)) (hol _ (hd''h (k + 1))),
        germMat_add (fun i j => HolAt.fintype_sum fun l => (hol _ (hd'h k) i l).mul (hol _ (hφ (k + 1)) l j))
          (fun i j => HolAt.fintype_sum fun l => (hol _ (hφ k) i l).mul (hol _ (hd''h (k + 1)) l j))]
      refine germMat_eq_zero (fun i j => (HolAt.fintype_sum fun l =>
        (hol _ (hd'h k) i l).mul (hol _ (hφ (k + 1)) l j)).add (HolAt.fintype_sum fun l =>
          (hol _ (hφ k) i l).mul (hol _ (hd''h (k + 1)) l j))) ?_
      filter_upwards [hV.mem_nhds hy] with z hz i j
      exact hid k z hz i j
    rw [hg, hg]
    exact matExact_submatrix (matExact_fromBlocks hφg (matExact_of_exactStartOn hV (hd' k) hy)
      (matExact_of_exactStartOn hV (hd'' k) hy)) (eH r' r'' k) (eH r' r'' (k + 1)) (eH r' r'' (k + 2))

end Chain

/-! ## Splittings of horseshoe chains -/

section Split
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- **Triangular matrix chains of two split chains are split** (`SplitBy.tri` through `sumCLE`). -/
theorem splitBy_triMatrix {A' C' : ℕ → Type*} [∀ k, Fintype (A' k)] [∀ k, Fintype (C' k)]
    {a : (k : ℕ) → A' k → A' (k + 1) → R} {h : (k : ℕ) → A' k → C' (k + 1) → R}
    {c : (k : ℕ) → C' k → C' (k + 1) → R} {m : ℕ}
    {tA : (k : ℕ) → (A' k → R) →L[ℂ] (A' (k + 1) → R)} {tC : (k : ℕ) → (C' k → R) →L[ℂ] (C' (k + 1) → R)}
    (hA : SplitBy (fun k => matrixOperator (a k)) tA m) (hC : SplitBy (fun k => matrixOperator (c k)) tC m)
    (hφ : ∀ k < m, ∀ y, matrixOperator (a k) (matrixOperator (h (k + 1)) y) +
      matrixOperator (h k) (matrixOperator (c (k + 1)) y) = 0) :
    ∃ t : (k : ℕ) → (A' k ⊕ C' k → R) →L[ℂ] (A' (k + 1) ⊕ C' (k + 1) → R),
      SplitBy (fun k => matrixOperator (triMatrix (a k) (h k) (c k))) t m := by
  have htri := SplitBy.tri (φ := fun k => matrixOperator (h k)) hA hC hφ
  refine ⟨_, htri.of_dominated'
    (fun k => ((sumCLE (R := R) (A' k) (C' k)).symm : _ →L[ℂ] (A' k ⊕ C' k → R)))
    (fun k => ((sumCLE (R := R) (A' k) (C' k)) : (A' k ⊕ C' k → R) →L[ℂ] _)) (fun _ => 0)
    (fun k x => ?_) (fun k y => ?_) (fun k _ y => ?_)⟩
  · simp only [ContinuousLinearEquiv.coe_coe]
    rw [matrixOperator_triMatrix_eq, ContinuousLinearEquiv.apply_symm_apply]
  · simp only [ContinuousLinearEquiv.coe_coe]
    rw [matrixOperator_triMatrix]
  · simp

end Split

section SplitHs
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {r' r'' : ℕ → ℕ}
  {d' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ}
  {d'' : (k : ℕ) → Fin (r'' k) → Fin (r'' (k + 1)) → X → ℂ}
  {φ : (k : ℕ) → Fin (r' k) → Fin (r'' (k + 1)) → X → ℂ}

/-- Identities on `V ⊇ K` of holomorphic matrices give identities of the `B(K)`-operators. -/
theorem restrict_identity (K : Set X) [CompactSpace K] {V : Set X} (hKV : K ⊆ V)
    {ι κ μ ν : Type*} [Fintype κ] [Fintype μ] [Fintype ν]
    {F : ι → κ → X → ℂ} {G : κ → ν → X → ℂ} {F' : ι → μ → X → ℂ} {G' : μ → ν → X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) V) (hG : ∀ i j, DifferentiableOn ℂ (G i j) V)
    (hF' : ∀ i j, DifferentiableOn ℂ (F' i j) V) (hG' : ∀ i j, DifferentiableOn ℂ (G' i j) V)
    (hid : ∀ y ∈ V, ∀ i j, ∑ l, F i l y * G l j y + ∑ l, F' i l y * G' l j y = 0)
    (v : ν → holSubalgebra K) :
    matrixOperator (restrictMatrix K hKV F hF) (matrixOperator (restrictMatrix K hKV G hG) v) +
      matrixOperator (restrictMatrix K hKV F' hF') (matrixOperator (restrictMatrix K hKV G' hG') v) =
        0 := by
  simp only [matrixOperator_apply_eq_mulVec, mulVec_mulVec, ← add_mulVec]
  have hz : Matrix.of (restrictMatrix K hKV F hF) * Matrix.of (restrictMatrix K hKV G hG) +
      Matrix.of (restrictMatrix K hKV F' hF') * Matrix.of (restrictMatrix K hKV G' hG') = 0 := by
    refine Matrix.ext fun i j => HironakaG10FlatPolydiscRemainderMap.ext_evalHom fun z => ?_
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply, map_add,
      map_sum, map_mul, map_zero]
    exact hid z (hKV z.2) i j
  rw [hz, zero_mulVec]

/-- The restricted horseshoe chain is the triangular chain of the restricted chains. -/
theorem restrict_hsFin (K : Set X) [CompactSpace K] {V : Set X} (hKV : K ⊆ V)
    (hd' : ∀ k i j, DifferentiableOn ℂ (d' k i j) V) (hd'' : ∀ k i j, DifferentiableOn ℂ (d'' k i j) V)
    (hφ : ∀ k i j, DifferentiableOn ℂ (φ k i j) V) (k : ℕ) (i : Fin (hsRank r' r'' k))
    (j : Fin (hsRank r' r'' (k + 1))) :
    restrictMatrix K hKV (hsFin d' d'' φ k) (hsFin_hol hd' hd'' hφ k) i j =
      triMatrix (restrictMatrix K hKV (d' k) (hd' k)) (restrictMatrix K hKV (φ k) (hφ k))
        (restrictMatrix K hKV (d'' k) (hd'' k)) (eH r' r'' k i) (eH r' r'' (k + 1) j) := by
  refine HironakaG10FlatPolydiscRemainderMap.ext_evalHom fun z => ?_
  show fromBlocks (d' k) (φ k) 0 (d'' k) (eH r' r'' k i) (eH r' r'' (k + 1) j) z = _
  rcases eH r' r'' k i with i' | i' <;> rcases eH r' r'' (k + 1) j with j' | j' <;> rfl

/-- **The horseshoe chain is split on `K` wherever `P'` and `P''` are.** -/
theorem splitBy_hsFin (K : Set X) [CompactSpace K] {V : Set X} (hKV : K ⊆ V)
    (hd' : ∀ k i j, DifferentiableOn ℂ (d' k i j) V) (hd'' : ∀ k i j, DifferentiableOn ℂ (d'' k i j) V)
    (hφ : ∀ k i j, DifferentiableOn ℂ (φ k i j) V)
    (hid : ∀ k, ∀ y ∈ V, ∀ i j, ∑ l, d' k i l y * φ (k + 1) l j y +
      ∑ l, φ k i l y * d'' (k + 1) l j y = 0) {M : ℕ}
    {t' : (k : ℕ) → (Fin (r' k) → holSubalgebra K) →L[ℂ] (Fin (r' (k + 1)) → holSubalgebra K)}
    (ht' : SplitBy (chainOp fun k => restrictMatrix K hKV (d' k) (hd' k)) t' M)
    {t'' : (k : ℕ) → (Fin (r'' k) → holSubalgebra K) →L[ℂ] (Fin (r'' (k + 1)) → holSubalgebra K)}
    (ht'' : SplitBy (chainOp fun k => restrictMatrix K hKV (d'' k) (hd'' k)) t'' M) :
    ∃ t : (k : ℕ) → (Fin (hsRank r' r'' k) → holSubalgebra K) →L[ℂ]
        (Fin (hsRank r' r'' (k + 1)) → holSubalgebra K),
      SplitBy (chainOp fun k => restrictMatrix K hKV (hsFin d' d'' φ k) (hsFin_hol hd' hd'' hφ k)) t M := by
  obtain ⟨t1, ht1⟩ := splitBy_triMatrix (h := fun k => restrictMatrix K hKV (φ k) (hφ k)) ht' ht''
    (fun k _ y => restrict_identity K hKV (hd' k) (hφ (k + 1)) (hφ k) (hd'' (k + 1)) (hid k) y)
  obtain ⟨t2, ht2⟩ := splitBy_relabel (r' := hsRank r' r'') (eH r' r'') ht1
  refine ⟨t2, ?_⟩
  have hfun : (fun k => restrictMatrix K hKV (hsFin d' d'' φ k) (hsFin_hol hd' hd'' hφ k)) =
      fun k i j => triMatrix (restrictMatrix K hKV (d' k) (hd' k)) (restrictMatrix K hKV (φ k) (hφ k))
        (restrictMatrix K hKV (d'' k) (hd'' k)) (eH r' r'' k i) (eH r' r'' (k + 1) j) :=
    funext fun k => funext fun i => funext fun j => restrict_hsFin K hKV hd' hd'' hφ k i j
  rw [hfun]
  exact ht2

end SplitHs

end
end Hironaka.HironakaG10FlatHorseshoe
