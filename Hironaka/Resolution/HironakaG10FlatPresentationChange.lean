import Hironaka.Resolution.HironakaG10FlatGermChain
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Presentation change: a finite resolution starting with a prescribed presentation matrix

Douady 1966, §7: the privileged-neighbourhood statement (`HironakaG10FlatPrivilegedNbhd`) asks for
a finite free resolution whose FIRST matrix is the given presentation `A` of `𝓕 = coker A`. The
inductive steps of Th. 1 produce resolutions `P` of `𝓕` with a different first matrix `d₀` having the
same image (`im d₀ = im A` in `L₀`). This module changes the presentation (a Schanuel-type
normalization) by explicit block matrices.

Data (over any ring): a chain `d_k : P_{k+1} → P_k` with `d_k d_{k+1} = 0`, a matrix `A : L₁ → L₀ = P₀`
and `X : L₁ → P₁`, `Y : P₁ → L₁`, `Z : P₁ → P₂` with
`d₀ X = A`, `A Y = d₀`, `d₁ Z = X Y − 1` (`PCData.Good`). The new chain `Q` (`pcδ`) is
`Q₀ = L₀, Q₁ = L₁, Q₂ = P₂ ⊕ L₁, Q₃ = P₃ ⊕ P₁, Q_k = P_k (k ≥ 4)`, with
`δ₀ = A`, `δ₁ = [Y d₁ | 1 − Y X]`, `δ₂ = [d₂ Z; 0 Y]`, `δ₃ = [d₃; 0]`, `δ_k = d_k (k ≥ 4)`
(bases relabelled to `Fin` along `finSumFinEquiv`).

* `pc_comp`: `δ_k δ_{k+1} = 0`; **`pc_exact`**: if `P` is exact in every degree (`MatExact`), so is `Q`.
* Domination of `Q` by `P` (Douady's Prop. 2 mechanism): chain maps `f : P → Q`, `g : Q → P` and a
  homotopy `1 − f g = δ h + h δ` (`pc_hf`, `pc_hg`, `pc_hh`); **`splitBy_pc`**: over a normed ring,
  a splitting of `P` in degrees `< M` gives a splitting of `Q` in degrees `< M`.
* **`exists_presentationChange`** (holomorphic matrices on an open `U`): if `P` is exact on `U` in every
  degree, `Q` (with `δ₀ = A`) is exact on `U` in every degree, and every compact `K ⊆ U` on which the
  `B(K)`-complex of `P` is split is split for `Q`.
BP: hironaka-g10-flat-presentation-change.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatPresentationChange
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatGermChain
  HironakaG10FlatFrischHolomorphicFlattener Matrix

/-! ## Block identities -/

section Block
variable {T : Type*} [Ring T] {L0 L1 P1 P2 P3 P4 P5 : Type*} [Fintype L0] [Fintype L1] [Fintype P1]
  [Fintype P2] [Fintype P3] [Fintype P4] [Fintype P5] [DecidableEq L1] [DecidableEq P1]
  [DecidableEq P2] [DecidableEq P3]
  {d0 : Matrix L0 P1 T} {d1 : Matrix P1 P2 T} {d2 : Matrix P2 P3 T} {d3 : Matrix P3 P4 T}
  {d4 : Matrix P4 P5 T} {A : Matrix L0 L1 T} {X : Matrix P1 L1 T} {Y : Matrix L1 P1 T}
  {Z : Matrix P2 P1 T}

theorem blk_comp0 (h0 : d0 * X = A) (h1 : A * Y = d0) (c01 : d0 * d1 = 0) :
    A * fromCols (Y * d1) (1 - Y * X) = 0 := by
  rw [mul_fromCols, ← Matrix.mul_assoc, h1, c01, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, h1, h0, sub_self, fromCols_zero]

theorem blk_comp1 (h2 : d1 * Z = X * Y - 1) (c12 : d1 * d2 = 0) :
    fromCols (Y * d1) (1 - Y * X) * fromBlocks d2 Z 0 Y = 0 := by
  rw [fromCols_mul_fromBlocks, Matrix.mul_assoc, c12, Matrix.mul_zero, Matrix.mul_zero, add_zero,
    Matrix.mul_assoc, h2]
  have : Y * (X * Y - 1) + (1 - Y * X) * Y = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [this, fromCols_zero]

theorem blk_comp2 (c23 : d2 * d3 = 0) :
    fromBlocks d2 Z 0 Y * fromRows d3 (0 : Matrix P1 P4 T) = 0 := by
  rw [fromBlocks_mul_fromRows, c23, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    add_zero, fromRows_zero]

theorem blk_comp3 (c34 : d3 * d4 = 0) : fromRows d3 (0 : Matrix P1 P4 T) * d4 = 0 := by
  rw [fromRows_mul, c34, Matrix.zero_mul, fromRows_zero]

theorem blk_exact0 (h0 : d0 * X = A) (hP : MatExact d1 d0) :
    MatExact (fromCols (Y * d1) (1 - Y * X)) A := by
  intro v hv
  obtain ⟨c, hc⟩ := hP (X *ᵥ v) (by rw [mulVec_mulVec, h0, hv])
  refine ⟨Sum.elim c v, ?_⟩
  rw [fromCols_mulVec_sumElim, ← mulVec_mulVec, hc, sub_mulVec, one_mulVec, ← mulVec_mulVec]
  abel

theorem blk_exact1 (h2 : d1 * Z = X * Y - 1) (hP : MatExact d2 d1) :
    MatExact (fromBlocks d2 Z 0 Y) (fromCols (Y * d1) (1 - Y * X)) := by
  intro w hw
  rw [fromCols_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at hw
  -- `u = Y v` with `v = X u − d₁ p`
  have hu : w ∘ Sum.inr = Y *ᵥ (X *ᵥ (w ∘ Sum.inr) - d1 *ᵥ (w ∘ Sum.inl)) := by
    rw [mulVec_sub]
    rw [← sub_eq_zero, ← hw]
    abel
  have hd : d1 *ᵥ (w ∘ Sum.inl - Z *ᵥ (X *ᵥ (w ∘ Sum.inr) - d1 *ᵥ (w ∘ Sum.inl))) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, h2, sub_mulVec, one_mulVec, ← mulVec_mulVec, ← hu]
    abel
  obtain ⟨q, hq⟩ := hP _ hd
  refine ⟨Sum.elim q (X *ᵥ (w ∘ Sum.inr) - d1 *ᵥ (w ∘ Sum.inl)), ?_⟩
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hq, zero_mulVec, zero_add, ← hu,
    sub_add_cancel, Sum.elim_comp_inl_inr]

theorem blk_exact2 (h2 : d1 * Z = X * Y - 1) (c12 : d1 * d2 = 0) (hP : MatExact d3 d2) :
    MatExact (fromRows d3 (0 : Matrix P1 P4 T)) (fromBlocks d2 Z 0 Y) := by
  intro w hw
  rw [fromBlocks_mulVec, zero_mulVec, zero_add] at hw
  have e1 : d2 *ᵥ (w ∘ Sum.inl) + Z *ᵥ (w ∘ Sum.inr) = 0 := by
    have := congrArg (· ∘ Sum.inl) hw
    simpa using this
  have e2 : Y *ᵥ (w ∘ Sum.inr) = 0 := by
    have := congrArg (· ∘ Sum.inr) hw
    simpa using this
  -- `v = X Y v − d₁ Z v = 0`
  have hv : w ∘ Sum.inr = 0 := by
    have h3 : (d1 * Z) *ᵥ (w ∘ Sum.inr) = 0 := by
      rw [← mulVec_mulVec, eq_neg_of_add_eq_zero_right e1, mulVec_neg, mulVec_mulVec, c12,
        zero_mulVec, neg_zero]
    rw [h2, sub_mulVec, one_mulVec, ← mulVec_mulVec, e2, mulVec_zero, zero_sub, neg_eq_zero] at h3
    exact h3
  have hq : d2 *ᵥ (w ∘ Sum.inl) = 0 := by rw [← e1, hv, mulVec_zero, add_zero]
  obtain ⟨c, hc⟩ := hP _ hq
  refine ⟨c, ?_⟩
  rw [fromRows_mulVec, hc, zero_mulVec, ← hv, Sum.elim_comp_inl_inr]

theorem blk_exact3 (hP : MatExact d4 d3) : MatExact d4 (fromRows d3 (0 : Matrix P1 P4 T)) := by
  intro v hv
  rw [fromRows_mulVec] at hv
  exact hP v (by simpa using congrArg (· ∘ Sum.inl) hv)

theorem fromBlocks_sub' {n o l m : Type*} (A A' : Matrix n l T) (B B' : Matrix n m T)
    (C C' : Matrix o l T) (D D' : Matrix o m T) :
    fromBlocks A B C D - fromBlocks A' B' C' D' = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> rfl

theorem blk_f1 : fromCols (Y * d1) (1 - Y * X) * fromRows (1 : Matrix P2 P2 T) (0 : Matrix L1 P2 T) =
    Y * d1 := by
  rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem blk_f2 : fromBlocks d2 Z 0 Y * fromRows (1 : Matrix P3 P3 T) (0 : Matrix P1 P3 T) =
    fromRows (1 : Matrix P2 P2 T) (0 : Matrix L1 P2 T) * d2 := by
  rw [fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul]

theorem blk_f3 : fromRows d3 (0 : Matrix P1 P4 T) =
    fromRows (1 : Matrix P3 P3 T) (0 : Matrix P1 P3 T) * d3 := by
  rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem blk_g1 (h2 : d1 * Z = X * Y - 1) :
    d1 * fromCols (1 + Z * d1) (-(Z * X)) = X * fromCols (Y * d1) (1 - Y * X) := by
  rw [mul_fromCols, mul_fromCols]
  congr 1
  · rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  · rw [Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_assoc]
    abel

theorem blk_g2 (h2 : d1 * Z = X * Y - 1) (c12 : d1 * d2 = 0) :
    d2 * fromCols (1 : Matrix P3 P3 T) (0 : Matrix P3 P1 T) =
      fromCols (1 + Z * d1) (-(Z * X)) * fromBlocks d2 Z 0 Y := by
  rw [mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero,
    add_zero, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, c12, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.neg_mul, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_assoc]
  congr 1
  abel

theorem blk_g3 : d3 = fromCols (1 : Matrix P3 P3 T) (0 : Matrix P3 P1 T) * fromRows d3
    (0 : Matrix P1 P4 T) := by
  rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]

theorem blk_h0 : 1 - Y * X =
    fromCols (Y * d1) (1 - Y * X) * fromRows (0 : Matrix P2 L1 T) (1 : Matrix L1 L1 T) +
      (0 : Matrix L1 L0 T) * A := by
  rw [fromCols_mul_fromRows, Matrix.mul_zero, zero_add, Matrix.mul_one, Matrix.zero_mul, add_zero]

theorem blk_h1 : 1 - fromRows (1 : Matrix P2 P2 T) (0 : Matrix L1 P2 T) *
      fromCols (1 + Z * d1) (-(Z * X)) =
    fromBlocks d2 Z 0 Y * fromBlocks (0 : Matrix P3 P2 T) (0 : Matrix P3 L1 T) (-d1) X +
      fromRows (0 : Matrix P2 L1 T) (1 : Matrix L1 L1 T) * fromCols (Y * d1) (1 - Y * X) := by
  rw [← fromBlocks_one, fromRows_mul_fromCols, fromBlocks_multiply, fromRows_mul_fromCols,
    fromBlocks_add, fromBlocks_sub']
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_neg, zero_add, sub_zero,
    zero_sub, neg_neg]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

theorem blk_h2 (h2 : d1 * Z = X * Y - 1) (c12 : d1 * d2 = 0) :
    1 - fromRows (1 : Matrix P3 P3 T) (0 : Matrix P1 P3 T) *
      fromCols (1 : Matrix P3 P3 T) (0 : Matrix P3 P1 T) =
    fromRows d3 (0 : Matrix P1 P4 T) * (0 : Matrix P4 (P3 ⊕ P1) T) +
      fromBlocks (0 : Matrix P3 P2 T) (0 : Matrix P3 L1 T) (-d1) X * fromBlocks d2 Z 0 Y := by
  rw [← fromBlocks_one, fromRows_mul_fromCols, fromBlocks_multiply, fromBlocks_sub']
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.neg_mul,
    zero_add, sub_zero, sub_self, add_zero, c12, neg_zero]
  rw [fromBlocks_inj]
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [h2]
  abel

end Block

/-! ## The new chain, with `Fin`-ranks -/

section Chain

/-- **The data of a presentation change** over `T`: a chain `d_k : T^{r (k+1)} → T^{r k}`, the target
presentation `A : T^b → T^{r 0}` and `X : T^b → T^{r 1}`, `Y : T^{r 1} → T^b`, `Z : T^{r 1} → T^{r 2}`. -/
structure PCData (T : Type*) (r : ℕ → ℕ) (b : ℕ) where
  d : (k : ℕ) → Matrix (Fin (r k)) (Fin (r (k + 1))) T
  A : Matrix (Fin (r 0)) (Fin b) T
  X : Matrix (Fin (r 1)) (Fin b) T
  Y : Matrix (Fin b) (Fin (r 1)) T
  Z : Matrix (Fin (r 2)) (Fin (r 1)) T

/-- The ranks of the new chain beyond degree `1`: `r 2 + b, r 3 + r 1, r 4, r 5, …`. -/
def pcS (r : ℕ → ℕ) (b : ℕ) : ℕ → ℕ
  | 0 => r 2 + b
  | 1 => r 3 + r 1
  | k + 2 => r (k + 4)

/-- The ranks of the new chain: `r 0, b, r 2 + b, r 3 + r 1, r 4, …`. -/
abbrev pcR (r : ℕ → ℕ) (b : ℕ) : ℕ → ℕ := rankSeq (r 0) b (pcS r b)

/-- `Fin (m + n) ≃ Fin m ⊕ Fin n`. -/
abbrev eS (m n : ℕ) : Fin (m + n) ≃ Fin m ⊕ Fin n := finSumFinEquiv.symm

variable {T : Type*} {r : ℕ → ℕ} {b : ℕ}

/-- Applying a map to all the data. -/
def PCData.map {T' : Type*} (D : PCData T r b) (ψ : T → T') : PCData T' r b :=
  ⟨fun k => (D.d k).map ψ, D.A.map ψ, D.X.map ψ, D.Y.map ψ, D.Z.map ψ⟩

variable [Ring T]

/-- The identities `d₀ X = A`, `A Y = d₀`, `d₁ Z = X Y − 1` and `d_k d_{k+1} = 0`. -/
structure PCData.Good (D : PCData T r b) : Prop where
  h0 : D.d 0 * D.X = D.A
  h1 : D.A * D.Y = D.d 0
  h2 : D.d 1 * D.Z = D.X * D.Y - 1
  comp : ∀ k, D.d k * D.d (k + 1) = 0

/-- **The new chain** `δ₀ = A`, `δ₁ = [Y d₁ | 1 − Y X]`, `δ₂ = [d₂ Z; 0 Y]`, `δ₃ = [d₃; 0]`,
`δ_k = d_k` (`k ≥ 4`). -/
def pcδ (D : PCData T r b) : (k : ℕ) → Matrix (Fin (pcR r b k)) (Fin (pcR r b (k + 1))) T
  | 0 => D.A
  | 1 => (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b)
  | 2 => (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1))
  | 3 => (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
      (Equiv.refl (Fin (r 4)))
  | k + 4 => D.d (k + 4)

/-- The chain map `f : P → Q`: `1, Y, (1, 0), (1, 0), 1, …`. -/
def pcf (D : PCData T r b) : (k : ℕ) → Matrix (Fin (pcR r b k)) (Fin (r k)) T
  | 0 => (1 : Matrix (Fin (r 0)) (Fin (r 0)) T)
  | 1 => D.Y
  | 2 => (fromRows (1 : Matrix (Fin (r 2)) (Fin (r 2)) T) (0 : Matrix (Fin b) (Fin (r 2)) T)).submatrix
      (eS (r 2) b) (Equiv.refl (Fin (r 2)))
  | 3 => (fromRows (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 1)) (Fin (r 3)) T)).submatrix
      (eS (r 3) (r 1)) (Equiv.refl (Fin (r 3)))
  | k + 4 => (1 : Matrix (Fin (r (k + 4))) (Fin (r (k + 4))) T)

/-- The chain map `g : Q → P`: `1, X, [1 + Z d₁ | −Z X], [1 | 0], 1, …`. -/
def pcg (D : PCData T r b) : (k : ℕ) → Matrix (Fin (r k)) (Fin (pcR r b k)) T
  | 0 => (1 : Matrix (Fin (r 0)) (Fin (r 0)) T)
  | 1 => D.X
  | 2 => (fromCols (1 + D.Z * D.d 1) (-(D.Z * D.X))).submatrix (Equiv.refl (Fin (r 2))) (eS (r 2) b)
  | 3 => (fromCols (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 3)) (Fin (r 1)) T)).submatrix
      (Equiv.refl (Fin (r 3))) (eS (r 3) (r 1))
  | k + 4 => (1 : Matrix (Fin (r (k + 4))) (Fin (r (k + 4))) T)

/-- The homotopy `h : Q_k → Q_{k+1}`: `0, (0, 1), [0 0; −d₁ X], 0, …`. -/
def pch (D : PCData T r b) : (k : ℕ) → Matrix (Fin (pcR r b (k + 1))) (Fin (pcR r b k)) T
  | 0 => 0
  | 1 => (fromRows (0 : Matrix (Fin (r 2)) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (eS (r 2) b) (Equiv.refl (Fin b))
  | 2 => (fromBlocks (0 : Matrix (Fin (r 3)) (Fin (r 2)) T) (0 : Matrix (Fin (r 3)) (Fin b) T)
      (-D.d 1) D.X).submatrix (eS (r 3) (r 1)) (eS (r 2) b)
  | _ + 3 => 0

variable {D : PCData T r b}

/-- `δ_k δ_{k+1} = 0`. -/
theorem pc_comp (hD : D.Good) : ∀ k, pcδ D k * pcδ D (k + 1) = 0
  | 0 => by
    show (D.A.submatrix (Equiv.refl (Fin (r 0))) (Equiv.refl (Fin b))) *
      (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b) = 0
    rw [submatrix_mul_equiv, blk_comp0 hD.h0 hD.h1 (hD.comp 0)]
    rfl
  | 1 => by
    show (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b) *
      (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1)) = 0
    rw [submatrix_mul_equiv, blk_comp1 hD.h2 (hD.comp 1)]
    rfl
  | 2 => by
    show (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1)) *
      (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
        (Equiv.refl (Fin (r 4))) = 0
    rw [submatrix_mul_equiv, blk_comp2 (hD.comp 2)]
    rfl
  | 3 => by
    show (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
        (Equiv.refl (Fin (r 4))) *
      (D.d 4).submatrix (Equiv.refl (Fin (r 4))) (Equiv.refl (Fin (r 5))) = 0
    rw [submatrix_mul_equiv, blk_comp3 (hD.comp 3)]
    rfl
  | k + 4 => hD.comp (k + 4)

/-- **`Q` is exact in every degree if `P` is.** -/
theorem pc_exact (hD : D.Good) (hP : ∀ k, MatExact (D.d (k + 1)) (D.d k)) :
    ∀ k, MatExact (pcδ D (k + 1)) (pcδ D k)
  | 0 => matExact_submatrix (blk_exact0 hD.h0 (hP 0)) (Equiv.refl _) (Equiv.refl _) (eS (r 2) b)
  | 1 => matExact_submatrix (blk_exact1 hD.h2 (hP 1)) (Equiv.refl _) (eS (r 2) b) (eS (r 3) (r 1))
  | 2 => matExact_submatrix (blk_exact2 hD.h2 (hD.comp 1) (hP 2)) (eS (r 2) b) (eS (r 3) (r 1))
      (Equiv.refl _)
  | 3 => matExact_submatrix (blk_exact3 (hP 3)) (eS (r 3) (r 1)) (Equiv.refl _) (Equiv.refl _)
  | k + 4 => hP (k + 4)

/-- `f` is a chain map: `δ_k f_{k+1} = f_k d_k`. -/
theorem pc_hf (hD : D.Good) : ∀ k, pcδ D k * pcf D (k + 1) = pcf D k * D.d k
  | 0 => by
    show D.A * D.Y = (1 : Matrix (Fin (r 0)) (Fin (r 0)) T) * D.d 0
    rw [hD.h1, Matrix.one_mul]
  | 1 => by
    show (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b) *
      (fromRows (1 : Matrix (Fin (r 2)) (Fin (r 2)) T) (0 : Matrix (Fin b) (Fin (r 2)) T)).submatrix
        (eS (r 2) b) (Equiv.refl (Fin (r 2))) =
      D.Y.submatrix (Equiv.refl (Fin b)) (Equiv.refl (Fin (r 1))) *
        (D.d 1).submatrix (Equiv.refl (Fin (r 1))) (Equiv.refl (Fin (r 2)))
    rw [submatrix_mul_equiv, submatrix_mul_equiv, blk_f1]
  | 2 => by
    show (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1)) *
      (fromRows (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 1)) (Fin (r 3)) T)).submatrix
        (eS (r 3) (r 1)) (Equiv.refl (Fin (r 3))) =
      (fromRows (1 : Matrix (Fin (r 2)) (Fin (r 2)) T) (0 : Matrix (Fin b) (Fin (r 2)) T)).submatrix
        (eS (r 2) b) (Equiv.refl (Fin (r 2))) *
        (D.d 2).submatrix (Equiv.refl (Fin (r 2))) (Equiv.refl (Fin (r 3)))
    rw [submatrix_mul_equiv, submatrix_mul_equiv, blk_f2]
  | 3 => by
    show (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
        (Equiv.refl (Fin (r 4))) * (1 : Matrix (Fin (r 4)) (Fin (r 4)) T) =
      (fromRows (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 1)) (Fin (r 3)) T)).submatrix
        (eS (r 3) (r 1)) (Equiv.refl (Fin (r 3))) *
        (D.d 3).submatrix (Equiv.refl (Fin (r 3))) (Equiv.refl (Fin (r 4)))
    rw [Matrix.mul_one, submatrix_mul_equiv, ← blk_f3]
  | k + 4 => by
    show D.d (k + 4) * (1 : Matrix (Fin (r (k + 5))) (Fin (r (k + 5))) T) =
      (1 : Matrix (Fin (r (k + 4))) (Fin (r (k + 4))) T) * D.d (k + 4)
    rw [Matrix.mul_one, Matrix.one_mul]

/-- `g` is a chain map: `d_k g_{k+1} = g_k δ_k`. -/
theorem pc_hg (hD : D.Good) : ∀ k, D.d k * pcg D (k + 1) = pcg D k * pcδ D k
  | 0 => by
    show D.d 0 * D.X = (1 : Matrix (Fin (r 0)) (Fin (r 0)) T) * D.A
    rw [hD.h0, Matrix.one_mul]
  | 1 => by
    show (D.d 1).submatrix (Equiv.refl (Fin (r 1))) (Equiv.refl (Fin (r 2))) *
      (fromCols (1 + D.Z * D.d 1) (-(D.Z * D.X))).submatrix (Equiv.refl (Fin (r 2))) (eS (r 2) b) =
      D.X.submatrix (Equiv.refl (Fin (r 1))) (Equiv.refl (Fin b)) *
        (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b)
    rw [submatrix_mul_equiv, submatrix_mul_equiv, blk_g1 hD.h2]
  | 2 => by
    show (D.d 2).submatrix (Equiv.refl (Fin (r 2))) (Equiv.refl (Fin (r 3))) *
      (fromCols (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 3)) (Fin (r 1)) T)).submatrix
        (Equiv.refl (Fin (r 3))) (eS (r 3) (r 1)) =
      (fromCols (1 + D.Z * D.d 1) (-(D.Z * D.X))).submatrix (Equiv.refl (Fin (r 2))) (eS (r 2) b) *
        (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1))
    rw [submatrix_mul_equiv, submatrix_mul_equiv, blk_g2 hD.h2 (hD.comp 1)]
  | 3 => by
    show D.d 3 * (1 : Matrix (Fin (r 4)) (Fin (r 4)) T) =
      (fromCols (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 3)) (Fin (r 1)) T)).submatrix
        (Equiv.refl (Fin (r 3))) (eS (r 3) (r 1)) *
        (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
          (Equiv.refl (Fin (r 4)))
    rw [Matrix.mul_one, submatrix_mul_equiv, ← blk_g3]
    rfl
  | k + 4 => by
    show D.d (k + 4) * (1 : Matrix (Fin (r (k + 5))) (Fin (r (k + 5))) T) =
      (1 : Matrix (Fin (r (k + 4))) (Fin (r (k + 4))) T) * D.d (k + 4)
    rw [Matrix.mul_one, Matrix.one_mul]

/-- The homotopy: `1 − f_{k+1} g_{k+1} = δ_{k+1} h_{k+1} + h_k δ_k`. -/
theorem pc_hh (hD : D.Good) :
    ∀ k, 1 - pcf D (k + 1) * pcg D (k + 1) = pcδ D (k + 1) * pch D (k + 1) + pch D k * pcδ D k
  | 0 => by
    show (1 : Matrix (Fin b) (Fin b) T) - D.Y * D.X =
      (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b) *
        (fromRows (0 : Matrix (Fin (r 2)) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
          (eS (r 2) b) (Equiv.refl (Fin b)) + (0 : Matrix (Fin b) (Fin (r 0)) T) * D.A
    rw [submatrix_mul_equiv]
    exact blk_h0 (d1 := D.d 1) (X := D.X) (Y := D.Y) (A := D.A)
  | 1 => by
    show (1 : Matrix (Fin (r 2 + b)) (Fin (r 2 + b)) T) -
      (fromRows (1 : Matrix (Fin (r 2)) (Fin (r 2)) T) (0 : Matrix (Fin b) (Fin (r 2)) T)).submatrix
        (eS (r 2) b) (Equiv.refl (Fin (r 2))) *
      (fromCols (1 + D.Z * D.d 1) (-(D.Z * D.X))).submatrix (Equiv.refl (Fin (r 2))) (eS (r 2) b) =
      (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1)) *
        (fromBlocks (0 : Matrix (Fin (r 3)) (Fin (r 2)) T) (0 : Matrix (Fin (r 3)) (Fin b) T)
          (-D.d 1) D.X).submatrix (eS (r 3) (r 1)) (eS (r 2) b) +
      (fromRows (0 : Matrix (Fin (r 2)) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
          (eS (r 2) b) (Equiv.refl (Fin b)) *
        (fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b)
    rw [submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
      ← submatrix_one_equiv (eS (r 2) b)]
    exact congrArg (fun M => M.submatrix (eS (r 2) b) (eS (r 2) b))
      (blk_h1 (d1 := D.d 1) (d2 := D.d 2) (X := D.X) (Y := D.Y) (Z := D.Z) (P3 := Fin (r 3)))
  | 2 => by
    show (1 : Matrix (Fin (r 3 + r 1)) (Fin (r 3 + r 1)) T) -
      (fromRows (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 1)) (Fin (r 3)) T)).submatrix
        (eS (r 3) (r 1)) (Equiv.refl (Fin (r 3))) *
      (fromCols (1 : Matrix (Fin (r 3)) (Fin (r 3)) T) (0 : Matrix (Fin (r 3)) (Fin (r 1)) T)).submatrix
        (Equiv.refl (Fin (r 3))) (eS (r 3) (r 1)) =
      (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
          (Equiv.refl (Fin (r 4))) *
        ((0 : Matrix (Fin (r 4)) (Fin (r 3) ⊕ Fin (r 1)) T).submatrix (Equiv.refl (Fin (r 4)))
          (eS (r 3) (r 1))) +
      (fromBlocks (0 : Matrix (Fin (r 3)) (Fin (r 2)) T) (0 : Matrix (Fin (r 3)) (Fin b) T)
          (-D.d 1) D.X).submatrix (eS (r 3) (r 1)) (eS (r 2) b) *
        (fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1))
    rw [submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
      ← submatrix_one_equiv (eS (r 3) (r 1))]
    exact congrArg (fun M => M.submatrix (eS (r 3) (r 1)) (eS (r 3) (r 1)))
      (blk_h2 (d1 := D.d 1) (d2 := D.d 2) (d3 := D.d 3) (X := D.X) (Y := D.Y) (Z := D.Z) hD.h2
        (hD.comp 1))
  | 3 => by
    show (1 : Matrix (Fin (r 4)) (Fin (r 4)) T) -
        (1 : Matrix (Fin (r 4)) (Fin (r 4)) T) * (1 : Matrix (Fin (r 4)) (Fin (r 4)) T) =
      D.d 4 * (0 : Matrix (Fin (r 5)) (Fin (r 4)) T) +
        (0 : Matrix (Fin (r 4)) (Fin (r 3 + r 1)) T) *
          (fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
            (Equiv.refl (Fin (r 4)))
    rw [Matrix.mul_one, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  | k + 4 => by
    show (1 : Matrix (Fin (r (k + 5))) (Fin (r (k + 5))) T) -
        (1 : Matrix (Fin (r (k + 5))) (Fin (r (k + 5))) T) *
          (1 : Matrix (Fin (r (k + 5))) (Fin (r (k + 5))) T) =
      D.d (k + 5) * (0 : Matrix (Fin (r (k + 6))) (Fin (r (k + 5))) T) +
        (0 : Matrix (Fin (r (k + 5))) (Fin (r (k + 4))) T) * D.d (k + 4)
    rw [Matrix.mul_one, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The new chain commutes with ring maps. -/
theorem pc_map {T' : Type*} [Ring T'] (D : PCData T r b) (ψ : T →+* T') :
    ∀ k, (pcδ D k).map ψ = pcδ (D.map ψ) k
  | 0 => rfl
  | 1 => by
    show ((fromCols (D.Y * D.d 1) (1 - D.Y * D.X)).submatrix (Equiv.refl (Fin b)) (eS (r 2) b)).map ψ =
      (fromCols (D.Y.map ψ * (D.d 1).map ψ) (1 - D.Y.map ψ * D.X.map ψ)).submatrix
        (Equiv.refl (Fin b)) (eS (r 2) b)
    rw [← submatrix_map, fromCols_map, Matrix.map_mul, Matrix.map_sub ψ (map_sub ψ),
      Matrix.map_one ψ (map_zero ψ) (map_one ψ), Matrix.map_mul]
  | 2 => by
    show ((fromBlocks (D.d 2) D.Z 0 D.Y).submatrix (eS (r 2) b) (eS (r 3) (r 1))).map ψ =
      (fromBlocks ((D.d 2).map ψ) (D.Z.map ψ) 0 (D.Y.map ψ)).submatrix (eS (r 2) b) (eS (r 3) (r 1))
    rw [← submatrix_map, fromBlocks_map, Matrix.map_zero ψ (map_zero ψ)]
  | 3 => by
    show ((fromRows (D.d 3) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T)).submatrix (eS (r 3) (r 1))
        (Equiv.refl (Fin (r 4)))).map ψ =
      (fromRows ((D.d 3).map ψ) (0 : Matrix (Fin (r 1)) (Fin (r 4)) T')).submatrix (eS (r 3) (r 1))
        (Equiv.refl (Fin (r 4)))
    rw [← submatrix_map, fromRows_map, Matrix.map_zero ψ (map_zero ψ)]
  | _ + 4 => rfl

end Chain

/-! ## Splittings over a normed ring -/

section Split
variable {T : Type*} [NormedRing T] [NormedAlgebra ℂ T] {r : ℕ → ℕ} {b : ℕ}

theorem matrixOperator_comp_eq {l m n m' : Type*} [Fintype m] [Fintype n] [Fintype m']
    {M : l → m → T} {N : m → n → T} {M' : l → m' → T} {N' : m' → n → T}
    (h : Matrix.of M * Matrix.of N = Matrix.of M' * Matrix.of N') (v : n → T) :
    matrixOperator M (matrixOperator N v) = matrixOperator M' (matrixOperator N' v) := by
  simp only [matrixOperator_apply_eq_mulVec, mulVec_mulVec, h]

theorem matrixOperator_homotopy {n m l o : Type*} [Fintype n] [Fintype m] [Fintype l] [Fintype o]
    [DecidableEq n] {F : n → m → T} {G : m → n → T} {D1 : n → l → T} {H1 : l → n → T}
    {H0 : n → o → T} {D0 : o → n → T}
    (h : 1 - Matrix.of F * Matrix.of G = Matrix.of D1 * Matrix.of H1 + Matrix.of H0 * Matrix.of D0)
    (y : n → T) :
    y - matrixOperator F (matrixOperator G y) =
      matrixOperator D1 (matrixOperator H1 y) + matrixOperator H0 (matrixOperator D0 y) := by
  simp only [matrixOperator_apply_eq_mulVec, mulVec_mulVec]
  have := congrArg (· *ᵥ y) h
  simp only [sub_mulVec, one_mulVec, add_mulVec] at this
  exact this

/-- **A splitting of `P` gives a splitting of `Q`** (in the same degrees), by domination. -/
theorem splitBy_pc (D : PCData T r b) (hD : D.Good) {M : ℕ}
    {t : (k : ℕ) → (Fin (r k) → T) →L[ℂ] (Fin (r (k + 1)) → T)} (ht : SplitBy (chainOp D.d) t M) :
    ∃ t' : (k : ℕ) → (Fin (pcR r b k) → T) →L[ℂ] (Fin (pcR r b (k + 1)) → T),
      SplitBy (chainOp (pcδ D)) t' M :=
  ⟨_, ht.of_dominated' (fun k => matrixOperator (pcf D k)) (fun k => matrixOperator (pcg D k))
    (fun k => matrixOperator (pch D k))
    (fun k x => matrixOperator_comp_eq (M := pcδ D k) (N := pcf D (k + 1)) (M' := pcf D k)
      (N' := D.d k) (pc_hf hD k) x)
    (fun k y => matrixOperator_comp_eq (M := D.d k) (N := pcg D (k + 1)) (M' := pcg D k)
      (N' := pcδ D k) (pc_hg hD k) y)
    (fun k _ y => matrixOperator_homotopy (F := pcf D (k + 1)) (G := pcg D (k + 1))
      (D1 := pcδ D (k + 1)) (H1 := pch D (k + 1)) (H0 := pch D k) (D0 := pcδ D k) (pc_hh hD k) y)⟩

end Split

/-! ## Holomorphic matrices on an open set -/

section Function
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {r : ℕ → ℕ} {b : ℕ}

/-- The data lifted to the ring `holOn U`. -/
def liftData (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ)
    (hd : ∀ k i j, DifferentiableOn ℂ (d k i j) U) (A : Fin (r 0) → Fin b → X → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (A i j) U) (Xm : Fin (r 1) → Fin b → X → ℂ)
    (hX : ∀ i j, DifferentiableOn ℂ (Xm i j) U) (Ym : Fin b → Fin (r 1) → X → ℂ)
    (hY : ∀ i j, DifferentiableOn ℂ (Ym i j) U) (Zm : Fin (r 2) → Fin (r 1) → X → ℂ)
    (hZ : ∀ i j, DifferentiableOn ℂ (Zm i j) U) : PCData (holOn U) r b :=
  ⟨fun k => liftMat (d k) (hd k), liftMat A hA, liftMat Xm hX, liftMat Ym hY, liftMat Zm hZ⟩

/-- The holomorphic matrices of the new chain. -/
def pcChain (D : PCData (holOn U) r b) (k : ℕ) :
    Fin (pcR r b k) → Fin (pcR r b (k + 1)) → X → ℂ :=
  fun i j => (pcδ D k i j).1

theorem pcChain_hol (D : PCData (holOn U) r b) (k : ℕ) (i : Fin (pcR r b k))
    (j : Fin (pcR r b (k + 1))) : DifferentiableOn ℂ (pcChain D k i j) U :=
  (pcδ D k i j).2

/-- Identities on `U` give the identities `PCData.Good` over the target of a ring map that only sees
`U`. -/
theorem good_map {T : Type*} [Ring T] {ψ : holOn U →+* T} (hψ : RespectsOn U ψ)
    (D : PCData (holOn U) r b)
    (h0 : ∀ x ∈ U, ∀ i j, ((D.d 0 * D.X) i j).1 x = (D.A i j).1 x)
    (h1 : ∀ x ∈ U, ∀ i j, ((D.A * D.Y) i j).1 x = (D.d 0 i j).1 x)
    (h2 : ∀ x ∈ U, ∀ i j, ((D.d 1 * D.Z) i j).1 x =
      ((D.X * D.Y - (1 : Matrix (Fin (r 1)) (Fin (r 1)) (holOn U))) i j).1 x)
    (hc : ∀ k, ∀ x ∈ U, ∀ i j, ((D.d k * D.d (k + 1)) i j).1 x = 0) : (D.map ψ).Good where
  h0 := (Matrix.map_mul).symm.trans (hψ.map_eq h0)
  h1 := (Matrix.map_mul).symm.trans (hψ.map_eq h1)
  h2 := (Matrix.map_mul).symm.trans ((hψ.map_eq h2).trans (by
    rw [Matrix.map_sub ψ (map_sub ψ), Matrix.map_mul, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
    rfl))
  comp k := (Matrix.map_mul).symm.trans ((hψ.map_eq (N := 0) (hc k)).trans
    (Matrix.map_zero ψ (map_zero ψ)))

/-- **Presentation change** (holomorphic matrices on an open `U`). Let `d` be a chain of holomorphic
matrices on `U`, exact on `U` in every degree, and `A`, `X`, `Y`, `Z` holomorphic on `U` with
`d₀ X = A`, `A Y = d₀`, `d₁ Z = X Y − 1` on `U`. Then the chain `δ` (`pcδ`, with `δ₀ = A` and ranks
`pcR r b`) is exact on `U` in every degree, and on every compact `K ⊆ U` on which the `B(K)`-complex of
`d` is split in degrees `< M`, the `B(K)`-complex of `δ` is split in degrees `< M`. -/
theorem exists_presentationChange (hU : IsOpen U)
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ} (hd : ∀ k i j, DifferentiableOn ℂ (d k i j) U)
    (hex : ∀ k, ExactStartOn U (d (k + 1)) (d k))
    {A : Fin (r 0) → Fin b → X → ℂ} (hA : ∀ i j, DifferentiableOn ℂ (A i j) U)
    {Xm : Fin (r 1) → Fin b → X → ℂ} (hX : ∀ i j, DifferentiableOn ℂ (Xm i j) U)
    {Ym : Fin b → Fin (r 1) → X → ℂ} (hY : ∀ i j, DifferentiableOn ℂ (Ym i j) U)
    {Zm : Fin (r 2) → Fin (r 1) → X → ℂ} (hZ : ∀ i j, DifferentiableOn ℂ (Zm i j) U)
    (h0 : ∀ x ∈ U, ∀ i j, ∑ l, d 0 i l x * Xm l j x = A i j x)
    (h1 : ∀ x ∈ U, ∀ i j, ∑ l, A i l x * Ym l j x = d 0 i j x)
    (h2 : ∀ x ∈ U, ∀ i j, ∑ l, d 1 i l x * Zm l j x =
      ∑ l, Xm i l x * Ym l j x - if i = j then 1 else 0) :
    ∃ (δ : (k : ℕ) → Fin (pcR r b k) → Fin (pcR r b (k + 1)) → X → ℂ)
      (hδ : ∀ k i j, DifferentiableOn ℂ (δ k i j) U),
      δ 0 = A ∧ (∀ k, ExactStartOn U (δ (k + 1)) (δ k)) ∧
      ∀ (K : Set X) [CompactSpace K] (hKU : K ⊆ U) (M : ℕ),
        (∃ t : (k : ℕ) → (Fin (r k) → holSubalgebra K) →L[ℂ] (Fin (r (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K hKU (d k) (hd k)) t M) →
        ∃ t : (k : ℕ) → (Fin (pcR r b k) → holSubalgebra K) →L[ℂ]
            (Fin (pcR r b (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K hKU (δ k) (hδ k)) t M := by
  set L := liftData d hd A hA Xm hX Ym hY Zm hZ with hL
  have p0 : ∀ x ∈ U, ∀ i j, ((L.d 0 * L.X) i j).1 x = (L.A i j).1 x := fun x hx i j => by
    rw [holOn_mul_apply]
    exact h0 x hx i j
  have p1 : ∀ x ∈ U, ∀ i j, ((L.A * L.Y) i j).1 x = (L.d 0 i j).1 x := fun x hx i j => by
    rw [holOn_mul_apply]
    exact h1 x hx i j
  have p2 : ∀ x ∈ U, ∀ i j, ((L.d 1 * L.Z) i j).1 x =
      ((L.X * L.Y - (1 : Matrix (Fin (r 1)) (Fin (r 1)) (holOn U))) i j).1 x :=
    fun x hx i j => by
      rw [holOn_mul_apply, Matrix.sub_apply, Matrix.one_apply]
      show _ = ((L.X * L.Y) i j).1 x - (if i = j then (1 : holOn U) else 0).1 x
      rw [holOn_mul_apply]
      refine (h2 x hx i j).trans ?_
      split_ifs <;> rfl
  have pc : ∀ k, ∀ x ∈ U, ∀ i j, ((L.d k * L.d (k + 1)) i j).1 x = 0 := fun k x hx i j => by
    rw [holOn_mul_apply]
    exact (hex k).comp i j x hx
  refine ⟨pcChain L, pcChain_hol L, rfl, fun k => ?_, fun K _ hKU M ⟨t, ht⟩ => ?_⟩
  · refine exactStartOn_of_matExact hU (pcChain_hol L k) (pcChain_hol L (k + 1))
      (fun i l x hx => ?_) (fun y hy => ?_)
    · have hev := congrFun (congrFun (pc_comp (good_map (respectsOn_evalHom (U := U) hx) L p0 p1 p2 pc) k) i) l
      rw [← pc_map, ← pc_map, ← Matrix.map_mul] at hev
      exact (holOn_mul_apply (pcδ L k) (pcδ L (k + 1)) i l x).symm.trans hev
    · have hP : ∀ k, MatExact ((L.map (germAt hU y hy)).d (k + 1)) ((L.map (germAt hU y hy)).d k) :=
        fun k => by
          show MatExact ((liftMat (d (k + 1)) (hd (k + 1))).map (germAt hU y hy))
            ((liftMat (d k) (hd k)).map (germAt hU y hy))
          rw [map_germAt_liftMat, map_germAt_liftMat]
          exact matExact_of_exactStartOn hU (hex k) hy
      have := pc_exact (good_map (respectsOn_germAt hU hy) L p0 p1 p2 pc) hP k
      rw [← pc_map, ← pc_map] at this
      rw [← map_germAt_liftMat hU hy _ (pcChain_hol L (k + 1)),
        ← map_germAt_liftMat hU hy _ (pcChain_hol L k)]
      exact this
  · obtain ⟨t', ht'⟩ := splitBy_pc (L.map (restrictHom K hKU))
      (good_map (respectsOn_restrictHom K hKU) L p0 p1 p2 pc) (t := t) ht
    refine ⟨t', ?_⟩
    have key : (fun k => restrictMatrix K hKU (pcChain L k) (pcChain_hol L k)) =
        pcδ (L.map (restrictHom K hKU)) := funext fun k => pc_map L (restrictHom K hKU) k
    rw [key]
    exact ht'

end Function

end
end Hironaka.HironakaG10FlatPresentationChange
