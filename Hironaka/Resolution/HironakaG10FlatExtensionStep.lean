import Hironaka.Resolution.HironakaG10FlatBlockRemoval
import Hironaka.Resolution.HironakaG10FlatTorsionStep

/-! # The extension step of Douady's theorem of privileged neighbourhoods

Douady 1966, §7 n° 1 Prop. 3 in the form needed by the induction of n° 4 Th. 1: let `𝓕 = coker A`
(`A : L_b → L_a`), `T : L_t → L_a` sections generating a subsheaf `𝓕' ⊆ 𝓕`, `C' : L_c → L_t` a
presentation of `𝓕'` (`im C' = {v | T v ∈ im A}` at `x`, and `T C' = A Q`), and `𝓕'' = coker [A | T]`.
From finite free resolutions `P'` of `coker C'` (first matrix `C'`) and `P''` of `coker [A | T]` (first
matrix `[A | T]`), exact in every degree on open sets around `x`, we build a finite free resolution of
`𝓕` with first matrix `A` on an open set around `x`, split on every compact on which `P'` and `P''` are.

Construction: the horseshoe of `P'`, `P''` with `φ₀ = [0 | −1]` (`HironakaG10FlatHorseshoe`); its first
matrix has the image of `[1 0; −T A]`; the presentation change (`HironakaG10FlatPresentationChange`)
with `X = (0; [[0, 1], [−1, 0]])`, `Y = [[C', φ₀], [Q, (1 | 0)]]`; and the removal of the identity block
(`HironakaG10FlatBlockRemoval`).

* Block identities (`ext_h0`, `ext_h1`) over any ring.
* **`extension_step`**.
BP: hironaka-g10-flat-extension-step.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatExtensionStep
noncomputable section
open OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart HironakaG10FlatGermChain
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatSplitComplex HironakaG10FlatPrivilegedNbhd
  HironakaG10FlatPresentationChange HironakaG10FlatHorseshoe HironakaG10FlatBlockRemoval Matrix

/-! ## Block identities -/

section Blocks
variable {S : Type*} [Ring S] {a b t c : ℕ}

/-- `φ₀ = [0 | −1] : L_b ⊕ L_t → L_t`. -/
def phiMat : Matrix (Fin t) (Fin (b + t)) S :=
  (fromCols (0 : Matrix (Fin t) (Fin b) S) (-1 : Matrix (Fin t) (Fin t) S)).submatrix
    (Equiv.refl (Fin t)) finSumFinEquiv.symm

/-- `[[0, 1], [−1, 0]] : L_t ⊕ L_b → L_b ⊕ L_t`. -/
def x2Mat : Matrix (Fin (b + t)) (Fin t ⊕ Fin b) S :=
  (fromRows (fromCols (0 : Matrix (Fin b) (Fin t) S) (1 : Matrix (Fin b) (Fin b) S))
    (fromCols (-1 : Matrix (Fin t) (Fin t) S) (0 : Matrix (Fin t) (Fin b) S))).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

/-- `X = (0; x2Mat)`. -/
def xMatE : Matrix (Fin c ⊕ Fin (b + t)) (Fin t ⊕ Fin b) S :=
  fromRows (0 : Matrix (Fin c) (Fin t ⊕ Fin b) S) x2Mat

/-- `(1 | 0) : L_b ⊕ L_t → L_b`. -/
def y22Mat : Matrix (Fin b) (Fin (b + t)) S :=
  (fromCols (1 : Matrix (Fin b) (Fin b) S) (0 : Matrix (Fin b) (Fin t) S)).submatrix
    (Equiv.refl (Fin b)) finSumFinEquiv.symm

/-- `[A | T]`. -/
def catMat (A : Matrix (Fin a) (Fin b) S) (T : Matrix (Fin a) (Fin t) S) : Matrix (Fin a) (Fin (b + t)) S :=
  (fromCols A T).submatrix (Equiv.refl (Fin a)) finSumFinEquiv.symm

theorem ext_h0 (C' : Matrix (Fin t) (Fin c) S) (A : Matrix (Fin a) (Fin b) S)
    (T : Matrix (Fin a) (Fin t) S) :
    fromBlocks C' phiMat 0 (catMat A T) * xMatE = fromBlocks 1 0 (-T) A := by
  rw [xMatE, fromBlocks_mul_fromRows, Matrix.mul_zero, Matrix.zero_mul, zero_add, zero_add,
    phiMat, x2Mat, catMat, submatrix_mul_equiv, submatrix_mul_equiv, fromCols_mul_fromRows,
    fromCols_mul_fromRows, Matrix.zero_mul, zero_add]
  simp only [Equiv.coe_refl, submatrix_id_id, mul_fromCols, Matrix.mul_zero, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul]
  rw [← fromRows_fromCols_eq_fromBlocks]
  congr 1 <;> ext i (j | j) <;> simp [fromCols]

theorem ext_h1 (C' : Matrix (Fin t) (Fin c) S) (A : Matrix (Fin a) (Fin b) S)
    (T : Matrix (Fin a) (Fin t) S) (Q : Matrix (Fin b) (Fin c) S) (hQ : A * Q = T * C') :
    fromBlocks 1 0 (-T) A * fromBlocks C' phiMat Q y22Mat = fromBlocks C' phiMat 0 (catMat A T) := by
  rw [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.one_mul,
    Matrix.zero_mul, add_zero, Matrix.neg_mul, hQ, neg_add_cancel, Matrix.neg_mul]
  congr 1
  rw [phiMat, y22Mat, catMat]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Equiv.refl_apply]
  rcases finSumFinEquiv.symm j with j' | j' <;> simp [fromCols, Matrix.one_apply]

theorem phiMat_sum (w : Fin (b + t) → S) (l : Fin t) :
    ∑ l', (phiMat : Matrix (Fin t) (Fin (b + t)) S) l l' * w l' = -w (finSumFinEquiv (Sum.inr l)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [phiMat, Matrix.submatrix_apply, Equiv.refl_apply, Equiv.symm_apply_apply,
    fromCols_apply_inl, fromCols_apply_inr, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, Matrix.neg_apply, Matrix.one_apply, neg_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem catMat_sum (A : Matrix (Fin a) (Fin b) S) (T : Matrix (Fin a) (Fin t) S) (w : Fin (b + t) → S)
    (i : Fin a) : ∑ l, catMat A T i l * w l =
      ∑ l, A i l * w (finSumFinEquiv (Sum.inl l)) + ∑ l, T i l * w (finSumFinEquiv (Sum.inr l)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [catMat, Matrix.submatrix_apply, Equiv.refl_apply, Equiv.symm_apply_apply,
    fromCols_apply_inl, fromCols_apply_inr]

theorem sum_reindex_mul {ι κ κ' μ : Type*} [Fintype κ] [Fintype κ'] (M : Matrix ι κ S)
    (N : Matrix κ μ S) (e : κ' ≃ κ) (i : ι) (j : μ) : ∑ l, M i (e l) * N (e l) j = (M * N) i j := by
  rw [Matrix.mul_apply]
  exact Equiv.sum_comp e (fun l => M i l * N l j)

end Blocks

/-! ## The extension step -/

section Ext
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `[A | T]` for matrices of functions. -/
def catCols {a b t : ℕ} (A : Fin a → Fin b → X → ℂ) (T : Fin a → Fin t → X → ℂ) :
    Fin a → Fin (b + t) → X → ℂ :=
  fun i j => Sum.elim (A i) (T i) (finSumFinEquiv.symm j)

theorem valMat_catCols {a b t : ℕ} (A : Fin a → Fin b → X → ℂ) (T : Fin a → Fin t → X → ℂ) (y : X) :
    valMat y (catCols A T) = catMat (valMat y A) (valMat y T) := by
  ext i j
  show Sum.elim (A i) (T i) (finSumFinEquiv.symm j) y =
    fromCols (valMat y A) (valMat y T) i (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm j with j' | j' <;> rfl

theorem valMat_fromBlocks_one {a b t : ℕ} (N : Fin a → Fin t → X → ℂ) (A : Fin a → Fin b → X → ℂ)
    (y : X) : valMat y (fromBlocks (1 : Matrix (Fin t) (Fin t) (X → ℂ)) 0 N A) =
      fromBlocks 1 0 (valMat y N) (valMat y A) := by
  ext (i | i) (j | j)
  · show (1 : Matrix (Fin t) (Fin t) (X → ℂ)) i j y = (1 : Matrix (Fin t) (Fin t) ℂ) i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · rfl
  · rfl
  · rfl

/-- **The extension step of Douady's Th. 1** (Prop. 3, whole resolutions). -/
theorem extension_step {U' U'' : Set X} (hU' : IsOpen U') (hU'' : IsOpen U'') {x : X} (hx' : x ∈ U')
    (hx'' : x ∈ U'') {a b t c : ℕ} {A : Fin a → Fin b → X → ℂ} {T : Fin a → Fin t → X → ℂ}
    {C' : Fin t → Fin c → X → ℂ} {Q : Fin b → Fin c → X → ℂ} (hQh : ∀ i j, HolAt (Q i j) x)
    (hQ : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ l, A i l y * Q l j y = ∑ l, T i l y * C' l j y)
    (hgen : ∀ v : Fin t → X → ℂ, (∀ j, HolAt (v j) x) →
      IsCombinationAt (columns A) x (fun i y => ∑ l, T i l y * v l y) → IsCombinationAt (columns C') x v)
    {s' : ℕ → ℕ} {m' : ℕ} {d' : (k : ℕ) → Fin (rankSeq t c s' k) → Fin (rankSeq t c s' (k + 1)) → X → ℂ}
    (hd' : ∀ k, ExactStartOn U' (d' (k + 1)) (d' k)) (hd'0 : d' 0 = C')
    (htail' : ∀ k, m' < k → rankSeq t c s' k = 0)
    {s'' : ℕ → ℕ} {m'' : ℕ}
    {d'' : (k : ℕ) → Fin (rankSeq a (b + t) s'' k) → Fin (rankSeq a (b + t) s'' (k + 1)) → X → ℂ}
    (hd'' : ∀ k, ExactStartOn U'' (d'' (k + 1)) (d'' k)) (hd''0 : d'' 0 = catCols A T)
    (htail'' : ∀ k, m'' < k → rankSeq a (b + t) s'' k = 0) :
    ∃ (V : Set X) (s : ℕ → ℕ) (δ : (k : ℕ) → Fin (rankSeq a b s k) → Fin (rankSeq a b s (k + 1)) → X → ℂ)
      (hδ : ∀ k i j, DifferentiableOn ℂ (δ k i j) V) (hVU' : V ⊆ U') (hVU'' : V ⊆ U''),
      IsOpen V ∧ x ∈ V ∧ δ 0 = A ∧ (∀ k, ExactStartOn V (δ (k + 1)) (δ k)) ∧
      (∀ k, m' + m'' + 4 < k → rankSeq a b s k = 0) ∧
      ∀ (K : Set X) [CompactSpace K] (hKV : K ⊆ V) (M : ℕ),
        (∃ t1 : (k : ℕ) → (Fin (rankSeq t c s' k) → holSubalgebra K) →L[ℂ]
            (Fin (rankSeq t c s' (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K (hKV.trans hVU') (d' k) ((hd' k).holF)) t1 M) →
        (∃ t2 : (k : ℕ) → (Fin (rankSeq a (b + t) s'' k) → holSubalgebra K) →L[ℂ]
            (Fin (rankSeq a (b + t) s'' (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K (hKV.trans hVU'') (d'' k) ((hd'' k).holF)) t2 M) →
        ∃ t3 : (k : ℕ) → (Fin (rankSeq a b s k) → holSubalgebra K) →L[ℂ]
            (Fin (rankSeq a b s (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K hKV (δ k) (hδ k)) t3 M := by
  -- notation and holomorphy at `x`
  have hd'h : ∀ k i j, HolAt (d' k i j) x :=
    fun k i j => holAt_of_differentiableOn hU' ((hd' k).holF i j) hx'
  have hd''h : ∀ k i j, HolAt (d'' k i j) x :=
    fun k i j => holAt_of_differentiableOn hU'' ((hd'' k).holF i j) hx''
  have hAh : ∀ i j, HolAt (A i j) x := fun i j => by
    have := hd''h 0 i (finSumFinEquiv (Sum.inl j))
    rw [hd''0] at this
    simpa [catCols] using this
  have hTh : ∀ i j, HolAt (T i j) x := fun i j => by
    have := hd''h 0 i (finSumFinEquiv (Sum.inr j))
    rw [hd''0] at this
    simpa [catCols] using this
  have hC'h : ∀ i j, HolAt (C' i j) x := fun i j => by
    have := hd'h 0 i j
    rw [hd'0] at this
    exact this
  -- the off-diagonal blocks of the horseshoe
  set φ0 : Fin (rankSeq t c s' 0) → Fin (rankSeq a (b + t) s'' 1) → X → ℂ :=
    fun i j _ => (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) i j with hφ0
  have h0sol : ∀ j, IsCombinationAt (columns (d' 0)) x
      (fun i y => -∑ l, φ0 i l y * d'' 1 l j y) := by
    intro j
    rw [hd'0]
    have hv : (fun i y => -∑ l, φ0 i l y * d'' 1 l j y) =
        fun (i : Fin t) y => d'' 1 (finSumFinEquiv (Sum.inr i)) j y := by
      funext i y
      have := phiMat_sum (S := ℂ) (b := b) (fun l => d'' 1 l j y) i
      rw [neg_eq_iff_eq_neg]
      exact this
    rw [hv]
    refine hgen _ (fun i => hd''h 1 _ j) ⟨fun l y => -d'' 1 (finSumFinEquiv (Sum.inl l)) j y,
      fun l => (hd''h 1 _ j).neg, fun i => ?_⟩
    filter_upwards [hU''.mem_nhds hx''] with y hy
    have hc := (hd'' 0).comp i j y hy
    rw [hd''0] at hc
    have hc' := catMat_sum (S := ℂ) (valMat y A) (valMat y T) (fun l => d'' 1 l j y) i
    rw [← valMat_catCols] at hc'
    have : ∑ l, T i l y * d'' 1 (finSumFinEquiv (Sum.inr l)) j y =
        -∑ l, A i l y * d'' 1 (finSumFinEquiv (Sum.inl l)) j y := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hc'.symm.trans hc
    rw [this]
    simp only [columns, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  -- the horseshoe near `x`
  have hc'' : ∀ k, ∀ᶠ y in 𝓝 x, ∀ i l, ∑ j, d'' k i j y * d'' (k + 1) j l y = 0 := fun k => by
    filter_upwards [hU''.mem_nhds hx''] with y hy i l
    exact (hd'' k).comp i l y hy
  have hφspec := fun k => hsPhi_spec (d' := d') (d'' := d'') (φ0 := φ0) (x := x)
    (fun i j => holAt_const _ x) hd''h (fun k => (hd' k).exact x hx') hc'' h0sol k
  set φ := hsPhi d' d'' φ0 x with hφ
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U' ∧ y ∈ U'' ∧ ∀ k ∈ Finset.range (m'' + 2),
      (∀ i j, DifferentiableAt ℂ (φ k i j) y) ∧
      ∀ i j, ∑ l, d' k i l y * φ (k + 1) l j y + ∑ l, φ k i l y * d'' (k + 1) l j y = 0 :=
    (Filter.eventually_of_mem (hU'.mem_nhds hx') fun y hy => hy).and
      ((Filter.eventually_of_mem (hU''.mem_nhds hx'') fun y hy => hy).and
      ((Finset.eventually_all _).2 fun k _ =>
      (eventually_all.2 fun i => eventually_all.2 fun j => (hφspec k).1 i j).and (hφspec k).2))
  obtain ⟨V₁, hV₁sub, hV₁o, hxV₁⟩ := _root_.eventually_nhds_iff.1 hev
  have hV₁U' : V₁ ⊆ U' := fun y hy => (hV₁sub y hy).1
  have hV₁U'' : V₁ ⊆ U'' := fun y hy => (hV₁sub y hy).2.1
  have hφV : ∀ k i j, DifferentiableOn ℂ (φ k i j) V₁ := by
    intro k i j y hy
    by_cases hk : k < m'' + 2
    · exact (((hV₁sub y hy).2.2 k (Finset.mem_range.2 hk)).1 i j).differentiableWithinAt
    · exact (Fin.cast (htail'' (k + 1) (by omega)) j).elim0
  have hidV : ∀ k, ∀ y ∈ V₁, ∀ i j, ∑ l, d' k i l y * φ (k + 1) l j y +
      ∑ l, φ k i l y * d'' (k + 1) l j y = 0 := by
    intro k y hy i j
    by_cases hk : k < m'' + 2
    · exact ((hV₁sub y hy).2.2 k (Finset.mem_range.2 hk)).2 i j
    · exact (Fin.cast (htail'' (k + 1 + 1) (by omega)) j).elim0
  have hR : ∀ k, ExactStartOn V₁ (hsFin d' d'' φ (k + 1)) (hsFin d' d'' φ k) :=
    exactStartOn_hsFin hV₁o (fun k => (hd' k).mono hV₁U') (fun k => (hd'' k).mono hV₁U'') hφV hidV
  -- the data of the presentation change
  set Xm : Fin (hsRank (rankSeq t c s') (rankSeq a (b + t) s'') 1) → Fin (t + b) → X → ℂ :=
    fun l j _ => (xMatE : Matrix (Fin c ⊕ Fin (b + t)) (Fin t ⊕ Fin b) ℂ)
      (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l) (eS t b j) with hXm
  set Ym : Fin (t + b) → Fin (hsRank (rankSeq t c s') (rankSeq a (b + t) s'') 1) → X → ℂ :=
    fun i l y => (fromBlocks (valMat y C') (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) (valMat y Q)
      (y22Mat : Matrix (Fin b) (Fin (b + t)) ℂ)) (eS t b i)
        (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l) with hYm
  set Anew : Fin (hsRank (rankSeq t c s') (rankSeq a (b + t) s'') 0) → Fin (t + b) → X → ℂ :=
    fun i j => (fromBlocks (1 : Matrix (Fin t) (Fin t) (X → ℂ)) 0 (-T) A) (eS t a i) (eS t b j)
      with hAnew
  have hblock : ∀ y, valMat y (hsBlock d' d'' φ 0) =
      fromBlocks (valMat y C') (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) 0
        (catMat (valMat y A) (valMat y T)) := by
    intro y
    rw [hsBlock, valMat_fromBlocks, hd'0, hd''0]
    exact congrArg (fun M => fromBlocks (valMat y C') (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) 0 M)
      (valMat_catCols A T y)
  have h0id : ∀ y, ∀ i j, ∑ l, hsFin d' d'' φ 0 i l y * Xm l j y = Anew i j y := by
    intro y i j
    have hb : ∀ l, hsFin d' d'' φ 0 i l y = (fromBlocks (valMat y C')
        (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) 0 (catMat (valMat y A) (valMat y T)))
          (eH (rankSeq t c s') (rankSeq a (b + t) s'') 0 i)
          (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l) := fun l =>
      congrFun (congrFun (hblock y) _) _
    rw [Finset.sum_congr rfl fun l _ => by rw [hb l]]
    exact (sum_reindex_mul _ _ (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1) _ _).trans
      ((congrFun (congrFun (ext_h0 (valMat y C') (valMat y A) (valMat y T)) _) _).trans
        (congrFun (congrFun (valMat_fromBlocks_one (-T) A y) _) _).symm)
  have h1id : ∀ y, (∀ i j, ∑ l, A i l y * Q l j y = ∑ l, T i l y * C' l j y) →
      ∀ i j, ∑ l, Anew i l y * Ym l j y = hsFin d' d'' φ 0 i j y := by
    intro y hy i j
    have ha : ∀ l, Anew i l y = (fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 (-valMat y T) (valMat y A))
        (eS t a i) (eS t b l) := fun l =>
      congrFun (congrFun (valMat_fromBlocks_one (-T) A y) _) _
    rw [Finset.sum_congr rfl fun l _ => by rw [ha l]]
    exact (sum_reindex_mul _ _ (eS t b) _ _).trans
      ((congrFun (congrFun (ext_h1 (valMat y C') (valMat y A) (valMat y T) (valMat y Q)
        (Matrix.ext fun i j => hy i j)) _) _).trans (congrFun (congrFun (hblock y) _) _).symm)
  -- the lift `Z` of the relations `X Y − 1`
  have hXh : ∀ l j, HolAt (Xm l j) x := fun l j => holAt_const _ x
  have hYh : ∀ i l, HolAt (Ym i l) x := by
    intro i l
    show HolAt (fun y => (fromBlocks (valMat y C') (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ) (valMat y Q)
      (y22Mat : Matrix (Fin b) (Fin (b + t)) ℂ)) (eS t b i)
        (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l)) x
    rcases eS t b i with i' | i' <;> rcases eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l with l' | l'
    · exact hC'h i' l'
    · exact holAt_const _ x
    · exact hQh i' l'
    · exact holAt_const _ x
  have hrel : ∀ j, IsCombinationAt (columns (hsFin d' d'' φ 1)) x
      (fun l y => ∑ m, Xm l m y * Ym m j y - if l = j then 1 else 0) := by
    intro j
    refine (hR 0).exact x hxV₁ _ ⟨fun l => (HolAt.fintype_sum fun m => (hXh l m).mul (hYh m j)).sub
      (holAt_const _ _), fun i => ?_⟩
    filter_upwards [hQ] with y hy
    exact HironakaG10FlatTorsionStep.sum_relation (fun i l => hsFin d' d'' φ 0 i l y)
      (fun l m => Xm l m y) (fun m l => Ym m l y) (fun i m => Anew i m y) (fun i m => h0id y i m)
      (fun i l => h1id y hy i l) i j
  choose Zc hZc hZcol using hrel
  -- holomorphy of `A`, `T`, `C'`
  have hAU : ∀ i j, DifferentiableOn ℂ (A i j) U'' := fun i j => by
    have := (hd'' 0).holF i (finSumFinEquiv (Sum.inl j))
    rw [hd''0] at this
    simpa [catCols] using this
  have hTU : ∀ i j, DifferentiableOn ℂ (T i j) U'' := fun i j => by
    have := (hd'' 0).holF i (finSumFinEquiv (Sum.inr j))
    rw [hd''0] at this
    simpa [catCols] using this
  have hC'U : ∀ i j, DifferentiableOn ℂ (C' i j) U' := fun i j => by
    have := (hd' 0).holF i j
    rw [hd'0] at this
    exact this
  -- an open neighbourhood of `x` where everything holds
  have hev2 : ∀ᶠ y in 𝓝 x, y ∈ V₁ ∧ (∀ i j, ∑ l, A i l y * Q l j y = ∑ l, T i l y * C' l j y) ∧
      (∀ i j, DifferentiableAt ℂ (Q i j) y) ∧ (∀ j k, DifferentiableAt ℂ (Zc j k) y) ∧
      ∀ l j, (∑ m, Xm l m y * Ym m j y - if l = j then 1 else 0) =
        ∑ k, Zc j k y * hsFin d' d'' φ 1 l k y :=
    (Filter.eventually_of_mem (hV₁o.mem_nhds hxV₁) fun y hy => hy).and (hQ.and
      ((eventually_all.2 fun i => eventually_all.2 fun j => hQh i j).and
      ((eventually_all.2 fun j => eventually_all.2 fun k => hZc j k).and
      (eventually_all.2 fun l => eventually_all.2 fun j => hZcol j l))))
  obtain ⟨V, hVsub, hVo, hxV⟩ := _root_.eventually_nhds_iff.1 hev2
  have hVV₁ : V ⊆ V₁ := fun y hy => (hVsub y hy).1
  have hdV : ∀ k i j, DifferentiableOn ℂ (hsFin d' d'' φ k i j) V :=
    fun k i j => ((hR k).holF i j).mono hVV₁
  have hAnewV : ∀ i j, DifferentiableOn ℂ (Anew i j) V := by
    intro i j
    show DifferentiableOn ℂ (fromBlocks (1 : Matrix (Fin t) (Fin t) (X → ℂ)) 0 (-T) A (eS t a i)
      (eS t b j)) V
    rcases eS t a i with i' | i' <;> rcases eS t b j with j' | j'
    · show DifferentiableOn ℂ ((1 : Matrix (Fin t) (Fin t) (X → ℂ)) i' j') V
      rw [Matrix.one_apply]
      split_ifs
      · exact differentiableOn_const (1 : ℂ)
      · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (0 : ℂ)
    · exact ((hTU i' j').neg).mono (hVV₁.trans hV₁U'')
    · exact (hAU i' j').mono (hVV₁.trans hV₁U'')
  have hXV : ∀ l j, DifferentiableOn ℂ (Xm l j) V := fun l j => differentiableOn_const _
  have hYV : ∀ i l, DifferentiableOn ℂ (Ym i l) V := by
    intro i l
    show DifferentiableOn ℂ (fun y => (fromBlocks (valMat y C') (phiMat : Matrix (Fin t) (Fin (b + t)) ℂ)
      (valMat y Q) (y22Mat : Matrix (Fin b) (Fin (b + t)) ℂ)) (eS t b i)
        (eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l)) V
    rcases eS t b i with i' | i' <;> rcases eH (rankSeq t c s') (rankSeq a (b + t) s'') 1 l with l' | l'
    · exact (hC'U i' l').mono (hVV₁.trans hV₁U')
    · exact differentiableOn_const _
    · exact fun y hy => ((hVsub y hy).2.2.1 i' l').differentiableWithinAt
    · exact differentiableOn_const _
  have hZV : ∀ k j, DifferentiableOn ℂ (fun y => Zc j k y) V :=
    fun k j y hy => ((hVsub y hy).2.2.2.1 j k).differentiableWithinAt
  -- the presentation change, then the removal of the identity block
  obtain ⟨δ1, hδ1, hδ10, hδ1ex, hδ1split⟩ := exists_presentationChange (b := t + b) hVo hdV
    (fun k => (hR k).mono hVV₁) (A := Anew) hAnewV hXV hYV (Zm := fun k j y => Zc j k y) hZV
    (fun y _ i j => h0id y i j) (fun y hy i j => h1id y (hVsub y hy).2.1 i j)
    (fun y hy i j => by
      refine Eq.trans ?_ ((hVsub y hy).2.2.2.2 i j).symm
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _)
  obtain ⟨δ2, hδ2, hδ20, hδ2ex, hδ2split⟩ := exists_blockRemoval (t := t) (a := a) (b := b)
    (s := pcS (hsRank (rankSeq t c s') (rankSeq a (b + t) s'')) (t + b)) hVo (δ := δ1) hδ1 hδ1ex
    (N := -T) (fun i j => ((hTU i j).neg).mono (hVV₁.trans hV₁U''))
    (A := A) (fun i j => (hAU i j).mono (hVV₁.trans hV₁U'')) (fun i j => by rw [hδ10])
  refine ⟨V, pcS (hsRank (rankSeq t c s') (rankSeq a (b + t) s'')) (t + b), δ2, hδ2,
    hVV₁.trans hV₁U', hVV₁.trans hV₁U'', hVo, hxV, hδ20, hδ2ex, fun k hk => ?_,
    fun K _ hKV M ⟨t1, ht1⟩ ⟨t2, ht2⟩ => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    show rankSeq t c s' (j + 4) + rankSeq a (b + t) s'' (j + 4) = 0
    rw [htail' _ (by omega), htail'' _ (by omega)]
  · obtain ⟨t3, ht3⟩ := splitBy_hsFin K (hKV.trans hVV₁) (fun k i j => ((hd' k).holF i j).mono hV₁U')
      (fun k i j => ((hd'' k).holF i j).mono hV₁U'') hφV hidV ht1 ht2
    obtain ⟨t4, ht4⟩ := hδ1split K hKV M ⟨t3, ht3⟩
    exact hδ2split K hKV M ⟨t4, ht4⟩

end Ext

end
end Hironaka.HironakaG10FlatExtensionStep
