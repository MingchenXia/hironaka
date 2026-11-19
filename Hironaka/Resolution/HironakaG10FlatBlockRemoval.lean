import Hironaka.Resolution.HironakaG10FlatHorseshoe

/-! # Removing an identity block from the first matrix of a resolution

If a resolution `Q` starts with `δ₀ = [1 0; N A] : L_t ⊕ L_b → L_t ⊕ L_a`, then `coker δ₀ = coker A` and
the chain `Q'` with `δ'₀ = A`, `δ'₁ = π_b δ₁` (the `L_b`-rows of `δ₁`; the `L_t`-rows vanish since
`δ₀ δ₁ = 0`) and `δ'_k = δ_k` (`k ≥ 2`) is a resolution, dominated by `Q`
(`f = ([−N | 1], [0 | 1], 1, …)`, `g = ((0, 1), (0, 1), 1, …)`, `h = 0`), hence privileged wherever
`Q` is. Used after the presentation change in the extension step of Douady's §7 Th. 1.

* Over any ring (`BRData`, `brδ`, `brf`, `brg`): `br_comp`, `br_exact`, `br_hf`, `br_hg`, `br_hh`,
  `splitBy_br`.
* **`exists_blockRemoval`** (holomorphic matrices on an open `U`).
BP: hironaka-g10-flat-block-removal.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatBlockRemoval
noncomputable section
open OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart HironakaG10FlatGermChain
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatSplitComplex HironakaG10FlatPrivilegedNbhd
  HironakaG10FlatPresentationChange HironakaG10FlatHorseshoe Matrix

/-! ## Over a ring -/

/-- The data: a chain `δ` with ranks `t + a, t + b, s 0, …` and the blocks `N`, `A`. -/
structure BRData (T : Type*) (t a b : ℕ) (s : ℕ → ℕ) where
  δ : (k : ℕ) → Matrix (Fin (rankSeq (t + a) (t + b) s k)) (Fin (rankSeq (t + a) (t + b) s (k + 1))) T
  N : Matrix (Fin a) (Fin t) T
  A : Matrix (Fin a) (Fin b) T

section Alg
variable {T : Type*} [Ring T] {t a b : ℕ} {s : ℕ → ℕ}

/-- `δ₀ = [1 0; N A]` and `δ_k δ_{k+1} = 0`. -/
structure BRData.Good (D : BRData T t a b s) : Prop where
  h0 : (D.δ 0 : Matrix (Fin (t + a)) (Fin (t + b)) T) =
    (fromBlocks (1 : Matrix (Fin t) (Fin t) T) 0 D.N D.A).submatrix (eS t a) (eS t b)
  comp : ∀ k, D.δ k * D.δ (k + 1) = 0

/-- `δ₀`, `δ₁` and `δ_{k+2}` with their natural types. -/
def BRData.δ0 (D : BRData T t a b s) : Matrix (Fin (t + a)) (Fin (t + b)) T := D.δ 0
def BRData.δ1 (D : BRData T t a b s) : Matrix (Fin (t + b)) (Fin (s 0)) T := D.δ 1
def BRData.δs (D : BRData T t a b s) (k : ℕ) : Matrix (Fin (s k)) (Fin (s (k + 1))) T := D.δ (k + 2)

/-- The `L_t`-rows of `δ₁`. -/
def BRData.top (D : BRData T t a b s) : Matrix (Fin t) (Fin (s 0)) T :=
  (D.δ 1).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id

/-- The `L_b`-rows of `δ₁`. -/
def BRData.bot (D : BRData T t a b s) : Matrix (Fin b) (Fin (s 0)) T :=
  (D.δ 1).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id

variable {D : BRData T t a b s}

theorem BRData.δ1_eq (D : BRData T t a b s) :
    (D.δ 1 : Matrix (Fin (t + b)) (Fin (s 0)) T) =
      (fromRows D.top D.bot).submatrix (eS t b) (Equiv.refl _) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  show D.δ 1 (finSumFinEquiv i') j = fromRows D.top D.bot (finSumFinEquiv.symm (finSumFinEquiv i')) j
  rw [Equiv.symm_apply_apply]
  rcases i' with i' | i' <;> rfl

theorem BRData.Good.top_bot (hD : D.Good) : D.top = 0 ∧ D.A * D.bot = 0 := by
  have h2 : (fromBlocks (1 : Matrix (Fin t) (Fin t) T) 0 D.N D.A).submatrix (eS t a) (eS t b) *
      (fromRows D.top D.bot).submatrix (eS t b) (Equiv.refl _) = 0 := by
    rw [← hD.h0, ← D.δ1_eq]
    exact hD.comp 0
  rw [submatrix_mul_equiv] at h2
  have h3 : fromBlocks (1 : Matrix (Fin t) (Fin t) T) 0 D.N D.A * fromRows D.top D.bot = 0 := by
    have := congrArg (fun M => M.submatrix (eS t a).symm (Equiv.refl (Fin (s 0)))) h2
    simpa using this
  rw [fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, ← fromRows_zero,
    fromRows_inj.eq_iff] at h3
  obtain ⟨h4, h5⟩ := h3
  refine ⟨h4, ?_⟩
  rw [h4, Matrix.mul_zero, zero_add] at h5
  exact h5

/-- **The chain without the identity block**: `A, π_b δ₁, δ₂, …`. -/
def brδ (D : BRData T t a b s) : (k : ℕ) → Matrix (Fin (rankSeq a b s k)) (Fin (rankSeq a b s (k + 1))) T
  | 0 => D.A
  | 1 => D.bot
  | k + 2 => D.δ (k + 2)

/-- The chain map `f : Q → Q'`. -/
def brf (D : BRData T t a b s) : (k : ℕ) → Matrix (Fin (rankSeq a b s k)) (Fin (rankSeq (t + a) (t + b) s k)) T
  | 0 => (fromCols (-D.N) (1 : Matrix (Fin a) (Fin a) T)).submatrix (Equiv.refl (Fin a)) (eS t a)
  | 1 => (fromCols (0 : Matrix (Fin b) (Fin t) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (Equiv.refl (Fin b)) (eS t b)
  | k + 2 => (1 : Matrix (Fin (s k)) (Fin (s k)) T)

/-- The chain map `g : Q' → Q`. -/
def brg (_D : BRData T t a b s) : (k : ℕ) → Matrix (Fin (rankSeq (t + a) (t + b) s k)) (Fin (rankSeq a b s k)) T
  | 0 => (fromRows (0 : Matrix (Fin t) (Fin a) T) (1 : Matrix (Fin a) (Fin a) T)).submatrix (eS t a)
      (Equiv.refl (Fin a))
  | 1 => (fromRows (0 : Matrix (Fin t) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix (eS t b)
      (Equiv.refl (Fin b))
  | k + 2 => (1 : Matrix (Fin (s k)) (Fin (s k)) T)

theorem br_comp (hD : D.Good) : ∀ k, brδ D k * brδ D (k + 1) = 0
  | 0 => hD.top_bot.2
  | 1 => by
    show D.bot * (show Matrix (Fin (s 0)) (Fin (s 1)) T from D.δ 2) = 0
    have := congrArg (fun M => M.submatrix (fun i : Fin b => finSumFinEquiv (Sum.inr i)) id)
      (hD.comp 1)
    exact this
  | k + 2 => hD.comp (k + 2)

theorem br_exact (hD : D.Good) (hP : ∀ k, MatExact (D.δ (k + 1)) (D.δ k)) :
    ∀ k, MatExact (brδ D (k + 1)) (brδ D k)
  | 0 => by
    rintro (v : Fin b → T) hv
    have hv' : D.A *ᵥ v = 0 := hv
    have hw : (fromBlocks (1 : Matrix (Fin t) (Fin t) T) 0 D.N D.A).submatrix (eS t a) (eS t b) *ᵥ
        (Sum.elim (0 : Fin t → T) v ∘ eS t b : Fin (t + b) → T) = 0 := by
      rw [submatrix_mulVec_equiv]
      have : (Sum.elim (0 : Fin t → T) v ∘ ⇑(eS t b)) ∘ ⇑(eS t b).symm =
          Sum.elim (0 : Fin t → T) v := by
        funext j; simp
      rw [this, fromBlocks_mulVec]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add, add_zero, hv']
      funext i
      rcases (eS t a) i with i' | i' <;> simp
    rw [← hD.h0] at hw
    obtain ⟨c, hc⟩ := hP 0 _ hw
    refine ⟨c, ?_⟩
    funext i
    have := congrFun hc (finSumFinEquiv (Sum.inr i))
    simp only [Function.comp_apply, eS, Equiv.symm_apply_apply] at this
    exact this
  | 1 => by
    rintro (v : Fin (s 0) → T) hv
    have hv' : D.bot *ᵥ v = 0 := hv
    have hw : (fromRows D.top D.bot).submatrix (eS t b) (Equiv.refl _) *ᵥ v = 0 := by
      rw [submatrix_mulVec_equiv, fromRows_mulVec, hD.top_bot.1, zero_mulVec]
      simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, hv']
      funext i
      rcases (eS t b) i with i' | i' <;> simp
    rw [← D.δ1_eq] at hw
    exact hP 1 v hw
  | k + 2 => hP (k + 2)

theorem BRData.Good.h0' (hD : D.Good) :
    D.δ0 = (fromBlocks (1 : Matrix (Fin t) (Fin t) T) 0 D.N D.A).submatrix (eS t a) (eS t b) := hD.h0

theorem BRData.δ1_eq' (D : BRData T t a b s) :
    D.δ1 = (fromRows D.top D.bot).submatrix (eS t b) (Equiv.refl _) := D.δ1_eq

theorem br_hf (hD : D.Good) : ∀ k, brδ D k * brf D (k + 1) = brf D k * D.δ k
  | 0 => by
    show D.A * (fromCols (0 : Matrix (Fin b) (Fin t) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (Equiv.refl (Fin b)) (eS t b) = (fromCols (-D.N) (1 : Matrix (Fin a) (Fin a) T)).submatrix
        (Equiv.refl (Fin a)) (eS t a) * D.δ0
    rw [hD.h0', submatrix_mul_equiv, fromCols_mul_fromBlocks]
    rw [show D.A * (fromCols (0 : Matrix (Fin b) (Fin t) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (Equiv.refl (Fin b)) (eS t b) = (D.A * fromCols (0 : Matrix (Fin b) (Fin t) T) 1).submatrix
        (Equiv.refl (Fin a)) (eS t b) from rfl, mul_fromCols]
    simp
  | 1 => by
    show D.bot * (1 : Matrix (Fin (s 0)) (Fin (s 0)) T) = (fromCols (0 : Matrix (Fin b) (Fin t) T)
      (1 : Matrix (Fin b) (Fin b) T)).submatrix (Equiv.refl (Fin b)) (eS t b) * D.δ1
    rw [D.δ1_eq', submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.zero_mul, zero_add,
      Matrix.one_mul, Matrix.mul_one]
    rfl
  | k + 2 => by
    show D.δs k * (1 : Matrix (Fin (s (k + 1))) (Fin (s (k + 1))) T) =
      (1 : Matrix (Fin (s k)) (Fin (s k)) T) * D.δs k
    rw [Matrix.mul_one, Matrix.one_mul]

theorem br_hg (hD : D.Good) : ∀ k, D.δ k * brg D (k + 1) = brg D k * brδ D k
  | 0 => by
    show D.δ0 * (fromRows (0 : Matrix (Fin t) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (eS t b) (Equiv.refl (Fin b)) = (fromRows (0 : Matrix (Fin t) (Fin a) T)
        (1 : Matrix (Fin a) (Fin a) T)).submatrix (eS t a) (Equiv.refl (Fin a)) * D.A
    rw [hD.h0', submatrix_mul_equiv, fromBlocks_mul_fromRows]
    rw [show (fromRows (0 : Matrix (Fin t) (Fin a) T) (1 : Matrix (Fin a) (Fin a) T)).submatrix
      (eS t a) (Equiv.refl (Fin a)) * D.A = (fromRows (0 : Matrix (Fin t) (Fin a) T) 1 * D.A).submatrix
        (eS t a) (Equiv.refl (Fin b)) from rfl, fromRows_mul]
    simp
  | 1 => by
    show D.δ1 * (1 : Matrix (Fin (s 0)) (Fin (s 0)) T) = (fromRows (0 : Matrix (Fin t) (Fin b) T)
      (1 : Matrix (Fin b) (Fin b) T)).submatrix (eS t b) (Equiv.refl (Fin b)) * D.bot
    rw [Matrix.mul_one, D.δ1_eq', hD.top_bot.1]
    rw [show (fromRows (0 : Matrix (Fin t) (Fin b) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (eS t b) (Equiv.refl (Fin b)) * D.bot = (fromRows (0 : Matrix (Fin t) (Fin b) T) 1 * D.bot).submatrix
        (eS t b) (Equiv.refl (Fin (s 0))) from rfl, fromRows_mul, Matrix.zero_mul, Matrix.one_mul]
  | k + 2 => by
    show D.δs k * (1 : Matrix (Fin (s (k + 1))) (Fin (s (k + 1))) T) =
      (1 : Matrix (Fin (s k)) (Fin (s k)) T) * D.δs k
    rw [Matrix.mul_one, Matrix.one_mul]

theorem br_hh : ∀ k, brf D (k + 1) * brg D (k + 1) = 1
  | 0 => by
    show (fromCols (0 : Matrix (Fin b) (Fin t) T) (1 : Matrix (Fin b) (Fin b) T)).submatrix
      (Equiv.refl (Fin b)) (eS t b) * (fromRows (0 : Matrix (Fin t) (Fin b) T)
        (1 : Matrix (Fin b) (Fin b) T)).submatrix (eS t b) (Equiv.refl (Fin b)) =
      (1 : Matrix (Fin b) (Fin b) T)
    rw [submatrix_mul_equiv, fromCols_mul_fromRows]
    simp
  | k + 1 => by
    show (1 : Matrix (Fin (s k)) (Fin (s k)) T) * (1 : Matrix (Fin (s k)) (Fin (s k)) T) = 1
    rw [Matrix.mul_one]

end Alg

/-! ## Splittings over a normed ring -/

section Split
variable {T : Type*} [NormedRing T] [NormedAlgebra ℂ T] {t a b : ℕ} {s : ℕ → ℕ}

/-- **Removing the identity block preserves splittings.** -/
theorem splitBy_br (D : BRData T t a b s) (hD : D.Good) {M : ℕ}
    {tQ : (k : ℕ) → (Fin (rankSeq (t + a) (t + b) s k) → T) →L[ℂ]
      (Fin (rankSeq (t + a) (t + b) s (k + 1)) → T)} (ht : SplitBy (chainOp D.δ) tQ M) :
    ∃ t' : (k : ℕ) → (Fin (rankSeq a b s k) → T) →L[ℂ] (Fin (rankSeq a b s (k + 1)) → T),
      SplitBy (chainOp (brδ D)) t' M :=
  ⟨_, ht.of_dominated' (fun k => matrixOperator (brf D k)) (fun k => matrixOperator (brg D k))
    (fun k => matrixOperator (0 : Matrix (Fin (rankSeq a b s (k + 1))) (Fin (rankSeq a b s k)) T))
    (fun k x => matrixOperator_comp_eq (M := brδ D k) (N := brf D (k + 1)) (M' := brf D k)
      (N' := D.δ k) (br_hf hD k) x)
    (fun k y => matrixOperator_comp_eq (M := D.δ k) (N := brg D (k + 1)) (M' := brg D k)
      (N' := brδ D k) (br_hg hD k) y)
    (fun k _ y => matrixOperator_homotopy (F := brf D (k + 1)) (G := brg D (k + 1))
      (D1 := brδ D (k + 1))
      (H1 := (0 : Matrix (Fin (rankSeq a b s (k + 2))) (Fin (rankSeq a b s (k + 1))) T))
      (H0 := (0 : Matrix (Fin (rankSeq a b s (k + 1))) (Fin (rankSeq a b s k)) T)) (D0 := brδ D k)
      (by
        show (1 : Matrix (Fin (rankSeq a b s (k + 1))) (Fin (rankSeq a b s (k + 1))) T) -
          brf D (k + 1) * brg D (k + 1) = brδ D (k + 1) *
            (0 : Matrix (Fin (rankSeq a b s (k + 2))) (Fin (rankSeq a b s (k + 1))) T) +
          (0 : Matrix (Fin (rankSeq a b s (k + 1))) (Fin (rankSeq a b s k)) T) * brδ D k
        rw [br_hh, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]) y)⟩

end Split

/-! ## Holomorphic matrices on an open set -/

section Function
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {t a b : ℕ} {s : ℕ → ℕ}

theorem germAt_one (y : X) : OkaGermBridge.germAt y (1 : X → ℂ) = 1 := by
  rw [show (1 : X → ℂ) = fun _ => 1 from rfl, germAt_const]
  exact map_one _

/-- **Removing an identity block** (holomorphic matrices on an open `U`): if `δ` is exact on `U` in
every degree with `δ₀ = [1 0; N A]`, the chain `A, π_b δ₁, δ₂, …` is exact on `U` in every degree and
split on every compact `K ⊆ U` on which `δ` is split. -/
theorem exists_blockRemoval (hU : IsOpen U)
    {δ : (k : ℕ) → Fin (rankSeq (t + a) (t + b) s k) → Fin (rankSeq (t + a) (t + b) s (k + 1)) → X → ℂ}
    (hδ : ∀ k i j, DifferentiableOn ℂ (δ k i j) U) (hex : ∀ k, ExactStartOn U (δ (k + 1)) (δ k))
    {N : Fin a → Fin t → X → ℂ} (hN : ∀ i j, DifferentiableOn ℂ (N i j) U)
    {A : Fin a → Fin b → X → ℂ} (hA : ∀ i j, DifferentiableOn ℂ (A i j) U)
    (h0 : ∀ i j, δ 0 i j = (fromBlocks (1 : Matrix (Fin t) (Fin t) (X → ℂ)) 0 N A) (eS t a i) (eS t b j)) :
    ∃ (δ' : (k : ℕ) → Fin (rankSeq a b s k) → Fin (rankSeq a b s (k + 1)) → X → ℂ)
      (hδ' : ∀ k i j, DifferentiableOn ℂ (δ' k i j) U),
      δ' 0 = A ∧ (∀ k, ExactStartOn U (δ' (k + 1)) (δ' k)) ∧
      ∀ (K : Set X) [CompactSpace K] (hKU : K ⊆ U) (M : ℕ),
        (∃ t' : (k : ℕ) → (Fin (rankSeq (t + a) (t + b) s k) → holSubalgebra K) →L[ℂ]
            (Fin (rankSeq (t + a) (t + b) s (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K hKU (δ k) (hδ k)) t' M) →
        ∃ t' : (k : ℕ) → (Fin (rankSeq a b s k) → holSubalgebra K) →L[ℂ]
            (Fin (rankSeq a b s (k + 1)) → holSubalgebra K),
          SplitBy (chainOp fun k => restrictMatrix K hKU (δ' k) (hδ' k)) t' M := by
  set Df : BRData (X → ℂ) t a b s := ⟨δ, N, A⟩ with hDf
  have hδ' : ∀ k i j, DifferentiableOn ℂ (brδ Df k i j) U := by
    intro k
    match k with
    | 0 => exact hA
    | 1 => exact fun i j => hδ 1 _ j
    | k + 2 => exact hδ (k + 2)
  -- the identities over the rings of germs, values and `B(K)`
  have hgood_g : ∀ y ∈ U, (⟨fun k => germMat y (δ k), germMat y N, germMat y A⟩ :
      BRData (HolGerm X) t a b s).Good := by
    intro y hy
    have hol : ∀ {ι κ : Type} (F : ι → κ → X → ℂ), (∀ i j, DifferentiableOn ℂ (F i j) U) →
        ∀ i j, HolAt (F i j) y := fun F hF i j => holAt_of_differentiableOn hU (hF i j) hy
    refine ⟨Matrix.ext fun i j => ?_, fun k => ?_⟩
    · show OkaGermBridge.germAt y (δ 0 i j) = (fromBlocks (1 : Matrix (Fin t) (Fin t) (HolGerm X)) 0
        (germMat y N) (germMat y A)) (eS t a i) (eS t b j)
      rw [h0 i j]
      rcases eS t a i with i' | i' <;> rcases eS t b j with j' | j'
      · show OkaGermBridge.germAt y ((1 : Matrix (Fin t) (Fin t) (X → ℂ)) i' j') =
          (1 : Matrix (Fin t) (Fin t) (HolGerm X)) i' j'
        rw [Matrix.one_apply, Matrix.one_apply]
        split_ifs
        · exact germAt_one y
        · exact germAt_zero y
      · exact germAt_zero y
      · rfl
      · rfl
    · show germMat y (δ k) * germMat y (δ (k + 1)) = 0
      rw [germMat_mul (hol _ (hδ k)) (hol _ (hδ (k + 1)))]
      refine germMat_eq_zero (fun i l => HolAt.fintype_sum fun j => (hol _ (hδ k) i j).mul
        (hol _ (hδ (k + 1)) j l)) ?_
      filter_upwards [hU.mem_nhds hy] with z hz i l
      exact (hex k).comp i l z hz
  have hgood_v : ∀ x ∈ U, (⟨fun k => valMat x (δ k), valMat x N, valMat x A⟩ :
      BRData ℂ t a b s).Good := by
    intro x hx
    refine ⟨Matrix.ext fun i j => ?_, fun k => Matrix.ext fun i l => (hex k).comp i l x hx⟩
    show δ 0 i j x = (fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 (valMat x N) (valMat x A))
      (eS t a i) (eS t b j)
    rw [h0 i j]
    rcases eS t a i with i' | i' <;> rcases eS t b j with j' | j'
    · show (1 : Matrix (Fin t) (Fin t) (X → ℂ)) i' j' x = (1 : Matrix (Fin t) (Fin t) ℂ) i' j'
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · rfl
    · rfl
    · rfl
  have hgerm : ∀ y k, germMat y (brδ Df k) =
      brδ (⟨fun k => germMat y (δ k), germMat y N, germMat y A⟩ : BRData (HolGerm X) t a b s) k := by
    intro y k
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => rfl
  have hval : ∀ x k, valMat x (brδ Df k) =
      brδ (⟨fun k => valMat x (δ k), valMat x N, valMat x A⟩ : BRData ℂ t a b s) k := by
    intro x k
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => rfl
  refine ⟨brδ Df, hδ', rfl, fun k => ?_, fun K _ hKU M ⟨tQ, htQ⟩ => ?_⟩
  · refine exactStartOn_of_matExact hU (hδ' k) (hδ' (k + 1)) (fun i l x hx => ?_) (fun y hy => ?_)
    · have := congrFun (congrFun (br_comp (hgood_v x hx) k) i) l
      rw [← hval, ← hval] at this
      exact this
    · rw [hgerm, hgerm]
      exact br_exact (hgood_g y hy) (fun k => matExact_of_exactStartOn hU (hex k) hy) k
  · set DK : BRData (holSubalgebra K) t a b s := ⟨fun k => restrictMatrix K hKU (δ k) (hδ k),
      restrictMatrix K hKU N hN, restrictMatrix K hKU A hA⟩ with hDK
    have hgood_K : DK.Good := by
      refine ⟨Matrix.ext fun i j => HironakaG10FlatPolydiscRemainderMap.ext_evalHom fun z => ?_,
        fun k => Matrix.ext fun i l => HironakaG10FlatPolydiscRemainderMap.ext_evalHom fun z => ?_⟩
      · show δ 0 i j z = HironakaG10FlatPolydiscRemainderMap.evalHom K z
          ((fromBlocks (1 : Matrix (Fin t) (Fin t) (holSubalgebra K)) 0 (restrictMatrix K hKU N hN)
            (restrictMatrix K hKU A hA)) (eS t a i) (eS t b j))
        rw [h0 i j]
        rcases eS t a i with i' | i' <;> rcases eS t b j with j' | j'
        · show (1 : Matrix (Fin t) (Fin t) (X → ℂ)) i' j' z =
            HironakaG10FlatPolydiscRemainderMap.evalHom K z ((1 : Matrix (Fin t) (Fin t) (holSubalgebra K)) i' j')
          rw [Matrix.one_apply, Matrix.one_apply]
          split_ifs
          · exact (map_one _).symm
          · exact (map_zero _).symm
        · exact (map_zero (HironakaG10FlatPolydiscRemainderMap.evalHom K z)).symm
        · rfl
        · rfl
      · simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.zero_apply, map_zero]
        exact (hex k).comp i l z (hKU z.2)
    obtain ⟨t', ht'⟩ := splitBy_br DK hgood_K htQ
    refine ⟨t', ?_⟩
    have hfun : (fun k => restrictMatrix K hKU (brδ Df k) (hδ' k)) = brδ DK := by
      funext k
      match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => rfl
    rw [hfun]
    exact ht'

end Function

end
end Hironaka.HironakaG10FlatBlockRemoval
