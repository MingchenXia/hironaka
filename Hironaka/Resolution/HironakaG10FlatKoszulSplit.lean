import Hironaka.Resolution.HironakaG10FlatSplitComplex

/-! # The Koszul step in all degrees: privilege for sheaves killed by a coordinate

Douady 1966, §7 n° 2, Prop. 5 Cor. (Banach core, all degrees). Let `R'` (think `B(K')`) and `R`
(think `B(K' × D̄)`) be normed algebras with a **division by `w`** (`RingDiv`): a bounded ring map
`ι : R' → R` (pull-back) and bounded maps `rem : R → R'`, `quot : R → R` with `x = w quot x + ι (rem x)`,
`rem (w x) = 0`, `quot (w x) = x`, `rem (ι a x) = a rem x`, `quot (ι a x) = ι a quot x`.

For a chain `e_k : R'^{r (k+1)} → R'^{r k}` the **Koszul chain** of `w` on its pull-back (`kosMat`,
a `triMatrix`) is
`R^{r k} ⊕ R^{r (k-1)} ← R^{r (k+1)} ⊕ R^{r k}`, `(x, y) ↦ (ι(e_k) x + w y, −ι(e_{k−1}) y)` —
the matrices of the free resolution of `i_* coker e_0` (`i : {w = 0} ↪`). It is dominated by `e`:
`f x = (ι x, 0)`, `g (x, y) = rem x`, `h (x, y) = (0, quot x)` (`kosF`, `kosG`, `kosH`), so
**if `e` is split in degrees `1..m` (and `r (m+1) = 0`), the Koszul chain is split in degrees
`1..m+1`** (`splitBy_koszul`): privilege of `K'` for the fibre passes to `K' × D̄` for the sheaf
killed by `w`. BP: hironaka-g10-flat-koszul-split.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatKoszulSplit
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatSplitComplex
  HironakaG10FlatTriangularExtension

/-- A division by `w` in `R` with remainders in `R'`. -/
structure RingDiv (R' R : Type*) [NormedRing R'] [NormedAlgebra ℂ R'] [NormedRing R]
    [NormedAlgebra ℂ R] where
  ι : R' →L[ℂ] R
  ι_mul : ∀ a b, ι (a * b) = ι a * ι b
  w : R
  rem : R →L[ℂ] R'
  quot : R →L[ℂ] R
  decomp : ∀ x, x = w * quot x + ι (rem x)
  rem_w : ∀ x, rem (w * x) = 0
  quot_w : ∀ x, quot (w * x) = x
  rem_ι_mul : ∀ a x, rem (ι a * x) = a * rem x
  quot_ι_mul : ∀ a x, quot (ι a * x) = ι a * quot x

variable {R' R : Type*} [NormedRing R'] [NormedAlgebra ℂ R'] [NormedRing R] [NormedAlgebra ℂ R]
  (V : RingDiv R' R) {r : ℕ → ℕ} (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R')

/-- The ranks shifted by one: `0, r 0, r 1, …`. -/
def shiftRank (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => r j

/-- `Fin (shiftRank r (k+1)) ≃ Fin (r k)`. -/
def shiftEquiv (r : ℕ → ℕ) (k : ℕ) : Fin (shiftRank r (k + 1)) ≃ Fin (r k) where
  toFun l := ⟨l.val, l.isLt⟩
  invFun i := ⟨i.val, i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The lower diagonal block `−ι(e_{k−1})` of the Koszul chain. -/
def kosLow : (k : ℕ) → Fin (shiftRank r k) → Fin (shiftRank r (k + 1)) → R
  | 0 => fun i => i.elim0
  | j + 1 => fun i l => -V.ι (e j (shiftEquiv r j i) (shiftEquiv r (j + 1) l))

/-- The off-diagonal block `w · 1`. -/
def kosMid (k : ℕ) : Fin (r k) → Fin (shiftRank r (k + 1)) → R :=
  fun i l => if l.val = i.val then V.w else 0

/-- **The Koszul chain** of `w` on the pull-back of `e`: `[ι(e_k)  w; 0  −ι(e_{k−1})]`. -/
def kosMat (k : ℕ) : Fin (r k) ⊕ Fin (shiftRank r k) → Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R :=
  triMatrix (fun i l => V.ι (e k i l)) (kosMid V k) (kosLow V e k)

/-- `f x = (ι x, 0)`. -/
def kosF (k : ℕ) : (Fin (r k) → R') →L[ℂ] (Fin (r k) ⊕ Fin (shiftRank r k) → R) :=
  ContinuousLinearMap.pi fun s => Sum.elim (fun i => V.ι.comp (ContinuousLinearMap.proj i))
    (fun _ => 0) s

/-- `g (x, y) = rem x`. -/
def kosG (k : ℕ) : (Fin (r k) ⊕ Fin (shiftRank r k) → R) →L[ℂ] (Fin (r k) → R') :=
  ContinuousLinearMap.pi fun i => V.rem.comp (ContinuousLinearMap.proj (Sum.inl i))

/-- `h (x, y) = (0, quot x)`. -/
def kosH (k : ℕ) :
    (Fin (r k) ⊕ Fin (shiftRank r k) → R) →L[ℂ] (Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R) :=
  ContinuousLinearMap.pi fun s => Sum.elim (fun _ => 0)
    (fun l => V.quot.comp (ContinuousLinearMap.proj (Sum.inl (shiftEquiv r k l)))) s

theorem kosF_apply (k : ℕ) (x : Fin (r k) → R') (s : Fin (r k) ⊕ Fin (shiftRank r k)) :
    kosF (r := r) V k x s = Sum.elim (fun i => V.ι (x i)) (fun _ => 0) s := by
  cases s <;> rfl

theorem kosG_apply (k : ℕ) (v : Fin (r k) ⊕ Fin (shiftRank r k) → R) (i : Fin (r k)) :
    kosG (r := r) V k v i = V.rem (v (Sum.inl i)) := rfl

theorem kosH_apply_inl (k : ℕ) (v : Fin (r k) ⊕ Fin (shiftRank r k) → R) (i : Fin (r (k + 1))) :
    kosH (r := r) V k v (Sum.inl i) = 0 := rfl

theorem kosH_apply_inr (k : ℕ) (v : Fin (r k) ⊕ Fin (shiftRank r k) → R)
    (l : Fin (shiftRank r (k + 1))) :
    kosH (r := r) V k v (Sum.inr l) = V.quot (v (Sum.inl (shiftEquiv r k l))) := rfl

/-- The operator of the Koszul chain on the first block. -/
theorem kosMat_apply_inl (k : ℕ) (v : Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R) (i : Fin (r k)) :
    matrixOperator (kosMat V e k) v (Sum.inl i) =
      ∑ l, V.ι (e k i l) * v (Sum.inl l) + V.w * v (Sum.inr ((shiftEquiv r k).symm i)) := by
  rw [matrixOperator_apply, Fintype.sum_sum_type]
  congr 1
  simp only [kosMat, triMatrix, Sum.elim_inr, kosMid]
  rw [Finset.sum_eq_single ((shiftEquiv r k).symm i)]
  · rw [if_pos (show ((shiftEquiv r k).symm i).val = i.val from rfl)]
  · intro l _ hl
    rw [if_neg (show ¬(l.val = i.val) from fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The operator of the Koszul chain on the second block. -/
theorem kosMat_apply_inr (k : ℕ) (v : Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R)
    (i : Fin (shiftRank r k)) :
    matrixOperator (kosMat V e k) v (Sum.inr i) = ∑ l, kosLow V e k i l * v (Sum.inr l) := by
  rw [matrixOperator_apply, Fintype.sum_sum_type]
  simp [kosMat, triMatrix]

/-- `f` is a chain map. -/
theorem kos_hf (k : ℕ) (x : Fin (r (k + 1)) → R') :
    matrixOperator (kosMat V e k) (kosF V (k + 1) x) = kosF V k (matrixOperator (e k) x) := by
  funext s
  rcases s with i | i
  · rw [kosMat_apply_inl, kosF_apply, kosF_apply]
    simp only [kosF_apply, Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero, matrixOperator_apply,
      map_sum, V.ι_mul]
  · rw [kosMat_apply_inr, kosF_apply]
    simp only [kosF_apply, Sum.elim_inr, mul_zero, Finset.sum_const_zero]

/-- `g` is a chain map. -/
theorem kos_hg (k : ℕ) (v : Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R) :
    matrixOperator (e k) (kosG V (k + 1) v) = kosG V k (matrixOperator (kosMat V e k) v) := by
  funext i
  rw [kosG_apply, kosMat_apply_inl, matrixOperator_apply, map_add, map_sum, V.rem_w, add_zero]
  exact Finset.sum_congr rfl fun l _ => by rw [kosG_apply, V.rem_ι_mul]

/-- The homotopy `1 − f g = D h + h D`. -/
theorem kos_hh (k : ℕ) (v : Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → R) :
    v - kosF V (k + 1) (kosG V (k + 1) v) =
      matrixOperator (kosMat V e (k + 1)) (kosH V (k + 1) v) +
        kosH V k (matrixOperator (kosMat V e k) v) := by
  funext s
  rcases s with i | i
  · simp only [Pi.sub_apply, Pi.add_apply, kosF_apply, Sum.elim_inl, kosG_apply]
    rw [kosMat_apply_inl, kosH_apply_inl]
    simp only [kosH_apply_inl, kosH_apply_inr, mul_zero, Finset.sum_const_zero, zero_add, add_zero,
      Equiv.apply_symm_apply]
    rw [sub_eq_iff_eq_add]
    exact V.decomp _
  · simp only [Pi.sub_apply, Pi.add_apply, kosF_apply, Sum.elim_inr, sub_zero]
    rw [kosMat_apply_inr, kosH_apply_inr, kosMat_apply_inl, map_add, map_sum, V.quot_w]
    simp only [kosH_apply_inr, kosLow, V.quot_ι_mul, neg_mul, Finset.sum_neg_distrib,
      Equiv.symm_apply_apply]
    rw [Fintype.sum_equiv (shiftEquiv r (k + 1)) _
      (fun l => V.ι (e k ((shiftEquiv r k) i) l) * V.quot (v (Sum.inl l))) (fun _ => rfl)]
    abel

/-- A split chain with top module `0` is split one degree higher. -/
theorem splitBy_succ_of_top {t : (k : ℕ) → (Fin (r k) → R') →L[ℂ] (Fin (r (k + 1)) → R')} {m : ℕ}
    (ht : SplitBy (chainOp e) t m) (htop : r (m + 1) = 0) : SplitBy (chainOp e) t (m + 1) := by
  intro k hk x
  by_cases hkm : k < m
  · exact ht k hkm x
  · have hk' : k = m := by omega
    subst hk'
    funext j
    exact (Fin.cast htop j).elim0

/-- **The Koszul step in all degrees** (Douady 1966, §7 Prop. 5 Cor., Banach core): if the chain
`e` over `R'` is split in degrees `1..m` and `r (m+1) = 0`, the Koszul chain of `w` on its pull-back
to `R` is split in degrees `1..m+1`. -/
theorem splitBy_koszul {t : (k : ℕ) → (Fin (r k) → R') →L[ℂ] (Fin (r (k + 1)) → R')} {m : ℕ}
    (ht : SplitBy (chainOp e) t m) (htop : r (m + 1) = 0) :
    SplitBy (fun k => matrixOperator (kosMat V e k))
      (fun k => (kosF V (k + 1)).comp ((t k).comp (kosG V k)) + kosH V k) (m + 1) :=
  SplitBy.of_dominated' (splitBy_succ_of_top e ht htop) (fun k => kosF V k) (fun k => kosG V k)
    (fun k => kosH V k) (fun k x => kos_hf V e k x) (fun k v => kos_hg V e k v)
    (fun k _ v => kos_hh V e k v)

end
end Hironaka.HironakaG10FlatKoszulSplit
