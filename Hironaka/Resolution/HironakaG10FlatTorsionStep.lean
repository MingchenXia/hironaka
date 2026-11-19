import Hironaka.Resolution.HironakaG10FlatKoszulExact
import Hironaka.Resolution.HironakaG10FlatKoszulPolydisc
import Hironaka.Resolution.HironakaG10FlatPresentationChange
import Hironaka.Resolution.HironakaG10FlatPrivilegedFlatStep

/-! # The torsion step of Douady's theorem of privileged neighbourhoods

Douady 1966, §7 n° 2 Prop. 5 Cor. and the torsion case of n° 4 Th. 1: a coherent sheaf
`𝓕 = coker C` on `ℂ × P` killed by the coordinate `w` near `(0, z₀)` (`w · 1 = C W`). If `e` is a free
resolution of the fibre `coker C(0,·)` on `U₀ ∋ z₀` (exact in every degree, ranks `0` beyond `m`),
then there is a finite free resolution `δ` of `𝓕` near `(z₀, 0)` (coordinates `P × ℂ`) with first
matrix `C` such that for EVERY compact regular-closed `K' ⊆ U₀` on which the `B(K')`-complex of `e`
is split and EVERY `ρ > 0` with `K' × D̄(0,ρ)` inside its domain, the `B(K' × D̄(0,ρ))`-complex of
`δ` is split.

* `restrict_kosChain`: on `K' × D̄(0,ρ)` the restricted holomorphic Koszul chain
  (`HironakaG10FlatKoszulExact.kosChain`) is `HironakaG10FlatKoszulSplit.kosMat` of the division by
  `w` (`HironakaG10FlatKoszulPolydisc.coordDiv`) on the `B(K')`-matrices of `e`.
* `splitBy_kosChain`: hence it is split (`splitBy_koszul`).
BP: hironaka-g10-flat-torsion-step.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Metric
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatTorsionStep
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatGermChain
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatFrischHolomorphicFlattener HironakaG10FlatKoszulSplit
  HironakaG10FlatSliceResolution HironakaG10FlatKoszulExact HironakaG10FlatKoszulPolydisc
  HironakaG10FlatPolydiscRemainderMap HironakaG10FlatFlatFamilyPrivilege HironakaG10FlatSplitComplex
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatResolutionPkg HironakaG10FlatPresentationChange

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {U₀ : Set P} {r : ℕ → ℕ}

/-! ## The `B(K' × D̄)`-complex of the Koszul chain -/

section Banach
variable [FiniteDimensional ℂ P] {K' : Set P} [CompactSpace K'] {ρ : ℝ}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]

/-- **The restricted Koszul chain is `kosMat` of the division by `w`.** -/
theorem restrict_kosChain (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) (hK'U₀ : K' ⊆ U₀)
    {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ}
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀)
    (hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' ((univ : Set ℂ) ×ˢ U₀)) (k : ℕ) (i) (j) :
    restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKV (swapMat (kosChain e he k))
        (differentiableOn_swapMat (kosChain_hol e he k)) i j =
      kosMat (coordDiv (K' := K') (ρ := ρ) hK' hρ) (fun k => restrictMatrix K' hK'U₀ (e k) (he k)) k i j := by
  apply ext_evalHom
  intro x
  have hx1 : (x : P × ℂ).1 ∈ K' := x.2.1
  rcases i with i | i <;> rcases j with j | j
  · show e k i j (x : P × ℂ).1 = extendZero K' ((restrict K' hK'U₀ (e k i j) (he k i j) :
      holSubalgebra K') : C(K', ℂ)) (x : P × ℂ).1
    rw [extendZero_of_mem K' _ hx1]
    rfl
  · show (kosMidA (wHol U₀) k i j).1 ((x : P × ℂ).2, (x : P × ℂ).1) =
      evalHom _ x (kosMid (coordDiv hK' hρ) k i j)
    simp only [kosMidA, kosMid]
    split_ifs
    · show (x : P × ℂ).2 = HironakaG10FlatDiscWeierstrassDivision.polyEval 1 coordCoeff (x : P × ℂ).1 (x : P × ℂ).2
      rw [polyEval_coordCoeff]
    · rfl
  · rfl
  · cases k with
    | zero => exact i.elim0
    | succ k =>
      show -e k i j (x : P × ℂ).1 = -extendZero K' ((restrict K' hK'U₀ (e k _ _) (he k _ _) :
        holSubalgebra K') : C(K', ℂ)) (x : P × ℂ).1
      rw [extendZero_of_mem K' _ hx1]
      rfl

/-- The ranks `r k + r (k-1)` of the Koszul chain. -/
def kosRank (r : ℕ → ℕ) (k : ℕ) : ℕ := r k + shiftRank r k

/-- `Fin (kosRank r k) ≃ Fin (r k) ⊕ Fin (shiftRank r k)`. -/
def eK (r : ℕ → ℕ) (k : ℕ) : Fin (kosRank r k) ≃ Fin (r k) ⊕ Fin (shiftRank r k) :=
  finSumFinEquiv.symm

/-- The Koszul chain with `Fin`-ranks. -/
def kosFin (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (k : ℕ) :
    Fin (kosRank r k) → Fin (kosRank r (k + 1)) → ℂ × P → ℂ :=
  fun i j => kosChain e he k (eK r k i) (eK r (k + 1) j)

theorem kosFin_hol (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (k : ℕ) (i) (j) :
    DifferentiableOn ℂ (kosFin e he k i j) ((univ : Set ℂ) ×ˢ U₀) :=
  kosChain_hol e he k _ _

theorem kosRank_eq_zero {m : ℕ} (htail : ∀ k, m < k → r k = 0) {k : ℕ} (hk : m + 1 < k) :
    kosRank r k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show r (j + 1) + r j = 0
  rw [htail (j + 1) (by omega), htail j (by omega)]

/-- **The `B(K' × D̄(0,ρ))`-complex of the Koszul chain is split in every degree** if the
`B(K')`-complex of `e` is split (ranks `0` beyond `m`). -/
theorem splitBy_kosFin (hK' : K' ⊆ closure (interior K')) (hρ : 0 < ρ) (hK'U₀ : K' ⊆ U₀)
    {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ}
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀)
    (hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' ((univ : Set ℂ) ×ˢ U₀)) {m : ℕ}
    (htail : ∀ k, m < k → r k = 0)
    {t : (k : ℕ) → (Fin (r k) → holSubalgebra K') →L[ℂ] (Fin (r (k + 1)) → holSubalgebra K')}
    (ht : SplitBy (chainOp fun k => restrictMatrix K' hK'U₀ (e k) (he k)) t m) (M : ℕ) :
    ∃ t' : (k : ℕ) → (Fin (kosRank r k) → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) →L[ℂ]
        (Fin (kosRank r (k + 1)) → holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)),
      SplitBy (chainOp fun k => restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKV
        (swapMat (kosFin e he k)) (differentiableOn_swapMat (kosFin_hol e he k))) t' M := by
  have h1 := splitBy_koszul (coordDiv (K' := K') (ρ := ρ) hK' hρ)
    (fun k => restrictMatrix K' hK'U₀ (e k) (he k)) ht (htail (m + 1) (by omega))
  have hfun : (fun k => matrixOperator (kosMat (coordDiv (K' := K') (ρ := ρ) hK' hρ)
      (fun k => restrictMatrix K' hK'U₀ (e k) (he k)) k)) = fun k =>
      matrixOperator (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKV (swapMat (kosChain e he k))
        (differentiableOn_swapMat (kosChain_hol e he k))) := by
    funext k
    congr 1
    funext i j
    exact (restrict_kosChain hK' hρ hK'U₀ he hKV k i j).symm
  rw [hfun] at h1
  obtain ⟨t', ht'⟩ := splitBy_relabel (r' := kosRank r) (eK r) h1
  exact ⟨t', splitBy_all ht' (fun k hk => kosRank_eq_zero htail hk) M⟩

end Banach

/-! ## Entries of the first Koszul matrix -/

theorem eK_zero (i : Fin (kosRank r 0)) : eK r 0 i = Sum.inl ⟨i.val, i.isLt⟩ :=
  finSumFinEquiv_symm_apply_castAdd (⟨i.val, i.isLt⟩ : Fin (r 0))

theorem kosChain_zero_inl (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (i : Fin (r 0)) (l : Fin (r 1)) (x : ℂ × P) :
    kosChain e he 0 (Sum.inl i) (Sum.inl l) x = e 0 i l x.2 := rfl

theorem kosChain_zero_inr (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (i : Fin (r 0)) (l : Fin (shiftRank r 1))
    (x : ℂ × P) : kosChain e he 0 (Sum.inl i) (Sum.inr l) x = if l.val = i.val then x.1 else 0 := by
  show (kosMidA (wHol U₀) 0 i l).1 x = _
  simp only [kosMidA]
  split_ifs <;> rfl

/-- A column of `X Y − 1` is a relation of `d₀` when `d₀ X = A` and `A Y = d₀`. -/
theorem sum_relation {ι κ μ : Type*} [Fintype κ] [Fintype μ] [DecidableEq κ] (d0 : ι → κ → ℂ)
    (X : κ → μ → ℂ) (Y : μ → κ → ℂ) (A : ι → μ → ℂ) (h0 : ∀ i m, ∑ l, d0 i l * X l m = A i m)
    (h1 : ∀ i j, ∑ m, A i m * Y m j = d0 i j) (i : ι) (j : κ) :
    ∑ l, (∑ m, X l m * Y m j - if l = j then 1 else 0) * d0 i l = 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm, sub_eq_zero, ← h1 i j]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← h0 i m, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The matrix `X = [1; C'']` (rows `Fin (r 1) ⊕ Fin (r 0)` relabelled). -/
def xMat (C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ) : Fin (kosRank r 1) → Fin (r 1) → ℂ × P → ℂ :=
  fun l j x => Sum.elim (fun l' : Fin (r 1) => if l' = j then (1 : ℂ) else 0)
    (fun l' : Fin (shiftRank r 1) => C'' l' j x) (eK r 1 l)

/-- The matrix `Y = [1 − W C'' | W]`. -/
def yMat (C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ) (W : Fin (r 1) → Fin (r 0) → ℂ × P → ℂ) :
    Fin (r 1) → Fin (kosRank r 1) → ℂ × P → ℂ :=
  fun j l x => Sum.elim (fun l' : Fin (r 1) => (if j = l' then (1 : ℂ) else 0) -
      ∑ m, W j m x * C'' m l' x) (fun l' : Fin (shiftRank r 1) => W j l' x) (eK r 1 l)

theorem xMat_inl {C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ} {l : Fin (kosRank r 1)} {l' : Fin (r 1)}
    (h : eK r 1 l = Sum.inl l') (j : Fin (r 1)) :
    xMat C'' l j = fun _ => if l' = j then (1 : ℂ) else 0 := by
  funext x; simp only [xMat, h, Sum.elim_inl]

theorem xMat_inr {C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ} {l : Fin (kosRank r 1)}
    {l' : Fin (shiftRank r 1)} (h : eK r 1 l = Sum.inr l') (j : Fin (r 1)) :
    xMat C'' l j = C'' l' j := by
  funext x; simp only [xMat, h, Sum.elim_inr]

theorem yMat_inl {C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ} {W : Fin (r 1) → Fin (r 0) → ℂ × P → ℂ}
    {l : Fin (kosRank r 1)} {l' : Fin (r 1)} (h : eK r 1 l = Sum.inl l') (j : Fin (r 1)) :
    yMat C'' W j l = fun x => (if j = l' then (1 : ℂ) else 0) - ∑ m, W j m x * C'' m l' x := by
  funext x; simp only [yMat, h, Sum.elim_inl]

theorem yMat_inr {C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ} {W : Fin (r 1) → Fin (r 0) → ℂ × P → ℂ}
    {l : Fin (kosRank r 1)} {l' : Fin (shiftRank r 1)} (h : eK r 1 l = Sum.inr l') (j : Fin (r 1)) :
    yMat C'' W j l = W j l' := by
  funext x; simp only [yMat, h, Sum.elim_inr]

theorem sum_eK_one (g : Fin (r 1) ⊕ Fin (shiftRank r 1) → ℂ) :
    ∑ l, g (eK r 1 l) = ∑ l : Fin (r 1), g (Sum.inl l) + ∑ l : Fin (shiftRank r 1), g (Sum.inr l) := by
  rw [Equiv.sum_comp (eK r 1) g, Fintype.sum_sum_type]

theorem sum_ite_val {n n' : ℕ} (i : Fin n) (hi : i.val < n') (f : Fin n' → ℂ) (c : ℂ) :
    ∑ l : Fin n', (if l.val = i.val then c else 0) * f l = c * f ⟨i.val, hi⟩ := by
  rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin n')]
  · rw [if_pos rfl]
  · intro l _ hl
    rw [if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `d₀ X = A` (with `C = π^*e₀ + w C''`). -/
theorem kos_h0 (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (C C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ)
    (x : ℂ × P) (hx : ∀ i j, C i j x - e 0 i j x.2 = x.1 * C'' i j x) (i : Fin (kosRank r 0))
    (j : Fin (r 1)) : ∑ l, kosFin e he 0 i l x * xMat C'' l j x = C ⟨i.val, i.isLt⟩ j x := by
  have h := sum_eK_one (r := r) (fun l' => kosChain e he 0 (eK r 0 i) l' x *
    Sum.elim (fun l' : Fin (r 1) => if l' = j then (1 : ℂ) else 0)
      (fun l' : Fin (shiftRank r 1) => C'' l' j x) l')
  refine h.trans ?_
  simp only [eK_zero, Sum.elim_inl, Sum.elim_inr, kosChain_zero_inl, kosChain_zero_inr, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [sum_ite_val (n' := shiftRank r 1) (⟨i.val, i.isLt⟩ : Fin (r 0)) i.isLt (fun l => C'' l j x) x.1]
  have := hx ⟨i.val, i.isLt⟩ j
  rw [sub_eq_iff_eq_add] at this
  rw [this, add_comm]
  rfl

/-- `A Y = d₀` (with `C W = w · 1`). -/
theorem kos_h1 (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (C C'' : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ)
    (W : Fin (r 1) → Fin (r 0) → ℂ × P → ℂ) (x : ℂ × P)
    (hx : ∀ i j, C i j x - e 0 i j x.2 = x.1 * C'' i j x)
    (hxW : ∀ i i', ∑ j, C i j x * W j i' x = if i = i' then x.1 else 0) (i : Fin (kosRank r 0))
    (l : Fin (kosRank r 1)) :
    ∑ j, C ⟨i.val, i.isLt⟩ j x * yMat C'' W j l x = kosFin e he 0 i l x := by
  set i' : Fin (r 0) := ⟨i.val, i.isLt⟩ with hi'
  show ∑ j, C i' j x * yMat C'' W j l x = kosChain e he 0 (eK r 0 i) (eK r 1 l) x
  rw [eK_zero]
  simp only [yMat]
  rcases (eK r 1 l) with l' | l'
  · simp only [Sum.elim_inl, kosChain_zero_inl, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    have hsw : ∑ j, ∑ m, C i' j x * (W j m x * C'' m l' x) = x.1 * C'' i' l' x := by
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, hxW, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [hsw, ← hx i' l']
    ring
  · simp only [Sum.elim_inr, kosChain_zero_inr]
    refine (hxW i' l').trans ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (congrArg Fin.val h1).symm h2
    · exact absurd (Fin.ext h2.symm) h1
    · rfl


/-! ## The torsion step -/

section Torsion
variable [FiniteDimensional ℂ P]

/-- **The torsion step of Douady's Th. 1** (Prop. 5 Cor.). Let `ℂ × P` have Oka's property, `e` a
chain exact on an open `U₀` in every degree with ranks `0` beyond `m` (a finite free resolution of the
fibre), and `C` a matrix holomorphic near `(0, z₀)` with `C(0,·) = e₀` near `z₀` and `w · 1 = C W`
near `(0, z₀)` (`coker C` is killed by `w`). Then there are an open `V ∋ (z₀, 0)` of `P × ℂ` and a
finite free resolution `δ` on `V` (ranks `rankSeq (r 0) (r 1) s'`) with first matrix `C` (swapped)
such that for every compact regular-closed `K' ⊆ U₀` on which the `B(K')`-complex of `e` is split and
every `ρ > 0` with `K' × D̄(0,ρ) ⊆ V`, `K' × D̄(0,ρ)` is privileged for `δ`. -/
theorem torsion_step (hX : OkaProperty (ℂ × P)) (hU₀ : IsOpen U₀) {m : ℕ}
    {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ} (hex : ∀ k, ExactStartOn U₀ (e (k + 1)) (e k))
    (htail : ∀ k, m < k → r k = 0) {C : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ} {z₀ : P} (hz₀ : z₀ ∈ U₀)
    (hC : ∀ i j, HolAt (C i j) ((0 : ℂ), z₀))
    (hC0 : ∀ᶠ z in 𝓝 z₀, ∀ i j, C i j ((0 : ℂ), z) = e 0 i j z)
    {W : Fin (r 1) → Fin (r 0) → ℂ × P → ℂ} (hW : ∀ i j, HolAt (W i j) ((0 : ℂ), z₀))
    (hCW : ∀ᶠ x in 𝓝 ((0 : ℂ), z₀), ∀ i i', ∑ j, C i j x * W j i' x = if i = i' then x.1 else 0) :
    ∃ (V : Set (P × ℂ)) (M : ℕ) (s' : ℕ → ℕ)
      (δ : (k : ℕ) → Fin (rankSeq (r 0) (r 1) s' k) → Fin (rankSeq (r 0) (r 1) s' (k + 1)) →
        P × ℂ → ℂ) (hδ : FiniteResolutionOn V M δ), IsOpen V ∧ (z₀, (0 : ℂ)) ∈ V ∧
      δ 0 = swapMat C ∧
      ∀ (K' : Set P) [CompactSpace K'] (hK'U₀ : K' ⊆ U₀), K' ⊆ closure (interior K') →
        (∃ t : (k : ℕ) → (Fin (r k) → holSubalgebra K') →L[ℂ] (Fin (r (k + 1)) → holSubalgebra K'),
          SplitBy (chainOp fun k => restrictMatrix K' hK'U₀ (e k) ((hex k).holF)) t m) →
        ∀ ρ : ℝ, 0 < ρ → ∀ (hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V)
          [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
          PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKV M δ hδ.hol := by
  set he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀ := fun k => (hex k).holF with hhe
  set y₀ : ℂ × P := ((0 : ℂ), z₀) with hy₀
  have hUo : IsOpen ((univ : Set ℂ) ×ˢ U₀) := isOpen_univ.prod hU₀
  have hy₀U : y₀ ∈ (univ : Set ℂ) ×ˢ U₀ := ⟨mem_univ _, hz₀⟩
  -- the Koszul chain with `Fin`-ranks is exact on `ℂ × U₀`
  have hKos : ∀ k, ExactStartOn ((univ : Set ℂ) ×ˢ U₀) (kosFin e he (k + 1)) (kosFin e he k) :=
    fun k => HironakaG10FlatReindex.exactStartOn_reindex (exactStartOn_kosChain hX hU₀ hex k)
      (eK r (k + 2)) (eK r (k + 1)) (eK r k)
  -- `C = π^* e₀ + w C''` near `(0, z₀)`
  have hdiv : ∀ i j, ∃ c : ℂ × P → ℂ, HolAt c y₀ ∧
      ∀ᶠ x in 𝓝 y₀, C i j x - e 0 i j x.2 = x.1 * c x := by
    intro i j
    refine exists_eq_fst_mul ((hC i j).sub (holAt_pull
      (holAt_of_differentiableOn hU₀ (he 0 i j) hz₀) 0)) rfl ?_
    filter_upwards [hC0] with z hz
    rw [hz i j, sub_self]
  choose C'' hC'' hCC'' using hdiv
  -- the relations `X Y − 1` of `d₀` lift through `d₁` near `(0, z₀)`
  have hev0 : ∀ᶠ x in 𝓝 y₀, (∀ i j, C i j x - e 0 i j x.2 = x.1 * C'' i j x) ∧
      (∀ i i', ∑ j, C i j x * W j i' x = if i = i' then x.1 else 0) :=
    (eventually_all.2 fun i => eventually_all.2 fun j => hCC'' i j).and hCW
  have hXh : ∀ l j, HolAt (xMat C'' l j) y₀ := by
    intro l j
    rcases h : eK r 1 l with l' | l'
    · rw [xMat_inl h]; exact holAt_const _ _
    · rw [xMat_inr h]; exact hC'' l' j
  have hYh : ∀ j l, HolAt (yMat C'' W j l) y₀ := by
    intro j l
    rcases h : eK r 1 l with l' | l'
    · rw [yMat_inl h]
      exact (holAt_const _ _).sub (HolAt.fintype_sum fun m => (hW j m).mul (hC'' m l'))
    · rw [yMat_inr h]; exact hW j l'
  have hlift : ∀ j : Fin (kosRank r 1), IsCombinationAt (columns (kosFin e he 1)) y₀
      (fun l x => ∑ m, xMat C'' l m x * yMat C'' W m j x - if l = j then 1 else 0) := by
    intro j
    refine (hKos 0).exact y₀ hy₀U _ ⟨fun l => (HolAt.fintype_sum fun m => (hXh l m).mul (hYh m j)).sub
      (holAt_const _ _), fun i => ?_⟩
    filter_upwards [hev0] with x ⟨hx, hxW⟩
    exact sum_relation (fun i l => kosFin e he 0 i l x) (fun l m => xMat C'' l m x)
      (fun m l => yMat C'' W m l x) (fun i m => C ⟨i.val, i.isLt⟩ m x)
      (fun i m => kos_h0 e he C C'' x hx i m) (fun i l => kos_h1 e he C C'' W x hx hxW i l) i j
  choose Zc hZc hZcol using hlift
  -- an open neighbourhood of `(0, z₀)` where everything holds
  have hev : ∀ᶠ x in 𝓝 y₀, x ∈ (univ : Set ℂ) ×ˢ U₀ ∧
      ((∀ i j, C i j x - e 0 i j x.2 = x.1 * C'' i j x) ∧
        (∀ i i', ∑ j, C i j x * W j i' x = if i = i' then x.1 else 0)) ∧
      (∀ i j, DifferentiableAt ℂ (C i j) x) ∧ (∀ i j, DifferentiableAt ℂ (C'' i j) x) ∧
      (∀ i j, DifferentiableAt ℂ (W i j) x) ∧ (∀ j k, DifferentiableAt ℂ (Zc j k) x) ∧
      ∀ l j, (∑ m, xMat C'' l m x * yMat C'' W m j x - if l = j then 1 else 0) =
        ∑ k, Zc j k x * kosFin e he 1 l k x := by
    refine (Filter.eventually_of_mem (hUo.mem_nhds hy₀U) fun x hx => hx).and (hev0.and ((eventually_all.2 fun i => eventually_all.2
      fun j => hC i j).and ((eventually_all.2 fun i => eventually_all.2 fun j => hC'' i j).and
      ((eventually_all.2 fun i => eventually_all.2 fun j => hW i j).and
      ((eventually_all.2 fun j => eventually_all.2 fun k => hZc j k).and
      (eventually_all.2 fun l => eventually_all.2 fun j => hZcol j l))))))
  obtain ⟨V, hVsub, hVo, hy₀V⟩ := _root_.eventually_nhds_iff.1 hev
  have hVU : V ⊆ (univ : Set ℂ) ×ˢ U₀ := fun x hx => (hVsub x hx).1
  -- holomorphy of the data on `V`
  have hA'V : ∀ i j, DifferentiableOn ℂ (fun x => C ⟨(i : Fin (kosRank r 0)).val, i.isLt⟩ j x) V :=
    fun i j x hx => ((hVsub x hx).2.2.1 _ j).differentiableWithinAt
  have hXV : ∀ l j, DifferentiableOn ℂ (xMat C'' l j) V := by
    intro l j x hx
    rcases h : eK r 1 l with l' | l'
    · rw [xMat_inl h]; exact differentiableWithinAt_const _
    · rw [xMat_inr h]; exact ((hVsub x hx).2.2.2.1 l' j).differentiableWithinAt
  have hYV : ∀ j l, DifferentiableOn ℂ (yMat C'' W j l) V := by
    intro j l x hx
    rcases h : eK r 1 l with l' | l'
    · rw [yMat_inl h]
      exact (differentiableWithinAt_const _).sub (DifferentiableWithinAt.fun_sum fun m _ =>
        ((hVsub x hx).2.2.2.2.1 j m).differentiableWithinAt.mul
          ((hVsub x hx).2.2.2.1 m l').differentiableWithinAt)
    · rw [yMat_inr h]; exact ((hVsub x hx).2.2.2.2.1 j l').differentiableWithinAt
  have hZV : ∀ k j, DifferentiableOn ℂ (fun x => Zc j k x) V :=
    fun k j x hx => ((hVsub x hx).2.2.2.2.2.1 j k).differentiableWithinAt
  -- the presentation change on `P × ℂ`
  have hVs : IsOpen (Prod.swap ⁻¹' V : Set (P × ℂ)) := hVo.preimage continuous_swap
  have hd : ∀ k i j, DifferentiableOn ℂ (swapMat (kosFin e he k) i j) (Prod.swap ⁻¹' V) :=
    fun k i j => (differentiableOn_swapMat (kosFin_hol e he k) i j).mono (preimage_mono hVU)
  have hexs : ∀ k, ExactStartOn (Prod.swap ⁻¹' V) (swapMat (kosFin e he (k + 1)))
      (swapMat (kosFin e he k)) :=
    fun k => HironakaG10FlatPrivilegedFlatStep.exactStartOn_swap ((hKos k).mono hVU)
  obtain ⟨δ, hδ, hδ0, hδex, hsplit⟩ := exists_presentationChange (b := r 1) hVs hd hexs
    (A := swapMat fun i j x => C ⟨(i : Fin (kosRank r 0)).val, i.isLt⟩ j x)
    (differentiableOn_swapMat hA'V) (differentiableOn_swapMat hXV) (differentiableOn_swapMat hYV)
    (Zm := swapMat fun k j x => Zc j k x) (differentiableOn_swapMat hZV)
    (fun q hq i j => kos_h0 e he C C'' (q.2, q.1) (hVsub _ hq).2.1.1 i j)
    (fun q hq i j => kos_h1 e he C C'' W (q.2, q.1) (hVsub _ hq).2.1.1 (hVsub _ hq).2.1.2 i j)
    (fun q hq i j => by
      refine Eq.trans ?_ ((hVsub _ hq).2.2.2.2.2.2 i j).symm
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _)
  have hres : FiniteResolutionOn (Prod.swap ⁻¹' V) (m + 4) δ :=
    ⟨by omega, kosRank_eq_zero htail (k := m + 1 + 4) (by omega), hδ, fun k _ => hδex k⟩
  obtain ⟨s', δ', hδ', hδ'0, hpriv⟩ := exists_rankSeq_resolution (a := r 0) (b := r 1)
    (r' := pcR (kosRank r) (r 1)) rfl rfl hres (A := swapMat C) (fun i j => by rw [hδ0]; rfl)
  refine ⟨Prod.swap ⁻¹' V, m + 4, s', δ', hδ', hVs, hy₀V, hδ'0, ?_⟩
  intro K' _ hK'U₀ hK'reg ⟨t, ht⟩ ρ hρ hKV _
  obtain ⟨t1, ht1⟩ := splitBy_kosFin hK'reg hρ hK'U₀ he (hKV.trans (preimage_mono hVU)) htail ht
    (m + 4)
  obtain ⟨t2, ht2⟩ := hsplit (K' ×ˢ closedBall (0 : ℂ) ρ) hKV (m + 4) ⟨t1, ht1⟩
  exact hpriv _ hKV ((privilegedOn_iff_exists_splitBy hres _ hKV).2 ⟨t2, ht2⟩)

end Torsion

end
end Hironaka.HironakaG10FlatTorsionStep
