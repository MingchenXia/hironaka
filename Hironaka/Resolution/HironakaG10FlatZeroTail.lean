import Hironaka.Resolution.HironakaG10FlatReindex

/-! # Finite free resolutions with zero tail

A `FiniteResolutionOn U m d` only asks `r (m+1) = 0`; the ranks `r k`, `k > m + 1`, and the matrices
`d k`, `k > m`, are arbitrary. Constructions that change the length (presentation changes, cones)
need the tail to vanish. `zeroTail` replaces the ranks by `rankZ r m k = r k` (`k ≤ m`), `0` (`k > m`)
and the matrices by `d k` relabelled along `Fin.cast` (`k ≤ m`), `0` beyond:
`finiteResolutionOn_zeroTail`, `privilegedOn_zeroTail` (same open set, same privileged compacts),
`zeroTail_apply` (`d k`, `k ≤ m`, unchanged up to the casts), `rankZ_eq_zero` (the tail vanishes).

Banach part: `SplitBy.of_dominated_le` (domination with chain-map identities only in the degrees that
are used) and `splitBy_of_relabel_le` (a chain that agrees with a split chain up to relabelling in
degrees `≤ m` is split in degrees `1..m`).
BP: hironaka-g10-flat-zero-tail.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatZeroTail
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatReindex

section Abstract
variable {E F : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℂ (E k)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℂ (F k)]
  {D : (k : ℕ) → E (k + 1) →L[ℂ] E k} {t : (k : ℕ) → E k →L[ℂ] E (k + 1)} {m : ℕ}

/-- **Domination, with the identities only in the degrees used** (`hf` in degrees `≤ m`, the
others in degrees `< m`). -/
theorem SplitBy.of_dominated_le {D' : (k : ℕ) → F (k + 1) →L[ℂ] F k}
    (f : (k : ℕ) → E k →L[ℂ] F k) (g : (k : ℕ) → F k →L[ℂ] E k) (h : (k : ℕ) → F k →L[ℂ] F (k + 1))
    (hf : ∀ k ≤ m, ∀ x, D' k (f (k + 1) x) = f k (D k x))
    (hg : ∀ k < m, ∀ y, D k (g (k + 1) y) = g k (D' k y))
    (hh : ∀ k < m, ∀ y, y - f (k + 1) (g (k + 1) y) = D' (k + 1) (h (k + 1) y) + h k (D' k y))
    (hs : SplitBy D t m) :
    SplitBy D' (fun k => (f (k + 1)).comp ((t k).comp (g k)) + h k) m := by
  intro k hk y
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.comp_apply, map_add]
  rw [hf (k + 1) hk, ← hg k hk]
  have e1 := congrArg (f (k + 1)) (hs k hk (g (k + 1) y))
  rw [map_add] at e1
  have e2 := hh k hk y
  have e3 : f (k + 1) (D (k + 1) (t (k + 1) (g (k + 1) y))) + D' (k + 1) (h (k + 1) y) +
      (f (k + 1) (t k (D k (g (k + 1) y))) + h k (D' k y)) =
      (f (k + 1) (D (k + 1) (t (k + 1) (g (k + 1) y))) + f (k + 1) (t k (D k (g (k + 1) y)))) +
        (D' (k + 1) (h (k + 1) y) + h k (D' k y)) := by abel
  rw [e3, e1, ← e2]
  abel

end Abstract

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] {r r' : ℕ → ℕ} {m : ℕ}

/-- **A chain agreeing with a split chain up to relabelling in degrees `≤ m` is split.** -/
theorem splitBy_of_relabel_le {M : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R}
    {M' : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → R}
    (σ : (k : ℕ) → k ≤ m + 1 → (Fin (r' k) ≃ Fin (r k)))
    (hM : ∀ k (hk : k ≤ m) i j, M' k i j = M k (σ k (by omega) i) (σ (k + 1) (by omega) j))
    {t : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r (k + 1)) → R)} (ht : SplitBy (chainOp M) t m) :
    ∃ t' : (k : ℕ) → (Fin (r' k) → R) →L[ℂ] (Fin (r' (k + 1)) → R), SplitBy (chainOp M') t' m := by
  classical
  let f : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r' k) → R) := fun k =>
    if hk : k ≤ m + 1 then relabel (σ k hk) else 0
  let g : (k : ℕ) → (Fin (r' k) → R) →L[ℂ] (Fin (r k) → R) := fun k =>
    if hk : k ≤ m + 1 then relabel (σ k hk).symm else 0
  have hfk : ∀ k (hk : k ≤ m + 1), f k = relabel (σ k hk) := fun k hk => dif_pos hk
  have hgk : ∀ k (hk : k ≤ m + 1), g k = relabel (σ k hk).symm := fun k hk => dif_pos hk
  refine ⟨_, SplitBy.of_dominated_le f g (fun _ => 0) (fun k hk x => ?_) (fun k hk y => ?_)
    (fun k hk y => ?_) ht⟩
  · rw [hfk (k + 1) (by omega), hfk k (by omega)]
    funext i
    simp only [chainOp, matrixOperator_apply, relabel_apply, hM k hk]
    exact Equiv.sum_comp (σ (k + 1) (by omega)) (fun j => M k (σ k (by omega) i) j * x j)
  · rw [hgk (k + 1) (by omega), hgk k (by omega)]
    funext i
    simp only [chainOp, matrixOperator_apply, relabel_apply, hM k hk.le, Equiv.apply_symm_apply]
    exact (Equiv.sum_comp (σ (k + 1) (by omega))
      (fun j => M k i j * y ((σ (k + 1) (by omega)).symm j))).symm.trans
      (Finset.sum_congr rfl fun j _ => by rw [Equiv.symm_apply_apply])
  · rw [hfk (k + 1) (by omega), hgk (k + 1) (by omega)]
    funext i
    simp [relabel_apply]

end Matrix

/-! ## Zero tails -/

/-- The ranks `r k` for `k ≤ m`, `0` beyond. -/
def rankZ (r : ℕ → ℕ) (m k : ℕ) : ℕ := if k ≤ m then r k else 0

variable {r : ℕ → ℕ} {m : ℕ}

theorem rankZ_of_le {k : ℕ} (hk : k ≤ m) : rankZ r m k = r k := if_pos hk

theorem rankZ_eq_zero {k : ℕ} (hk : m < k) : rankZ r m k = 0 := if_neg (not_le.mpr hk)

theorem rankZ_eq (htop : r (m + 1) = 0) {k : ℕ} (hk : k ≤ m + 1) : rankZ r m k = r k := by
  by_cases h : k ≤ m
  · exact rankZ_of_le h
  · have : k = m + 1 := by omega
    subst this
    rw [rankZ_eq_zero (Nat.lt_succ_self m), htop]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}
  {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}

/-- **The chain with zero tail.** -/
def zeroTail (htop : r (m + 1) = 0) (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ) :
    (k : ℕ) → Fin (rankZ r m k) → Fin (rankZ r m (k + 1)) → X → ℂ :=
  fun k i j => if hk : k ≤ m then
    d k (finCongr (rankZ_eq htop (by omega)) i) (finCongr (rankZ_eq htop (by omega)) j) else 0

omit [NormedAddCommGroup X] [NormedSpace ℂ X] in
theorem zeroTail_apply (htop : r (m + 1) = 0) {k : ℕ} (hk : k ≤ m) (i : Fin (rankZ r m k))
    (j : Fin (rankZ r m (k + 1))) :
    zeroTail htop d k i j =
      d k (finCongr (rankZ_eq htop (by omega)) i) (finCongr (rankZ_eq htop (by omega)) j) := by
  unfold zeroTail
  rw [dif_pos hk]

/-- **The zero-tail chain of a finite free resolution is a finite free resolution** on the same set. -/
theorem finiteResolutionOn_zeroTail (h : FiniteResolutionOn U m d) :
    FiniteResolutionOn U m (zeroTail h.top d) := by
  refine ⟨h.pos, rankZ_eq_zero (Nat.lt_succ_self m), fun k i j => ?_, fun k hk => ?_⟩
  · by_cases hk : k ≤ m
    · have : zeroTail h.top d k i j = d k (finCongr (rankZ_eq h.top (by omega)) i)
          (finCongr (rankZ_eq h.top (by omega)) j) := zeroTail_apply h.top hk i j
      rw [this]
      exact h.hol _ _ _
    · have : zeroTail h.top d k i j = 0 := by unfold zeroTail; rw [dif_neg hk]
      rw [this]
      exact differentiableOn_const 0
  · have e1 : zeroTail h.top d (k + 1) = fun j l => d (k + 1)
        (finCongr (rankZ_eq h.top (by omega)) j) (finCongr (rankZ_eq h.top (by omega)) l) := by
      funext j l
      exact zeroTail_apply h.top (by omega) j l
    have e0 : zeroTail h.top d k = fun i j => d k
        (finCongr (rankZ_eq h.top (by omega)) i) (finCongr (rankZ_eq h.top (by omega)) j) := by
      funext i j
      exact zeroTail_apply h.top (by omega) i j
    rw [e1, e0]
    exact exactStartOn_reindex (h.exact k hk) _ _ _

/-- `restrict` of equal functions. -/
theorem restrict_congr (K : Set X) {V : Set X} (hKV : K ⊆ V) {F G : X → ℂ} (hFG : F = G)
    (hF : DifferentiableOn ℂ F V) (hG : DifferentiableOn ℂ G V) :
    restrict K hKV F hF = restrict K hKV G hG := by
  subst hFG
  rfl

/-- **Privilege passes to the zero-tail chain.** -/
theorem privilegedOn_zeroTail (h : FiniteResolutionOn U m d) (K : Set X) [CompactSpace K]
    (hKU : K ⊆ U) (hpriv : PrivilegedOn K hKU m d h.hol) :
    PrivilegedOn K hKU m (zeroTail h.top d) (finiteResolutionOn_zeroTail h).hol := by
  obtain ⟨t, ht⟩ := (privilegedOn_iff_exists_splitBy h K hKU).mp hpriv
  rw [privilegedOn_iff_exists_splitBy (finiteResolutionOn_zeroTail h) K hKU]
  exact splitBy_of_relabel_le (M := fun k => restrictMatrix K hKU (d k) (h.hol k))
    (fun k hk => finCongr (rankZ_eq h.top hk))
    (fun k hk i j => restrict_congr K hKU (F := zeroTail h.top d k i j)
      (G := d k (finCongr (rankZ_eq h.top (by omega)) i) (finCongr (rankZ_eq h.top (by omega)) j))
      (funext fun x => by rw [zeroTail_apply h.top hk]) _ _) ht

end
end Hironaka.HironakaG10FlatZeroTail
