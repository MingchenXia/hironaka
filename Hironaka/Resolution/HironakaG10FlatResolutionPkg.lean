import Hironaka.Resolution.HironakaG10FlatZeroTail

/-! # Packaging finite free resolutions: all degrees, structured bases, `rankSeq` form

Bookkeeping between the constructions of Douady's §7 Th. 1 (Koszul chains with bases `E_k ⊕ E_{k-1}`,
presentation changes with ranks `pcR`, …) and the `Fin`/`rankSeq`-ranked form of
`HironakaG10FlatPrivilegedNbhd.HasPrivilegedNbhds`.

* `exactStartOn_of_isEmpty`: a start whose middle module is `0` is exact.
* `FiniteResolutionOn.exactStartOn_all`: a finite free resolution of length `m` with ranks `0` beyond
  `m` is an exact start on `U` in EVERY degree; `splitBy_all`: a splitting in degrees `< m` of a chain
  with ranks `0` beyond `m` is a splitting in all degrees.
* `splitBy_relabel`: splittings of chains with structured bases `C k` transport to `Fin`-ranked
  chains along bijections `Fin (r' k) ≃ C k`.
* **`exists_rankSeq_resolution`**: a finite free resolution with ranks `r'`, `r' 0 = a`, `r' 1 = b`,
  first matrix `A` up to the casts, is relabelled to ranks `rankSeq a b s'` with first matrix exactly
  `A`, on the same open set and with the same privileged compacts (`pkgEquiv`).
BP: hironaka-g10-flat-resolution-pkg.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatResolutionPkg
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatReindex

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}

/-- A start whose middle module is `0` is exact. -/
theorem exactStartOn_of_isEmpty {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
    [IsEmpty ι₁] {G : ι₁ → ι₂ → X → ℂ} {F : ι₀ → ι₁ → X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) (hG : ∀ j k, DifferentiableOn ℂ (G j k) U) :
    ExactStartOn U G F :=
  ⟨hF, hG, fun _ _ _ _ => Finset.sum_of_isEmpty _, fun y _ _ _ =>
    ⟨fun _ => fun _ => 0, fun _ => holAt_const 0 y, fun j => isEmptyElim j⟩⟩

variable {m : ℕ} {r : ℕ → ℕ} {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}

/-- **A finite free resolution with zero tail is exact in every degree.** -/
theorem exactStartOn_all (h : FiniteResolutionOn U m d) (htail : ∀ k, m < k → r k = 0) :
    ∀ k, ExactStartOn U (d (k + 1)) (d k) := by
  intro k
  by_cases hk : k < m
  · exact h.exact k hk
  · have h0 : r (k + 1) = 0 := htail (k + 1) (by omega)
    have : IsEmpty (Fin (r (k + 1))) := by rw [h0]; exact Fin.isEmpty'
    exact exactStartOn_of_isEmpty (h.hol k) (h.hol (k + 1))

/-- **A splitting of a chain with zero tail is a splitting in every degree.** -/
theorem splitBy_all {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    {M : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R}
    {t : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r (k + 1)) → R)} (ht : SplitBy (chainOp M) t m)
    (htail : ∀ k, m < k → r k = 0) (M' : ℕ) : SplitBy (chainOp M) t M' := by
  intro k _ x
  by_cases hk : k < m
  · exact ht k hk x
  · have h0 : r (k + 1) = 0 := htail (k + 1) (by omega)
    have hx : ∀ y : Fin (r (k + 1)) → R, y = 0 := fun y => funext fun j => (Fin.cast h0 j).elim0
    rw [hx x, map_zero, map_zero, map_zero, map_zero, add_zero]

/-! ## Relabelling structured bases -/

section Relabel
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- Relabelling vectors along `σ : ι' ≃ ι`. -/
def relabelG {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι' ≃ ι) : (ι → R) →L[ℂ] (ι' → R) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)

theorem relabelG_apply {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι' ≃ ι) (v : ι → R) (i : ι') :
    relabelG σ v i = v (σ i) := rfl

/-- **Splittings transport from structured bases to `Fin` bases.** -/
theorem splitBy_relabel {C : ℕ → Type*} [∀ k, Fintype (C k)] {M : (k : ℕ) → C k → C (k + 1) → R}
    {r' : ℕ → ℕ} (σ : (k : ℕ) → Fin (r' k) ≃ C k)
    {t : (k : ℕ) → (C k → R) →L[ℂ] (C (k + 1) → R)} {m : ℕ}
    (ht : SplitBy (fun k => matrixOperator (M k)) t m) :
    ∃ t' : (k : ℕ) → (Fin (r' k) → R) →L[ℂ] (Fin (r' (k + 1)) → R),
      SplitBy (chainOp fun k i j => M k (σ k i) (σ (k + 1) j)) t' m := by
  refine ⟨_, ht.of_dominated' (fun k => relabelG (σ k)) (fun k => relabelG (σ k).symm) (fun _ => 0)
    (fun k x => ?_) (fun k y => ?_) (fun k _ y => ?_)⟩
  · funext i
    simp only [chainOp, matrixOperator_apply, relabelG_apply]
    exact Equiv.sum_comp (σ (k + 1)) (fun j => M k (σ k i) j * x j)
  · funext i
    simp only [chainOp, matrixOperator_apply, relabelG_apply, Equiv.apply_symm_apply]
    exact (Equiv.sum_comp (σ (k + 1)) (fun j => M k i j * y ((σ (k + 1)).symm j))).symm.trans
      (Finset.sum_congr rfl fun j _ => by rw [Equiv.symm_apply_apply])
  · funext i
    simp [relabelG_apply]

end Relabel

/-! ## The `rankSeq` form -/

/-- The relabelling `Fin (rankSeq a b s' k) ≃ Fin (r' k)` (`s' k = r' (k+2)`). -/
def pkgEquiv {r' : ℕ → ℕ} {a b : ℕ} (h0 : r' 0 = a) (h1 : r' 1 = b) :
    (k : ℕ) → Fin (rankSeq a b (fun k => r' (k + 2)) k) ≃ Fin (r' k)
  | 0 => finCongr h0.symm
  | 1 => finCongr h1.symm
  | _ + 2 => Equiv.refl _

/-- **The `rankSeq` form of a finite free resolution**: a finite free resolution `δ` with ranks
`r'` (`r' 0 = a`, `r' 1 = b`) whose first matrix is `A` up to the casts becomes, after relabelling, a
finite free resolution with ranks `rankSeq a b s'` and first matrix exactly `A`, privileged on the
same compacts. -/
theorem exists_rankSeq_resolution {r' : ℕ → ℕ} {a b : ℕ} (h0 : r' 0 = a) (h1 : r' 1 = b)
    {δ : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ} (hδ : FiniteResolutionOn U m δ)
    {A : Fin a → Fin b → X → ℂ}
    (hA : ∀ i j, δ 0 (Fin.cast h0.symm i) (Fin.cast h1.symm j) = A i j) :
    ∃ (s' : ℕ → ℕ) (d : (k : ℕ) → Fin (rankSeq a b s' k) → Fin (rankSeq a b s' (k + 1)) → X → ℂ)
      (hd : FiniteResolutionOn U m d), d 0 = A ∧
      ∀ (K : Set X) [CompactSpace K] (hKU : K ⊆ U), PrivilegedOn K hKU m δ hδ.hol →
        PrivilegedOn K hKU m d hd.hol :=
  ⟨fun k => r' (k + 2), reindexChain δ (pkgEquiv h0 h1), finiteResolutionOn_reindex hδ _,
    funext fun i => funext fun j => hA i j,
    fun K _ hKU hp => privilegedOn_reindex hδ (pkgEquiv h0 h1) K hKU hp⟩

end
end Hironaka.HironakaG10FlatResolutionPkg
