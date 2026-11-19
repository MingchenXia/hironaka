import Hironaka.Resolution.HironakaG10FlatSplitComplex

/-! # Reindexing finite free resolutions

Exactness and privilege do not depend on how the bases of the free modules are labelled: for
bijections `σ k : Fin (r' k) ≃ Fin (r k)` the relabelled chain `d' k i j = d k (σ k i) (σ (k+1) j)`
is a finite free resolution (`finiteResolutionOn_reindex`) privileged on the same compacts
(`privilegedOn_reindex`, by domination with `h = 0`). This converts resolutions built with
structured index types (sums, shifted ranks) into the `Fin`-ranked form of
`HironakaG10FlatPrivilegedNbhd.HasPrivilegedNbhds`.

* `exactStartOn_reindex`: an exact start relabelled in all three degrees.
* `finiteResolutionOn_reindex`, `privilegedOn_reindex`; `splitBy_reindex` (the abstract Banach form).
BP: hironaka-g10-flat-reindex.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatReindex
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex

section Germ
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ι₂ ι₁ ι₀ κ₂ κ₁ κ₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀] [Fintype κ₂] [Fintype κ₁]
  [Fintype κ₀]

/-- **An exact start relabelled in all three degrees is an exact start.** -/
theorem exactStartOn_reindex {U : Set X} {G : ι₁ → ι₂ → X → ℂ} {F : ι₀ → ι₁ → X → ℂ}
    (h : ExactStartOn U G F) (e₂ : κ₂ ≃ ι₂) (e₁ : κ₁ ≃ ι₁) (e₀ : κ₀ ≃ ι₀) :
    ExactStartOn U (fun j k => G (e₁ j) (e₂ k)) (fun i j => F (e₀ i) (e₁ j)) := by
  refine ⟨fun i j => h.holF _ _, fun j k => h.holG _ _, fun i k x hx => ?_, fun y hy a ha => ?_⟩
  · rw [Equiv.sum_comp e₁ (fun j => F (e₀ i) j x * G j (e₂ k) x)]
    exact h.comp _ _ x hx
  · -- `a ∘ e₁⁻¹` is a relation of `F`
    have ha' : IsRelationAt F y fun j => a (e₁.symm j) := by
      refine ⟨fun j => ha.1 _, fun i => ?_⟩
      filter_upwards [ha.2 (e₀.symm i)] with x hx
      rw [← hx, ← Equiv.sum_comp e₁]
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    obtain ⟨c, hc, hca⟩ := h.exact y hy _ ha'
    refine ⟨fun k => c (e₂ k), fun k => hc _, fun j => ?_⟩
    filter_upwards [hca (e₁ j)] with x hx
    simp only [Equiv.symm_apply_apply] at hx
    rw [hx]
    exact (Equiv.sum_comp e₂ (fun k => c k x * columns G k (e₁ j) x)).symm

end Germ

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {m : ℕ} {r r' : ℕ → ℕ}
  {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}

/-- The relabelled chain `d' k i j = d k (σ k i) (σ (k+1) j)`. -/
def reindexChain (d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ)
    (σ : (k : ℕ) → Fin (r' k) ≃ Fin (r k)) : (k : ℕ) → Fin (r' k) → Fin (r' (k + 1)) → X → ℂ :=
  fun k i j => d k (σ k i) (σ (k + 1) j)

/-- **A relabelled finite free resolution is a finite free resolution.** -/
theorem finiteResolutionOn_reindex (h : FiniteResolutionOn U m d)
    (σ : (k : ℕ) → Fin (r' k) ≃ Fin (r k)) : FiniteResolutionOn U m (reindexChain d σ) := by
  refine ⟨h.pos, ?_, fun k i j => h.hol _ _ _, fun k hk => ?_⟩
  · have := Fintype.card_congr (σ (m + 1))
    simpa [h.top] using this
  · exact exactStartOn_reindex (h.exact k hk) (σ (k + 2)) (σ (k + 1)) (σ k)

section Banach
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- Relabelling vectors along `σ : Fin n' ≃ Fin n`. -/
def relabel {n n' : ℕ} (σ : Fin n' ≃ Fin n) : (Fin n → R) →L[ℂ] (Fin n' → R) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)

theorem relabel_apply {n n' : ℕ} (σ : Fin n' ≃ Fin n) (v : Fin n → R) (i : Fin n') :
    relabel σ v i = v (σ i) := rfl

/-- **Splittings transport along relabellings** (domination by an isomorphic complex). -/
theorem splitBy_reindex {M : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R}
    (σ : (k : ℕ) → Fin (r' k) ≃ Fin (r k))
    {t : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r (k + 1)) → R)} (ht : SplitBy (chainOp M) t m) :
    ∃ t' : (k : ℕ) → (Fin (r' k) → R) →L[ℂ] (Fin (r' (k + 1)) → R),
      SplitBy (chainOp fun k i j => M k (σ k i) (σ (k + 1) j)) t' m := by
  refine ⟨_, ht.of_dominated' (fun k => relabel (σ k)) (fun k => relabel (σ k).symm) (fun _ => 0)
    (fun k x => ?_) (fun k y => ?_) (fun k _ y => ?_)⟩
  · funext i
    simp only [chainOp, matrixOperator_apply, relabel_apply]
    exact Equiv.sum_comp (σ (k + 1)) (fun j => M k (σ k i) j * x j)
  · funext i
    simp only [chainOp, matrixOperator_apply, relabel_apply, Equiv.apply_symm_apply]
    exact (Equiv.sum_comp (σ (k + 1)) (fun j => M k i j * y ((σ (k + 1)).symm j))).symm.trans
      (Finset.sum_congr rfl fun j _ => by rw [Equiv.symm_apply_apply])
  · funext i
    simp [relabel_apply]

end Banach

/-- **Privilege transports along relabellings.** -/
theorem privilegedOn_reindex (h : FiniteResolutionOn U m d) (σ : (k : ℕ) → Fin (r' k) ≃ Fin (r k))
    (K : Set X) [CompactSpace K] (hKU : K ⊆ U) (hpriv : PrivilegedOn K hKU m d h.hol) :
    PrivilegedOn K hKU m (reindexChain d σ) (finiteResolutionOn_reindex h σ).hol := by
  obtain ⟨t, ht⟩ := (privilegedOn_iff_exists_splitBy h K hKU).mp hpriv
  rw [privilegedOn_iff_exists_splitBy (finiteResolutionOn_reindex h σ) K hKU]
  have hM : (fun k => restrictMatrix K hKU (reindexChain d σ k)
      ((finiteResolutionOn_reindex h σ).hol k)) =
      fun k i j => restrictMatrix K hKU (d k) (h.hol k) (σ k i) (σ (k + 1) j) := rfl
  rw [hM]
  exact splitBy_reindex σ ht

end
end Hironaka.HironakaG10FlatReindex
