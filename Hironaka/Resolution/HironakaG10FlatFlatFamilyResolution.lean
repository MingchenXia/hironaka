import Hironaka.Resolution.HironakaG10FlatFlatFamilyPrivilege

/-! # Douady's Proposition 6 (a) for finite resolutions

Douady 1966, §7 n° 3, Prop. 6 (a), all degrees: a holomorphic family `w ↦ D_k(w)` of complexes of
Banach spaces `0 → E_m → ⋯ → E_0` (`D_k(w) : E_{k+1} → E_k`, `D_m = 0`) which at `w = 0` is exact in
degrees `1, …, m` and direct has, near `0`, holomorphic generalized inverses in every degree and stays
exact (`exists_chain_generalizedInverse`, descending induction with
`HironakaG10FlatComplexPersistence.eventually_step_holomorphic`).

For a finite chain of holomorphic matrices `d_k(w, z)` (`d_k d_{k+1} = 0`, `d_m = 0`) whose
`B(K')`-complex at `w = 0` is exact in degrees `1, …, m` and direct, every consecutive pair of
restrictions to `K' × D̄(0,ρ)` is a `DirectExact` start for all small `ρ > 0`
(**`eventually_directExact_chain`**): `K' × D̄(0,ρ)` is privileged for the resolved sheaf.
BP: hironaka-g10-flat-flat-family-resolution.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatFlatFamilyResolution
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatGeneralizedInverse
  HironakaG10FlatComplexPersistence HironakaG10FlatFlatFamilyPrivilege HironakaG10FlatPolydiscParametric

/-! ## Abstract chains -/

section Abstract
variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)]

/-- **Holomorphic generalized inverses in every degree** of a finite holomorphic family of
complexes which is exact and direct at `0`. -/
theorem exists_chain_generalizedInverse {m : ℕ} (D : (k : ℕ) → ℂ → E (k + 1) →L[ℂ] E k)
    (htop : ∀ w, D m w = 0) (hhol : ∀ k ≤ m, ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ (D k) w)
    (hcomp : ∀ k < m, ∀ᶠ w in 𝓝 (0 : ℂ), ∀ u, D k w (D (k + 1) w u) = 0)
    (hex : ∀ k < m, ∀ x, D k 0 x = 0 → ∃ u, D (k + 1) 0 u = x)
    (hdir : ∀ k < m, ∃ S : E k →L[ℂ] E (k + 1), ∀ x, D k 0 (S (D k 0 x)) = D k 0 x) :
    ∀ k ≤ m, ∃ R : ℂ → E k →L[ℂ] E (k + 1), (∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ R w) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), ∀ x, D k w (R w (D k w x)) = D k w x) ∧
      (k < m → ∀ᶠ w in 𝓝 (0 : ℂ), ∀ x, D k w x = 0 → ∃ u, D (k + 1) w u = x) := by
  intro k hk
  refine Nat.decreasingInduction (n := m) (motive := fun k _ => ∃ R : ℂ → E k →L[ℂ] E (k + 1),
      (∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ R w) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), ∀ x, D k w (R w (D k w x)) = D k w x) ∧
      (k < m → ∀ᶠ w in 𝓝 (0 : ℂ), ∀ x, D k w x = 0 → ∃ u, D (k + 1) w u = x))
    (fun k hkm ih => ?_) ?_ hk
  · obtain ⟨R₂, hR₂d, hR₂, -⟩ := ih
    obtain ⟨S₀, hS₀⟩ := hdir k hkm
    have h := eventually_step_holomorphic (d₂ := D (k + 1)) (d₁ := D k) (hhol k hkm.le)
      (hhol (k + 1) hkm) hR₂d hR₂ (hcomp k hkm) (hex k hkm) hS₀
    exact ⟨stepInvFam (D (k + 1)) R₂ (D k) 0 S₀, h.mono fun w hw => hw.1,
      h.mono fun w hw => hw.2.2, fun _ => h.mono fun w hw => hw.2.1⟩
  · refine ⟨fun _ => 0, Eventually.of_forall fun _ => differentiableAt_const _,
      Eventually.of_forall fun w x => ?_, fun h => absurd h (lt_irrefl _)⟩
    rw [htop w]
    rfl

end Abstract

/-! ## Finite resolutions over `K' × D̄(0,ρ)` -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} [CompactSpace K']

/-- **Douady 1966, §7 Prop. 6 (a), for a finite resolution.** Let `d_k : L_{k+1} → L_k`
(`k = 0, …, m`, ranks `r k`) be holomorphic matrices on an open `O ⊆ ℂ × P` containing `{w} × K'` for
`w` near `0`, with `d_k d_{k+1} = 0` and `d_m = 0` on `O`. If the `B(K')`-complex of the slices at
`w = 0` is exact at `L_{k+1}` and `D_k(0)` is direct for every `k < m`, then there is `ρ₀ > 0` such
that for every `0 < ρ < ρ₀` and every `k < m` the restrictions of `(d_{k+1}, d_k)` to
`K' × D̄(0,ρ)` form a `DirectExact` start over `B(K' × D̄(0,ρ))`. -/
theorem eventually_directExact_chain (hK' : K' ⊆ closure (interior K')) {O : Set (ℂ × P)}
    (hOo : IsOpen O) (hO : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ z ∈ K', (w, z) ∈ O) {m : ℕ} {r : ℕ → ℕ}
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ}
    (hd : ∀ k i j, DifferentiableOn ℂ (d k i j) O)
    (hcomp : ∀ k < m, ∀ i l, ∀ q ∈ O, ∑ j, d k i j q * d (k + 1) j l q = 0)
    (htop : ∀ i j, ∀ q ∈ O, d m i j q = 0)
    (hex₀ : ∀ k < m, ∀ x, fibreOp K' (hd k) 0 x = 0 → ∃ u, fibreOp K' (hd (k + 1)) 0 u = x)
    (hker₀ : ∀ k < m, (LinearMap.ker (fibreOp K' (hd k) 0 : (Fin (r (k + 1)) → holSubalgebra K') →ₗ[ℂ]
      (Fin (r k) → holSubalgebra K'))).ClosedComplemented)
    (hran₀ : ∀ k < m, (LinearMap.range (fibreOp K' (hd k) 0 :
      (Fin (r (k + 1)) → holSubalgebra K') →ₗ[ℂ] (Fin (r k) → holSubalgebra K'))).ClosedComplemented) :
    ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → ∃ hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' O,
      ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)], ∀ k < m,
        DirectExact (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (swapMat (d (k + 1)))
            (differentiableOn_swapMat (hd (k + 1))))
          (restrictMatrix (K' ×ˢ closedBall (0 : ℂ) ρ) hKO (swapMat (d k))
            (differentiableOn_swapMat (hd k))) := by
  -- the fibre operators
  have hDtop : ∀ w, fibreOp K' (hd m) w = 0 := by
    intro w
    apply ContinuousLinearMap.ext
    intro x
    funext i
    show matrixOperator (fun i j => restrictParam K' (hd m i j) w) x i =
      (0 : Fin (r m) → holSubalgebra K') i
    rw [matrixOperator_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : restrictParam K' (hd m i j) w = 0 := by
      unfold restrictParam
      split_ifs with hw
      · apply Subtype.ext; apply ContinuousMap.ext; intro z
        exact htop i j (w, z) (hw z z.2)
      · rfl
    rw [h0, zero_mul]
  have hhol : ∀ k ≤ m, ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fibreOp K' (hd k)) w := by
    intro k _
    filter_upwards [eventually_eventually_nhds.2 hO] with w hw
    exact differentiableAt_matrixOperator_restrictParam K' hOo (hd k) hw.self_of_nhds
  have hcompD : ∀ k < m, ∀ᶠ w in 𝓝 (0 : ℂ),
      ∀ u, fibreOp K' (hd k) w (fibreOp K' (hd (k + 1)) w u) = 0 := by
    intro k hk
    filter_upwards [hO] with w hw u
    exact matrixOperator_comp_apply (fun j l => restrictParam K' (hd (k + 1) j l) w)
      (fun i j => restrictParam K' (hd k i j) w)
      (restrictParam_comp (hd (k + 1)) (hd k) (hcomp k hk) hw) u
  have hdir : ∀ k < m, ∃ S : (Fin (r k) → holSubalgebra K') →L[ℂ] (Fin (r (k + 1)) → holSubalgebra K'),
      ∀ x, fibreOp K' (hd k) 0 (S (fibreOp K' (hd k) 0 x)) = fibreOp K' (hd k) 0 x :=
    fun k hk => exists_generalizedInverse _ (hker₀ k hk) (hran₀ k hk)
  have hchain := exists_chain_generalizedInverse (E := fun k => Fin (r k) → holSubalgebra K')
    (fun k => fibreOp K' (hd k)) hDtop hhol hcompD hex₀ hdir
  choose R hR using hchain
  -- one ball for all degrees
  have hall : ∀ᶠ w in 𝓝 (0 : ℂ), (∀ z ∈ K', (w, z) ∈ O) ∧ ∀ k ∈ Finset.range (m + 1),
      ∀ hk : k ≤ m, DifferentiableAt ℂ (R k hk) w ∧
        (∀ x, fibreOp K' (hd k) w (R k hk w (fibreOp K' (hd k) w x)) = fibreOp K' (hd k) w x) ∧
        (k < m → ∀ x, fibreOp K' (hd k) w x = 0 → ∃ u, fibreOp K' (hd (k + 1)) w u = x) := by
    refine hO.and ((Finset.eventually_all _).2 fun k hk => ?_)
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    obtain ⟨h1, h2, h3⟩ := hR k hkm
    by_cases hlt : k < m
    · filter_upwards [h1, h2, h3 hlt] with w hw1 hw2 hw3 hk'
      exact ⟨hw1, hw2, fun _ => hw3⟩
    · filter_upwards [h1, h2] with w hw1 hw2 hk'
      exact ⟨hw1, hw2, fun h => absurd h hlt⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hwO : ∀ w ∈ closedBall (0 : ℂ) ρ, ∀ z ∈ K', (w, z) ∈ O := fun w hw =>
    (hball w (closedBall_subset_ball hρρ₀ hw)).1
  have hKO : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Prod.swap ⁻¹' O := fun q hq =>
    hwO q.2 (Set.mem_prod.mp hq).2 q.1 (Set.mem_prod.mp hq).1
  refine ⟨hKO, fun {_} k hk => ?_⟩
  have hk1 : k + 1 ≤ m := hk
  have hdeg : ∀ j (hj : j ≤ m), ∀ w ∈ closedBall (0 : ℂ) ρ, DifferentiableAt ℂ (R j hj) w ∧
      (∀ x, fibreOp K' (hd j) w (R j hj w (fibreOp K' (hd j) w x)) = fibreOp K' (hd j) w x) ∧
      (j < m → ∀ x, fibreOp K' (hd j) w x = 0 → ∃ u, fibreOp K' (hd (j + 1)) w u = x) :=
    fun j hj w hw => (hball w (closedBall_subset_ball hρρ₀ hw)).2 j
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj
  have hdiff : ∀ j (hj : j ≤ m), DifferentiableOn ℂ (R j hj) (ball 0 ρ₀) := fun j hj w hw =>
    ((hball w hw).2 j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj).1.differentiableWithinAt
  refine directExact_of_slices hK' hρ hρρ₀ (restrictMatrix_comp _ _ _ _ fun i l q hq =>
      hcomp k hk i l (q.2, q.1) hq) (hdiff (k + 1) hk1) (hdiff k hk.le) (fun w hw x => ?_)
      (fun w hw x => ?_) (fun w hw x hx => ?_)
  · rw [sliceMat_restrictMatrix hρ (hd (k + 1)) hKO hw (hwO w hw)]
    exact (hdeg (k + 1) hk1 w hw).2.1 x
  · rw [sliceMat_restrictMatrix hρ (hd k) hKO hw (hwO w hw)]
    exact (hdeg k hk.le w hw).2.1 x
  · rw [sliceMat_restrictMatrix hρ (hd k) hKO hw (hwO w hw)] at hx
    rw [sliceMat_restrictMatrix hρ (hd (k + 1)) hKO hw (hwO w hw)]
    exact (hdeg k hk.le w hw).2.2 hk x hx

end
end Hironaka.HironakaG10FlatFlatFamilyResolution
