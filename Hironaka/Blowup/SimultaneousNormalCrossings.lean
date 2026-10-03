/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Analytic.GeneratorMultiplicityOne
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPushforward
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Simultaneous normal crossings coordinates for a centre, a submanifold and a divisor

Sources: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Definitions 2.1--2.2 ("`E` is transverse to
`N`", "`C` and `E` have only normal crossings") and the remark after them; Wlodarczyk 2005
(`wlodarczyk05-hironaka`), §2.1.

Let `C ⊆ N` be subsets of a complex manifold `X` and `E = [H₁, …, H_s]` a simple normal crossings
divisor, transverse to `N`, with which `C` has only normal crossings.  Then at every point `x ∈ C`
there are holomorphic coordinates in which simultaneously `C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`
and every member of `E` through `x` is a coordinate hyperplane `{w_{s i} = 0}`, `s i < k_N`, the
`s i` distinct (`isAdaptedAt_of_hasNormalCrossings`; `IsAdaptedAt` is the hypothesis of
`BlowupSNCTransform`).

Proof.  Take coordinates `Θ` (normal crossings of `C` and `E`: `C = L_Y`, `H_i = {u_{t'_i} = 0}`)
and `Ψ` (transversality: `N = L_{S₀}`, `H_i = {v_{t_i} = 0}`, `t_i ∉ S₀`), and read
`Ξ = Ψ ∘ Θ⁻¹` in the `Θ`-coordinates `u`.  The differential `L` of `Ξ` at `0` is invertible;
the rows `L_s`, `s ∈ S₀`, vanish on `L_Y` (since `C ⊆ N`), and for the members `H_i ⊇ C`
(`t'_i ∈ Y`) the row `L_{t_i}` is a nonzero multiple of `du_{t'_i}`.  Hence the rows `L_s`,
`s ∈ S₀`, restricted to the coordinates `Y' = Y \ {t'_i : t'_i ∈ Y}`, are independent; choose
`X ⊆ Y'` with `|X| = |S₀|` on which they stay independent (`exists_linearIndependent'`), and
replace the coordinates `u_t`, `t ∈ X`, by the components `Ξ_s`, `s ∈ S₀`
(`exists_model_coords`).  The new map has invertible differential (inverse function theorem);
its zero set of the coordinates indexed by `Y` is exactly `L_Y` near `0`, because it is
injective near `0` and does not change when the coordinates `u_Y` are put to `0`.  A permutation
of the coordinates (`exists_perm_nested`) puts the `S₀`-block last and the `Y`-block just before
it.  The distinctness of the `s i` comes from the simple normal crossings of `E`: two members
agreeing near `x` are equal (`eq_of_eventually_mem_iff`).

The statement needs `0 < n`: in dimension `0` no function `Fin E.length → Fin 0` exists when `E`
is nonempty.  Every blowup centre with a point has `0 < n` (`pos_of_isBlowupAlong`), since the
centre of a blowup has empty interior.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SimultaneousNormalCrossings

open Hironaka.BlowupSequences NormalCrossings BlowupSNCTransform BlowupStrictSubmanifold RegularAtDimTransport RegularPatchPushforward

noncomputable section

variable {n : ℕ}

/-! ### Linear algebra in `ℂⁿ` -/

section Linear

/-- Selection of coordinates: `(selMap f p v) r = v (f r)` if `p r`, and `0` otherwise. -/
def selMap (f : Fin n → Fin n) (p : Fin n → Prop) [DecidablePred p] :
    ComplexModel n →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun r => if p r then v (f r) else 0)
      map_add' := by
        intro v w
        ext r
        by_cases h : p r <;> simp [h]
      map_smul' := by
        intro c v
        ext r
        by_cases h : p r <;> simp [h] }

theorem selMap_apply (f : Fin n → Fin n) (p : Fin n → Prop) [DecidablePred p]
    (v : ComplexModel n) (r : Fin n) : selMap f p v r = if p r then v (f r) else 0 := rfl

/-- The number of `r : Fin n` with `a ≤ r < b`, `b ≤ n`. -/
theorem card_filter_le_lt {a b : ℕ} (hb : b ≤ n) :
    (Finset.univ.filter fun r : Fin n => a ≤ r.1 ∧ r.1 < b).card = b - a := by
  have h : (Finset.univ.filter fun r : Fin n => a ≤ r.1 ∧ r.1 < b).map Fin.valEmbedding =
      Finset.Ico a b := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨r, h, rfl⟩
      exact h
    · rintro ⟨h1, h2⟩
      exact ⟨⟨m, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico]

/-- **A permutation of the coordinates putting a nested pair of index sets last**: for
`X ⊆ Y ⊆ Fin n`, `a + |X| = n` and `b + |Y| = n` there is `σ` with `a ≤ σ t ↔ t ∈ X` and
`b ≤ σ t ↔ t ∈ Y`. -/
theorem exists_perm_nested_aux {X Y : Finset (Fin n)} (hXY : X ⊆ Y) {a b : ℕ}
    (ha : a + X.card = n) (hb : b + Y.card = n) :
    ∃ σ : Fin n ≃ Fin n, ∀ t, (a ≤ (σ t).1 ↔ t ∈ X) ∧ (b ≤ (σ t).1 ↔ t ∈ Y) := by
  classical
  have hXc : X.card ≤ Y.card := Finset.card_le_card hXY
  have hba : b ≤ a := by omega
  set f : Fin n → ℕ := fun t => if t ∈ X then 2 else if t ∈ Y then 1 else 0 with hf
  set g : Fin n → ℕ := fun r => if a ≤ r.1 then 2 else if b ≤ r.1 then 1 else 0 with hg
  have hf2 : ∀ t, f t = 2 ↔ t ∈ X := by
    intro t
    by_cases htX : t ∈ X
    · simp [hf, htX]
    · by_cases htY : t ∈ Y <;> simp [hf, htX, htY]
  have hf1 : ∀ t, f t = 1 ↔ t ∈ Y ∧ t ∉ X := by
    intro t
    by_cases htX : t ∈ X
    · simp [hf, htX]
    · by_cases htY : t ∈ Y <;> simp [hf, htX, htY]
  have hf0 : ∀ t, f t = 0 ↔ t ∉ Y := by
    intro t
    by_cases htX : t ∈ X
    · simp [hf, htX, hXY htX]
    · by_cases htY : t ∈ Y <;> simp [hf, htX, htY]
  have hf3 : ∀ t, f t < 3 := by
    intro t
    simp only [hf]
    split_ifs <;> omega
  have hg2 : ∀ r : Fin n, g r = 2 ↔ a ≤ r.1 := by
    intro r
    by_cases h3 : a ≤ r.1
    · simp [hg, h3]
    · by_cases h4 : b ≤ r.1 <;> simp [hg, h3, h4]
  have hg1 : ∀ r : Fin n, g r = 1 ↔ b ≤ r.1 ∧ r.1 < a := by
    intro r
    by_cases h3 : a ≤ r.1
    · simp [hg, h3]
    · by_cases h4 : b ≤ r.1
      · simp [hg, h3, h4]
        omega
      · simp [hg, h3, h4]
  have hg0 : ∀ r : Fin n, g r = 0 ↔ r.1 < b := by
    intro r
    by_cases h3 : a ≤ r.1
    · simp [hg, h3]
      omega
    · by_cases h4 : b ≤ r.1
      · simp [hg, h3, h4]
      · simp [hg, h3, h4]
        omega
  have hg3 : ∀ r : Fin n, g r < 3 := by
    intro r
    simp only [hg]
    split_ifs <;> omega
  have hcard : ∀ c, Fintype.card {t // f t = c} = Fintype.card {r // g r = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases Nat.lt_or_ge c 3 with hc | hc
    · interval_cases c
      · have h1 : (Finset.univ.filter fun t => f t = 0) = Finset.univ \ Y := by
          ext t
          simp [hf0]
        have h2 : (Finset.univ.filter fun r => g r = 0) =
            Finset.univ.filter fun r : Fin n => 0 ≤ r.1 ∧ r.1 < b := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg0, zero_le]
        rw [h1, h2, card_filter_le_lt (by omega), Finset.card_sdiff_of_subset
          (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      · have h1 : (Finset.univ.filter fun t => f t = 1) = Y \ X := by
          ext t
          simp [hf1]
        have h2 : (Finset.univ.filter fun r => g r = 1) =
            Finset.univ.filter fun r : Fin n => b ≤ r.1 ∧ r.1 < a := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg1]
        rw [h1, h2, card_filter_le_lt (by omega), Finset.card_sdiff_of_subset hXY]
        omega
      · have h1 : (Finset.univ.filter fun t => f t = 2) = X := by
          ext t
          simp [hf2]
        have h2 : (Finset.univ.filter fun r => g r = 2) =
            Finset.univ.filter fun r : Fin n => a ≤ r.1 ∧ r.1 < n := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg2, r.2, and_true]
        rw [h1, h2, card_filter_le_lt le_rfl]
        omega
    · have h1 : (Finset.univ.filter fun t => f t = c) = ∅ := by
        ext t
        have := hf3 t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        omega
      have h2 : (Finset.univ.filter fun r => g r = c) = ∅ := by
        ext r
        have := hg3 r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        omega
      rw [h1, h2]
  set σ := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
  refine ⟨σ, fun t => ?_⟩
  have h : g (σ t) = f t := Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) t
  constructor
  · rw [← hg2, h, hf2]
  · have h0 := hg0 (σ t)
    have h0' := hf0 t
    rw [h] at h0
    constructor
    · intro h5
      by_contra h6
      have := h0.mp (h0'.mpr h6)
      omega
    · intro h5
      by_contra h6
      exact h0'.mp (h0.mpr (by omega)) h5

/-- **A permutation of the coordinates putting a nested pair of index sets last**: for
`X ⊆ Y ⊆ Fin n` there is `σ` with `σ t ≥ n - |X| ↔ t ∈ X` and `σ t ≥ n - |Y| ↔ t ∈ Y`. -/
theorem exists_perm_nested {X Y : Finset (Fin n)} (hXY : X ⊆ Y) :
    ∃ σ : Fin n ≃ Fin n, ∀ t, (n - X.card ≤ (σ t).1 ↔ t ∈ X) ∧ (n - Y.card ≤ (σ t).1 ↔ t ∈ Y) := by
  have hYn : Y.card ≤ n := by simpa using Finset.card_le_univ Y
  have hXn : X.card ≤ n := (Finset.card_le_card hXY).trans hYn
  exact exists_perm_nested_aux hXY (Nat.sub_add_cancel hXn) (Nat.sub_add_cancel hYn)

/-- **A derivative vanishes along a line on which a component vanishes.** -/
theorem apply_eq_zero_of_eventually_smul {f : ComplexModel n → ComplexModel n}
    {L : ComplexModel n →L[ℂ] ComplexModel n} (hf : HasFDerivAt f L 0) {v : ComplexModel n}
    {r : Fin n} (h : ∀ᶠ τ : ℂ in 𝓝 0, f (τ • v) r = 0) : L v r = 0 := by
  have h1 : HasDerivAt (fun τ : ℂ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hf' : HasFDerivAt f L ((0 : ℂ) • v) := by rwa [zero_smul]
  have h2 : HasDerivAt (fun τ : ℂ => f (τ • v)) (L v) 0 := hf'.comp_hasDerivAt (0 : ℂ) h1
  have h3 : HasDerivAt (fun τ : ℂ => f (τ • v) r) (L v r) 0 :=
    (EuclideanSpace.proj r : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
  have h4 : HasDerivAt (fun τ : ℂ => f (τ • v) r) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq h
  exact h3.unique h4

/-- Putting coordinates to `0` does not increase the norm. -/
theorem norm_zeroCoords_le (Y : Finset (Fin n)) (u : ComplexModel n) :
    ‖(WithLp.toLp 2 fun t => if t ∈ Y then 0 else u t : ComplexModel n)‖ ≤ ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun t _ => ?_)
  by_cases ht : t ∈ Y
  · simp [ht]
  · simp [ht]

/-- The decomposition `v = ∑_{t ∈ T} v_t e_t` of a vector supported on `T`. -/
theorem eq_sum_single_of_support {T : Finset (Fin n)} {v : ComplexModel n}
    (hv : ∀ t ∉ T, v t = 0) : v = ∑ t ∈ T, v t • EuclideanSpace.single t (1 : ℂ) := by
  ext r
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.ofLp_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]
  by_cases hr : r ∈ T
  · simp [hr]
  · simp [hr, hv r hr]

end Linear

/-! ### The model: replacing coordinates by components of a local biholomorphism -/

section Model

/-- **The model lemma.**  Let `Ξ` be a local biholomorphism at `0` of `ℂⁿ` (in the application,
`Ψ ∘ Θ⁻¹` read in normal crossings coordinates `Θ` of `C`), mapping `L_Y` into `L_{S₀}`
(`C ⊆ N`), and for `i ∈ A` let the component `Ξ_{q i}` vanish on `{u_{p i} = 0}`, with
`q i ∉ S₀` (members of `E` containing `C`, transverse to `N`).  Then there are
`X ⊆ Y` avoiding the `p i`, a permutation `σ` of the coordinates and a local biholomorphism `Φ`
at `0` such that, near `0`, `Φ` maps `L_Y` onto `ℂ^{n - |Y|} × 0`, `Ξ⁻¹(L_{S₀})` onto
`ℂ^{n - |S₀|} × 0`, the coordinates `u_t`, `t ∉ X`, to the coordinates `σ t`, and the `σ t` with
`t ∉ X` are exactly those below `n - |S₀|`. -/
theorem exists_model_coords {ι : Type*} (Ξ : LocalHolomorphicEquivAt (n := n) 0)
    (Y S₀ : Finset (Fin n)) (A : Set ι) (p q : ι → Fin n) (hqS : ∀ i ∈ A, q i ∉ S₀)
    (hvan : ∀ i ∈ A, ∀ u ∈ Ξ.source, u (p i) = 0 → Ξ.toFun u (q i) = 0)
    (hYS : ∀ u ∈ Ξ.source, u ∈ coordSubspace Y → Ξ.toFun u ∈ coordSubspace S₀) :
    ∃ (X : Finset (Fin n)) (σ : Fin n ≃ Fin n) (Φ : LocalHolomorphicEquivAt (n := n) 0),
      X ⊆ Y ∧ (∀ i ∈ A, p i ∉ X) ∧ Φ.source ⊆ Ξ.source ∧
      (∀ t, n - S₀.card ≤ (σ t).1 ↔ t ∈ X) ∧
      ∀ u ∈ Φ.source,
        (u ∈ coordSubspace Y ↔ Φ.toFun u ∈ complexCoordinatePlane n (n - Y.card)) ∧
        (Ξ.toFun u ∈ coordSubspace S₀ ↔
          Φ.toFun u ∈ complexCoordinatePlane n (n - S₀.card)) ∧
        ∀ t, t ∉ X → Φ.toFun u (σ t) = u t := by
  classical
  set L := fderiv ℂ Ξ.toFun 0 with hL
  have hΞd : HasFDerivAt Ξ.toFun L 0 :=
    (Ξ.toFun_holomorphic.differentiableAt
      (Ξ.isOpen_source.mem_nhds Ξ.center_mem_source)).hasFDerivAt
  have hLsurj : Function.Surjective L :=
    GeneratorMultiplicityOne.surjective_fderiv_toFun Ξ Ξ.center_mem_source
  -- small multiples of a vector stay in the source
  have hsmall : ∀ v : ComplexModel n, ∀ᶠ τ : ℂ in 𝓝 0, τ • v ∈ Ξ.source := by
    intro v
    have h : Tendsto (fun τ : ℂ => τ • v) (𝓝 0) (𝓝 ((0 : ℂ) • v)) :=
      (continuous_id.smul continuous_const : Continuous fun τ : ℂ => τ • v).tendsto 0
    rw [zero_smul] at h
    exact h.eventually (Ξ.isOpen_source.mem_nhds Ξ.center_mem_source)
  -- the rows of `L` indexed by `S₀` vanish on `L_Y`
  have hF1 : ∀ s ∈ S₀, ∀ v ∈ coordSubspace Y, L v s = 0 := by
    intro s hs v hv
    refine apply_eq_zero_of_eventually_smul hΞd ?_
    filter_upwards [hsmall v] with τ hτ
    refine hYS _ hτ (fun t ht => ?_) s hs
    simp [hv t ht]
  -- the row `q i` vanishes on `{v_{p i} = 0}`
  have hF2 : ∀ i ∈ A, ∀ v : ComplexModel n, v (p i) = 0 → L v (q i) = 0 := by
    intro i hi v hv
    refine apply_eq_zero_of_eventually_smul hΞd ?_
    filter_upwards [hsmall v] with τ hτ
    exact hvan i hi _ hτ (by simp [hv])
  have hF2' : ∀ i ∈ A, ∀ v : ComplexModel n,
      L v (q i) = v (p i) * L (EuclideanSpace.single (p i) 1) (q i) := by
    intro i hi v
    have h := hF2 i hi (v - v (p i) • EuclideanSpace.single (p i) 1) (by simp)
    rw [map_sub, map_smul] at h
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
    linear_combination h
  have hc : ∀ i ∈ A, L (EuclideanSpace.single (p i) 1) (q i) ≠ 0 := by
    intro i hi h0
    obtain ⟨v, hv⟩ := hLsurj (EuclideanSpace.single (q i) 1)
    have h := hF2' i hi v
    rw [hv, h0, mul_zero] at h
    simp at h
  -- the coordinates of `Y` not among the `p i`
  set Y' : Finset (Fin n) := Y.filter fun t => ∀ i ∈ A, p i ≠ t with hY'
  -- every value of the `S₀`-rows is attained on vectors supported on `Y'`
  have hsurj : ∀ b : S₀ → ℂ, ∃ v : ComplexModel n, (∀ t ∉ Y', v t = 0) ∧
      ∀ s : S₀, L v s = b s := by
    intro b
    obtain ⟨w, hw⟩ := hLsurj (WithLp.toLp 2 fun r => if h : r ∈ S₀ then b ⟨r, h⟩ else 0)
    have hwp : ∀ i ∈ A, w (p i) = 0 := by
      intro i hi
      have h1 := hF2' i hi w
      rw [hw] at h1
      simp only [hqS i hi, dite_false] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (hc i hi)
    refine ⟨WithLp.toLp 2 fun t => if t ∈ Y then w t else 0, fun t ht => ?_, fun s => ?_⟩
    · by_cases htY : t ∈ Y
      · have : ¬ ∀ i ∈ A, p i ≠ t := fun h => ht (Finset.mem_filter.mpr ⟨htY, h⟩)
        push Not at this
        obtain ⟨i, hi, rfl⟩ := this
        simp [htY, hwp i hi]
      · simp [htY]
    · have hd : (WithLp.toLp 2 fun t => if t ∈ Y then w t else 0 : ComplexModel n) - w ∈
          coordSubspace Y := by
        intro t ht
        simp [ht]
      have h1 := hF1 s s.2 _ hd
      rw [map_sub, PiLp.sub_apply, sub_eq_zero, hw] at h1
      rw [h1]
      simp
  -- the `S₀`-rows on the basis vectors of `Y'`
  set lam : Y' → (S₀ → ℂ) := fun y s => L (EuclideanSpace.single (y : Fin n) 1) s with hlam
  have hspan : Submodule.span ℂ (Set.range lam) = ⊤ := by
    refine eq_top_iff.mpr fun b _ => ?_
    obtain ⟨v, hv0, hvb⟩ := hsurj b
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun y => v y, ?_⟩
    ext s
    have hdec : L v = ∑ t ∈ Y', v t • L (EuclideanSpace.single t (1 : ℂ)) := by
      conv_lhs => rw [eq_sum_single_of_support hv0]
      simp only [map_sum, map_smul]
    rw [← hvb s, hdec, ← Finset.sum_coe_sort Y']
    simp [hlam]
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' ℂ lam
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = S₀.card := by
    have h1 := finrank_span_eq_card hli
    rw [hspa, hspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    exact h1.symm
  set X : Finset (Fin n) := Finset.univ.image fun k => ((a k : Y') : Fin n) with hXdef
  have hainj : Function.Injective fun k => ((a k : Y') : Fin n) :=
    Subtype.val_injective.comp ha
  have hXcard : X.card = S₀.card := by
    rw [hXdef, Finset.card_image_of_injective _ hainj, Finset.card_univ, hcardκ]
  have hXY' : X ⊆ Y' := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
    exact (a k).2
  have hXY : X ⊆ Y := hXY'.trans (Finset.filter_subset _ _)
  have hXp : ∀ i ∈ A, p i ∉ X := fun i hi h => (Finset.mem_filter.mp (hXY' h)).2 i hi rfl
  -- a bijection `X ≃ S₀`, extended to `Fin n`
  set βe : X ≃ S₀ := Finset.equivOfCardEq hXcard with hβe
  set β : Fin n → Fin n := fun t => if h : t ∈ X then (βe ⟨t, h⟩ : Fin n) else t with hβ
  have hβS : ∀ t ∈ X, β t ∈ S₀ := fun t ht => by simp only [hβ, ht, dite_true]; exact (βe _).2
  have hβsurj : ∀ s ∈ S₀, ∃ t ∈ X, β t = s := by
    intro s hs
    refine ⟨βe.symm ⟨s, hs⟩, (βe.symm ⟨s, hs⟩).2, ?_⟩
    simp only [hβ, (βe.symm ⟨s, hs⟩).2, dite_true, Subtype.coe_eta, Equiv.apply_symm_apply]
  -- the permutation
  obtain ⟨σ, hσ⟩ := exists_perm_nested hXY
  -- the new coordinates
  set R := selMap (fun r => σ.symm r) (fun r => σ.symm r ∉ X) with hR
  set Q := selMap (fun r => β (σ.symm r)) (fun r => σ.symm r ∈ X) with hQ
  set G : ComplexModel n → ComplexModel n := fun u => R u + Q (Ξ.toFun u) with hG
  have hGapp : ∀ u t, G u (σ t) = if t ∈ X then Ξ.toFun u (β t) else u t := by
    intro u t
    by_cases ht : t ∈ X
    · simp [hG, hR, hQ, selMap_apply, ht]
    · simp [hG, hR, hQ, selMap_apply, ht]
  have hGd : DifferentiableOn ℂ G Ξ.source :=
    R.differentiable.differentiableOn.add (Q.differentiable.comp_differentiableOn
      Ξ.toFun_holomorphic)
  have hGderiv : HasFDerivAt G (R + Q.comp L) 0 :=
    R.hasFDerivAt.add (Q.hasFDerivAt.comp 0 hΞd)
  have hinj : Function.Injective (fderiv ℂ G 0) := by
    rw [hGderiv.fderiv, injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ t, (if t ∈ X then L v (β t) else v t) = 0 := by
      intro t
      have h := congrArg (fun z : ComplexModel n => z (σ t)) hv
      by_cases ht : t ∈ X
      · simpa [hR, hQ, selMap_apply, ht] using h
      · simpa [hR, hQ, selMap_apply, ht] using h
    have hvX : ∀ t ∉ X, v t = 0 := fun t ht => by simpa [ht] using hv' t
    have hLv : ∀ s ∈ S₀, L v s = 0 := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hβsurj s hs
      simpa [ht] using hv' t
    have hdec : v = ∑ k : κ, v (a k) • EuclideanSpace.single ((a k : Y') : Fin n) (1 : ℂ) := by
      calc v = ∑ t ∈ X, v t • EuclideanSpace.single t (1 : ℂ) := eq_sum_single_of_support hvX
        _ = _ := by rw [hXdef, Finset.sum_image fun k _ l _ h => hainj h]
    have hcomb : ∑ k : κ, v (a k) • lam (a k) = 0 := by
      ext s
      have h := hLv s s.2
      rw [hdec] at h
      simpa [map_sum, map_smul, hlam] using h
    have hzero : ∀ k, v (a k) = 0 := Fintype.linearIndependent_iff.mp hli _ hcomb
    ext t
    by_cases ht : t ∈ X
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ht
      simpa using hzero k
    · simpa using hvX t ht
  -- the inverse function theorem, then a ball
  obtain ⟨Φ₀, hΦ₀s, hΦ₀G, -⟩ :=
    exists_localHolomorphicEquivAt Ξ.isOpen_source Ξ.center_mem_source hGd hinj
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp Φ₀.isOpen_source 0 Φ₀.center_mem_source
  set Φ := Φ₀.restrict (Metric.ball 0 ρ) Metric.isOpen_ball 0
    ⟨Φ₀.center_mem_source, Metric.mem_ball_self hρ⟩ with hΦ
  have hΦG : Φ.toFun = G := hΦ₀G
  refine ⟨X, σ, Φ, hXY, hXp, fun u hu => hΦ₀s hu.1, fun t => by rw [← hXcard]; exact (hσ t).1,
    fun u hu => ⟨?_, ?_, fun t ht => by rw [hΦG, hGapp]; simp [ht]⟩⟩
  · -- the centre
    have huΞ : u ∈ Ξ.source := hΦ₀s hu.1
    rw [hΦG]
    constructor
    · intro huY i hi
      obtain ⟨t, rfl⟩ := σ.surjective i
      rw [hGapp]
      by_cases ht : t ∈ X
      · simp only [ht, if_true]
        exact hYS u huΞ huY _ (hβS t ht)
      · simp only [ht, if_false]
        exact huY t ((hσ t).2.mp hi)
    · intro hGu
      have hGu' : ∀ t ∈ Y, (if t ∈ X then Ξ.toFun u (β t) else u t) = 0 := by
        intro t ht
        rw [← hGapp]
        exact hGu _ ((hσ t).2.mpr ht)
      set u' : ComplexModel n := WithLp.toLp 2 fun t => if t ∈ Y then 0 else u t with hu'
      have hu'Y : u' ∈ coordSubspace Y := by
        intro t ht
        simp [hu', ht]
      have hu'b : u' ∈ Metric.ball (0 : ComplexModel n) ρ := by
        have h1 := hu.2
        rw [Metric.mem_ball, dist_zero_right] at h1 ⊢
        exact (norm_zeroCoords_le Y u).trans_lt h1
      have hu's : u' ∈ Φ₀.source := hball hu'b
      have hG' : G u' = G u := by
        ext r
        obtain ⟨t, rfl⟩ := σ.surjective r
        rw [hGapp, hGapp]
        by_cases ht : t ∈ X
        · simp only [ht, if_true]
          rw [hYS u' (hΦ₀s hu's) hu'Y _ (hβS t ht)]
          have := hGu' t (hXY ht)
          simp only [ht, if_true] at this
          exact this.symm
        · simp only [ht, if_false]
          by_cases htY : t ∈ Y
          · have := hGu' t htY
            simp only [ht, if_false] at this
            simp [hu', htY, this]
          · simp [hu', htY]
      have huu' : u = u' := by
        have h1 := Φ₀.left_inv u hu.1
        have h2 := Φ₀.left_inv u' hu's
        rw [hΦ₀G] at h1 h2
        rw [← h1, ← h2, hG']
      rw [huu']
      exact hu'Y
  · -- the submanifold
    rw [hΦG]
    constructor
    · intro hΞu i hi
      obtain ⟨t, rfl⟩ := σ.surjective i
      rw [hGapp]
      have htX : t ∈ X := (hσ t).1.mp (by rw [hXcard]; exact hi)
      simp only [htX, if_true]
      exact hΞu _ (hβS t htX)
    · intro hGu s hs
      obtain ⟨t, ht, rfl⟩ := hβsurj s hs
      have h1 := hGu (σ t) (by rw [← hXcard]; exact (hσ t).1.mpr ht)
      rw [hGapp] at h1
      simpa [ht] using h1

end Model

/-! ### Simultaneous normal crossings coordinates on a manifold -/

section Manifold

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Members of a simple normal crossings divisor are distinct as germs**: two members through
`x` that agree near `x` are the same member. -/
theorem eq_of_eventually_mem_iff {E : List (Set X)} (hE : IsSNCDivisor n E) {x : X}
    {i j : Fin E.length} (hi : x ∈ E.get i) (hj : x ∈ E.get j)
    (hij : ∀ᶠ y in 𝓝 x, y ∈ E.get i ↔ y ∈ E.get j) : i = j := by
  classical
  by_contra hne
  obtain ⟨S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, hinj⟩ := hE.2 x
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hi)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard j hj)
  have hab : a ≠ b := fun h => hne (hinj hi hj (by rw [ha, hb, h]))
  let e := (complexChartAt (n := n) x).val
  have h0t : (0 : ComplexModel n) ∈ Φ.target := hΦ0 ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e x := by
    rw [← hΦ0]
    exact Φ.left_inv _ Φ.center_mem_source
  set v : ComplexModel n := EuclideanSpace.single b (1 : ℂ) with hv
  have hlin : Tendsto (fun τ : ℂ => τ • v) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun τ : ℂ => τ • v) (𝓝 0) (𝓝 ((0 : ℂ) • v)) :=
      (continuous_id.smul continuous_const : Continuous fun τ : ℂ => τ • v).tendsto 0
    rw [zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hinvc : ContinuousAt Φ.invFun 0 :=
    Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds h0t)
  have hsymm : ContinuousAt e.symm (e x) :=
    e.continuousAt_symm (e.map_source (mem_complexChartAt_source x))
  have hcurve : Tendsto (fun τ : ℂ => e.symm (Φ.invFun (τ • v))) (𝓝[≠] 0) (𝓝 x) := by
    have h1 : Tendsto (fun τ : ℂ => Φ.invFun (τ • v)) (𝓝[≠] 0) (𝓝 (Φ.invFun 0)) :=
      hinvc.tendsto.comp hlin
    rw [hinv0] at h1
    have h2 := hsymm.tendsto.comp h1
    rwa [e.left_inv (mem_complexChartAt_source x)] at h2
  have hev : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (e.symm (Φ.invFun (τ • v)) ∈ E.get i ↔ e.symm (Φ.invFun (τ • v)) ∈ E.get j) ∧
        τ • v ∈ Φ.target :=
    (hcurve.eventually hij).and (hlin.eventually (Φ.isOpen_target.mem_nhds h0t))
  obtain ⟨τ, ⟨hiff, htgt⟩, hτ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hwΦ : Φ.invFun (τ • v) ∈ Φ.source := Φ.mapsTo_invFun htgt
  have hwe : Φ.invFun (τ • v) ∈ e.target := hΦt hwΦ
  have hy : e.symm (Φ.invFun (τ • v)) ∈ e.source := e.map_target hwe
  have hey : e (e.symm (Φ.invFun (τ • v))) = Φ.invFun (τ • v) := e.right_inv hwe
  have hyΦ : e (e.symm (Φ.invFun (τ • v))) ∈ Φ.source := by rw [hey]; exact hwΦ
  have h1 : (e.symm (Φ.invFun (τ • v)) ∈ E.get i ↔
      Φ.toFun (e (e.symm (Φ.invFun (τ • v)))) ∈ coordSubspace (S i)) := hΦA i hi hy hyΦ
  have h2 : (e.symm (Φ.invFun (τ • v)) ∈ E.get j ↔
      Φ.toFun (e (e.symm (Φ.invFun (τ • v)))) ∈ coordSubspace (S j)) := hΦA j hj hy hyΦ
  rw [hey, Φ.right_inv _ htgt, ha, mem_coordSubspace_singleton] at h1
  rw [hey, Φ.right_inv _ htgt, hb, mem_coordSubspace_singleton] at h2
  have hva : (τ • v) a = 0 := by simp [hv, hab]
  have hvb : (τ • v) b ≠ 0 := by simpa [hv] using hτ
  exact hvb (h2.mp (hiff.mp (h1.mpr hva)))

/-- **Simultaneous normal crossings coordinates.**  If `E` is a simple normal crossings divisor
transverse to `N`, `C ⊆ N` and `C` has only normal crossings with `E`, then at every point of `C`
there are coordinates adapted to `C ⊆ N` and `E` (`C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`, each
member of `E` through the point a coordinate hyperplane `{w_{s i} = 0}`, `s i < k_N`, the
`s i` distinct).  (`0 < n` is needed for the indices `s i` to exist when `E` is nonempty.) -/
theorem isAdaptedAt_of_hasNormalCrossings (hn : 0 < n) {C N : Set X} {E : List (Set X)}
    (hCN : C ⊆ N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hnc : HasNormalCrossings n C E) {x : X} (hx : x ∈ C) : IsAdaptedAt n C N E x := by
  classical
  obtain ⟨S₀, S, ⟨Ψ, hΨt, hΨ0, hΨA⟩, hS⟩ := hT x (hCN hx)
  obtain ⟨Y, S', ⟨Θ, hΘt, hΘ0, hΘA⟩, hS'⟩ := hnc x hx
  let e := (complexChartAt (n := n) x).val
  -- the index of a one-element set
  set pick : Finset (Fin n) → Fin n := fun s => if h : s.Nonempty then s.min' h else ⟨0, hn⟩
    with hpick
  have hpick1 : ∀ s : Finset (Fin n), s.card = 1 → s = {pick s} := by
    intro s hs
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    simp [hpick]
  set t : Fin E.length → Fin n := fun i => pick (S i) with ht
  set t' : Fin E.length → Fin n := fun i => pick (S' i) with ht'
  -- the members through `x` in the two coordinate systems
  have hHΨ : ∀ i, x ∈ E.get i → ∀ {y : X}, y ∈ e.source → e y ∈ Ψ.source →
      (y ∈ E.get i ↔ Ψ.toFun (e y) (t i) = 0) := by
    intro i hi y hy hyΨ
    have h : (y ∈ E.get i ↔ Ψ.toFun (e y) ∈ coordSubspace (S i)) := hΨA (some i) hi hy hyΨ
    rw [hpick1 _ (hS i hi).1, mem_coordSubspace_singleton] at h
    exact h
  have htS : ∀ i, x ∈ E.get i → t i ∉ S₀ := by
    intro i hi h
    have h1 := (hS i hi).2
    rw [hpick1 _ (hS i hi).1] at h1
    exact Finset.disjoint_singleton_left.mp h1 h
  have hHΘ : ∀ i, x ∈ E.get i → ∀ {y : X}, y ∈ e.source → e y ∈ Θ.source →
      (y ∈ E.get i ↔ Θ.toFun (e y) (t' i) = 0) := by
    intro i hi y hy hyΘ
    have h : (y ∈ E.get i ↔ Θ.toFun (e y) ∈ coordSubspace (S' i)) := hΘA (some i) hi hy hyΘ
    rw [hpick1 _ (hS' i hi), mem_coordSubspace_singleton] at h
    exact h
  have hNΨ : ∀ {y : X}, y ∈ e.source → e y ∈ Ψ.source →
      (y ∈ N ↔ Ψ.toFun (e y) ∈ coordSubspace S₀) := fun hy hyΨ => hΨA none (hCN hx) hy hyΨ
  have hCΘ : ∀ {y : X}, y ∈ e.source → e y ∈ Θ.source →
      (y ∈ C ↔ Θ.toFun (e y) ∈ coordSubspace Y) := fun hy hyΘ => hΘA none hx hy hyΘ
  -- the members through `x` are distinct coordinate hyperplanes of `Θ`
  have ht'inj : Set.InjOn t' {i | x ∈ E.get i} := by
    intro i hi j hj hij
    refine eq_of_eventually_mem_iff hE hi hj ?_
    have hU : e.source ∩ e ⁻¹' Θ.source ∈ 𝓝 x :=
      (e.continuousOn.isOpen_inter_preimage e.open_source Θ.isOpen_source).mem_nhds
        ⟨mem_complexChartAt_source x, Θ.center_mem_source⟩
    filter_upwards [hU] with y hy
    rw [hHΘ i hi hy.1 hy.2, hHΘ j hj hy.1 hy.2, hij]
  -- `Ξ = Ψ ∘ Θ⁻¹` in the `Θ`-coordinates
  have h0Θ : (0 : ComplexModel n) ∈ Θ.target := hΘ0 ▸ Θ.mapsTo_toFun Θ.center_mem_source
  have hΘinv0 : Θ.invFun 0 = e x := by
    rw [← hΘ0]
    exact Θ.left_inv _ Θ.center_mem_source
  set Ξ := LocalHolomorphicEquivAt.comp (symmAt Θ h0Θ) Ψ hΘinv0 with hΞ
  -- a point of `Ξ.source` comes from the point `e.symm (Θ⁻¹ u)` of `X`
  have hpt : ∀ u ∈ Ξ.source, e.symm (Θ.invFun u) ∈ e.source ∧
      e (e.symm (Θ.invFun u)) ∈ Θ.source ∧ e (e.symm (Θ.invFun u)) ∈ Ψ.source ∧
      Θ.toFun (e (e.symm (Θ.invFun u))) = u ∧
      Ψ.toFun (e (e.symm (Θ.invFun u))) = Ξ.toFun u := by
    intro u hu
    have hwΘ : Θ.invFun u ∈ Θ.source := Θ.mapsTo_invFun hu.1
    have hwe : Θ.invFun u ∈ e.target := hΘt hwΘ
    rw [e.right_inv hwe]
    exact ⟨e.map_target hwe, hwΘ, hu.2, Θ.right_inv u hu.1, rfl⟩
  -- the model
  obtain ⟨Xs, σ, Φ', hXY, hXp, hΦ's, hσ, hΦ'⟩ := exists_model_coords Ξ Y S₀
    {i | x ∈ E.get i ∧ t' i ∈ Y} t' t (fun i hi => htS i hi.1)
    (fun i hi u hu hu0 => by
      obtain ⟨hy, hyΘ, hyΨ, hΘu, hΨu⟩ := hpt u hu
      have hmem : e.symm (Θ.invFun u) ∈ E.get i := (hHΘ i hi.1 hy hyΘ).mpr (by rw [hΘu]; exact hu0)
      rw [← hΨu]
      exact (hHΨ i hi.1 hy hyΨ).mp hmem)
    (fun u hu huY => by
      obtain ⟨hy, hyΘ, hyΨ, hΘu, hΨu⟩ := hpt u hu
      have hmem : e.symm (Θ.invFun u) ∈ C := (hCΘ hy hyΘ).mpr (by rw [hΘu]; exact huY)
      rw [← hΨu]
      exact (hNΨ hy hyΨ).mp (hCN hmem))
  have hΘΦ : Θ.toFun (e x) = 0 := hΘ0
  refine ⟨n - Y.card, n - S₀.card, LocalHolomorphicEquivAt.comp Θ Φ' hΘΦ,
    fun i => σ (t' i), fun w hw => hΘt hw.1, fun i hi => ?_,
    σ.injective.comp_injOn ht'inj, fun {y} hy hyΦ => ?_⟩
  · -- the hyperplane indices are below `k_N`
    by_contra h
    have hX : t' i ∈ Xs := (hσ (t' i)).mp (not_lt.mp h)
    exact hXp i ⟨hi, hXY hX⟩ hX
  · -- the three descriptions
    obtain ⟨hyΘ, huΦ'⟩ := hyΦ
    set u := Θ.toFun (e y) with hu
    have huΞ : u ∈ Ξ.source := hΦ's huΦ'
    have hinv : Θ.invFun u = e y := Θ.left_inv _ hyΘ
    have hyΨ : e y ∈ Ψ.source := by rw [← hinv]; exact huΞ.2
    have hΞu : Ξ.toFun u = Ψ.toFun (e y) := by
      show Ψ.toFun (Θ.invFun u) = _
      rw [hinv]
    obtain ⟨hC', hN', hH'⟩ := hΦ' u huΦ'
    change (y ∈ C ↔ Φ'.toFun u ∈ _) ∧ (y ∈ N ↔ Φ'.toFun u ∈ _) ∧
      ∀ i, x ∈ E.get i → (y ∈ E.get i ↔ Φ'.toFun u (σ (t' i)) = 0)
    refine ⟨(hCΘ hy hyΘ).trans hC', (hNΨ hy hyΨ).trans (hΞu ▸ hN'), fun i hi => ?_⟩
    have hX : t' i ∉ Xs := by
      intro h
      exact hXp i ⟨hi, hXY h⟩ h
    rw [hH' _ hX]
    exact hHΘ i hi hy hyΘ

/-- **A simple normal crossings divisor is transverse to the whole manifold** (`N = X`, cut out by
no coordinate). -/
theorem isTransverse_univ_of_isSNCDivisor {E : List (Set X)} (hE : IsSNCDivisor n E) :
    IsTransverse n (univ : Set X) E := by
  intro x _
  obtain ⟨S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, -⟩ := hE.2 x
  refine ⟨∅, S, ⟨Φ, hΦt, hΦ0, ?_⟩, fun i hi => ⟨hcard i hi, Finset.disjoint_empty_right _⟩⟩
  rintro (_ | i) hi y hy hyΦ
  · simp [coordSubspace]
  · exact hΦA i hi hy hyΦ

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **A blowup centre with a point lives in positive dimension**: in dimension `0` every point is
open, while the centre of a blowup has empty interior. -/
theorem pos_of_isBlowupAlong {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) {x : X}
    (hx : x ∈ C) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exfalso
    have hsub : ∀ z w : ComplexModel 0, z = w := fun z w => by
      ext i
      exact i.elim0
    have hsrc : (chartAt (ComplexModel 0) x).source = {x} := by
      ext y
      constructor
      · intro hy
        have h1 := (chartAt (ComplexModel 0) x).left_inv hy
        have h2 := (chartAt (ComplexModel 0) x).left_inv (mem_chart_source _ x)
        rw [hsub (chartAt (ComplexModel 0) x y) (chartAt (ComplexModel 0) x x), h2] at h1
        exact h1.symm
      · intro hy
        rw [Set.mem_singleton_iff.mp hy]
        exact mem_chart_source _ x
    have hopen : IsOpen ({x} : Set X) := hsrc ▸ (chartAt (ComplexModel 0) x).open_source
    have hint : x ∈ interior C :=
      interior_mono (singleton_subset_iff.mpr hx) (hopen.interior_eq.symm ▸ rfl)
    rw [hπ.2.1] at hint
    exact hint
  · exact h0

/-- **The transformed divisor is simple normal crossings** (Bierstone--Milman 2008, remark after
Definitions 2.2): if `E` is a simple normal crossings divisor and the centre `C` has only normal
crossings with `E`, then `[H₁', …, H_s', π⁻¹ C]` is a simple normal crossings divisor. -/
theorem isSNCDivisor_geoTransformE_of_hasNormalCrossings {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hnc : HasNormalCrossings n C E) :
    IsSNCDivisor n (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) :=
  isSNCDivisor_geoTransformE hπ (N := univ) hE fun _ hx =>
    isAdaptedAt_of_hasNormalCrossings (pos_of_isBlowupAlong hπ hx) (subset_univ C) hE
      (isTransverse_univ_of_isSNCDivisor hE) hnc hx

/-- **The transformed divisor is transverse to the strict transform** (Bierstone--Milman 2008,
remark after Definitions 2.2): if `E` is a simple normal crossings divisor transverse to the closed
set `N ⊇ C` and `C` has only normal crossings with `E`, then `[H₁', …, H_s', π⁻¹ C]` is transverse
to `N' = closure (π⁻¹(N \ C))`. -/
theorem isTransverse_geoTransformE_of_hasNormalCrossings {C N : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hNc : IsClosed N) (hCN : C ⊆ N) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) (hnc : HasNormalCrossings n C E) :
    IsTransverse n (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) :=
  isTransverse_geoTransformE hπ hNc hE hT fun _ hx =>
    isAdaptedAt_of_hasNormalCrossings (pos_of_isBlowupAlong hπ hx) hCN hE hT hnc hx

end Manifold

end

end Hironaka.SimultaneousNormalCrossings
