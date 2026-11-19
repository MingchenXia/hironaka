import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

/-!
# Closure of an invariant subspace under an approximate nilpotent division

This is the linear-algebra core that replaces Galligo's division estimate in the
proof of strong openness for increasing sequences (`Hironaka.StrongOpennessRegularRoute`).

Let `E` be a finite-dimensional complex normed space, `T` a nilpotent endomorphism and
`U` a `T`-invariant subspace.  Suppose that for a sequence of nonzero scalars `w k` and
vectors `Y k → 0`,

  `T (Y k) - w k • Y k + w k • x ∈ U`.

Then `x ∈ U`.

In the application `E` is the space of Taylor coefficients of order below `N`, `U`
the image of an ideal of germs, `T` multiplication by the last coordinate, and the
relation is `F - f = (z_last - w) g` with `F` in the ideal and `Y = w g` small.

The proof is a downward induction on `k` showing `T^k x ∈ U`.  For `w ≠ 0` the map
`w - T` is injective modulo `U`, since `T^N = 0`.  So applying `T^{k+1}` to the relation
puts `T^{k+1} Y` in `U`, and applying `T^k` puts `T^k x - T^k Y` in `U`.  Letting
`Y → 0` gives `T^k x` in the closure of `U`, which is `U`.
-/

open Filter
open scoped Topology

namespace Hironaka

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For `w ≠ 0` and nilpotent `T` preserving `U`, `w - T` is injective modulo `U`. -/
theorem mem_of_sub_smul_mem_of_nilpotent (U : Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hTU : ∀ u ∈ U, T u ∈ U) {N : ℕ} (hN : T ^ N = 0) {w : ℂ} (hw : w ≠ 0) {z : E}
    (hz : T z - w • z ∈ U) : z ∈ U := by
  have key : ∀ i : ℕ, (T ^ i) z - w ^ i • z ∈ U := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        have h1 : T ((T ^ i) z - w ^ i • z) ∈ U := hTU _ ih
        have h2 : w ^ i • (T z - w • z) ∈ U := U.smul_mem _ hz
        have : (T ^ (i + 1)) z - w ^ (i + 1) • z =
            T ((T ^ i) z - w ^ i • z) + w ^ i • (T z - w • z) := by
          rw [pow_succ', Module.End.mul_apply, map_sub, map_smul, smul_sub, smul_smul,
            pow_succ]
          abel
        rw [this]
        exact U.add_mem h1 h2
  have hN' := key N
  rw [hN, LinearMap.zero_apply, zero_sub, neg_mem_iff] at hN'
  have hwN : w ^ N ≠ 0 := pow_ne_zero N hw
  simpa [hwN] using U.smul_mem (w ^ N)⁻¹ hN'

variable [FiniteDimensional ℂ E]

/-- **Closure under approximate nilpotent division.**  If `T` is nilpotent and preserves
the subspace `U` of a finite-dimensional space, and `T (Y k) - w k • Y k + w k • x ∈ U`
for nonzero scalars `w k` and vectors `Y k → 0`, then `x ∈ U`. -/
theorem mem_of_nilpotent_shift_relation (U : Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hTU : ∀ u ∈ U, T u ∈ U) {N : ℕ} (hN : T ^ N = 0) (x : E) (w : ℕ → ℂ) (Y : ℕ → E)
    (hw : ∀ k, w k ≠ 0) (hY : Tendsto Y atTop (𝓝 0))
    (hrel : ∀ k, T (Y k) - w k • Y k + w k • x ∈ U) : x ∈ U := by
  have hTiU : ∀ i : ℕ, ∀ u ∈ U, (T ^ i) u ∈ U := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        intro u hu
        rw [pow_succ', Module.End.mul_apply]
        exact hTU _ (ih u hu)
  have hUclosed : IsClosed (U : Set E) := U.closed_of_finiteDimensional
  -- Downward induction: `T^(N - i) x ∈ U` for all `i ≤ N`.
  have hdown : ∀ i : ℕ, i ≤ N → (T ^ (N - i)) x ∈ U := by
    intro i
    induction i with
    | zero => intro _; simp [hN]
    | succ i ih =>
        intro hi
        set k := N - (i + 1) with hk
        have hk1 : N - i = k + 1 := by omega
        have hxk1 : (T ^ (k + 1)) x ∈ U := hk1 ▸ ih (by omega)
        -- `T^(k+1) (Y j) ∈ U` for every `j`.
        have hYk1 : ∀ j, (T ^ (k + 1)) (Y j) ∈ U := by
          intro j
          refine mem_of_sub_smul_mem_of_nilpotent U T hTU hN (hw j) ?_
          have h := hTiU (k + 1) _ (hrel j)
          have hsm : w j • (T ^ (k + 1)) x ∈ U := U.smul_mem _ hxk1
          have : T ((T ^ (k + 1)) (Y j)) - w j • (T ^ (k + 1)) (Y j) =
              (T ^ (k + 1)) (T (Y j) - w j • Y j + w j • x) - w j • (T ^ (k + 1)) x := by
            have e : ∀ v, (T ^ (k + 1)) (T v) = T ((T ^ (k + 1)) v) := fun v => by
              rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
            rw [map_add, map_sub, map_smul, map_smul, e]
            abel
          rw [this]
          exact U.sub_mem h hsm
        -- `T^k x - T^k (Y j) ∈ U` for every `j`.
        have hdiff : ∀ j, (T ^ k) x - (T ^ k) (Y j) ∈ U := by
          intro j
          have h := hTiU k _ (hrel j)
          have hwU : w j • ((T ^ k) x - (T ^ k) (Y j)) ∈ U := by
            have : w j • ((T ^ k) x - (T ^ k) (Y j)) =
                (T ^ k) (T (Y j) - w j • Y j + w j • x) - (T ^ (k + 1)) (Y j) := by
              have e : ∀ v, (T ^ k) (T v) = (T ^ (k + 1)) v := fun v => by
                rw [pow_succ, Module.End.mul_apply]
              rw [map_add, map_sub, map_smul, map_smul, e, smul_sub]
              abel
            rw [this]
            exact U.sub_mem h (hYk1 j)
          simpa [hw j] using U.smul_mem (w j)⁻¹ hwU
        have hcont : Continuous (T ^ k) := LinearMap.continuous_of_finiteDimensional _
        have hlim : Tendsto (fun j => (T ^ k) x - (T ^ k) (Y j)) atTop (𝓝 ((T ^ k) x)) := by
          have := (hcont.tendsto 0).comp hY
          simpa using tendsto_const_nhds.sub this
        exact hUclosed.mem_of_tendsto hlim (Eventually.of_forall hdiff)
  simpa using hdown N le_rfl

end Hironaka
