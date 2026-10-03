/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaRelationSheaf
import Hironaka.Coherence.OkaGermRelations
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.HolomorphicGermRing
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# From functions holomorphic near a point to germs at the origin, and back

The function-level statements of `OkaRelationSheaf` (eventual identities near a point `y`) are
translated into the ring `HolGerm Z` of germs at the origin by `germAt y f`, the germ at `0` of
`x ↦ f (y + x)`.  For functions holomorphic near `y`, `germAt y` is additive and multiplicative,
detects eventual equality near `y`, and is onto.

On `E × ℂ`, polynomials in the last variable with coefficients holomorphic near `z₀` are
evaluated at `(z₀, t₀)` by `OkaGermRelations.shiftEval t₀`:
`shiftEval_sum_C_germAt`: `shiftEval t₀ (∑_{k<n} C (germAt z₀ α_k) X^k)` is the germ at `(z₀, t₀)`
of `(z, t) ↦ ∑_{k<n} α_k(z) t^k`.
-/

open Filter Topology Polynomial

namespace Hironaka.OkaGermBridge

open HolGerm OkaRelationSheaf OkaGermRelations

noncomputable section

section General

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem eventually_nhds_iff_translate {p : Z → Prop} (y : Z) :
    (∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 (0 : Z), p (y + x) := by
  rw [← map_add_left_nhds_zero y, eventually_map]

theorem _root_.Hironaka.OkaRelationSheaf.HolAt.translate {f : Z → ℂ} {y : Z} (hf : HolAt f y) :
    ∀ᶠ x in 𝓝 (0 : Z), DifferentiableAt ℂ (fun x => f (y + x)) x := by
  have h1 : HolAt f ((fun x => y + x) 0) := by
    show HolAt f (y + 0)
    rw [add_zero]
    exact hf
  exact h1.comp (continuous_const.add continuous_id)
    (fun x => (differentiableAt_const y).add differentiableAt_id)

/-- The germ at `0` of `x ↦ f (y + x)` (zero if `f` is not holomorphic near `y`). -/
def germAt (y : Z) (f : Z → ℂ) : HolGerm Z :=
  haveI := Classical.propDecidable (HolAt f y)
  if h : HolAt f y then HolGerm.mk (fun x => f (y + x)) h.translate else 0

theorem germAt_of_holAt {f : Z → ℂ} {y : Z} (hf : HolAt f y) :
    germAt y f = HolGerm.mk (fun x => f (y + x)) hf.translate :=
  dif_pos hf

theorem germAt_eq_germAt_iff {f g : Z → ℂ} {y : Z} (hf : HolAt f y) (hg : HolAt g y) :
    germAt y f = germAt y g ↔ f =ᶠ[𝓝 y] g := by
  rw [germAt_of_holAt hf, germAt_of_holAt hg, mk_eq_mk_iff]
  exact (eventually_nhds_iff_translate (p := fun x => f x = g x) y).symm

theorem germAt_add {f g : Z → ℂ} {y : Z} (hf : HolAt f y) (hg : HolAt g y) :
    germAt y (fun x => f x + g x) = germAt y f + germAt y g := by
  rw [germAt_of_holAt hf, germAt_of_holAt hg, germAt_of_holAt (hf.add hg), ← mk_add]

theorem germAt_mul {f g : Z → ℂ} {y : Z} (hf : HolAt f y) (hg : HolAt g y) :
    germAt y (fun x => f x * g x) = germAt y f * germAt y g := by
  rw [germAt_of_holAt hf, germAt_of_holAt hg, germAt_of_holAt (hf.mul hg), ← mk_mul]

theorem germAt_const (c : ℂ) (y : Z) : germAt y (fun _ => c) = constHom c := by
  rw [germAt_of_holAt (holAt_const c y)]
  rfl

theorem germAt_zero (y : Z) : germAt y (fun _ => (0 : ℂ)) = 0 := by
  rw [germAt_const, map_zero]

theorem germAt_sum {α : Type*} (s : Finset α) {f : α → Z → ℂ} {y : Z}
    (hf : ∀ i ∈ s, HolAt (f i) y) : germAt y (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, germAt y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using germAt_zero y
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hs : HolAt (fun x => ∑ i ∈ s, f i x) y :=
        HolAt.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [germAt_add (hf a (Finset.mem_insert_self a s)) hs,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem germAt_pow {f : Z → ℂ} {y : Z} (hf : HolAt f y) (n : ℕ) :
    germAt y (fun x => f x ^ n) = germAt y f ^ n := by
  induction n with
  | zero => simpa using germAt_const (1 : ℂ) y
  | succ n ih =>
      have hfn : HolAt (fun x => f x ^ n) y := hf.eventually.mono fun x hx => by
        exact (hx.differentiableAt.pow n)
      simp only [pow_succ]
      rw [germAt_mul hfn hf, ih]

/-- Every germ at `0` is `germAt y f` for some `f` holomorphic near `y`. -/
theorem exists_germAt_eq (g : HolGerm Z) (y : Z) : ∃ f : Z → ℂ, HolAt f y ∧ germAt y f = g := by
  obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
  have hf' : HolAt (fun x => f (x - y)) y := by
    have h1 : HolAt f ((fun x => x - y) y) := by
      show HolAt f (y - y)
      rw [sub_self]
      exact hf
    exact HolAt.comp (φ := fun x => x - y) (y := y) h1 (continuous_id.sub continuous_const)
      (fun x => differentiableAt_id.sub (differentiableAt_const y))
  refine ⟨fun x => f (x - y), hf', ?_⟩
  rw [germAt_of_holAt hf', mk_eq_mk_iff]
  exact Eventually.of_forall fun x => by simp

/-- A germ vanishes iff the function vanishes near the point. -/
theorem germAt_eq_zero_iff {f : Z → ℂ} {y : Z} (hf : HolAt f y) :
    germAt y f = 0 ↔ f =ᶠ[𝓝 y] fun _ => 0 := by
  rw [← germAt_zero y, germAt_eq_germAt_iff hf (holAt_const 0 y)]

end General

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem _root_.Hironaka.OkaRelationSheaf.HolAt.comp_fst {f : E → ℂ} {z₀ : E} (hf : HolAt f z₀) (t₀ : ℂ) :
    HolAt (fun x : E × ℂ => f x.1) (z₀, t₀) :=
  HolAt.comp (φ := Prod.fst) (y := (z₀, t₀)) hf continuous_fst fun _ => differentiableAt_fst

theorem holAt_snd (y : E × ℂ) : HolAt (fun x : E × ℂ => x.2) y :=
  Eventually.of_forall fun _ => differentiableAt_snd

theorem ofFst_germAt {f : E → ℂ} {z₀ : E} (hf : HolAt f z₀) (t₀ : ℂ) :
    ofFst (germAt z₀ f) = germAt ((z₀, t₀) : E × ℂ) (fun x => f x.1) := by
  rw [germAt_of_holAt hf, germAt_of_holAt (hf.comp_fst t₀)]
  rfl

theorem lastCoord_add_ofFst_constHom (z₀ : E) (t₀ : ℂ) :
    (lastCoord : HolGerm (E × ℂ)) + ofFst (constHom t₀) =
      germAt ((z₀, t₀) : E × ℂ) (fun x => x.2) := by
  rw [germAt_of_holAt (holAt_snd _)]
  have h : ofFst (constHom t₀ : HolGerm E) = constHom t₀ := rfl
  rw [h, HolGerm.lastCoord, ← mk_const, ← mk_add, mk_eq_mk_iff]
  exact Eventually.of_forall fun x => by simp [add_comm]

/-- The germ at `(z₀, t₀)` of `(z, t) ↦ ∑_{k<n} α_k(z) t^k` is `shiftEval t₀` of the polynomial
with the germs of the `α_k` as coefficients. -/
theorem shiftEval_sum_C_germAt {z₀ : E} (t₀ : ℂ) {α : ℕ → E → ℂ} {n : ℕ}
    (hα : ∀ k < n, HolAt (α k) z₀) :
    shiftEval t₀ (∑ k ∈ Finset.range n, C (germAt z₀ (α k)) * X ^ k) =
      germAt ((z₀, t₀) : E × ℂ) (fun x => ∑ k ∈ Finset.range n, α k x.1 * x.2 ^ k) := by
  have hterm : ∀ k ∈ Finset.range n, HolAt (fun x : E × ℂ => α k x.1 * x.2 ^ k) (z₀, t₀) :=
    fun k hk => ((hα k (Finset.mem_range.1 hk)).comp_fst t₀).mul
      ((holAt_snd _).eventually.mono fun x hx => hx.differentiableAt.pow k)
  rw [germAt_sum _ hterm, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := hα k (Finset.mem_range.1 hk)
  have hpow : HolAt (fun x : E × ℂ => x.2 ^ k) (z₀, t₀) :=
    (holAt_snd _).eventually.mono fun x hx => hx.differentiableAt.pow k
  rw [germAt_mul (hk'.comp_fst t₀) hpow, germAt_pow (holAt_snd _) k, ← ofFst_germAt hk' t₀,
    ← lastCoord_add_ofFst_constHom z₀ t₀]
  simp only [shiftEval, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow]

end Product

end

end Hironaka.OkaGermBridge
