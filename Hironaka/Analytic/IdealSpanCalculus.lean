/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false

/-!
# Local spans of holomorphic functions

Local spans of families of holomorphic functions at a point (`IsInSpanAt`) and along a subset (`IsInSpanOnAt`):
monotonicity, sums, products with holomorphic functions, transitivity, and holomorphic multiples of members of
coherent and invertible ideal sheaves.

Declarations:
* `IsInSpanAt.restrict`
* `IsInSpanOnAt.mono`
* `IsInSpanAt.add`
* `IsInSpanAt.mul_left`
* `IsInSpanAt.sum`
* `IsInSpanAt.trans`
* `IsInSpanOnAt.mul_left`
* `IsInSpanOnAt.add`
* `IsInSpanOnAt.sum`
* `IsInSpanOnAt.congr_right`
* `IsInSpanOnAt.trans`
* `holomorphicAt_inv`
* `IsInSpanOnAt.cancel_right_of_holomorphicAt_ne_zero`
* `GermIdeal.mem_pullback_iff`
* `GermIdeal.IsCoherent.holomorphicAt_mem`
* `GermIdeal.IsInvertible.holomorphicAt_mem`
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.RelativePrincipalizationSpan

open Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

section Span

variable {W : Set M} {x : M} {g g' c : M → ℂ} {S T : (M → ℂ) → Prop}

/-- An ambient germ relation restricts to a relation on any subset. -/
theorem IsInSpanAt.restrict (hg : IsInSpanAt (n := n) S x g) :
    IsInSpanOnAt (n := n) W S x g := by
  obtain ⟨_, N, s, a, hs, ha, hsum⟩ := hg
  exact ⟨N, s, a, hs, ha, hsum.mono fun _ hy _ => hy⟩

/-- Restricted span membership is monotone in the family of generators. -/
theorem IsInSpanOnAt.mono (hST : ∀ s, S s → T s)
    (hg : IsInSpanOnAt (n := n) W S x g) : IsInSpanOnAt (n := n) W T x g := by
  obtain ⟨N, s, a, hs, ha, hsum⟩ := hg
  exact ⟨N, s, a, fun i => hST _ (hs i), ha, hsum⟩

/-- Ambient span membership is closed under addition. -/
theorem IsInSpanAt.add (hg : IsInSpanAt (n := n) S x g)
    (hg' : IsInSpanAt (n := n) S x g') :
    IsInSpanAt (n := n) S x (fun y => g y + g' y) := by
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hg
  obtain ⟨hhol', N', s', a', hs', ha', hsum'⟩ := hg'
  refine ⟨hhol.add hhol', N + N', Fin.addCases s s', Fin.addCases a a',
    ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using hs j
    · intro j
      simpa using hs' j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using ha j
    · intro j
      simpa using ha' j
  filter_upwards [hsum, hsum'] with y hy hy'
  rw [hy, hy']
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- Ambient span membership is closed under multiplication by a holomorphic
coefficient. -/
theorem IsInSpanAt.mul_left (hc : HolomorphicAt n c x)
    (hg : IsInSpanAt (n := n) S x g) :
    IsInSpanAt (n := n) S x (fun y => c y * g y) := by
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hg
  refine ⟨hc.mul hhol, N, s, fun i y => c y * a i y, hs,
    fun i => hc.mul (ha i), ?_⟩
  filter_upwards [hsum] with y hy
  rw [hy, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A finite sum of ambient span relations is again an ambient span relation. -/
theorem IsInSpanAt.sum {ι : Type*} (I : Finset ι) {F : ι → M → ℂ}
    (hF : ∀ i ∈ I, IsInSpanAt (n := n) S x (F i)) :
    IsInSpanAt (n := n) S x (fun y => ∑ i ∈ I, F i y) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨holomorphicAt_const (n := n) (x := x) 0, 0, Fin.elim0, Fin.elim0,
      ?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · exact Eventually.of_forall fun _ => by simp
  | insert i I hi ih =>
    simpa [Finset.sum_insert, hi] using
      IsInSpanAt.add (hF i (Finset.mem_insert_self i I))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- Finite linear combinations may substitute a span relation for each
generator. -/
theorem IsInSpanAt.trans (hST : ∀ s, S s → IsInSpanAt (n := n) T x s)
    (hg : IsInSpanAt (n := n) S x g) : IsInSpanAt (n := n) T x g := by
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hg
  let F : Fin N → M → ℂ := fun i y => a i y * s i y
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin N)), IsInSpanAt (n := n) T x (F i) := by
    intro i _
    exact IsInSpanAt.mul_left (ha i) (hST _ (hs i))
  obtain ⟨_, K, t, b, ht, hb, hFsum⟩ :=
    IsInSpanAt.sum (n := n) (S := T) (x := x) Finset.univ hF
  refine ⟨hhol, K, t, b, ht, hb, ?_⟩
  filter_upwards [hsum, hFsum] with y hy hy'
  rw [hy]
  simpa [F] using hy'

/-- A restricted span relation may be multiplied by a holomorphic coefficient. -/
theorem IsInSpanOnAt.mul_left (hc : HolomorphicAt n c x)
    (hg : IsInSpanOnAt (n := n) W S x g) :
    IsInSpanOnAt (n := n) W S x (fun y => c y * g y) := by
  obtain ⟨N, s, a, hs, ha, hsum⟩ := hg
  refine ⟨N, s, fun i y => c y * a i y, hs, fun i => hc.mul (ha i), ?_⟩
  filter_upwards [hsum] with y hy hyW
  rw [hy hyW, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Restricted span membership is closed under addition. -/
theorem IsInSpanOnAt.add (hg : IsInSpanOnAt (n := n) W S x g)
    (hg' : IsInSpanOnAt (n := n) W S x g') :
    IsInSpanOnAt (n := n) W S x (fun y => g y + g' y) := by
  obtain ⟨N, s, a, hs, ha, hsum⟩ := hg
  obtain ⟨N', s', a', hs', ha', hsum'⟩ := hg'
  refine ⟨N + N', Fin.addCases s s', Fin.addCases a a',
    ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using hs j
    · intro j
      simpa using hs' j
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using ha j
    · intro j
      simpa using ha' j
  filter_upwards [hsum, hsum'] with y hy hy' hyW
  rw [hy hyW, hy' hyW]
  simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- A finite sum of restricted span relations is again a restricted span
relation. -/
theorem IsInSpanOnAt.sum {ι : Type*} (I : Finset ι) {F : ι → M → ℂ}
    (hF : ∀ i ∈ I, IsInSpanOnAt (n := n) W S x (F i)) :
    IsInSpanOnAt (n := n) W S x (fun y => ∑ i ∈ I, F i y) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · exact Eventually.of_forall fun _ _ => by simp
  | insert i I hi ih =>
    simpa [Finset.sum_insert, hi] using
      IsInSpanOnAt.add (hF i (Finset.mem_insert_self i I))
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- A restricted span relation is invariant under equality on the subset near
the base point. -/
theorem IsInSpanOnAt.congr_right (hg : IsInSpanOnAt (n := n) W S x g)
    (hgg' : ∀ᶠ y in 𝓝 x, y ∈ W → g' y = g y) :
    IsInSpanOnAt (n := n) W S x g' := by
  obtain ⟨N, s, a, hs, ha, hsum⟩ := hg
  refine ⟨N, s, a, hs, ha, ?_⟩
  filter_upwards [hgg', hsum] with y hgg' hy hyW
  rw [hgg' hyW, hy hyW]

/-- Restricted finite linear combinations may substitute a restricted span
relation for each generator. -/
theorem IsInSpanOnAt.trans (hST : ∀ s, S s → IsInSpanOnAt (n := n) W T x s)
    (hg : IsInSpanOnAt (n := n) W S x g) : IsInSpanOnAt (n := n) W T x g := by
  obtain ⟨N, s, a, hs, ha, hsum⟩ := hg
  let F : Fin N → M → ℂ := fun i y => a i y * s i y
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      IsInSpanOnAt (n := n) W T x (F i) := by
    intro i _
    exact IsInSpanOnAt.mul_left (ha i) (hST _ (hs i))
  obtain ⟨K, t, b, ht, hb, hFsum⟩ :=
    IsInSpanOnAt.sum (n := n) (W := W) (S := T) (x := x) Finset.univ hF
  refine ⟨K, t, b, ht, hb, ?_⟩
  filter_upwards [hsum, hFsum] with y hy hy' hyW
  rw [hy hyW]
  simpa [F] using hy' hyW

/-- The reciprocal of a holomorphic germ nonzero at the base point is
holomorphic. -/
theorem holomorphicAt_inv (hc : HolomorphicAt n c x) (hcx : c x ≠ 0) :
    HolomorphicAt n (fun y => (c y)⁻¹) x := by
  filter_upwards [hc.eventually,
    hc.continuousAt.eventually (isOpen_ne.mem_nhds hcx)] with y hy hy0
  exact (differentiableAt_inv hy0).mdifferentiableAt.comp y hy.mdifferentiableAt

/-- A nonzero holomorphic factor can be cancelled from a restricted span
relation. -/
theorem IsInSpanOnAt.cancel_right_of_holomorphicAt_ne_zero {q : M → ℂ}
    (hq : HolomorphicAt n q x) (hqx : q x ≠ 0)
    (hg : IsInSpanOnAt (n := n) W S x (fun y => g y * q y)) :
    IsInSpanOnAt (n := n) W S x g := by
  refine IsInSpanOnAt.congr_right
    (IsInSpanOnAt.mul_left (holomorphicAt_inv hq hqx) hg) ?_
  filter_upwards [hq.continuousAt.eventually_ne hqx] with y hy _
  calc
    g y = 1 * g y := (one_mul _).symm
    _ = (q y)⁻¹ * q y * g y := by rw [inv_mul_cancel₀ hy]
    _ = (q y)⁻¹ * (g y * q y) := by ring

end Span

section Pullback

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel m) Y]
  {f : Y → M} {𝔞 : GermIdeal n M} {y : Y} {g : Y → ℂ}

/-- Unfolding a pullback ideal gives exactly the ambient span of the pulled-back
source family.  In particular, this is an ambient-germ statement, rather than
the restricted-span statement needed on a strict transform. -/
theorem GermIdeal.mem_pullback_iff :
    (GermIdeal.pullback (m := m) f 𝔞).mem y g ↔
      IsInSpanAt (n := m)
        (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g :=
  Iff.rfl

/-- Coherence forces every recorded ideal member to be holomorphic at the
corresponding point.  This supplies the regularity needed when a source
generator is promoted to an ambient pullback germ. -/
theorem GermIdeal.IsCoherent.holomorphicAt_mem
    (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ} (hg : 𝔞.mem x g) :
    HolomorphicAt n g x := by
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  exact ((hgen x hxU g).mp hg).1

/-- Invertibility likewise forces every divisor-ideal member to be
holomorphic. -/
theorem GermIdeal.IsInvertible.holomorphicAt_mem {𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsInvertible) {x : M} {g : M → ℂ} (hg : 𝔟.mem x g) :
    HolomorphicAt n g x := by
  obtain ⟨U, hU, hxU, q, hq, hnon, hgen⟩ := h𝔟 x
  exact ((hgen x hxU g).mp hg).1

end Pullback

end

end Hironaka.RelativePrincipalizationSpan
