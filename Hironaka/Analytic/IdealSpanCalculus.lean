import Hironaka.Analytic.HolomorphicGermAlgebra

set_option autoImplicit false

/-!
# Local span algebra for relative principalization

The relative-principalization theorem has two logically distinct parts.  The
existence of an adapted analytic principalization is the Hironaka statement
(`RelativePrincipalization.exists_factorizationData`, proved in place from the canonical resolution invariant).  Once
one has a factorization by an invertible ideal whose zero locus avoids the
strict transform, the comparison of the two restricted ideal spans is local
algebra: a local generator is a unit along the strict transform and can be
cancelled.  This file records the elementary span and unit lemmas needed for
that second step, without asserting the principalization itself.
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

section Unit

variable {x : M} {𝔟 : GermIdeal n M}

/-- At a point outside the zero locus of an invertible ideal, a local principal
generator is nonzero at that point.  This is the local unit needed to cancel
the factor disjoint from the strict transform. -/
theorem GermIdeal.IsInvertible.exists_holomorphicAt_generator_ne_zero
    (h𝔟 : 𝔟.IsInvertible) (hx : x ∉ 𝔟.zeroLocus) :
    ∃ q : M → ℂ, HolomorphicAt n q x ∧ q x ≠ 0 ∧
      ∀ g, 𝔟.mem x g ↔ IsInSpanAt (n := n) (fun s => s = q) x g := by
  obtain ⟨U, hU, hxU, q, hq, _, hgen⟩ := h𝔟 x
  refine ⟨q, ?_, ?_, hgen x hxU⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hq y hy).mdifferentiableAt (hU.mem_nhds hy)
  · intro hqx
    apply hx
    intro g hg
    obtain ⟨_, N, s, a, hs, _, hsum⟩ := (hgen x hxU g).mp hg
    rw [hsum.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _
    rw [hs i, hqx, mul_zero]

/-- The preceding local unit can be chosen at every point of a set disjoint
from an effective divisor's support. -/
theorem EffectiveDivisor.exists_holomorphicAt_generator_ne_zero
    (D : EffectiveDivisor n M) {W : Set M} (hW : Disjoint D.support W)
    {x : M} (hx : x ∈ W) :
    ∃ q : M → ℂ, HolomorphicAt n q x ∧ q x ≠ 0 ∧
      ∀ g, D.ideal.mem x g ↔ IsInSpanAt (n := n) (fun s => s = q) x g := by
  apply GermIdeal.IsInvertible.exists_holomorphicAt_generator_ne_zero D.isInvertible
  intro hxD
  exact (Set.disjoint_left.mp hW) hxD hx

end Unit

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

section Factorization

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [IsComplexManifold n M] {f : Y → M} {W : Set Y} {𝔞 : GermIdeal n M}
  {H H' : EffectiveDivisor n Y} {y : Y}

/-- The restricted span comparison in relative principalization is a formal
consequence of a coherent pullback factorization once the second divisor avoids
the subset.  It does not require the existence of the adapted blowup sequence:
that is the separate Hironaka statement `RelativePrincipalization.exists_factorizationData`. -/
theorem isInSpanOnAt_pullback_iff_divisor_of_factorization
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (h𝔞 : 𝔞.IsCoherent)
    (hfactor : GermIdeal.pullback (m := n) f 𝔞 = H.ideal.mul H'.ideal)
    (hdisjoint : Disjoint H'.support W) (hy : y ∈ W) {g : Y → ℂ} :
    (IsInSpanOnAt (n := n) W
        (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y g ↔
      IsInSpanOnAt (n := n) W (H.ideal.mem y) y g) := by
  let A : (Y → ℂ) → Prop := fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f
  let B : (Y → ℂ) → Prop := H.ideal.mem y
  let P : (Y → ℂ) → Prop := fun s => ∃ h b,
    H.ideal.mem y h ∧ H'.ideal.mem y b ∧ s = h * b
  obtain ⟨q, hq, hq0, hgen⟩ :=
    EffectiveDivisor.exists_holomorphicAt_generator_ne_zero H' hdisjoint hy
  have hqmem : H'.ideal.mem y q := by
    apply (hgen q).mpr
    exact isInSpanAt_of_eq_mul rfl hq (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)
  have hBtoA : ∀ h, B h → IsInSpanOnAt (n := n) W A y h := by
    intro h hh
    have hhhol : HolomorphicAt n h y :=
      GermIdeal.IsInvertible.holomorphicAt_mem H.isInvertible hh
    have hprodmem : (H.ideal.mul H'.ideal).mem y (fun z => h z * q z) := by
      change IsInSpanAt (n := n)
        (fun s => ∃ h' b, H.ideal.mem y h' ∧ H'.ideal.mem y b ∧ s = h' * b)
        y (fun z => h z * q z)
      refine isInSpanAt_of_eq_mul ⟨h, q, hh, hqmem, rfl⟩ (hhhol.mul hq)
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)
    have hpullmem : (GermIdeal.pullback (m := n) f 𝔞).mem y (fun z => h z * q z) := by
      rw [hfactor]
      exact hprodmem
    have hpullspan : IsInSpanAt (n := n) A y (fun z => h z * q z) :=
      GermIdeal.mem_pullback_iff.mp hpullmem
    exact IsInSpanOnAt.cancel_right_of_holomorphicAt_ne_zero hq hq0
      (IsInSpanAt.restrict hpullspan)
  have hAtoB : ∀ s, A s → IsInSpanOnAt (n := n) W B y s := by
    rintro s ⟨a, ha, rfl⟩
    have hahol : HolomorphicAt n a (f y) :=
      GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha
    have hsHol : HolomorphicAt n (a ∘ f) y :=
      hahol.comp_contMDiff (Eventually.of_forall fun z => hf.contMDiffAt)
    have hpullmem : (GermIdeal.pullback (m := n) f 𝔞).mem y (a ∘ f) := by
      apply GermIdeal.mem_pullback_iff.mpr
      exact isInSpanAt_of_eq_mul ⟨a, ha, rfl⟩ hsHol (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp)
    have hprodmem : (H.ideal.mul H'.ideal).mem y (a ∘ f) := by
      rw [← hfactor]
      exact hpullmem
    have hprodspan : IsInSpanAt (n := n) P y (a ∘ f) := by
      simpa only [P, GermIdeal.mul] using hprodmem
    have hPtoB : ∀ p, P p → IsInSpanAt (n := n) B y p := by
      rintro p ⟨h, b, hh, hb, rfl⟩
      have hhhol : HolomorphicAt n h y :=
        GermIdeal.IsInvertible.holomorphicAt_mem H.isInvertible hh
      have hbhol : HolomorphicAt n b y :=
        GermIdeal.IsInvertible.holomorphicAt_mem H'.isInvertible hb
      obtain ⟨_, c, hc, hbeq⟩ :=
        isInSpanAt_eq_iff.mp ((hgen b).mp hb)
      refine isInSpanAt_of_eq_mul hh (hhhol.mul hbhol) (hc.mul hq) ?_
      filter_upwards [hbeq] with z hz
      change h z * b z = c z * q z * h z
      rw [hz]
      ring
    exact IsInSpanAt.restrict (IsInSpanAt.trans hPtoB hprodspan)
  constructor
  · exact fun hg => IsInSpanOnAt.trans hAtoB hg
  · exact fun hg => IsInSpanOnAt.trans hBtoA hg

end Factorization

end

end Hironaka.RelativePrincipalizationSpan
