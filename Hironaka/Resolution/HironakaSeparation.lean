/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Coherence.CartanIrreducible
import Hironaka.MarkedIdeal.CoefficientRestrictionTower
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Separating strict transforms by principalizing `𝓘_A + 𝓘_B` (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6 (the strict transform of a
non-equidimensional space is smooth, so its parts of different dimensions end up disjoint) and Theorem 1.10
(principalization); Kollár 2007 (`kollar07-resolution`), "Principalization III" (principalization relative to a
simple normal crossings divisor).

**The separation lemma** (`disjoint_strictTransform_of_pullback_sumIdeal`).  Let `f : Y → X` be holomorphic between complex
manifolds of the same dimension, `A, B ⊆ X` closed, each the closure of its part off the other (`A ⊆ closure (A \ B)`,
`B ⊆ closure (B \ A)`), and `D` an effective divisor on `Y` with `f^*(𝓘_A + 𝓘_B) = 𝒪(-D)` and `supp D ⊆ f⁻¹(A ∩ B)`.  Then the
strict transforms of `A` and `B` are disjoint.

Proof.  Let `z` be a point of both, and `h` a local generator of `𝒪(-D)` at `z`.  Since `h` lies in the pullback ideal, it is a
holomorphic combination of germs `τ ∘ f` with `τ` a local equation of `A` or of `B` at `f z`; each `τ ∘ f` is a multiple `u_τ h`.
Hence `h = h Φ` with `Φ = Σ a_τ u_τ`, and since `h` vanishes identically on no open set, `Φ = 1` near `z`; so some `u_τ(z) ≠ 0`,
say with `τ` an equation of `A`.  Near `z`, every point over `A` is then a zero of `τ ∘ f = u_τ h`, hence of `h`, hence lies over
`A ∩ B`.  But `z` lies in the strict transform of `A`, so arbitrarily near `z` there are non-exceptional points over `A`, and since
`f` is open there and `A \ B` is dense in `A`, points over `A \ B`: a contradiction.

**The separation step** (`exists_separation`).  For analytic `A, B` (`A` with empty interior, `A ∩ B` compact) as above and a
divisor `E₀` with simple normal crossings, principalization of `𝓘_A + 𝓘_B` relative to `E₀`
(`HironakaPrincipalizationBoundary.exists_principalization_boundary`; the ideal is coherent by Cartan's theorem, nonzero at every
point, and its zero locus is `A ∩ B`, `zeroLocus_sumIdeal_vanishingIdeal`) gives an admissible sequence of `(X, E₀)` with
centres over `A ∩ B` after which the strict transforms of `A` and `B` are disjoint.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaSeparation

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence Hironaka.DivisorExponentAlong Hironaka.RestrictedIdealExtension

noncomputable section

variable {n : ℕ}

/-! ### The zero locus of a sum of vanishing ideals -/

section Ideal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The zero locus of `𝓘_A + 𝓘_B` is `A ∩ B`** (`A`, `B` closed). -/
theorem zeroLocus_sumIdeal_vanishingIdeal {A B : Set M} (hA : IsClosed A) (hB : IsClosed B) :
    (sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B)).zeroLocus = A ∩ B := by
  ext x
  constructor
  · intro hx
    have hA' : x ∈ (vanishingIdeal (n := n) A).zeroLocus := fun g hg =>
      hx g (IdealOrderArithmetic.le_sumIdeal_left' (𝔞 := vanishingIdeal (n := n) A)
        (𝔟 := vanishingIdeal (n := n) B) (fun _ _ h => h.1) x g hg)
    have hB' : x ∈ (vanishingIdeal (n := n) B).zeroLocus := fun g hg =>
      hx g (IdealOrderArithmetic.le_sumIdeal_right' (𝔞 := vanishingIdeal (n := n) A)
        (𝔟 := vanishingIdeal (n := n) B) (fun _ _ h => h.1) x g hg)
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hA] at hA'
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hB] at hB'
    exact ⟨hA', hB'⟩
  · rintro ⟨hxA, hxB⟩ g hg
    obtain ⟨-, N, s, a, hs, -, hsum⟩ := IdealOrderArithmetic.mem_sumIdeal_iff.mp hg
    rw [hsum.self_of_nhds]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hs i with h | h
    · rw [h.2.self_of_nhds hxA, mul_zero]
    · rw [h.2.self_of_nhds hxB, mul_zero]

/-- **A unit among the generators**: let `h` be holomorphic at `z`, vanishing identically on no nonempty open subset of an open
`U ∋ z`.  If `h` is a holomorphic combination of germs from `S` at `z`, each of which is a holomorphic multiple of `h`, then some
germ of `S` is a multiple `u h` with `u(z) ≠ 0`. -/
theorem exists_unit_of_isInSpanAt {U : Set M} (hU : IsOpen U) {h : M → ℂ}
    (hnon : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0) {z : M} (hzU : z ∈ U)
    {S : (M → ℂ) → Prop} (hspan : IsInSpanAt (n := n) S z h)
    (hdiv : ∀ s, S s → ∃ u, HolomorphicAt n u z ∧ s =ᶠ[𝓝 z] fun y => u y * h y) :
    ∃ s, S s ∧ ∃ u, HolomorphicAt n u z ∧ u z ≠ 0 ∧ s =ᶠ[𝓝 z] fun y => u y * h y := by
  obtain ⟨-, N, s, a, hs, ha, hsum⟩ := hspan
  choose u hu hsu using fun i => hdiv (s i) (hs i)
  set Φ : M → ℂ := fun y => ∑ i, a i y * u i y with hΦdef
  have hΦ : HolomorphicAt n Φ z := HolomorphicAt.sum _ fun i _ => (ha i).mul (hu i)
  have heq : ∀ᶠ y in 𝓝 z, h y * 1 = h y * Φ y := by
    filter_upwards [hsum, eventually_all.mpr hsu] with y hy hy'
    rw [mul_one]
    conv_lhs => rw [hy]
    rw [hΦdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy' i]
    ring
  have h1 := InvertibleIdealQuotient.eventuallyEq_of_mul_eventuallyEq hU hnon hzU (holomorphicAt_const 1) hΦ heq
  have hz1 : ∑ i, a i z * u i z ≠ 0 := by
    have h2 : Φ z = 1 := h1.self_of_nhds.symm
    change Φ z ≠ 0
    rw [h2]
    exact one_ne_zero
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz1
  exact ⟨s i, hs i, u i, hu i, right_ne_zero_of_mul hi, hsu i⟩

end Ideal

/-! ### The separation lemma -/

section Separation

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **A point near which every point over `A` lies over `B` is not in the strict transform of `A`**, when `A \ B` is dense in
`A` (`f` is open off its exceptional locus). -/
theorem notMem_strictTransform_of_eventually {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {A B : Set X} (hAB : A ⊆ closure (A \ B)) {z : Y}
    (hz : ∀ᶠ y in 𝓝 z, f y ∈ A → f y ∈ B) : z ∉ strictTransform n f A := by
  intro hzA
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp hz
  obtain ⟨y, hyV, hyA, hyE⟩ := mem_closure_iff.mp hzA V hVo hzV
  have hV' : V ∩ (exceptionalLocus n f)ᶜ ∈ 𝓝 y :=
    inter_mem (hVo.mem_nhds hyV) ((StrictTransformComposition.isOpen_compl_exceptionalLocus hf).mem_nhds hyE)
  have himg : f '' (V ∩ (exceptionalLocus n f)ᶜ) ∈ 𝓝 (f y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hf hyE]
    exact image_mem_map hV'
  obtain ⟨_, ⟨w, ⟨hwV, -⟩, rfl⟩, hwA, hwB⟩ := mem_closure_iff_nhds.mp (hAB hyA) _ himg
  exact hwB (hVsub hwV hwA)

/-- **The separation lemma**: if `f^*(𝓘_A + 𝓘_B) = 𝒪(-D)` with `supp D ⊆ f⁻¹(A ∩ B)`, and each of the closed sets `A`, `B` is the
closure of its part off the other, then the strict transforms of `A` and `B` are disjoint. -/
theorem disjoint_strictTransform_of_pullback_sumIdeal {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {A B : Set X}
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A)) (D : EffectiveDivisor n Y)
    (hD : GermIdeal.pullback (m := n) f (sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B)) = D.ideal)
    (hsupp : D.support ⊆ f ⁻¹' (A ∩ B)) :
    Disjoint (strictTransform n f A) (strictTransform n f B) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  obtain ⟨U, hU, hzU, h, hhd, hnon, hgen⟩ := D.isInvertible z
  have hh : HolomorphicAt n h z := InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hhd hzU
  have hfd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f w :=
    Eventually.of_forall fun w => (hf w).mdifferentiableAt (by simp)
  set J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B) with hJdef
  have hmem : (GermIdeal.pullback (m := n) f J).mem z h := by
    rw [hD]
    exact (hgen z hzU h).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hh)
  set S : (Y → ℂ) → Prop := fun s => ∃ τ, ((vanishingIdeal (n := n) A).mem (f z) τ ∨
    (vanishingIdeal (n := n) B).mem (f z) τ) ∧ s = τ ∘ f with hSdef
  have hspan : IsInSpanAt (n := n) S z h := by
    refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hmem)
    rintro s ⟨a, ha, rfl⟩
    exact CoefficientRestrictionTower.isInSpanAt_comp_map hfd ha
  have hdiv : ∀ s, S s → ∃ u, HolomorphicAt n u z ∧ s =ᶠ[𝓝 z] fun y => u y * h y := by
    rintro s ⟨τ, hτ, rfl⟩
    have hτhol : HolomorphicAt n τ (f z) := hτ.elim (fun h' => h'.1) (fun h' => h'.1)
    have hτJ : J.mem (f z) τ :=
      IdealOrderArithmetic.mem_sumIdeal_iff.mpr (isInSpanAt_of_eq_mul
        (S := fun s => (vanishingIdeal (n := n) A).mem (f z) s ∨ (vanishingIdeal (n := n) B).mem (f z) s) hτ hτhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    have hcomp : HolomorphicAt n (τ ∘ f) z := HadamardBridge.holomorphicAt_comp_map hfd hτhol
    have hpb : (GermIdeal.pullback (m := n) f J).mem z (τ ∘ f) :=
      RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, J.mem (f z) a ∧ s = a ∘ f) ⟨τ, hτJ, rfl⟩ hcomp)
    rw [hD] at hpb
    exact (isInSpanAt_eq_iff.mp ((hgen z hzU _).mp hpb)).2
  obtain ⟨s, ⟨τ, hτ, rfl⟩, u, hu, huz, hsu⟩ := exists_unit_of_isInSpanAt hU hnon hzU hspan hdiv
  -- near `z`, the zeros of `τ ∘ f` lie over `A ∩ B`
  have hsuppz : ∀ᶠ y in 𝓝 z, τ (f y) = 0 → f y ∈ A ∩ B := by
    filter_upwards [hU.mem_nhds hzU, hsu, hu.continuousAt.eventually_ne huz] with y hyU hy hyu hτy
    apply hsupp
    intro g hg
    obtain ⟨-, c, -, hgc⟩ := isInSpanAt_eq_iff.mp ((hgen y hyU g).mp hg)
    have hhy : h y = 0 := by
      have h0 : u y * h y = 0 := by
        have := hy
        simp only [Function.comp_apply] at this
        rw [← this]
        exact hτy
      exact (mul_eq_zero.mp h0).resolve_left hyu
    rw [hgc.self_of_nhds]
    simp [hhy]
  rcases hτ with hτA | hτB
  · refine notMem_strictTransform_of_eventually hf hAB ?_ hzA
    filter_upwards [hf.continuous.continuousAt.eventually hτA.2, hsuppz] with y h1 h2 hyA
    exact (h2 (h1 hyA)).2
  · refine notMem_strictTransform_of_eventually hf hBA ?_ hzB
    filter_upwards [hf.continuous.continuousAt.eventually hτB.2, hsuppz] with y h1 h2 hyB
    exact (h2 (h1 hyB)).1

end Separation

/-! ### The separation step -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Separation by principalization of `𝓘_A + 𝓘_B`, relative to a boundary**: let `A, B ⊆ X` be analytic, `A` with empty
interior, `A ∩ B` compact, each the closure of its part off the other, and `E₀` a divisor with simple normal crossings.  There is
an admissible blowup sequence of `(X, E₀)` with centres over `A ∩ B`, with a divisor with simple normal crossings, after which the
strict transforms of `A` and `B` are disjoint. -/
theorem exists_separation {A B : Set X} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hint : interior A = ∅) (hK : IsCompact (A ∩ B))
    (hAB : A ⊆ closure (A \ B)) (hBA : B ⊆ closure (B \ A)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (A ∩ B) X' f E ∧ IsSNCDivisor n E ∧
      Disjoint (strictTransform n f A) (strictTransform n f B) := by
  set J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B) with hJdef
  have hJ : J.IsCoherent :=
    isCoherent_sumIdeal (CartanIrreducible.cartanCoherence A hAa) (CartanIrreducible.cartanCoherence B hBa)
  have hne : ∀ x, IsNonzeroAlongAt univ J x := fun x =>
    InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left (𝔟 := vanishingIdeal (n := n) A)
      (𝔠 := vanishingIdeal (n := n) B) (fun _ _ h => h.1)
      (HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hAa hint x)
  have hZ : J.zeroLocus = A ∩ B := zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
  obtain ⟨X', i1, i2, i3, f, D, E, hadm, hsnc, hpb, -, hsupp, -⟩ :=
    HironakaPrincipalizationBoundary.exists_principalization_boundary hJ hne (by rw [hZ]; exact hK) hE₀
  rw [hZ] at hadm hsupp
  exact ⟨X', i1, i2, i3, f, E, hadm, hsnc,
    disjoint_strictTransform_of_pullback_sumIdeal hadm.isBlowupSequence.contMDiff hAB hBA D hpb hsupp.le⟩

end Step

end

end Hironaka.HironakaSeparation
