import Hironaka.Analytic.BergmanGeneratorFrameChange
import Hironaka.Coherence.FiniteGeneratorIdealDescent

/-!
# Generator-span consequences of holomorphic frame changes

The local-generator descent theorem asks for two inclusions of finite
holomorphic generator spans at every overlap point.  This file turns concrete
holomorphic linear transition data into those inclusions.  In particular, a
nowhere-vanishing holomorphic scalar frame changes a finite family without
changing its germ span.

No compatibility is asserted here between independently chosen Bergman
presentations.  A caller must supply the actual transition equalities (on an
open overlap, or as germs) and the holomorphicity of the coefficients.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.BergmanGeneratorSpan


open Hironaka.HolomorphicIdealSheaves
open BergmanGeneratorFrameChange

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- An explicit finite holomorphic linear combination of a generator family is
in its germ span. -/
theorem isInSpanAt_of_holomorphicGeneratorExpansion
    {x : M} {p q : ℕ} (f : Fin p → M → ℂ) (g : Fin q → M → ℂ)
    (a : Fin q → Fin p → M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (ha : ∀ j i, HolomorphicAt n (a j i) x)
    (hgf : ∀ j, g j =ᶠ[𝓝 x] fun y => ∑ i, a j i y * f i y) :
    ∀ j, IsInSpanAt (n := n) (· ∈ range f) x (g j) := by
  intro j
  refine ⟨?_, p, f, a j, ?_, ha j, hgf j⟩
  · exact (HolomorphicAt.sum (Finset.univ : Finset (Fin p))
      fun i _ => (ha j i).mul (hf i)).congr (hgf j).symm
  · intro i
    exact ⟨i, rfl⟩

omit [IsComplexManifold n M] in
/-- Mutual finite holomorphic generator expansions give precisely the two
per-generator inclusions consumed by
`hasAnalyticSingularities_of_localGeneratorInclusions`. -/
theorem generatorInclusions_of_mutualHolomorphicGeneratorExpansions
    {x : M} {p q : ℕ} (f : Fin p → M → ℂ) (g : Fin q → M → ℂ)
    (a : Fin q → Fin p → M → ℂ) (b : Fin p → Fin q → M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (ha : ∀ j i, HolomorphicAt n (a j i) x)
    (hb : ∀ i j, HolomorphicAt n (b i j) x)
    (hgf : ∀ j, g j =ᶠ[𝓝 x] fun y => ∑ i, a j i y * f i y)
    (hfg : ∀ i, f i =ᶠ[𝓝 x] fun y => ∑ j, b i j y * g j y) :
    (∀ j, IsInSpanAt (n := n) (· ∈ range f) x (g j)) ∧
      ∀ i, IsInSpanAt (n := n) (· ∈ range g) x (f i) := by
  have hforward := isInSpanAt_of_holomorphicGeneratorExpansion f g a hf ha hgf
  have hg : ∀ j, HolomorphicAt n (g j) x := fun j => (hforward j).holomorphicAt
  exact ⟨hforward,
    isInSpanAt_of_holomorphicGeneratorExpansion g f b hg hb hfg⟩

omit [IsComplexManifold n M] in
/-- A nowhere-vanishing holomorphic scalar frame preserves a finite generator
span at a point.  The first inclusion uses the frame; the second uses its
holomorphic reciprocal. -/
theorem generatorInclusions_of_holomorphicFrameChange
    {x : M} {p : ℕ} (f g : Fin p → M → ℂ) (q : M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (hq : HolomorphicAt n q x) (hqx : q x ≠ 0)
    (hgf : ∀ i, g i =ᶠ[𝓝 x] fun y => q y * f i y) :
    (∀ i, IsInSpanAt (n := n) (· ∈ range f) x (g i)) ∧
      ∀ i, IsInSpanAt (n := n) (· ∈ range g) x (f i) := by
  have hforward : ∀ i, IsInSpanAt (n := n) (· ∈ range f) x (g i) := by
    intro i
    exact isInSpanAt_of_eq_mul ⟨i, rfl⟩
      ((hq.mul (hf i)).congr (hgf i).symm) hq (hgf i)
  refine ⟨hforward, ?_⟩
  intro i
  refine isInSpanAt_of_eq_mul ⟨i, rfl⟩ (hf i)
    (Hironaka.RelativePrincipalizationSpan.holomorphicAt_inv hq hqx) ?_
  filter_upwards [hgf i, hq.continuousAt.eventually_ne hqx] with y hy hyq
  rw [hy]
  calc
    f i y = 1 * f i y := (one_mul _).symm
    _ = ((q y)⁻¹ * q y) * f i y := by rw [inv_mul_cancel₀ hyq]
    _ = (q y)⁻¹ * (q y * f i y) := by ring

omit [IsComplexManifold n M] in
/-- Pointwise frame-change equations on an open overlap induce the germ
inclusions at every chosen overlap point. -/
theorem generatorInclusions_of_holomorphicFrameChangeOn
    {x : M} {p : ℕ} (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (f g : Fin p → M → ℂ) (q : M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (hq : HolomorphicAt n q x) (hqx : q x ≠ 0)
    (hgf : ∀ i y, y ∈ W → g i y = q y * f i y) :
    (∀ i, IsInSpanAt (n := n) (· ∈ range f) x (g i)) ∧
      ∀ i, IsInSpanAt (n := n) (· ∈ range g) x (f i) := by
  apply generatorInclusions_of_holomorphicFrameChange f g q hf hq hqx
  intro i
  filter_upwards [hW.mem_nhds hxW] with y hy
  exact hgf i y hy

omit [IsComplexManifold n M] in
/-- The exponential frame from `BergmanGeneratorFrameChange` is a valid span
bridge as soon as its holomorphic germ and the actual overlap equality are
provided.  Its nonvanishing is automatic. -/
theorem generatorInclusions_of_bergmanHolomorphicFrameChangeOn
    {x : M} {p : ℕ} (W : Set M) (hW : IsOpen W) (hxW : x ∈ W)
    (c : ℝ) (transition : M → ℂ) (f g : Fin p → M → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (hframe : HolomorphicAt n (holomorphicFrame c transition) x)
    (hgf : ∀ i y, y ∈ W →
      g i y = holomorphicFrame c transition y * f i y) :
    (∀ i, IsInSpanAt (n := n) (· ∈ range f) x (g i)) ∧
      ∀ i, IsInSpanAt (n := n) (· ∈ range g) x (f i) := by
  exact generatorInclusions_of_holomorphicFrameChangeOn W hW hxW f g
    (holomorphicFrame c transition) hf hframe
    (holomorphicFrame_ne_zero c transition x) hgf

end

end Hironaka.BergmanGeneratorSpan
