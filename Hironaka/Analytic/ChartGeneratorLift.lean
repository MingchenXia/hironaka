import Hironaka.Analytic.BergmanGeneratorFrameChange

/-!
# Lifting finite coordinate generators to a chart domain

A finite family of holomorphic coordinate functions can be read as ambient
functions by precomposing it with one actual chart.  The resulting functions
are only asserted to be holomorphic on that chart's inverse image of the
coordinate domain; their arbitrary values away from the chart source are never
used.  This supplies the regularity and exact logarithmic identity required by
local finite-generator descent.

No overlap frame comparison is constructed here.  In particular, a finite
Bergman atlas supplies local coordinate families, but needs separate data to
identify their germ spans on chart overlaps.
-/

set_option autoImplicit false

open Set
open scoped Manifold Topology

namespace Hironaka.ChartGeneratorLift



noncomputable section

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The manifold domain lying over the coordinate set `W`. -/
def domain (e : ComplexChart n M) (W : Set (ComplexModel n)) : Set M :=
  e.val.source ∩ e.val ⁻¹' W

/-- Regard a coordinate generator as a total ambient function by composing
with the chart.  Only its restriction to `domain e W` is used below. -/
def generator (e : ComplexChart n M) (F : Fin N → ComplexModel n → ℂ) :
    Fin N → M → ℂ :=
  fun i => F i ∘ e.val

omit [IsComplexManifold n M] in
/-- The inverse image of an open coordinate domain is open in the chart source. -/
theorem isOpen_domain (e : ComplexChart n M) {W : Set (ComplexModel n)}
    (hW : IsOpen W) : IsOpen (domain e W) :=
  e.val.isOpen_inter_preimage hW

/-- Coordinate differentiability transfers to manifold differentiability on
the part of the chart source which maps into the coordinate domain. -/
theorem generator_mdifferentiableOn (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (F : Fin N → ComplexModel n → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) W) :
    ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (generator e F i)
      (domain e W) := by
  intro i
  have he : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      e.val e.val.source :=
    (contMDiffOn_of_mem_maximalAtlas (n := 1)
      (IsManifold.subset_maximalAtlas e.property)).mdifferentiableOn (by simp)
  exact (hF i).mdifferentiableOn.comp (he.mono inter_subset_left) fun x hx => hx.2

/-- The same lift applies directly to coordinate families presented as
holomorphic on neighborhoods of the coordinate domain. -/
theorem generator_mdifferentiableOn_of_analyticOnNhd (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (F : Fin N → ComplexModel n → ℂ)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) W) :
    ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (generator e F i)
      (domain e W) :=
  generator_mdifferentiableOn e W F fun i => (hF i).differentiableOn

omit [IsComplexManifold n M] in
/-- Evaluating the lifted family at an ambient point gives exactly the
coordinate generator logarithm at its chart image. -/
theorem generatorLog_apply (e : ComplexChart n M)
    (F : Fin N → ComplexModel n → ℂ) (x : M) :
    generatorLog (generator e F) x = generatorLog F (e.val x) :=
  rfl

omit [IsComplexManifold n M] in
/-- On the actual chart target, pulling the lifted family back through the
chart inverse recovers the original coordinate family exactly. -/
theorem generatorLog_chartSymm_apply (e : ComplexChart n M)
    (F : Fin N → ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    generatorLog (fun i => fun y => generator e F i (e.val.symm y)) z =
      generatorLog F z := by
  apply BergmanGeneratorFrameChange.generatorLog_congr_at
  intro i
  simp only [generator, Function.comp_apply]
  rw [e.val.right_inv hz]

/-- The exact local bridge packaged as one existential statement.  A caller
with `W ⊆ e.target` may use the final equality on every point of `W`; no
claim about another chart's generators or their overlap span is made. -/
theorem exists_globalGenerators_of_coordinateDifferentiable
    (e : ComplexChart n M) (W : Set (ComplexModel n))
    (hWtarget : W ⊆ e.val.target) (F : Fin N → ComplexModel n → ℂ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) W) :
    ∃ G : Fin N → M → ℂ,
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) (domain e W)) ∧
      (∀ x : M, generatorLog G x = generatorLog F (e.val x)) ∧
      ∀ z ∈ W, generatorLog (fun i => fun y => G i (e.val.symm y)) z = generatorLog F z := by
  refine ⟨generator e F, generator_mdifferentiableOn e W F hF,
    generatorLog_apply e F, ?_⟩
  intro z hz
  exact generatorLog_chartSymm_apply e F (hWtarget hz)

end

end Hironaka.ChartGeneratorLift
