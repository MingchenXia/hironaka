import Hironaka.Analytic.LocalBergmanSmoothLogSum
import Hironaka.Analytic.PrescribedBallPotentials
import Hironaka.Analytic.WeakDbarWeyl

set_option autoImplicit false

/-!
# Finite Bergman log-sum descent data on overlaps

The finite collar recursion cannot retain the strong smooth-remainder
singularity convention across genuine overlaps: `FiniteShiftedBergmanPriorityObstruction`
shows that its local-priority cover would force a global chart on a nonempty
preconnected manifold.  This file records the different, non-max route.

On a common coordinate neighbourhood, transport each active Bergman branch to
one local potential of `θ`.  An exact holomorphic frame change makes every
branch take the form `c log Σ |fᵢ|² - ρ`.  Concatenating *all* such aligned
families gives a single finite logarithmic sum.  The remaining descent datum
asserts that these local sums are the coordinate functions of one global
potential.  It is this exact frame/cocycle datum, rather than an ordinary
maximum or a priority cover, that yields both theta-PSH and the CT22 strong
analytic-singularity conclusion.

The file proves the formal consequence of this concrete data, and proves the
local additive holomorphic transition between two smooth potentials on a
ball.  Turning that transition into a multiplicative unit in the finite
generator algebra, and proving the resulting overlap descent, remains the
global Bergman/coherent-ideal input.
-/

open Set
open scoped Topology ContDiff

namespace Hironaka.FiniteBergmanOverlapLogSumCocycle


open Hironaka.NumericalRestrictedVolumeScaffold
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open StrongAnalyticOverlapGluing
open StrongAnalyticOverlapThetaPsh
open LocalBergmanSmoothLogSum
open Metric

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite holomorphic generator family for one actual Bergman branch,
rewritten relative to a specified ambient-chart local potential.  The final
equality is the exact frame-change condition: it is stronger than bounded
equivalence and is precisely what allows this branch to participate in an
honest common log-sum. -/
def AlignedBergmanBranchPresentation
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) (c : ℝ)
    {p : ℕ} (f : Fin p → ComplexModel n → ℂ) : Prop :=
  IsSmoothLocalPotential θ e W ρ ∧
    (∀ k, DifferentiableOn ℂ (f k) W) ∧
    (∀ y ∈ W, e.val.symm y ∈ D.source) ∧
    ∀ y ∈ W, chartFunction (bergmanBranch D) e y =
      (c : EReal) * generatorLog f y - (ρ y : EReal)

/-- On a coordinate ball, two smooth local potentials for the same form have
a holomorphic additive transition after shrinking the radius by one half.
This is the analytic precursor of the nowhere-zero multiplicative frame
`exp (g / (2c))` used to align logarithmic generator families.  The conclusion
is stated as complex differentiability on the ball, which is the concrete
holomorphic condition used by the generator API. -/
theorem exists_holomorphic_additiveTransition_of_localPotentialsOnBall
    {θ : SmoothRealForm n M 2} (e : ComplexChart n M)
    {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    {ρ σ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e (ball x₀ r) ρ)
    (hσ : IsSmoothLocalPotential θ e (ball x₀ r) σ) :
    ∃ g : ComplexModel n → ℂ,
      DifferentiableOn ℂ g (ball x₀ (r / 2)) ∧
        ∀ z ∈ ball x₀ (r / 2), (g z).re = σ z - ρ z := by
  let δ : ComplexModel n → ℝ := fun z => σ z - ρ z
  have hδ : ContDiffOn ℝ ∞ δ (ball x₀ r) := hσ.2.2.1.sub hρ.2.2.1
  have hδzero : ∀ z ∈ ball x₀ r, smoothDDC δ z = 0 := by
    intro z hz
    change smoothDDC (fun y => σ y - ρ y) z = 0
    rw [PositiveClasses.smoothDDC_sub isOpen_ball hσ.2.2.1 hρ.2.2.1 hz,
      hσ.2.2.2 hz, hρ.2.2.2 hz, sub_self]
  obtain ⟨g, hg, hbar, hre⟩ :=
    PrescribedBall.exists_holomorphic_re_eq_ball hr δ hδ hδzero
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact (differentiableAt_complex_of_dbarDir_eq_zero
      (hg.differentiable (by simp) z) (hbar z hz)).differentiableWithinAt
  · intro z hz
    simpa [δ] using hre z hz

/-- The local Bergman construction supplies an aligned presentation when the
chosen common potential is its own transported potential.  Thus the alignment
predicate is inhabited before any overlap comparison; the missing step is to
align several such presentations to one potential on a genuine overlap. -/
theorem exists_alignedBergmanBranchPresentation
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (c : ℝ) (p : ℕ) (f : Fin p → ComplexModel n → ℂ),
      z ∈ W ∧ 0 < c ∧
        AlignedBergmanBranchPresentation D e W ρ c f := by
  obtain ⟨W, ρ, p, q, c, f, g, hzW, hρ, hc, hf, hg, hWsource, hrep⟩ :=
    exists_localSmoothLogSumPresentation_bergmanBranch D hm e hz hzsource
  let F : Fin (p + q) → ComplexModel n → ℂ := Fin.append f g
  have hF : ∀ k, DifferentiableOn ℂ (F k) W := by
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro l
      simpa [F] using hf l
    · intro l
      simpa [F] using hg l
  refine ⟨W, ρ, c, p + q, F, hzW, hc, hρ, hF, hWsource, ?_⟩
  intro y hy
  change chartFunction (bergmanBranch D) e y =
    (c : EReal) * generatorLog (Fin.append f g) y - (ρ y : EReal)
  simpa [smoothLogSum, sub_eq_add_neg] using hrep y hy

/-- Exact finite overlap descent for a Bergman atlas.  At each ambient-chart
point, `block` records the finite active patch branches; `reindex` identifies
their disjoint union of generator families with one finite generator family
`F`.  Every branch is expressed relative to the same local potential `ρ`, and
the final equality is the cocycle/descent equation for the proposed global
potential `w`.

No plurisubharmonicity or analytic-singularity conclusion is included in this
definition.  Its ingredients are only local potentials, holomorphic
generators, exact branch identities, finite reindexing, and exact descent. -/
def FiniteBergmanLogSumCocycle
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ) (c : ℝ)
      (r : ℕ) (p : Fin r → ℕ) (N : ℕ)
      (block : Fin r → Fin A.count)
      (f : ∀ a : Fin r, Fin (p a) → ComplexModel n → ℂ)
      (F : Fin N → ComplexModel n → ℂ)
      (reindex : Fin N ≃ (Σ a : Fin r, Fin (p a))),
      z ∈ W ∧ 0 < c ∧ 0 < r ∧
        (∀ a, AlignedBergmanBranchPresentation
          (A.patch (block a)).patch e W ρ c (f a)) ∧
        (∀ l y, F l y = f (reindex l).1 (reindex l).2 y) ∧
        ∀ y ∈ W, chartFunction w e y =
          (c : EReal) * generatorLog F y - (ρ y : EReal)

/-- Exact finite log-sum descent data produces the local common-potential
presentations required by the overlap curvature bridge.  The proof uses no
maximum and no core-priority condition; it simply installs the flattened
finite holomorphic family `F` and an empty second block. -/
theorem hasLocalSmoothLogSumPresentations_of_finiteBergmanLogSumCocycle
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m)
    (h : FiniteBergmanLogSumCocycle (w := w) A) :
    HasLocalSmoothLogSumPresentations θ w := by
  intro e z hz
  obtain ⟨W, ρ, c, r, p, N, block, f, F, reindex,
    hzW, hc, hr, haligned, hflatten, hdescent⟩ := h e z hz
  let a₀ : Fin r := ⟨0, hr⟩
  have hρ : IsSmoothLocalPotential θ e W ρ := (haligned a₀).1
  have hF : ∀ l, DifferentiableOn ℂ (F l) W := by
    intro l
    let a : Fin r := (reindex l).1
    let k : Fin (p a) := (reindex l).2
    have hFk : F l = f a k := funext fun y => hflatten l y
    rw [hFk]
    exact (haligned a).2.1 k
  refine ⟨W, ρ, N, 0, c, F, fun j : Fin 0 => j.elim0,
    hzW, hρ, hc, hF, ?_, ?_⟩
  · intro j
    exact j.elim0
  · intro y hy
    rw [smoothLogSum_append_empty]
    simpa only [sub_eq_add_neg, EReal.coe_neg] using hdescent y hy

/-- The exact finite overlap cocycle gives theta-plurisubharmonicity and the
strong smooth-remainder analytic singularities required by CT22.  The only
unproved mathematical input left by this bridge is construction of the
multiplicative frame changes in the generator algebra and their descent
equation in `FiniteBergmanLogSumCocycle`. -/
theorem thetaPsh_and_strongAnalytic_of_finiteBergmanLogSumCocycle
    {θ : SmoothRealForm n M 2} {u w : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m)
    (h : FiniteBergmanLogSumCocycle (w := w) A) :
    ThetaPlurisubharmonic θ w ∧
      HasManifoldSmoothAnalyticSingularities (n := n) w :=
  thetaPsh_and_strongAnalytic_of_localSmoothLogSumPresentations
    (hasLocalSmoothLogSumPresentations_of_finiteBergmanLogSumCocycle A h)

end

end Hironaka.FiniteBergmanOverlapLogSumCocycle
