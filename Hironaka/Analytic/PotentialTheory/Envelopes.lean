import Hironaka.Analytic.ThetaPshEnvelopes

/-!
# Compatibility wrappers for analytic properties of the actual envelopes

These three statements are now exact wrappers around proofs in the checked
core. They concern the concrete supremum and regularization and do not define pseudoeffectivity
or assume an abstract envelope operator. Compactness, a nonempty manifold,
closedness, type (1,1), local potentials and nonempty theta-PSH potentials are
explicit in the signatures. `IsComplexManifold` includes Hausdorffness,
second-countability and holomorphic chart compatibility. Its model is the
concrete finite-dimensional Euclidean complex space with compatible real
scalars. No ambient measure is a parameter of these disc-based statements,
so no unmentioned Borel or Haar structure on the manifold is needed.

The proofs use locally bounded PSH supremum regularization, change of smooth
local potential, and normalization by a finite upper bound on a compact
manifold. Nothing here asserts non-pluripolar mass preservation.
-/

open Set

namespace Hironaka

open Hironaka

/-- The pointwise supremum V_theta is already a genuine
theta-PSH potential; in particular its regularization does not change it.
Existence of a potential replaces any undefined pseudoeffectivity assumption. -/
theorem _root_.Hironaka.PotentialTheory.Envelopes.thetaPshSupremum_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (hne : ∃ u, IsThetaPshPotential θ u) :
    IsThetaPshPotential θ (thetaPshSupremum θ) := by
  exact _root_.Hironaka.thetaPshSupremum_isThetaPshPotential θ hclosed h11 hlocal hne

/-- Canonical minimal singularities: every theta-PSH potential
is more singular than the actual pointwise supremum V_theta. -/
theorem _root_.Hironaka.PotentialTheory.Envelopes.thetaPshSupremum_minimalSingularities
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (hne : ∃ u, IsThetaPshPotential θ u)
    (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    MoreSingularOn u (thetaPshSupremum θ) univ := by
  exact _root_.Hironaka.thetaPshSupremum_minimalSingularities
    θ hclosed h11 hlocal hne u hu

/-- The singularity-type envelope of an actual theta-PSH
potential is again a theta-PSH potential. It need not have the same additive
singularity type as its reference potential. -/
theorem _root_.Hironaka.PotentialTheory.Envelopes.singularityEnvelope_isThetaPshPotential
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [Nonempty M]
    (θ : SmoothRealForm n M 2) (hclosed : θ.IsClosed) (h11 : θ.IsTypeOneOne)
    (hlocal : HasSmoothLocalPotentials θ) (φ : M → EReal) (hφ : IsThetaPshPotential θ φ) :
    IsThetaPshPotential θ (singularityEnvelope θ φ) := by
  exact _root_.Hironaka.singularityEnvelope_isThetaPshPotential
    θ hclosed h11 hlocal φ hφ

end Hironaka
