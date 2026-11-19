import Hironaka.Analytic.SingularLocus

set_option autoImplicit false

/-!
# Hypotheses of the analytic gluing argument

Source: Copy-4, `prop:gluing`, `prop:principalization` and `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:gluing`,
`ana:principalization-data`, `ana:local-gluing-data`.

New definitions of this first pass (recorded in the blueprint):

* `ThetaPlurisubharmonicOn θ u Ω` and `IsThetaPshPotentialOn θ u Ω`: the existing
  chartwise theta-PSH criterion and local nondegeneracy, tested only at points of
  the set `Ω`.
* `IsKahlerCurrentPotential θ u`: `θ + ddᶜ u` dominates a Kähler form on the whole
  manifold, i.e. it is a Kähler current.
* `DominatesKahlerFormOn θ u Ω`: `θ + ddᶜ u ≥ ω'` on `Ω` for a Kähler form `ω'`
  of the manifold.  The manuscript asks for a Kähler form on a neighbourhood;
  on a compact Kähler manifold, whenever the neighbourhood may be shrunk around
  a compact set (as in both uses below), a Kähler form on the neighbourhood
  dominates `δ ω` for a global Kähler form `ω` on a smaller neighbourhood, so the
  existential statements are unchanged.
* `GluingHypotheses θ U₁ U₂ p φ_G φ_U`: hypotheses (i)–(iii) of `prop:gluing`.
* `PrincipalizationGluingConclusions θ W y U φ_G φ_U`: conclusions (1)–(3) of
  `prop:principalization`.
* `RelCompactSubset A B`: `A ⋐ B`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticGluingData

noncomputable section

open PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The theta-PSH criterion tested at chart points lying over `Ω`. -/
def ThetaPlurisubharmonicOn (θ : SmoothRealForm n M 2) (u : M → EReal) (Ω : Set M) :
    Prop :=
  ∀ e z, z ∈ e.val.target → e.val.symm z ∈ Ω →
    ∃ W ρ, z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) W

/-- A theta-PSH potential on `Ω`: theta-PSH over `Ω` and not identically `-∞` on
any neighbourhood of a point of `Ω`. -/
def IsThetaPshPotentialOn (θ : SmoothRealForm n M 2) (u : M → EReal) (Ω : Set M) :
    Prop :=
  ThetaPlurisubharmonicOn θ u Ω ∧
    ∀ x ∈ Ω, ∀ U : Set M, IsOpen U → x ∈ U → ∃ y ∈ U, u y ≠ ⊥

/-- `θ + ddᶜ u` is a Kähler current. -/
def IsKahlerCurrentPotential (θ : ClosedRealOneOneForm n M) (u : M → EReal) : Prop :=
  ∃ omega' : KahlerBackground n M, IsThetaPshPotential (θ - omega'.form).val u

/-- `θ + ddᶜ u` dominates a Kähler form on `Ω`. -/
def DominatesKahlerFormOn (θ : ClosedRealOneOneForm n M) (u : M → EReal) (Ω : Set M) :
    Prop :=
  ∃ omega' : KahlerBackground n M, IsThetaPshPotentialOn (θ - omega'.form).val u Ω

/-- `A ⋐ B`. -/
def RelCompactSubset (A B : Set M) : Prop :=
  IsCompact (closure A) ∧ closure A ⊆ B

/-- Hypotheses (i)–(iii) of the gluing proposition, for open sets `U₁ ⋐ U₂`
and a point `p ∈ U₁`. -/
def GluingHypotheses (θ : ClosedRealOneOneForm n M) (U₁ U₂ : Set M) (p : M)
    (φG φU : M → EReal) : Prop :=
  (IsKahlerCurrentPotential θ φG ∧ φG p = ⊥) ∧
    ((∃ Ω : Set M, IsOpen Ω ∧ closure U₂ ⊆ Ω ∧ DominatesKahlerFormOn θ φU Ω) ∧
      IsSmoothNear (n := n) φU p) ∧
    ∃ C : ℝ, ∀ y ∈ closure U₂ \ U₁, φU y ≤ φG y + (C : EReal)

/-- Conclusions (1)–(3) of the principalization proposition, for the strict
transform `W`, a point `y ∈ W` and an open neighbourhood `U` of `W`. -/
def PrincipalizationGluingConclusions (θ : ClosedRealOneOneForm n M) (W : Set M)
    (y : M) (U : Set M) (φG φU : M → EReal) : Prop :=
  (IsKahlerCurrentPotential θ φG ∧ ∀ w ∈ W, φG w = ⊥) ∧
    (DominatesKahlerFormOn θ φU U ∧ IsSmoothNear (n := n) φU y) ∧
    ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
      ∃ C : ℝ, ∀ z ∈ Λ, φU z ≤ φG z + (C : EReal)

end

end Hironaka.AnalyticGluingData
