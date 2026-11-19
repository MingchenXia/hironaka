import Hironaka.Analytic.FiniteRegularizedMaxBergmanCoreData

set_option autoImplicit false

/-!
# Feasible offsets for strict finite regularized-max Bergman gluing

For the strict regularized maximum, the chosen shift must retain a full scale
`δ` at both ends of the raw-comparison interval.  If the comparison constants
are externally fixed and satisfy

`Cminus + Cplus + 2 * δ ≤ 0`,

then the explicit choice `offset = Cminus + δ` is feasible.  The construction
below applies this numerical observation only after the two raw comparisons
for that actual shifted recursion have been supplied.  It makes no claim that
the Bergman estimates establish either the feasibility inequality or those
self-dependent raw comparisons.
-/

open Set
open scoped Topology

namespace Hironaka.FiniteRegularizedMaxBergmanOffsetFeasibility


open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open FiniteRegularizedMaxBergmanCoreData
open FiniteRegularizedMaxCollarGluing
open FiniteRegularizedMaxCoreCover
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A pointwise feasibility margin of two copies of `δ` selects the strict
offset interval explicitly.  The comparison constants are inputs: this is only
the finite-dimensional arithmetic needed after they have been supplied. -/
theorem exists_strict_offset_family_of_feasible_sum
    {N : ℕ} (Cminus Cplus : Fin N → ℝ) (δ : ℝ)
    (hfeasible : ∀ i, Cminus i + Cplus i + 2 * δ ≤ 0) :
    ∃ offset : Fin N → ℝ, ∀ i,
      Cminus i + δ ≤ offset i ∧ offset i + Cplus i + δ ≤ 0 := by
  refine ⟨fun i => Cminus i + δ, ?_⟩
  intro i
  constructor
  · exact le_rfl
  · linarith [hfeasible i]

/-- A selected strict offset interval together with the regularized-max core
data built from its shifted Bergman branches. -/
structure FeasibleRegularizedMaxCoreData
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (δ : ℝ) (g : M → EReal)
    (Cminus Cplus : Fin A.count → ℝ) where
  offset : Fin A.count → ℝ
  strict_offset : ∀ i, Cminus i + δ ≤ offset i ∧ offset i + Cplus i + δ ≤ 0
  core : RegularizedMaxCoreData δ
    (fun j => ((A.patch j).patch.source : Set M))
    (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g

/-- Once the raw comparisons have been established for the explicit actual
recursion with offsets `Cminus + δ`, the feasibility margin supplies both
strict interval inequalities and hence the existing regularized-max core data.
The hypotheses deliberately do not claim that the raw estimates are invariant
under this choice of offsets. -/
noncomputable def regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (δ : ℝ) (g : M → EReal)
    (inner : Fin A.count → Set M)
    (hinner_open : ∀ i, IsOpen (inner i))
    (hclosure : ∀ i, closure (inner i) ⊆ (A.patch i).patch.source)
    (Cminus Cplus : Fin A.count → ℝ)
    (hfeasible : ∀ i, Cminus i + Cplus i + 2 * δ ≤ 0)
    (h_lower : ∀ i, ∀ x ∈ inner i,
      finiteRegularizedMaxGlued δ
          (fun j => ((A.patch j).patch.source : Set M))
          (fun j => shiftedBergmanBranch (A.patch j).patch (Cminus j + δ)) g i.val x ≤
        bergmanBranch (A.patch i).patch x + (Cminus i : EReal))
    (h_unshifted_upper : ∀ i, ∀ x ∈ ((A.patch i).patch.source : Set M) \ inner i,
      bergmanBranch (A.patch i).patch x ≤
        finiteRegularizedMaxGlued δ
          (fun j => ((A.patch j).patch.source : Set M))
          (fun j => shiftedBergmanBranch (A.patch j).patch (Cminus j + δ)) g i.val x +
          (Cplus i : EReal)) :
    FeasibleRegularizedMaxCoreData A δ g Cminus Cplus := by
  refine {
    offset := fun i => Cminus i + δ
    strict_offset := ?_
    core := ?_ }
  · intro i
    constructor
    · exact le_rfl
    · linarith [hfeasible i]
  · exact regularizedMaxCoreData_of_offset_interval_unshifted_comparisons
      A δ (fun i => Cminus i + δ) g inner hinner_open hclosure Cminus Cplus
      h_lower h_unshifted_upper (fun _ => le_rfl)
      (fun i => by linarith [hfeasible i])

end

end Hironaka.FiniteRegularizedMaxBergmanOffsetFeasibility
