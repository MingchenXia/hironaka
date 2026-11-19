import Hironaka.Analytic.FiniteRegularizedMaxCoreCover
import Hironaka.Analytic.FiniteShiftedBergmanCollarGluing
import Hironaka.Analytic.ShiftedBergmanBranch

set_option autoImplicit false

/-!
# Strict finite regularized-max collar data from raw Bergman comparisons

The regularized maximum needs a full scale `δ` on *both* halves of the
collar comparison.  This module records the exact endpoint-safe algebra which
turns unshifted Bergman comparisons for the actual regularized-max predecessor
into `RegularizedMaxCoreData` when a prescribed branch shift lies in the
strict interval

`Cminus + δ ≤ offset` and `offset + Cplus + δ ≤ 0`.

The two raw comparisons and the two strict interval inequalities remain
arguments of the constructor.  In particular, this makes no claim that the
weighted Bergman estimates select compatible shifts on their own.
-/

open Set
open scoped Topology

namespace Hironaka.FiniteRegularizedMaxBergmanCoreData


open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open FiniteRegularizedMaxCollarGluing
open FiniteRegularizedMaxCoreCover
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A raw predecessor-to-unshifted-branch comparison gains the strict core
gap after a sufficiently large prescribed real shift. -/
theorem predecessor_add_delta_le_shiftedBergmanBranch_of_rawCoreLower
    {p b : EReal} {Cminus offset δ : ℝ}
    (h_lower : p ≤ b + (Cminus : EReal))
    (hCminus_delta_offset : Cminus + δ ≤ offset) :
    p + (δ : EReal) ≤ b + (offset : EReal) := by
  calc
    p + (δ : EReal) ≤ (b + (Cminus : EReal)) + (δ : EReal) :=
      add_le_add h_lower le_rfl
    _ = b + ((Cminus + δ : ℝ) : EReal) := by
      rw [EReal.coe_add, add_assoc]
    _ ≤ b + (offset : EReal) :=
      add_le_add le_rfl (EReal.coe_le_coe hCminus_delta_offset)

/-- A raw unshifted collar-upper comparison gains the strict regularized-max
gap after a sufficiently small prescribed real shift. -/
theorem shiftedBergmanBranch_add_delta_le_predecessor_of_unshiftedRawCollarUpper
    {p b : EReal} {offset Cplus δ : ℝ}
    (h_unshifted_upper : b ≤ p + (Cplus : EReal))
    (hoffset_Cplus_delta : offset + Cplus + δ ≤ 0) :
    (b + (offset : EReal)) + (δ : EReal) ≤ p := by
  have hsum : Cplus + offset + δ ≤ 0 := by
    linarith
  calc
    (b + (offset : EReal)) + (δ : EReal) ≤
        (p + (Cplus : EReal) + (offset : EReal)) + (δ : EReal) :=
      add_le_add (add_le_add h_unshifted_upper le_rfl) le_rfl
    _ = p + ((Cplus + offset + δ : ℝ) : EReal) := by
      rw [EReal.coe_add, EReal.coe_add]
      ac_rfl
    _ ≤ p + 0 := add_le_add le_rfl (EReal.coe_le_coe hsum)
    _ = p := add_zero p

/-- Explicit raw core and collar comparisons for the actual finite
regularized-max recursion construct its strict core data when the fixed shifts
retain one full `δ` of room at both ends.  This is the regularized-max analogue
of the offset-interval constructor for ordinary shifted Bergman gluing. -/
noncomputable def regularizedMaxCoreData_of_offset_interval_unshifted_comparisons
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (δ : ℝ)
    (offset : Fin A.count → ℝ) (g : M → EReal)
    (inner : Fin A.count → Set M)
    (hinner_open : ∀ i, IsOpen (inner i))
    (hclosure : ∀ i, closure (inner i) ⊆ (A.patch i).patch.source)
    (Cminus Cplus : Fin A.count → ℝ)
    (h_lower : ∀ i, ∀ x ∈ inner i,
      finiteRegularizedMaxGlued δ
          (fun j => ((A.patch j).patch.source : Set M))
          (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g i.val x ≤
        bergmanBranch (A.patch i).patch x + (Cminus i : EReal))
    (h_unshifted_upper : ∀ i, ∀ x ∈ ((A.patch i).patch.source : Set M) \ inner i,
      bergmanBranch (A.patch i).patch x ≤
        finiteRegularizedMaxGlued δ
          (fun j => ((A.patch j).patch.source : Set M))
          (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g i.val x +
          (Cplus i : EReal))
    (hCminus_delta_offset : ∀ i, Cminus i + δ ≤ offset i)
    (hoffset_Cplus_delta : ∀ i, offset i + Cplus i + δ ≤ 0) :
    RegularizedMaxCoreData δ
      (fun j => ((A.patch j).patch.source : Set M))
      (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g := by
  refine {
    source_open := fun i => (A.patch i).patch.source.isOpen
    inner := inner
    closure_inner_subset := hclosure
    gap := ?_
    inner_open := hinner_open
    core := ?_ }
  · intro i x hx
    change (bergmanBranch (A.patch i).patch x + (offset i : EReal)) +
      (δ : EReal) ≤
      finiteRegularizedMaxGlued δ
        (fun j => ((A.patch j).patch.source : Set M))
        (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g i.val x
    exact shiftedBergmanBranch_add_delta_le_predecessor_of_unshiftedRawCollarUpper
      (h_unshifted_upper i x hx) (hoffset_Cplus_delta i)
  · intro i x hx
    change finiteRegularizedMaxGlued δ
        (fun j => ((A.patch j).patch.source : Set M))
        (fun j => shiftedBergmanBranch (A.patch j).patch (offset j)) g i.val x +
        (δ : EReal) ≤
      bergmanBranch (A.patch i).patch x + (offset i : EReal)
    exact predecessor_add_delta_le_shiftedBergmanBranch_of_rawCoreLower
      (h_lower i x hx) (hCminus_delta_offset i)

end

end Hironaka.FiniteRegularizedMaxBergmanCoreData
