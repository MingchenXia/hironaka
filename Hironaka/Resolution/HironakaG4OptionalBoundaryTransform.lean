import Hironaka.Resolution.HironakaG4ToricSuccessorFamily

/-!
# Optional coordinate masks through a toric blowup chart

An absent boundary member is recorded by `none`; a present coordinate locus
is recorded by `some mask`. A strict transform whose mask contains the pivot
becomes absent. Already absent closed members stay absent in the chart.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalBoundaryTransform
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG4ToricSuccessorFamily

variable {n : ℕ}

def optionalCoordLocus : Option (Finset (Fin n)) → Set (ComplexModel n)
  | none => ∅
  | some S => coordSubspace S

def successorMask (σ : Fin n ≃ Fin n) (j : Fin n) :
    Option (Finset (Fin n)) → Option (Finset (Fin n))
  | none => none
  | some S => if j ∈ S.image σ then none else some (S.image σ)

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} {z : Y}
  {Φ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- A complete optional boundary dictionary transforms through the same
actual permuted monomial chart, including already absent members. -/
theorem optional_strict_family_after_permuted_chart
    (hπ : Continuous π) (hΘΦ : Θ.source ⊆ Φ.source) (σ : Fin n ≃ Fin n)
    (hperm : ∀ w i, Θ.toFun w (σ i) = Φ.toFun w i)
    {k : ℕ} (hflatC : ∀ y ∈ flatDomain Θ,
      y ∈ C ↔ flatMap Θ y ∈ complexCoordinatePlane n k)
    {ι : Type*} (D : ι → Set X) (M : ι → Option (Finset (Fin n))) (hclosed : ∀ i, IsClosed (D i))
    (hflatD : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ optionalCoordLocus (M i)))
    {j : Fin n} (hj : k ≤ j.val)
    (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hcoords : ∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Θ ∧
      monomial k j (flatMap Ψ u) = flatMap Θ (π u)) :
    ∀ u ∈ flatDomain Ψ, ∀ i, u ∈ geoStrictTransform π C (D i) ↔
      flatMap Ψ u ∈ optionalCoordLocus (successorMask σ j (M i)) := by
  intro u hu i
  cases hi : M i with
  | none =>
    have hdom := (hcoords u hu).1
    have hnot : π u ∉ D i := by
      have hh := hflatD i hdom.1 (hΘΦ hdom.2)
      simpa only [hi, optionalCoordLocus, mem_empty_iff_false, iff_false] using hh
    have hnot' : u ∉ geoStrictTransform π C (D i) := by
      intro huD
      exact hnot (geoStrictTransform_subset_preimage hπ (hclosed i) huD)
    simp [successorMask, optionalCoordLocus, hnot']
  | some S =>
    have hsingle : ∀ (_ : Unit) {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) y ∈ Φ.source →
          (y ∈ (fun _ : Unit => D i) () ↔
            Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace ((fun _ : Unit => S) ())) := by
      intro _ y hy hyΦ
      simpa only [hi, optionalCoordLocus] using hflatD i hy hyΦ
    have hfamily := permuted_strict_family_and_exceptional hΘΦ σ hperm hflatC
      (fun _ : Unit => D i) (fun _ : Unit => S) hsingle hj Ψ hΨsrc hcoords
    have heq := (hfamily u hu).1 ()
    change u ∈ geoStrictTransform π C (D i) ↔
      j ∉ S.image σ ∧ flatMap Ψ u ∈ coordSubspace (S.image σ) at heq
    by_cases hjS : j ∈ S.image σ
    · simp [successorMask, hjS, optionalCoordLocus] at heq ⊢
      exact heq
    · simpa [hi, successorMask, hjS, optionalCoordLocus] using heq

end
end Hironaka.HironakaG4OptionalBoundaryTransform
