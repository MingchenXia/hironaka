import Hironaka.Resolution.HironakaG3UniverseCarrierGeometry
import Hironaka.Blowup.NormalCrossingsInvariance
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseNormalCrossings
open BlowupTowers NormalCrossings HironakaG3UniverseChartTransport
  HironakaActualIndexedBoundaryContinuation HironakaG3UniverseCarrierGeometry
  NormalCrossingsInvariance
noncomputable section

/-- Normal crossings with an ordered list transport through the literal copied atlas. -/
theorem transported_list_normalCrossings {n : ℕ} (X : CMfd.{u} n) {Y : Type v}
    [TopologicalSpace Y] (e : X ≃ₜ Y) (C : Set X) (E : List (Set X))
    (hC : HasNormalCrossings n C E) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    HasNormalCrossings n (e.symm ⁻¹' C) (E.map (e.symm ⁻¹' ·)) := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  have hIndexed : HasNormalCrossingsWithBoundary C (fun i : Fin E.length => E.get i) := hC
  have ht := transported_normalCrossings X e C (fun i : Fin E.length => E.get i) hIndexed
  intro y hy
  obtain ⟨S₀,S,hcoord,hcard⟩ := ht y hy
  let ix : Fin (E.map (e.symm ⁻¹' ·)).length → Fin E.length :=
    fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hget : ∀ i, (E.map (e.symm ⁻¹' ·)).get i = e.symm ⁻¹' E.get (ix i) := by
    intro i
    simp only [List.get_eq_getElem,List.getElem_map]
    rfl
  refine ⟨S₀,S ∘ ix,IsCoordinateFamilyAt.reindex hcoord (Option.map ix) ?_ ?_,?_⟩
  · intro o
    cases o with
    | none => rfl
    | some i => exact hget i
  · intro o
    cases o <;> rfl
  · intro i hi
    exact hcard (ix i) (by change y ∈ e.symm ⁻¹' E.get (ix i); rw [← hget i]; exact hi)
end
end Hironaka.HironakaG3UniverseNormalCrossings
