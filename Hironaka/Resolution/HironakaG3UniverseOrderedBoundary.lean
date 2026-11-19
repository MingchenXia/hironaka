import Hironaka.Resolution.HironakaG3UniverseCoordinateTransport
import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Hironaka.Blowup.NormalCrossingsInvariance
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseOrderedBoundary
open BlowupTowers NormalCrossings HironakaG3UniverseChartTransport
  HironakaG3UniverseCoordinateTransport NormalCrossingsInvariance
noncomputable section

/-- Ordered SNC boundary data transfer along the actual transported atlas. -/
theorem transported_list_snc {n : ℕ} (X : CMfd.{u} n) {Y : Type v} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsSNCDivisor n (E.map (e.symm ⁻¹' ·)) := by
  let : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  let : IsComplexManifold n Y := transported_complex_manifold e
  refine ⟨?_,?_⟩
  · intro H hH
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hH
    exact (hE.1 A hA).preimage e.symm.continuous
  · intro y
    obtain ⟨S,hcoord,hcard,hinj⟩ := hE.2 (e.symm y)
    have hc := transported_coordinate_family e (fun i : Fin E.length => E.get i) S y hcoord
    let ix : Fin (E.map (e.symm ⁻¹' ·)).length → Fin E.length :=
      fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
    have hget : ∀ i, (E.map (e.symm ⁻¹' ·)).get i = e.symm ⁻¹' E.get (ix i) := by
      intro i
      simp only [List.get_eq_getElem,List.getElem_map]
      rfl
    have hix : Function.Injective ix := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun l : Fin E.length => l.val) hij
    refine ⟨S ∘ ix, IsCoordinateFamilyAt.reindex hc ix hget (fun _ => rfl),?_,?_⟩
    · intro i hi
      exact hcard (ix i) (by change y ∈ e.symm ⁻¹' E.get (ix i); rw [← hget i]; exact hi)
    · intro i hi j hj hij
      apply hix
      apply hinj
      · change y ∈ e.symm ⁻¹' E.get (ix i)
        rw [← hget i]; exact hi
      · change y ∈ e.symm ⁻¹' E.get (ix j)
        rw [← hget j]; exact hj
      · exact hij

/-- Ordered carrier transversality transfers with the same coordinate witnesses. -/
theorem transported_list_transverse {n : ℕ} (X : CMfd.{u} n) {Y : Type v} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (N : Set X) (E : List (Set X)) (hN : IsTransverse n N E) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    IsTransverse n (e.symm ⁻¹' N) (E.map (e.symm ⁻¹' ·)) := by
  let : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  let : IsComplexManifold n Y := transported_complex_manifold e
  intro y hy
  obtain ⟨S₀,S,hcoord,hcard⟩ := hN (e.symm y) hy
  have hc := transported_coordinate_family e (fun o : Option (Fin E.length) => o.elim N fun i => E.get i)
    (fun o => o.elim S₀ S) y hcoord
  let ix : Fin (E.map (e.symm ⁻¹' ·)).length → Fin E.length :=
    fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hget : ∀ i, (E.map (e.symm ⁻¹' ·)).get i = e.symm ⁻¹' E.get (ix i) := by
    intro i
    simp only [List.get_eq_getElem,List.getElem_map]
    rfl
  refine ⟨S₀,S ∘ ix,IsCoordinateFamilyAt.reindex hc (Option.map ix) ?_ ?_,?_⟩
  · intro o
    cases o with
    | none => rfl
    | some i => exact hget i
  · intro o
    cases o <;> rfl
  · intro i hi
    exact hcard (ix i) (by change y ∈ e.symm ⁻¹' E.get (ix i); rw [← hget i]; exact hi)

end
end Hironaka.HironakaG3UniverseOrderedBoundary
