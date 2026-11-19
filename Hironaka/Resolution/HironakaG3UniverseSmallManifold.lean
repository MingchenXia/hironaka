import Hironaka.Blowup.BlowupTowers
import Mathlib.Data.Countable.Small
set_option autoImplicit false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold
universe u
namespace Hironaka.HironakaG3UniverseSmallManifold
noncomputable section
open BlowupTowers

/-- A second-countable complex manifold has a carrier representable in Type. -/
theorem complex_manifold_small {n : ℕ} (X : CMfd.{u} n) : Small.{0} X := by
  classical
  obtain ⟨S,hS,hCover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : X => chart_source_mem_nhds (ComplexModel n) x)
  let : Countable S := hS.to_subtype
  have : Small.{0} S := inferInstance
  have : Small.{0} (ComplexModel n) := inferInstance
  have : Small.{0} (S × ComplexModel n) := inferInstance
  have hAt : ∀ x : X, ∃ q : S, x ∈ (chartAt (ComplexModel n) (q : X)).source := by
    intro x
    have hx : x ∈ ⋃ q ∈ S, (chartAt (ComplexModel n) q).source := by rw [hCover]; exact mem_univ x
    obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨q,hq⟩,hxq⟩
  choose q hq using hAt
  let f : X → S × ComplexModel n := fun x => (q x, chartAt (ComplexModel n) (q x : X) x)
  apply small_of_injective (f := f)
  intro x y hxy
  have hqxy : q x = q y := congrArg Prod.fst hxy
  have hcxy : chartAt (ComplexModel n) (q x : X) x = chartAt (ComplexModel n) (q y : X) y :=
    congrArg Prod.snd hxy
  have hy : y ∈ (chartAt (ComplexModel n) (q x : X)).source := by simpa only [hqxy] using hq y
  apply (chartAt (ComplexModel n) (q x : X)).injOn (hq x) hy
  simpa only [hqxy] using hcxy
end
end Hironaka.HironakaG3UniverseSmallManifold
