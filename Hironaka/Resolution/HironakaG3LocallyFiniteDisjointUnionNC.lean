import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
import Hironaka.Resolution.HironakaActualIndexedBoundaryContinuation
import Hironaka.Invariant.CodimOneAdmissibleAlong
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocallyFiniteDisjointUnionNC
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualIndexedBoundaryContinuation HironakaG3IndexedSeparatedComponents

theorem locally_finite_disjoint_union_nc {n : ℕ} {Z : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set Z) (D : κ → Set Z) (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hDis : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hNC : ∀ i, HasNormalCrossingsWithBoundary (A i) D) :
    HasNormalCrossingsWithBoundary (⋃ i, A i) D := by
  intro x hx
  obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
  obtain ⟨U,hAU,hOther⟩ := exists_component_isolating_open A hClosed hLF hDis i
  obtain ⟨S₀,S,hcoord,hcard⟩ := hNC i x hxi
  refine ⟨S₀,S,?_,hcard⟩
  apply CodimOneAdmissibleAlong.isCoordinateFamilyAt_congr _ hcoord
  filter_upwards [U.isOpen.mem_nhds (hAU hxi)] with y hy
  rintro (_ | j)
  · constructor
    · intro hyA
      obtain ⟨j,hyj⟩ := mem_iUnion.mp hyA
      by_cases hji : j = i
      · simpa [hji] using hyj
      · exact False.elim (Set.disjoint_left.mp (hOther j hji) hyj hy)
    · intro hyA
      exact mem_iUnion.mpr ⟨i,hyA⟩
  · exact Iff.rfl
end
end Hironaka.HironakaG3LocallyFiniteDisjointUnionNC
