import Hironaka.Resolution.HironakaG3UniverseSmallManifold
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold
universe u v
namespace Hironaka.HironakaG3UniverseSmallBoundary
noncomputable section
open BlowupTowers HironakaActualLocallyFiniteBoundary HironakaG3UniverseSmallManifold

/-- The nonempty positions of an indexed SNC family are small, even when
the original index type has arbitrarily many empty positions. -/
theorem nonempty_index_small {n : ℕ} (X : CMfd.{u} n) {ι : Type v}
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    Small.{0} {i : ι // (D i).Nonempty} := by
  classical
  let J := {i : ι // (D i).Nonempty}
  have : Small.{0} X := complex_manifold_small X
  have : Small.{0} (Finset (Fin n)) := inferInstance
  have : Small.{0} (X × Finset (Fin n)) := inferInstance
  choose p hp using fun i : J => i.property
  choose S hCoord hCard hInj using hD.2.2
  let f : J → X × Finset (Fin n) := fun i => (p i,S (p i) i.val)
  apply small_of_injective (f := f)
  intro i j hij
  have hpij : p i = p j := congrArg Prod.fst hij
  have hSij : S (p i) i.val = S (p j) j.val := congrArg Prod.snd hij
  have hpi : p i ∈ D i.val := hp i
  have hpj : p i ∈ D j.val := by simpa only [hpij] using hp j
  apply Subtype.ext
  exact hInj (p i) hpi hpj (by simpa only [hpij] using hSij)
end
end Hironaka.HironakaG3UniverseSmallBoundary
