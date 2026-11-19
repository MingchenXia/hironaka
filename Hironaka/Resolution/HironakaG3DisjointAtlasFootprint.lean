import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
import Hironaka.Resolution.HironakaG3GluedClassFootprint
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointAtlasFootprint
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3GluedClassFootprint RestrictEmptyTower
open ResolutionInvariantExt (IsEmptyTower)

private theorem centres_mono {n : ℕ} {X : CMfd.{0} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centres_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

private theorem empty_centres_over {n : ℕ} {X : CMfd.{0} n} (F : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsEmptyTower T → CentresOver F T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => ⟨empty_centres_over F T h.1, by rw [h.2]; exact empty_subset _⟩

/-- Every chart tower of the assembled class has all centres over the union. -/
theorem disjoint_class_centres_over_union {n : ℕ} {X : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : disjointWindowClass A W K U Y T) :
    CentresOver ((Subtype.val : U → X) ⁻¹' (⋃ i, A i)) T := by
  rcases hT with ⟨i,_,hK⟩ | ⟨_,hEmpty⟩
  · apply centres_mono _ T (hCentres i U Y T hK)
    intro x hx
    exact mem_iUnion.mpr ⟨i,hx⟩
  · exact empty_centres_over _ T hEmpty

/-- The actual glued map is an isomorphism away from the union of component supports. -/
theorem disjoint_atlas_footprint {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    {P : Z → X} (hP : IsGluedFrom (disjointWindowClass A W K) Z P) :
    exceptionalLocus n P ⊆ P ⁻¹' (⋃ i, A i) ∧ IsIsomorphismOver n P (⋃ i, A i)ᶜ := by
  refine ⟨glued_exceptional_subset (⋃ i, A i) (hLF.isClosed_iUnion hClosed) ?_ hP,
    glued_isomorphism_over_compl (⋃ i, A i) (hLF.isClosed_iUnion hClosed) ?_ hP⟩
  all_goals exact disjoint_class_centres_over_union A W K hCentres
end
end Hironaka.HironakaG3DisjointAtlasFootprint
