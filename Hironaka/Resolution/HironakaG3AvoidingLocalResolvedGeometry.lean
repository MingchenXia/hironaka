import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryNonerasure
import Hironaka.Resolution.HironakaG3RBoundaryEmbedded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AvoidingLocalResolvedGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3RBoundaryEmbedded EmbeddedFromResolution MaxLocusLocal

theorem indexed_avoiding_member_resolved_geometry {n : ℕ} {X Y : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (U : Opens X) (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : indexedAvoidingBoundaryClass C r D U Y T) :
    T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
    ∀ y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C),
      RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) y r := by
  obtain ⟨R,_hVis,hStop⟩ := hT
  let E := (R.sort (· ≤ ·)).map D
  have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ E, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    have hjS : j ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)
  have hg := bdry_stopped_geometry hC.analytic hr hpure hE hAvoid U T hStop
  have hDense : C ⊆ closure (C ∩ bdryOpen C r E) :=
    subset_closure_inter_bdryOpen hC.analytic.isClosed hpure hE.1 hAvoid
  have hDenseU : (Subtype.val : U → X) ⁻¹' C ⊆
      closure (((Subtype.val : U → X) ⁻¹' C) ∩ (nestedOpens U (bdryOpen C r E) : Set U)) := by
    intro x hx
    have heq := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (C ∩ bdryOpen C r E)
    exact (Set.ext_iff.mp heq x).mp (hDense hx)
  have hClosed : IsClosed (T.proj '' strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C)) :=
    (HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence T.isBlowupSequence).isClosedMap _ isClosed_closure
  constructor
  · apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous
        (hC.analytic.isClosed.preimage continuous_subtype_val) hy
    · intro x hx
      apply closure_minimal _ hClosed (hDenseU hx)
      rintro q ⟨hqC,hqO⟩
      obtain ⟨y,hyq⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence q
      have hyO : T.proj y ∈ nestedOpens U (bdryOpen C r E) := by rw [hyq]; exact hqO
      have hyC : T.proj y ∈ (Subtype.val : U → X) ⁻¹' C := by rw [hyq]; exact hqC
      have hy : y ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C) :=
        (mem_strictTransform_iff_of_centresAvoid (nestedOpens U (bdryOpen C r E)) T hStop.2.1
          (hC.analytic.isClosed.preimage continuous_subtype_val) hyO).2 hyC
      exact ⟨y,hy,hyq⟩
  · exact hg.2.2.2.2.2.2.2.1
end
end Hironaka.HironakaG3AvoidingLocalResolvedGeometry
