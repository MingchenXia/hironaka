import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryClass
import Hironaka.Resolution.HironakaG3RPureEmbedded
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedAvoidingBoundaryNonerasure
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3RBoundaryEmbedded EmbeddedFromResolution MaxLocusLocal

/-- The actual glued avoiding-boundary map retains the whole target. -/
theorem glued_indexed_avoiding_boundary_nonerasure {n : ℕ} {X Z : CMfd.{0} n}
    {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    {r : ℕ} (_hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    {P : Z → X} (h : IsGluedFrom (indexedAvoidingBoundaryClass C r D) Z P) :
    P '' strictTransform n P C = C := by
  have hClosed : IsClosed (P '' strictTransform n P C) := h.2.1.isClosedMap _ isClosed_closure
  have hAvoidR (R : Finset ι) : C ⊆ closure (C \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiS : i ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  apply Set.Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous hC.analytic.isClosed hz
  · intro x hx
    obtain ⟨c,hxU⟩ := h.2.2.2 x
    obtain ⟨R,_hVis,hHead⟩ := c.mem
    let E := (R.sort (· ≤ ·)).map D
    have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
    have hdense : C ⊆ closure (C ∩ bdryOpen C r E) :=
      subset_closure_inter_bdryOpen hC.analytic.isClosed hpure hE.1 (hAvoidR R)
    have hxcl : x ∈ closure ((c.U : Set X) ∩ (C ∩ bdryOpen C r E)) :=
      c.U.isOpen.inter_closure ⟨hxU,hdense hx⟩
    apply closure_minimal _ hClosed hxcl
    rintro q ⟨hqU,hqC,hqO⟩
    obtain ⟨z,hzq⟩ := h.2.2.1 q
    have hzV : z ∈ c.V := c.mem_V (hzq ▸ hqU)
    let y := c.φ.symm ⟨z,hzV⟩
    have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
    have hyproj : ((c.T.proj y : c.U) : X) = q := by
      rw [← proj_chartIncl c y,hyz,hzq]
    have hyO : c.T.proj y ∈ nestedOpens c.U (bdryOpen C r E) := by
      change ((c.T.proj y : c.U) : X) ∈ bdryOpen C r E
      rw [hyproj]
      exact hqO
    have hyC : c.T.proj y ∈ (Subtype.val : c.U → X) ⁻¹' C := by
      change ((c.T.proj y : c.U) : X) ∈ C
      rw [hyproj]
      exact hqC
    have hy : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' C) :=
      (mem_strictTransform_iff_of_centresAvoid (nestedOpens c.U (bdryOpen C r E)) c.T hHead.2.1
        (hC.analytic.isClosed.preimage continuous_subtype_val) hyO).2 hyC
    rw [strictTransform_chart c h.1 C] at hy
    exact ⟨z,hyz ▸ hy,hzq⟩
end
end Hironaka.HironakaG3IndexedAvoidingBoundaryNonerasure
