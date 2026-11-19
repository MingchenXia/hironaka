import Hironaka.Resolution.HironakaG3SeparatedAvoidingAtlas
import Hironaka.Resolution.HironakaG3DisjointAtlasComponentChart
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedAvoidingGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3RBoundaryEmbedded HironakaG3DisjointLocalTowerAtlas
  HironakaG3DisjointAtlasComponentChart EmbeddedFromResolution MaxLocusLocal

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
  (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
  (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
  (hD : IsLocallyFiniteSNCDivisor n D)
  (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
  (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
  (W : ι → Opens X) (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
  {P : Z → X} (hG : IsGluedFrom (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) Z P)

include hC hD hS in
private theorem finite_window_dense (i : ι) (R : Finset κ) :
    C i ⊆ closure (C i \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
  apply (dense_off_residual_family (C i) D (hC i) hD).trans
  apply closure_mono
  rintro x ⟨hxC,hxOut⟩
  refine ⟨hxC,?_⟩
  intro hxB
  obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
  have hjS : j ∉ containingLabels (C i) D (hC i).nonempty hD.1 := by rw [hS i]; simp
  exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)

include hC hD hS hr hpure hWindow hG

theorem separated_avoiding_strict_regular (i : ι) :
    ∀ z ∈ strictTransform n P (C i), RegularAtDim (n := n) (strictTransform n P (C i)) z (r i) := by
  intro z hz
  have hzC : P z ∈ C i := HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hC i).analytic.isClosed hz
  obtain ⟨c,hU,_⟩ := exists_component_chart_for_disjoint_atlas C W (fun j => indexedAvoidingBoundaryClass (C j) (r j) D) hWindow hG i hzC
  obtain ⟨R,_hVis,hStop⟩ := c.mem
  have hg := bdry_stopped_geometry (hC i).analytic (hr i) (hpure i) (sorted_boundary_snc D hD R)
    (finite_window_dense C D hC hD hS i R) c.U c.T hStop
  have hst := strictTransform_chart c hG.1 (C i)
  have hzV : z ∈ c.V := c.mem_V hU
  let y := c.φ.symm ⟨z,hzV⟩
  have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
  rw [← hyz] at hz ⊢
  refine regularAtDim_of_chart c ?_
  rw [← hst]
  refine hg.2.2.2.2.2.2.2.1 y ?_
  rw [hst]
  exact hz

theorem separated_avoiding_strict_closed_submanifold (i : ι) : IsClosedSubmanifold n (strictTransform n P (C i)) :=
  ⟨isClosed_closure,fun z hz => ⟨r i,separated_avoiding_strict_regular C r D hC hD hS hr hpure W hWindow hG i z hz⟩⟩

omit hr in
theorem separated_avoiding_nonerasure (i : ι) : P '' strictTransform n P (C i) = C i := by
  have hClosed : IsClosed (P '' strictTransform n P (C i)) := hG.2.1.isClosedMap _ isClosed_closure
  apply Set.Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hC i).analytic.isClosed hz
  · intro x hx
    obtain ⟨c,hxU,_⟩ := exists_component_chart_for_disjoint_atlas C W (fun j => indexedAvoidingBoundaryClass (C j) (r j) D) hWindow hG i hx
    obtain ⟨R,_hVis,hHead⟩ := c.mem
    let E := (R.sort (· ≤ ·)).map D
    have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
    have hdense : C i ⊆ closure (C i ∩ bdryOpen (C i) (r i) E) :=
      subset_closure_inter_bdryOpen (hC i).analytic.isClosed (hpure i) hE.1 (finite_window_dense C D hC hD hS i R)
    have hxcl : x ∈ closure ((c.U : Set X) ∩ (C i ∩ bdryOpen (C i) (r i) E)) :=
      c.U.isOpen.inter_closure ⟨hxU,hdense hx⟩
    apply closure_minimal _ hClosed hxcl
    rintro q ⟨hqU,hqC,hqO⟩
    obtain ⟨z,hzq⟩ := hG.2.2.1 q
    have hzV : z ∈ c.V := c.mem_V (hzq ▸ hqU)
    let y := c.φ.symm ⟨z,hzV⟩
    have hyz : chartIncl c y = z := chartIncl_symm c ⟨z,hzV⟩
    have hyproj : ((c.T.proj y : c.U) : X) = q := by
      rw [← proj_chartIncl c y,hyz,hzq]
    have hyO : c.T.proj y ∈ nestedOpens c.U (bdryOpen (C i) (r i) E) := by
      change ((c.T.proj y : c.U) : X) ∈ bdryOpen (C i) (r i) E
      rw [hyproj]
      exact hqO
    have hyC : c.T.proj y ∈ (Subtype.val : c.U → X) ⁻¹' C i := by
      change ((c.T.proj y : c.U) : X) ∈ C i
      rw [hyproj]
      exact hqC
    have hy : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' C i) :=
      (mem_strictTransform_iff_of_centresAvoid (nestedOpens c.U (bdryOpen (C i) (r i) E)) c.T hHead.2.1
        ((hC i).analytic.isClosed.preimage continuous_subtype_val) hyO).2 hyC
    rw [strictTransform_chart c hG.1 (C i)] at hy
    exact ⟨z,hyz ▸ hy,hzq⟩
end
end Hironaka.HironakaG3SeparatedAvoidingGeometry
