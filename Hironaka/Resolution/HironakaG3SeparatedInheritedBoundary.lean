import Hironaka.Resolution.HironakaG3SeparatedVisibleChartBoundary
import Hironaka.Resolution.HironakaG3DisjointAtlasFootprint
import Hironaka.Resolution.HironakaG3IndexedSeparatedComponents
import Hironaka.Resolution.HironakaG8P1ArcTangentTrace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedInheritedBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaDisjointFiniteControlledHistory
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3IndexedSeparatedComponents
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedAvoidingBoundaryClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3DisjointAtlasFootprint HironakaG3FiniteVisibleAtlas HironakaG3SeparatedVisibleChartWindow
  HironakaG3SeparatedVisibleChartBoundary HironakaG3EmptyAwareFullBoundary HironakaG8P1ArcTangentTrace
  MaxLocusLocal RestrictEmptyTower HomogenizedGlueingTower

/-- Actual strict transforms of a locally finite closed initial family remain locally finite. -/
theorem inherited_strict_family_locally_finite {n : ℕ} {X Z : CMfd.{0} n} {κ : Type*}
    (D : κ → Set X) (hClosed : ∀ j, IsClosed (D j)) (hLF : LocallyFinite D)
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P) :
    LocallyFinite (fun j => strictTransform n P (D j)) :=
  locallyFinite_strictTransforms D hClosed hLF hP.continuous

/-- In any actual chart whose centres lie over a locally finite closed family,
old slots agree with conventional strict transforms if the boundary is dense
off that family. -/
theorem inherited_old_slot_eq_strict_trace_of_centres_over {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} (C : ι → Set X) (D : κ → Set X)
    (hCclosed : ∀ i, IsClosed (C i)) (hCLF : LocallyFinite C) (hDclosed : ∀ j, IsClosed (D j))
    (hDense : ∀ j, D j ⊆ closure (D j \ ⋃ i, C i))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    {𝒞 : LocalTowerClass X} (c : TowerChart 𝒞 Z P)
    (hOver : CentresOver ((Subtype.val : c.U → X) ⁻¹' (⋃ i, C i)) c.T) (j : κ) :
    strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j) =
      chartIncl c ⁻¹' strictTransform n P (D j) := by
  let F := ⋃ i, C i
  let O : Opens (CMfd.of (n := n) c.U) := ⟨((Subtype.val : c.U → X) ⁻¹' F)ᶜ,
    ((hCLF.isClosed_iUnion hCclosed).preimage continuous_subtype_val).isOpen_compl⟩
  have hAvoid : CentresAvoid O c.T := centresAvoid_of_centresOver O disjoint_compl_left c.T hOver
  have hDensU : (Subtype.val : c.U → X) ⁻¹' D j ⊆ closure ((Subtype.val : c.U → X) ⁻¹' (D j \ F)) := by
    intro x hx
    have hx' := hDense j hx
    exact (Set.ext_iff.mp (c.U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val _) x).mp hx'
  have hDensO : (Subtype.val : c.U → X) ⁻¹' D j ⊆
      closure (((Subtype.val : c.U → X) ⁻¹' D j) ∩ (O : Set (CMfd.of (n := n) c.U))) := by
    change (Subtype.val : c.U → X) ⁻¹' D j ⊆
      closure (((Subtype.val : c.U → X) ⁻¹' D j) ∩ ((Subtype.val : c.U → X) ⁻¹' F)ᶜ)
    simpa only [preimage_sdiff,preimage_inter,preimage_compl,sdiff_eq] using hDensU
  rw [strictAlong_eq_conventional_of_centresAvoid _ ((hDclosed j).preimage continuous_subtype_val) O hDensO c.T hAvoid,
    strictTransform_chart c hP (D j)]


/-- The actual old tower slot equals the pullback of the conventional global strict transform. -/
theorem inherited_old_slot_eq_strict_trace {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X)
    (hCclosed : ∀ i, IsClosed (C i)) (hCLF : LocallyFinite C) (hDclosed : ∀ j, IsClosed (D j))
    (hDense : ∀ j, D j ⊆ closure (D j \ ⋃ i, C i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      indexedAvoidingBoundaryClass (C i) (r i) D U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
      (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) (j : κ) :
    strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j) =
      chartIncl c ⁻¹' strictTransform n P (D j) := by
  apply inherited_old_slot_eq_strict_trace_of_centres_over C D hCclosed hCLF hDclosed hDense hP c _ j
  exact disjoint_class_centres_over_union C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)
    hCentres c.U c.Y c.T c.mem.1

/-- Under an explicit density-off-components hypothesis, an actual inherited
strict-transform trace is literally an old slot of every chart which it meets. -/
theorem inherited_strict_trace_is_old_slot {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X)
    (hCclosed : ∀ i, IsClosed (C i)) (hCLF : LocallyFinite C) (hDclosed : ∀ j, IsClosed (D j))
    (hDense : ∀ j, D j ⊆ closure (D j \ ⋃ i, C i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      indexedAvoidingBoundaryClass (C i) (r i) D U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
      (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) (j : κ)
    (hTrace : (strictTransform n P (D j) ∩ c.V).Nonempty) :
    strictTransform n P (D j) ∩ c.V ∈ separatedVisibleChartBoundary C r D W c := by
  let R := separatedChartWindow C r D W c
  let M := fullMarked (((R.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·))
    (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X)))
  have hVis : ∀ i, (D i ∩ (c.U : Set X)).Nonempty → i ∈ R := (separated_chart_window_spec C r D W c).1
  have hOld := inherited_old_slot_eq_strict_trace C r D W hCclosed hCLF hDclosed hDense hCentres hP c j
  have hMeet : (D j ∩ (c.U : Set X)).Nonempty := by
    obtain ⟨z,hzD,hzV⟩ := hTrace
    have hzPre := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hDclosed j) hzD
    exact ⟨P z,hzPre,by rw [c.V_eq] at hzV; exact hzV⟩
  have hR : j ∈ R := hVis j hMeet
  have hE : (Subtype.val : c.U → X) ⁻¹' D j ∈ M.E := by
    change _ ∈ (((R.sort (· ≤ ·)).map D).map ((Subtype.val : c.U → X) ⁻¹' ·))
    exact List.mem_map.mpr ⟨D j,List.mem_map.mpr ⟨j,by simpa using hR,rfl⟩,rfl⟩
  have hSlot : strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j) ∈ (geoTransformAlong M c.T).E := by
    rw [boundary_decomp]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_,hE,rfl⟩)
  have hImage : chartIncl c '' (strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j)) =
      strictTransform n P (D j) ∩ c.V := by
    rw [hOld,Set.image_preimage_eq_inter_range,range_chartIncl]
  unfold separatedVisibleChartBoundary
  change _ ∈ (geoTransformAlong M c.T).E.map (chartIncl c '' ·)
  rw [← hImage]
  exact List.mem_map.mpr ⟨_,hSlot,rfl⟩
end
end Hironaka.HironakaG3SeparatedInheritedBoundary
