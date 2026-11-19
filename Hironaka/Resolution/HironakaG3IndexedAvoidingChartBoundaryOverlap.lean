import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryClass
import Hironaka.Resolution.HironakaG3ResidualFullBoundaryTransport
import Hironaka.Resolution.HironakaG3RGluedBoundary
import Hironaka.Resolution.HironakaG3RPureBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedAvoidingChartBoundaryOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MaxLocusLocal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RPureBoundary
  HironakaG3RGluedBoundary HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows HironakaG3ResidualStoppedOverlapFinite
  HironakaG3ResidualFullBoundaryTransport HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3RBoundaryEmbedded

variable {n : ℕ} {X : CMfd.{0} n} {ι : Type*} [LinearOrder ι]
  (C : Set X) (r : ℕ) (D : ι → Set X) {Z : CMfd.{0} n} {P : Z → X}

/-- The finite visible boundary labels chosen for this actual class chart. -/
def avoidingChartWindow (c : TowerChart (indexedAvoidingBoundaryClass C r D) Z P) : Finset ι :=
  Classical.choose c.mem

/-- The transformed full finite boundary of this actual class chart. -/
def avoidingChartBoundary (c : TowerChart (indexedAvoidingBoundaryClass C r D) Z P) : List (Set Z) :=
  let R := avoidingChartWindow C r D c
  let E := (R.sort (· ≤ ·)).map D
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) C)
  (geoTransformAlong (fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·)) J) c.T).E.map (chartIncl c '' ·)

/-- Literal chart boundary traces agree on actual overlaps after removing empty sets. -/
theorem avoiding_chart_boundary_overlap
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅)
    (hr : r < n) (hpure : C ⊆ closure (regularLocus (n := n) C r))
    (c₁ c₂ : TowerChart (indexedAvoidingBoundaryClass C r D) Z P) :
    ((avoidingChartBoundary C r D c₁).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
    ((avoidingChartBoundary C r D c₂).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
  let R₁ := avoidingChartWindow C r D c₁
  let R₂ := avoidingChartWindow C r D c₂
  have h₁ := Classical.choose_spec c₁.mem
  have h₂ := Classical.choose_spec c₂.mem
  change (∀ i, (D i ∩ (c₁.U : Set X)).Nonempty → i ∈ R₁) ∧
    bdryClass C r ((R₁.sort (· ≤ ·)).map D) c₁.U c₁.Y c₁.T at h₁
  change (∀ i, (D i ∩ (c₂.U : Set X)).Nonempty → i ∈ R₂) ∧
    bdryClass C r ((R₂.sort (· ≤ ·)).map D) c₂.U c₂.Y c₂.T at h₂
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
  have hn : 0 < n := by omega
  obtain ⟨β,hβ⟩ := residual_stopped_histories_overlap_of_window_avoid hn C hC.analytic hr hpure D hD.2.1
    ∅ R₁ R₂ (by simp) (by simp) (sorted_boundary_snc D hD R₁) (sorted_boundary_snc D hD R₂)
    (hAvoidR R₁) (hAvoidR R₂) c₁.U c₂.U (fun i _ => h₁.1 i) (fun i _ => h₂.1 i)
    c₁.T c₂.T h₁.2 h₂.2
  have hEtrace := residual_full_boundary_transport_on_overlap D hD.2.1 ∅ R₁ R₂ (by simp) (by simp) c₁.U c₂.U
    (fun i _ => h₁.1 i) (fun i _ => h₂.1 i) (vanishingIdeal (n := n) C) c₁.T c₂.T β hβ
  have hβproj := emptyAware_proj_comm hβ
  have hβ' : ∀ z, ((c₂.T.proj (β z).1 : c₂.U) : X) = ((c₁.T.proj z.1 : c₁.U) : X) := by
    intro y
    have hz := congrArg (fun q : nestedOpens c₂.U (c₁.U ⊓ c₂.U) => q.val.val) (hβproj y)
    rw [overlapBaseEquiv_point] at hz
    have htproj := congrArg (fun q : c₂.U => q.val)
      (proj_restrict (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) c₂.T (β y))
    have hsproj := congrArg (fun q : c₁.U => q.val)
      (proj_restrict (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) c₁.T y)
    exact htproj.symm.trans (hz.trans hsproj)
  have hincl := HironakaG3RPureBoundary.incl_comparison c₁ c₂ inf_le_right β hβ'
  have hL : ∀ c : TowerChart (indexedAvoidingBoundaryClass C r D) Z P,
      let E := ((avoidingChartWindow C r D c).sort (· ≤ ·)).map D
      (avoidingChartBoundary C r D c).map
          (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        ((geoTransformAlong (fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·))
          (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) C))) c.T).E.map
          ((Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y) ⁻¹' ·)).map
          ((chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y)) '' ·) := by
    intro c
    dsimp only
    unfold avoidingChartBoundary
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _
    exact HironakaG3RPureBoundary.chartIncl_image_inter_preimage c _ H
  rw [hL c₁,hL c₂,HironakaG3RGluedBoundary.filter_nonempty_map_image,
    HironakaG3RGluedBoundary.filter_nonempty_map_image]
  simp only [Finset.sort_empty, List.map_nil, List.append_nil] at hEtrace
  erw [hEtrace]
  rw [List.map_map]
  congr 1
  funext K
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨β a,ha,hincl a⟩
  · rintro ⟨b,hb,rfl⟩
    refine ⟨β.symm b,show β (β.symm b) ∈ K by rw [β.apply_symm_apply]; exact hb, ?_⟩
    have h := hincl (β.symm b)
    rw [β.apply_symm_apply] at h
    exact h.symm
end
end Hironaka.HironakaG3IndexedAvoidingChartBoundaryOverlap
