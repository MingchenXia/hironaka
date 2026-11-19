import Hironaka.Resolution.HironakaG3DisjointPhysicalOverlap
import Hironaka.Resolution.HironakaG3FiniteVisibleAtlas
import Hironaka.Resolution.HironakaG3BornBoundaryPhysicalOverlap
import Hironaka.Resolution.HironakaG3RGluedBoundary
import Hironaka.Resolution.HironakaG3RPureBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GenericBornChartOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RPureBoundary
  HironakaG3RGluedBoundary HironakaG3DisjointLocalTowerAtlas HironakaG3DisjointPhysicalOverlap HironakaG3FiniteVisibleAtlas
  HironakaG3BornBoundaryPhysicalOverlap HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareHistory
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal RestrictEmptyTower

/-- The literal images of the born slots of any actual tower chart. -/
def bornChartBoundary {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X} {P : Z → X}
    (c : TowerChart 𝒞 Z P) : List (Set Z) := (bornAlong c.T).map (chartIncl c '' ·)

/-- A physical comparison of two actual charts identifies the ordered lists
of their nonempty born traces on the literal same-map overlap. -/
theorem born_chart_overlap_of_physical {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X} {P : Z → X}
    (c₁ c₂ : TowerChart 𝒞 Z P)
    (β : CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage c₂.T (nestedOpens c₂.U (c₁.U ⊓ c₂.U))))
    (hβ : EmptyAwareTowerIso (overlapBaseEquiv (n := n)
      (inf_le_left : c₁.U ⊓ c₂.U ≤ c₁.U) inf_le_right)
        (restrict (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) c₁.T)
        (restrict (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) c₂.T) β) :
    ((bornChartBoundary c₁).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) =
    ((bornChartBoundary c₂).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) := by
  have hEtrace := born_boundary_physical_overlap c₁.U c₂.U c₁.T c₂.T β hβ
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
  have hL : ∀ c : TowerChart 𝒞 Z P,
      (bornChartBoundary c).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        ((bornAlong c.T).map
          ((Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y) ⁻¹' ·)).map
          ((chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y)) '' ·) := by
    intro c
    unfold bornChartBoundary
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _
    exact HironakaG3RPureBoundary.chartIncl_image_inter_preimage c _ H
  rw [hL c₁,hL c₂,HironakaG3RGluedBoundary.filter_nonempty_map_image,
    HironakaG3RGluedBoundary.filter_nonempty_map_image]
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
/-- The actual isolated disjoint class supplies its physical comparison from
per-component comparisons and centre footprints; no overlap map is supplied. -/
theorem disjoint_born_chart_overlap {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (A : ι → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X) (D : κ → Set X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (A j) (W i : Set X))
    (hSame : ∀ (i : ι) (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{0} n)
      (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁) (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂),
      K i U₁ Y₁ T₁ → K i U₂ Y₂ T₂ →
      ∃ β : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
        EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
          (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) T₁) (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) T₂) β)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' A i) T)
    {P : Z → X} (c₁ c₂ : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P) :
    ((bornChartBoundary c₁).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) =
    ((bornChartBoundary c₂).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) := by
  obtain ⟨β,hβ⟩ := disjoint_physical_overlap A W K hWindow hSame hCentres
    c₁.U c₂.U c₁.Y c₂.Y c₁.T c₂.T c₁.mem.1 c₂.mem.1
  exact born_chart_overlap_of_physical c₁ c₂ β hβ
end
end Hironaka.HironakaG3GenericBornChartOverlap
