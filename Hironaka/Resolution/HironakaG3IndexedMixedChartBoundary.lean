import Hironaka.Resolution.HironakaG3IndexedMixedGluing
import Hironaka.Resolution.HironakaG3RPureBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedChartBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSeparation
  HironakaG3IndexedMixedGluing HironakaG3IndexedMixedOverlap
  HironakaG3RPureBoundary HironakaG3RPureEmbedded BlowupTowerTransforms RestrictEmptyTower
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X)

/-- The actual transformed local boundary, carried into the glued ambient space. -/
def mixedChartBoundary (c : TowerChart (indexedMixedClass V D) Z P)
    (E : List (Set c.Y)) : List (Set Z) := E.map (chartIncl c '' ·)

/-- Actual transformed boundary lists agree on the glued ambient overlap, after
omitting empty traces, for any complete window witnesses of the two charts. -/
theorem mixed_chart_boundary_overlap
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (c₁ c₂ : TowerChart (indexedMixedClass V D) Z P)
    (s₁ s₂ : Finset ι) (r₁ r₂ : Finset κ) (Ef₁ : List (Set c₁.Y)) (Ef₂ : List (Set c₂.Y))
    (hs₁ : ∀ i, ((V i).carrier ∩ (c₁.U : Set X)).Nonempty → i ∈ s₁)
    (hs₂ : ∀ i, ((V i).carrier ∩ (c₂.U : Set X)).Nonempty → i ∈ s₂)
    (hr₁ : ∀ i, (D i ∩ (c₁.U : Set X)).Nonempty → i ∈ r₁)
    (hr₂ : ∀ i, (D i ∩ (c₂.U : Set X)).Nonempty → i ∈ r₂)
    (hTree₁ : CanonicalMixedSeparation (((r₁.sort (· ≤ ·)).map D).map ((Subtype.val : c₁.U → X) ⁻¹' ·))
      ((s₁.sort (· ≤ ·)).map (fun a => ((Subtype.val : c₁.U → X) ⁻¹' (V a).carrier,(V a).dim))) c₁.T Ef₁)
    (hTree₂ : CanonicalMixedSeparation (((r₂.sort (· ≤ ·)).map D).map ((Subtype.val : c₂.U → X) ⁻¹' ·))
      ((s₂.sort (· ≤ ·)).map (fun a => ((Subtype.val : c₂.U → X) ⁻¹' (V a).carrier,(V a).dim))) c₂.T Ef₂)
    (hOver₁ : CentresOver ((Subtype.val : c₁.U → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₁.sort (· ≤ ·)).length => V ((s₁.sort (· ≤ ·)).get j))) c₁.T)
    (hOver₂ : CentresOver ((Subtype.val : c₂.U → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₂.sort (· ≤ ·)).length => V ((s₂.sort (· ≤ ·)).get j))) c₂.T) :
    ((mixedChartBoundary V D c₁ Ef₁).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
    ((mixedChartBoundary V D c₂ Ef₂).map
      (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) := by
  obtain ⟨η,hη,hEtrace⟩ := indexed_mixed_trees_overlap_with_boundary V hDim hDistinct D s₁ s₂ r₁ r₂
    c₁.U c₂.U hs₁ hs₂ hr₁ hr₂ c₁.T c₂.T Ef₁ Ef₂ hTree₁ hTree₂ hOver₁ hOver₂
  have hincl := HironakaG3RPureBoundary.incl_comparison c₁ c₂ inf_le_right η hη
  have hL : ∀ (c : TowerChart (indexedMixedClass V D) Z P) (Ef : List (Set c.Y)),
      (mixedChartBoundary V D c Ef).map
          (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        (Ef.map ((Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y) ⁻¹' ·)).map
          ((chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y)) '' ·) := by
    intro c Ef
    unfold mixedChartBoundary
    rw [List.map_map,List.map_map]
    congr 1
    funext H
    exact HironakaG3RPureBoundary.chartIncl_image_inter_preimage c _ H
  rw [hL c₁ Ef₁,hL c₂ Ef₂,HironakaG3RGluedBoundary.filter_nonempty_map_image,
    HironakaG3RGluedBoundary.filter_nonempty_map_image]
  erw [hEtrace]
  rw [List.map_map]
  congr 1
  funext C
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨η a,ha,hincl a⟩
  · rintro ⟨b,hb,rfl⟩
    refine ⟨η.symm b,show η (η.symm b) ∈ C by rw [η.apply_symm_apply]; exact hb, ?_⟩
    have h := hincl (η.symm b)
    rw [η.apply_symm_apply] at h
    exact h.symm
end
end Hironaka.HironakaG3IndexedMixedChartBoundary
