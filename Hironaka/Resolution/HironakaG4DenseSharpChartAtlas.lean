import Hironaka.Resolution.HironakaG4OrderedContainmentAtlas

/-! Adapt actual compact-relative dense cleanup charts to the local tower
class used by the full sharp cleanup theorem. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4DenseSharpChartAtlas
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealTowerTransport NormalCrossings NormalCrossingsInvariance
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons G3UniverseEmptyAwareCore
  HironakaG4SharpTerminalAtlas HironakaG4OrderedContainmentAtlas HironakaG34NonPureLowDim
  HironakaOriginalTerminalOverlapComparison MaxLocusLocal

/-- A predicate on actual finite towers with a smooth carrier and its
literal ordered initial boundary on the source manifold. -/
abbrev DenseSharpChart (n : ℕ) :=
  {X Y : CMfd.{u} n} → Set X → List (Set X) → BlowupTower X Y → Prop

/-- Existence near compact sets and actual comparison on matching source
data suffice to build the compatible dense chart class. -/
structure DenseSharpChartService {n : ℕ} (Chart : DenseSharpChart.{u} n) : Prop where
  restrictOpen : ∀ {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y},
    Chart W E T → ∀ O : Opens X,
      Chart ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  rebase : ∀ {X X' Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y},
    Chart W E T → ∀ e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      Chart (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower
  compare : ∀ {X X' Y Y' : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    Chart W E T → Chart (e ⁻¹' W) (E.map (e ⁻¹' ·)) T' →
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso e T' T η
  terminal : ∀ {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)} {T : BlowupTower X Y},
    Chart W E T → IsSharpTerminalTower W E T
  nearCompact : ∀ {X : CMfd.{u} n} {W : Set X} {E : List (Set X)},
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    ∀ K : Set X, IsCompact K → ∃ V : Opens X, K ⊆ V ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) V) Y),
        Chart ((Subtype.val : V → X) ⁻¹' W) (E.map ((Subtype.val : V → X) ⁻¹' ·)) T

variable {n : ℕ} {Chart : DenseSharpChart.{u} n} {X : CMfd.{u} n}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- The original overlap identifies the literal restricted data. Existence
near a compact enclosure gives an actual chart on the prescribed open. -/
theorem exists_dense_sharp_chart_class (service : DenseSharpChartService Chart)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    ∃ C : LocalTowerClass X, SharpTerminalClass W E C ∧ HasPhysicalComparisons C ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), C U Y T := by
  let C : LocalTowerClass X := fun U _ T =>
    Chart ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T
  refine ⟨C,fun _ _ _ h => service.terminal h,?_,?_⟩
  · intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
    let J := U₁ ⊓ U₂
    let D₁ := nestedOpens U₁ J
    let D₂ := nestedOpens U₂ J
    let e := overlapBaseEquiv (n := n) (show J ≤ U₁ from inf_le_left) (show J ≤ U₂ from inf_le_right)
    let W₁ := (Subtype.val : D₁ → U₁) ⁻¹' ((Subtype.val : U₁ → X) ⁻¹' W)
    let W₂ := (Subtype.val : D₂ → U₂) ⁻¹' ((Subtype.val : U₂ → X) ⁻¹' W)
    let E₁ := (E.map ((Subtype.val : U₁ → X) ⁻¹' ·)).map ((Subtype.val : D₁ → U₁) ⁻¹' ·)
    let E₂ := (E.map ((Subtype.val : U₂ → X) ⁻¹' ·)).map ((Subtype.val : D₂ → U₂) ⁻¹' ·)
    have hPoint (z : D₁) : (e z).val.val = z.val.val := overlapBaseEquiv_point inf_le_left inf_le_right z
    have hCarrier : e ⁻¹' W₂ = W₁ := by
      ext z
      change (e z).val.val ∈ W ↔ z.val.val ∈ W
      rw [hPoint]
    have hBoundary : E₂.map (e ⁻¹' ·) = E₁ := by
      simp only [E₁,E₂,List.map_map]
      apply List.map_congr_left
      intro H _
      ext z
      change (e z).val.val ∈ H ↔ z.val.val ∈ H
      rw [hPoint]
    have hW₂ := BlowupRestrictOpen.isClosedSubmanifold_preimage_val
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U₂) D₂
    have hE₂ := isSNCDivisor_map_preimage (pullsBackCoordinates_val D₂) continuous_subtype_val
      (isSNCDivisor_map_preimage (pullsBackCoordinates_val U₂) continuous_subtype_val hE)
    have hDense₂ := open_full_density (X := CMfd.of (n := n) U₂) (open_full_density hDense U₂) D₂
    have hT₁ : Chart W₁ E₁ (restrict D₁ T₁) := service.restrictOpen h₁ D₁
    rw [← hCarrier,← hBoundary] at hT₁
    exact service.compare e hW₂ hE₂ hDense₂ (service.restrictOpen h₂ D₂) hT₁
  · intro U K hK hUK
    obtain ⟨V,hKV,Y,T,hT⟩ := service.nearCompact hW hE hDense K hK
    have hUV : U ≤ V := hUK.trans hKV
    let D := nestedOpens V U
    let e := (nestedOpensDiffeo (n := n) hUV).symm
    let R := transport e (restrict D T)
    have hR := service.rebase (service.restrictOpen hT D) e
    have hList : ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : D → V) ⁻¹' ·)).map
        (e ⁻¹' ·) = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
      simp only [List.map_map]
      rfl
    rw [hList] at hR
    exact ⟨R.target,R.tower,hR⟩

/-- The supplied actual dense-chart operations discharge the dense service
of the already established arbitrary-containment atlas. -/
theorem denseSharpAtlasService_of_charts {Chart : DenseSharpChart.{0} n}
    (service : DenseSharpChartService Chart) : DenseSharpAtlasService n := by
  intro X W hW E hE hDense
  exact exists_dense_sharp_chart_class service hW hE hDense

end
end Hironaka.HironakaG4DenseSharpChartAtlas
