import Hironaka.Resolution.HironakaG8NoncompactInitialBoundaryAtlas
import Hironaka.Invariant.ResolutionInvariantSegments

/-! # Counts above one compact probe in the certified physical atlas -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8AtlasCompactProbeBound
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec ResolutionInvariantSegments HironakaG3EmptyAwareHistory
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons MaxLocusLocal
  HironakaEmbeddedAnalytic NormalCrossings HironakaG8NoncompactInitialBoundaryAtlas
  HironakaG8LabelledEmbeddedAtlas HironakaG8LabelledEmbeddedTape
  HironakaG8LocalMixedEmbeddedResolution HironakaG8UniverseBMTransport
  HironakaOriginalTerminalOverlapComparison HironakaG8OrderedSmoothSuffix HironakaG8LocalMixedSmoothCleanup

/-- Empty-aware physical comparison preserves the count of centres
meeting the preimage of any fixed probe in the base. -/
theorem count_centres_meeting_emptyAware {n : ℕ} {X A Y B : CMfd.{0} n}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {T : BlowupTower X Y} {S : BlowupTower A B}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    (h : EmptyAwareTowerIso φ T S χ) (K : Set A) :
    countCentresMeeting (φ ⁻¹' K) T = countCentresMeeting K S := by
  induction h with
  | refl => rfl
  | @step Y B Z W T S e h C π hπ D ρ hρ f hMap hCentre ih =>
    have he : (C ∩ T.proj ⁻¹' (φ ⁻¹' K)).Nonempty ↔
        (D ∩ S.proj ⁻¹' K).Nonempty := by
      constructor
      · rintro ⟨x,hx,hxK⟩
        refine ⟨e x,?_ ,?_⟩
        · change x ∈ e ⁻¹' D
          rwa [hCentre]
        · change S.proj (e x) ∈ K
          rw [emptyAware_proj_comm h]
          exact hxK
      · rintro ⟨y,hy,hyK⟩
        let x := e.symm y
        have hx : e x = y := e.apply_symm_apply y
        refine ⟨x,?_ ,?_⟩
        · rw [← hCentre]
          change e x ∈ D
          rwa [hx]
        · change φ (T.proj x) ∈ K
          rw [← emptyAware_proj_comm h, hx]
          exact hyK
    simp only [countCentresMeeting, ih]
    by_cases hn : (D ∩ S.proj ⁻¹' K).Nonempty
    · rw [if_pos hn,if_pos (he.mpr hn)]
    · rw [if_neg hn,if_neg (fun hh => hn (he.mp hh))]
  | leftEmpty h _ _ _ ih =>
    simpa only [countCentresMeeting,empty_inter,Set.not_nonempty_empty,if_false,Nat.add_zero] using ih
  | rightEmpty h _ _ _ ih =>
    simpa only [countCentresMeeting,empty_inter,Set.not_nonempty_empty,if_false,Nat.add_zero] using ih

/-- Given one reference chart containing a probe, every chart in the
same physical class has at most its number of probe-meeting centres.
There is no assumption of a common serial clock. -/
theorem atlas_probe_count_le_reference {n : ℕ} {X : CMfd.{0} n}
    {F : LocalTowerClass X} (hCmp : HasPhysicalComparisons F)
    (U V : Opens X) {Y Z : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y)
    (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hT : F U Y T) (hS : F V Z S)
    (K : Set X) (hKV : K ⊆ V) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) T ≤
      countCentresMeeting ((Subtype.val : V → X) ⁻¹' K) S := by
  let O := U ⊓ V
  let L := nestedOpens U O
  let R := nestedOpens V O
  let φ := overlapBaseEquiv (n := n) (inf_le_left : O ≤ U) (inf_le_right : O ≤ V)
  let KU := (Subtype.val : U → X) ⁻¹' K
  let KV := (Subtype.val : V → X) ⁻¹' K
  have hSub : KU ⊆ L := fun x hx => ⟨x.property,hKV hx⟩
  have hK : (Subtype.val : L → U) ⁻¹' KU =
      φ ⁻¹' ((Subtype.val : R → V) ⁻¹' KV) := by
    ext x
    change x.val.val ∈ K ↔ (φ x).val.val ∈ K
    rw [overlapBaseEquiv_point]
  obtain ⟨χ,h⟩ := hCmp U V Y Z T S hT hS
  calc
    _ = countCentresMeeting ((Subtype.val : L → U) ⁻¹' KU) (restrict L T) :=
      (countCentresMeeting_restrict_of_subset L hSub T).symm
    _ = countCentresMeeting ((Subtype.val : R → V) ⁻¹' KV) (restrict R S) := by
      rw [hK]
      exact count_centres_meeting_emptyAware h _
    _ = countCentresMeeting (KV ∩ (R : Set V)) S := countCentresMeeting_restrict R KV S
    _ ≤ _ := countCentresMeeting_mono inter_subset_left S

/-- The exact probe count is independent of the reference chart when
both chart bases contain the entire probe. -/
theorem atlas_probe_count_eq_of_both_contain {n : ℕ} {X : CMfd.{0} n}
    {F : LocalTowerClass X} (hCmp : HasPhysicalComparisons F)
    (U V : Opens X) {Y Z : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hT : F U Y T) (hS : F V Z S)
    (K : Set X) (hKU : K ⊆ U) (hKV : K ⊆ V) :
    countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) T =
      countCentresMeeting ((Subtype.val : V → X) ⁻¹' K) S :=
  le_antisymm (atlas_probe_count_le_reference hCmp U V T S hT hS K hKV)
    (atlas_probe_count_le_reference hCmp V U S T hS hT K hKU)

/-- The certified noncompact construction has a uniform finite bound
for the number of centres hitting any one fixed compact base probe,
simultaneously for all actual charts of the class. -/
theorem initial_boundary_atlas_uniform_compact_probe_bound {m : ℕ} {X : CMfd.{0} (m+1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m+1) W)
    {E : List (Set X)} (hE : IsSNCDivisor (m+1) E)
    (hDense : W ⊆ closure (W \ ⋃ D ∈ E, D))
    (K : Set X) (hK : IsCompact K) :
    ∃ b : ℕ, ∀ (U : Opens X) (Y : CMfd.{0} (m+1))
      (T : BlowupTower (CMfd.of (n := m+1) U) Y),
      orderedInitialBoundaryClass W E U Y T →
      countCentresMeeting ((Subtype.val : U → X) ⁻¹' K) T ≤ b := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel (m+1)) X
  obtain ⟨L,hL,hKL,_⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let V : Opens X := ⟨interior L,isOpen_interior⟩
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate (m+1)) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange (m+2)) hB hT' hT
  have hProduce : ProducesLocalSmoothCertificates (ascending_smooth_tail_certificate (m+1)) := by
    intro A A₀ hSmooth E hE hDense L hL
    exact local_mixed_smooth_boundary_cleanup_ordered hSmooth E hE hDense L hL
  have hCmp := initial_boundary_class_physical (Nat.succ_pos m) hC hW hE hDense
  obtain ⟨Y,S,hS⟩ := initial_boundary_class_compact_windows hProduce hW hE hDense V L hL interior_subset
  exact ⟨countCentresMeeting ((Subtype.val : V → X) ⁻¹' K) S,
    fun U Z T hT => atlas_probe_count_le_reference hCmp U V T S hT hS K hKL⟩

end
end Hironaka.HironakaG8AtlasCompactProbeBound
