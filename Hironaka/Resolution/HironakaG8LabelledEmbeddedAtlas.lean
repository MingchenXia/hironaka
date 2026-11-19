import Hironaka.Resolution.HironakaG8LabelledEmbeddedTape
import Hironaka.Resolution.HironakaG8CompleteEmbeddedAtlasBoundary

/-! Glue the physically compared labelled mixed finite histories. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LabelledEmbeddedAtlas

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaEmbeddedBoundary NormalCrossings HironakaStageCenters
  HironakaG8LabelledNativeHistory HironakaG8LabelledNativeOverlap HironakaG8FilteredBoundaryTerminalOverlap
  HironakaG8LabelledEmbeddedTape HironakaG8LocalMixedPhaseAssembly HironakaG8LocalMixedEmbeddedResolution
  HironakaG8CompleteEmbeddedAtlas HironakaG8CompleteEmbeddedAtlasBoundary HironakaG8IsolatedCompactSingularAtlas
  HironakaG3RTowerClass HironakaG3RChartOfMember G3UniversePhysicalClassComparisons HironakaG3EmptyAwareHistory
  HironakaG3BiholomorphicFirstMeeting HironakaG3EmptyAwareBornSlots HironakaG3GenericBornChartOverlap
  MaxLocusLocal HironakaOriginalTerminalOverlapComparison
  HironakaG8UniverseDenseBoundary HironakaG8UniverseBMTransport HironakaG8LocalPureFinish
  HironakaSharpActualFiniteChronologicalHistory HironakaCoherentTransformExtension
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation HironakaG3REmbeddedGlobalSNC

variable {n : ℕ}

/-- Comparison of the actual retained smooth suffixes after matching the
current carriers and the nonempty initial slots over the base. -/
def SmoothTailHasComparisons (C : SmoothTailCertificate n) : Prop :=
  ∀ {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} {F : List (Set X')}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'},
    F.filter (fun B => decide B.Nonempty) = (E.filter (fun B => decide B.Nonempty)).map (φ ⁻¹' ·) →
    C.holds (φ ⁻¹' W) F T' → C.holds W E T →
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ T' T χ

/-- Compare complete actual mixed histories by comparing the singular
prefixes and then the smooth suffixes over their matched endpoints. -/
theorem labelled_embedded_history_emptyAware (hn : 0 < n)
    {C : SmoothTailCertificate n} (hC : SmoothTailHasComparisons C)
    {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {F : List (Set X')}
    {T : BlowupTower X Y} {S : BlowupTower X' Y'}
    (hW : W' = φ ⁻¹' W)
    (hE : F.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ F, B))
    (hS : LabelledEmbeddedHistory C W' F univ S) (hT : LabelledEmbeddedHistory C W E univ T) :
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso φ S T χ := by
  obtain ⟨A,Z,P,Q,e,L,hP,hQ,hFactor⟩ := hT.phases
  obtain ⟨A',Z',P',Q',e',L',hP',hQ',hFactor'⟩ := hS.phases
  obtain ⟨ψ,hPrefix⟩ := labelled_native_history_overlap hn φ hW hE hDense' hDense hP' hP
  obtain ⟨hCarrier,hBoundary,_,_⟩ := aligned_after_prefixes hP'.source_analytic hP.source_analytic
    hP'.source_snc hP.source_snc hDense' hDense hW hE hP'.test_and_singular.1 hP.test_and_singular.1
    hP'.test_and_singular.2 hP.test_and_singular.2 hPrefix
  rw [hCarrier] at hQ'
  rw [filter_map_bijection ψ ψ.surjective] at hBoundary
  obtain ⟨β,hTail⟩ := hC ψ hBoundary hQ' hQ
  exact compare_from_factors hFactor' (emptyAware_append_same_base_transport hPrefix hTail) hFactor

/-- The actual complete tower class used to glue the empty-initial-boundary
embedded resolution. -/
def labelledEmbeddedClass (C : SmoothTailCertificate n) {X : CMfd.{0} n} (W : Set X) : LocalTowerClass X :=
  fun U _ T => LabelledEmbeddedHistory C ((Subtype.val : U → X) ⁻¹' W) [] univ T

private theorem bmStages_to_embeddedPositions {X : CMfd.{0} n} (W : Set X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), BMStages W [] T → EmbeddedPositions W T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    refine ⟨bmStages_to_embeddedPositions W T h.1,?_⟩
    have hStage := h.2
    let M : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
    let G := geometricTemplate (univ : Set X) []
    have hE : (geoTransformAlong G T).E = (geoTransformAlong M T).E :=
      geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl T
    change BMPosition (strictTransform n T.proj W) (geoTransformAlong G T).E C at hStage
    rw [hE] at hStage
    refine ⟨?_,hStage.2⟩
    rcases hStage.1 with hSing | hBoundary
    · exact Or.inl (fun x hx => mem_singularSet_iff.mp (hSing hx))
    · exact Or.inr hBoundary

theorem labelled_embedded_class_complete {C : SmoothTailCertificate n}
    {X : CMfd.{0} n} {W : Set X} :
    ClassHasCompleteEmbeddedHistories W (labelledEmbeddedClass C W) := by
  intro U Y T h
  obtain ⟨_,hStages,hSmooth,hSNC,hNC,_,_,_,_,_,_,_,_⟩ := h.geometry
  exact completeEmbeddedHistory_of_empty_initial (bmStages_to_embeddedPositions _ T hStages) hSmooth hSNC hNC

private theorem dense_of_empty_boundary {X : Type} [TopologicalSpace X] (W : Set X) :
    W ⊆ closure (W \ ⋃ B ∈ ([] : List (Set X)), B) := by
  simpa using
    (subset_closure : W ⊆ closure W)

/-- Any two members compare on the actual intersection of their base
opens and identify the actual birth stages. -/
theorem labelled_embedded_class_physical (hn : 0 < n)
    {C : SmoothTailCertificate n} (hC : SmoothTailHasComparisons C)
    {X : CMfd.{0} n} {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) :
    HasPhysicalComparisons (labelledEmbeddedClass C W) := by
  intro U V Y Z T S hT hS
  let OU := nestedOpens U (U ⊓ V)
  let OV := nestedOpens V (U ⊓ V)
  let e := overlapBaseEquiv (n := n) (show U ⊓ V ≤ U from inf_le_left) (show U ⊓ V ≤ V from inf_le_right)
  let WU := (Subtype.val : U → X) ⁻¹' W
  let WV := (Subtype.val : V → X) ⁻¹' W
  have hTU := hT.restrictOpen (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U)
    isSNCDivisor_nil (dense_of_empty_boundary WU) OU
  have hSV := hS.restrictOpen (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V)
    isSNCDivisor_nil (dense_of_empty_boundary WV) OV
  simp only [List.map_nil,preimage_univ] at hTU hSV
  have hCarrier : (Subtype.val : OU → U) ⁻¹' WU = e ⁻¹' ((Subtype.val : OV → V) ⁻¹' WV) := by
    ext x
    change x.val.val ∈ W ↔ (e x).val.val ∈ W
    rw [overlapBaseEquiv_point]
  exact labelled_embedded_history_emptyAware hn hC e (E := []) (F := []) hCarrier rfl
    (dense_of_empty_boundary _) (dense_of_empty_boundary _) hTU hSV

/-- Prescribed compact-enclosed opens are members of the same compatible
class, so the final projection has their physical finite towers. -/
theorem labelled_embedded_class_compact_windows {m : ℕ} {C : SmoothTailCertificate (m + 1)}
    (hProduce : ProducesLocalSmoothCertificates C)
    {X : CMfd.{0} (m + 1)} {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W) :
    ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
      ∃ (Y : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) U) Y),
        labelledEmbeddedClass C W U Y T := by
  intro U K hK hUK
  simpa only [List.map_nil,labelledEmbeddedClass] using exists_labelled_embedded_history_on_compact_enclosed_open C hProduce hW
    [] isSNCDivisor_nil (dense_of_empty_boundary W) U K hK hUK

/-- Read the complete locally finite actual atlas from the certified
finite histories, retaining their global born-boundary members. -/
theorem exists_labelled_complete_embedded_atlas_of_windows {C : SmoothTailCertificate n}
    {X : CMfd.{0} n} {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (hPhysical : HasPhysicalComparisons (labelledEmbeddedClass C W))
    (hWindows : ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), labelledEmbeddedClass C W U Y T) :
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      CompleteEmbeddedAtlas W (labelledEmbeddedClass C W) P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (labelledEmbeddedClass C W) Z P, c.U = U) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (labelledEmbeddedClass C W) Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
        (⋃ j, B j) = P ⁻¹' singularSet (n := n) W ∧
        HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  have hCover : Covers (labelledEmbeddedClass C W) := by
    have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    let L := CompactExhaustion.choice X
    intro x
    obtain ⟨k,hx⟩ := L.exists_mem x
    let U : Opens X := ⟨interior (L (k+1)),isOpen_interior⟩
    obtain ⟨Y,T,hT⟩ := hWindows U (L (k+1)) (L.isCompact (k+1)) interior_subset
    exact ⟨U,L.subset_interior_succ k hx,Y,T,hT⟩
  obtain ⟨Z,P,h⟩ := exists_glued_complete_embedded_atlas hW hCover
    (physical_comparisons_to_comparisons hPhysical) labelled_embedded_class_complete
  refine ⟨Z,P,h,?_,complete_embedded_atlas_indexed_boundary h hPhysical hWindows⟩
  intro U K hK hUK
  obtain ⟨Y,T,hT⟩ := hWindows U K hK hUK
  exact ⟨chartOfMember (physical_comparisons_to_comparisons hPhysical) T hT h.glued.2.2.2
    h.glued.1.continuous,rfl⟩

/-- The supplied local certificate service and physical comparison
produce the same complete glued atlas. -/
theorem exists_labelled_complete_embedded_atlas {m : ℕ} {C : SmoothTailCertificate (m + 1)}
    (hProduce : ProducesLocalSmoothCertificates C) (hC : SmoothTailHasComparisons C)
    {X : CMfd.{0} (m + 1)} {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W) :
    ∃ (Z : CMfd.{0} (m + 1)) (P : Z → X),
      CompleteEmbeddedAtlas W (labelledEmbeddedClass C W) P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (labelledEmbeddedClass C W) Z P, c.U = U) ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (labelledEmbeddedClass C W) Z P, Ex.W k = c.V ∧ Ex.B k = bornChartBoundary c) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m + 1) B ∧ (∀ j, (B j).Nonempty) ∧
        (⋃ j, B j) = P ⁻¹' singularSet (n := m + 1) W ∧
        HasNormalCrossingsWithBoundary (strictTransform (m + 1) P W) B :=
  exists_labelled_complete_embedded_atlas_of_windows hW
    (labelled_embedded_class_physical (Nat.succ_pos m) hC hW)
    (labelled_embedded_class_compact_windows hProduce hW)

end
end Hironaka.HironakaG8LabelledEmbeddedAtlas
