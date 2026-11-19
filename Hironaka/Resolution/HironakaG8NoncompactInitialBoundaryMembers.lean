import Hironaka.Resolution.HironakaG8NoncompactInitialBoundaryAtlas
import Hironaka.Resolution.HironakaG8CompleteEmbeddedAtlasBoundary

/-! Global SNC members of the full ordered initial-boundary atlas. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NoncompactInitialBoundaryMembers
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic NormalCrossings NormalCrossingsInvariance
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3RChartOfMember
  HironakaG3GenericBornChartOverlap G3UniversePhysicalClassComparisons
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8LocalMixedPhaseAssembly
  HironakaG8LabelledEmbeddedTape HironakaG8UniverseDenseBoundary
  HironakaG4SharpTerminalAtlas HironakaG8SurfaceLimitEndpoint
  HironakaSharpActualFiniteChronologicalHistory HironakaG34NonPureLowDim
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3REmbeddedGlobalSNC HironakaG3REmbeddedNC Hironaka.HolomorphicIdealSheaves
  MarkedIdealTowerTransport HironakaCoherentTransformExtension
  HironakaG8LabelledEmbeddedAtlas HironakaG8OrderedSmoothSuffix
  HironakaG8LocalMixedSmoothCleanup HironakaG8LocalMixedEmbeddedResolution
  HironakaResolutionSpaceLocal

theorem initial_boundary_chart_geometry {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    {E : List (Set X)} {C : SmoothTailCertificate n} {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (initialBoundaryClass C W E) Z P) :
    IsSNCDivisor n ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
      ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  let M := geometricTemplate (univ : Set X) E
  have hList := chartBoundary_map_val c M
  have hCarrier : (Subtype.val : c.V → Z) ⁻¹' strictTransform n P W =
      c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
    rw [strictTransform_chart c hP W]
    ext z
    change z.val ∈ strictTransform n P W ↔ chartIncl c (c.φ.symm z) ∈ strictTransform n P W
    rw [chartIncl_symm]
  have hE : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : c.U → X) M) c.T).E =
      (geoTransformAlong (⟨univ,E.map ((Subtype.val : c.U → X) ⁻¹' ·),
        vanishingIdeal (n := n) ((Subtype.val : c.U → X) ⁻¹' W),1⟩ :
        MarkedIdeal n c.U) c.T).E := by
    apply geoTransformAlong_E_eq_of_E_eq
    rfl
  rw [hE] at hList
  change (fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·) = _ at hList
  rw [hList,hCarrier]
  exact ⟨(isSNCDivisor_map_preimage_iff c.φ.symm).mpr c.mem.geometry.2.2.2.1,
    (hasNormalCrossings_preimage_iff c.φ.symm).mpr c.mem.geometry.2.2.2.2.1⟩

/-- The exact old-and-born chart boundaries give one globally locally
finite indexed SNC divisor on the same proper ambient map. -/
theorem initial_boundary_atlas_indexed_members {n : ℕ} {X Z : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} {C : SmoothTailCertificate n} {P : Z → X}
    (hE : IsSNCDivisor n E) (hG : IsGluedFrom (initialBoundaryClass C W E) Z P)
    (hPhysical : HasPhysicalComparisons (initialBoundaryClass C W E))
    (hWindows : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), initialBoundaryClass C W E U Y T) :
    ∃ Ex : SNCExhaustion Z,
      (∀ k, ∃ c : TowerChart (initialBoundaryClass C W E) Z P,
        Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E) ∧
      let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
      IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let L := CompactExhaustion.choice X
  let U (k : ℕ) : Opens X := ⟨interior (L (k+1)),isOpen_interior⟩
  choose Y T hT using fun k : ℕ => hWindows (U k) (L (k+1)) (L.isCompact (k+1)) interior_subset
  let c (k : ℕ) := chartOfMember (physical_comparisons_to_comparisons hPhysical) (T k) (hT k)
    hG.2.2.2 hG.1.continuous
  have hUmono {j k : ℕ} (hjk : j ≤ k) : (c j).U ≤ (c k).U :=
    interior_mono (L.subset (Nat.succ_le_succ hjk))
  have hVmono {j k : ℕ} (hjk : j ≤ k) : ((c j).V : Set Z) ⊆ (c k).V := by
    intro z hz
    apply (c k).mem_V
    apply hUmono hjk
    rw [(c j).V_eq] at hz
    exact hz
  have hCover (z : Z) : ∃ k, z ∈ (c k).V := by
    obtain ⟨k,hk⟩ := L.exists_mem (P z)
    exact ⟨k,(c k).mem_V (L.subset_interior_succ k hk)⟩
  have hSub {k : ℕ} {H : Set Z} (hH : H ∈ fullChartBoundary (c k) E) : H ⊆ (c k).V := by
    obtain ⟨D,_,rfl⟩ := List.mem_map.mp hH
    rintro _ ⟨y,_,rfl⟩
    exact ((c k).φ y).property
  have hNested {j k : ℕ} (hjk : j ≤ k) :
      ((fullChartBoundary (c k) E).map (· ∩ ((c j).V : Set Z))).filter
        (fun H => decide H.Nonempty) = (fullChartBoundary (c j) E).filter (fun H => decide H.Nonempty) := by
    have hov := initial_boundary_chart_overlap hE hPhysical (c j) (c k)
    have hPre : P ⁻¹' ((((c j).U ⊓ (c k).U : Opens X) : Set X)) = ((c j).V : Set Z) := by
      rw [inf_eq_left.mpr (hUmono hjk),(c j).V_eq]
    have hSelf : (fullChartBoundary (c j) E).map (· ∩ ((c j).V : Set Z)) = fullChartBoundary (c j) E := by
      conv_rhs => rw [← List.map_id (fullChartBoundary (c j) E)]
      exact List.map_congr_left fun _ hH => inter_eq_left.mpr (hSub hH)
    rw [hPre,hSelf] at hov
    exact hov.symm
  let Ex : SNCExhaustion Z :=
    { W := fun k => (c k).V
      B := fun k => fullChartBoundary (c k) E
      mono := hVmono
      cover := hCover
      sub := hSub
      snc := fun k => (initial_boundary_chart_geometry hG.1 (c k)).1
      nested := hNested }
  have hC (k : ℕ) : ∃ c : TowerChart (initialBoundaryClass C W E) Z P, Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E :=
    ⟨c k,rfl,rfl⟩
  refine ⟨Ex,hC,⟨Ex.locallyFinite_globalMember,fun i => Ex.isClosed_globalMember i.2,
    Ex.coordinates_globalMember⟩,fun i => i.2.1,?_⟩
  apply SNCExhaustion'.hasNormalCrossingsWithBoundary Ex
  intro k
  exact (initial_boundary_chart_geometry hG.1 (c k)).2


/-- A proper embedded-resolution atlas with all original and born
boundary members on that same ambient manifold. -/
theorem exists_locally_finite_initial_boundary_resolution
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P, c.U = U) ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
          Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m+1) B ∧ (∀ j, (B j).Nonempty) ∧
        HasNormalCrossingsWithBoundary (strictTransform (m+1) P W) B := by
  obtain ⟨Z,P,hG,hWindow,hSmooth,hIso⟩ := exists_locally_finite_initial_boundary_atlas hW hE hDense
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate (m+1)) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange (m+2)) hB hT' hT
  have hProduce : ProducesLocalSmoothCertificates (ascending_smooth_tail_certificate (m+1)) := by
    intro A A₀ hSmooth E hE hDense L hL
    exact local_mixed_smooth_boundary_cleanup_ordered hSmooth E hE hDense L hL
  exact ⟨Z,P,hG,hWindow,hSmooth,hIso,initial_boundary_atlas_indexed_members hE hG
    (initial_boundary_class_physical (Nat.succ_pos m) hC hW hE hDense)
    (initial_boundary_class_compact_windows hProduce hW hE hDense)⟩

end
end Hironaka.HironakaG8NoncompactInitialBoundaryMembers
