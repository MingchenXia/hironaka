import Hironaka.Resolution.HironakaG8LocalPureFinish
import Hironaka.Resolution.HironakaG8NativeRelativePhase

/-! Finite relative embedded resolution of a pure analytic carrier with an
initial SNC boundary whose complement is dense in the carrier. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LocalPureEmbeddedResolution

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport MaxLocusLocal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaEmbeddedBoundary NormalCrossings NormalCrossingsInvariance HironakaBaseChange
  HironakaG8UniverseBMTransport HironakaG8UniverseDenseBoundary HironakaG8LocalPureFinish
  HironakaG8NativeRelativePhase HironakaActualSmoothBoundaryCleanup HironakaG3CentresOverGenericFactor
  HironakaMixedDimensionalBoundaryFiniteResolution HironakaSharpActualFiniteChronologicalHistory
  HironakaCoherentTransformExtension HironakaNormalCrossingsSeparationChoiceComparison

/-- The resolution predicate is invariant under physical rebasing of the
same finite tower by a given ambient biholomorphism. -/
theorem dense_boundary_resolution_rebase {n : ℕ} {X X' Y : CMfd.{0} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (T : BlowupTower X Y) (h : DenseBoundaryResolution W E T) :
    DenseBoundaryResolution (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower := by
  obtain ⟨hAdm, hStages, hSmooth, hSNC, hNC, _, _, _, _, _, _, _, _⟩ := h
  let R := transport e T
  let W' := e ⁻¹' W
  let E' := E.map (e ⁻¹' ·)
  let M := actualSmoothBoundaryMarked W E
  let M' := actualSmoothBoundaryMarked (X := X') W' E'
  let G := geometricTemplate (univ : Set X) E
  let G' := geometricTemplate (univ : Set X') E'
  let A' := strictTransform n R.tower.proj W'
  let B' := (geoTransformAlong M' R.tower).E
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let F' := singularSet (n := n) W' ∪ (W' ∩ ⋃ H ∈ E', H)
  have hF : F' = e ⁻¹' F := by
    dsimp only [F', F, W', E']
    rw [HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism e),
      ← preimage_biUnion_list, preimage_union, preimage_inter]
  have hA' : A' = R.back ⁻¹' strictTransform n T.proj W :=
    strictTransform_preimage_of_square e R.back R.tower.contMDiff_proj T.contMDiff_proj W hW.isClosed
      (fun z => (proj_transport e T z).symm)
  have hB' : B' = (geoTransformAlong M T).E.map (R.back ⁻¹' ·) := by
    change (geoTransformAlong M' R.tower).E = _
    rw [geoTransformAlong_E_eq_of_E_eq (𝔍 := M') (𝔪 := G') rfl R.tower, rebase_bm_boundary_eq e W E hE T hStages]
    rw [geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl T]
  have hStages' : BMStages W' E' R.tower := rebase_bm_stages e W E hE T hStages
  have hOver : CentresOver F T := by
    apply centresOver_of_exceptionalDivisor_support_subset F T
    rw [HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M hE.1 T]
    exact (IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hAdm).2
  have hOver' : CentresOver F' R.tower := hF.symm ▸ centresOver_rebase e F T hOver
  have hAdm' : IsAdmissibleBlowupSequence n X' E' F' R.target R.tower.proj B' := by
    have h := isAdmissibleBlowupSequence_proj G' F' R.tower (bm_stage_test W' E' R.tower hStages') hOver'
    rw [geoTransformAlong_E_eq_of_E_eq (𝔍 := G') (𝔪 := M') rfl R.tower] at h
    exact h
  have hSmooth' : IsClosedSubmanifold n A' := hA'.symm ▸ (isClosedSubmanifold_preimage_iff R.back).mpr hSmooth
  have hSNC' : IsSNCDivisor n B' := hB'.symm ▸
    isSNCDivisor_map_preimage (pullsBackCoordinates R.back) R.back.continuous hSNC
  have hNC' : HasNormalCrossings n A' B' := by
    rw [hA', hB']
    exact hasNormalCrossings_preimage (pullsBackCoordinates R.back) hNC
  have hW' := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage e.contMDiff hW
  have hE' := isSNCDivisor_map_preimage (pullsBackCoordinates e) e.continuous hE
  have hDense' : W' ⊆ closure (W' \ ⋃ H ∈ E', H) := by
    dsimp only [W', E']
    rw [← preimage_biUnion_list, ← preimage_sdiff]
    intro x hx
    have hh := e.toHomeomorph.preimage_closure (W \ ⋃ H ∈ E, H)
    exact (Set.ext_iff.mp hh x).mp (hDense hx)
  exact dense_boundary_resolution_of_final_normalCrossings hW' E' hE' hDense'
    R.tower hStages' hAdm' hSmooth' hSNC' hNC'


/-- A finite embedded resolution on a nested source open gives one on its
literal ambient image, preserving every field of the endpoint. -/
theorem flatten_local_dense_boundary_resolution
    {n : ℕ} {X : CMfd.{0} n} {W K : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (V : Opens X) (hKV : K ⊆ V) (U : Opens V)
    (hKU : (Subtype.val : V → X) ⁻¹' K ⊆ U)
    {Z : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hT : DenseBoundaryResolution
      ((Subtype.val : U → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W))
      ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : U → V) ⁻¹' ·)) T) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} n) (J : BlowupTower (CMfd.of (n := n) O) Z),
      DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) J := by
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
  have hDenseV := dense_complement_restrict W E hDense V
  let O : Opens X := ⟨(Subtype.val : V → X) '' (U : Set V), V.isOpen.isOpenMap_subtype_val _ U.isOpen⟩
  have hOV : O ≤ V := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hVU (x : V) : x ∈ U ↔ x.val ∈ O :=
    ⟨fun hx => ⟨x,hx,rfl⟩, fun ⟨p,hp,he⟩ => (Subtype.ext he : p = x) ▸ hp⟩
  let e := (nestedDiffeo (n := n) V U O hVU hOV).symm
  let R := transport e T
  let WU := (Subtype.val : U → V) ⁻¹' WV
  let EU := EV.map ((Subtype.val : U → V) ⁻¹' ·)
  have hWU := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWV U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hEV
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU, H) := dense_complement_restrict WV EV hDenseV U
  have hRebase := dense_boundary_resolution_rebase e hWU EU hEU hDenseU T hT
  have hList : EU.map (e ⁻¹' ·) = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    dsimp only [EU, EV]
    rw [List.map_map, List.map_map]
    rfl
  rw [hList] at hRebase
  refine ⟨O, ?_, R.target, R.tower, hRebase⟩
  exact fun x hx => ⟨⟨x, hKV hx⟩, hKU hx, rfl⟩


set_option maxHeartbeats 1000000 in
/-- Every compact subset of the original ambient has an open neighbourhood
with one actual finite pure embedded resolution and its full SNC boundary. -/
theorem exists_local_pure_embedded_resolution_of_dense_boundary_complement
    {m d : ℕ} {X : CMfd.{0} (m + 1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (hPure : W ⊆ closure (regularLocus (n := m + 1) W d)) (hd : d < m + 1)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) O) Z),
      DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) T := by
  let n := m + 1
  obtain ⟨V, hKV, Y, S, hS, hStage, hSmooth⟩ :=
    exists_native_singular_resolution_near_compact (Nat.succ_pos m) hW E hE hDense K hK
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let KV := (Subtype.val : V → X) ⁻¹' K
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
  have hKVC : IsCompact KV := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hKV]
    exact hK
  have hPureV : WV ⊆ closure (regularLocus (n := n) WV d) := by
    have hReg : regularLocus (n := n) WV d = (Subtype.val : V → X) ⁻¹' regularLocus (n := n) W d := by
      ext x
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff
    rw [hReg]
    intro x hx
    have hh := V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      (continuous_subtype_val : Continuous (Subtype.val : V → X)) (regularLocus (n := n) W d)
    exact (Set.ext_iff.mp hh x).mp (hPure hx)
  have hDenseV : WV ⊆ closure (WV \ ⋃ H ∈ EV, H) := dense_complement_restrict W E hDense V
  obtain ⟨U, hKU, Z, T, hT⟩ := exists_local_pure_finish_of_singular_history (X := CMfd.of (n := n) V)
    hWV hPureV hd EV hEV hDenseV S hS hStage hSmooth KV hKVC
  exact flatten_local_dense_boundary_resolution hW E hE hDense V hKV U hKU T hT

end
end Hironaka.HironakaG8LocalPureEmbeddedResolution
