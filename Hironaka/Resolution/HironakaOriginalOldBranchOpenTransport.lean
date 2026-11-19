import Hironaka.Resolution.HironakaOriginalOldBranchThroughPoint
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Resolution.HironakaBaseChange

set_option autoImplicit false

/-!
# The same reverse open extension retains every original branch presentation

The actual nested-open tower isomorphisms identify the two restrictions to
an intersection. Arbitrary original branch lists are pulled back literally;
cosupport-covering reflection then recovers their ambient test histories.
There is no compactness hypothesis on any original branch chart.

Blueprint: `hir:original-old-branch-reverse-open-universal-history`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings GermIdealPullbackCalculus
  MaxLocusLocal StepOneTangentChange HironakaBaseChange HomogenizedGlueingTower BlowupRestrictOpen

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem pullback_id_coherent {A : Type u} [TopologicalSpace A]
    [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A] (M : MarkedIdeal n A)
    (hI : M.ideal.IsCoherent) : MarkedIdeal.pullback (id : A → A) M = M :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (show M.E.map (fun C => (id : A → A) ⁻¹' C) = M.E by simp)
    (BlowupControlledTransform.pullback_id hI) rfl

/-- The same literal branch list on a smaller open pulls back through the actual
nested-open identification, together with the entire retained boundary. -/
theorem pullback_nested_added_boundary (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    {U K : Opens X} (hKU : K ≤ U) (B : List (Set K)) :
    let L := nestedOpens U K
    let φ := nestedOpensDiffeo (n := n) hKU
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    let MK := MarkedIdeal.pullback (Subtype.val : K → X) M
    MarkedIdeal.pullback φ ({ MK with E := B ++ MK.E } : MarkedIdeal n K) =
      ({ MarkedIdeal.pullback (Subtype.val : L → U) MU with
        E := B.map (φ ⁻¹' ·) ++ (MarkedIdeal.pullback (Subtype.val : L → U) MU).E } :
          MarkedIdeal n L) := by
  dsimp only
  have hBase := pullback_val_pullback_val (𝔪 := M) hI hKU
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (congrArg (fun A => A.N) hBase).symm ?_
    (congrArg (fun A => A.ideal) hBase).symm
    (congrArg (fun A => A.d) hBase).symm
  change (B ++ (MarkedIdeal.pullback (Subtype.val : K → X) M).E).map
      ((nestedOpensDiffeo (n := n) hKU) ⁻¹' ·) = _
  rw [List.map_append]
  congr 1
  exact (congrArg (fun A => A.E) hBase).symm

/-- Actual nested-open tower comparison transports an added original list without
supplying any ambient or terminal augmented-history certificate. -/
theorem isGeoTestTower_nested_added_boundary_iff (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    {U K : Opens X} (hKU : K ≤ U) (B : List (Set K))
    {Y : CMfd.{u} n} (Q : BlowupTower X Y) :
    let L := nestedOpens U K
    let φ := nestedOpensDiffeo (n := n) hKU
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    let MK := MarkedIdeal.pullback (Subtype.val : K → X) M
    IsGeoTestTower
      ({ MarkedIdeal.pullback (Subtype.val : L → U) MU with
        E := B.map (φ ⁻¹' ·) ++ (MarkedIdeal.pullback (Subtype.val : L → U) MU).E } :
          MarkedIdeal n L) (restrict L (restrict U Q)) ↔
      IsGeoTestTower ({ MK with E := B ++ MK.E } : MarkedIdeal n K) (restrict K Q) := by
  dsimp only
  rw [← pullback_nested_added_boundary M hI hKU B]
  exact IsTowerIso.isGeoTestTower_iff (nestedOpensDiffeo (n := n) hKU)
    (isClosedSubmanifold_preimage_val hN K)
    (isCoherent_pullback contMDiff_subtype_val hI)
    (isTowerIso_restrict_nestedOpens hKU Q)

/-- A genuine tower isomorphism over the identity transports the universal original
branch property on the same original base. -/
theorem isOriginalBranchTestTower_of_towerIso_refl (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) {H : Set X}
    {Y Z : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) S T χ)
    (hS : IsOriginalBranchTestTower M H S) : IsOriginalBranchTestTower M H T := by
  intro V B hSNC hUnion
  let A : MarkedIdeal n V :=
    { MarkedIdeal.pullback (Subtype.val : V → X) M with
      E := B ++ (MarkedIdeal.pullback (Subtype.val : V → X) M).E }
  have hNA : IsClosedSubmanifold n A.N := isClosedSubmanifold_preimage_val hN V
  have hIA : A.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hMatch : ∀ q : X, q ∈ V ↔
      Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞ q ∈ V := fun _ => Iff.rfl
  have hLast := isTowerIso_mem_openPreimage_iff hIso hMatch
  have hV := isTowerIso_restrictOpens hMatch hIso hLast
  apply (IsTowerIso.isGeoTestTower_iff
    (diffeoOpens (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) V V hMatch) hNA hIA hV).mp
  change IsGeoTestTower (MarkedIdeal.pullback (id : V → V) A) (restrict V S)
  rw [pullback_id_coherent A hIA]
  exact hS V B hSNC hUnion

private theorem preimage_list_union {A B : Type*} (f : A → B) (L : List (Set B)) :
    f ⁻¹' (⋃ C ∈ L, C) = ⋃ C ∈ L.map (f ⁻¹' ·), C := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨f ⁻¹' C, List.mem_map.mpr ⟨C, hC, rfl⟩, hxC⟩
  · intro hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact mem_iUnion₂.mpr ⟨D, hD, hxC⟩

/-- Universal original-branch histories reflect from the actual restriction to an open
covering the entire original cosupport. An arbitrary branch chart need not be compact. -/
theorem isOriginalBranchTestTower_of_restrict_cosupport_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) {H : Set X}
    (U : Opens X) (hU : M.cosupp ⊆ U) {Y : CMfd.{u} n} (Q : BlowupTower X Y)
    (hQ : IsGeoTestTower M Q)
    (hHistory : IsOriginalBranchTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M)
      ((Subtype.val : U → X) ⁻¹' H) (restrict U Q)) :
    IsOriginalBranchTestTower M H Q := by
  classical
  intro W B hSNC hUnion
  let K : Opens X := U ⊓ W
  have hKU : K ≤ U := inf_le_left
  have hKW : K ≤ W := inf_le_right
  let LU := nestedOpens U K
  let LW := nestedOpens W K
  let φU := nestedOpensDiffeo (n := n) hKU
  let φW := nestedOpensDiffeo (n := n) hKW
  let jW : K → W := fun q => ⟨q.val, hKW q.property⟩
  let f : LU → W := fun q => jW (φU q)
  let BK := B.map (jW ⁻¹' ·)
  let BL := BK.map (φU ⁻¹' ·)
  let MW := MarkedIdeal.pullback (Subtype.val : W → X) M
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let ML := MarkedIdeal.pullback (Subtype.val : LU → U) MU
  have hf : IsOpenHoloEmbedding n f := by
    obtain ⟨O, ψ, hψ⟩ :=
      (isOpenHoloEmbedding_val (n := n) K).codRestrict W (fun q => hKW q.property)
    exact ⟨O, φU.trans ψ, fun q => hψ (φU q)⟩
  have hBL : BL = B.map (f ⁻¹' ·) := by
    change (B.map (jW ⁻¹' ·)).map (φU ⁻¹' ·) = _
    rw [List.map_map]
    rfl
  have hSNCL : IsSNCDivisor n (BL ++ ML.E) := by
    have hPull := hf.isSNCDivisor_map_preimage hSNC
    rw [List.map_append] at hPull
    have hE : (MarkedIdeal.pullback (Subtype.val : W → X) M).E.map (f ⁻¹' ·) = ML.E := by
      change (M.E.map ((Subtype.val : W → X) ⁻¹' ·)).map (f ⁻¹' ·) =
        (M.E.map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : LU → U) ⁻¹' ·)
      rw [List.map_map, List.map_map]
      rfl
    rw [← hBL, hE] at hPull
    exact hPull
  have hUnionL : (Subtype.val : LU → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' H) =
      ⋃ C ∈ BL, C := by
    change f ⁻¹' ((Subtype.val : W → X) ⁻¹' H) = _
    rw [hUnion, preimage_list_union, ← hBL]
  have hTestL := hHistory LU BL hSNCL hUnionL
  have hTestK := (isGeoTestTower_nested_added_boundary_iff M hN hI hKU BK Q).mp hTestL
  have hTestLW := (isGeoTestTower_nested_added_boundary_iff M hN hI hKW BK Q).mpr hTestK
  have hBW : BK.map (φW ⁻¹' ·) = B.map ((Subtype.val : LW → W) ⁻¹' ·) := by
    change (B.map (jW ⁻¹' ·)).map (φW ⁻¹' ·) = _
    rw [List.map_map]
    rfl
  have hAugLocal : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : LW → W)
      ({ MW with E := B ++ MW.E } : MarkedIdeal n W)) (restrict LW (restrict W Q)) := by
    rw [pullback_add_old_boundary (X := CMfd.of (n := n) W) MW B LW]
    simpa only [← hBW] using hTestLW
  have hNMW : IsClosedSubmanifold n MW.N := isClosedSubmanifold_preimage_val hN W
  have hIMW : MW.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hI
  have hCoverW : MW.cosupp ⊆ LW := by
    intro w hw
    rw [cosupp_pullback_val M
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg) W]
      at hw
    exact ⟨hU hw, w.property⟩
  exact isGeoTestTower_of_restrict_cosupport_cover (X := CMfd.of (n := n) W)
    MW hNMW hIMW (B ++ MW.E) LW hCoverW
    (restrict W Q) (isGeoTestTower_restrict W hN hI Q hQ) hAugLocal

/-- The SAME actual prescribed reverse open extension produces universal original-branch
testness from the recursively produced open history and its actual whole-tower isomorphism. -/
theorem isOriginalBranchTestTower_of_open_extension (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) {H : Set X}
    (U : Opens X) (hU : M.cosupp ⊆ U) {Y Z : CMfd.{u} n} (Q : BlowupTower X Y)
    (hQ : IsGeoTestTower M Q) (S : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage Q U)
    (hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞) S (restrict U Q) e)
    (hHistory : IsOriginalBranchTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M)
      ((Subtype.val : U → X) ⁻¹' H) S) : IsOriginalBranchTestTower M H Q := by
  apply isOriginalBranchTestTower_of_restrict_cosupport_cover M hN hI U hU Q hQ
  exact isOriginalBranchTestTower_of_towerIso_refl _
    (isClosedSubmanifold_preimage_val hN U)
    (isCoherent_pullback contMDiff_subtype_val hI) hIso hHistory

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
