import Hironaka.Resolution.HironakaG4FullBoundaryCompactCleanup
import Hironaka.Resolution.HironakaBoundaryContainedSharpBad
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

/-! A finite full-boundary finish for an actual compact singular-centred history. -/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompactSharpFinish

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms RestrictEmptyTower HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaEmbeddedAnalytic
  HironakaStageCenters HironakaAdmissibleSequence HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaBoundaryContainedSharpBad
  HironakaHypersurfaceMultiplicityDescent HironakaG8IntrinsicSingularBlockSchedule
  MarkedIdealRestrictOpen MarkedIdealOpenBiholomorphism HironakaSharpActualFiniteChronologicalHistory

private theorem sharp_suffix_positions {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosedSubmanifold n W) (E : List (Set X))
    (M : MarkedIdeal n X) (hME : M.E = E)
    (O : Opens X) (hDense : W ⊆ closure (W ∩ (O : Set X))) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
      CurrentSharpCentres W E T → CentresAvoid O T →
      StageCentres (fun P C =>
        (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
          C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈
            (geoTransformAlong M P).E, H) ∧
        HasNormalCrossings n C (geoTransformAlong M P).E) T
  | _, .refl, _, _, _, _ => trivial
  | _, .step P C π hπ, hCarrier, hBoundary, hSharp, hAvoid => by
    refine ⟨sharp_suffix_positions hW E M hME O hDense P hCarrier.1 hBoundary.1 hSharp.1 hAvoid.1, ?_⟩
    have hClosed := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := geometricTemplate W []) hW IdealWeightPowers.isCoherent_unitIdeal P hCarrier.1).1
    rw [N_geoTransformAlong] at hClosed
    change IsClosedSubmanifold n (strictAlong P W) at hClosed
    have hLoc := hSharp.2.trans (originalSharpBadLocus_subset_boundary hClosed)
    have hStrict := HironakaActualSmoothBoundaryCleanup.strictAlong_eq_library_of_avoid
      W hW.1 O hDense P hAvoid.1
    rw [hStrict] at hClosed hLoc
    dsimp only
    rw [boundary_geoTransformAlong_eq_of_boundary_eq M
      (geometricTemplate (univ : Set X) E) hME P]
    exact ⟨⟨hClosed, hLoc⟩, hBoundary.2.2.2⟩

theorem singular_positions_with_boundary {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsGeoTestTower M T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      StageCentres (fun P C =>
        C ⊆ {x | x ∈ strictTransform n P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := n) (strictTransform n P.proj W) x k} ∧
        HasNormalCrossings n C (geoTransformAlong M P).E) T
  | _, .refl, _, _ => trivial
  | _, .step P _ _ _, hTest, hS =>
    ⟨singular_positions_with_boundary W M P hTest.1 hS.1,
      fun _ hx => mem_singularSet_iff.mp (hS.2 hx), hTest.2.2.2⟩

/-- Once an actual compact singular-centred prefix has a smooth strict
transform, a finite sharp suffix prepares its full accumulated boundary. -/
theorem exists_compact_singular_history_with_snc_finish {m : ℕ} {X Y : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E)
    (hK : IsCompact (singularSet (n := m + 1) W ∪ (W ∩ ⋃ H ∈ E, H)))
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩ : MarkedIdeal (m + 1) X) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) T)
    (hSmooth : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W)) :
    ∃ (Z : CMfd.{0} (m + 1)) (R : BlowupTower Y Z),
      let U := T.append R
      let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩
      let F := singularSet (n := m + 1) W ∪ (W ∩ ⋃ H ∈ E, H)
      let WU := strictTransform (m + 1) U.proj W
      let EU := (geoTransformAlong M U).E
      IsAdmissibleBlowupSequence (m + 1) X E F Z U.proj EU ∧
      StageCentres (fun P C =>
        (C ⊆ {x | x ∈ strictTransform (m + 1) P.proj W ∧
          ∀ k, ¬ RegularAtDim (n := m + 1) (strictTransform (m + 1) P.proj W) x k} ∨
        (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj W) ∧
          C ⊆ strictTransform (m + 1) P.proj W ∩ ⋃ H ∈ (geoTransformAlong M P).E, H)) ∧
          HasNormalCrossings (m + 1) C (geoTransformAlong M P).E) U ∧
      IsClosedSubmanifold (m + 1) WU ∧ IsSNCDivisor (m + 1) EU ∧ HasNormalCrossings (m + 1) WU EU ∧
      IsProperMap U.proj ∧ Surjective U.proj ∧ IsIsomorphismOver (m + 1) U.proj Fᶜ ∧
      (E = [] → exceptionalLocus (m + 1) U.proj = U.proj ⁻¹' singularSet (n := m + 1) W) := by
  let M : MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, 1⟩
  let S := strictTransform (m + 1) T.proj W
  let ET := (geoTransformAlong M T).E
  let C := geometricTemplate (univ : Set Y) ET
  let F := singularSet (n := m + 1) W ∪ (W ∩ ⋃ H ∈ E, H)
  let B := originalSharpBadLocus (n := m + 1) S ET
  let O₀ : Opens X := ⟨(singularSet (n := m + 1) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hOverSing : CentresOver (singularSet (n := m + 1) W) T := by
    simpa [O₀] using centresOver_compl_of_centresAvoid O₀ T
      (intrinsic_singular_history_avoids_regular_open hW O₀ disjoint_compl_right T hStage)
  have hAdmT := isAdmissibleBlowupSequence_proj M _ T hTest hOverSing
  have hWF : M.IsWellFormed :=
    ⟨isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET : IsSNCDivisor (m + 1) ET := (isWellFormed_geoTransformAlong hWF T hTest).isSNCDivisor
  have hTailSupport : B ⊆ T.proj ⁻¹' F := by
    intro y hy
    obtain ⟨hyS, hyE⟩ := originalSharpBadLocus_subset_boundary hSmooth hy
    have hyW := HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hyS
    rcases HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hAdmT hE.1 hyE with hyOld | hySing
    · exact Or.inr ⟨hyW, hyOld⟩
    · exact Or.inl hySing
  have hBK : IsCompact B :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
      (isClosed_originalSharpBadLocus hSmooth.1 hET.1) hTailSupport
  obtain ⟨Z, R, hRcarrier, hRboundary, hRsharp, hROver, hRSmooth, hRE, hRNC, _, _⟩ :=
    HironakaG4FullBoundaryCompactCleanup.exists_actual_compact_sharp_cleanup_full_boundary
      (Nat.succ_pos m) hSmooth hET hBK
  let O : Opens Y := ⟨Bᶜ, (isClosed_originalSharpBadLocus hSmooth.1 hET.1).isOpen_compl⟩
  have hSDense : S ⊆ closure (S ∩ (O : Set Y)) := by
    intro x hx
    apply mem_closure_iff.mpr
    intro V hV hxV
    by_contra hNo
    have hSub : V ∩ S ⊆ B := by
      rintro y ⟨hyV, hyS⟩
      by_contra hyB
      exact hNo ⟨y, hyV, hyS, hyB⟩
    have hEmpty := (original_sharp_bad_analytic_and_thin hSmooth hET).2 V hV hSub
    have hxBoth : x ∈ V ∩ S := ⟨hxV, hx⟩
    rw [hEmpty] at hxBoth
    exact hxBoth
  have hRAvoid := centresAvoid_of_centresOver O (F := B) disjoint_compl_left R hROver
  let MS : MarkedIdeal (m + 1) Y := ⟨univ, ET, vanishingIdeal (n := m + 1) S, 1⟩
  have hPositions := sharp_suffix_positions hSmooth ET MS rfl O hSDense R hRcarrier hRboundary hRsharp hRAvoid
  have hPositionsAll := stageCentres_embedded_position_append W E T R
    (singular_positions_with_boundary W M T hTest hStage) hPositions
  have hAdmTF := hAdmT.mono (show singularSet (n := m + 1) W ⊆ F from subset_union_left)
  have hAdmR := (isAdmissibleBlowupSequence_proj C B R hRboundary hROver).mono hTailSupport
  have hFinalE : (geoTransformAlong M (T.append R)).E = (geoTransformAlong C R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_eq_of_boundary_eq (geoTransformAlong M T) C rfl R
  have hFinalAdm : IsAdmissibleBlowupSequence (m + 1) X E F Z (T.append R).proj
      (geoTransformAlong M (T.append R)).E := by
    rw [BlowupTower.proj_append, hFinalE]
    exact HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.comp hAdmTF hAdmR
  have hStrict := StrictTransformComposition.strictTransform_comp T.contMDiff_proj R.contMDiff_proj W
  rw [← BlowupTower.proj_append] at hStrict
  have hRS := HironakaActualSmoothBoundaryCleanup.strictAlong_eq_library_of_avoid S hSmooth.1 O hSDense R hRAvoid
  rw [N_geoTransformAlong] at hRSmooth hRNC
  change IsClosedSubmanifold (m + 1) (strictAlong R S) at hRSmooth
  change HasNormalCrossings (m + 1) (strictAlong R S) (geoTransformAlong C R).E at hRNC
  change IsSNCDivisor (m + 1) (geoTransformAlong C R).E at hRE
  rw [hRS, ← hStrict] at hRSmooth hRNC
  rw [← hFinalE] at hRE hRNC
  have hIso := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hFinalAdm
  refine ⟨Z, R, hFinalAdm, hPositionsAll, hRSmooth, hRE, hRNC,
    HironakaLocalPrincipalization.isProperMap_proj _,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective (T.append R).isBlowupSequence, hIso, ?_⟩
  intro hEmpty
  have hF : F = singularSet (n := m + 1) W := by simp [F, hEmpty]
  rw [hF] at hIso
  exact HironakaG8SurfaceLimitEndpoint.exceptionalLocus_eq_singular_preimage W hW.isClosed _
    (T.append R).contMDiff_proj hIso hRSmooth

end
end Hironaka.HironakaG8CompactSharpFinish
