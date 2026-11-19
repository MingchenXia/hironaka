import Hironaka.Resolution.HironakaG4SharpTerminalAtlas
import Hironaka.Resolution.HironakaG4WindowSharpEndpoint
import Hironaka.Resolution.HironakaActualLocallyFiniteBlowupLimitGeometry
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison
import Hironaka.Resolution.HironakaActualProtectedGammaOpenCompatibility

/-!
# The actual stable-prefix atlas of a compact-cut sharp schedule

The selected schedule supplies stable actual finite restrictions.
Their physical comparisons are obtained by discarding empty tails
on overlaps of their base opens.

Blueprint: `hironaka-g4-compact-cut-sharp-atlas.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SharpStableAtlas

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RestrictEmptyTower NormalCrossings
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons G3UniverseEmptyAwareCore
  HironakaG3AppendEmptyTailComparison HironakaOriginalTerminalOverlapComparison MaxLocusLocal
  HironakaG4SharpTerminalAtlas HironakaG4WindowSharpSchedule HironakaG4WindowSharpEndpoint
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalAllBoundaryCentre HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteBlowupLimitGeometry HironakaLocallyFiniteResolutionSequence
  HironakaActualProtectedGammaOpenCompatibility HironakaG34NonPureLowDim ResolutionInvariantSeq

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- A region already resolved at a finite sharp prefix has an actual sharp
terminal history given by that prefix's restriction. -/
theorem sharp_terminal_restrict {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (U : Opens X) (T : BlowupTower X Y)
    (hCarrier : IsGeoTestTower (geometricTemplate W []) T)
    (hBoundary : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hNC : ∀ z ∈ strictAlong T W, T.proj z ∈ U →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))
      (restrict U T) := by
  let M := geometricTemplate (univ : Set X) E
  have hC := isGeoTestTower_restrict U hW (IdealWeightPowers.isCoherent_unitIdeal (n := n) (M := X))
    T hCarrier
  have hM := isGeoTestTower_restrict U isClosedSubmanifold_univ
    (IdealWeightPowers.isCoherent_unitIdeal (n := n) (M := X)) T hBoundary
  rw [template_pullback (Y := CMfd.of (n := n) U), List.map_nil] at hC
  rw [template_pullback (Y := CMfd.of (n := n) U), preimage_univ] at hM
  refine ⟨hC, hM, currentSharp_restrict U T hBoundary hSharp, ?_⟩
  have hEq := congrArg MarkedIdeal.E (geoTransformAlong_restrict U isClosedSubmanifold_univ
    (IdealWeightPowers.isCoherent_unitIdeal (n := n) (M := X)) T hBoundary)
  rw [template_pullback (Y := CMfd.of (n := n) U), preimage_univ] at hEq
  change (geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U)
      (E.map ((Subtype.val : U → X) ⁻¹' ·))) (restrict U T)).E =
      (geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) at hEq
  rw [strictAlong_restrict, hEq]
  intro z hz
  exact normalCrossingsAt_preimage_val_iff.mpr (hNC z.val hz z.property)

/-- Two nested chart restrictions compare on the overlap whenever the
corresponding ambient restrictions physically compare over the same open. -/
theorem nested_restrict_physical_overlap (U₁ U₂ : Opens X)
    (T₁ : BlowupTower X Y) (T₂ : BlowupTower X Z)
    (β : (CMfd.of (n := n) (openPreimage T₁ (U₁ ⊓ U₂))) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage T₂ (U₁ ⊓ U₂))))
    (hβ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) ↥(U₁ ⊓ U₂)) ∞)
      (restrict (U₁ ⊓ U₂) T₁) (restrict (U₁ ⊓ U₂) T₂) β) :
    ∃ η : (CMfd.of (n := n) (openPreimage (restrict U₁ T₁) (nestedOpens U₁ (U₁ ⊓ U₂))))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        (CMfd.of (n := n) (openPreimage (restrict U₂ T₂) (nestedOpens U₂ (U₁ ⊓ U₂)))),
      EmptyAwareTowerIso (overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right)
        (restrict (nestedOpens U₁ (U₁ ⊓ U₂)) (restrict U₁ T₁))
        (restrict (nestedOpens U₂ (U₁ ⊓ U₂)) (restrict U₂ T₂)) η := by
  have h₁ := isTowerIso_restrict_nestedOpens (inf_le_left : U₁ ⊓ U₂ ≤ U₁) T₁
  have h₂ := isTowerIso_restrict_nestedOpens (inf_le_right : U₁ ⊓ U₂ ≤ U₂) T₂
  have h := G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso h₁)
    (G3UniverseEmptyAwareCore.trans hβ (emptyAware_of_isTowerIso h₂.symm))
  simp only [Diffeomorph.refl_trans] at h
  exact ⟨_, h⟩

private theorem same_open_late_prefix_physical (s : GrowingSeq X) (U : Opens X)
    {i j : ℕ} (hij : i ≤ j)
    (hAvoid : ∀ k, i ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (U : Set X))) :
    ∃ η : (CMfd.of (n := n) (openPreimage (s.stage j).2 U)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage (s.stage i).2 U)),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (s.stage j).2) (restrict U (s.stage i).2) η := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hEmpty := (isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s i U hAvoid r)
  rw [← append_tailTower s i r]
  exact restricted_append_comparison_of_empty_tail (s.stage i).2 (tailTower s i r) U hEmpty

private theorem stable_open_late_avoidance (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (U : Opens X) (i : ℕ) (hU : U ≤ actualStableOpen s hLF i) :
    ∀ k, i ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (U : Set X)) := by
  intro k hk
  apply disjoint_left.mpr
  intro z hz hUz
  have hTail := (mem_actualStableOpen s hLF i ((s.stage k).2.proj z)).mp (hU hUz)
  exact hTail k hk ⟨z, hz, rfl⟩

/-- A member is a literal stable restriction of one prefix of the selected
actual history. Its terminal condition is on that restricted prefix. -/
def stableSharpClass (W : Set X) (E : List (Set X)) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : LocalTowerClass X :=
  fun U Y T => ∃ N, U ≤ actualStableOpen s hLF N ∧
    (⟨Y, T⟩ : Σ Y : CMfd.{u} n, BlowupTower (CMfd.of (n := n) U) Y) =
      ⟨CMfd.of (n := n) (openPreimage (s.stage N).2 U), restrict U (s.stage N).2⟩ ∧
    IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T

theorem stable_sharp_class_terminal (W : Set X) (E : List (Set X)) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : SharpTerminalClass W E (stableSharpClass W E s hLF) :=
  fun _ _ _ hT => hT.choose_spec.2.2

/-- Stability of two actual windows identifies both histories after
restriction to their common base, with the empty suffix retained. -/
theorem stable_sharp_class_physical (W : Set X) (E : List (Set X)) (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : HasPhysicalComparisons (stableSharpClass W E s hLF) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  obtain ⟨i, hi, heq₁, _⟩ := h₁
  obtain ⟨j, hj, heq₂, _⟩ := h₂
  obtain ⟨hY₁, hT₁⟩ := Sigma.mk.inj_iff.mp heq₁
  obtain ⟨hY₂, hT₂⟩ := Sigma.mk.inj_iff.mp heq₂
  cases hY₁
  cases hT₁
  cases hY₂
  cases hT₂
  let U := U₁ ⊓ U₂
  rcases le_total i j with h | h
  · obtain ⟨η, hη⟩ := same_open_late_prefix_physical s U h
      (stable_open_late_avoidance s hLF U i (inf_le_left.trans hi))
    have hη' : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (s.stage i).2) (restrict U (s.stage j).2) η.symm := by
      simpa only [Diffeomorph.symm_refl] using G3UniverseEmptyAwareCore.symm hη
    exact nested_restrict_physical_overlap U₁ U₂ (s.stage i).2 (s.stage j).2 η.symm hη'
  · obtain ⟨η, hη⟩ := same_open_late_prefix_physical s U h
      (stable_open_late_avoidance s hLF U j (inf_le_right.trans hj))
    exact nested_restrict_physical_overlap U₁ U₂ (s.stage i).2 (s.stage j).2 η hη

/-- A single finite ambient terminal history also supplies the coherent
family of all its actual open restrictions. -/
def finiteSharpClass (T : BlowupTower X Y) : LocalTowerClass X :=
  fun U Z Q => (⟨Z, Q⟩ : Σ Z : CMfd.{u} n, BlowupTower (CMfd.of (n := n) U) Z) =
    ⟨CMfd.of (n := n) (openPreimage T U), restrict U T⟩

theorem finite_sharp_class_terminal {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (T : BlowupTower X Y) (hT : IsSharpTerminalTower W E T) :
    SharpTerminalClass W E (finiteSharpClass T) := by
  intro U Z Q heq
  obtain ⟨hZ, hQ⟩ := Sigma.mk.inj_iff.mp heq
  cases hZ
  cases hQ
  exact sharp_terminal_restrict hW U T hT.carrierTest hT.boundaryTest hT.sharp
    (fun z hz _ => hT.normalCrossings z hz)

theorem finite_sharp_class_physical (T : BlowupTower X Y) :
    HasPhysicalComparisons (finiteSharpClass T) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  obtain ⟨hY₁, hT₁⟩ := Sigma.mk.inj_iff.mp h₁
  obtain ⟨hY₂, hT₂⟩ := Sigma.mk.inj_iff.mp h₂
  cases hY₁
  cases hT₁
  cases hY₂
  cases hT₂
  exact nested_restrict_physical_overlap U₁ U₂ T T _ (emptyAware_of_isTowerIso (IsTowerIso.refl_self _))

/-- Internally selected compact bad cuts yield a covering class of actual
sharp terminal histories and physical overlap comparisons. -/
theorem compact_bad_windows_sharp_atlas {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ U : Opens X,
      x ∈ U ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ U)) :
    ∃ (K : LocalTowerClass X) (Z : CMfd.{u} n) (P : Z → X), IsGluedSharpCleanup K W E Z P ∧
      ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ c : TowerChart K Z P, c.U = U := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let B := CompactExhaustion.choice X
  rcases finite_or_locallyFinite_full_boundary_window_sharp_schedule hW hE hLocal B with
    ⟨a, hStat⟩ | ⟨s, hBlocks, hT, hFull, hSharp, _hGood, hLF, _hEmpty⟩
  · let T := (fullBoundaryBlocks hW hE hLocal B a).2
    obtain ⟨hT, hF, hS, _, _, _, hNC, _, _⟩ :=
      stationary_full_boundary_blocks_terminal hW hE hLocal B a hStat
    rw [N_geoTransformAlong] at hNC
    have hFin : IsSharpTerminalTower W E T := ⟨hT, hF, hS, hNC⟩
    have hWindows (U : Opens X) (_L : Set X) (_hL : IsCompact _L) (_hUL : (U : Set X) ⊆ _L) :
        ∃ (Y : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) U) Y), finiteSharpClass T U Y Q :=
      ⟨CMfd.of (n := n) (openPreimage T U), restrict U T, rfl⟩
    obtain ⟨Z, P, hP, hU⟩ := glue_compatible_sharp_terminal_histories hW hE
      (finite_sharp_class_terminal hW T hFin) (finite_sharp_class_physical T) hWindows
    exact ⟨finiteSharpClass T, Z, P, hP, hU⟩
  · have hWindows (U : Opens X) (L : Set X) (hL : IsCompact L) (hUL : (U : Set X) ⊆ L) :
        ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), stableSharpClass W E s hLF U Y T := by
      obtain ⟨N₀, hStable⟩ := exists_compact_subset_actualStableOpen s hLF hL
      obtain ⟨V, N₁, hLV, hGood⟩ := growing_full_boundary_eventually_nc_on_compacts hW hE hLocal B
        s hBlocks hSharp L hL
      let N := max N₀ N₁
      let T := (s.stage N).2
      let Q := restrict U T
      have hSt : U ≤ actualStableOpen s hLF N :=
        hUL.trans (hStable.trans (actualStableOpen_mono s hLF (le_max_left N₀ N₁)))
      exact ⟨CMfd.of (n := n) (openPreimage T U), Q, N, hSt, rfl,
        sharp_terminal_restrict hW U T (hT N) (hFull N) (hSharp N)
          (fun z hz hzU => hGood N (le_max_right N₀ N₁) z hz (hLV (hUL hzU)))⟩
    obtain ⟨Z, P, hP, hU⟩ := glue_compatible_sharp_terminal_histories hW hE
      (stable_sharp_class_terminal W E s hLF) (stable_sharp_class_physical W E s hLF) hWindows
    exact ⟨stableSharpClass W E s hLF, Z, P, hP, hU⟩

end
end Hironaka.HironakaG4SharpStableAtlas
