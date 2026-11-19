import Hironaka.Resolution.HironakaG8InitialBoundaryAtlasMarkOne
import Hironaka.Resolution.HironakaG8LabelledOriginalCanonicalPrefixes

/-! Original mark-one TEST and canonical native HS epochs on one ordered atlas. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8CorrectedOrderedEndpoint

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaEmbeddedAnalytic
  HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC HironakaG3REmbeddedNC
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8InitialBoundaryAtlasMarkOne
  HironakaG8LabelledEmbeddedTape HironakaG8LabelledNativeHistory
  HironakaG8LabelledOriginalCanonicalPrefixes HironakaActualSmoothBoundaryCleanup
  HironakaG8LocalMixedPhaseAssembly HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG4SharpTerminalAtlas HironakaG8LocalMixedSmoothCleanup

/-- Canonicality on the actual native part of this chart's finite tower.
The same factorization retains the original native history and the separately
certified smooth cleanup with the full accumulated ordered boundary. -/
def InitialBoundaryChartEpochs {m : ℕ} {X Z : CMfd.{0} (m+1)}
    {W : Set X} {E : List (Set X)} {P : Z → X}
    (c : TowerChart (orderedInitialBoundaryClass W E) Z P) : Prop :=
  let A := CMfd.of (n := m+1) c.U
  let W₀ := (Subtype.val : c.U → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : c.U → X) ⁻¹' ·)
  ∃ (B D : CMfd.{0} (m+1)) (S : BlowupTower A B) (Q : BlowupTower B D)
    (χ : _ ≃ₘ⟮𝓘(ℂ,ComplexModel (m+1)), 𝓘(ℂ,ComplexModel (m+1))⟯ D) (L : List (ℕ → ℕ)),
    LabelledNativeTower (m+1) W₀ E₀ univ S L ∧
    LabelledRawEpochPrefixes (Nat.succ_pos m) W₀ E₀ S L ∧
    (ascending_smooth_tail_certificate (m+1)).holds (strictTransform (m+1) S.proj W₀)
      (geoTransformAlong (actualSmoothBoundaryMarked W₀ E₀) S).E Q ∧
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (m+1)) A ∞) c.T (S.append Q) χ

theorem initial_boundary_chart_epochs {m : ℕ} {X Z : CMfd.{0} (m+1)}
    {W : Set X} {E : List (Set X)} {P : Z → X}
    (c : TowerChart (orderedInitialBoundaryClass W E) Z P) :
    InitialBoundaryChartEpochs c := by
  obtain ⟨B,D,S,Q,χ,L,hS,hQ,hT⟩ := c.mem.phases
  exact ⟨B,D,S,Q,χ,L,hS,labelled_native_raw_epoch_prefixes (Nat.succ_pos m) hS,hQ,hT⟩

/-- The same proper embedded resolution charts carry both the original
mark-one TEST and canonical raw prefixes for their actual native HS epochs. -/
theorem exists_ordered_boundary_resolution_epoch_canonical
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P, c.U = U) ∧
      IsProperMap P ∧
      (∀ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
        InitialBoundaryChartMarkOne c ∧ InitialBoundaryChartEpochs c) ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
          Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m+1) B ∧ (∀ j, (B j).Nonempty) ∧
        HasNormalCrossingsWithBoundary (strictTransform (m+1) P W) B := by
  obtain ⟨Z,P,hGlue,hWindows,hTest,hSmooth,hIso,hMembers⟩ :=
    exists_locally_finite_initial_boundary_original_markOne_atlas hW hE hDense
  exact ⟨Z,P,hGlue,hWindows,hGlue.2.1,fun c => ⟨hTest c,initial_boundary_chart_epochs c⟩,
    hSmooth,hIso,hMembers⟩

#print axioms initial_boundary_chart_epochs
#print axioms exists_ordered_boundary_resolution_epoch_canonical

end
end Hironaka.HironakaG8CorrectedOrderedEndpoint
