import Hironaka.Analytic.Unibranch.OriginalNativeSmoothNormalizedSquare
import Hironaka.Resolution.HironakaG1ActualDeletedHistoryComposition

/-! The SAME actual normalized canonical source has a direct deleted history
to the original target, with its original physical clock and native map.
Blueprint first: `original-native-smooth-direct-deleted-history.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothDirectDeletedHistory
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers BlowupTowerIsomorphism BlowupTowerSplit
  HironakaG1DeletedSmoothHistory HironakaG1ActualDeletedHistoryComposition
  HironakaG1PhysicalHistoryCoherence HironakaActualAnalyticSubspaceMaps
  HironakaResolutionSpace HironakaResolutionSpaceComplex
  SourceReducedComplexSpace OriginalNativeSmoothCanonicalSquare OriginalNativeSmoothNormalizedSquare

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {x : X.obj.left}
  {V : Opens X.obj.left} {T : Opens Y.obj.left}
  {a : LocalCanonicalPullback f x V T} (b : NormalizedSource a)

/-- The same normalized Q-source is a genuine deletion of the ORIGINAL target clock. -/
theorem direct_history : IsDeletedSmoothHistory (baseMap a.window a.neighbourhood)
    b.tower a.targetTower (a.lift ∘ b.biholomorphism) b.retained :=
  actual_comp_id_deleted a.history b.deletion

theorem direct_accounting : b.retained.length = b.tower.length ∧ b.retained.Pairwise (· < ·) ∧
    ∀ j ∈ b.retained, j < a.targetTower.length :=
  (direct_history b).physical_accounting

theorem direct_prefix (j : ℕ) :
    ∃ i k, IsDeletedSmoothHistory (baseMap a.window a.neighbourhood)
      (head b.tower i) (head a.targetTower j) k
      (b.retained.filter (fun t => decide (t < a.targetTower.length-j))) :=
  (direct_history b).prefix j

theorem direct_old_boundary (E : List (Set a.neighbourhood)) (hE : ∀ A ∈ E, IsClosed A) :
    oldBoundaryAlong (E.map (baseMap a.window a.neighbourhood ⁻¹' ·)) b.tower =
      (oldBoundaryAlong E a.targetTower).map ((a.lift ∘ b.biholomorphism) ⁻¹' ·) :=
  (direct_history b).old_boundary_dictionary E hE

theorem direct_born_boundary : bornBoundaryAlong b.tower =
    selectBirths ((bornBoundaryAlong a.targetTower).map ((a.lift ∘ b.biholomorphism) ⁻¹' ·)) b.retained :=
  (direct_history b).born_boundary_dictionary

theorem direct_omitted_birth (j : ℕ) (hj : j < a.targetTower.length) (hjL : j ∉ b.retained) :
    (a.lift ∘ b.biholomorphism) ⁻¹' (bornBoundaryAlong a.targetTower).getD j ∅ = ∅ :=
  (direct_history b).omitted_birth_empty j hj hjL

private theorem directLift_mapsTo :
    ∀ z ∈ strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood),
      (a.lift ∘ b.biholomorphism) z ∈
        strictTransform a.window.target.dim a.targetTower.proj (targetCarrier a.window a.neighbourhood) := by
  intro z hz
  have hQ := (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)) z).mp hz
  exact (Set.ext_iff.mp a.strict_preimage_eq (b.biholomorphism z)).mp hQ

/-- The FULL native lift is the quotient map of precisely this direct history's terminal map. -/
theorem native_lift_is_actual : (NormalizedSource.lift b).hom.left =
    actualSubspaceMap (a.history.isSubmersion.contMDiff.comp b.biholomorphism.contMDiff) (directLift_mapsTo b) := by
  have hcomp := actualSubspaceMap_comp
    (n := a.window.sourceDim) (m := a.window.sourceDim) (p := a.window.target.dim)
    (C := strictTransform a.window.sourceDim b.tower.proj (sourceCarrier a.window a.neighbourhood))
    (D := strictTransform a.window.sourceDim a.sourceTower.proj (sourceCarrier a.window a.neighbourhood))
    (E := strictTransform a.window.target.dim a.targetTower.proj (targetCarrier a.window a.neighbourhood))
    (f := b.biholomorphism) (g := a.lift) b.biholomorphism.contMDiff a.history.isSubmersion.contMDiff
    (fun z hz => (Set.ext_iff.mp (b.whole_strict (sourceCarrier a.window a.neighbourhood)) z).mp hz)
    (fun z hz => (Set.ext_iff.mp a.strict_preimage_eq z).mp hz)
  exact hcomp.symm

theorem normalized_identity_history : IsDeletedSmoothHistory
    (id : sourceOpen a.window a.neighbourhood → sourceOpen a.window a.neighbourhood)
    b.tower b.tower id (List.range b.tower.length) :=
  identity_of_nonempty_centres b.tower b.deletion.nonempty_centres

theorem subsequent_composition {ℓ : ℕ} {Z F : CMfd.{0} ℓ}
    {h : Z → sourceOpen a.window a.neighbourhood} {e : F → b.endpoint}
    {R : BlowupTower Z F} {K : List ℕ} (HR : IsDeletedSmoothHistory h R b.tower e K) :
    IsDeletedSmoothHistory (baseMap a.window a.neighbourhood ∘ h) R a.targetTower
      ((a.lift ∘ b.biholomorphism) ∘ e) (composeRetained b.retained K) :=
  HironakaG1PhysicalHistoryCoherence.IsDeletedSmoothHistory.comp (direct_history b) HR

theorem direct_choice {F : CMfd.{0} a.window.sourceDim}
    {R : BlowupTower (CMfd.of (n := a.window.sourceDim) (sourceOpen a.window a.neighbourhood)) F}
    {k : F → a.targetEnd} {K : List ℕ}
    (HR : IsDeletedSmoothHistory (baseMap a.window a.neighbourhood) R a.targetTower k K) :
    b.retained = K ∧ ∃ φ : b.endpoint ≃ₘ⟮𝓘(ℂ,ComplexModel a.window.sourceDim),𝓘(ℂ,ComplexModel a.window.sourceDim)⟯ F,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel a.window.sourceDim) (sourceOpen a.window a.neighbourhood) ∞)
        b.tower R φ ∧ ∀ z, k (φ z) = a.lift (b.biholomorphism z) :=
  direct_choice_comparison a.history b.deletion HR

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothDirectDeletedHistory
