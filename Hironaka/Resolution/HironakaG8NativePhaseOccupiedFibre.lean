import Hironaka.Resolution.HironakaG8StageRankCoherence
import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NativePhaseOccupiedFibre
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals
  RestrictEmptyTower HironakaActualVanishingIntrinsicHSTransport
  HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaG8StageRankCoherence HironakaG8NativePhaseCertificate
  HironakaG8ClosedNativeTestGlobalization HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private theorem strict_profile_on_untouched_open (W : Set X) (hW : IsClosed W)
    (T : BlowupTower X Y) (O : Opens X) (hAvoid : CentresAvoid O T) (x : O) :
    ∃ z : Y, T.proj z = x.val ∧
      hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) T.proj W)) z =
        hilbertSamuelAt (vanishingIdeal (n := n+1) W) x.val := by
  let Q := openPreimage T O
  let P := restrict O T
  have hEmpty := (isEmptyTower_restrict_iff O T).mpr hAvoid
  obtain ⟨β,hβ⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection P hEmpty
  have hProj : (β : Q → O) = P.proj := funext hβ
  have hExc (z : Q) : z ∉ exceptionalLocus (n+1) β :=
    MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply z
  have hExcEmpty : exceptionalLocus (n+1) β = ∅ := eq_empty_iff_forall_notMem.mpr hExc
  have hV : (Subtype.val : Q → Y) ⁻¹' strictTransform (n+1) T.proj W =
      β ⁻¹' ((Subtype.val : O → X) ⁻¹' W) := by
    rw [← strictTransform_restricted_tower O T W,← show (β : Q → O) = (restrict O T).proj from hProj]
    simp only [strictTransform,hExcEmpty,sdiff_empty,((hW.preimage continuous_subtype_val).preimage β.continuous).closure_eq]
  let z := β.symm x
  have hz : β z = x := β.apply_symm_apply x
  refine ⟨z.val,?_,?_⟩
  · exact (proj_restrict O T z).symm.trans (congrArg Subtype.val ((hβ z).symm.trans hz))
  · funext l
    rw [← hilbertSamuelAt_vanishing_actual_open_any Q _ z l,
      hV,hilbertSamuelAt_vanishing_actual_biholomorphic_any,hz,
      hilbertSamuelAt_vanishing_actual_open_any]

/-- The projected union of occupied centres of an actual native phase is its
entire serviced profile level. Strict drop forces an occupied centre over
each source point of that level. -/
theorem baseCentreFootprint_eq_phaseLevel {W : Set X} (hW : IsClosed W)
    {E : List (Set X)} {H : ℕ → ℕ} {T : BlowupTower X Y}
    (h : ActualNativePhase W E H T) :
    baseCentreFootprint T = phaseLevel W H := by
  apply Subset.antisymm ((centresOver_iff_baseCentreFootprint_subset T).mp h.supports)
  intro x hx
  by_contra hOutside
  let F := baseCentreFootprint T
  let O : Opens X := ⟨Fᶜ,(isClosed_baseCentreFootprint T).isOpen_compl⟩
  have hOver : CentresOver F T := (centresOver_iff_baseCentreFootprint_subset T).mpr Subset.rfl
  have hAvoid : CentresAvoid O T := centresAvoid_of_centresOver O (show Disjoint (O : Set X) F from disjoint_compl_left) T hOver
  obtain ⟨z,hz,hHS⟩ := strict_profile_on_untouched_open W hW T O hAvoid ⟨x,hOutside⟩
  have hDrop := h.strictDrop z (show T.proj z ∈ phaseLevel W H from hz.symm ▸ hx)
  change hilbertSamuelAt (vanishingIdeal (n := n+1) W) x = H at hx
  rw [hHS,hx] at hDrop
  exact (lt_irrefl _ hDrop)

end
end Hironaka.HironakaG8NativePhaseOccupiedFibre
