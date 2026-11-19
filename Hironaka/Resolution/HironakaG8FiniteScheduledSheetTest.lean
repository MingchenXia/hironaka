import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaG8DisjointClockAtlas
import Hironaka.Resolution.HironakaG8ScheduledSheetTriple
import Hironaka.Resolution.HironakaG8FirstFootprintOrder

/-! An exact finite physical schedule on the first m+1 disjoint sheets. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteScheduledSheetTest

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG3EmptyAwareHistory
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder
  HironakaG8DisjointClockAtlas HironakaG8ScheduledSheetTriple
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8FiniteSingularTowerMerge
  HironakaG8SingularFootprintExtension HironakaNormalCrossingsSeparationChoiceComparison
  HironakaNormalCrossingsOpenRestrictionSeparation MarkedIdealTowerTransport

variable {n m : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Finite sheet schedules realize the leaf mergers in actual whole TEST
towers, with exact literal per-sheet raw footprints and terminal projections. -/
theorem exists_finite_scheduled_sheet_test
    (U : Fin (m+1) → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hDisj : Pairwise fun i j => Disjoint (U i : Set X) (U j : Set X))
    {Y : Fin (m+1) → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hLen : ∀ i, (T i).length = 3)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i))
    (W : Set X) (hW : IsClosed W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (T i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (T i).proj ((Subtype.val : U i → X) ⁻¹' W))) :
    ∃ (Z : CMfd.{0} n) (R : BlowupTower X Z),
      R.length = m+3 ∧ IsGeoTestTower M R ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      IsClosedSubmanifold n (strictTransform n R.proj W) ∧ ∀ i,
        (∃ e : Y i ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage R (U i)),
          EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (U i)) ∞)
            (T i) (restrict (U i) R) e ∧
          ∀ y, R.proj (e y).val = ((T i).proj y).val) ∧
        slotFootprint (restrict (U i) R) i.val = slotFootprint (T i) 0 ∧
        slotFootprint (restrict (U i) R) (i.val+1) = slotFootprint (T i) 1 ∧
        slotFootprint (restrict (U i) R) (m+2) = slotFootprint (T i) 2 ∧
        (∀ j, (slotFootprint (restrict (U i) R) j).Nonempty → j = i.val ∨ j = i.val+1 ∨ j = m+2) := by
  classical
  let M' i := MarkedIdeal.pullback (Subtype.val : U i → X) M
  have hM' i : (M' i).IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (U i)
  have hPad (i : Fin (m+1)) := exists_scheduled_sheet_triple (T i) (hLen i) (M' i) (hM' i) (hTest i)
    m i.val (Nat.le_of_lt_succ i.isLt)
  choose S hSLen hSTest hSProj hSAware hS0 hS1 hS2 hSOther using hPad
  obtain ⟨Z,R,hRLen,hRTest,hIso⟩ :=
    exists_disjoint_clock_test_tower U hCover hDisj S (m+2) hSLen M hM hSTest
  choose e hStrictIso using hIso
  have hSheet (i : Fin (m+1)) :
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (U i)) ∞)
        (T i) (restrict (U i) R) (e i) := by
    have hCompare := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.symm (hSAware i))
      (emptyAware_of_isTowerIso (hStrictIso i))
    simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans] using hCompare
  refine ⟨Z,R,hRLen,hRTest,?_,?_,?_⟩
  · apply singular_stages_of_open_cover W U hCover R
    intro i
    have hi := singular_stages_of_emptyAware ((Subtype.val : U i → X) ⁻¹' W)
      (hW.preimage continuous_subtype_val) _ (hSheet i)
    simpa only [Diffeomorph.coe_refl,preimage_id] using hi (by
      simpa only [Diffeomorph.coe_refl,preimage_id] using hSing i)
  · refine ⟨isClosed_closure,?_⟩
    intro z hz
    obtain ⟨i,hi⟩ := hCover (R.proj z)
    let WU := (Subtype.val : U i → X) ⁻¹' W
    have hEq := strictTransform_preimage_of_square
      (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (U i)) ∞) (e i)
      (T i).contMDiff_proj (restrict (U i) R).contMDiff_proj WU (hW.preimage continuous_subtype_val)
      (emptyAware_proj_comm (hSheet i))
    rw [Diffeomorph.coe_refl,preimage_id] at hEq
    have hS : IsClosedSubmanifold n (strictTransform n (restrict (U i) R).proj WU) :=
      (isClosedSubmanifold_preimage_iff (e i)).mp (hEq ▸ hSmooth i)
    let zU : openPreimage R (U i) := ⟨z,hi⟩
    have hStrict := strictTransform_restricted_tower (U i) R W
    have hzU : zU ∈ strictTransform n (restrict (U i) R).proj WU := by
      rw [hStrict]
      exact hz
    obtain ⟨d,hd⟩ := hS.2 zU hzU
    rw [hStrict] at hd
    exact ⟨d,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hd⟩
  · intro i
    have hFoot (j : ℕ) : slotFootprint (restrict (U i) R) j = slotFootprint (S i) j := by
      simpa only [Diffeomorph.coe_refl,preimage_id] using (slotFootprint_of_isTowerIso (hStrictIso i) j).symm
    refine ⟨⟨e i,hSheet i,?_⟩,(hFoot _).trans (hS0 i),(hFoot _).trans (hS1 i),(hFoot _).trans (hS2 i),?_⟩
    · intro y
      have h := congrArg Subtype.val ((hStrictIso i).proj_comm y)
      change ((S i).proj y).val = ((restrict (U i) R).proj (e i y)).val at h
      rw [proj_restrict,hSProj i] at h
      exact h.symm
    · intro j hj
      rw [hFoot j] at hj
      exact hSOther i j hj

end Hironaka.HironakaG8FiniteScheduledSheetTest
