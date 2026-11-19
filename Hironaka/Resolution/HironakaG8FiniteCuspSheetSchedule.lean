import Hironaka.Resolution.HironakaG8CountableCuspSheets
import Hironaka.Resolution.HironakaG8FiniteScheduledSheetTest
import Hironaka.Resolution.HironakaG8CuspPointTower
import Hironaka.Resolution.HironakaG8OddCuspGeometricSource

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8FiniteCuspSheetSchedule
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupRestrictOpen BlowupTowerIsomorphism BlowupTowerTransforms HironakaG8CuspPointTower HironakaEmbeddedAnalytic MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG3EmptyAwareHistory HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaG8CountableCuspSheets HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource
  HironakaG8FiniteScheduledSheetTest HironakaG8SingularFootprintExtension
  HironakaNormalCrossingsSeparationChoiceComparison HironakaStageCenters NormalCrossings

local notation "𝓘c" => 𝓘(ℂ, ComplexModel 3)

abbrev prefixMfd (m : ℕ) := CMfd.of (n := 3) (prefixOpen m)

def cuspPrefix (m : ℕ) : Set (prefixMfd m) :=
  (Subtype.val : prefixOpen m → CuspSheets) ⁻¹' sheetCusps (fun _ => 7)

def cuspMarked {X : CMfd.{0} 3} (W : Set X) : MarkedIdeal 3 X :=
  ⟨univ,[],vanishingIdeal (n := 3) W,1⟩

def patch {m : ℕ} (i : Fin (m+1)) : Opens (prefixMfd m) := prefixSheetOpen m i.val

def patchCoord {m : ℕ} (i : Fin (m+1)) :
    patch i ≃ₘ⟮𝓘c,𝓘c⟯ CuspAmbient :=
  prefixSheetBiholomorph (Nat.le_of_lt_succ i.isLt)

def patchOrigin {m : ℕ} (i : Fin (m+1)) : patch i := (patchCoord i).symm 0

theorem patchOrigin_val {m : ℕ} (i : Fin (m+1)) :
    ((patchOrigin i).val.val : CuspSheets) = (i.val,0) := rfl

theorem patch_cover (m : ℕ) (x : prefixMfd m) : ∃ i : Fin (m+1), x ∈ patch i := by
  have hx : x.val.1 ≤ m := x.property
  exact ⟨⟨x.val.1,Nat.lt_succ_of_le hx⟩,mem_singleton _,mem_univ _⟩

theorem patch_disjoint (m : ℕ) :
    Pairwise fun i j : Fin (m+1) => Disjoint (patch i : Set (prefixMfd m)) (patch j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hi : x.val.1 = i.val := mem_singleton_iff.mp hx.1
  have hj : x.val.1 = j.val := mem_singleton_iff.mp hy.1
  exact hij (Fin.ext (hi.symm.trans hj))

/-- The local footprint singleton gives the literal original ambient trace. -/
theorem ambient_patch_trace_of_singleton {m j : ℕ} (i : Fin (m+1)) {Z : CMfd.{0} 3}
    (R : BlowupTower (prefixMfd m) Z)
    (hF : slotFootprint (restrict (patch i) R) j = {patchOrigin i}) :
    (fun x : patch i => (x.val.val : CuspSheets)) '' slotFootprint (restrict (patch i) R) j =
      {(i.val,0)} := by
  rw [hF,image_singleton,patchOrigin_val]

/-- A single fixed geometric cusp test supplies every patch of every cutoff. -/
theorem finite_cusp_sheet_schedule {Y : CMfd.{0} 3} (T : BlowupTower CuspAmbient Y)
    (hLen : T.length = 3)
    (hTest : IsGeoTestTower (cuspMarked (embeddedCuspSet 7)) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := 3)
      (strictTransform 3 P.proj (embeddedCuspSet 7))) T)
    (hSmooth : IsClosedSubmanifold 3 (strictTransform 3 T.proj (embeddedCuspSet 7)))
    (hFoot : ∀ j < 3, slotFootprint T j = ({0} : Set CuspAmbient)) (m : ℕ) :
    ∃ (Z : CMfd.{0} 3) (R : BlowupTower (prefixMfd m) Z),
      R.length = m+3 ∧ IsGeoTestTower (cuspMarked (cuspPrefix m)) R ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 3) (strictTransform 3 P.proj (cuspPrefix m))) R ∧
      IsClosedSubmanifold 3 (strictTransform 3 R.proj (cuspPrefix m)) ∧
      ∀ i : Fin (m+1),
        (∃ e : Y ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := 3) (openPreimage R (patch i)),
          EmptyAwareTowerIso (patchCoord i).symm T (restrict (patch i) R) e ∧
          ∀ y, R.proj (e y).val = ((patchCoord i).symm (T.proj y)).val) ∧
        slotFootprint (restrict (patch i) R) i.val = {patchOrigin i} ∧
        slotFootprint (restrict (patch i) R) (i.val+1) = {patchOrigin i} ∧
        slotFootprint (restrict (patch i) R) (m+2) = {patchOrigin i} ∧
        (∀ j, (slotFootprint (restrict (patch i) R) j).Nonempty → j = i.val ∨ j = i.val+1 ∨ j = m+2) := by
  let S (i : Fin (m+1)) := transport (X' := CMfd.of (n := 3) (patch i)) (patchCoord i) T
  have hIso (i : Fin (m+1)) : IsTowerIso (patchCoord i) (S i).tower T (S i).back :=
    transport_isTowerIso (X' := CMfd.of (n := 3) (patch i)) (patchCoord i) T
  have hClosed : IsClosed (cuspPrefix m) := (sheetCusps_isClosed (fun _ => 7)).preimage
    (continuous_subtype_val (p := fun x : CuspSheets => x ∈ prefixOpen m))
  have hAnalytic : IsComplexAnalyticSubset (n := 3) (cuspPrefix m) :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (sheetCusps_isAnalytic (fun _ => 7)) (prefixOpen m)
  have hM : (cuspMarked (cuspPrefix m)).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      CartanIrreducible.cartanCoherence _ hAnalytic, isSNCDivisor_nil,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  have hRead (i : Fin (m+1)) :
      (Subtype.val : patch i → prefixMfd m) ⁻¹' cuspPrefix m =
      patchCoord i ⁻¹' embeddedCuspSet 7 :=
    sheetCusps_preimage_prefix_sheet (fun _ => 7) (Nat.le_of_lt_succ i.isLt)
  have hMarked (i : Fin (m+1)) :
      MarkedIdeal.pullback (Subtype.val : patch i → prefixMfd m) (cuspMarked (cuspPrefix m)) =
      MarkedIdeal.pullback (patchCoord i) (cuspMarked (embeddedCuspSet 7)) := by
    have h₁ := pullback_vanishingIdeal_opens (m := 3) (n := 3) (patch i) (id : patch i → patch i) (cuspPrefix m)
    have h₂ := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      (patchCoord i).contMDiff (patchCoord i).symm.contMDiff
      (patchCoord i).apply_symm_apply (patchCoord i).symm_apply_apply
      (contMDiff_id (I := 𝓘c) (M := patch i)) (embeddedCuspSet 7)
    rw [hRead] at h₁
    have hI := h₁.symm.trans h₂
    change MarkedIdeal.mk _ _ _ _ = MarkedIdeal.mk _ _ _ _
    congr 1
  have hSTest (i : Fin (m+1)) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : patch i → prefixMfd m)
        (cuspMarked (cuspPrefix m))) (S i).tower := by
    rw [hMarked]
    exact (isGeoTestTower_transport_iff (X' := CMfd.of (n := 3) (patch i)) (patchCoord i)
      (CartanIrreducible.cartanCoherence _ (embedded_cusp_isAnalytic 7)) T).mpr hTest
  have hSStage (i : Fin (m+1)) :
      StageCentres (fun P C => C ⊆ singularSet (n := 3)
        (strictTransform 3 P.proj ((Subtype.val : patch i → prefixMfd m) ⁻¹' cuspPrefix m))) (S i).tower := by
    apply singular_stages_of_tower_iso _ (hClosed.preimage continuous_subtype_val) (patchCoord i).symm
      (hIso i).symm
    have hPre : (patchCoord i).symm ⁻¹'
        ((Subtype.val : patch i → prefixMfd m) ⁻¹' cuspPrefix m) = embeddedCuspSet 7 := by
      rw [hRead]
      ext x
      simp only [mem_preimage,Diffeomorph.apply_symm_apply]
    rwa [hPre]
  have hSSmooth (i : Fin (m+1)) :
      IsClosedSubmanifold 3 (strictTransform 3 (S i).tower.proj
        ((Subtype.val : patch i → prefixMfd m) ⁻¹' cuspPrefix m)) := by
    rw [hRead,strictTransform_preimage_of_square (patchCoord i) (S i).back
      (S i).tower.contMDiff_proj T.contMDiff_proj _ (embedded_cusp_isAnalytic 7).isClosed
      (fun z => ((hIso i).proj_comm z).symm)]
    exact (isClosedSubmanifold_preimage_iff (S i).back).mpr hSmooth
  obtain ⟨Z,R,hRL,hRT,hRS,hRSm,hPatch⟩ :=
    exists_finite_scheduled_sheet_test patch (patch_cover m) (patch_disjoint m)
      (fun i => (S i).tower) (fun i => (length_transport (X' := CMfd.of (n := 3) (patch i)) (patchCoord i) T).trans hLen)
      _ hM hSTest _ hClosed hSStage hSSmooth
  refine ⟨Z,R,hRL,hRT,hRS,hRSm,fun i => ?_⟩
  obtain ⟨⟨e,he,_⟩,h0,h1,h2,hOther⟩ := hPatch i
  have hF (j : ℕ) (hj : j < 3) : slotFootprint (S i).tower j = {patchOrigin i} := by
    rw [slotFootprint_of_isTowerIso (hIso i) j,hFoot j hj]
    ext x
    simp only [mem_preimage,mem_singleton_iff,patchOrigin]
    exact ⟨fun hx => (patchCoord i).injective (hx.trans ((patchCoord i).apply_symm_apply 0).symm),
      fun hx => hx ▸ (patchCoord i).apply_symm_apply 0⟩
  let χ := (S i).back.symm.trans e
  have hχ : EmptyAwareTowerIso (patchCoord i).symm T (restrict (patch i) R) χ := by
    simpa only [Diffeomorph.trans_refl] using
      G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso (hIso i).symm) he
  refine ⟨⟨χ,hχ,?_⟩,h0.trans (hF 0 (by decide)),h1.trans (hF 1 (by decide)),
    h2.trans (hF 2 (by decide)),hOther⟩
  intro y
  have h := congrArg Subtype.val (emptyAware_proj_comm hχ y)
  rwa [proj_restrict] at h

#print axioms finite_cusp_sheet_schedule

end
end Hironaka.HironakaG8FiniteCuspSheetSchedule
