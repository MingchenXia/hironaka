import Hironaka.Resolution.HironakaG8CountablePlaneSheets
import Hironaka.Resolution.HironakaG8PlaneArrangementSingular
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport
import Hironaka.Resolution.HironakaG8LabelledNativeOverlap

set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Topology
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CountablePlaneArrangement
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers HironakaEmbeddedAnalytic HironakaG8CountablePlaneSheets
  HironakaG8PlaneLineProducts HironakaG8PlaneArrangementSingular
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  AnalyticSubsetOpens HironakaResolutionSpaceLocal HironakaOriginalCanonicalDimensionList HironakaSmoothSubmersionOriginalGlobalFinite

def arrangementSheetOpen (i : ℕ) : Opens PlaneSheets :=
  ⟨(sheetChart i).source, (sheetChart i).open_source⟩

def arrangementSheetBiholomorph (i : ℕ) :
    arrangementSheetOpen i ≃ₘ⟮𝓘(ℂ, ComplexModel 2), 𝓘(ℂ, ComplexModel 2)⟯ ComplexModel 2 where
  toEquiv :=
    { toFun := fun x => x.val.2
      invFun := fun z => ⟨(i,z),mem_singleton i,mem_univ z⟩
      left_inv := fun x => Subtype.ext (Prod.ext (mem_singleton_iff.mp x.property.1).symm rfl)
      right_inv := fun _ => rfl }
  contMDiff_toFun := by
    have h := contMDiffOn_chart (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
      (x := ((i,0) : PlaneSheets))
    exact contMDiff_restrict (U := arrangementSheetOpen i) h
  contMDiff_invFun := by
    intro z
    apply (ContMDiffAt.subtypeVal_comp_iff (arrangementSheetOpen i) _ z).mp
    have h := contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
      (x := ((i,0) : PlaneSheets))
    exact h.contMDiffAt (show (sheetChart i).target ∈ 𝓝 z from univ_mem)

def countablePlaneArrangement : Set PlaneSheets :=
  {x | x.2 ∈ planeLineArrangement (x.1 + 2)}

theorem countablePlaneArrangement_preimage_sheet (i : ℕ) :
    (Subtype.val : arrangementSheetOpen i → PlaneSheets) ⁻¹' countablePlaneArrangement =
      arrangementSheetBiholomorph i ⁻¹' planeLineArrangement (i+2) := by
  ext x
  have hi : x.val.1 = i := mem_singleton_iff.mp x.property.1
  change (x.val.2 ∈ planeLineArrangement (x.val.1 + 2)) ↔
    (x.val.2 ∈ planeLineArrangement (i+2))
  rw [hi]

theorem countablePlaneArrangement_profile (i : ℕ) (z : ComplexModel 2) (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 2) countablePlaneArrangement) (i,z) l =
      hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement (i+2))) z l := by
  let w : arrangementSheetOpen i := ⟨(i,z),mem_singleton i,mem_univ z⟩
  rw [← hilbertSamuelAt_vanishing_actual_open_any (arrangementSheetOpen i) _ w l,
    countablePlaneArrangement_preimage_sheet,
    hilbertSamuelAt_vanishing_actual_biholomorphic_any]
  rfl

theorem countablePlaneArrangement_singularSet :
    singularSet (n := 2) countablePlaneArrangement = {x | x.2 = 0} := by
  ext x
  let w : arrangementSheetOpen x.1 := ⟨x,mem_singleton x.1,mem_univ x.2⟩
  have h := congrArg (fun A : Set (arrangementSheetOpen x.1) => w ∈ A)
    (singularSet_preimage_val (n := 2) (W := countablePlaneArrangement) (arrangementSheetOpen x.1))
  rw [countablePlaneArrangement_preimage_sheet,singularSet_preimage_eq
    (isSubmersion_biholomorphism (D := CMfd.of (n := 2) (arrangementSheetOpen x.1))
      (C := CMfd.of (n := 2) (ComplexModel 2)) (arrangementSheetBiholomorph x.1))
      (planeLineArrangement (x.1+2)),
    singularSet_planeLineArrangement (by omega)] at h
  exact Iff.of_eq h.symm

theorem countablePlaneArrangement_origin_profile_strictMono :
    StrictMono (fun i : ℕ => toLex
      (hilbertSamuelAt (vanishingIdeal (n := 2) countablePlaneArrangement) (i,0))) := by
  intro i j hij
  have h₁ := funext (countablePlaneArrangement_profile i 0)
  have h₂ := funext (countablePlaneArrangement_profile j 0)
  change toLex (hilbertSamuelAt (vanishingIdeal (n := 2) countablePlaneArrangement) (i,0)) <
    toLex (hilbertSamuelAt (vanishingIdeal (n := 2) countablePlaneArrangement) (j,0))
  rw [h₁,h₂]
  exact planeLineArrangement_profile_strictMono (by omega : i+2 < j+2)

theorem isComplexAnalyticSubset_countablePlaneArrangement :
    IsComplexAnalyticSubset (n := 2) countablePlaneArrangement :=
  isComplexAnalyticSubset_sheetwise _ (fun i => isComplexAnalyticSubset_planeLineArrangement (i+2))

end
end Hironaka.HironakaG8CountablePlaneArrangement
