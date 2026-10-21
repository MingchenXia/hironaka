/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalMap
import Hironaka.Resolution.HironakaSmoothSubmersionGlobalBlowupSubmersion
/-! Genuine local normal forms for the same arbitrary-target original arrow.
Complete blueprint preceded code. Actual open inclusions, genuine range
biholomorphisms and internally produced local submersions give all forms. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalSubmersion
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaSmoothSubmersionOriginalSourceChartMap
  HironakaSmoothSubmersionOriginalGlobalMap HironakaSmoothSubmersionOriginalLocalChartArrow
  HironakaSmoothSubmersionOriginalLocalGlobalArrow HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionGlobalBlowupSubmersion
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

private theorem subtypeInclusion_holomorphic {k : ℕ} {A : CMfd.{u} k}
    (O : Opens A) (hO : Nonempty O) :
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞
      (O.openPartialHomeomorphSubtypeCoe hO) (O.openPartialHomeomorphSubtypeCoe hO).source ∧
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞
      (O.openPartialHomeomorphSubtypeCoe hO).symm (O.openPartialHomeomorphSubtypeCoe hO).target := by
  refine ⟨contMDiff_subtype_val.contMDiffOn,?_⟩
  let e := O.openPartialHomeomorphSubtypeCoe hO
  have hv : ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞
      ((Subtype.val : O → A) ∘ e.symm) e.target :=
    contMDiffOn_id.congr (fun x hx => e.right_inv hx)
  intro x hx
  exact (ContMDiffWithinAt.subtypeVal_comp_iff O e.symm e.target x).mp (hv x hx)

private theorem partial_trans_holomorphic {k : ℕ} {A B D : CMfd.{u} k}
    (e : OpenPartialHomeomorph A B) (f : OpenPartialHomeomorph B D)
    (he : ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ e.symm e.target)
    (hf : ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ f.symm f.target) :
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (e.trans f) (e.trans f).source ∧
      ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (e.trans f).symm (e.trans f).target := by
  constructor
  · exact hf.1.comp (he.1.mono inter_subset_left) (fun _ hx => hx.2)
  · exact he.2.comp (hf.2.mono inter_subset_left) (fun _ hx => hx.2)

section Partial
variable {k : ℕ} {A E : CMfd.{u} k} (U : Opens A)
  (e : E ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ U) (hU : Nonempty U)

def openRangePartial : OpenPartialHomeomorph A E :=
  (U.openPartialHomeomorphSubtypeCoe hU).symm.trans e.symm.toHomeomorph.toOpenPartialHomeomorph

theorem openRangePartial_source : (openRangePartial U e hU).source=(U : Set A) := by
  unfold openRangePartial
  rw [OpenPartialHomeomorph.trans_source]
  simp only [OpenPartialHomeomorph.symm_source,Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]

theorem openRangePartial_holomorphic :
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (openRangePartial U e hU) (openRangePartial U e hU).source ∧
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (openRangePartial U e hU).symm (openRangePartial U e hU).target :=
  partial_trans_holomorphic (A := A) (B := CMfd.of U) (D := E) _ _
    (subtypeInclusion_holomorphic U hU).symm ⟨e.symm.contMDiff.contMDiffOn,e.contMDiff.contMDiffOn⟩

theorem openRangePartial_inverse_point (x : A) (hx : x ∈ U) :
    (e (openRangePartial U e hU x)).val=x := by
  let i := U.openPartialHomeomorphSubtypeCoe hU
  have hxi : x ∈ i.target := by
    rw [show i.target=(U : Set A) from U.openPartialHomeomorphSubtypeCoe_target hU]
    exact hx
  change (e (e.symm (i.symm x))).val=x
  rw [e.apply_symm_apply]
  exact i.right_inv hxi

theorem openRangePartial_at_inclusion (x : E) :
    openRangePartial U e hU (e x).val=x := by
  apply e.injective
  apply Subtype.ext
  exact openRangePartial_inverse_point U e hU (e x).val (e x).property
end Partial

private theorem normalizeSubmersionAt {m n : ℕ} {Y : CMfd.{u} m} {X : CMfd.{u} n}
    {g : Y → X} {y : Y}
    (h : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g y) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel (m-n))
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g y :=
  h.isSubmersionAtOfComplement_complement.trans_F (complementCoordinates h)

variable {m n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
section Original
variable (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)
private abbrev A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)

/-- Genuine entire source-chart submersion, ONLY original inputs. -/
theorem originalSourceChartSmoothMap_isSubmersion (i : Y) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalSourceChartSmoothMap hf M hM i) := by
  have hforms : Manifold.IsSubmersionOfComplement (ComplexModel (m-n))
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalSourceChartSmoothMap hf M hM i) := by
    intro y
    let B := actualLocalTerminalAtlas M hM
    let j := f (((A hf M hM).tower i).proj y).val
    let R : Opens ((A hf M hM).finalSpace i) := originalLocalSmoothChartArrowSourceOpen hf M hM i j
    have hy : y ∈ R := ⟨(((A hf M hM).tower i).proj y).property,B.point_mem j⟩
    let hR : Nonempty R := ⟨⟨y,hy⟩⟩
    let b := (R.openPartialHomeomorphSubtypeCoe hR).symm
    let g := originalLocalTerminalSmoothChartArrow hf M hM i j
    have hg := (originalLocalTerminalSmoothChartArrow_properties hf M hM i j).1
    let U := originalTerminalLocalRangeOpen M hM j
    let e := originalTerminalLocalBiholomorphism M hM j
    let hU : Nonempty U := ⟨e (g ⟨y,hy⟩)⟩
    let a := openRangePartial U e hU
    have hb : ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ b b.source ∧
        ContMDiffOn 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ b.symm b.target :=
      (subtypeInclusion_holomorphic (A := (A hf M hM).finalSpace i) R hR).symm
    have hbsource : b.source=(R : Set ((A hf M hM).finalSpace i)) := R.openPartialHomeomorphSubtypeCoe_target hR
    have hsquare : ∀ q ∈ b.source, a (originalSourceChartSmoothMap hf M hM i q)=g (b q) := by
      intro q hq
      have hbq : (b q).val=q := (R.openPartialHomeomorphSubtypeCoe hR).right_inv hq
      have hlocal := originalSourceChartSmoothMap_local hf M hM i j (b q)
      rw [hbq] at hlocal
      change originalSourceChartSmoothMap hf M hM i q=originalTerminalLocalInclusion M hM j (g (b q)) at hlocal
      rw [hlocal]
      exact openRangePartial_at_inclusion U e hU (g (b q))
    have hsource : b.source ⊆ (originalSourceChartSmoothMap hf M hM i) ⁻¹' a.source := by
      intro q hq
      change originalSourceChartSmoothMap hf M hM i q ∈ a.source
      rw [openRangePartial_source]
      have hbq : (b q).val=q := (R.openPartialHomeomorphSubtypeCoe hR).right_inv hq
      have hlocal := originalSourceChartSmoothMap_local hf M hM i j (b q)
      rw [hbq] at hlocal
      change originalSourceChartSmoothMap hf M hM i q=originalTerminalLocalInclusion M hM j (g (b q)) at hlocal
      rw [hlocal]
      exact (e (g (b q))).property
    exact isSubmersionAtOfComplement_local_square
      (X := B.finalSpace j) (X' := originalTerminalManifold M hM)
      (Y := CMfd.of (n := m) R) (Y' := (A hf M hM).finalSpace i)
      a b (openRangePartial_holomorphic U e hU) hb hg.contMDiff.continuous
      (normalizeSubmersionAt (hg.isSubmersionAt (b y)))
      (originalSourceChartSmoothMap_contMDiff hf M hM i).continuous.continuousAt
      (hbsource.symm ▸ hy) hsource hsquare
  exact hforms.isSubmersion

/-- The SAME entire original arbitrary-target Cartesian arrow is a genuine
submersion. No compactness, histories, or normal-form certificates are inputs. -/
theorem originalGlobalSmoothMap_isSubmersion :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalGlobalSmoothMap hf M hM) := by
  have hforms : Manifold.IsSubmersionOfComplement (ComplexModel (m-n))
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalGlobalSmoothMap hf M hM) := by
    intro z
    let N := markedPullback (m := m) f M
    let hN := original_ambient_domain_pullback hf M hM
    obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective N hN z
    let U := originalTerminalLocalRangeOpen N hN i
    let e := originalTerminalLocalBiholomorphism N hN i
    let hU : Nonempty U := ⟨e y⟩
    let b := openRangePartial U e hU
    let a : OpenPartialHomeomorph (originalTerminalManifold M hM) (originalTerminalManifold M hM) := OpenPartialHomeomorph.refl _
    have ha : ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ a a.source ∧
        ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ a.symm a.target :=
      ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩
    have hsquare : ∀ q ∈ b.source, a (originalGlobalSmoothMap hf M hM q)=originalSourceChartSmoothMap hf M hM i (b q) := by
      intro q hq
      have hqi : q ∈ U := by rwa [openRangePartial_source] at hq
      have hinc : originalTerminalLocalInclusion N hN i (b q)=q := openRangePartial_inverse_point U e hU q hqi
      exact (congrArg (originalGlobalSmoothMap hf M hM) hinc).symm.trans (originalGlobalSmoothMap_local hf M hM i (b q))
    have hp : originalTerminalLocalInclusion N hN i y ∈ b.source := by
      rw [openRangePartial_source]
      exact (e y).property
    exact isSubmersionAtOfComplement_local_square
      (X := originalTerminalManifold M hM) (X' := originalTerminalManifold M hM)
      (Y := (A hf M hM).finalSpace i) (Y' := originalTerminalManifold N hN)
      a b ha (openRangePartial_holomorphic U e hU)
      (originalSourceChartSmoothMap_contMDiff hf M hM i).continuous
      (normalizeSubmersionAt ((originalSourceChartSmoothMap_isSubmersion hf M hM i).isSubmersionAt _))
      (originalGlobalSmoothMap_contMDiff hf M hM).continuous.continuousAt hp
      (fun _ _ => mem_univ _) hsquare
  exact hforms.isSubmersion
end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalSubmersion
