/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFiniteFunctor
import Hironaka.Resolution.HironakaSmoothSubmersionContactCoefficientRestriction
/-! Actual original local terminal smooth arrows for arbitrary noncompact targets.
Complete three-node mathematics preceded code. Actual source chart intersections,
fixed-complement submersions and whole original marked dictionaries internally
supply genuinely restricted terminal histories before any chart arrow is chosen. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalLocalChartArrow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas
  HironakaOriginalTerminalOpenComparison HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalTerminalSubmersion HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionContactCoefficientRestriction HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange MaxLocusLocal
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}

private def openRestrictionMap (U : Opens Y) (V : Opens X) (hUV : ∀ y : U, f y.val ∈ V) : U → V :=
  fun y => ⟨f y.val,hUV y⟩

/-- Restriction to a genuine source open retains the SAME fixed complement,
including empty opens. Target subtype membership is true geometric membership. -/
private theorem openRestrictionMap_isSubmersionOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) (hUV : ∀ y : U, f y.val ∈ V) :
    Manifold.IsSubmersionOfComplement hf.complement
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (openRestrictionMap U V hUV) := by
  intro y
  let h := hf.isSubmersionOfComplement_complement y.val
  have hU : Nonempty U := ⟨y⟩
  have hV : Nonempty V := ⟨openRestrictionMap U V hUV y⟩
  let a := U.openPartialHomeomorphSubtypeCoe hU
  let b := V.openPartialHomeomorphSubtypeCoe hV
  let d := a.trans h.domChart
  let c := b.trans h.codChart
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv d c
  · exact ⟨mem_univ _,h.mem_domChart_source⟩
  · exact ⟨mem_univ _,h.mem_codChart_source⟩
  · exact restrictedChart_mem_maximal U hU h.domChart h.domChart_mem_maximalAtlas
  · exact restrictedChart_mem_maximal V hV h.codChart h.codChart_mem_maximalAtlas
  · intro z hz
    exact ⟨mem_univ _,h.source_subset_preimage_source hz.2⟩
  · intro z hz
    have hz' : z ∈ d.target := by simpa only [mfld_simps] using hz
    have ha : (a.symm (h.domChart.symm z)).val=h.domChart.symm z := a.right_inv hz'.2
    have hzo : z ∈ (h.domChart.extend 𝓘(ℂ,ComplexModel m)).target := by
      simpa only [mfld_simps] using hz'.1
    have he := h.writtenInCharts hzo
    simpa only [c,d,b,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps,openRestrictionMap,ha] using he

/-- The literal actual original source intersection with the target preimage. -/
def actualSmoothChartCommonOpen
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) : Opens Y := U ⊓ preimageOpen hf V

/-- The same intersection as a literal nested base in the original source open. -/
def actualSmoothChartNestedOpen
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) : Opens (CMfd.of (n := m) U) :=
  nestedOpens U (actualSmoothChartCommonOpen hf U V)

def actualSmoothChartBaseMap
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) : actualSmoothChartNestedOpen hf U V → V :=
  fun y => ⟨f y.val.val,y.property.2⟩

theorem actualSmoothChartBaseMap_isSubmersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (actualSmoothChartBaseMap hf U V) := by
  let Q := actualSmoothChartCommonOpen hf U V
  let hQV : ∀ y : Q, f y.val ∈ V := fun y => y.property.2
  have h := (openRestrictionMap_isSubmersionOfComplement hf Q V hQV).isSubmersion
  exact isSubmersion_precompose_biholomorphism
    (E := CMfd.of (n := m) (actualSmoothChartNestedOpen hf U V))
    (Z := CMfd.of (n := m) Q) (D := CMfd.of (n := n) V) h
    (nestedOpensDiffeo (show Q ≤ U from inf_le_left))

theorem actualSmoothChartBaseMap_whole_marked_dictionary
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (U : Opens Y) (V : Opens X) (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    markedPullback (m := m) (actualSmoothChartBaseMap hf U V) (pullback (Subtype.val : V → X) M)=
      pullback (Subtype.val : actualSmoothChartNestedOpen hf U V → U)
        (pullback (Subtype.val : U → Y) (markedPullback (m := m) f M)) := by
  have hbase := (actualSmoothChartBaseMap_isSubmersion hf U V).contMDiff
  have hN : (markedPullback (m := m) f M).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hI
  calc
    _ = markedPullback (m := m) ((Subtype.val : V → X) ∘ actualSmoothChartBaseMap hf U V) M :=
      (whole_markedPullback_comp contMDiff_subtype_val hbase M hI).symm
    _ = markedPullback (m := m) (f ∘ ((Subtype.val : U → Y) ∘
        (Subtype.val : actualSmoothChartNestedOpen hf U V → U))) M := rfl
    _ = markedPullback (m := m) ((Subtype.val : U → Y) ∘
        (Subtype.val : actualSmoothChartNestedOpen hf U V → U)) (markedPullback (m := m) f M) :=
      whole_markedPullback_comp hf.contMDiff (contMDiff_subtype_val.comp contMDiff_subtype_val) M hI
    _ = _ := whole_markedPullback_comp contMDiff_subtype_val contMDiff_subtype_val _ hN

section ActualOriginalCharts
variable (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

private def sourceOriginalAtlas : ActualLocalTerminalAtlas (markedPullback (m := m) f M) :=
  actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)

/-- The actual original source final-space open; no final-space domain input. -/
def originalLocalSmoothChartArrowSourceOpen (i : Y) (j : X) :
    Opens ((sourceOriginalAtlas hf M hM).finalSpace i) :=
  openPreimage ((sourceOriginalAtlas hf M hM).tower i)
    (actualSmoothChartNestedOpen hf ((sourceOriginalAtlas hf M hM).openSet i)
      ((actualLocalTerminalAtlas M hM).openSet j))

/-- Actual selected original local towers genuinely supply EVERY required
source and target canonical/terminal marked record, with no caller witnesses. -/
private theorem originalLocalSmoothChartArrow_history_data (i : Y) (j : X) :
    let A := sourceOriginalAtlas hf M hM
    let B := actualLocalTerminalAtlas M hM
    let W := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
    let MV := pullback (Subtype.val : B.openSet j → X) M
    IsInvDomain n MV ∧
      IsCanonical (markedPullback (m := m) (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j)) MV)
        ((canonicalInvariant m).inv (markedPullback (m := m)
          (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j)) MV)) (restrict W (A.tower i)) ∧
      IsGeoResolution (markedPullback (m := m)
        (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j)) MV) (restrict W (A.tower i)) := by
  dsimp only
  let A := sourceOriginalAtlas hf M hM
  let B := actualLocalTerminalAtlas M hM
  let U := A.openSet i
  let V := B.openSet j
  let W := actualSmoothChartNestedOpen hf U V
  let hN := original_ambient_domain_pullback hf M hM
  have hNU := InvDomainTowerAlong.isInvDomain_pullback_val U hN
  have hS := original_terminal_open_history_data _ hNU (A.tower i) (A.canonical i) (A.terminal i) W
  have hrec := actualSmoothChartBaseMap_whole_marked_dictionary hf U V M hM.isWellFormed.isCoherent
  exact ⟨InvDomainTowerAlong.isInvDomain_pullback_val V hM,hrec.symm ▸ hS.2.1,hrec.symm ▸ hS.2.2⟩

/-- ONLY original M/domain and smooth f choose the real original chart arrow. -/
def originalLocalTerminalSmoothChartArrow (i : Y) (j : X) :
    originalLocalSmoothChartArrowSourceOpen hf M hM i j → (actualLocalTerminalAtlas M hM).finalSpace j :=
  let A := sourceOriginalAtlas hf M hM
  let B := actualLocalTerminalAtlas M hM
  let W := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
  let hbase := actualSmoothChartBaseMap_isSubmersion hf (A.openSet i) (B.openSet j)
  let hdata := originalLocalSmoothChartArrow_history_data hf M hM i j
  terminalSmoothMap hbase (pullback (Subtype.val : B.openSet j → X) M) hdata.1
    (restrict W (A.tower i)) (B.tower j) hdata.2.1 (B.canonical j) hdata.2.2 (B.terminal j)

theorem originalLocalTerminalSmoothChartArrow_properties (i : Y) (j : X) :
    let A := sourceOriginalAtlas hf M hM
    let B := actualLocalTerminalAtlas M hM
    let W := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
    let G := originalLocalTerminalSmoothChartArrow hf M hM i j
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ y, ((B.tower j).proj (G y)).val=f (((A.tower i).proj y.val).val)) ∧
      HolomorphicSquarePullback (actualSmoothChartBaseMap hf (A.openSet i) (B.openSet j)) G
        (restrict W (A.tower i)).proj (B.tower j).proj := by
  dsimp only
  let A := sourceOriginalAtlas hf M hM
  let B := actualLocalTerminalAtlas M hM
  let W := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
  let hbase := actualSmoothChartBaseMap_isSubmersion hf (A.openSet i) (B.openSet j)
  let hdata := originalLocalSmoothChartArrow_history_data hf M hM i j
  have hG := terminalSmoothMap_properties hbase (pullback (Subtype.val : B.openSet j → X) M) hdata.1
    (restrict W (A.tower i)) (B.tower j) hdata.2.1 (B.canonical j) hdata.2.2 (B.terminal j)
  refine ⟨hG.1,?_,hG.2.2⟩
  intro y
  let q : openPreimage (A.tower i) W := y
  have h := congrArg Subtype.val (hG.2.1 q)
  change ((B.tower j).proj (originalLocalTerminalSmoothChartArrow hf M hM i j q)).val=
    f (((restrict W (A.tower i)).proj q).val.val) at h
  have hp := congrArg (fun z : A.openSet i => z.val) (proj_restrict W (A.tower i) q)
  exact h.trans (congrArg f hp)


end ActualOriginalCharts
end
end Hironaka.HironakaSmoothSubmersionOriginalLocalChartArrow
