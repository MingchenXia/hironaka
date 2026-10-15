/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCrossingLowerHistory
import Hironaka.Invariant.ContactEmptyPrefix
/-! Genuine original zero-contact lower records across an interior identity empty step.
Complete mathematics written first in `hironaka-original-interior-zero-lower-history-extension.tex`. Whole higher recursive
invariant value/order transport and noncompact scheduling remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalInteriorZeroLowerHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit StepOneRegime StepOneValue StepOneValueMasked StepOneLowerDomain
  MonomialInvariantEmptyMember HomogenizedGlueingTower MemberInterLocusAlong
  MemberInterTowerAlong TangentDirectionAlong HomogenizedIdealAlong
  CoefficientIdealRestriction MarkedIdealBiholomorphism
  HironakaOriginalInteriorEmptyHistory
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- Genuine closed carriers are unchanged across the original interior identity
empty step, for arbitrary actual heads and tails. -/
theorem strictAlong_closed_interior_empty {B : Set X} (hB : IsClosed B)
    (H : BlowupTower X A) (S : BlowupTower A Y) :
    strictAlong (interiorEmptyHistory H S) B = strictAlong (H.append S) B := by
  rw [interiorEmptyHistory,strictAlong_append,strictAlong_append,strictAlong_step,
    ContactCanonicalAlong.geoStrictTransform_empty continuous_id (isClosed_strictAlong H hB)]
  rfl

/-- The actual chosen contact zero set has a genuine closed representative on
its actual open, including the absent-choice branch whose open is empty. -/
theorem chosen_contact_closed_representative (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (x : X) :
    IsOpen (tangentChoice M x).1 ∧ ∃ B : Set X, IsClosed B ∧
      (M.N ∩ {z | (tangentChoice M x).2 z = 0}) ∩ (tangentChoice M x).1 =
        B ∩ (tangentChoice M x).1 := by
  classical
  by_cases h : ∃ (U : Set X) (w : X → ℂ), x ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U w
  · have hu := (tangentChoice_spec M h).2
    let U := (tangentChoice M x).1
    let w := (tangentChoice M x).2
    let B : Set X := M.N ∩ closure ({z | w z = 0} ∩ U)
    have hcont : ∀ z ∈ U, ContinuousAt w z := fun z hz =>
      HolomorphicAt.continuousAt (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hM.isCoherent hg) (M.d-1) z w (hu.mem z hz))
    refine ⟨hu.isOpen,B,hM.isClosedSubmanifold_N.1.inter isClosed_closure,?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzN,hz0⟩,hzU⟩
      exact ⟨⟨hzN,subset_closure ⟨hz0,hzU⟩⟩,hzU⟩
    · rintro ⟨⟨hzN,hzc⟩,hzU⟩
      refine ⟨⟨hzN,?_⟩,hzU⟩
      by_contra hne
      have hev : ∀ᶠ a in 𝓝 z, w a ≠ 0 := (hcont z hzU).eventually_ne hne
      obtain ⟨a,ha,ha'⟩ := mem_closure_iff_nhds.mp hzc _ hev
      exact ha ha'.1
  · rw [tangentChoice,dif_neg h]
    exact ⟨isOpen_empty,∅,isClosed_empty,by simp⟩

/-- The whole actual mask sees equal original contact carriers. No global
closedness of the chosen zero set or contact equality is an input. -/
theorem masked_contact_carrier_dictionary (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (S : BlowupTower A Y) (p : Y) :
    (Subtype.val : maskB M (H.append S) p → Y) ⁻¹'
        strictAlong (interiorEmptyHistory H S)
          (M.N ∩ {x | (tangentChoice M ((interiorEmptyHistory H S).proj p)).2 x = 0}) =
      (Subtype.val : maskB M (H.append S) p → Y) ⁻¹'
        strictAlong (H.append S)
          (M.N ∩ {x | (tangentChoice M ((H.append S).proj p)).2 x = 0}) := by
  rw [proj_interiorEmptyHistory]
  obtain ⟨hU,B,hB,hAB⟩ := chosen_contact_closed_representative M hM ((H.append S).proj p)
  have hnew := ContactEquivalenceStage.strictAlong_inter_preimage_eq hU hAB
    (interiorEmptyHistory H S)
  have hold := ContactEquivalenceStage.strictAlong_inter_preimage_eq hU hAB (H.append S)
  rw [strictAlong_closed_interior_empty hB H S,proj_interiorEmptyHistory] at hnew
  have htrace := hnew.trans hold.symm
  ext z
  have hzU : (H.append S).proj z ∈ (tangentChoice M ((H.append S).proj p)).1 :=
    (interior_subset z.property).1
  have he := Set.ext_iff.mp htrace (z : Y)
  simpa only [mem_inter_iff,mem_preimage,hzU,and_true] using he

private theorem pullback_contact_insertEmpty_heq (J : MarkedIdeal n Y) (j : ℕ)
    (C D : Set Y) (U V : Opens Y) (hUV : U=V)
    (hCD : (Subtype.val : V → Y) ⁻¹' C = (Subtype.val : V → Y) ⁻¹' D) :
    HEq (MarkedIdeal.pullback (Subtype.val : U → Y) (withN (coeffMarkedAlong (insertEmpty j J)) C))
      (insertEmpty j (MarkedIdeal.pullback (Subtype.val : V → Y) (withN (coeffMarkedAlong J) D))) := by
  subst U
  apply heq_of_eq
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hCD
  · change (J.E.insertIdx j ∅).map ((Subtype.val : V → Y) ⁻¹' ·) =
      (J.E.map ((Subtype.val : V → Y) ⁻¹' ·)).insertIdx j ∅
    rw [List.map_insertIdx,preimage_empty]
  · rfl
  · rfl

/-- The true future insertion index is valid in the WHOLE zero lower boundary;
the original members have been kept, rather than deleted or filtered. -/
theorem zeroLowerIndex_le_boundary (M : MarkedIdeal n X)
    (H : BlowupTower X A) (S : BlowupTower A Y) (p : Y) :
    M.E.length + H.length ≤ (lowerMarkedM M 0 (H.append S) p).E.length := by
  change M.E.length + H.length ≤
    ((geoTransformAlong (barMarked M) (H.append S)).E.map
      ((Subtype.val : maskB M (H.append S) p → Y) ⁻¹' ·)).length
  rw [List.length_map,length_E_geoTransformAlong,BlowupTower.length_append]
  change M.E.length + H.length ≤ M.E.length + (H.length + S.length)
  omega

/-- The ACTUAL original zero-contact lower record across the interior empty
step. The local chosen-contact geometry and entire lower carrier are produced
internally; no contact/lower equality is assumed. -/
theorem original_zero_lower_record (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (S : BlowupTower A Y) (hS : 0 < S.length) (p : Y) :
    HEq (lowerMarkedM M 0 (interiorEmptyHistory H S) p)
      (insertEmpty (M.E.length + H.length) (lowerMarkedM M 0 (H.append S) p)) := by
  change HEq (lowerMarkedB M (interiorEmptyHistory H S) p)
    (insertEmpty (M.E.length + H.length) (lowerMarkedB M (H.append S) p))
  unfold lowerMarkedB
  rw [whole_record_of_nonempty_tail (barMarked M) (isWellFormed_barMarked M hM) H hH S hS]
  exact pullback_contact_insertEmpty_heq _ _ _ _ _ _
    (maskB_dictionary M hM H hH S p) (masked_contact_carrier_dictionary M hM H S p)

/-- BOTH entire original selected split records at the computed own-level
short run, including level zero, with their literal common final tail. -/
theorem actual_short_all_level_splits (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y)
    (hshort : regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y < S.length) :
    let r := regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y
    let r' := regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y
    r' = r ∧ split (H.append S) r = ⟨(split S r).1,H.append (head S r),tail S r⟩ ∧
      split (interiorEmptyHistory H S) r' =
        ⟨(split S r).1,interiorEmptyHistory H (head S r),tail S r⟩ := by
  dsimp only
  have hr : regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y))
      (interiorEmptyHistory H S) y =
      regimeRun (stepRegime M (level M (H.append S) y)) (H.append S) y := by
    rw [level_dictionary M hM H hH S y,stepRegime_run_dictionary M hM H hH]
    exact if_pos hshort
  refine ⟨hr,StepOneEmptyPrefix.split_append_of_le H S _ hshort.le,?_⟩
  rw [hr]
  exact StepOneEmptyPrefix.split_append_of_le
    (H.step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty) S _ hshort.le

private theorem restrict_heq_of_equal_masks {D B : CMfd.{u} n}
    (U V : Opens D) (hUV : U=V) (Q : BlowupTower D B) :
    HEq (restrict U Q) (restrict V Q) := by
  cases hUV
  rfl

/-- Genuine selected short-run ZERO-contact lower records and WHOLE actual
restricted tails. The selected-prefix nonemptiness and true whole-boundary
index are consequences, not caller certificates. -/
theorem actual_short_zero_lower_diagram (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H) (S : BlowupTower A Y)
    (y : Y) (hlevel : level M (H.append S) y = 0)
    (hshort : regimeRun (stepRegime M 0) (H.append S) y < S.length) :
    let r := regimeRun (stepRegime M 0) (H.append S) y
    let P := head S r
    let Q := tail S r
    let p := Q.proj y
    regimeRun (stepRegime M (level M (interiorEmptyHistory H S) y)) (interiorEmptyHistory H S) y = r ∧
      lowerMask M 0 (interiorEmptyHistory H P) p = lowerMask M 0 (H.append P) p ∧
      M.E.length + H.length ≤ (lowerMarkedM M 0 (H.append P) p).E.length ∧
      HEq (lowerMarkedM M 0 (interiorEmptyHistory H P) p)
        (insertEmpty (M.E.length + H.length) (lowerMarkedM M 0 (H.append P) p)) ∧
      HEq (restrict (lowerMask M 0 (interiorEmptyHistory H P) p) Q)
        (restrict (lowerMask M 0 (H.append P) p) Q) := by
  dsimp only
  have hp : 0 < (head S (regimeRun (stepRegime M 0) (H.append S) y)).length := by
    rw [length_head]
    omega
  have hm := lowerMask_dictionary M hM H hH
    (head S (regimeRun (stepRegime M 0) (H.append S) y)) 0
    ((tail S (regimeRun (stepRegime M 0) (H.append S) y)).proj y)
  have hall := actual_short_all_level_splits M hM H hH S y (by simpa only [hlevel] using hshort)
  rw [hlevel] at hall
  exact ⟨hall.1,hm,zeroLowerIndex_le_boundary M H _ _,
    original_zero_lower_record M hM H hH _ hp _,restrict_heq_of_equal_masks _ _ hm _⟩

end
end Hironaka.HironakaOriginalInteriorZeroLowerHistory
