/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace
import Hironaka.Invariant.StepOneTangentChange

/-!
Actual all-head empty-stage compression of independently chosen ordered
marking-one monomial procedures on genuine opens. The complete mathematics
was written first in Mathematics.tex. Entire controls and literal retained
history, independent OWN finite bounds and genuine choice cocycles are produced.
Formal registration/native build/publication and higher-invariant functoriality
remain pending; no caller compression or termination certificate is used.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOrderedChoiceOpenCompression
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
open BlowupTowerIsomorphism HironakaNormalCrossingsOpenRestrictionSeparation
open HironakaNormalCrossingsOrderedChoiceComparison HironakaNormalCrossingsOrderedOpenTrace
open HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionOrderedChoiceImageTrace
open HironakaNormalCrossingsOrderedMonomialTail HironakaSmoothSubmersionOrderedMonomialProcedure
open HironakaNormalCrossingsFiniteMarkedCompletion NormalCrossings
open RelativePrincipalizationSpan GermIdealPullbackCalculus MarkedIdeals MarkedIdeals.MarkedIdeal
open HironakaSmoothSubmersionCoefficientIdeals HironakaDivisorResidual IdealWeightPowers MarkedIdealBiholomorphism
noncomputable section
section Transport
variable {n : ℕ} {A' A A'' D' D D'' : CMfd.{u} n}
/-- Every genuine matched or silent source stage survives true target tower transport. -/
theorem compression_target_iso
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A}
    {Ψ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A''}
    {T' : BlowupTower A' D'} {T : BlowupTower A D} {S : BlowupTower A'' D''}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D}
    {θ : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D''}
    (hc : IsStageCompression Φ T' T χ) (hi : IsTowerIso Ψ T S θ) :
    IsStageCompression (Φ.trans Ψ) T' S (χ.trans θ) := by
  induction hc generalizing D'' with
  | refl =>
    cases S with
    | refl => obtain rfl := hi.refl_inv; exact .refl
    | step S C π hπ => exact absurd hi.length_eq (by simp)
  | @matched Y' Y Z' Z T' T χ hc C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    cases S with
    | refl => exact absurd hi.length_eq (by simp)
    | step S CS πS hπS =>
      obtain ⟨θ₀,hi₀,hcomm₀,hC₀⟩ := hi.step_inv
      refine .matched (ih hi₀) hπ' hπS (χ₁.trans θ) (fun z => ?_) ?_
      · simp only [Diffeomorph.coe_trans,Function.comp_apply]
        rw [hcomm₀,hcomm]
      · rw [Diffeomorph.coe_trans,preimage_comp,hC₀,hC]
  | @silent Y' Y Z' T' T χ hc π' hπ' χ₁ hcomm ih =>
    refine .silent (ih hi) hπ' (χ₁.trans θ) (fun z => ?_)
    simp only [Diffeomorph.coe_trans,Function.comp_apply]
    rw [hcomm]
end Transport
section ActualRestriction
variable {n : ℕ} {A : CMfd.{u} n}
/-- The actual internally produced global chosen-reference comparison restricts to literal open towers. -/
theorem exists_chosen_reference_restrict_iso (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (U : Opens A) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (procedureTower q F hF) U),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (chosenProcedure β q A F hF).T) (restrict U (procedureTower q F hF)) χ := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞
  have hb : ∀ x : A, x ∈ U ↔ Φ x ∈ U := fun _ => Iff.rfl
  have hi := chosenProcedure_self_reference β q F hF
  have he := StepOneTangentChange.isTowerIso_restrictOpens hb hi
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hi hb)
  have hbase : StepOneTangentChange.diffeoOpens Φ U U hb =
      Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞ :=
    Diffeomorph.ext (fun _ => Subtype.ext rfl)
  rw [hbase] at he
  exact ⟨_,he⟩
/-- Actual bounded reference compression is produced from the literal trace induction. -/
theorem exists_reference_open_compression (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (procedureTower q F hF) U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U,
      IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (procedureTower q F hF))
        (procedureTower (traceCount (Subtype.val : U → A) n q F)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) χ := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞
  obtain ⟨χ,hχ⟩ := literal_restrict_to_uncompressed_trace q U Φ F hF (openWeights_isSNCDivisor U F hF)
  have hc := tracedTower_genuine_empty_compression (B := CMfd.of (n := n) U)
    (Subtype.val : U → A) q F (openWeights_isSNCDivisor U F hF)
  have hfull := hc.source_iso hχ
  rw [tracedTower_is_independent_procedure _ _ _ _ (initialTrace _ F)] at hfull
  refine ⟨χ,?_⟩
  simpa only [Φ,Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using hfull
/-- True original SNC and two primitive Cartier choices internally supply actual all-head open compression. -/
theorem exists_chosen_open_compression (β α : CartierBlowupChoices.{u} n)
    (q : ℕ) (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
          (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
            (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D,
      IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (chosenProcedure β q A F hF).T)
        (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T χ := by
  obtain ⟨χg,hg⟩ := exists_chosen_reference_restrict_iso β q U F hF
  obtain ⟨χr,hr⟩ := exists_reference_open_compression q U F hF
  have hl := (chosenProcedure_self_reference (A := CMfd.of (n := n) U) α (traceCount (Subtype.val : U → A) n q F)
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).symm
  have hc := compression_target_iso hr hl
  have hfull := hc.source_iso hg
  exact ⟨_,by simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using hfull⟩
/-- BOTH genuine chosen procedures complete at their OWN internally computed coefficient sums. -/
theorem exists_completed_chosen_open_compression (β α : CartierBlowupChoices.{u} n)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ χ : CMfd.of (n := n) (openPreimage (chosenProcedure β (coefficientSum F) A F hF).T U)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
          (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
            (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D,
      IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (chosenProcedure β (coefficientSum F) A F hF).T)
        (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T χ := by
  obtain ⟨χg,hg⟩ := exists_chosen_reference_restrict_iso β (coefficientSum F) U F hF
  obtain ⟨χr,hr⟩ := actual_completed_open_compression U F hF
  have hl := (chosenProcedure_self_reference (A := CMfd.of (n := n) U) α
    (coefficientSum (pulledWeights (Subtype.val : U → A) F))
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).symm
  have hc := compression_target_iso hr hl
  have hfull := hc.source_iso hg
  exact ⟨_,by simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans,Diffeomorph.trans_refl] using hfull⟩

/-- The actual produced endpoint biholomorphism is output, never a caller comparison certificate. -/
def chosenOpenCompression (β α : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
        (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  Classical.choose (exists_chosen_open_compression β α q U F hF)

theorem chosenOpenCompression_spec (β α : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (chosenProcedure β q A F hF).T)
      (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T
      (chosenOpenCompression β α q U F hF) :=
  Classical.choose_spec (exists_chosen_open_compression β α q U F hF)

/-- The genuine completed endpoint is independently generated with literal OWN bounds. -/
def completedChosenOpenCompression (β α : CartierBlowupChoices.{u} n)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    CMfd.of (n := n) (openPreimage (chosenProcedure β (coefficientSum F) A F hF).T U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
        (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  Classical.choose (exists_completed_chosen_open_compression β α U F hF)

theorem completedChosenOpenCompression_spec (β α : CartierBlowupChoices.{u} n)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsStageCompression (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (chosenProcedure β (coefficientSum F) A F hF).T)
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T
      (completedChosenOpenCompression β α U F hF) :=
  Classical.choose_spec (exists_completed_chosen_open_compression β α U F hF)

/-- True all-head compression commutes with the literal whole chosen projections. -/
theorem chosenOpenCompression_proj_comm (β α : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ z, (restrict U (chosenProcedure β q A F hF).T).proj z =
      (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.proj
        (chosenOpenCompression β α q U F hF z) :=
  (chosenOpenCompression_spec β α q U F hF).proj_comm

/-- The OWN completed geometric compression commutes with its true projections. -/
theorem completedChosenOpenCompression_proj_comm (β α : CartierBlowupChoices.{u} n)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ z, (restrict U (chosenProcedure β (coefficientSum F) A F hF).T).proj z =
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.proj
        (completedChosenOpenCompression β α U F hF z) :=
  (completedChosenOpenCompression_spec β α U F hF).proj_comm


/-- Every actual chosen stage internally retains whole ideal coherence. -/
theorem chosen_stage_coherent (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β q A F hF).T).ideal.IsCoherent := by
  rw [chosen_whole_reference]
  exact isCoherent_pullback (chosenProcedure β q A F hF).back.contMDiff
    (reference_stage_coherent q F hF)

/-- Whole actual raw marked control of the literal restricted chosen global tower. -/
def rawRestrictedMarked (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal n (CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T U)) :=
  geoTransformAlong
    (MarkedIdeal.pullback (Subtype.val : U → A) (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
    (restrict U (chosenProcedure β q A F hF).T)

/-- Genuine restriction of the actual test tower internally gives the ENTIRE raw marked record. -/
theorem rawRestrictedMarked_eq (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    rawRestrictedMarked β q U F hF =
      markedPullback (m := n)
        (Subtype.val : openPreimage (chosenProcedure β q A F hF).T U → (chosenProcedure β q A F hF).D)
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (chosenProcedure β q A F hF).T) := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  exact MarkedIdealRestrictOpen.geoTransformAlong_restrict U hw.isClosedSubmanifold_N hw.isCoherent
    _ (chosenProcedure_isGeoTestTower β q F hF)

/-- The true inverse compression square retains the whole original projections as actual maps. -/
theorem chosenOpenCompression_back_square (β α : CartierBlowupChoices.{u} n) (q : ℕ)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q A F hF).back ∘
        (Subtype.val : openPreimage (chosenProcedure β q A F hF).T U → (chosenProcedure β q A F hF).D) ∘
        (chosenOpenCompression β α q U F hF).symm =
      (Subtype.val : U → A) ∘
        (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back := by
  funext z
  have he := chosenOpenCompression_proj_comm β α q U F hF
    ((chosenOpenCompression β α q U F hF).symm z)
  rw [Diffeomorph.apply_symm_apply] at he
  have hv := congrArg (Subtype.val : U → A) he
  rw [proj_restrict] at hv
  rw [ChosenOutput.proj_eq,ChosenOutput.proj_eq]
  exact hv

/-- The internally generated completed compression has the SAME true whole projection square. -/
theorem completedChosenOpenCompression_back_square (β α : CartierBlowupChoices.{u} n)
    (U : Opens A) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β (coefficientSum F) A F hF).back ∘
        (Subtype.val : openPreimage (chosenProcedure β (coefficientSum F) A F hF).T U →
          (chosenProcedure β (coefficientSum F) A F hF).D) ∘
        (completedChosenOpenCompression β α U F hF).symm =
      (Subtype.val : U → A) ∘
        (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back := by
  funext z
  have he := completedChosenOpenCompression_proj_comm β α U F hF
    ((completedChosenOpenCompression β α U F hF).symm z)
  rw [Diffeomorph.apply_symm_apply] at he
  have hv := congrArg (Subtype.val : U → A) he
  rw [proj_restrict] at hv
  rw [ChosenOutput.proj_eq,ChosenOutput.proj_eq]
  exact hv


/-- The actual independently chosen local controlled datum at the internally retained prefix. -/
def localOpenMarked (α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal n (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  geoTransformAlong (monomialMarkedIdeal (n := n) ((pulledWeights (Subtype.val : U → A) F).map Prod.fst)
    (pulledWeights (Subtype.val : U → A) F))
    (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T

/-- The SAME true local OWN-completed controlled marked datum. -/
def completedLocalOpenMarked (α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal n (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  geoTransformAlong (monomialMarkedIdeal (n := n) ((pulledWeights (Subtype.val : U → A) F).map Prod.fst)
    (pulledWeights (Subtype.val : U → A) F))
    (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T

/-- The internally produced actual retained RAW restricted record, including literal empty metadata. -/
def retainedRestrictedMarked (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal n (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  let R := rawRestrictedMarked β q U F hF
  let ψ := (chosenOpenCompression β α q U F hF).symm
  { N := ψ ⁻¹' R.N
    E := (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => ψ ⁻¹' ((R.E[k]?).getD ∅))
    ideal := GermIdeal.pullback (m := n) ψ R.ideal
    d := R.d }

/-- OWN-completed raw record retains the same genuine global creation mask. -/
def completedRetainedRestrictedMarked (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal n (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  let R := rawRestrictedMarked β (coefficientSum F) U F hF
  let ψ := (completedChosenOpenCompression β α U F hF).symm
  { N := ψ ⁻¹' R.N
    E := (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
      (fun k => ψ ⁻¹' ((R.E[k]?).getD ∅))
    ideal := GermIdeal.pullback (m := n) ψ R.ideal
    d := R.d }

/-- Source OWN recursion and the real reference trace internally supply its entire actual local record. -/
theorem localOpenMarked_eq_trace (α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    localOpenMarked α q U F hF =
      markedPullback (m := n) (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back
        (traceStageMarked U q F hF) := by
  unfold localOpenMarked
  rw [chosen_whole_reference,actual_open_trace_whole_marked]

/-- The same genuine local OWN-completed trace holds with its own independently computed bound. -/
theorem completedLocalOpenMarked_eq_trace (α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedLocalOpenMarked α U F hF =
      markedPullback (m := n)
        (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
          (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back
        (traceStageMarked U (coefficientSum F) F hF) := by
  unfold completedLocalOpenMarked
  rw [chosen_whole_reference,actual_completed_open_whole_marked]

/-- ENTIRE original controlled ideal equality across the actual all-head compressed geometry. -/
theorem localOpenMarked_ideal_eq (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (localOpenMarked α q U F hF).ideal = (retainedRestrictedMarked β α q U F hF).ideal := by
  change (localOpenMarked α q U F hF).ideal =
    GermIdeal.pullback (m := n) (chosenOpenCompression β α q U F hF).symm (rawRestrictedMarked β q U F hF).ideal
  rw [localOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) (Subtype.val : U → A)
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).ideal) =
    GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) _
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).ideal))
  rw [← coherent_pullback_comp contMDiff_subtype_val
    (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back.contMDiff
    _ (reference_stage_coherent q F hF)]
  rw [← coherent_pullback_comp (chosenProcedure β q A F hF).back.contMDiff contMDiff_subtype_val
    _ (reference_stage_coherent q F hF)]
  rw [← coherent_pullback_comp ((chosenProcedure β q A F hF).back.contMDiff.comp contMDiff_subtype_val)
    (chosenOpenCompression β α q U F hF).symm.contMDiff _ (reference_stage_coherent q F hF)]
  rw [Function.comp_assoc,chosenOpenCompression_back_square]

/-- The actual whole controlled carrier is transported by the same true inverse compression. -/
theorem localOpenMarked_N_eq (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (localOpenMarked α q U F hF).N = (retainedRestrictedMarked β α q U F hF).N := by
  change (localOpenMarked α q U F hF).N = (chosenOpenCompression β α q U F hF).symm ⁻¹'
    (rawRestrictedMarked β q U F hF).N
  rw [localOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change ((Subtype.val : U → A) ∘
    (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back) ⁻¹' _ =
    ((chosenProcedure β q A F hF).back ∘ _ ∘ (chosenOpenCompression β α q U F hF).symm) ⁻¹' _
  rw [chosenOpenCompression_back_square]


private theorem preimage_getD {X Y : Type u} (f : Y → X) (E : List (Set X)) (k : ℕ) :
    ((E.map (f ⁻¹' ·))[k]?).getD ∅ = f ⁻¹' ((E[k]?).getD ∅) := by
  rw [List.getElem?_map]
  cases E[k]? <;> rfl

/-- The true entire raw boundary supplies the literal retained original/creation sublist. -/
theorem localOpenMarked_E_eq (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (localOpenMarked α q U F hF).E = (retainedRestrictedMarked β α q U F hF).E := by
  change (localOpenMarked α q U F hF).E =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => (chosenOpenCompression β α q U F hF).symm ⁻¹' (((rawRestrictedMarked β q U F hF).E[k]?).getD ∅))
  rw [localOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change (traceStageMarked U q F hF).E.map
    ((chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back ⁻¹' ·) =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => (chosenOpenCompression β α q U F hF).symm ⁻¹'
        (((((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).E.map
          ((chosenProcedure β q A F hF).back ⁻¹' ·)).map
          ((Subtype.val : openPreimage (chosenProcedure β q A F hF).T U → (chosenProcedure β q A F hF).D) ⁻¹' ·))[k]?).getD ∅))
  simp_rw [preimage_getD]
  rw [show (traceStageMarked U q F hF).E =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => (Subtype.val : U → A) ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).E[k]?).getD ∅))
    from rfl,List.map_map]
  change (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
    (fun k => ((Subtype.val : U → A) ∘
      (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back) ⁻¹' _) =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n q F).map
      (fun k => ((chosenProcedure β q A F hF).back ∘ _ ∘ (chosenOpenCompression β α q U F hF).symm) ⁻¹' _)
  rw [chosenOpenCompression_back_square]
  rfl

/-- The genuine whole marking is kept literally one across all matched and silent heads. -/
theorem localOpenMarked_d_eq (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (localOpenMarked α q U F hF).d = (retainedRestrictedMarked β α q U F hF).d := by
  change (localOpenMarked α q U F hF).d = (rawRestrictedMarked β q U F hF).d
  rw [localOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  rfl

/-- Actual independently chosen local WHOLE record equals the retained actual RAW restricted global control. -/
theorem localOpenMarked_eq_retained (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    localOpenMarked α q U F hF = retainedRestrictedMarked β α q U F hF :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of (localOpenMarked_N_eq β α q U F hF)
    (localOpenMarked_E_eq β α q U F hF) (localOpenMarked_ideal_eq β α q U F hF)
    (localOpenMarked_d_eq β α q U F hF)

/-- Entire actual OWN-completed dictionary, using both genuine independent bounds. -/
theorem completedLocalOpenMarked_ideal_eq (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedLocalOpenMarked α U F hF).ideal = (completedRetainedRestrictedMarked β α U F hF).ideal := by
  change (completedLocalOpenMarked α U F hF).ideal =
    GermIdeal.pullback (m := n) (completedChosenOpenCompression β α U F hF).symm (rawRestrictedMarked β (coefficientSum F) U F hF).ideal
  rw [completedLocalOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) (Subtype.val : U → A)
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).ideal) =
    GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) _ (GermIdeal.pullback (m := n) _
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).ideal))
  rw [← coherent_pullback_comp contMDiff_subtype_val
    (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back.contMDiff
    _ (reference_stage_coherent (coefficientSum F) F hF)]
  rw [← coherent_pullback_comp (chosenProcedure β (coefficientSum F) A F hF).back.contMDiff contMDiff_subtype_val
    _ (reference_stage_coherent (coefficientSum F) F hF)]
  rw [← coherent_pullback_comp ((chosenProcedure β (coefficientSum F) A F hF).back.contMDiff.comp contMDiff_subtype_val)
    (completedChosenOpenCompression β α U F hF).symm.contMDiff _ (reference_stage_coherent (coefficientSum F) F hF)]
  rw [Function.comp_assoc,completedChosenOpenCompression_back_square]


/-- Entire actual OWN-completed dictionary, using both genuine independent bounds. -/
theorem completedLocalOpenMarked_N_eq (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedLocalOpenMarked α U F hF).N = (completedRetainedRestrictedMarked β α U F hF).N := by
  change (completedLocalOpenMarked α U F hF).N = (completedChosenOpenCompression β α U F hF).symm ⁻¹'
    (rawRestrictedMarked β (coefficientSum F) U F hF).N
  rw [completedLocalOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change ((Subtype.val : U → A) ∘
    (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back) ⁻¹' _ =
    ((chosenProcedure β (coefficientSum F) A F hF).back ∘ _ ∘ (completedChosenOpenCompression β α U F hF).symm) ⁻¹' _
  rw [completedChosenOpenCompression_back_square]


/-- Entire actual OWN-completed dictionary, using both genuine independent bounds. -/
theorem completedLocalOpenMarked_E_eq (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedLocalOpenMarked α U F hF).E = (completedRetainedRestrictedMarked β α U F hF).E := by
  change (completedLocalOpenMarked α U F hF).E =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
      (fun k => (completedChosenOpenCompression β α U F hF).symm ⁻¹' (((rawRestrictedMarked β (coefficientSum F) U F hF).E[k]?).getD ∅))
  rw [completedLocalOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  change (traceStageMarked U (coefficientSum F) F hF).E.map
    ((chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back ⁻¹' ·) =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
      (fun k => (completedChosenOpenCompression β α U F hF).symm ⁻¹'
        (((((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).E.map
          ((chosenProcedure β (coefficientSum F) A F hF).back ⁻¹' ·)).map
          ((Subtype.val : openPreimage (chosenProcedure β (coefficientSum F) A F hF).T U → (chosenProcedure β (coefficientSum F) A F hF).D) ⁻¹' ·))[k]?).getD ∅))
  simp_rw [preimage_getD]
  rw [show (traceStageMarked U (coefficientSum F) F hF).E =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
      (fun k => (Subtype.val : U → A) ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).E[k]?).getD ∅))
    from rfl,List.map_map]
  change (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
    (fun k => ((Subtype.val : U → A) ∘
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).back) ⁻¹' _) =
    (List.range F.length ++ newHistoryTrace (Subtype.val : U → A) n (coefficientSum F) F).map
      (fun k => ((chosenProcedure β (coefficientSum F) A F hF).back ∘ _ ∘ (completedChosenOpenCompression β α U F hF).symm) ⁻¹' _)
  rw [completedChosenOpenCompression_back_square]
  rfl


/-- Entire actual OWN-completed dictionary, using both genuine independent bounds. -/
theorem completedLocalOpenMarked_d_eq (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedLocalOpenMarked α U F hF).d = (completedRetainedRestrictedMarked β α U F hF).d := by
  change (completedLocalOpenMarked α U F hF).d = (rawRestrictedMarked β (coefficientSum F) U F hF).d
  rw [completedLocalOpenMarked_eq_trace,rawRestrictedMarked_eq,chosen_whole_reference]
  rfl


/-- Entire actual OWN-completed dictionary, using both genuine independent bounds. -/
theorem completedLocalOpenMarked_eq_retained (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedLocalOpenMarked α U F hF = completedRetainedRestrictedMarked β α U F hF :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of (completedLocalOpenMarked_N_eq β α U F hF)
    (completedLocalOpenMarked_E_eq β α U F hF) (completedLocalOpenMarked_ideal_eq β α U F hF)
    (completedLocalOpenMarked_d_eq β α U F hF)



private theorem chosen_projection_injective (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Function.Injective (chosenProcedure β q A F hF).T.proj := by
  rw [← ChosenOutput.proj_eq]
  exact (chosenProcedure β q A F hF).back.injective

/-- Actual local retained prefix length, internally computed from the original centre word. -/
theorem chosen_open_length (α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.length =
      traceCount (Subtype.val : U → A) n q F := by
  rw [chosenProcedure_length_eq,procedureTower_length,(actual_trace_run (n := n) (Subtype.val : U → A) q F).2]
  rfl

/-- The OWN-completed local real length is exactly the global retained trace count. -/
theorem completed_chosen_open_length (α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.length =
      traceCount (Subtype.val : U → A) n (coefficientSum F) F := by
  rw [chosenProcedure_length_eq,procedureTower_length,(actual_completed_trace (n := n) (Subtype.val : U → A) F).1]
  rfl

/-- Genuine same original pulled ideal has its entire actual OWN-completed unit endpoint. -/
theorem completedLocalOpenMarked_unit (α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedLocalOpenMarked α U F hF).ideal =
      unitIdeal n (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D :=
  chosenProcedure_ideal_eq_unit α _ _

/-- The SAME actual OWN-completed chosen open tower genuinely resolves the original pulled full product. -/
theorem completed_chosen_open_resolution (α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution (monomialMarkedIdeal (n := n) ((pulledWeights (Subtype.val : U → A) F).map Prod.fst)
      (pulledWeights (Subtype.val : U → A) F))
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T :=
  chosenProcedure_isGeoResolution α _ _

/-- Genuine actual projection compatibility identifies the produced compressed endpoint map. -/
theorem chosenOpenCompression_unique (β α : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (g : openPreimage (chosenProcedure β q A F hF).T U →
      (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D)
    (hg : ∀ z, (restrict U (chosenProcedure β q A F hF).T).proj z =
      (chosenProcedure α (traceCount (Subtype.val : U → A) n q F) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.proj (g z)) :
    g = chosenOpenCompression β α q U F hF := by
  funext z
  apply chosen_projection_injective (A := CMfd.of (n := n) U) α (traceCount (Subtype.val : U → A) n q F)
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)
  exact (hg z).symm.trans (chosenOpenCompression_proj_comm β α q U F hF z)

/-- OWN completed true projection compatibility identifies the same actual completed endpoint. -/
theorem completedChosenOpenCompression_unique (β α : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (g : openPreimage (chosenProcedure β (coefficientSum F) A F hF).T U →
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).D)
    (hg : ∀ z, (restrict U (chosenProcedure β (coefficientSum F) A F hF).T).proj z =
      (chosenProcedure α (coefficientSum (pulledWeights (Subtype.val : U → A) F)) (CMfd.of (n := n) U)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).T.proj (g z)) :
    g = completedChosenOpenCompression β α U F hF := by
  funext z
  apply chosen_projection_injective (A := CMfd.of (n := n) U) α (coefficientSum (pulledWeights (Subtype.val : U → A) F))
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)
  exact (hg z).symm.trans (completedChosenOpenCompression_proj_comm β α U F hF z)

/-- The true internally generated global choice comparison restricts to its actual matching open endpoints. -/
def restrictedChoiceComparison (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    CMfd.of (n := n) (openPreimage (chosenProcedure β₁ q A F hF).T U)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (chosenProcedure β₂ q A F hF).T U) :=
  StepOneTangentChange.diffeoOpens (choiceComparison β₁ β₂ q F hF) _ _
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff (choiceComparison_isTowerIso β₁ β₂ q F hF)
      (fun _ => Iff.rfl))

/-- The actual restricted two-choice comparison is a genuine literal tower isomorphism. -/
theorem restrictedChoiceComparison_isTowerIso (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U (chosenProcedure β₁ q A F hF).T) (restrict U (chosenProcedure β₂ q A F hF).T)
      (restrictedChoiceComparison β₁ β₂ q U F hF) := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞
  have hb : ∀ x : A, x ∈ U ↔ Φ x ∈ U := fun _ => Iff.rfl
  have hi := choiceComparison_isTowerIso β₁ β₂ q F hF
  have he := StepOneTangentChange.isTowerIso_restrictOpens hb hi
    (StepOneTangentChange.isTowerIso_mem_openPreimage_iff hi hb)
  have hbase : StepOneTangentChange.diffeoOpens Φ U U hb =
      Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞ :=
    Diffeomorph.ext (fun _ => Subtype.ext rfl)
  rw [hbase] at he
  exact he

/-- Real independently chosen restricted projections commute with their genuine produced comparison. -/
theorem restrictedChoiceComparison_proj_comm (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ z, (restrict U (chosenProcedure β₁ q A F hF).T).proj z =
      (restrict U (chosenProcedure β₂ q A F hF).T).proj (restrictedChoiceComparison β₁ β₂ q U F hF z) :=
  (restrictedChoiceComparison_isTowerIso β₁ β₂ q U F hF).proj_comm

/-- Two primitive pairs of choices give the SAME actual bounded compression projection-square cocycle. -/
theorem chosenOpenCompression_choice_cocycle (β₁ β₂ α₁ α₂ : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenOpenCompression β₁ α₁ q U F hF).trans
      (choiceComparison (A := CMfd.of (n := n) U) α₁ α₂ (traceCount (Subtype.val : U → A) n q F)
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) =
    (restrictedChoiceComparison β₁ β₂ q U F hF).trans (chosenOpenCompression β₂ α₂ q U F hF) := by
  apply Diffeomorph.ext
  intro z
  apply chosen_projection_injective (A := CMfd.of (n := n) U) α₂ (traceCount (Subtype.val : U → A) n q F)
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)
  simp only [Diffeomorph.coe_trans,Function.comp_apply]
  rw [
    ← (choiceComparison_isTowerIso (A := CMfd.of (n := n) U) α₁ α₂ (traceCount (Subtype.val : U → A) n q F)
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).proj_comm,
    ← chosenOpenCompression_proj_comm β₁ α₁ q U F hF,
    ← chosenOpenCompression_proj_comm β₂ α₂ q U F hF,
    ← restrictedChoiceComparison_proj_comm β₁ β₂ q U F hF]
  rfl

/-- The genuine OWN-completed choice cocycle uses each side's actual independent bound. -/
theorem completedChosenOpenCompression_choice_cocycle (β₁ β₂ α₁ α₂ : CartierBlowupChoices.{u} n) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedChosenOpenCompression β₁ α₁ U F hF).trans
      (choiceComparison (A := CMfd.of (n := n) U) α₁ α₂ (coefficientSum (pulledWeights (Subtype.val : U → A) F))
        (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)) =
    (restrictedChoiceComparison β₁ β₂ (coefficientSum F) U F hF).trans
      (completedChosenOpenCompression β₂ α₂ U F hF) := by
  apply Diffeomorph.ext
  intro z
  apply chosen_projection_injective (A := CMfd.of (n := n) U) α₂ (coefficientSum (pulledWeights (Subtype.val : U → A) F))
    (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)
  simp only [Diffeomorph.coe_trans,Function.comp_apply]
  rw [
    ← (choiceComparison_isTowerIso (A := CMfd.of (n := n) U) α₁ α₂
      (coefficientSum (pulledWeights (Subtype.val : U → A) F))
      (pulledWeights (Subtype.val : U → A) F) (openWeights_isSNCDivisor U F hF)).proj_comm,
    ← completedChosenOpenCompression_proj_comm β₁ α₁ U F hF,
    ← completedChosenOpenCompression_proj_comm β₂ α₂ U F hF,
    ← restrictedChoiceComparison_proj_comm β₁ β₂ (coefficientSum F) U F hF]
  rfl

end ActualRestriction
end
end Hironaka.HironakaNormalCrossingsOrderedChoiceOpenCompression
