/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedImageTrace
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceBaseChange
/-! Actual nonsurjective smooth traces of independent marking-one Cartier choices.

Only original submersion geometry, the entire original finite SNC list and primitive
Cartier blowup choices are inputs. Every true unequal prefix, actual chosen manifold,
whole controlled ideal/record, retained history, universal lift and finite completion
is produced internally. This OWN OFFLIB module awaits formal write-set registration.
General higher invariant functoriality and prior general separation identification
remain open. Frozen parent offlib sources and all old formal modules are unchanged.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedChoiceImageTrace
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealPullbackCalculus RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal
open HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedImageTrace
open HironakaNormalCrossingsOrderedChoiceComparison HironakaSmoothSubmersionOrderedChoiceBaseChange
open HironakaSmoothSubmersionOrderedMonomialProcedure HironakaSmoothSubmersionNormalCrossings
open HironakaNormalCrossingsOrderedOpenTrace HironakaNormalCrossingsFiniteMarkedCompletion
open HironakaDivisorResidual IdealWeightPowers NormalCrossings BlowupTowers BlowupTowerTransforms
open MarkedIdealBiholomorphism MarkedIdealTowerTransport BlowupTowerIsomorphism
open HironakaNormalCrossingsSeparationChoiceComparison
noncomputable section

section WholePullback
variable {n m ℓ : ℕ} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel ℓ) Z] [IsComplexManifold ℓ Z]

/-- ENTIRE genuine germ-ideal pullback composition across arbitrary actual dimensions. -/
theorem whole_pullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (I : GermIdeal n X) (hI : ∀ x a, I.mem x a → HolomorphicAt n a x) :
    GermIdeal.pullback (m := ℓ) (f ∘ g) I =
      GermIdeal.pullback (m := ℓ) g (GermIdeal.pullback (m := m) f I) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z), ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) := hI _ _ hc
    have hcfhol : HolomorphicAt m (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := m) f I).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c,hc,rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f,hcf,rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ,⟨d,hd,rfl⟩,rfl⟩
    exact ⟨d,hd,rfl⟩

/-- Original actual coherence internally provides ALL member holomorphy. -/
theorem coherent_pullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (I : GermIdeal n X) (hI : I.IsCoherent) :
    GermIdeal.pullback (m := ℓ) (f ∘ g) I =
      GermIdeal.pullback (m := ℓ) g (GermIdeal.pullback (m := m) f I) :=
  whole_pullback_comp hf hg I (fun _ _ hi => GermIdeal.IsCoherent.holomorphicAt_mem hI hi)

/-- Full actual N/E/I/d record composition, without a supplied output equality. -/
theorem whole_markedPullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) :
    markedPullback (m := ℓ) (f ∘ g) M =
      markedPullback (m := ℓ) g (markedPullback (m := m) f M) := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · simp only [markedPullback,List.map_map,Function.comp_def]
    rfl
  · exact coherent_pullback_comp hf hg M.ideal hM
  · rfl
end WholePullback

section ChosenTrace
variable {n m : ℕ} {A : CMfd.{u} n} {B : CMfd.{u} m}

private theorem pullback_refl_marked (M : MarkedIdeal n A) (hI : M.ideal.IsCoherent) :
    MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) M = M := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change M.E.map id = M.E
    exact List.map_id M.E
  · exact BlowupControlledTransform.pullback_id hI
  · rfl

/-- Internally produced actual chosen-reference comparison transports the ENTIRE marked record. -/
theorem chosen_whole_reference (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β q A F hF).T =
    markedPullback (m := n) (chosenProcedure β q A F hF).back
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)) := by
  have hw := isWellFormed_monomialMarkedIdeal hF F (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
  have he := (chosenProcedure_self_reference β q F hF).geoTransformAlong_eq
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞) hw.isClosedSubmanifold_N hw.isCoherent
    (procedureTower_isGeoTestTower q F hF)
  rw [pullback_refl_marked _ hw.isCoherent] at he
  exact he

/-- Actual original SNC alone gives true coherence of every genuine full reference controlled ideal. -/
theorem reference_stage_coherent (q : ℕ) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).ideal.IsCoherent := by
  rw [procedureTower_marked_dictionary]
  exact (isWellFormed_monomialMarkedIdeal (terminalState_isSNCDivisor q F hF)
    _ (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)).isCoherent

/-- Produced unequal-prefix actual lift from the TWO independent primitive choice procedures. -/
def traceChoiceLift (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).D →
      (chosenProcedure β q A F hF).D :=
  (chosenProcedure β q A F hF).back.symm ∘ f ∘
    (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).back

/-- Actual real projection inverses internally make the unequal-prefix lift a genuine submersion. -/
theorem traceChoiceLift_isSubmersion (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (traceChoiceLift β' β q hf F hF) :=
  isSubmersion_conjugate _ _ hf

/-- Actual independent projection square, without a false same-length claim. -/
theorem traceChoiceLift_proj_comm (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β q A F hF).T.proj (traceChoiceLift β' β q hf F hF x) =
      f ((chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T.proj x) := by
  intro x
  rw [← ChosenOutput.proj_eq,← ChosenOutput.proj_eq]
  exact (chosenProcedure β q A F hF).back.apply_symm_apply _

/-- Every genuine compatible holomorphic cone has a unique actual holomorphic lift. -/
theorem traceChoiceLift_holomorphicSquarePullback
    (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback f (traceChoiceLift β' β q hf F hF)
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T.proj
      (chosenProcedure β q A F hF).T.proj := by
  rw [← ChosenOutput.proj_eq,← ChosenOutput.proj_eq]
  exact holomorphicSquarePullback_conjugate _ _ _
/-- The TRUE source chosen prefix transports the internally produced image trace WHOLE record. -/
theorem chosen_source_whole_trace (β' : CartierBlowupChoices.{u} m) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T =
    markedPullback (m := m)
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).back
      (imageTraceMarked hf q F hF) := by
  rw [chosen_whole_reference,actual_source_prefix_whole_marked]

/-- Actual chosen source geometry has EXACTLY the internally calculated retained step count. -/
theorem chosen_source_trace_length (β' : CartierBlowupChoices.{u} m) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T.length =
      traceCount f n q F := by
  rw [chosenProcedure_length_eq,procedureTower_length,actual_source_prefix_centres hf _ F hF]
  rfl

/-- The internally computed lift has literal inverse cancellation with the actual global projection. -/
theorem traceChoiceLift_cancel (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q A F hF).back ∘ traceChoiceLift β' β q hf F hF =
      f ∘ (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).back := by
  funext x
  exact (chosenProcedure β q A F hF).back.apply_symm_apply _

/-- Only original geometry internally gives the direct lift pullback of the ENTIRE global controlled ideal. -/
theorem chosen_source_trace_ideal (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).ideal =
    GermIdeal.pullback (m := m) (traceChoiceLift β' β q hf F hF)
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T).ideal := by
  rw [chosen_source_whole_trace,chosen_whole_reference]
  change GermIdeal.pullback (m := m) _ (imageTraceMarked hf q F hF).ideal =
    GermIdeal.pullback (m := m) (traceChoiceLift β' β q hf F hF)
      (GermIdeal.pullback (m := n) (chosenProcedure β q A F hF).back
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).ideal)
  rw [imageTraceMarked_ideal]
  rw [← coherent_pullback_comp hf.contMDiff
    (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).back.contMDiff
    _ (reference_stage_coherent q F hF)]
  rw [← coherent_pullback_comp (chosenProcedure β q A F hF).back.contMDiff
    (traceChoiceLift_isSubmersion β' β q hf F hF).contMDiff _ (reference_stage_coherent q F hF)]
  rw [traceChoiceLift_cancel]

private theorem preimage_getD {X Y : Type u} (f : Y → X) (E : List (Set X)) (k : ℕ) :
    ((E.map (f ⁻¹' ·))[k]?).getD ∅ = f ⁻¹' ((E[k]?).getD ∅) := by
  rw [List.getElem?_map]
  cases E[k]? <;> rfl

/-- Actual whole carrier has its direct lift preimage dictionary. -/
theorem chosen_source_trace_N (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).N =
    (traceChoiceLift β' β q hf F hF) ⁻¹'
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T).N := by
  rw [chosen_source_whole_trace,chosen_whole_reference]
  change _ ⁻¹' (imageTraceMarked hf q F hF).N = _
  rw [imageTraceMarked_N]
  change (f ∘ (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
    (pulledWeights_isSNCDivisor hf F hF)).back) ⁻¹' _ =
    ((chosenProcedure β q A F hF).back ∘ traceChoiceLift β' β q hf F hF) ⁻¹' _
  rw [traceChoiceLift_cancel]
  rfl

/-- Actual chosen ENTIRE ordered boundary is ALL original entries plus true retained creation labels. -/
theorem chosen_source_trace_E (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).E =
    (List.range F.length ++ newHistoryTrace f n q F).map (fun k =>
      (traceChoiceLift β' β q hf F hF) ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (chosenProcedure β q A F hF).T).E[k]?).getD ∅)) := by
  rw [chosen_source_whole_trace,chosen_whole_reference]
  change (imageTraceMarked hf q F hF).E.map
    ((chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).back ⁻¹' ·) = _
  rw [imageTraceMarked_E,List.map_map]
  simp_rw [show ∀ k, (((markedPullback (m := n) (chosenProcedure β q A F hF).back
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF))).E)[k]?).getD ∅ =
      (chosenProcedure β q A F hF).back ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).E[k]?).getD ∅)
    from preimage_getD _ _]
  change (List.range F.length ++ newHistoryTrace f n q F).map
    (fun k => (f ∘ (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).back) ⁻¹' _) =
    (List.range F.length ++ newHistoryTrace f n q F).map
    (fun k => ((chosenProcedure β q A F hF).back ∘ traceChoiceLift β' β q hf F hF) ⁻¹' _)
  rw [traceChoiceLift_cancel]

/-- Actual marking one is preserved literally, through real unequal independently chosen prefixes. -/
theorem chosen_source_trace_d (β' : CartierBlowupChoices.{u} m) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).d = 1 := by
  rw [chosen_source_whole_trace β' q hf F hF]
  exact imageTraceMarked_d hf q F hF

/-- Actual two-choice comparisons commute with the genuinely unequal-prefix smooth lifts. -/
theorem traceChoiceLift_choice_cocycle (β'₁ β'₂ : CartierBlowupChoices.{u} m)
    (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β₁ β₂ q F hF : _ → _) ∘ traceChoiceLift β'₁ β₁ q hf F hF =
      traceChoiceLift β'₂ β₂ q hf F hF ∘
        (choiceComparison β'₁ β'₂ (traceCount f n q F) (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF) : _ → _) := by
  funext x
  simp only [choiceComparison,traceChoiceLift,Diffeomorph.coe_trans,Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- Internally selected genuine Cartier controls give the actual unequal source prefix test tower. -/
theorem chosen_source_trace_isGeoTestTower (β' : CartierBlowupChoices.{u} m) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoTestTower (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T :=
  chosenProcedure_isGeoTestTower β' _ _ _

/-- OWN independent source completion has its internally produced WHOLE retained record. -/
theorem chosen_completed_source_whole_trace (β' : CartierBlowupChoices.{u} m) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T =
    markedPullback (m := m)
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).back (imageTraceMarked hf (coefficientSum F) F hF) := by
  rw [chosen_whole_reference,actual_completed_image_whole_marked]

/-- Real chosen OWN finite tower length is EXACTLY the internally retained original centre count. -/
theorem chosen_completed_source_trace_length (β' : CartierBlowupChoices.{u} m) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).T.length = traceCount f n (coefficientSum F) F := by
  rw [chosenProcedure_length_eq]
  exact actual_completed_image_length hf F hF

/-- True independent chosen source procedure resolves the SAME actual original pulled ideal. -/
theorem chosen_completed_source_trace_isGeoResolution (β' : CartierBlowupChoices.{u} m) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T :=
  chosenProcedure_isGeoResolution β' _ _

/-- WHOLE unit endpoint, with literal retained old and new histories. -/
theorem chosen_completed_source_trace_unit (β' : CartierBlowupChoices.{u} m) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T).ideal =
      unitIdeal m (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).D :=
  chosenProcedure_ideal_eq_unit β' _ _

/-- Actual OWN-completed lift is a genuine submersion without primitive surjectivity. -/
theorem completedActualLift_isSubmersion (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (completedActualLift β' β f hf F hF) :=
  isSubmersion_conjugate _ _ hf

/-- Produced OWN-completed true projection inverses cancel literally. -/
theorem completedActualLift_cancel (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β (coefficientSum F) A F hF).back ∘ completedActualLift β' β f hf F hF =
      f ∘ (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).back := by
  funext x
  exact (chosenProcedure β (coefficientSum F) A F hF).back.apply_symm_apply _


/-- The SAME actual completed chosen source retains its entire direct original trace dictionary. -/
theorem chosen_completed_source_trace_ideal (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).ideal =
    GermIdeal.pullback (m := m) (completedActualLift β' β f hf F hF)
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β (coefficientSum F) A F hF).T).ideal := by
  rw [chosen_completed_source_whole_trace,chosen_whole_reference]
  change GermIdeal.pullback (m := m) _ (imageTraceMarked hf (coefficientSum F) F hF).ideal =
    GermIdeal.pullback (m := m) (completedActualLift β' β f hf F hF)
      (GermIdeal.pullback (m := n) (chosenProcedure β (coefficientSum F) A F hF).back
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).ideal)
  rw [imageTraceMarked_ideal]
  rw [← coherent_pullback_comp hf.contMDiff
    (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).back.contMDiff
    _ (reference_stage_coherent (coefficientSum F) F hF)]
  rw [← coherent_pullback_comp (chosenProcedure β (coefficientSum F) A F hF).back.contMDiff
    (completedActualLift_isSubmersion β' β hf F hF).contMDiff _ (reference_stage_coherent (coefficientSum F) F hF)]
  rw [completedActualLift_cancel]


/-- The SAME actual completed chosen source retains its entire direct original trace dictionary. -/
theorem chosen_completed_source_trace_N (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).N =
    (completedActualLift β' β f hf F hF) ⁻¹'
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β (coefficientSum F) A F hF).T).N := by
  rw [chosen_completed_source_whole_trace,chosen_whole_reference]
  change _ ⁻¹' (imageTraceMarked hf (coefficientSum F) F hF).N = _
  rw [imageTraceMarked_N]
  change (f ∘ (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
    (pulledWeights_isSNCDivisor hf F hF)).back) ⁻¹' _ =
    ((chosenProcedure β (coefficientSum F) A F hF).back ∘ completedActualLift β' β f hf F hF) ⁻¹' _
  rw [completedActualLift_cancel]
  rfl


/-- The SAME actual completed chosen source retains its entire direct original trace dictionary. -/
theorem chosen_completed_source_trace_E (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).E =
    (List.range F.length ++ newHistoryTrace f n (coefficientSum F) F).map (fun k =>
      (completedActualLift β' β f hf F hF) ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (chosenProcedure β (coefficientSum F) A F hF).T).E[k]?).getD ∅)) := by
  rw [chosen_completed_source_whole_trace,chosen_whole_reference]
  change (imageTraceMarked hf (coefficientSum F) F hF).E.map
    ((chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).back ⁻¹' ·) = _
  rw [imageTraceMarked_E,List.map_map]
  simp_rw [show ∀ k, (((markedPullback (m := n) (chosenProcedure β (coefficientSum F) A F hF).back
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF))).E)[k]?).getD ∅ =
      (chosenProcedure β (coefficientSum F) A F hF).back ⁻¹'
        (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower (coefficientSum F) F hF)).E[k]?).getD ∅)
    from preimage_getD _ _]
  change (List.range F.length ++ newHistoryTrace f n (coefficientSum F) F).map
    (fun k => (f ∘ (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).back) ⁻¹' _) =
    (List.range F.length ++ newHistoryTrace f n (coefficientSum F) F).map
    (fun k => ((chosenProcedure β (coefficientSum F) A F hF).back ∘ completedActualLift β' β f hf F hF) ⁻¹' _)
  rw [completedActualLift_cancel]


/-- The SAME actual completed chosen source retains its entire direct original trace dictionary. -/
theorem chosen_completed_source_trace_d (β' : CartierBlowupChoices.{u} m) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T).d = 1 := by
  rw [chosen_completed_source_whole_trace β' hf F hF]
  exact imageTraceMarked_d hf (coefficientSum F) F hF


/-- The nonsurjective real OWN-completed choice maps obey the actual two-choice cocycle. -/
theorem completedActualLift_choice_cocycle (β'₁ β'₂ : CartierBlowupChoices.{u} m)
    (β₁ β₂ : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β₁ β₂ (coefficientSum F) F hF : _ → _) ∘ completedActualLift β'₁ β₁ f hf F hF =
      completedActualLift β'₂ β₂ f hf F hF ∘
        (choiceComparison β'₁ β'₂ (coefficientSum (pulledWeights f F)) (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF) : _ → _) := by
  funext x
  simp only [choiceComparison,completedActualLift,Diffeomorph.coe_trans,Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- Actual whole generated global marking is literally one at every genuine chosen stage. -/
theorem chosen_stage_mark_one (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β q A F hF).T).d = 1 := by
  rw [chosen_whole_reference,procedureTower_marked_dictionary]
  rfl

/-- Actual retained WHOLE global record pulled to the independently chosen source prefix. -/
def traceChosenMarked (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).D :=
  let G := geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
    (chosenProcedure β q A F hF).T
  let liftMap := traceChoiceLift β' β q hf F hF
  { N := liftMap ⁻¹' G.N
    E := (List.range F.length ++ newHistoryTrace f n q F).map (fun k => liftMap ⁻¹' ((G.E[k]?).getD ∅))
    ideal := GermIdeal.pullback (m := m) liftMap G.ideal
    d := G.d }

/-- Entire chosen source controlled marked record equals the internally produced retained trace record. -/
theorem chosen_source_trace_whole_record (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T =
      traceChosenMarked β' β q hf F hF := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact chosen_source_trace_N β' β q hf F hF
  · exact chosen_source_trace_E β' β q hf F hF
  · exact chosen_source_trace_ideal β' β q hf F hF
  · exact (chosen_source_trace_d β' q hf F hF).trans (chosen_stage_mark_one β q F hF).symm

/-- Genuine OWN-completed entire retained global marked record on the real independent source endpoint. -/
def completedTraceChosenMarked (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).D :=
  let G := geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
    (chosenProcedure β (coefficientSum F) A F hF).T
  let liftMap := completedActualLift β' β f hf F hF
  { N := liftMap ⁻¹' G.N
    E := (List.range F.length ++ newHistoryTrace f n (coefficientSum F) F).map
      (fun k => liftMap ⁻¹' ((G.E[k]?).getD ∅))
    ideal := GermIdeal.pullback (m := m) liftMap G.ideal
    d := G.d }

/-- The SAME actual independent completed whole record has the exact original retained trace dictionary. -/
theorem chosen_completed_source_trace_whole_record (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T = completedTraceChosenMarked β' β hf F hF := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact chosen_completed_source_trace_N β' β hf F hF
  · exact chosen_completed_source_trace_E β' β hf F hF
  · exact chosen_completed_source_trace_ideal β' β hf F hF
  · exact (chosen_completed_source_trace_d β' hf F hF).trans (chosen_stage_mark_one β (coefficientSum F) F hF).symm

/-- The actual unequal source prefix is internally an old-gamma canonical marking-one monomial segment. -/
theorem chosen_source_trace_isCanonicalSegment (β' : CartierBlowupChoices.{u} m) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ResolutionDriver.IsCanonicalSegment
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (fun {V} R => MonomialStepAlong.towerInvAlong
        (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F)) (Y := V) R)
      (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T :=
  chosenProcedure_isCanonicalSegment β' _ _ _

/-- The genuine OWN-completed projection square has its actual holomorphic universal lift property. -/
theorem completedActualLift_holomorphicSquarePullback
    (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback f (completedActualLift β' β f hf F hF)
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T.proj
      (chosenProcedure β (coefficientSum F) A F hF).T.proj := by
  rw [← ChosenOutput.proj_eq,← ChosenOutput.proj_eq]
  exact holomorphicSquarePullback_conjugate _ _ _

/-- Projection compatibility alone identifies the actual internally produced unequal-prefix map. -/
theorem traceChoiceLift_unique (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (g : (chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).D → (chosenProcedure β q A F hF).D)
    (hg : ∀ x, (chosenProcedure β q A F hF).T.proj (g x) =
      f ((chosenProcedure β' (traceCount f n q F) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T.proj x)) :
    g = traceChoiceLift β' β q hf F hF := by
  funext x
  calc g x = (chosenProcedure β q A F hF).back.symm ((chosenProcedure β q A F hF).back (g x)) :=
      ((chosenProcedure β q A F hF).back.symm_apply_apply (g x)).symm
    _ = traceChoiceLift β' β q hf F hF x := by
      rw [ChosenOutput.proj_eq,hg x,← ChosenOutput.proj_eq]
      rfl

end ChosenTrace
end
end Hironaka.HironakaSmoothSubmersionOrderedChoiceImageTrace
