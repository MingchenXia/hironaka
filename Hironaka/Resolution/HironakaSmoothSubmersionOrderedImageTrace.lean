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
import Hironaka.Resolution.HironakaNormalCrossingsOrderedOpenTrace
import Hironaka.Resolution.HironakaSmoothSubmersionOrder
/-!
# Actual nonsurjective ordered marking-one image trace

Only original genuine submersion and original entire indexed SNC data are inputs.
Actual open range charts internally produce a genuine surjective image factor.
The independent source procedure has exactly the true nonempty original centre
traces, whole controlled prefix dictionaries and OWN finite unit completion.
All original entries and genuinely retained creation events remain literal.
General higher-invariant functoriality and prior separation identification remain open.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedImageTrace
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers HironakaSmoothSubmersionOrder HironakaNormalCrossingsOrderedOpenTrace
open HironakaSmoothSubmersionOrderedMonomialProcedure HironakaSmoothSubmersionNormalCrossings
open HironakaNormalCrossingsOrderedMonomialTail MarkedIdeals MarkedIdeals.MarkedIdeal
open BlowupTowerTransforms NormalCrossings HironakaNormalCrossingsFiniteMarkedCompletion
open HironakaSmoothSubmersionCoefficientIdeals HironakaDivisorResidual MonomialCase IdealWeightPowers
noncomputable section
variable {n m : ℕ} {A : CMfd.{u} n} {B : CMfd.{u} m}

/-- Actual local holomorphic sections prove that the genuine submersion is an open map. -/
theorem isOpenMap_of_isSubmersion {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    IsOpenMap f := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro a ⟨b,hb,rfl⟩
  obtain ⟨s,hsb,hsh,hsq⟩ := exists_holomorphic_localSection (hf.isSubmersionAt b)
  have hsc : ContinuousAt s (f b) := hsh.self_of_nhds.continuousAt
  have hsbW : s (f b) ∈ W := by rw [hsb]; exact hb
  have hsW : ∀ᶠ z in 𝓝 (f b), s z ∈ W := hsc.eventually (hW.mem_nhds hsbW)
  filter_upwards [hsW,hsq] with z hz he
  exact ⟨s z,hz,he⟩

/-- Genuine original geometry internally supplies its actual open range. -/
def imageOpen {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    TopologicalSpace.Opens A :=
  ⟨range f,by simpa only [image_univ] using (isOpenMap_of_isSubmersion hf) univ isOpen_univ⟩

def imageFactor {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) : B → imageOpen hf :=
  fun b => ⟨f b,⟨b,rfl⟩⟩

theorem imageFactor_projection {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (Subtype.val : imageOpen hf → A) ∘ imageFactor hf = f := rfl

theorem imageFactor_surjective {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    Function.Surjective (imageFactor hf) := by
  intro a
  obtain ⟨b,hb⟩ := a.property
  exact ⟨b,Subtype.ext hb⟩


private theorem subtypeChart_maximal (O : TopologicalSpace.Opens A) (hO : Nonempty O)
    (e : OpenPartialHomeomorph A (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A) :
    e.subtypeRestr hO ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ O := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · rw [OpenPartialHomeomorph.subtypeRestr_source,OpenPartialHomeomorph.subtypeRestr_coe]
    change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (e ∘ (Subtype.val : O → A)) ((Subtype.val : O → A) ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      contMDiff_subtype_val.contMDiffOn (fun _ hz => hz)
  · let c := e.subtypeRestr hO
    have hval : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        ((Subtype.val : O → A) ∘ c.symm) c.target :=
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono (e.subtypeRestr_target_subset hO)).congr
        (fun z hz => e.subtypeRestr_symm_apply hO hz)
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff O c.symm c.target z).mp (hval z hz)

/-- Actual restricted range charts retain the SAME genuine globally chosen submersion complement. -/
theorem imageFactor_isSubmersion {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (imageFactor hf) := by
  apply Manifold.IsSubmersionOfComplement.isSubmersion (F := hf.complement)
  intro b
  let h := hf.isSubmersionOfComplement_complement b
  let O := imageOpen hf
  have hO : Nonempty O := ⟨imageFactor hf b⟩
  let c := h.codChart.subtypeRestr hO
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv h.domChart c
  · exact h.mem_domChart_source
  · change imageFactor hf b ∈ (h.codChart.subtypeRestr hO).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact h.mem_codChart_source
  · exact h.domChart_mem_maximalAtlas
  · exact subtypeChart_maximal O hO h.codChart h.codChart_mem_maximalAtlas
  · intro w hw
    change imageFactor hf w ∈ (h.codChart.subtypeRestr hO).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact h.source_subset_preimage_source hw
  · intro w hw
    have he := h.writtenInCharts hw
    simpa [c,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps,imageFactor] using he

/-- Genuine produced submersion charts supply actual holomorphy of the literal image factor. -/
theorem imageFactor_holomorphic {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (imageFactor hf) :=
  (imageFactor_isSubmersion hf).contMDiff

/-- Entire original indices and powers agree under the actual range factor. -/
theorem imageFactor_weights {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) :
    pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F) =
      pulledWeights f F := by
  rw [← pulledWeights_comp,imageFactor_projection]

/-- Actual original SNC coordinates produce the whole literal image family. -/
theorem image_weights_isSNCDivisor {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSNCDivisor n ((pulledWeights (Subtype.val : imageOpen hf → A) F).map Prod.fst) :=
  openWeights_isSNCDivisor (imageOpen hf) F hF

/-- Genuine range witnesses identify exact nonemptiness, including empty source. -/
theorem image_preimage_nonempty {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) (C : Set A) :
    ((Subtype.val : imageOpen hf → A) ⁻¹' C).Nonempty ↔ (f ⁻¹' C).Nonempty := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := a.property
    refine ⟨b,?_⟩
    change f b ∈ C
    rw [hb]
    exact ha
  · rintro ⟨b,hb⟩
    exact ⟨imageFactor hf b,hb⟩

/-- Actual creation-centre traces through the produced range are literal f-traces. -/
theorem image_traceCentres {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) :
    (traceCentres (Subtype.val : imageOpen hf → A) n q F).map ((imageFactor hf) ⁻¹' ·) =
      traceCentres f n q F := by
  classical
  unfold traceCentres
  generalize centreTrace n q F = L
  induction L with
  | nil => rfl
  | cons C L ih =>
    by_cases hC : ((Subtype.val : imageOpen hf → A) ⁻¹' C).Nonempty
    · have hfC := (image_preimage_nonempty hf C).mp hC
      simp only [List.filterMap_cons,if_pos hC,if_pos hfC,List.map_cons]
      exact congrArg (List.cons (f ⁻¹' C)) ih
    · have hfC : ¬ (f ⁻¹' C).Nonempty := fun h => hC ((image_preimage_nonempty hf C).mpr h)
      simpa only [List.filterMap_cons,if_neg hC,if_neg hfC,Option.toList_none,
        List.nil_append] using ih

/-- Only original genuine submersion and original SNC produce the independent source centre word. -/
theorem actual_completed_image_centres {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    centreTrace m (coefficientSum (pulledWeights f F)) (pulledWeights f F) =
      traceCentres f n (coefficientSum F) F := by
  have h := (completed_history_pullback (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)).2.1
  rw [imageFactor_weights] at h
  rw [(actual_completed_trace (n := n) (Subtype.val : imageOpen hf → A) F).1] at h
  exact h.trans (image_traceCentres hf _ F)

/-- The produced range trace pulls its ENTIRE marked record, including actual creation history. -/
def imageTraceMarked {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) : MarkedIdeal m B :=
  markedPullback (m := m) (imageFactor hf) (traceStageMarked (imageOpen hf) q F hF)

/-- Every original prefix gives the independent source's true compressed ENTIRE controlled datum. -/
theorem actual_image_trace_whole_marked {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (procedureTower (traceCount (Subtype.val : imageOpen hf → A) n q F)
        (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)) =
      imageTraceMarked hf q F hF := by
  unfold imageTraceMarked
  rw [← actual_open_trace_whole_marked]
  have h := bounded_controlled_marked_pullback (A := CMfd.of (n := n) (imageOpen hf))
    (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (traceCount (Subtype.val : imageOpen hf → A) n q F)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)
  rw [markedPullback_indexed_dictionary (imageFactor_isSubmersion hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)] at h
  simpa only [imageFactor_weights] using h.symm

/-- Actual f-preimage nonemptiness internally identifies the compressed source prefix number. -/
theorem image_traceCount {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) :
    traceCount (Subtype.val : imageOpen hf → A) n q F = traceCount f n q F := by
  have h := congrArg List.length (image_traceCentres hf q F)
  simpa only [List.length_map,traceCount] using h

/-- Literal f-trace lengths specify every independent source prefix without a caller compression count. -/
theorem actual_source_prefix_whole_marked {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (procedureTower (traceCount f n q F) (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)) =
      imageTraceMarked hf q F hF := by
  rw [← image_traceCount hf q F]
  exact actual_image_trace_whole_marked hf q F hF

/-- OWN finite completion has the true image-filtered entire endpoint record. -/
theorem actual_completed_image_whole_marked {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (procedureTower (coefficientSum (pulledWeights f F))
        (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)) =
      imageTraceMarked hf (coefficientSum F) F hF := by
  unfold imageTraceMarked
  rw [← actual_completed_open_whole_marked]
  have h := completed_controlled_marked_pullback (A := CMfd.of (n := n) (imageOpen hf))
    (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)
  rw [markedPullback_indexed_dictionary (imageFactor_isSubmersion hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)] at h
  simpa only [imageFactor_weights] using h.symm

/-- The actual entire endpoint ideal is unit; empty metadata remains literal. -/
theorem actual_completed_image_unit {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageTraceMarked hf (coefficientSum F) F hF).ideal = unitIdeal m B := by
  rw [← actual_completed_image_whole_marked]
  exact procedureTower_ideal_eq_unit _ (pulledWeights_isSNCDivisor hf F hF)

/-- The true source completed tower length is exactly the internally calculated retained centre count. -/
theorem actual_completed_image_length {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (procedureTower (coefficientSum (pulledWeights f F))
      (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).length =
      traceCount f n (coefficientSum F) F := by
  rw [procedureTower_length,actual_completed_image_centres hf F hF]
  rfl

/-- Every genuinely retained creation event has the SAME original chronological label. -/
theorem image_newHistoryTrace {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) :
    newHistoryTrace (Subtype.val : imageOpen hf → A) n q F = newHistoryTrace f n q F := by
  classical
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none => simp only [newHistoryTrace,hs]
    | some j =>
      simp only [newHistoryTrace,hs,image_preimage_nonempty,ih]

/-- The actual ENTIRE carrier is the direct f-preimage of the original geometric carrier. -/
theorem imageTraceMarked_N {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageTraceMarked hf q F hF).N = f ⁻¹'
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).N := rfl

/-- Whole ordered boundary is precisely ALL original entries plus actual nonempty creation events. -/
theorem imageTraceMarked_E {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageTraceMarked hf q F hF).E = (List.range F.length ++ newHistoryTrace f n q F).map
      (fun k => f ⁻¹' (((geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (procedureTower q F hF)).E[k]?).getD ∅)) := by
  unfold imageTraceMarked traceStageMarked markedPullback
  dsimp only
  rw [List.map_map,image_newHistoryTrace]
  rfl

/-- Entire controlled ideal is the actual direct f-pullback, with no support-only substitution. -/
theorem imageTraceMarked_ideal {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageTraceMarked hf q F hF).ideal = GermIdeal.pullback (m := m) f
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (procedureTower q F hF)).ideal := by
  unfold imageTraceMarked traceStageMarked markedPullback
  dsimp only
  rw [procedureTower_marked_dictionary]
  change GermIdeal.pullback (m := m) (imageFactor hf)
      (GermIdeal.pullback (m := n) (Subtype.val : imageOpen hf → A)
        (componentPowerProduct (n := n) (terminalState n q F))) =
    GermIdeal.pullback (m := m) f (componentPowerProduct (n := n) (terminalState n q F))
  rw [open_pullback_componentPowerProduct (imageOpen hf) _ (terminalState_isSNCDivisor q F hF)]
  rw [pullback_componentPowerProduct (imageFactor_isSubmersion hf) _
    (openWeights_isSNCDivisor (imageOpen hf) _ (terminalState_isSNCDivisor q F hF))]
  rw [pullback_componentPowerProduct hf _ (terminalState_isSNCDivisor q F hF),imageFactor_weights]

/-- The actual marking remains the true original literal marking one. -/
theorem imageTraceMarked_d {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageTraceMarked hf q F hF).d = 1 := by
  unfold imageTraceMarked traceStageMarked markedPullback
  dsimp only
  rw [procedureTower_marked_dictionary]
  rfl

/-- Every bounded global prefix yields its actual independent source nonempty centre word. -/
theorem actual_source_prefix_centres {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    centreTrace m (traceCount f n q F) (pulledWeights f F) = traceCentres f n q F := by
  have h := (bounded_history_pullback (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (traceCount (Subtype.val : imageOpen hf → A) n q F)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)).2.1
  rw [imageFactor_weights] at h
  rw [(actual_trace_run (n := n) (Subtype.val : imageOpen hf → A) q F).2] at h
  rw [image_traceCount] at h
  exact h.trans (image_traceCentres hf q F)

/-- Genuine SNC and actual selected-factor controls make every traced prefix a true test tower. -/
theorem actual_source_prefix_isGeoTestTower {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoTestTower
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (procedureTower (traceCount f n q F) (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)) :=
  procedureTower_isGeoTestTower _ _ (pulledWeights_isSNCDivisor hf F hF)

/-- The actual identity-Cartier projections give the genuine dimensional projection square. -/
theorem actual_source_prefix_projection {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (q : ℕ) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    f ∘ (procedureTower (traceCount f n q F) (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).proj = (procedureTower q F hF).proj ∘ f := by
  rw [procedureTower_proj,procedureTower_proj]
  rfl

end
end Hironaka.HironakaSmoothSubmersionOrderedImageTrace
