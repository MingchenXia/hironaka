import Hironaka.Resolution.HironakaActualInheritedDiagramJetPivot
import Hironaka.Resolution.HironakaActualAnalyticNearbyVertexGenerators
import Hironaka.Resolution.HironakaActualHSConstantCentreJetFrames

/-! Original coherent whole HS equality forces all low derivatives of the
SAME current inherited family to vanish on the actual centre. The source
diagram is only a historical set of jet rows. No nearby diagram equality,
rank/minor certificate, normal power or desired order is an input. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualInheritedHSContactContainment
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainSaturation
  HironakaActualAnalyticNearbyVertexGenerators HironakaActualInheritedDiagramJetPivot
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetQuotientFrames
  HironakaHolomorphicJetChartInvariance HironakaActualHSConstantCentreJetFrames
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedNestedContactFlag HironakaActualRelativeNormalJetDivision
  HironakaActualAnalyticFormalNormalPowers HolomorphicTaylorTail

variable {n : ℕ}

private theorem chartTranslatedGerm_model_point (p : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolomorphicAt n f p) :
    chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) f hf =
      translatedGerm p f (hf.mono fun _ hz => hz.differentiableAt) := by
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [chartAt_self_eq]

private theorem whole_stalk_eq_translated_of_oka_span
    (A : GermIdeal n (ComplexModel n)) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hH : ∀ i, HolAt (H i) p)
    (hgen : ∀ f, A.mem p f ↔ InSpanAt H p f) :
    wholeChartStalkIdeal A p p (mem_chart_source (ComplexModel n) p) =
      translatedIdeal H p hH := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hAf, rfl⟩
    obtain ⟨hfh, c, hc, he⟩ := (hgen f).mp hAf
    have ht : Tendsto (fun z : ComplexModel n => z+p) (𝓝 0) (𝓝 p) := by
      have hcont : ContinuousAt (fun z : ComplexModel n => z+p) (0 : ComplexModel n) :=
        continuousAt_id.add continuousAt_const
      simpa only [zero_add] using hcont.tendsto
    have hmem : translatedGerm p f hfh ∈ translatedIdeal H p hH := by
      apply (inSpanAt_zero_iff_mem_origin_span
        (fun i z => H i (z+p)) (fun i => translated_holomorphic p (hH i))
        (translated_holomorphic p hfh)).mp
      refine ⟨translated_holomorphic p hfh, fun i z => c i (z+p),
        fun i => translated_holomorphic p (hc i), ?_⟩
      exact ht.eventually he
    rw [chartTranslatedGerm_model_point]
    exact hmem
  · apply Ideal.span_le.mpr
    rintro g ⟨i, rfl⟩
    apply Ideal.subset_span
    refine ⟨H i, (hH i).mono (fun _ hz => hz.mdifferentiableAt),
      (hgen _).mpr (inSpanAt_self hH i), ?_⟩
    simp only [chartTranslatedGerm, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]

set_option linter.unusedVariables false in
/-- Original coherence and actual origin generation internally produce
SAME functions on one real generation domain and the whole original HS
dictionary there. This does not reselect the family or a flattening. -/
theorem exists_actual_same_origin_generators_hs_dictionary
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    {ι : Type} [Fintype ι] (G : ι → HolGerm (ComplexModel n))
    (hspan : Ideal.span (range G) = originalCoherentOriginIdeal A) :
    ∃ (H : ι → ComplexModel n → ℂ) (hg : ∀ a, HolAt (H a) 0),
      (∀ a, HolGerm.mk (H a) (hg a) = G a) ∧
      ∃ (U : Set (ComplexModel n)), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        (∀ a, DifferentiableOn ℂ (H a) U) ∧
        (∀ p ∈ U, ∀ f, A.mem p f ↔ InSpanAt H p f) ∧
        ∃ hhol : ∀ p ∈ U, ∀ a, HolAt (H a) p,
          (∀ p (hp : p ∈ U) (ℓ : ℕ), hilbertSamuelAt A p ℓ =
            hilbertSamuelValue (translatedIdeal H p (hhol p hp)) ℓ) ∧
          ∀ p (hp : p ∈ U) (ℓ : ℕ), hilbertSamuelAt A p ℓ =
            Module.finrank ℂ (LinearMap.range (finiteJet (n := n) (ℓ+1))) -
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p)) := by
  have hfg : IdealFGAt A.mem (0 : ComplexModel n) :=
    idealFGAt_of_coherentOn A univ (coherentOn_of_isCoherent A hA univ isOpen_univ) (mem_univ _)
  obtain ⟨H, hg, hG, U, hU, h0U, hH, hgen⟩ :=
    exists_actual_nearby_representatives_of_origin_span A hfg G hspan
  have hhol : ∀ p ∈ U, ∀ a, HolAt (H a) p := by
    intro p hp a
    filter_upwards [hU.mem_nhds hp] with z hz
    exact (hH a z hz).differentiableAt (hU.mem_nhds hz)
  have hdict (p : ComplexModel n) (hp : p ∈ U) (ℓ : ℕ) :
      hilbertSamuelAt A p ℓ = hilbertSamuelValue (translatedIdeal H p (hhol p hp)) ℓ := by
    change hilbertSamuelValue
      (wholeChartStalkIdeal A p p (mem_chart_source (ComplexModel n) p)) ℓ = _
    rw [whole_stalk_eq_translated_of_oka_span A H p (hhol p hp) (hgen p hp)]
  refine ⟨H, hg, hG, U, hU, h0U, hH, hgen, hhol, hdict, ?_⟩
  intro p hp ℓ
  exact (hdict p hp ℓ).trans
    (hilbertSamuelValue_translatedIdeal_eq_original_matrix_rank ℓ H p (hhol p hp))

variable {K : Ideal (MvPowerSeries (Fin n) ℂ)}

private theorem degree_mono {α β : Fin n →₀ ℕ} (h : α ≤ β) :
    normalExponentDegree α ≤ normalExponentDegree β := by
  exact Finset.sum_le_sum fun i _ => h i

/-- WHOLE proper-prefix support makes each lower source-diagram
derivative literally zero in the entire analytic germ ring. -/
theorem actual_inherited_diagram_derivative_eq_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (a : actualInitialVertices MonomialOrder.degLex K) (α : Fin n →₀ ℕ)
    (hαD : α ∈ actualInitialDiagram MonomialOrder.degLex K)
    (hα : normalExponentDegree α < normalExponentDegree a.val) :
    actualAnalyticMultiDerivative α (G.germs a) = 0 := by
  obtain ⟨c, hc, hcα⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hαD
  let b : actualInitialVertices MonomialOrder.degLex K := ⟨c, hc⟩
  have hb : normalExponentDegree b.val < normalExponentDegree a.val :=
    (degree_mono hcα).trans_lt hα
  apply (actualAnalyticMultiDerivative_eq_zero_iff_cone α (G.germs a)).mpr
  intro β hαβ
  exact hred (normalExponentDegree a.val-1) a (by omega) b (by omega) β (hcα.trans hαβ)

private theorem inherited_diagram_word_derivative_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (a : actualInitialVertices MonomialOrder.degLex K)
    (w : monomialIndex n (normalExponentDegree a.val))
    (hw : actualJetWordExponent w ∈ actualInitialDiagram MonomialOrder.degLex K) :
    actualAnalyticWordDerivative (List.ofFn w.2) (G.germs a) = 0 := by
  have hzero := actual_inherited_diagram_derivative_eq_zero G hred a
    (actualJetWordExponent w) hw
    (by rw [actualJetWordExponent_degree]; exact w.1.isLt)
  dsimp only [actualJetWordExponent] at hzero
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [actualTaylor_actualAnalyticWordDerivative,
    ← actualTaylor_actualAnalyticMultiDerivative, hzero, map_zero]

/-- The CURRENT original ideal determines the family label type. It is
not an arbitrary ideal with equal-looking vertices. -/
abbrev actualInheritedOriginFormalIdeal (A : GermIdeal n (ComplexModel n)) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (originalCoherentOriginIdeal A)

/-- Actual original HS equality at the finitely many member marks
internally gives the SAME member orders on ONE common real open.
Every rank, source-diagram pivot and whole nearby-stalk dictionary is
produced internally. No nearby diagram equality is asserted. -/
theorem exists_actual_inherited_hs_locus_member_orders
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k) :
    ∃ (H : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A) →
          ComplexModel n → ℂ) (hg : ∀ a, HolAt (H a) 0),
      (∀ a, HolGerm.mk (H a) (hg a) = G.germs a) ∧
      ∃ V : Set (ComplexModel n), IsOpen V ∧ (0 : ComplexModel n) ∈ V ∧
        (∀ a, DifferentiableOn ℂ (H a) V) ∧
        (∀ p ∈ V, ∀ f, A.mem p f ↔ InSpanAt H p f) ∧
        ∃ hhol : ∀ p ∈ V, ∀ a, HolAt (H a) p,
          ∀ p (hp : p ∈ V),
            (∀ a : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A),
              0 < normalExponentDegree a.val →
              hilbertSamuelAt A p (normalExponentDegree a.val-1) =
                hilbertSamuelAt A 0 (normalExponentDegree a.val-1)) →
            ∀ a, translatedGerm p (H a) (hhol p hp a) ∈
              IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val := by
  obtain ⟨H, hg, hG, U, hU, h0U, hH, hgen, hhol, hdict, _hRanks⟩ :=
    exists_actual_same_origin_generators_hs_dictionary A hA G.germs hspan
  have hspanH : Ideal.span (range fun a => HolGerm.mk (H a) (hhol 0 h0U a)) =
      originalCoherentOriginIdeal A := by
    have he : (fun a => HolGerm.mk (H a) (hhol 0 h0U a)) = G.germs :=
      funext fun a => hG a
    rw [he]
    exact hspan
  choose r rows cols hrows hrank hdet using
    fun a : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A) =>
    exists_actual_source_diagram_jet_pivot (originalCoherentOriginIdeal A)
      (normalExponentDegree a.val) H (hhol 0 h0U) hspanH
  have hpiv : ∀ᶠ p in 𝓝 (0 : ComplexModel n), ∀ a,
      (pivotMatrix (normalExponentDegree a.val) H (rows a) (cols a) p).det ≠ 0 := by
    apply eventually_all.mpr
    intro a
    have hcont := ((differentiableOn_originalMacaulayMinor
      (normalExponentDegree a.val) H hU hH (rows a) (cols a)).differentiableAt
        (hU.mem_nhds h0U)).continuousAt
    exact hcont.eventually_ne (hdet a)
  have hzero (a : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A))
      (i : Fin (r a)) :
      ∀ᶠ p in 𝓝 (0 : ComplexModel n),
        iterDeriv ((List.ofFn (rows a i).2).map
          (fun j => EuclideanSpace.single j (1 : ℂ))) (H a) p = 0 := by
    have hz := inherited_diagram_word_derivative_zero G hred a (rows a i) (hrows a i)
    rw [← hG a, actualAnalyticWordDerivative, iteratedDerivativeGerm_mk] at hz
    rw [← HolGerm.mk_zero] at hz
    exact HolGerm.mk_eq_mk_iff.mp hz
  have hzeros : ∀ᶠ p in 𝓝 (0 : ComplexModel n), ∀ a, ∀ i : Fin (r a),
      iterDeriv ((List.ofFn (rows a i).2).map
        (fun j => EuclideanSpace.single j (1 : ℂ))) (H a) p = 0 :=
    eventually_all.mpr fun a => eventually_all.mpr (hzero a)
  have hnearU : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ U := hU.mem_nhds h0U
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.mp (hnearU.and (hpiv.and hzeros))
  have hsub : V ⊆ U := fun _ hp => (hVU hp).1
  let hholV : ∀ p ∈ V, ∀ a, HolAt (H a) p := fun p hp => hhol p (hsub hp)
  refine ⟨H, hg, hG, V, hV, h0V, fun a => (hH a).mono hsub,
    fun p hp => hgen p (hsub hp), hholV, ?_⟩
  intro p hp hHS a
  by_cases hμ : 0 < normalExponentDegree a.val
  · have hq : normalExponentDegree a.val-1+1 = normalExponentDegree a.val := by omega
    have hTranslatedHS :
        hilbertSamuelValue (translatedIdeal H p (hhol p (hsub hp)))
            (normalExponentDegree a.val-1) =
          hilbertSamuelValue (translatedIdeal H 0 (hhol 0 h0U))
            (normalExponentDegree a.val-1) :=
      (hdict p (hsub hp) _).symm.trans ((hHS a hμ).trans (hdict 0 h0U _))
    have hRankP := originalMacaulay_rank_eq_of_translated_hs_eq
      (normalExponentDegree a.val-1) H p 0 (hhol p (hsub hp)) (hhol 0 h0U) hTranslatedHS
    rw [hq] at hRankP
    have hRank : Module.finrank ℂ (LinearMap.range
        (originalMacaulayLinearMap (normalExponentDegree a.val) H p)) = r a :=
      hRankP.trans (hrank a)
    let v := scalarJet (normalExponentDegree a.val)
      (translatedGerm p (H a) (hhol p (hsub hp) a))
    have hv : v ∈ LinearMap.range (originalMacaulayLinearMap (normalExponentDegree a.val) H p) := by
      rw [range_originalMacaulay_eq_whole_scalar_image _ H p (hhol p (hsub hp))]
      exact ⟨translatedGerm p (H a) (hhol p (hsub hp) a),
        Ideal.mem_span_range_self (x := a), rfl⟩
    have hrowzero : rowMap (normalExponentDegree a.val) (rows a) v = 0 := by
      funext i
      change scalarJet (normalExponentDegree a.val)
        (translatedGerm p (H a) (hhol p (hsub hp) a)) (rows a i) = 0
      rw [scalarJet_translatedGerm_eq_iterDeriv]
      exact (hVU hp).2.2 a i
    have hvzero : v = 0 := by
      have hker := ker_pivotProjection_eq_entire_image (normalExponentDegree a.val)
        H (rows a) (cols a) p ((hVU hp).2.1 a) hRank
      have hzeroP : pivotProjection (normalExponentDegree a.val) H (rows a) (cols a) p v = 0 := by
        apply LinearMap.mem_ker.mp
        rwa [hker]
      rwa [pivotProjection_eq_self _ H (rows a) (cols a) p v hrowzero] at hzeroP
    change translatedGerm p (H a) (hhol p (hsub hp) a) ∈
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val).restrictScalars ℂ
    rw [← ker_scalarJet (n := n) (normalExponentDegree a.val)]
    exact LinearMap.mem_ker.mpr hvzero
  · have hz : normalExponentDegree a.val = 0 := by omega
    simp only [hz, pow_zero, Ideal.one_eq_top, Submodule.mem_top]

/-- Raw original coherent HS constancy on ANY actual set forces EVERY
low derivative of the SAME CURRENT inherited member into its genuine
vanishing ideal. C need not be smooth. The family label ideal is exactly
the formal extension of the actual original origin ideal. -/
theorem actual_inherited_low_derivatives_mem_hs_centre
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (C : Set (ComplexModel n))
    (hHS : ∀ p ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ)
    (a : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A))
    (γ : Fin n →₀ ℕ) (hγ : normalExponentDegree γ < normalExponentDegree a.val) :
    actualAnalyticMultiDerivative γ (G.germs a) ∈
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) := by
  obtain ⟨H, hg, hG, V, hV, h0V, _hH, _hgen, hhol, horders⟩ :=
    exists_actual_inherited_hs_locus_member_orders A hA G hspan hred
  obtain ⟨w, hw⟩ := exists_actualJetWordExponent (normalExponentDegree a.val) γ hγ
  let L := (List.ofFn w.2).map (fun i => EuclideanSpace.single i (1 : ℂ))
  let f := iterDeriv L (H a)
  have hf : HolAt f 0 := eventually_holomorphic_iterDeriv (hg a) L
  have hword : actualAnalyticMultiDerivative γ (G.germs a) =
      actualAnalyticWordDerivative (List.ofFn w.2) (G.germs a) := by
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [actualTaylor_actualAnalyticMultiDerivative, actualTaylor_actualAnalyticWordDerivative,
      show actualCoordinateWordExponent (List.ofFn w.2) = γ from hw]
  have hrep : actualAnalyticMultiDerivative γ (G.germs a) = HolGerm.mk f hf := by
    rw [hword, ← hG a, actualAnalyticWordDerivative, iteratedDerivativeGerm_mk]
  rw [hrep]
  apply Ideal.subset_span
  refine ⟨f, hf, ⟨hf.mono (fun _ hz => hz.mdifferentiableAt), ?_⟩, rfl⟩
  filter_upwards [hV.mem_nhds h0V] with p hp hCp
  have hm := horders p hp (fun _ _ => hHS p hCp _) a
  have hj : scalarJet (normalExponentDegree a.val)
      (translatedGerm p (H a) (hhol p hp a)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_scalarJet]
    exact hm
  have hentry := congrFun hj w
  rw [scalarJet_translatedGerm_eq_iterDeriv] at hentry
  exact hentry

end
end Hironaka.HironakaActualInheritedHSContactContainment
