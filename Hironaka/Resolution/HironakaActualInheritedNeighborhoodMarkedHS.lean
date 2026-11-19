import Hironaka.Resolution.HironakaActualInheritedNeighborhoodStandardJets
import Hironaka.Resolution.HironakaActualInheritedLocalHSContact
import Hironaka.Resolution.HironakaActualDiagonalTaylor
import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Resolution.HironakaActualFiniteCoefficientIdeals
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

/-! ONE real neighborhood identifies the SAME finite principal marked
presentation with the WHOLE original Hilbert--Samuel stratum. Actual local
finite generation supplies the original stalk dictionaries. A finite genuine
representative equality and the actual reciprocal diagonal map remove the
Cauchy scaling at every point; no nearby initial diagram is assumed constant.
SOURCE ONLY, not checked or accepted. Complete mathematics precedes this
source in work/hironaka-inherited-neighborhood-marked-hs-20261023/. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualInheritedNeighborhoodMarkedHS
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  InvertibleIdealQuotient RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers OrderTaylor MarkedIdeals
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalCoherentSaturation
  HironakaSmoothCentreCoherentDomain HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedNestedContactFlag HironakaActualInheritedHSContactContainment
  HironakaActualInheritedLocalHSContact HironakaActualInheritedSmallTails
  HironakaActualWeightedVertexSmallTails
  HironakaActualOriginalScaledAnalyticDivision HironakaActualFiniteDegLexWeights
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyNeumannDivision
  HironakaActualCauchyTaylorSupport HironakaActualInheritedSourceCauchyRemainder
  HironakaActualInheritedUniformTranslatedTails HironakaActualInheritedNeighborhoodStandardJets
  HironakaActualDiagonalTaylor HironakaActualPointGeometricBennett
  HironakaSharpOriginalProductTraceOrder HironakaActualFiniteCoefficientIdeals
  MarkedIdealBiholomorphism

variable {n : ℕ}

/-- The native whole principal ideal, with exactly the indicated generator. -/
def actualInheritedPrincipalIdeal (f : ComplexModel n → ℂ) :
    GermIdeal n (ComplexModel n) :=
  actualPrincipalCoefficientIdeal n f

/-- The actual original empty-boundary marked principal ideal. Mark zero is
retained, including a unit source's zero vertex. -/
def actualInheritedPrincipalMarked (f : ComplexModel n → ℂ) (q : ℕ) :
    MarkedIdeal n (ComplexModel n) :=
  ⟨univ, [], actualInheritedPrincipalIdeal f, q⟩

/-- Finite intersection of the native marked cosupports, with literal labels. -/
def actualInheritedMarkedCosupport {ι : Type*} (H : ι → ComplexModel n → ℂ)
    (μ : ι → ℕ) : Set (ComplexModel n) :=
  ⋂ a, (actualInheritedPrincipalMarked (H a) (μ a)).cosupp

/-- True marked restriction to the actual open submanifold, not a global
extension of the representative's holomorphic domain. -/
def actualInheritedOpenPrincipalMarked (U : TopologicalSpace.Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (q : ℕ) : MarkedIdeal n U :=
  MarkedIdeal.pullback (Subtype.val : U → ComplexModel n)
    (actualInheritedPrincipalMarked f q)

private theorem principal_coherentOn (f : ComplexModel n → ℂ)
    (U : Set (ComplexModel n)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : CoherentOn (actualInheritedPrincipalIdeal f) U :=
  coherentOn_actualPrincipalCoefficientIdeal n f U hU
    (mdifferentiableOn_iff_differentiableOn.mpr hf)

private theorem open_principal_membership
    (U : TopologicalSpace.Opens (ComplexModel n)) (f : ComplexModel n → ℂ)
    (p : U) (hf : HolomorphicAt n f (p : ComplexModel n)) (g : U → ℂ) :
    (GermIdeal.pullback (m := n) (Subtype.val : U → ComplexModel n)
      (actualInheritedPrincipalIdeal f)).mem p g ↔
      IsInSpanAt (n := n) (· = f ∘ Subtype.val) p g := by
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨b,hb,rfl⟩
    obtain ⟨hbhol,c,hc,he⟩ := isInSpanAt_eq_iff.mp hb
    apply isInSpanAt_eq_iff.mpr
    refine ⟨(Hironaka.HolomorphicIdealSheaves.holomorphicAt_comp_val_iff U).mpr hbhol,
      c ∘ Subtype.val,(Hironaka.HolomorphicIdealSheaves.holomorphicAt_comp_val_iff U).mpr hc,?_⟩
    exact continuous_subtype_val.continuousAt.tendsto.eventually he
  · intro hg
    apply RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    refine IsInSpanAt.trans ?_ hg
    rintro s rfl
    have hfm : (actualInheritedPrincipalIdeal f).mem (p : ComplexModel n) f :=
      isInSpanAt_eq_iff.mpr ⟨hf,1,holomorphicAt_const 1,
        Eventually.of_forall fun z => (one_mul (f z)).symm⟩
    exact isInSpanAt_self (S := fun s => ∃ b,
      (actualInheritedPrincipalIdeal f).mem (p : ComplexModel n) b ∧ s = b ∘ Subtype.val)
      ⟨f,hfm,rfl⟩ ((Hironaka.HolomorphicIdealSheaves.holomorphicAt_comp_val_iff U).mpr hf)

private theorem open_principal_isCoherent
    (U : TopologicalSpace.Opens (ComplexModel n)) (f : ComplexModel n → ℂ)
    (hf : DifferentiableOn ℂ f U) (q : ℕ) :
    (actualInheritedOpenPrincipalMarked U f q).ideal.IsCoherent := by
  have hfd := mdifferentiableOn_iff_differentiableOn.mpr hf
  have hhol (p : U) : HolomorphicAt n f (p : ComplexModel n) :=
    holomorphicAt_of_mdifferentiableOn U.isOpen hfd p.property
  have hcomp : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (f ∘ (Subtype.val : U → ComplexModel n)) := by
    intro p
    exact (hfd.mdifferentiableAt (U.isOpen.mem_nhds p.property)).comp p
      ((contMDiff_subtype_val (I := 𝓘(ℂ,ComplexModel n)) (n := ∞) p).mdifferentiableAt
        (by simp))
  intro p
  refine ⟨univ,isOpen_univ,mem_univ p,1,fun _ => f ∘ Subtype.val,
    fun _ => hcomp.mdifferentiableOn,?_⟩
  intro y _ g
  have he := open_principal_membership U f y (hhol y) g
  change (GermIdeal.pullback (m := n) (Subtype.val : U → ComplexModel n)
    (actualInheritedPrincipalIdeal f)).mem y g ↔ _
  simpa only [range_const,mem_singleton_iff] using he

private theorem translated_power_iff_point_power (p : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolAt f p) (q : ℕ) :
    translatedGerm p f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      (idealPow (pointIdeal n p) q).mem p f := by
  change HolGerm.mk (fun z => f (z+p)) (translated_holomorphic p hf) ∈
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔ _
  rw [mem_maximalIdeal_pow_iff_iteratedFDeriv (translated_holomorphic p hf) q,
    OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv
      (hf.mono fun _ hz => hz.mdifferentiableAt) q]
  simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, Function.comp_def, id_eq,
    iteratedFDeriv_comp_add_right, zero_add]

/-- Native principal marked cosupport is exactly the SAME original member's
whole recentered maximal-ideal power, at every real holomorphic point. -/
theorem mem_actualInheritedPrincipalMarked_cosupp_iff
    (f : ComplexModel n → ℂ) (p : ComplexModel n) (hf : HolAt f p) (q : ℕ) :
    p ∈ (actualInheritedPrincipalMarked f q).cosupp ↔
      translatedGerm p f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  change p ∈ cosupport n univ (actualInheritedPrincipalIdeal f) q ↔ _
  have hgen : ∀ g, (actualInheritedPrincipalIdeal f).mem p g ↔
      IsInSpanAt (n := n) (· = f) p g := by
    intro g
    rfl
  have hfh : HolomorphicAt n f p := hf.mono fun _ hz => hz.mdifferentiableAt
  have hprincipal : p ∈ cosupport n univ (actualInheritedPrincipalIdeal f) q ↔
      VanishesToOrderOn n univ p q f :=
    cosupport_principal_iff_vanishes (n := n)
      (X := BlowupTowers.CMfd.of (ComplexModel n)) (W := univ)
      (I := actualInheritedPrincipalIdeal f) (f := f) (x := p)
      (mem_univ p) hfh hgen q
  rw [hprincipal,translated_power_iff_point_power]
  exact ⟨mem_idealPow_of_vanishesToOrderOn_univ,
    fun h => ⟨f,h,Eventually.of_forall fun _ _ => rfl⟩⟩

private def diagonalAlgEquiv (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) := by
  apply AlgEquiv.ofAlgHom (actualDiagonalPullback c)
    (actualDiagonalPullback (fun i => (c i)⁻¹))
  · apply AlgHom.ext
    intro F
    change actualDiagonalPullback c
      (actualDiagonalPullback (fun i => (c i)⁻¹) F) = F
    have h := actualDiagonalPullback_inverse (fun i => (c i)⁻¹)
      (fun i => inv_ne_zero (hc i)) F
    simpa only [inv_inv] using h
  · apply AlgHom.ext
    intro F
    exact actualDiagonalPullback_inverse c hc F

private theorem diagonalMap_inverse (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (y : ComplexModel n) :
    actualDiagonalMap c (actualDiagonalMap (fun i => (c i)⁻¹) y) = y := by
  ext i
  rw [actualDiagonalMap_apply,actualDiagonalMap_apply,← mul_assoc,
    mul_inv_cancel₀ (hc i),one_mul]

private theorem algEquiv_map_maximal_power
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (q : ℕ) :
    Ideal.map E.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) =
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  rw [Ideal.map_pow]
  exact congrArg (fun J : Ideal (HolGerm (ComplexModel n)) => J ^ q)
    (IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv)

private theorem algEquiv_mem_maximal_power_iff
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (q : ℕ) (F : HolGerm (ComplexModel n)) :
    E F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  constructor
  · intro h
    have hm := Ideal.mem_map_of_mem E.symm.toRingEquiv.toRingHom h
    rw [algEquiv_map_maximal_power] at hm
    change E.symm (E F) ∈ _ at hm
    simpa only [AlgEquiv.symm_apply_apply] using hm
  · intro h
    have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom h
    rwa [algEquiv_map_maximal_power] at hm

private theorem hilbertSamuelValue_map_algEquiv
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (J : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map E.toRingEquiv.toRingHom J) ℓ =
      hilbertSamuelValue J ℓ := by
  let Q :
      (HolGerm (ComplexModel n) ⧸
        (J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1))) ≃ₐ[ℂ]
      (HolGerm (ComplexModel n) ⧸
        (Ideal.map E.toRingEquiv.toRingHom J ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1))) :=
    Ideal.quotientEquivAlg _ _ E (by
      rw [Ideal.map_sup]
      change Ideal.map E.toRingEquiv.toRingHom J ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1) =
        Ideal.map E.toRingEquiv.toRingHom J ⊔
          Ideal.map E.toRingEquiv.toRingHom
            (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1))
      rw [algEquiv_map_maximal_power])
  exact Q.toLinearEquiv.finrank_eq.symm

private theorem span_units_equiv_reindex {ι κ : Type*}
    (e : ι ≃ κ) (u : ι → ℂ) (hu : ∀ j, u j ≠ 0)
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (F : κ → HolGerm (ComplexModel n)) :
    Ideal.span (range fun j => HolGerm.constHom (u j) * E (F (e j))) =
      Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range F)) := by
  rw [Ideal.map_span,← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨j,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e j,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨a,rfl⟩
    obtain ⟨j,rfl⟩ := e.surjective a
    apply (Ideal.unit_mul_mem_iff_mem _
      ((isUnit_iff_ne_zero.mpr (hu j)).map HolGerm.constHom)).mp
    exact Ideal.subset_span ⟨j,rfl⟩

private theorem whole_stalk_eq_translated_of_oka_span
    (A : GermIdeal n (ComplexModel n)) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hH : ∀ i, HolAt (H i) p)
    (hgen : ∀ f, A.mem p f ↔ InSpanAt H p f) :
    wholeChartStalkIdeal A p p (mem_chart_source (ComplexModel n) p) =
      translatedIdeal H p hH := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hAf,rfl⟩
    obtain ⟨hfh,c,hc,he⟩ := (hgen f).mp hAf
    have ht : Tendsto (fun z : ComplexModel n => z+p) (𝓝 0) (𝓝 p) := by
      have hc : ContinuousAt (fun z : ComplexModel n => z+p) 0 :=
        continuousAt_id.add continuousAt_const
      simpa only [zero_add] using hc.tendsto
    have hmem : translatedGerm p f hfh ∈ translatedIdeal H p hH := by
      apply (inSpanAt_zero_iff_mem_origin_span
        (fun i z => H i (z+p)) (fun i => translated_holomorphic p (hH i))
        (translated_holomorphic p hfh)).mp
      exact ⟨translated_holomorphic p hfh,fun i z => c i (z+p),
        fun i => translated_holomorphic p (hc i),ht.eventually he⟩
    have heq : chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) f hf =
        translatedGerm p f hfh := by
      simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq,
        OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]
    rwa [heq]
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    apply Ideal.subset_span
    refine ⟨H i,(hH i).mono fun _ hz => hz.mdifferentiableAt,
      (hgen _).mpr (inSpanAt_self hH i),?_⟩
    simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq,
      OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq]

private theorem original_hs_dictionary
    (A : GermIdeal n (ComplexModel n)) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) (p : ComplexModel n)
    (hH : ∀ i, HolAt (H i) p)
    (hgen : ∀ f, A.mem p f ↔ InSpanAt H p f) (ℓ : ℕ) :
    hilbertSamuelAt A p ℓ = hilbertSamuelValue (translatedIdeal H p hH) ℓ := by
  change hilbertSamuelValue
    (wholeChartStalkIdeal A p p (mem_chart_source (ComplexModel n) p)) ℓ = _
  rw [whole_stalk_eq_translated_of_oka_span A H p hH hgen]

variable {I : Ideal (HolGerm (ComplexModel n))}
variable {G : ActualAnalyticInheritedFamily n 0
  (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

private theorem scaled_representatives_eventually_eq
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (H : ActualVertexIndex n I → ComplexModel n → ℂ)
    (hH : ∀ a, HolAt (H a) 0) (hG : ∀ a, HolGerm.mk (H a) (hH a) = G.germs a) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ j : Fin (actualVertexCount n I),
      modelFunction (actualInheritedSourceScaledFamily P s j) x =
        (s ^ weightedDegree (degLexWeight n P.germs.degreeBound)
          (actualVertexEnumeration n I j).val)⁻¹ *
        H (actualVertexEnumeration n I j)
          (actualDiagonalMap (fun i => s ^ degLexWeight n P.germs.degreeBound i) x) := by
  apply eventually_all.mpr
  intro j
  let c : Fin n → ℂ := fun i => s ^ degLexWeight n P.germs.degreeBound i
  let u : ℂ := (s ^ weightedDegree (degLexWeight n P.germs.degreeBound)
    (actualVertexEnumeration n I j).val)⁻¹
  have he : modelGerm P.radius_pos
      (actualInheritedSourceScaledFamily_differentiableOn P hs j) =
      HolGerm.constHom u * actualDiagonalPullback c
        (HolGerm.mk (H (actualVertexEnumeration n I j))
          (hH (actualVertexEnumeration n I j))) :=
    (actualInheritedSourceScaledFamily_modelGerm P hs j).trans
      (congrArg (fun F : HolGerm (ComplexModel n) =>
        HolGerm.constHom u * actualDiagonalPullback c F)
          (hG (actualVertexEnumeration n I j)).symm)
  rw [actualDiagonalPullback,compAlgHom_mk,← HolGerm.mk_const,← HolGerm.mk_mul] at he
  exact HolGerm.mk_eq_mk_iff.mp he

private theorem translated_scaled_member_dictionary
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (H : ActualVertexIndex n I → ComplexModel n → ℂ)
    (u : Fin (actualVertexCount n I) → ℂ)
    (W : Set (ComplexModel n)) (hW : IsOpen W)
    (heq : ∀ x ∈ W, ∀ j, modelFunction (actualInheritedSourceScaledFamily P s j) x =
      u j * H (actualVertexEnumeration n I j) (actualDiagonalMap c x))
    (x : ComplexModel n) (hx : x ∈ W)
    (hH : ∀ a, HolAt (H a) (actualDiagonalMap c x))
    (hdom : MapsTo (fun z => EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) x + z)
      (ball 0 (P.radius/2)) (ball 0 P.radius))
    (j : Fin (actualVertexCount n I)) :
    actualInheritedTranslatedGerm P hs
        (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) x) hdom j =
      HolGerm.constHom (u j) * diagonalAlgEquiv c hc
        (translatedGerm (actualDiagonalMap c x) (H (actualVertexEnumeration n I j))
          (hH (actualVertexEnumeration n I j))) := by
  change modelGerm (half_pos P.radius_pos) _ =
    HolGerm.constHom (u j) * actualDiagonalPullback c _
  unfold translatedGerm
  rw [actualDiagonalPullback,compAlgHom_mk,← HolGerm.mk_const,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  have ht : Tendsto (fun z : ComplexModel n => z+x) (𝓝 0) (𝓝 x) := by
    have hc : ContinuousAt (fun z : ComplexModel n => z+x) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  filter_upwards [ht.eventually (hW.mem_nhds hx)] with z hz
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  change actualInheritedSourceScaledFamily P s j (e x + e z) =
    u j * H (actualVertexEnumeration n I j) (actualDiagonalMap c z + actualDiagonalMap c x)
  have hh := heq (z+x) hz j
  change actualInheritedSourceScaledFamily P s j (e (z+x)) = _ at hh
  simpa only [map_add,add_comm] using hh

private theorem translated_scaled_ideal_dictionary
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s ∈ ball 0 P.radius)
    (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (H : ActualVertexIndex n I → ComplexModel n → ℂ)
    (u : Fin (actualVertexCount n I) → ℂ) (hu : ∀ j, u j ≠ 0)
    (W : Set (ComplexModel n)) (hW : IsOpen W)
    (heq : ∀ x ∈ W, ∀ j, modelFunction (actualInheritedSourceScaledFamily P s j) x =
      u j * H (actualVertexEnumeration n I j) (actualDiagonalMap c x))
    (x : ComplexModel n) (hx : x ∈ W)
    (hH : ∀ a, HolAt (H a) (actualDiagonalMap c x))
    (hdom : MapsTo (fun z => EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) x + z)
      (ball 0 (P.radius/2)) (ball 0 P.radius)) :
    actualInheritedTranslatedIdeal P hs
        (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) x) hdom =
      Ideal.map (diagonalAlgEquiv c hc).toRingEquiv.toRingHom
        (translatedIdeal H (actualDiagonalMap c x) hH) := by
  have hfun :
      actualInheritedTranslatedGerm P hs
          (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) x) hdom =
        fun j => HolGerm.constHom (u j) * diagonalAlgEquiv c hc
          (translatedGerm (actualDiagonalMap c x) (H (actualVertexEnumeration n I j))
            (hH (actualVertexEnumeration n I j))) :=
    funext fun j => translated_scaled_member_dictionary P hs c hc H u W hW heq x hx hH hdom j
  change Ideal.span (range _) = _
  rw [hfun]
  exact span_units_equiv_reindex (actualVertexEnumeration n I) u hu
    (diagonalAlgEquiv c hc) (fun a => translatedGerm (actualDiagonalMap c x) (H a) (hH a))

/-- ONLY local original finite generation, SAME whole inherited generation
and whole prefixes produce ONE original open on which SAME member marked
orders are equivalent to the ENTIRE original HS profile. -/
theorem exists_actual_inherited_neighborhood_member_orders_iff_hs
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k) :
    ∃ (H : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A) →
        ComplexModel n → ℂ) (hg : ∀ a, HolAt (H a) 0),
      (∀ a, HolGerm.mk (H a) (hg a) = G.germs a) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        (∀ a, DifferentiableOn ℂ (H a) U) ∧
        (∀ y ∈ U, ∀ f, A.mem y f ↔ InSpanAt H y f) ∧
        ∃ hhol : ∀ y ∈ U, ∀ a, HolAt (H a) y,
          ∀ y (hy : y ∈ U),
            (∀ a, translatedGerm y (H a) (hhol y hy a) ∈
              IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) ↔
            ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A 0 ℓ := by
  let I := originalCoherentOriginIdeal A
  obtain ⟨H,hg,hG,V,hV,h0V,hHd,hgen,hhol,horders⟩ :=
    exists_actual_inherited_local_hs_locus_member_orders A hfg G hspan hred
  obtain ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,_hsource,hnear⟩ :=
    exists_actual_inherited_neighborhood_standard_jets I G hspan
  let c : Fin n → ℂ := fun i => s ^ degLexWeight n P.germs.degreeBound i
  have hc : ∀ i, c i ≠ 0 := fun i => pow_ne_zero _ hs0
  let L := actualDiagonalMap c
  let L' := actualDiagonalMap (fun i => (c i)⁻¹)
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  let u (j : Fin (actualVertexCount n I)) : ℂ :=
    (s ^ weightedDegree (degLexWeight n P.germs.degreeBound)
      (actualVertexEnumeration n I j).val)⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j => inv_ne_zero (pow_ne_zero _ hs0)
  obtain ⟨W,hWeq,hW,h0W⟩ := _root_.mem_nhds_iff.mp
    (scaled_representatives_eventually_eq P hs H hg hG)
  let U := V ∩ L' ⁻¹' W ∩ (fun y => e (L' y)) ⁻¹' ball 0 δ
  have hU : IsOpen U := (hV.inter (hW.preimage L'.continuous)).inter
    (isOpen_ball.preimage (e.continuous.comp L'.continuous))
  have h0U : (0 : ComplexModel n) ∈ U := by
    exact ⟨⟨h0V,by simpa only [mem_preimage,map_zero] using h0W⟩,
      by simpa only [mem_preimage,map_zero] using mem_ball_self hδ⟩
  have hUV : U ⊆ V := fun _ hy => hy.1.1
  let hholU : ∀ y ∈ U, ∀ a, HolAt (H a) y := fun y hy a => hhol y (hUV hy) a
  refine ⟨H,hg,hG,U,hU,h0U,fun a => (hHd a).mono hUV,
    fun y hy => hgen y (hUV hy),hholU,?_⟩
  intro y hy
  constructor
  · intro hmarked ℓ
    let x := L' y
    let p := e x
    have hx : x ∈ W := hy.1.2
    have hp : p ∈ ball (0 : CoordinateSpace n) δ := hy.2
    have hLy : L x = y := diagonalMap_inverse c hc y
    change actualDiagonalMap c x = y at hLy
    obtain ⟨hdom,_hTd,_hTb,_hSurj,hEqHS⟩ := hnear p hp
    have hHscaled : ∀ a, HolAt (H a) (actualDiagonalMap c x) := by
      simpa only [hLy] using hholU y hy
    have hmem : ∀ j, actualInheritedTranslatedGerm P hs p hdom j ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^
          normalExponentDegree (actualVertexEnumeration n I j).val := by
      intro j
      have hm := translated_scaled_member_dictionary P hs c hc H u W hW hWeq x hx
        hHscaled hdom j
      rw [hm,Ideal.unit_mul_mem_iff_mem _ ((isUnit_iff_ne_zero.mpr (hu j)).map HolGerm.constHom),
        algEquiv_mem_maximal_power_iff]
      simpa only [hLy] using hmarked (actualVertexEnumeration n I j)
    have hJ := translated_scaled_ideal_dictionary P hs c hc H u hu W hW hWeq x hx
      hHscaled hdom
    have hvalue : hilbertSamuelValue (actualInheritedTranslatedIdeal P hs p hdom) ℓ =
        hilbertSamuelValue (translatedIdeal H y (hholU y hy)) ℓ := by
      rw [hJ,hilbertSamuelValue_map_algEquiv]
      simp only [hLy]
    calc
      hilbertSamuelAt A y ℓ = hilbertSamuelValue (translatedIdeal H y (hholU y hy)) ℓ :=
        original_hs_dictionary A H y (hholU y hy) (hgen y (hUV hy)) ℓ
      _ = hilbertSamuelValue (actualInheritedTranslatedIdeal P hs p hdom) ℓ := hvalue.symm
      _ = hilbertSamuelValue I ℓ := (hEqHS hmem).2 ℓ
      _ = hilbertSamuelAt A 0 ℓ := (hilbertSamuelAt_model_zero A ℓ).symm
  · intro hHS
    exact horders y (hUV hy) (fun a _ => hHS _) 

/-- The SAME finite native principal marked ideals are genuinely coherent
on the actual open submanifold. Their ENTIRE common cosupport equals the
original all-order HS stratum, with one representative/generation domain.
No target diagram/HS or fresh canonical family/selector is supplied. -/
theorem exists_actual_inherited_neighborhood_marked_cosupport_eq_hs
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k) :
    ∃ (H : actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A) →
        ComplexModel n → ℂ) (hg : ∀ a, HolAt (H a) 0),
      (∀ a, HolGerm.mk (H a) (hg a) = G.germs a) ∧
      ∃ U : TopologicalSpace.Opens (ComplexModel n), (0 : ComplexModel n) ∈ U ∧
        (∀ a, DifferentiableOn ℂ (H a) U) ∧
        (∀ y ∈ U, ∀ f, A.mem y f ↔ InSpanAt H y f) ∧
        (∀ a, CoherentOn (actualInheritedPrincipalIdeal (H a)) U) ∧
        (∀ a, (actualInheritedOpenPrincipalMarked U (H a)
          (normalExponentDegree a.val)).ideal.IsCoherent) ∧
        (⋂ a, (actualInheritedOpenPrincipalMarked U (H a)
            (normalExponentDegree a.val)).cosupp) =
          {y : U | ∀ ℓ : ℕ, hilbertSamuelAt A (y : ComplexModel n) ℓ = hilbertSamuelAt A 0 ℓ} := by
  obtain ⟨H,hg,hG,U,hU,h0U,hHd,hgen,hhol,hiff⟩ :=
    exists_actual_inherited_neighborhood_member_orders_iff_hs A hfg G hspan hred
  let O : TopologicalSpace.Opens (ComplexModel n) := ⟨U,hU⟩
  refine ⟨H,hg,hG,O,h0U,hHd,hgen,
    fun a => principal_coherentOn (H a) U hU (hHd a),
    fun a => open_principal_isCoherent O (H a) (hHd a) _,?_⟩
  have hcos (y : O) (a : actualInitialVertices MonomialOrder.degLex
      (actualInheritedOriginFormalIdeal A)) :
      y ∈ (actualInheritedOpenPrincipalMarked O (H a) (normalExponentDegree a.val)).cosupp ↔
        (y : ComplexModel n) ∈ (actualInheritedPrincipalMarked (H a)
          (normalExponentDegree a.val)).cosupp := by
    change y ∈ (MarkedIdeal.pullback (Subtype.val : O → ComplexModel n)
      (actualInheritedPrincipalMarked (H a) (normalExponentDegree a.val))).cosupp ↔ _
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val
      (actualInheritedPrincipalMarked (H a) (normalExponentDegree a.val))
        (fun x g hg => hg.1) O]
    rfl
  ext y
  constructor
  · intro hy
    apply (hiff (y : ComplexModel n) y.property).mp
    intro a
    exact (mem_actualInheritedPrincipalMarked_cosupp_iff (H a) y (hhol y y.property a) _).mp
      ((hcos y a).mp (mem_iInter.mp hy a))
  · intro hHS
    apply mem_iInter.mpr
    intro a
    apply (hcos y a).mpr
    exact (mem_actualInheritedPrincipalMarked_cosupp_iff (H a) y (hhol y y.property a) _).mpr
      ((hiff (y : ComplexModel n) y.property).mpr hHS a)

end
end Hironaka.HironakaActualInheritedNeighborhoodMarkedHS

namespace Hironaka.HironakaActualInheritedNeighborhoodMarkedHS
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci GermIdealOrder IdealWeightPowers OkaRelationSheaf

/-- Public interface to the existing whole translated-germ/point-power dictionary. -/
theorem translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal {n : ℕ}
    (p : ComplexModel n) (f : ComplexModel n → ℂ) (hf : HolAt f p) (q : ℕ) :
    translatedGerm p f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      (idealPow (pointIdeal n p) q).mem p f :=
  translated_power_iff_point_power p f hf q

end Hironaka.HironakaActualInheritedNeighborhoodMarkedHS
