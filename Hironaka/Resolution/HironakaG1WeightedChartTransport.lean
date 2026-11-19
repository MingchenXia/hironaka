import Hironaka.Resolution.HironakaG1WeightedPresentationTransport
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep
import Hironaka.Resolution.HironakaActualNativeSourceChartComposition
import Hironaka.Resolution.HironakaEmbeddedExceptional

/-! Entire weighted block ideals in independently chosen adapted coordinates. -/
set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped BigOperators Topology Manifold ContDiff

namespace Hironaka.HironakaG1WeightedChartTransport

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers HolGerm
  HironakaHolomorphicJetChartInvariance HironakaSmoothSubmersionGermIdealColon
  HironakaActualNativeSourceChartComposition HironakaEmbeddedExceptional
  HironakaG1WeightedPresentationTransport HironakaActualWeightedCoefficientCompression
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaSmoothCentreCoherentDomain

variable {n : ℕ} {X : CMfd.{0} n}

/-- The transition from the second chart's coordinates to the first chart's
coordinates is the actual forward first chart after the inverse second chart. -/
def adaptedChartTransition (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) :=
  RegularAtDimTransport.LocalHolomorphicEquivAt.comp
    (LocalHolomorphicEquivAt.symmAt Θ hΘ) Φ
    (by
      change Θ.invFun 0 = chartAt (ComplexModel n) x x
      simpa only [hΘ] using Θ.left_inv _ Θ.center_mem_source)

theorem adaptedChartTransition_zero (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    (adaptedChartTransition x Φ Θ hΘ).toFun 0 = 0 := by
  change Φ.toFun (Θ.invFun 0) = 0
  have hInv : Θ.invFun 0 = chartAt (ComplexModel n) x x := by
    simpa only [hΘ] using Θ.left_inv _ Θ.center_mem_source
  rw [hInv, hΦ]

/-- Pullback by the actual transition carries a first-chart germ to the
second-chart expression of the same source germ. -/
def adaptedChartGermEquiv (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (adaptedChartTransition x Φ Θ hΘ) (adaptedChartTransition_zero x Φ Θ hΦ hΘ)

/-- Entire original germs in two independently chosen adapted charts are
related by the actual holomorphic transition. -/
theorem adaptedChartGermEquiv_apply (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) (F : X → ℂ)
    (hF : HolomorphicAt n F x) :
    adaptedChartGermEquiv x Φ Θ hΦ hΘ (adaptedGerm x Φ hΦ F hF) =
      adaptedGerm x Θ hΘ F hF := by
  unfold adaptedChartGermEquiv adaptedGerm
  rw [localGermAlgEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  let D := adaptedChartTransition x Φ Θ hΘ
  filter_upwards [D.isOpen_source.mem_nhds D.center_mem_source] with z hz
  have hzΦ : Θ.invFun z ∈ Φ.source := hz.2
  change F ((chartAt (ComplexModel n) x).symm (Φ.invFun (Φ.toFun (Θ.invFun z)))) =
    F ((chartAt (ComplexModel n) x).symm (Θ.invFun z))
  rw [Φ.left_inv _ hzΦ]

/-- Whole ideal transport between independently chosen charts. -/
theorem map_adaptedIdeal_transition (I : GermIdeal n X) (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    Ideal.map (adaptedChartGermEquiv x Φ Θ hΦ hΘ).toRingEquiv.toRingHom (adaptedIdeal I x Φ hΦ) =
      adaptedIdeal I x Θ hΘ := by
  unfold adaptedIdeal
  rw [Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨F, hF, hI, rfl⟩, rfl⟩
    exact ⟨F, hF, hI, (adaptedChartGermEquiv_apply x Φ Θ hΦ hΘ F hF)⟩
  · rintro ⟨F, hF, hI, rfl⟩
    exact ⟨_, ⟨F, hF, hI, rfl⟩, adaptedChartGermEquiv_apply x Φ Θ hΦ hΘ F hF⟩

/-- The same map relates the entire analytic source origin ideals in two
genuine native chart choices. -/
theorem map_native_origin_ideal_transition (W : Set X)
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (x : X)
    (Φ Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    Ideal.map (adaptedChartGermEquiv x Φ Θ hΦ hΘ).toRingEquiv.toRingHom
      (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0)) =
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Θ) 0) := by
  rw [actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hΦsrc hΦ W hW,
    actual_original_translated_flattened_vanishing_origin_eq_adapted x Θ hΘsrc hΘ W hW]
  exact map_adaptedIdeal_transition _ x Φ Θ hΦ hΘ

/-- Coordinate transport commutes with compression at the unchanged
literal cross mark. -/
theorem map_weightedCompression {ι R A : Type*} [Fintype ι] [CommRing R] [CommRing A]
    (φ : R →+* A) (w : ι → ℕ) (c : ι → R) :
    Ideal.map φ (weightedCompression w c) = weightedCompression w (φ ∘ c) := by
  unfold weightedCompression
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (map_pow φ (c i) _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, map_pow φ (c i) _⟩

private theorem map_finset_ideal_sum {S R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (s : Finset S) (I : S → Ideal R) :
    Ideal.map φ (∑ i ∈ s, I i) = ∑ i ∈ s, Ideal.map φ (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Ideal.add_eq_sup, Ideal.map_sup, ih, Ideal.add_eq_sup]

/-- Every normalized block power and their total reference transport under
the same original coordinate map. -/
theorem map_blockPowerReference {S R A : Type*} [Fintype S] [CommRing R] [CommRing A]
    (φ : R →+* A) (e : S → ℕ) (I : S → Ideal R) :
    Ideal.map φ (blockPowerReference e I) =
      blockPowerReference e (fun i => Ideal.map φ (I i)) := by
  unfold blockPowerReference
  rw [map_finset_ideal_sum]
  simp only [Ideal.map_pow]


/-- Coordinate transport sends each block span to the span of the
transported generators, and therefore transports their normalized powers. -/
theorem map_blockPowerReference_generators {S R A : Type*} [Fintype S] [CommRing R] [CommRing A]
    {τ : S → Type*} (φ : R →+* A) (e : S → ℕ) (c : (i : S) → τ i → R) :
    Ideal.map φ (blockPowerReference e (fun i => Ideal.span (range (c i)))) =
      blockPowerReference e (fun i => Ideal.span (range (φ ∘ c i))) := by
  rw [map_blockPowerReference]
  congr 1
  funext i
  rw [Ideal.map_span]
  congr 1
  exact (Set.range_comp _ _).symm

open MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG1FiniteWeightedBlocks HironakaG8LocalHistory

/-- The actual source chart, generator family, and two whole adapted
ideal identities needed for finite weighted block comparison. -/
structure BlockPresentationInChart
    (S : Type*) [Fintype S] (τ : S → Type*) [∀ i, Fintype (τ i)]
    (w : S → ℕ) (P B : MarkedIdeal n X) (x : X) where
  chart : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)
  source : chart.source ⊆ (chartAt (ComplexModel n) x).target
  centered : chart.toFun (chartAt (ComplexModel n) x x) = 0
  generators : (i : S) → τ i → HolGerm (ComplexModel n)
  compression : adaptedIdeal P.ideal x chart centered =
    weightedCompression (blockWeights (τ := τ) w) (fun a => generators a.1 a.2)
  reference : adaptedIdeal B.ideal x chart centered =
    blockPowerReference (fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i)
      (fun i => Ideal.span (range (generators i)))

/-- Transport a whole compression and its reference from its original
adapted coordinates to any other actual chart of the same source point. -/
def BlockPresentationInChart.transport
    {S : Type*} [Fintype S] {τ : S → Type*} [∀ i, Fintype (τ i)] {w : S → ℕ}
    {P B : MarkedIdeal n X} {x : X}
    (D : BlockPresentationInChart S τ w P B x)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    BlockPresentationInChart S τ w P B x where
  chart := Θ
  source := hΘsrc
  centered := hΘ
  generators := fun i j => adaptedChartGermEquiv x D.chart Θ D.centered hΘ (D.generators i j)
  compression := by
    rw [← map_adaptedIdeal_transition P.ideal x D.chart Θ D.centered hΘ, D.compression,
      map_weightedCompression]
    rfl
  reference := by
    rw [← map_adaptedIdeal_transition B.ideal x D.chart Θ D.centered hΘ, D.reference,
      map_blockPowerReference_generators]
    rfl

/-- A pair of independently chosen adapted source charts may give the two
compressed records. The left chart also presents their coherent reference.
Filtered matching is expressed after transporting the left germs. -/
def HasIndependentChartFilteredBlockChange
    (S : Type*) [Fintype S] (τ υ : S → Type*) [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    (w : S → ℕ) (P Q B : MarkedIdeal n X) (x : X) : Prop :=
  ∃ (D : BlockPresentationInChart S τ w P B x)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0)
    (d : (i : S) → υ i → HolGerm (ComplexModel n)),
    let c := (D.transport Θ hΘsrc hΘ).generators
    let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
    adaptedIdeal Q.ideal x Θ hΘ =
      weightedCompression (blockWeights (τ := υ) w) (fun a => d a.1 a.2) ∧
    (∀ i j, ∃ y ∈ Ideal.span (range (d i)), c i j - y ∈
      blockPowerReference e (fun a => Ideal.span (range (d a)))) ∧
    (∀ i j, ∃ y ∈ Ideal.span (range (c i)), d i j - y ∈
      blockPowerReference e (fun a => Ideal.span (range (c a))))

theorem HasIndependentChartFilteredBlockChange.to_common_chart
    {S : Type*} [Fintype S] {τ υ : S → Type*} [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    {w : S → ℕ} {P Q B : MarkedIdeal n X} {x : X}
    (h : HasIndependentChartFilteredBlockChange S τ υ w P Q B x) :
    HasFilteredBlockChange S τ υ w P Q B x := by
  obtain ⟨D, Θ, hΘsrc, hΘ, d, hQ, hCD, hDC⟩ := h
  let T := D.transport Θ hΘsrc hΘ
  exact ⟨Θ, hΘ, T.generators, d, T.compression, hQ, T.reference, hCD, hDC⟩

/-- Matching transported block generators at the actual cross mark yields
the full proper-carrier test comparison in independently chosen charts. -/
theorem locWPEquiv_of_independentChartFilteredBlockChanges
    {k l q : ℕ} (S : Type*) [Fintype S] (τ υ : S → Type*)
    [∀ i, Fintype (τ i)] [∀ i, Fintype (υ i)]
    [∀ i, Nonempty (τ i)] [∀ i, Nonempty (υ i)]
    (w : S → ℕ) (hw : ∀ i, 0 < w i)
    (hCross : weightedCommonMark (blockWeights (τ := τ) w) =
      weightedCommonMark (blockWeights (τ := υ) w))
    (P Q B : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (hB : IsInvDomain q B)
    (hPN : P.N = B.N) (hQN : Q.N = B.N) (hPE : B.E = P.E) (hQE : B.E = Q.E)
    (hPM : P.d = B.d) (hQM : Q.d = B.d)
    (hAt : ∀ x ∈ P.N, HasIndependentChartFilteredBlockChange S τ υ w P Q B x) :
    LocWPEquiv P Q :=
  locWPEquiv_of_filteredBlockChanges S τ υ w hw hCross P Q B hP hQ hB
    hPN hQN hPE hQE hPM hQM (fun x hx => (hAt x hx).to_common_chart)


open HironakaActualHistoricalNativeStageStep HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis

/-- Actual native point data furnish the entire transported source span and
compressed ideal in any other chosen actual chart. The five point laws
are kept on the original witnesses. -/
theorem native_point_weighted_data_in_given_chart
    {V : Finset (Fin n →₀ ℕ)} {k : ℕ}
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (W : Set X) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (P : MarkedIdeal n X) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a words W P x)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΘ : Θ.toFun (chartAt (ComplexModel n) x x) = 0) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (_hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
      (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
      (Γ : V → HolGerm (ComplexModel n)),
      let Γ' := adaptedChartGermEquiv x Φ Θ hΦ hΘ ∘ Γ
      ActualHistoricalFivePointLaws S a words Γ ∧
      Ideal.span (range (fun i => Γ (a i))) = originalCoherentOriginIdeal
        (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n := n) W) x Φ) 0) ∧
      Ideal.span (range Γ') = adaptedIdeal (vanishingIdeal (n := n) W) x Θ hΘ ∧
      adaptedIdeal P.ideal x Θ hΘ =
        weightedCompression (fun v : V => normalExponentDegree v.val) Γ' := by
  obtain ⟨Φ, hΦsrc, hΦ, Γ, hLaws, hSpan, hComp⟩ := hAt
  let φ := (adaptedChartGermEquiv x Φ Θ hΦ hΘ).toRingEquiv.toRingHom
  refine ⟨Φ, hΦsrc, hΦ, Γ, hLaws, hSpan, ?_, ?_⟩
  have hRange : range (fun i => Γ (a i)) = range Γ := a.surjective.range_comp Γ
  have hWSpan : Ideal.span (range Γ) = adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ := by
    rw [hRange] at hSpan
    exact hSpan.trans (actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hΦsrc hΦ W hW)
  · change Ideal.span (range (φ ∘ Γ)) = adaptedIdeal (vanishingIdeal (n := n) W) x Θ hΘ
    rw [← map_adaptedIdeal_transition _ x Φ Θ hΦ hΘ, ← hWSpan, Ideal.map_span]
    congr 1
    exact Set.range_comp _ _
  · change adaptedIdeal P.ideal x Θ hΘ =
      weightedCompression (fun v : V => normalExponentDegree v.val) (φ ∘ Γ)
    rw [← map_adaptedIdeal_transition _ x Φ Θ hΦ hΘ, hComp, map_weightedCompression]

end

end Hironaka.HironakaG1WeightedChartTransport
