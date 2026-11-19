import Hironaka.Resolution.HironakaG1WeightedPresentationTransport
import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers

/-! Native prefix and supported-division laws in normalized block comparison. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped BigOperators Manifold ContDiff

namespace Hironaka.HironakaG1NativePrefixWeightComparison

noncomputable section

open HolGerm HironakaActualAnalyticFormalNormalPowers
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalFormalSupportedDivision HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualHistoricalMovingPrefixSupport
  HironakaActualFixedInheritedSelector HironakaRelativeNormalMonomialBasis
  HironakaG1WeightedPresentationTransport HironakaG1FiniteWeightedBlocks
  HironakaActualWeightedCoefficientCompression

variable {n k : ℕ} {V : Finset (Fin n →₀ ℕ)}

private theorem native_taylor_span (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range Γ)) =
      Ideal.span (range (fun i => actualUnshiftedTaylorAlgHom n (Γ (a i)))) := by
  rw [Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨a.symm v, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Γ (a i), ⟨a i, rfl⟩, rfl⟩

/-- Supported division and whole-jet bijectivity make the owned
coefficients separate the entire original analytic ideal. -/
theorem native_owned_coefficients_separate
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (Γ : V → HolGerm (ComplexModel n))
    (hLaws : ActualHistoricalFivePointLaws S a words Γ)
    {F G : HolGerm (ComplexModel n)}
    (hF : F ∈ Ideal.span (range Γ)) (hG : G ∈ Ideal.span (range Γ))
    (hCoeff : ∀ β, historicalOwner words β ≠ none →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n F) =
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n G)) :
    F = G := by
  let g : Fin k → MvPowerSeries (Fin n) ℂ :=
    fun i => actualUnshiftedTaylorAlgHom n (Γ (a i))
  have hSep := historicalComplement_separates_of_division words g
    (fun i => (hLaws.1 i).1) hLaws.2.1 hLaws.2.2.2.1
  have hMem := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom
    ((Ideal.span (range Γ)).sub_mem hF hG)
  rw [native_taylor_span Γ a] at hMem
  have hz := hSep _ hMem (fun β hβ => by
    change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (F - G)) = 0
    rw [map_sub, map_sub, sub_eq_zero]
    exact hCoeff β hβ)
  apply sub_eq_zero.mp
  apply actualUnshiftedTaylorAlgHom_injective n
  change actualUnshiftedTaylorAlgHom n (F - G) = 0 at hz
  simpa only [map_zero] using hz

/-- Prefix support supplies all the lower-owned coefficients. To identify
the germ it remains to compare only the owned cones from its degree upward. -/
theorem native_prefix_match_identifies_germ
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (hWords : ∀ i, wordExponent (words i) = (a i).val)
    (Γ Δ : V → HolGerm (ComplexModel n))
    (hΓ : ActualHistoricalFivePointLaws S a words Γ)
    (hΔ : HistoricalWholePrefixSupport V (fun v => actualUnshiftedTaylorAlgHom n (Δ v)))
    (s : V) (G : HolGerm (ComplexModel n))
    (hSource : Δ s ∈ Ideal.span (range Γ)) (hRep : G ∈ Ideal.span (range Γ))
    (hLower : ∀ β i, historicalOwner words β = some i →
      normalExponentDegree (wordExponent (words i)) < normalExponentDegree s.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n G) = 0)
    (hUpper : ∀ β i, historicalOwner words β = some i →
      normalExponentDegree s.val ≤ normalExponentDegree (wordExponent (words i)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (Δ s)) =
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n G)) :
    Δ s = G := by
  apply native_owned_coefficients_separate S a words Γ hΓ hSource hRep
  intro β hβ
  cases hOwn : historicalOwner words β with
  | none => exact (hβ hOwn).elim
  | some i =>
    by_cases hLow : normalExponentDegree (wordExponent (words i)) < normalExponentDegree s.val
    · have hCone := ((historicalOwner_eq_some_iff words β i).mp hOwn).1
      rw [hWords i] at hCone hLow
      rw [hΔ (normalExponentDegree (a i).val) s hLow (a i) le_rfl β hCone,
        hLower β i hOwn (by simpa only [hWords i] using hLow)]
    · exact hUpper β i hOwn (Nat.le_of_not_gt hLow)


/-- The original analytic span of a degree block, with labels from the
same genuine ordered diagram. -/
def nativeBlockSpans {T : Type*} {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (Γ : V → HolGerm (ComplexModel n)) :
    T → Ideal (HolGerm (ComplexModel n)) :=
  fun i => Ideal.span (range fun j => Γ (split ⟨i, j⟩))

private theorem nativeBlockSpan_le_whole {T : Type*} {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (Γ : V → HolGerm (ComplexModel n)) (i : T) :
    nativeBlockSpans split Γ i ≤ Ideal.span (range Γ) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Ideal.subset_span ⟨split ⟨i, j⟩, rfl⟩

private theorem nativeReference_le_whole {T : Type*} [Fintype T] {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (Γ : V → HolGerm (ComplexModel n))
    (e : T → ℕ) (he : ∀ i, 1 ≤ e i) :
    blockPowerReference e (nativeBlockSpans split Γ) ≤ Ideal.span (range Γ) := by
  classical
  unfold blockPowerReference
  have h (s : Finset T) : (∑ i ∈ s, nativeBlockSpans split Γ i ^ e i) ≤ Ideal.span (range Γ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Ideal.add_eq_sup]
      refine sup_le ?_ ih
      have hPow : nativeBlockSpans split Γ i ^ e i ≤ nativeBlockSpans split Γ i ^ 1 :=
        Ideal.pow_le_pow_right (he i)
      rw [pow_one] at hPow
      exact hPow.trans (nativeBlockSpan_le_whole split Γ i)
  exact h Finset.univ

/-- The remaining coefficient test for a native degree block. A candidate
may lie in the corresponding source block plus the target normalized
reference. Its lower owned coefficients must vanish, and its remaining
owned coefficients must match the generator. -/
def NativePrefixBlockMatch {T : Type*} [Fintype T] {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (e : T → ℕ)
    (words : Fin k → CoordinateWord n) (Γ Δ : V → HolGerm (ComplexModel n)) : Prop :=
  ∀ i j, ∃ y ∈ nativeBlockSpans split Γ i,
    ∃ z ∈ blockPowerReference e (nativeBlockSpans split Γ),
      (∀ β l, historicalOwner words β = some l →
        normalExponentDegree (wordExponent (words l)) < normalExponentDegree (split ⟨i, j⟩).val →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (y + z)) = 0) ∧
      (∀ β l, historicalOwner words β = some l →
        normalExponentDegree (split ⟨i, j⟩).val ≤ normalExponentDegree (wordExponent (words l)) →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (Δ (split ⟨i, j⟩))) =
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (y + z)))

/-- Native division turns an owned-coefficient match into the filtered
generator change used by weighted presentation transport. -/
theorem filtered_generator_changes_of_native_prefix_matches
    {T : Type*} [Fintype T] {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (e : T → ℕ) (he : ∀ i, 1 ≤ e i)
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (hWords : ∀ i, wordExponent (words i) = (a i).val)
    (Γ Δ : V → HolGerm (ComplexModel n))
    (hΓ : ActualHistoricalFivePointLaws S a words Γ)
    (hΔ : HistoricalWholePrefixSupport V (fun v => actualUnshiftedTaylorAlgHom n (Δ v)))
    (hWhole : Ideal.span (range Δ) ≤ Ideal.span (range Γ))
    (hMatch : NativePrefixBlockMatch split e words Γ Δ) :
    ∀ i j, ∃ y ∈ nativeBlockSpans split Γ i,
      Δ (split ⟨i, j⟩) - y ∈ blockPowerReference e (nativeBlockSpans split Γ) := by
  intro i j
  obtain ⟨y, hy, z, hz, hLow, hHigh⟩ := hMatch i j
  have hSource : Δ (split ⟨i, j⟩) ∈ Ideal.span (range Γ) :=
    hWhole (Ideal.subset_span ⟨split ⟨i, j⟩, rfl⟩)
  have hRep : y + z ∈ Ideal.span (range Γ) :=
    Ideal.add_mem _ (nativeBlockSpan_le_whole split Γ i hy)
      (nativeReference_le_whole split Γ e he hz)
  have h := native_prefix_match_identifies_germ S a words hWords Γ Δ hΓ hΔ
    (split ⟨i, j⟩) (y + z) hSource hRep hLow hHigh
  exact ⟨y, hy, by rw [h, add_sub_cancel_left]; exact hz⟩

/-- Native same-diagram division reduces reference inclusion to a matching
condition on owned coefficients. The match may use errors from the whole
normalized reference, so block spans need not coincide. -/
theorem normalizedReference_le_of_native_prefix_matches
    {T : Type*} [Fintype T] {τ : T → Type*}
    (split : (Σ i, τ i) ≃ V) (e : T → ℕ) (he : ∀ i, 1 ≤ e i)
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (hWords : ∀ i, wordExponent (words i) = (a i).val)
    (Γ Δ : V → HolGerm (ComplexModel n))
    (hΓ : ActualHistoricalFivePointLaws S a words Γ)
    (hΔ : HistoricalWholePrefixSupport V (fun v => actualUnshiftedTaylorAlgHom n (Δ v)))
    (hWhole : Ideal.span (range Δ) ≤ Ideal.span (range Γ))
    (hMatch : NativePrefixBlockMatch split e words Γ Δ) :
    blockPowerReference e (nativeBlockSpans split Δ) ≤
      blockPowerReference e (nativeBlockSpans split Γ) := by
  have hChanges := filtered_generator_changes_of_native_prefix_matches
    split e he S a words hWords Γ Δ hΓ hΔ hWhole hMatch
  apply blockPowerReference_le_of_modulo
  intro i
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨y, hy, he⟩ := hChanges i j
  have hMem := (nativeBlockSpans split Γ i ⊔ blockPowerReference e (nativeBlockSpans split Γ)).add_mem
    (Ideal.mem_sup_left hy) (Ideal.mem_sup_right he)
  rwa [add_comm y, sub_add_cancel] at hMem

/-- Mutual native cone matches at the actual cross mark give equality of
the normalized block references for different selectors on the same diagram. -/
theorem normalizedReference_eq_of_native_prefix_matches
    {T : Type*} [Fintype T] {τ : T → Type*} [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (split : (Σ i, τ i) ≃ V) (w : T → ℕ) (hw : ∀ i, 0 < w i)
    (S S' : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (words : Fin k → CoordinateWord n)
    (hWords : ∀ i, wordExponent (words i) = (a i).val)
    (Γ Δ : V → HolGerm (ComplexModel n))
    (hΓ : ActualHistoricalFivePointLaws S a words Γ)
    (hΔ : ActualHistoricalFivePointLaws S' a words Δ)
    (hWhole : Ideal.span (range Δ) = Ideal.span (range Γ))
    (hMatch : let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
      NativePrefixBlockMatch split e words Γ Δ ∧ NativePrefixBlockMatch split e words Δ Γ) :
    let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
    blockPowerReference e (nativeBlockSpans split Γ) =
      blockPowerReference e (nativeBlockSpans split Δ) := by
  intro e
  have he (i : T) : 1 ≤ e i := by
    obtain ⟨j⟩ := (inferInstance : Nonempty (τ i))
    exact compressionExponent_pos (blockWeights (τ := τ) w) (fun b => hw b.1) ⟨i, j⟩
  exact le_antisymm
    (normalizedReference_le_of_native_prefix_matches split e he S' a words hWords Δ Γ
      hΔ hΓ.2.2.2.2.2 hWhole.ge hMatch.2)
    (normalizedReference_le_of_native_prefix_matches split e he S a words hWords Γ Δ
      hΓ hΔ.2.2.2.2.2 hWhole.le hMatch.1)


private theorem native_weightedCompression_reindex {T : Type*} [Fintype T]
    {τ : T → Type*} [∀ i, Fintype (τ i)]
    (split : (Σ i, τ i) ≃ V) (w : T → ℕ)
    (hDegree : ∀ i j, w i = normalExponentDegree (split ⟨i, j⟩).val)
    (Γ : V → HolGerm (ComplexModel n)) :
    weightedCompression (fun v : V => normalExponentDegree v.val) Γ =
      weightedCompression (blockWeights (τ := τ) w) (Γ ∘ split) := by
  have hMark : weightedCommonMark (blockWeights (τ := τ) w) =
      weightedCommonMark (fun v : V => normalExponentDegree v.val) :=
    Fintype.prod_equiv split _ _ (fun a => hDegree a.1 a.2)
  unfold weightedCompression
  rw [hMark]
  congr 1
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := split.surjective v
    rcases a with ⟨i, j⟩
    exact ⟨⟨i, j⟩, by simp only [Function.comp_apply, blockWeights, hDegree i j]⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨split ⟨i, j⟩, by simp only [Function.comp_apply, blockWeights, hDegree i j]⟩

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionGermIdealColon HironakaG8LocalHistory

variable {X : CMfd.{0} n}

/-- Actual adapted point data on a common analytic source. Only the listed
owned coefficients are compared; the block generators remain separate. -/
def HasNativePrefixComparison
    {T : Type*} [Fintype T] {τ : T → Type*} [∀ i, Fintype (τ i)]
    (split : (Σ i, τ i) ≃ V) (w : T → ℕ)
    (S S' : ActualFixedInheritedSelector V) (a : Fin k ≃ V)
    (words : Fin k → CoordinateWord n) (W : Set X)
    (P Q B : MarkedIdeal n X) (x : X) : Prop :=
  let e := fun i => weightedCommonMark (blockWeights (τ := τ) w) / w i
  ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (Γ Δ : V → HolGerm (ComplexModel n)),
    ActualHistoricalFivePointLaws S a words Γ ∧ ActualHistoricalFivePointLaws S' a words Δ ∧
    Ideal.span (range Γ) = adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ ∧
    Ideal.span (range Δ) = adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ ∧
    adaptedIdeal P.ideal x Φ hΦ = weightedCompression (fun v : V => normalExponentDegree v.val) Γ ∧
    adaptedIdeal Q.ideal x Φ hΦ = weightedCompression (fun v : V => normalExponentDegree v.val) Δ ∧
    adaptedIdeal B.ideal x Φ hΦ = blockPowerReference e (nativeBlockSpans split Γ) ∧
    NativePrefixBlockMatch split e words Γ Δ ∧ NativePrefixBlockMatch split e words Δ Γ

/-- Owned-coefficient comparisons on the whole proper carrier suffice for
the full weak test class of two native records on the same genuine diagram. -/
theorem locWPEquiv_of_native_prefix_comparisons
    {l m q : ℕ} {T : Type*} [Fintype T] {τ : T → Type*}
    [∀ i, Fintype (τ i)] [∀ i, Nonempty (τ i)]
    (split : (Σ i, τ i) ≃ V) (w : T → ℕ) (hw : ∀ i, 0 < w i)
    (hDegree : ∀ i j, w i = normalExponentDegree (split ⟨i, j⟩).val)
    (S S' : ActualFixedInheritedSelector V) (a : Fin k ≃ V)
    (words : Fin k → CoordinateWord n) (hWords : ∀ i, wordExponent (words i) = (a i).val)
    (W : Set X) (P Q B : MarkedIdeal n X)
    (hP : IsInvDomain l P) (hQ : IsInvDomain m Q) (hB : IsInvDomain q B)
    (hPN : P.N = B.N) (hQN : Q.N = B.N) (hPE : B.E = P.E) (hQE : B.E = Q.E)
    (hPM : P.d = B.d) (hQM : Q.d = B.d)
    (hAt : ∀ x ∈ P.N, HasNativePrefixComparison split w S S' a words W P Q B x) :
    LocWPEquiv P Q := by
  apply locWPEquiv_of_independent_finiteBlockAdaptedPresentations T T τ τ w w hw hw
    P Q B hP hQ hB hPN hQN hPE hQE hPM hQM
  · intro x hx
    obtain ⟨Φ, hΦ, Γ, _, _, _, _, _, hComp, _, hRef, _, _⟩ := hAt x hx
    refine ⟨Φ, hΦ, (fun i j => Γ (split ⟨i, j⟩)), ?_, hRef⟩
    exact hComp.trans (native_weightedCompression_reindex split w hDegree Γ)
  · intro x hx
    have hx' : x ∈ P.N := by rwa [hPN, ← hQN]
    obtain ⟨Φ, hΦ, Γ, Δ, hΓ, hΔ, hΓSpan, hΔSpan, _, hComp, hRef, hF, hR⟩ := hAt x hx'
    refine ⟨Φ, hΦ, (fun i j => Δ (split ⟨i, j⟩)), ?_, ?_⟩
    · exact hComp.trans (native_weightedCompression_reindex split w hDegree Δ)
    · exact hRef.trans (normalizedReference_eq_of_native_prefix_matches split w hw S S' a words
        hWords Γ Δ hΓ hΔ (hΔSpan.trans hΓSpan.symm) ⟨hF, hR⟩)

end

end Hironaka.HironakaG1NativePrefixWeightComparison
