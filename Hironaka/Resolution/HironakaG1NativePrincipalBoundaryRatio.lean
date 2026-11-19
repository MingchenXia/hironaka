import Hironaka.Resolution.HironakaG1CarrierPowerReduction
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents
import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers

/-! Exact boundary ratios for uniform-degree native presentations of a principal analytic stalk. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.HironakaG1NativePrincipalBoundaryRatio
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression HironakaActualNativeSourceChartComposition
  HironakaSmoothSubmersionGermIdealColon HironakaG1CarrierPowerReduction
  HironakaActualPowerBoundaryExponents HironakaG8MixedBoundaryExponents
  DivisorExponent DivisorExponentAlong IdealWeightPowers GermIdealPullbackCalculus
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
  HironakaSmoothCentreCoherentDomain GermIdealOrder OrderTaylor HironakaActualOriginalFormalHSTransfer

/-- Literal powers of any finite generating family of a nonzero principal
ideal in a local domain generate the whole power of that ideal. -/
theorem span_uniformPowers_of_principal {R ι : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] [Fintype ι] (c : ι → R) {g : R} (hg : g ≠ 0)
    (hSpan : Ideal.span (range c) = Ideal.span ({g} : Set R)) (r : ℕ) :
    Ideal.span (range (fun i => c i ^ r)) = (Ideal.span (range c)) ^ r := by
  have hMem (i : ι) : g ∣ c i := by
    apply Ideal.mem_span_singleton.mp
    rw [← hSpan]
    exact Ideal.subset_span ⟨i,rfl⟩
  choose b hb using hMem
  have hgMem : g ∈ Ideal.span (range c) := hSpan.symm ▸ Ideal.mem_span_singleton_self g
  obtain ⟨a,ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgMem
  have hsum : (∑ i, a i * b i) = 1 := by
    apply mul_right_cancel₀ hg
    rw [one_mul]
    calc
      _ = ∑ i, a i * c i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hb i]
        ring
      _ = g := ha
  have hunit : ∃ i, IsUnit (b i) := by
    by_contra hn
    push Not at hn
    have hMax : (∑ i, a i * b i) ∈ IsLocalRing.maximalIdeal R := by
      apply Ideal.sum_mem _
      intro i _
      exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hn i))
    exact (Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal R))
      ((Ideal.eq_top_iff_one _).mpr (hsum ▸ hMax))
  obtain ⟨i,hi⟩ := hunit
  rw [hSpan, Ideal.span_singleton_pow]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.mem_span_singleton.mpr (pow_dvd_pow_of_dvd (show g ∣ c j from ⟨b j,hb j⟩) r)
  · apply Ideal.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    have hd : c i ^ r ∣ g ^ r := by
      rw [hb i, mul_pow, mul_comm (g ^ r), (hi.pow r).mul_left_dvd]
    obtain ⟨b,hb⟩ := hd
    rw [hb]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i,rfl⟩)

variable {n k : ℕ} {X : CMfd.{0} n} {W : Set X} {Q : MarkedIdeal n X}

/-- The marked compression of a uniform-degree native family generating a
nonzero principal source has the exact original normalized boundary exponent.
The native common mark can differ from the common vertex degree. -/
theorem native_uniformPrincipal_boundary_ratio
    {V : Finset (Fin n →₀ ℕ)} (hV : V.Nonempty) (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (μ : ℕ) (hμ : 0 < μ) (hUniform : ∀ v : V, normalExponentDegree v.val = μ)
    (hMark : Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (hN : Q.N = univ) (hQN : IsClosedSubmanifold n Q.N) (hQI : Q.ideal.IsCoherent)
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x)
    (hPrincipal : ∀ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0),
      ∃ g ≠ 0, adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ = Ideal.span {g})
    (H : Set X) {p : ℕ} (hH : RegularAtDim (n := n) H x p) :
    μ * divExpAlong n Q.N Q.ideal H x =
      Q.d * divExpAlong n Q.N (vanishingIdeal (n := n) W) H x := by
  obtain ⟨Φ,hSrc,hΦ,Γ,_,hSpan,hComp⟩ := hAt
  let I := vanishingIdeal (n := n) W
  let r := Q.d / μ
  have hWeights (v : V) : 0 < normalExponentDegree v.val := hUniform v ▸ hμ
  obtain ⟨v,hv⟩ := hV
  let u : V := ⟨v,hv⟩
  have hr : 1 ≤ r := by
    have hh := compressionExponent_pos (fun v : V => normalExponentDegree v.val) hWeights u
    rwa [← hMark, hUniform u] at hh
  have hScale : μ * r = Q.d := by
    have hh := weight_mul_compressionExponent (fun v : V => normalExponentDegree v.val) u
    rwa [← hMark, hUniform u] at hh
  obtain ⟨g,hg,hPrincipal'⟩ := hPrincipal Φ hΦ
  have hOriginal : Ideal.span (range Γ) = adaptedIdeal I x Φ hΦ := by
    rw [← a.surjective.range_comp Γ]
    exact hSpan.trans (actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hSrc hΦ W hW)
  have heq : adaptedIdeal Q.ideal x Φ hΦ = adaptedIdeal (idealPow I r) x Φ hΦ := by
    rw [hComp, adaptedIdeal_power_exact I hW x Φ hΦ]
    unfold weightedCompression
    simp only [← hMark]
    simp only [hUniform]
    rw [span_uniformPowers_of_principal Γ hg (hOriginal.trans hPrincipal'), hOriginal]
  have hPower := isCoherent_idealPow hW r
  have hMem (F : X → ℂ) : Q.ideal.mem x F ↔ (idealPow I r).mem x F := by
    constructor
    · intro hf
      have hHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQI hf
      exact (mem_adaptedIdeal_iff _ hPower x Φ hΦ F hHol).mp
        (heq ▸ (mem_adaptedIdeal_iff _ hQI x Φ hΦ F hHol).mpr hf)
    · intro hf
      have hHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hPower hf
      exact (mem_adaptedIdeal_iff _ hQI x Φ hΦ F hHol).mp
        (heq.symm ▸ (mem_adaptedIdeal_iff _ hPower x Φ hΦ F hHol).mpr hf)
  have hExp : divExpAlong n Q.N Q.ideal H x = divExpAlong n Q.N (idealPow I r) H x := by
    apply HironakaG8MixedBoundaryExponents.divExpAlong_congr
    intro e
    rw [hN, isDivNearAlong_univ_iff, isDivNearAlong_univ_iff,
      isDivNear_iff hQI hH, isDivNear_iff hPower hH]
    exact forall_congr' (fun F => imp_congr (hMem F) Iff.rfl)
  rw [hExp,divExpAlong_idealPow hQN hW hr, ← Nat.mul_assoc, hScale]

/-- A nonzero principal ideal has exactly its generator's first exponent
as its actual Taylor diagram vertex. -/
theorem actualInitialVertices_principal {F : MvPowerSeries (Fin n) ℂ}
    (hF : F ≠ 0) (m : MonomialOrder (Fin n)) :
    actualInitialVertices m (Ideal.span {F}) = {actualInitialExponent m F hF} := by
  let J : Ideal (MvPowerSeries (Fin n) ℂ) := Ideal.span {F}
  let g := actualInitialExponent m F hF
  have hg : g ∈ actualInitialDiagram m J := ⟨F,Ideal.subset_span (mem_singleton F),hF,rfl⟩
  have hle (a : Fin n →₀ ℕ) (ha : a ∈ actualInitialDiagram m J) : g ≤ a := by
    obtain ⟨G,hG,hGne,hGexp⟩ := ha
    obtain ⟨R,rfl⟩ := Ideal.mem_span_singleton.mp hG
    have hR : R ≠ 0 := right_ne_zero_of_mul hGne
    rw [actualInitialExponent_mul m F R hF hR] at hGexp
    exact hGexp ▸ le_self_add
  ext a
  change a ∈ actualInitialVertices m J ↔ a ∈ ({g} : Finset (Fin n →₀ ℕ))
  rw [Finset.mem_singleton]
  constructor
  · intro ha
    have hm : Minimal (· ∈ actualInitialDiagram m J) a := by
      simpa [actualInitialVertices] using ha
    exact (hm.eq_of_le hg (hle a hm.prop)).symm
  · rintro rfl
    have hm : Minimal (· ∈ actualInitialDiagram m J) g := ⟨hg,fun a ha _ => hle a ha⟩
    simpa [actualInitialVertices] using hm

/-- At the actual principal analytic origin ideal, all canonical initial
weights arise from the single true Taylor exponent, with no extra terms. -/
theorem analyticPrincipal_initial_vertices {g : HolGerm (ComplexModel n)} (hg : g ≠ 0) :
    let f := actualUnshiftedTaylorAlgHom n g
    let hF : f ≠ 0 := fun h =>
      hg (actualUnshiftedTaylorAlgHom_injective n (h.trans (map_zero _).symm))
    actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n (Ideal.span {g})) =
      {actualInitialExponent MonomialOrder.degLex f hF} := by
  dsimp only
  rw [analyticZeroTaylorIdeal, Ideal.map_span, Set.image_singleton]
  exact actualInitialVertices_principal _ _

private theorem adapted_pointIdeal_maximal (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    adaptedIdeal (pointIdeal n x) x Φ hΦ = IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  have hEval (F : X → ℂ) (hF : HolomorphicAt n F x) :
      HolGerm.eval (adaptedGerm x Φ hΦ F hF) = F x := by
    rw [adaptedGerm, HolGerm.eval_mk]
    change F (actualFlatteningInverseMap x Φ 0) = _
    rw [actualFlatteningInverseMap_zero x Φ hΦ]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨F,hF,hMem,rfl⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    exact (hEval F hF).trans (hMem.2.self_of_nhds (mem_singleton x))
  · intro g hg
    obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative x Φ hΦ g
    have hZ := (HolGerm.mem_maximalIdeal_iff _).mp hg
    rw [hEval] at hZ
    exact Ideal.subset_span ⟨F,hF,mem_pointIdeal_of_apply_eq_zero hF hZ,rfl⟩

private theorem adapted_cut_iff (J : GermIdeal n X) (hJ : J.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (d : ℕ) :
    x ∈ cosupport n univ J d ↔
      adaptedIdeal J x Φ hΦ ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ d := by
  have hCoherent : (pointIdeal n x).IsCoherent :=
    CartanIrreducible.cartanCoherence {x} (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton x)
  have hEq := adaptedIdeal_power_exact (pointIdeal n x) hCoherent x Φ hΦ d
  rw [adapted_pointIdeal_maximal] at hEq
  rw [← hEq]
  have hP := isCoherent_idealPow hCoherent d
  constructor
  · intro h
    apply Ideal.span_le.mpr
    rintro _ ⟨F,hF,hMem,rfl⟩
    apply (mem_adaptedIdeal_iff _ hP x Φ hΦ F hF).mpr
    exact mem_idealPow_of_vanishesToOrderOn_univ (h.2 F hMem)
  · intro h
    refine ⟨mem_univ _,fun F hF => ?_⟩
    have hHol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hF
    have hp := (mem_adaptedIdeal_iff _ hP x Φ hΦ F hHol).mp
      (h (Ideal.subset_span ⟨F,hHol,hF,rfl⟩))
    exact ⟨F,hp,Filter.Eventually.of_forall (fun _ _ => rfl)⟩

/-- The uniform native degree is intrinsic. It is the last true ordinary
cut of the original reduced analytic ideal, in any independently chosen chart. -/
theorem native_uniformDegree_original_cut
    {V : Finset (Fin n →₀ ℕ)} (hV : V.Nonempty) (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (μ : ℕ) (hUniform : ∀ v : V, normalExponentDegree v.val = μ)
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    x ∈ cosupport n univ (vanishingIdeal (n := n) W) μ ∧
      x ∉ cosupport n univ (vanishingIdeal (n := n) W) (μ+1) := by
  obtain ⟨Φ,hSrc,hΦ,Γ,hFive,hSpan,_⟩ := hAt
  have hGeneration : Ideal.span (range (fun i => Γ (a i))) =
      adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ :=
    hSpan.trans (actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hSrc hΦ W hW)
  have hMember (G : HolGerm (ComplexModel n)) (d : ℕ) :
      G ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ d ↔
        actualUnshiftedTaylorAlgHom n G ∈ genuineFormalVariables n ^ d := by
    rw [← map_actualUnshifted_maximal_pow]
    exact mem_analytic_ideal_iff_actualUnshifted_extension n _ G
  have hOrd (i : Fin k) := hFive.1 i
  have hExact (i : Fin k) :
      Γ (a i) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ μ ∧
        Γ (a i) ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (μ+1) := by
    have h := hOrd i
    rw [hw i,hUniform (a i)] at h
    exact ⟨(hMember _ _).mpr h.1,fun hG => h.2 ((hMember _ _).mp hG)⟩
  constructor
  · rw [adapted_cut_iff _ hW x Φ hΦ, ← hGeneration, Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    exact (hExact i).1
  · intro h
    rw [adapted_cut_iff _ hW x Φ hΦ, ← hGeneration] at h
    obtain ⟨v,hv⟩ := hV
    let i := a.symm ⟨v,hv⟩
    exact (hExact i).2 (h (Ideal.subset_span ⟨i,rfl⟩))

/-- Two exact principal-stalk ratio computations at the same positive
intrinsic degree give cross-mark equality of the original boundary values. -/
theorem normalized_agreement_of_principal_ratios {μ dP dQ p q e : ℕ} (hμ : 0 < μ)
    (hP : μ * p = dP * e) (hQ : μ * q = dQ * e) :
    dQ * p = dP * q := by
  apply Nat.eq_of_mul_eq_mul_left hμ
  calc
    μ * (dQ * p) = dQ * (μ * p) := by ac_rfl
    _ = dP * (μ * q) := by rw [hP,hQ]; ac_rfl
    _ = μ * (dP * q) := by ac_rfl

/-- Independent uniform-degree native presentations of the same original
principal analytic germ have the same normalized exponent. Their finite
labels, selectors, charts, original common marks, and stated degrees may
be supplied independently. The degree equality is a consequence. -/
theorem independent_native_uniformPrincipal_boundary_ratio
    {P : MarkedIdeal n X} {V T : Finset (Fin n →₀ ℕ)} {j : ℕ}
    (hV : V.Nonempty) (hT : T.Nonempty)
    (S : ActualFixedInheritedSelector V) (S' : ActualFixedInheritedSelector T)
    (a : Fin k ≃ V) (b : Fin j ≃ T)
    (w : Fin k → CoordinateWord n) (v : Fin j → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (hv : ∀ i, wordExponent (v i) = (b i).val)
    (μ ν : ℕ) (hμ : 0 < μ)
    (hUniV : ∀ i : V, normalExponentDegree i.val = μ)
    (hUniT : ∀ i : T, normalExponentDegree i.val = ν)
    (hPMark : P.d = weightedCommonMark (fun i : V => normalExponentDegree i.val))
    (hQMark : Q.d = weightedCommonMark (fun i : T => normalExponentDegree i.val))
    (hPN : P.N = univ) (hQN : Q.N = univ)
    (hPC : IsClosedSubmanifold n P.N) (hQC : IsClosedSubmanifold n Q.N)
    (hPI : P.ideal.IsCoherent) (hQI : Q.ideal.IsCoherent)
    (hW : (vanishingIdeal (n := n) W).IsCoherent) (x : X)
    (hP : ActualHistoricalNativePointPresentation S a w W P x)
    (hQ : ActualHistoricalNativePointPresentation S' b v W Q x)
    (hPrincipal : ∀ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0),
      ∃ g ≠ 0, adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ = Ideal.span {g})
    (H : Set X) {p : ℕ} (hH : RegularAtDim (n := n) H x p) :
    μ = ν ∧ Q.d * divExpAlong n P.N P.ideal H x =
      P.d * divExpAlong n Q.N Q.ideal H x := by
  obtain ⟨hC₁,hC₁'⟩ := native_uniformDegree_original_cut hV S a w hw μ hUniV hW x hP
  obtain ⟨hC₂,hC₂'⟩ := native_uniformDegree_original_cut hT S' b v hv ν hUniT hW x hQ
  have heq : μ = ν := by
    apply le_antisymm
    · by_contra h
      exact hC₂' (cosupport_anti (by omega) hC₁)
    · by_contra h
      exact hC₁' (cosupport_anti (by omega) hC₂)
  refine ⟨heq,?_⟩
  have h1 := native_uniformPrincipal_boundary_ratio hV S a w μ hμ hUniV hPMark
    hPN hPC hPI hW x hP hPrincipal H hH
  have h2 := native_uniformPrincipal_boundary_ratio hT S' b v ν (heq ▸ hμ) hUniT hQMark
    hQN hQC hQI hW x hQ hPrincipal H hH
  rw [← heq] at h2
  rw [hPN] at h1 ⊢
  rw [hQN] at h2 ⊢
  exact normalized_agreement_of_principal_ratios hμ h1 h2

#print axioms native_uniformPrincipal_boundary_ratio
#print axioms analyticPrincipal_initial_vertices
#print axioms native_uniformDegree_original_cut
#print axioms independent_native_uniformPrincipal_boundary_ratio

end
end Hironaka.HironakaG1NativePrincipalBoundaryRatio
