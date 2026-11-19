import Hironaka.Resolution.HironakaG1NativeCrossingIdeal
import Hironaka.Resolution.HironakaActualOpenEmbeddingVanishingIdeal

/-! Independent centered initial crossing charts and their exact common-window records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1IndependentInitialCrossing
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves OkaRelationSheaf
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG1NativeCrossingGeometry HironakaG1NativeCrossingIdeal
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualNativeSourceChartComposition HironakaActualFixedFlatteningHSComparison
  HironakaActualPrescribedCentreRebasing HironakaSmoothCentreCoherentDomain
  HironakaSmoothSubmersionGermIdealColon HironakaRelativeNormalDeformationInitialRelations
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualWeightedCoefficientCompression HironakaRelativeNormalMonomialBasis
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualGeometricCurrentNeighborhoodHS
  HironakaSmoothSubmersionComposition BlowupRestrictOpen
  HironakaActualOpenEmbeddingVanishingIdeal HironakaBaseChange DivisorExponentAlong
  HironakaActualRelativeNormalJetDivision HironakaHolomorphicJetChartInvariance
  MonomialInvariantFunctorialAlong OkaIdealOperations CoherentIdealColon

private theorem model_span_iff {ι : Type} [Fintype ι]
    (s : ι → ComplexModel 2 → ℂ) (x : ComplexModel 2) (f : ComplexModel 2 → ℂ) :
    InSpanAt s x f ↔ IsInSpanAt (n := 2) (· ∈ range s) x f := by
  let e := Fintype.equivFin ι
  let t := s ∘ e.symm
  have hR : range t = range s := e.symm.surjective.range_comp s
  rw [← hR, isInSpanAt_range_iff]
  constructor
  · rintro ⟨hf,c,hc,he⟩
    refine ⟨?_,c ∘ e.symm,fun i => ?_,he.trans ?_⟩
    · simpa only [HolomorphicAt, HolAt, mdifferentiableAt_iff_differentiableAt] using hf
    · simpa only [HolomorphicAt, HolAt, mdifferentiableAt_iff_differentiableAt, Function.comp_apply] using hc (e.symm i)
    exact Eventually.of_forall fun z =>
      (e.symm.sum_comp (fun i => c i z * s i z)).symm
  · rintro ⟨hf,c,hc,he⟩
    refine ⟨?_,c ∘ e,fun i => ?_,he.trans ?_⟩
    · simpa only [HolomorphicAt, HolAt, mdifferentiableAt_iff_differentiableAt] using hf
    · simpa only [HolomorphicAt, HolAt, mdifferentiableAt_iff_differentiableAt, Function.comp_apply] using hc (e i)
    exact Eventually.of_forall fun z => by
      simpa [t,Function.comp_def] using (e.symm.sum_comp (fun i => c (e i) z * s i z))

private theorem pulled_initial_ideal_eq
    {B : GermIdeal 2 (ComplexModel 2)} {I : Ideal (HolGerm (ComplexModel 2))}
    {G : ActualAnalyticInheritedFamily 2 0 (analyticZeroTaylorIdeal 2 I)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R)
    (hMark : weightedCommonMark (fun i : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 2 I) => normalExponentDegree i.val) = 2)
    (hWeight : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal 2 I),
      normalExponentDegree i.val = 2)
    {D : Set (ComplexModel 2)} (hB : B = vanishingIdeal (n := 2) D)
    (f : presentationOpen PHS → M) (E : List (Set M)) :
    (initialWeightedRecord PHS f E).ideal =
      vanishingIdeal (n := 2) ((Subtype.val : presentationOpen PHS → ComplexModel 2) ⁻¹' D) := by
  let U := presentationOpen PHS
  let Vtx := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal 2 I)
  let c := PHS.representatives
  have hFamily : (fun i : Vtx => fun z : U => c i z.val ^
      (weightedCommonMark (fun i : Vtx => normalExponentDegree i.val) / normalExponentDegree i.val)) =
      fun i (z : U) => c i z.val := by
    funext i z
    rw [hMark,hWeight i]
    norm_num
  ext x g
  change IsInSpanAt (n := 2) (· ∈ range (fun i (z : U) => c i z.val ^
      (weightedCommonMark (fun i : Vtx => normalExponentDegree i.val) / normalExponentDegree i.val))) x g ↔ _
  rw [hFamily, vanishingIdeal_opens_mem_iff U, ← hB,
    PHS.wholeGeneration x.val x.property, model_span_iff]
  have hR : (· ∈ range (fun i (z : U) => c i z.val)) =
      (fun s' : U → ℂ => ∃ s, s ∈ range c ∧ s' = s ∘ Subtype.val) := by
    funext s
    apply propext
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨c i,⟨i,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [hR]
  exact isInSpanAt_comp_val_iff U

/-- The actual finite weighted-function initial record for the crossing has
native mark two and exponent one on its literal ordered boundary. -/
theorem exists_crossing_initial_ratio_in_centered_chart
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel 2) origin origin))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel 2) origin).target)
    (hΘ : Θ.toFun (chartAt (ComplexModel 2) origin origin) = 0) :
    ∃ (X : CMfd.{0} 2) (ι : X → M) (Q : MarkedIdeal 2 X) (x : X),
      IsOpenHoloEmbedding 2 ι ∧ ι x = origin ∧ IsInvDomain 2 Q ∧
      Q.N = univ ∧ Q.E = [ι ⁻¹' axis 0] ∧
      Q.ideal = vanishingIdeal (n := 2) (ι ⁻¹' crossing) ∧
      x ∈ Q.cosupp ∧ Q.d = 2 ∧
      divExpAlong 2 Q.N Q.ideal (ι ⁻¹' axis 0) x = 1 := by
  obtain ⟨Ψ,hΨ,hsrc,h0,G,S,PHS,_,_,_,_,_,_,hPHS,_,V,η,hV,hη,_,hDom,_,_,hx,_⟩ :=
    exists_original_initial_hs_phase crossing crossing_analytic origin crossing_origin_singular
      [axis 0] axis_zero_ordered_snc Θ hΘsrc hΘ
  let U := presentationOpen PHS
  let X := CMfd.of (n := 2) U
  let ι : X → M := fun z => (η z : M)
  let Q : MarkedIdeal 2 X := initialWeightedRecord PHS ι [axis 0]
  let x : X := ⟨0,PHS.zero_mem⟩
  let Ξ := currentCoordinateFlattening origin Θ hΘ Ψ hΨ
  let C := actualFixedFlatteningSet origin Ξ crossing
  let B := vanishingIdeal (n := 2) C
  have hi : originalCoherentOriginIdeal B =
      adaptedIdeal (vanishingIdeal (n := 2) crossing) origin Ξ h0 := by
    exact (originalFlattenedVanishingOriginIdeal_eq_model origin Ξ hsrc h0 crossing).symm.trans
      (actual_original_translated_flattened_vanishing_origin_eq_adapted origin Ξ hsrc h0
        crossing (CartanIrreducible.cartanCoherence crossing crossing_analytic))
  have hMark := crossing_adapted_canonical_mark_two Ξ h0
  dsimp only at hMark
  rw [← hi] at hMark
  have hxι : ι x = origin := (hη x).trans (actualFlatteningInverseMap_zero origin Ξ h0)
  have hCarrier : ((Subtype.val : U → ComplexModel 2) ⁻¹' C) = ι ⁻¹' crossing := by
    ext y
    change (y.val ∈ Ξ.target ∧ actualFlatteningInverseMap origin Ξ y.val ∈ crossing) ↔ (η y : M) ∈ crossing
    rw [hη y]
    exact and_iff_right (hPHS y.property)
  have hIdeal : Q.ideal = vanishingIdeal (n := 2) (ι ⁻¹' crossing) := by
    exact (pulled_initial_ideal_eq PHS hMark.1 hMark.2 rfl ι [axis 0]).trans
      (congrArg (vanishingIdeal (n := 2)) hCarrier)
  have hExpo : divExpAlong 2 univ (vanishingIdeal (n := 2) (ι ⁻¹' crossing)) (ι ⁻¹' axis 0) x =
      divExpAlong 2 univ (vanishingIdeal (n := 2) crossing) (axis 0) (ι x) := by
    let J := vanishingIdeal (n := 2) crossing
    let JV := GermIdeal.pullback (m := 2) (Subtype.val : V → M) J
    have hJV : JV = vanishingIdeal (n := 2) ((Subtype.val : V → M) ⁻¹' crossing) :=
      pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val V) crossing
    have hJη : GermIdeal.pullback (m := 2) η JV =
        vanishingIdeal (n := 2) (ι ⁻¹' crossing) := by
      rw [hJV,pullback_vanishingIdeal_of_biholomorphism]
      rfl
    have hJVhol : ∀ y F, JV.mem y F → HolomorphicAt 2 F y := by
      rw [hJV]
      exact fun _ _ hh => hh.1
    have hexpι := MonomialInvariantFunctorialAlong.divExpAlong_pullback
      (N := (univ : Set M)) (𝔞 := J) (φ := (Subtype.val : V → M)) (x' := η x)
      (fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨univ,[],J,e⟩ : MarkedIdeal 2 M)
        (fun _ _ hh => hh.1) V)
      (V.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (η x)) (axis 0)
    have hexpη := MonomialInvariantFunctorialAlong.divExpAlong_pullback
      (N := (univ : Set V)) (𝔞 := JV) (φ := (η : U → V)) (x' := x)
      (fun e => MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
        η.apply_symm_apply η.symm_apply_apply (⟨univ,[],JV,e⟩ : MarkedIdeal 2 V) hJVhol)
      (η.toHomeomorph.map_nhds_eq x) ((Subtype.val : V → M) ⁻¹' axis 0)
    have hComp := (show _ = divExpAlong 2 univ JV ((Subtype.val : V → M) ⁻¹' axis 0) (η x) from hexpη).trans
      (show divExpAlong 2 univ JV ((Subtype.val : V → M) ⁻¹' axis 0) (η x) = _ from hexpι)
    rw [preimage_univ,hJη] at hComp
    exact hComp
  refine ⟨X,ι,Q,x,⟨V,η,fun _ => rfl⟩,hxι,hDom,rfl,rfl,hIdeal,hx,hMark.1,?_⟩
  change divExpAlong 2 univ Q.ideal (ι ⁻¹' axis 0) x = 1
  rw [hIdeal,hExpo,hxι,crossing_axis_exponent_one]

/-- Actual initial records from independent choices identify as whole marked
records on any common chart over the original crossing. This includes the
ordered boundary and the entire coherent ideal. -/
theorem crossing_initial_common_window_eq
    {X Y Z : CMfd.{0} 2} {i : X → M} {j : Y → M}
    {P : MarkedIdeal 2 X} {Q : MarkedIdeal 2 Y}
    (b : Z → X) (c : Z → Y)
    (hb : IsOpenHoloEmbedding 2 b) (hc : IsOpenHoloEmbedding 2 c)
    (hSame : i ∘ b = j ∘ c)
    (hPN : P.N = univ) (hQN : Q.N = univ)
    (hPE : P.E = [i ⁻¹' axis 0]) (hQE : Q.E = [j ⁻¹' axis 0])
    (hPI : P.ideal = vanishingIdeal (n := 2) (i ⁻¹' crossing))
    (hQI : Q.ideal = vanishingIdeal (n := 2) (j ⁻¹' crossing))
    (hPd : P.d = 2) (hQd : Q.d = 2) :
    MarkedIdealBiholomorphism.MarkedIdeal.pullback b P = MarkedIdealBiholomorphism.MarkedIdeal.pullback c Q := by
  simp only [MarkedIdealBiholomorphism.MarkedIdeal.pullback, hPN, hQN, hPE, hQE, hPI, hQI, hPd, hQd,
    preimage_univ, List.map_cons, List.map_nil,
    pullback_vanishingIdeal_of_isOpenHoloEmbedding b hb,
    pullback_vanishingIdeal_of_isOpenHoloEmbedding c hc, ← preimage_comp, hSame]

/-- Independent centered source charts give independently constructed initial
records. On every common actual chart over the original germ, the records
give equal recursive values along every common tower. -/
theorem exists_independent_crossing_initial_history_comparison
    (Θ Λ : LocalHolomorphicEquivAt (chartAt (ComplexModel 2) origin origin))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel 2) origin).target)
    (hΛsrc : Λ.source ⊆ (chartAt (ComplexModel 2) origin).target)
    (hΘ : Θ.toFun (chartAt (ComplexModel 2) origin origin) = 0)
    (hΛ : Λ.toFun (chartAt (ComplexModel 2) origin origin) = 0) :
    ∃ (X Y : CMfd.{0} 2) (i : X → M) (j : Y → M) (x : X) (y : Y)
        (P : MarkedIdeal 2 X) (Q : MarkedIdeal 2 Y),
      IsOpenHoloEmbedding 2 i ∧ IsOpenHoloEmbedding 2 j ∧ i x = origin ∧ j y = origin ∧
      IsInvDomain 2 P ∧ IsInvDomain 2 Q ∧ x ∈ P.cosupp ∧ y ∈ Q.cosupp ∧
      P.E = [i ⁻¹' axis 0] ∧ Q.E = [j ⁻¹' axis 0] ∧ P.d = 2 ∧ Q.d = 2 ∧
      divExpAlong 2 P.N P.ideal (i ⁻¹' axis 0) x = 1 ∧
      divExpAlong 2 Q.N Q.ideal (j ⁻¹' axis 0) y = 1 ∧
      ∀ {Z A : CMfd.{0} 2} (b : Z → X) (c : Z → Y),
        IsOpenHoloEmbedding 2 b → IsOpenHoloEmbedding 2 c → i ∘ b = j ∘ c →
        ∀ T : BlowupTower Z A,
          let L := MarkedIdealBiholomorphism.MarkedIdeal.pullback b P
          let R := MarkedIdealBiholomorphism.MarkedIdeal.pullback c Q
          let I := CanonicalCentres.canonicalInvariant 2
          L = R ∧
          (IsCanonical L (I.inv L) T ↔
            IsCanonical R (I.inv R) T) ∧
          I.inv L T = I.inv R T := by
  obtain ⟨X,i,P,x,hi,hix,hPD,hPN,hPE,hPI,hx,hPd,hPx⟩ :=
    exists_crossing_initial_ratio_in_centered_chart Θ hΘsrc hΘ
  obtain ⟨Y,j,Q,y,hj,hjy,hQD,hQN,hQE,hQI,hy,hQd,hQy⟩ :=
    exists_crossing_initial_ratio_in_centered_chart Λ hΛsrc hΛ
  refine ⟨X,Y,i,j,x,y,P,Q,hi,hj,hix,hjy,hPD,hQD,hx,hy,hPE,hQE,hPd,hQd,hPx,hQy,?_⟩
  intro Z A b c hb hc hSame T L R I
  have h : L = R := crossing_initial_common_window_eq b c hb hc hSame
    hPN hQN hPE hQE hPI hQI hPd hQd
  exact ⟨h, by rw [h], by rw [h]⟩

#print axioms exists_crossing_initial_ratio_in_centered_chart
#print axioms crossing_initial_common_window_eq
#print axioms exists_independent_crossing_initial_history_comparison

end
end Hironaka.HironakaG1IndependentInitialCrossing
