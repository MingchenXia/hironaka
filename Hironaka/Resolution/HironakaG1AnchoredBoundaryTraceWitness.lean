import Hironaka.Resolution.HironakaActualHistoricalOriginalNativePhase
import Hironaka.Resolution.HironakaG1NativeBoundaryTrace

/-! Realization of an escaping analytic boundary trace by the actual anchored initial record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1AnchoredBoundaryTraceWitness
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec NormalCrossings DivisorExponent DivisorExponentAlong
  GermIdealOrder FactorizationFromResolution HironakaEmbeddedAnalytic HironakaG11PresTowerState
  HironakaActualHistoricalOriginalNativePhase HironakaActualHistoricalNativeFunctionTower
  HironakaActualHistoricalNativeFunctionSuccessor HironakaActualNativeBornWeightedExponents
  HironakaActualPrescribedCentreRebasing HironakaActualFixedFlatteningHSComparison
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression HironakaHolomorphicJetChartInvariance
  HironakaActualVanishingIntrinsicHSTransport HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaActualHistoricalNativeStageStep HironakaSmoothCentreCoherentDomain
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision

variable {n : ℕ} {M : CMfd.{0} n}

/-- Original analytic and HS geometry suffice to realize a strictly positive
submark exponent in the anchored initial weighted record on a genuine open. -/
theorem exists_anchored_submark_boundary
    (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W) (a : M)
    (ha : a ∈ singularSet (n := n) W)
    (E : List (Set M)) (hE : IsSNCDivisor n E) (i : Fin E.length) (hi : a ∈ E.get i)
    (hIn : ∀ᶠ y in 𝓝 a, y ∈ E.get i → y ∈ W)
    (hEscape : ∃ᶠ y in 𝓝 a, y ∈ E.get i ∧
      ∃ q, hilbertSamuelAt (vanishingIdeal (n := n) W) y q ≠
        hilbertSamuelAt (vanishingIdeal (n := n) W) a q)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hSrc : Φ.source ⊆ (chartAt (ComplexModel n) a).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) a a) = 0) :
    ∃ (X : CMfd.{0} n) (ι : X → M) (Q : MarkedIdeal n X) (x : X),
      Topology.IsOpenEmbedding ι ∧ ι x = a ∧ IsInvDomain n Q ∧ Q.N = univ ∧
      Q.E = E.map (ι ⁻¹' ·) ∧ x ∈ Q.cosupp ∧
      0 < divExpAlong n Q.N Q.ideal (ι ⁻¹' E.get i) x ∧
      divExpAlong n Q.N Q.ideal (ι ⁻¹' E.get i) x < Q.d ∧
      (∀ᶠ y in 𝓝 x, y ∈ ι ⁻¹' E.get i → y ∈ ι ⁻¹' W) ∧
      (∃ᶠ y in 𝓝 x, y ∈ ι ⁻¹' E.get i ∧ y ∉ Q.cosupp) ∧
      ∃ (Vtx : Finset (Fin n →₀ ℕ)) (S : ActualFixedInheritedSelector Vtx)
        (k : ℕ) (a : Fin k ≃ Vtx) (w : Fin k → CoordinateWord n),
        ActualHistoricalNativePointPresentation S a w (ι ⁻¹' W) Q x := by
  obtain ⟨Ψ,hΨ,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,_,
    _,hMap,hOpen,haImage,hDom,hN,hBoundaries,hMark,hWphase,hCut,_,_,hTower,_⟩ :=
    exists_actual_original_native_anchored_hs_phase W hW a ha E hE Φ hSrc h0
  let X := CMfd.of (n := n) O
  let ι : X → M := fun x => (η x.val : M)
  let Q : MarkedIdeal n X := MarkedIdealBiholomorphism.MarkedIdeal.pullback
    (Subtype.val : O → presentationOpen PHS) (initialWeightedRecord PHS (fun z => (η z : M)) E)
  let D : Set X := ι ⁻¹' W
  let Ξ := currentCoordinateFlattening a Φ h0 Ψ hΨ
  have hDphase : ((Subtype.val : O → presentationOpen PHS) ⁻¹'
      ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W)) = D := by
    ext z
    change (z.val.val ∈ Ξ.target ∧ actualFlatteningInverseMap a Ξ z.val.val ∈ W) ↔ (η z.val : M) ∈ W
    rw [hη z.val]
    exact and_iff_right (hPHS z.val.property)
  dsimp only [Ξ] at hDphase
  rw [hDphase] at hWphase hCut hTower
  obtain ⟨x,hx⟩ := haImage
  change ι x = a at hx
  have hsAt : ∀ y q, hilbertSamuelAt (vanishingIdeal (n := n) D) y q =
      hilbertSamuelAt (vanishingIdeal (n := n) W) (ι y) q := by
    intro y q
    have hO' := hilbertSamuelAt_vanishing_actual_open_any (n := n) O
      ((fun z : presentationOpen PHS => (η z : M)) ⁻¹' W) y q
    have hB := hilbertSamuelAt_vanishing_actual_biholomorphic_any (n := n) η
      ((Subtype.val : V → M) ⁻¹' W) y.val q
    have hV := hilbertSamuelAt_vanishing_actual_open_any (n := n) V W (η y.val) q
    exact hO'.trans (hB.trans hV)
  have hxQ : x ∈ Q.cosupp := by
    rw [hCut]
    intro q
    rw [hsAt, hx]
  have hIn' : ∀ᶠ y in 𝓝 x, y ∈ ι ⁻¹' E.get i → y ∈ D := by
    rw [← hx, ← hOpen.map_nhds_eq] at hIn
    exact hIn
  have hEsc' : ∃ᶠ y in 𝓝 x, y ∈ ι ⁻¹' E.get i ∧ y ∉ Q.cosupp := by
    rw [← hx, ← hOpen.map_nhds_eq] at hEscape
    refine Filter.Frequently.mono hEscape ?_
    rintro y ⟨hy,q,hq⟩
    refine ⟨hy,?_⟩
    intro hyQ
    rw [hx] at hq
    apply hq
    rw [hCut] at hyQ
    exact (hsAt y q).symm.trans (hyQ q)
  have hWclosed := hWphase.isClosed
  have hTest : IsGeoTestTower Q (.refl : BlowupTower X X) := by trivial
  have hAtF := (hTower X (.refl : BlowupTower X X) hTest).1 x
  rw [geoTransformAlong_refl] at hAtF
  obtain ⟨Θ,hΘsrc,hΘ0,Γ,den,hFive,hWhole,hComp,_,_⟩ := hAtF hxQ
  rw [BlowupTower.proj_refl, strictTransform_id hWclosed] at hWhole
  have hAt : ActualHistoricalNativePointPresentation S _ _ D Q x :=
    ⟨Θ,hΘsrc,hΘ0,Γ,hFive,hWhole,hComp⟩
  let I := originalCoherentOriginIdeal
    (vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W))
  let vertices := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
  have hPos (v : vertices) : 0 < normalExponentDegree v.val := by
    have hD := hDom.one_le_d
    change 1 ≤ Q.d at hD
    rw [hMark] at hD
    change 1 ≤ weightedCommonMark (fun a : vertices => normalExponentDegree a.val) at hD
    by_contra hn
    have hd : normalExponentDegree v.val = 0 := by omega
    have hz : weightedCommonMark (fun a : vertices => normalExponentDegree a.val) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hd
    rw [hz] at hD
    omega
  obtain ⟨_,_,_,_,hReflect,_⟩ := actual_native_point_reduced_stalk_dictionary
    S _ _ hPos D hWphase Q hDom.isWellFormed.isCoherent x hAt
  change Q.E = E.map (ι ⁻¹' ·) at hBoundaries
  let j : Fin Q.E.length := ⟨i.val, by rw [hBoundaries,List.length_map]; exact i.isLt⟩
  have hSlot : Q.E.get j = ι ⁻¹' E.get i := by
    simp only [List.get_eq_getElem]
    rw [getElem_congr hBoundaries rfl j.isLt, List.getElem_map]
  have hxH : x ∈ Q.E.get j := by
    rw [hSlot]
    change ι x ∈ E.get i
    rwa [hx]
  obtain ⟨b,hb⟩ := (snc_member_codimOne_geometry hDom.isWellFormed.isSNCDivisor j).1.2 x hxH
  have hIH := DivisorMetric.isCoherent_of_isInvertible
    (isInvertible_vanishingIdeal_snc_member hDom.isWellFormed.isSNCDivisor j)
  have hJcoh := CartanIrreducible.cartanCoherence D hWphase
  have hDivJ : IsDivNear n (vanishingIdeal (n := n) D) (Q.E.get j) 1 x := by
    have hHol : ∀ y G, (vanishingIdeal (n := n) D).mem y G → HolomorphicAt n G y :=
      fun _ _ h => h.1
    unfold IsDivNear
    rw [cosupport_one hHol, univ_inter,
      BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hWclosed, hSlot]
    exact hIn'
  have hDivQ : IsDivNear n Q.ideal (Q.E.get j) 1 x := by
    rw [isDivNear_iff hDom.isWellFormed.isCoherent hb, idealPow_one_of_isCoherent hIH]
    apply (hReflect (Q.E.get j) hIH).mpr
    have hJ := (isDivNear_iff hJcoh hb).mp hDivJ
    rwa [idealPow_one_of_isCoherent hIH] at hJ
  have hxN := Q.cosupp_subset_N hxQ
  have hDiv (e : ℕ) := isDivNearAlong_get_iff_le hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent j hxN hxH (hDom.isNonzeroAlongAt x hxN) (e := e)
  have hPosExp := (hDiv 1).mp (by rwa [hN, isDivNearAlong_univ_iff])
  have hBelow : divExpAlong n Q.N Q.ideal (Q.E.get j) x < Q.d := by
    by_contra! hle
    have ht := (hDiv Q.d).mpr hle
    have he : ∀ᶠ y in 𝓝 x, y ∈ ι ⁻¹' E.get i → y ∈ Q.cosupp := by
      rw [← hSlot]
      exact Filter.Eventually.mono ht (fun _ h hy => h (hN.symm ▸ mem_univ _) hy)
    obtain ⟨z,hz,hz'⟩ := (hEsc'.and_eventually he).exists
    exact hz.2 (hz' hz.1)
  exact ⟨X,ι,Q,x,hOpen,hx,hDom,hN,hBoundaries,hxQ,hSlot ▸ hPosExp,hSlot ▸ hBelow,
    hIn',hEsc',⟨_,S,_,_,_,hAt⟩⟩

#print axioms exists_anchored_submark_boundary

end
end Hironaka.HironakaG1AnchoredBoundaryTraceWitness
