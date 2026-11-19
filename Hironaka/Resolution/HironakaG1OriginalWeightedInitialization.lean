import Hironaka.Resolution.HironakaG1DenseOldDivisorFactor
import Hironaka.Resolution.HironakaActualOriginalInitialHSPhase
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaActualInitialNonmonomialCoefficientBoundary

/-! Boundary-dense initialization of the SAME actual original weighted PHS record.
Blueprint FIRST: hironaka-g1-original-weighted-initialization.tex.
No marking-one/weighted phase equivalence or raw invariant equality is asserted. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1OriginalWeightedInitialization
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  IdealWeightPowers IdealOrderArithmetic GermIdealOrder DivisorExponent DivisorExponentAlong
  NormalCrossings HironakaG1DenseOldDivisorFactor HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealOperationsAlong HomogenizedIdealAlong CoefficientIdealRestriction StepOneValue
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec CanonicalCentres ResolutionDriver
  HironakaG8HomStable HironakaG11InvBMClass HironakaG1OriginalUnequalMarkCanonical
  HironakaActualInitialNonmonomialCoefficientBoundary
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualOriginalInitialHSPhase
  HironakaActualAnalyticAdaptedCurrentFamily HironakaActualNormalZeroAnalyticSaturation
  HironakaActualRelativeNormalGeometry HironakaRelativeNormalCoherentSaturation
  HironakaActualFixedFlatteningHSComparison HironakaActualInheritedNestedContactFlag
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalMonomialBasis
  HironakaActualCauchyCoefficientLimits HironakaActualInheritedNeighborhoodMarkedHS
  HironakaActualRelativeNormalJetDivision MarkedIdealRestrictOpen
  HironakaActualHistoricalHSMarkedDomain HironakaActualFormalInitialDiagram

variable {n : ℕ}

section Presentation
variable {W₀ : Set (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

/-- Literal PHS representatives are holomorphic only on their genuine native open. -/
theorem presentation_functions_holomorphic
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W₀) I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen P=>P.representatives i z.val) := by
  intro z
  have hh:=DivisorExponent.holomorphicAt_of_mdifferentiableOn_open P.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (P.holomorphicOn i)) z.property
  exact (hh.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U:=presentationOpen P)).contMDiffAt)).mdifferentiableAt

/-- The existing whole PHS field gives ENTIRE native generators without a new witness packet. -/
theorem presentation_vanishing_generators
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W₀) I G R)
    (z : presentationOpen P) (F : presentationOpen P→ℂ) :
    (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen P→ComplexModel n) ⁻¹' W₀)).mem z F↔
      IsInSpanAt (n:=n) (·∈range fun i (y : presentationOpen P)=>P.representatives i y.val) z F := by
  let U:=presentationOpen P
  let ι:=actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)
  let e:=Fintype.equivFin ι
  constructor
  · intro hF
    have hFa:=(BlowupRestrictOpen.vanishingIdeal_opens_mem_iff U).mp hF
    obtain ⟨_hh,a,ha,he⟩:=(P.wholeGeneration z.val z.property _).mp hFa
    refine ⟨hF.1,Fintype.card ι,
      (fun j y=>P.representatives (e.symm j) y.val),
      (fun j y=>a (e.symm j) y.val),fun j=>⟨e.symm j,rfl⟩,?_,?_⟩
    · intro j
      apply (holomorphicAt_comp_val_iff U).mpr
      simpa only [OkaRelationSheaf.HolAt,HolomorphicAt,mdifferentiableAt_iff_differentiableAt] using ha (e.symm j)
    · have he' := (eventually_nhds_val_iff U).mp he
      filter_upwards [he'] with y hy
      rw [←extendOpens_val U F y,hy]
      exact (Equiv.sum_comp e.symm (fun i=>a i y.val*P.representatives i y.val)).symm
  · intro hF
    apply BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt' ?_ hF
    rintro F₀ ⟨i,rfl⟩
    apply BlowupRestrictOpen.vanishingIdeal_opens_mem_comp_val U
    apply (P.wholeGeneration z.val z.property _).mpr
    exact OkaIdealOperations.inSpanAt_self (fun j=>P.holomorphicAt z.val z.property j) i

end Presentation

/-- Density is inherited on the SAME actual selector/PHS window. -/
theorem boundary_density_actual_window {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (W : Set M) (E : List (Set M)) (hDense : W⊆closure (W\⋃H∈E,H))
    (a : M) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (U : Opens (ComplexModel n)) (hU : (U : Set (ComplexModel n))⊆Ξ.target)
    (V : Opens M) (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hη : ∀z,(η z : M)=actualFlatteningInverseMap a Ξ z.val) :
    ((Subtype.val : U→ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W)⊆
      closure (((Subtype.val : U→ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W)\
        ⋃H∈E.map ((fun z : U=>(η z : M)) ⁻¹' ·),H) := by
  let b : U→M:=fun z=>(η z : M)
  have hSet : (Subtype.val : U→ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W=b ⁻¹' W := by
    ext z
    change (z.val∈Ξ.target∧actualFlatteningInverseMap a Ξ z.val∈W)↔b z∈W
    rw [←hη z]
    exact and_iff_right (hU z.property)
  have hbo : IsOpenMap b:=V.isOpen.isOpenMap_subtype_val.comp η.toHomeomorph.isOpenMap
  have hbc : Continuous b:=continuous_subtype_val.comp η.contMDiff.continuous
  rw [hSet]
  intro z hz
  have hh:=preimage_mono (f:=b) hDense hz
  rw [hbo.preimage_closure_eq_closure_preimage hbc,preimage_sdiff,
    HironakaEmbeddedBoundary.preimage_biUnion_list b E] at hh
  exact hh

section Weighted
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {ι : Type*} [Fintype ι] {k : ℕ}

/-- The TRUE weighted record and TRUE bar both have zero old exponents, internally. -/
theorem weighted_and_bar_exponents_zero
    (W : Set X) (E : List (Set X)) (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→X→ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (hgen : ∀x F,(vanishingIdeal (n:=n) W).mem x F↔IsInSpanAt (n:=n) (·∈range c) x F)
    (hDense : W⊆closure (W\⋃H∈E,H))
    (hQ : IsInvDomain k (⟨univ,E,weightedFunctionIdeal w c,weightedCommonMark w⟩ : MarkedIdeal n X))
    (H : Set X) (hH : H∈E) (x : X) :
    let Q : MarkedIdeal n X:=⟨univ,E,weightedFunctionIdeal w c,weightedCommonMark w⟩
    divExpAlong n Q.N Q.ideal H x=0 ∧
      divExpAlong n (barMarked (X:=CMfd.of (n:=n) X) Q).N
        (barMarked (X:=CMfd.of (n:=n) X) Q).ideal H x=0 := by
  let Q : MarkedIdeal n X:=⟨univ,E,weightedFunctionIdeal w c,weightedCommonMark w⟩
  let B:=barMarked (X:=CMfd.of (n:=n) X) Q
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked (X:=CMfd.of (n:=n) X) Q hQ
  refine ⟨weighted_divExpAlong_eq_zero_of_dense W E w hw c hc hgen hDense hQ H hH x,?_⟩
  change divExpAlong n univ B.ideal H x=0
  rw [divExpAlong_univ]
  let e:=CoefficientIdeal.sumExp (fun j=>Q.d-j) Q.d 0
  have he : 0<e := CoefficientIdeal.one_le_sumExp (by intro j hj; omega) 0
  have hPow (j : ι) (y : X) : B.ideal.mem y (fun z=>c j z^((weightedCommonMark w/w j)*e)) := by
    have hh : HolomorphicAt n (fun z=>c j z^(weightedCommonMark w/w j)) y:=
      Eventually.of_forall ((hc j).pow _)
    have hm : Q.ideal.mem y (fun z=>c j z^(weightedCommonMark w/w j)):=
      isInSpanAt_self ⟨j,rfl⟩ hh
    have hhom : (homMarkedAlong Q).ideal.mem y (fun z=>c j z^(weightedCommonMark w/w j)):=
      le_homogenizedIdealAlong (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem
        hQ.isWellFormed.isCoherent hg) hQ.one_le_d y _ hm
    have hp:=zerothPower_le_coefficient (X:=CMfd.of (n:=n) X) (homMarkedAlong Q) hQ.one_le_d
      y _ (HomogenizedIdeal.pow_mem_idealPow hhom hh e)
    simpa only [←pow_mul] using hp
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hH
  subst H
  have hE:=hQ.isWellFormed.isSNCDivisor
  have hD : W⊆closure (W\E.get i) := by
    apply hDense.trans (closure_mono ?_)
    rintro y ⟨hyW,hyE⟩
    exact ⟨hyW,fun hyH=>hyE (mem_iUnion.mpr ⟨E.get i,
      mem_iUnion.mpr ⟨List.get_mem _ _,hyH⟩⟩)⟩
  by_cases hx : x∈E.get i
  · have hnot:=not_isDivNear_of_generator_powers_dense W E hE c hc hgen B.ideal
      hB.isWellFormed.isCoherent (fun j=>(weightedCommonMark w/w j)*e)
      (fun j=>Nat.mul_pos (compressionExponent_pos w hw j) he) hPow i hD x hx
      (vanishing_nonzero_of_weighted_domain W E w hw c hc hgen hQ x)
    by_contra hne
    exact hnot ((isDivNear_divExp (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem
      hB.isWellFormed.isCoherent hg) x).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hnone : ¬∃e,¬IsDivNear n B.ideal (E.get i) (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem (hE.1 _ (List.get_mem _ _)) hx (e+1))
    simp only [divExp,dif_neg hnone]

end Weighted

section Original
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

/-- BOTH entire old exponent families of the EXISTING original initialWeightedRecord. -/
theorem initialWeightedRecord_exponents_zero {k : ℕ}
    (W : Set M) (E : List (Set M)) (hDense : W⊆closure (W\⋃H∈E,H))
    (a : M) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (P : ActualGeometricInheritedNeighborhoodHS
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet a Ξ W)) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    (hU : P.neighborhood⊆Ξ.target) (V : Opens M)
    (η : presentationOpen P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hη : ∀z,(η z : M)=actualFlatteningInverseMap a Ξ z.val)
    (hQ : IsInvDomain k (initialWeightedRecord P (fun z=>(η z : M)) E))
    (H : Set (presentationOpen P)) (hH : H∈(initialWeightedRecord P (fun z=>(η z : M)) E).E)
    (z : presentationOpen P) :
    let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
    divExpAlong n Q.N Q.ideal H z=0 ∧
      divExpAlong n (barMarked (X:=CMfd.of (n:=n) (presentationOpen P)) Q).N
        (barMarked (X:=CMfd.of (n:=n) (presentationOpen P)) Q).ideal H z=0 := by
  exact weighted_and_bar_exponents_zero (n:=n) (X:=presentationOpen P) (k:=k)
    (ι:=actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    ((Subtype.val : presentationOpen P→ComplexModel n) ⁻¹' actualFixedFlatteningSet a Ξ W)
    (E.map ((fun z=>(η z : M)) ⁻¹' ·)) (fun i=>normalExponentDegree i.val) hw
    (fun i (y : presentationOpen P)=>P.representatives i y.val)
    (presentation_functions_holomorphic P) (presentation_vanishing_generators P)
    (boundary_density_actual_window W E hDense a Ξ (presentationOpen P) hU V η hη) hQ H hH z

/-- Every genuine original family bound, retaining the SAME actual PHS and tower. -/
theorem initialWeightedRecord_invFamily_isCanonical_bar_iff {k : ℕ} (hn : 0<n)
    (W : Set M) (E : List (Set M)) (hDense : W⊆closure (W\⋃H∈E,H))
    (a : M) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (P : ActualGeometricInheritedNeighborhoodHS
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet a Ξ W)) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    (hU : P.neighborhood⊆Ξ.target) (V : Opens M)
    (η : presentationOpen P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hη : ∀z,(η z : M)=actualFlatteningInverseMap a Ξ z.val)
    (hQ : IsInvDomain k (initialWeightedRecord P (fun z=>(η z : M)) E))
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n:=n) (presentationOpen P)) Y) :
    let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
    IsCanonical Q ((invFamily hn k).inv Q) T↔
      IsCanonical (barMarked Q) ((invFamily hn k).inv (barMarked Q)) T := by
  let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
  let B:=barMarked (X:=CMfd.of (n:=n) (presentationOpen P)) Q
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ
  apply invFamily_isCanonical_iff_of_local (X:=CMfd.of (n:=n) (presentationOpen P)) hn Q B hQ hB
    (bar_local_any_boundary (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ)
    (SameCarrierDim.of_N_eq rfl) ?_ T
  intro H hH z _hz _hzH
  obtain ⟨h0,h1⟩:=initialWeightedRecord_exponents_zero W E hDense a Ξ P hw hU V η hη hQ H hH z
  rw [h0,h1,mul_zero,mul_zero]

/-- The SAME original weighted and bar histories are canonical on the SAME actual tower. -/
theorem initialWeightedRecord_isCanonical_bar_iff
    (W : Set M) (E : List (Set M)) (hDense : W⊆closure (W\⋃H∈E,H))
    (a : M) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (P : ActualGeometricInheritedNeighborhoodHS
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet a Ξ W)) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    (hU : P.neighborhood⊆Ξ.target) (V : Opens M)
    (η : presentationOpen P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hη : ∀z,(η z : M)=actualFlatteningInverseMap a Ξ z.val)
    (hQ : IsInvDomain n (initialWeightedRecord P (fun z=>(η z : M)) E))
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n:=n) (presentationOpen P)) Y) :
    let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
    IsCanonical Q ((canonicalInvariant n).inv Q) T↔
      IsCanonical (barMarked Q) ((canonicalInvariant n).inv (barMarked Q)) T := by
  let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
  let B:=barMarked (X:=CMfd.of (n:=n) (presentationOpen P)) Q
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ
  apply canonicalInvariant_isCanonical_iff_of_local (X:=CMfd.of (n:=n) (presentationOpen P)) Q B hQ hB
    (bar_local_any_boundary (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ)
    (SameCarrierDim.of_N_eq rfl) ?_ T
  intro H hH z _hz _hzH
  obtain ⟨h0,h1⟩:=initialWeightedRecord_exponents_zero W E hDense a Ξ P hw hU V η hη hQ H hH z
  rw [h0,h1,mul_zero,mul_zero]

/-- The ENTIRE true maximum centre, with bar CAN derived, at every SAME original prefix. -/
theorem initialWeightedRecord_maxLocus_bar
    (W : Set M) (E : List (Set M)) (hDense : W⊆closure (W\⋃H∈E,H))
    (a : M) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (P : ActualGeometricInheritedNeighborhoodHS
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet a Ξ W)) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    (hU : P.neighborhood⊆Ξ.target) (V : Opens M)
    (η : presentationOpen P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
    (hη : ∀z,(η z : M)=actualFlatteningInverseMap a Ξ z.val)
    (hQ : IsInvDomain n (initialWeightedRecord P (fun z=>(η z : M)) E))
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n:=n) (presentationOpen P)) Y)
    (hCan : IsCanonical (initialWeightedRecord P (fun z=>(η z : M)) E)
      ((canonicalInvariant n).inv (initialWeightedRecord P (fun z=>(η z : M)) E)) T) :
    let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
    maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=
      maxLocus ((canonicalInvariant n).inv (barMarked Q) T) (geoTransformAlong (barMarked Q) T).cosupp := by
  let Q:=initialWeightedRecord P (fun z=>(η z : M)) E
  let B:=barMarked (X:=CMfd.of (n:=n) (presentationOpen P)) Q
  have hB:=HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ
  have hL:=bar_local_any_boundary (X:=CMfd.of (n:=n) (presentationOpen P)) Q hQ
  have hDim : SameCarrierDim (X:=CMfd.of (n:=n) (presentationOpen P)) Q B:=SameCarrierDim.of_N_eq rfl
  have hExp : ∀H∈Q.E,∀z∈Q.cosupp,z∈H→
      B.d*divExpAlong n Q.N Q.ideal H z=Q.d*divExpAlong n B.N B.ideal H z := by
    intro H hH z _hz _hzH
    obtain ⟨h0,h1⟩:=initialWeightedRecord_exponents_zero W E hDense a Ξ P hw hU V η hη hQ H hH z
    rw [h0,h1,mul_zero,mul_zero]
  have hCanB:=(initialWeightedRecord_isCanonical_bar_iff W E hDense a Ξ P hw hU V η hη hQ T).mp hCan
  have hTest:=(canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  have hCos:=(hL.wEquiv.2 T).2 hTest
  have hCuts:=canonicalTwoPairCuts_canonicalInvariant n Q B Q B hQ hB hQ hB hL hDim hExp hL hDim hExp
    rfl rfl trivial trivial trivial trivial T T hCan hCanB hCan hCanB
  change maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=
    maxLocus ((canonicalInvariant n).inv B T) (geoTransformAlong B T).cosupp
  rw [←hCos]
  ext z
  constructor
  · rintro ⟨hz,hMax⟩
    refine ⟨hz,fun y hy=>?_⟩
    exact le_of_not_gt (fun h=>not_lt_of_ge (hMax y hy) ((hCuts z hz y hy).mpr h))
  · rintro ⟨hz,hMax⟩
    refine ⟨hz,fun y hy=>?_⟩
    exact le_of_not_gt (fun h=>not_lt_of_ge (hMax y hy) ((hCuts z hz y hy).mp h))

end Original

end
end Hironaka.HironakaG1OriginalWeightedInitialization
