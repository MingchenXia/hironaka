import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum
import Hironaka.Resolution.HironakaG1OriginalWeightedMaximalOrder
import Hironaka.Resolution.HironakaActualNativeSourceChartComposition

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalNativeInitialization

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan OrderTaylor DivisorExponentAlong GermIdealOrder
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaActualRelativeNormalJetDivision
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualOriginalInitialHSPhase HironakaActualGeometricCurrentNeighborhoodHS
  HironakaG1OriginalWeightedInitialization HironakaG1OriginalWeightedMaximalOrder
  HironakaG8InitialCommonIdealMaximum
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualInheritedNeighborhoodMarkedHS HironakaActualInheritedSmallTails
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticFormalNormalPowers HironakaActualCoefficientPresentationCentrePower
  HironakaActualHistoricalHSMarkedDomain HironakaRelativeNormalMonomialBasis
  HironakaEmbeddedAnalytic HironakaActualPrescribedCentreRebasing HironakaActualFixedFlatteningHSComparison
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreCoherentDomain
  HironakaActualSingularChartTransport HomogenizedIdealAlong BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen

/-- Principality in the initial centered chart gives the nonzero principal
origin ideal in every actual flattening used by the initial native phase. -/
theorem principal_origin_under_current_flattening
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (W : Set M) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : M) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a) = 0)
    (hPrincipal : ∃ g : HolGerm (ComplexModel n), g ≠ 0 ∧
      originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Φ W)) =
        Ideal.span {g})
    (Ψ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0 = 0) :
    let Ξ := currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
    ∃ g : HolGerm (ComplexModel n), g ≠ 0 ∧
      originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)) =
        Ideal.span {g} := by
  intro Ξ
  let D := HironakaEmbeddedExceptional.LocalHolomorphicEquivAt.symmAt Ψ hΨ0
  have hD0 : D.toFun 0 = 0 := local_invFun_zero Ψ hΨ0
  let I := vanishingIdeal (n := n) W
  have hI := CartanIrreducible.cartanCoherence W hW
  have hAdapt (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
      (hΘ : Θ.source ⊆ (chartAt (ComplexModel n) a).target)
      (hΘ0 : Θ.toFun (chartAt (ComplexModel n) a a) = 0) :
      originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Θ W)) =
        HironakaSmoothSubmersionGermIdealColon.adaptedIdeal I a Θ hΘ0 :=
    (originalFlattenedVanishingOriginIdeal_eq_model a Θ hΘ hΘ0 W).symm.trans
      (HironakaActualNativeSourceChartComposition.actual_original_translated_flattened_vanishing_origin_eq_adapted
        a Θ hΘ hΘ0 W hI)
  obtain ⟨g, hg, hSpan⟩ := hPrincipal
  have hMap := HironakaActualNativeSourceChartComposition.actual_native_source_chart_comp_ideal
    a Φ hsrc hΦ0 D hD0 I
  obtain ⟨hΞsrc, hΞ0⟩ := HironakaActualNativeSourceChartComposition.actual_native_source_chart_comp_geometry
    a Φ hsrc hΦ0 D hD0
  let e := (localGermAlgEquiv D hD0).symm
  refine ⟨e g, fun hz => hg (e.injective (hz.trans (map_zero e).symm)), ?_⟩
  calc
    originalCoherentOriginIdeal (vanishingIdeal (n := n) (actualFixedFlatteningSet a Ξ W)) =
        HironakaSmoothSubmersionGermIdealColon.adaptedIdeal I a
          (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0) hΞ0 :=
      hAdapt _ hΞsrc hΞ0
    _ = Ideal.map e.toRingEquiv.toRingHom
          (HironakaSmoothSubmersionGermIdealColon.adaptedIdeal I a Φ hΦ0) := hMap
    _ = Ideal.span {e g} := by
      rw [← hAdapt Φ hsrc hΦ0, hSpan, Ideal.map_span, Set.image_singleton]
      rfl

/-- A nonzero principal actual formal ideal has exactly one vertex. -/
theorem actualInitialVertices_span_singleton {n : ℕ} (m : MonomialOrder (Fin n))
    (f : MvPowerSeries (Fin n) ℂ) (hf : f ≠ 0) :
    actualInitialVertices m (Ideal.span {f}) = {actualInitialExponent m f hf} := by
  classical
  let a := actualInitialExponent m f hf
  let I : Ideal (MvPowerSeries (Fin n) ℂ) := Ideal.span {f}
  have ha : a ∈ actualInitialDiagram m I :=
    ⟨f, Ideal.subset_span (mem_singleton f), hf, rfl⟩
  have hle (b : Fin n →₀ ℕ) (hb : b ∈ actualInitialDiagram m I) : a ≤ b := by
    obtain ⟨g,hg,hg0,rfl⟩ := hb
    obtain ⟨k,hk⟩ := Ideal.mem_span_singleton.mp hg
    have hk0 : k ≠ 0 := by
      intro h
      exact hg0 (by simp [hk,h])
    have hExp : actualInitialExponent m g hg0 =
        actualInitialExponent m f hf + actualInitialExponent m k hk0 := by
      subst g
      exact actualInitialExponent_mul m f k hf hk0
    rw [hExp]
    exact le_self_add
  ext b
  simp only [actualInitialVertices,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,Finset.mem_singleton]
  constructor
  · intro hb
    exact le_antisymm (hb.le_of_le ha (hle b hb.prop)) (hle b hb.prop)
  · rintro rfl
    exact ⟨ha,fun _ hc _ => hle _ hc⟩

/-- A maximal-order whole record of the same ideal gives the mark-one
initial maximum whenever its cosupport is inhabited. -/
private theorem maximum_of_same_ideal_maximal_order
    {n : ℕ} {U : CMfd.{0} (n+1)} (J : GermIdeal (n+1) U)
    (Q : MarkedIdeal (n+1) U) (hN : Q.N = univ) (hE : Q.E = [])
    (hIdeal : Q.ideal = J) (hQ : IsInvDomain (n+1) Q) (hNonempty : Q.cosupp.Nonempty)
    (hBound : IsMaximalOrderAlong Q.N Q.ideal Q.d) :
    let A : MarkedIdeal (n+1) U := ⟨univ,[],J,1⟩
    IsInvDomain (n+1) A ∧
      maxLocus ((canonicalInvariant (n+1)).inv A .refl) A.cosupp =
        maxLocus ((canonicalInvariant (n+1)).inv Q .refl) Q.cosupp := by
  rcases Q with ⟨N,E,I,m⟩
  change N = univ at hN
  change E = [] at hE
  change I = J at hIdeal
  subst N E I
  let A : MarkedIdeal (n+1) U := ⟨univ,[],J,1⟩
  have hA : IsInvDomain (n+1) A :=
    ⟨⟨hQ.isWellFormed.isClosedSubmanifold_N,hQ.isWellFormed.isCoherent,
        hQ.isWellFormed.isSNCDivisor,hQ.isWellFormed.isTransverse⟩,
      hQ.dimLE,le_rfl,hQ.isNonzeroAlongAt⟩
  have hOrd (x : U) (d : ℕ) : x ∈ cosupport (n+1) univ J d ↔ d ≤ ordinaryTraceOrder univ J x :=
    ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      hA.isNonzeroAlongAt (mem_univ x) d
  have hUpper (x : U) : ordinaryTraceOrder univ J x ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge (mt (hOrd x (m+1)).mpr (hBound x)))
  obtain ⟨a,ha⟩ := hNonempty
  have hTop : ∃ x : U, ordinaryTraceOrder univ J x = m :=
    ⟨a,le_antisymm (hUpper a) ((hOrd a m).mp ha)⟩
  exact ⟨hA,initial_maxLocus_markOne_eq_topMark (X := U) J hA hQ.one_le_d hUpper hTop⟩

section Presentation

variable {n : ℕ} {W : Set (ComplexModel (n+1))}
  {I : Ideal (HolGerm (ComplexModel (n+1)))}
  {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
  {R : ℕ → ℕ}

/-- The actual boundary-free producer, at a nonzero principal adapted
origin ideal, retains the whole vanishing sheaf on its genuine PHS open. -/
theorem principal_initialWeightedRecord_ideal
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n := n+1) W) I G R)
    (g : HolGerm (ComplexModel (n+1))) (hg : g ≠ 0) (hI : I = Ideal.span {g})
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I),
      0 < normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P → M) :
    (initialWeightedRecord P η []).ideal =
      vanishingIdeal (n := n+1) ((Subtype.val : presentationOpen P → ComplexModel (n+1)) ⁻¹' W) := by
  classical
  let U := presentationOpen P
  let f := actualUnshiftedTaylorAlgHom (n+1) g
  have hf : f ≠ 0 := fun he => hg (actualUnshiftedTaylorAlgHom_injective (n+1)
    (he.trans (map_zero (actualUnshiftedTaylorAlgHom (n+1))).symm))
  have hTaylor : analyticZeroTaylorIdeal (n+1) I = Ideal.span {f} := by
    rw [hI,analyticZeroTaylorIdeal,Ideal.map_span]
    simp [f]
  have hVertices := actualInitialVertices_span_singleton MonomialOrder.degLex f hf
  rw [← hTaylor] at hVertices
  let J := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)
  let i : J := ⟨actualInitialExponent MonomialOrder.degLex f hf, by
    change actualInitialExponent MonomialOrder.degLex f hf ∈
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)
    rw [hVertices]; simp⟩
  have hUnique (j : J) : j = i := by
    apply Subtype.ext
    have hj := j.property
    change j.val ∈ actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I) at hj
    rw [hVertices,Finset.mem_singleton] at hj
    exact hj
  let _ : Subsingleton J := ⟨fun j k => (hUnique j).trans (hUnique k).symm⟩
  let w : J → ℕ := fun j => normalExponentDegree j.val
  let c : J → U → ℂ := fun j z => P.representatives j z.val
  have hRecord := singleton_weighted_initial_record (X := CMfd.of (n := n+1) U) i w (hw i) c
  have hIdeal :
      (initialWeightedRecord P η []).ideal = finiteFunctionIdeal (fun _ : Unit => c i) :=
    congrArg MarkedIdeal.ideal hRecord
  rw [hIdeal]
  have hRange : range (fun _ : Unit => c i) = range c := by
    ext F
    constructor
    · rintro ⟨_,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨j,rfl⟩
      exact ⟨(),congrArg c (hUnique j).symm⟩
  ext z F
  change IsInSpanAt (n := n+1) (· ∈ range (fun _ : Unit => c i)) z F ↔ _
  rw [hRange]
  exact (presentation_vanishing_generators P z F).symm

/-- For the actual principal PHS initialization the producer supplies both
the whole ideal and the ordinary order bound needed by the mark-one
transfer. No equality of sheaves or pointwise order bound is assumed. -/
theorem principal_initialWeightedRecord_markOne_maximum
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n := n+1) W) I G R)
    (g : HolGerm (ComplexModel (n+1))) (hg : g ≠ 0) (hI : I = Ideal.span {g})
    (hSpan : Ideal.span (range G.germs) = I) (hRef : ∀ ℓ, hilbertSamuelValue I ℓ = R ℓ)
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I),
      0 < normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P → M)
    (hQ : IsInvDomain (n+1) (initialWeightedRecord P η []))
    (hNonempty : (initialWeightedRecord P η []).cosupp.Nonempty) :
    let U := CMfd.of (n := n+1) (presentationOpen P)
    let W' := (Subtype.val : U → ComplexModel (n+1)) ⁻¹' W
    let A : MarkedIdeal (n+1) U := ⟨univ,[],vanishingIdeal (n := n+1) W',1⟩
    let Q : MarkedIdeal (n+1) U := initialWeightedRecord P η []
    IsInvDomain (n+1) A ∧
      maxLocus ((canonicalInvariant (n+1)).inv A .refl) A.cosupp =
        maxLocus ((canonicalInvariant (n+1)).inv Q .refl) Q.cosupp := by
  let U := CMfd.of (n := n+1) (presentationOpen P)
  let W' := (Subtype.val : U → ComplexModel (n+1)) ⁻¹' W
  let J := vanishingIdeal (n := n+1) W'
  let Q : MarkedIdeal (n+1) U := initialWeightedRecord P η []
  have hIdeal : Q.ideal = J := principal_initialWeightedRecord_ideal P g hg hI hw η
  have hBound : IsMaximalOrderAlong Q.N Q.ideal Q.d :=
    initialWeightedRecord_maximalOrder P hSpan hRef hw η [] hQ
  exact maximum_of_same_ideal_maximal_order (U := U) J Q rfl rfl hIdeal hQ hNonempty hBound

end Presentation

/-- An attained maximum on that genuine chart yields one actual singular
blowup, canonical for both the native record and the whole mark-one
record. The maximum equality is supplied by the principal initialization. -/
theorem exists_singular_blowup_of_initial_shared_maximum
    {n : ℕ} {X : CMfd.{0} (n+1)} (A Q : MarkedIdeal (n+1) X)
    (hQ : IsInvDomain (n+1) Q) (S : Set X) (hSing : Q.cosupp ⊆ S)
    (hMax : maxLocus ((canonicalInvariant (n+1)).inv A .refl) A.cosupp =
      maxLocus ((canonicalInvariant (n+1)).inv Q .refl) Q.cosupp)
    (hAttain : (maxLocus ((canonicalInvariant (n+1)).inv Q .refl) Q.cosupp).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{0} (n+1)) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π),
      C.Nonempty ∧ C ⊆ S ∧
      IsCanonical Q ((canonicalInvariant (n+1)).inv Q) (.step .refl C π hπ) ∧
      IsCanonical A ((canonicalInvariant (n+1)).inv A) (.step .refl C π hπ) := by
  let R := canonicalInvariant (n+1)
  let C := maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp
  have hAdm := R.isInvValue.isAdmissibleCentre_maxLocus hQ (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hAdm
  have hInt : interior C = ∅ := eq_empty_of_subset_empty
    ((interior_mono hAdm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hQ).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hAdm.1 hInt
  exact ⟨C,Y,π,hπ,hAttain,hAdm.2.1.trans hSing,⟨trivial,Or.inr rfl⟩,⟨trivial,Or.inr hMax.symm⟩⟩

/-- The native maximizer is attained after an actual open shrink about an
active point. If the native initial record is a whole maximal-order
vanishing ideal, the produced singular blowup is already mark-one
canonical on that same open. -/
theorem exists_local_singular_blowup_of_native_whole_initial
    {n : ℕ} {X : CMfd.{0} (n+1)} (W S : Set X)
    (Q : MarkedIdeal (n+1) X)
    (hN : Q.N = univ) (hE : Q.E = []) (hJ : Q.ideal = vanishingIdeal (n := n+1) W)
    (hQ : IsInvDomain (n+1) Q) (hBound : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (hSing : Q.cosupp ⊆ S) (a : X) (ha : a ∈ Q.cosupp) :
    ∃ (O : Opens X), a ∈ O ∧
      let Xo := CMfd.of (n := n+1) O
      let Qₒ := MarkedIdeal.pullback (Subtype.val : O → X) Q
      let A : MarkedIdeal (n+1) Xo :=
        ⟨univ,[],vanishingIdeal (n := n+1) ((Subtype.val : O → X) ⁻¹' W),1⟩
      ∃ (C : Set Xo) (Y : CMfd.{0} (n+1)) (π : Y → Xo) (hπ : IsBlowupAlong (n+1) C π),
        C.Nonempty ∧ C ⊆ (Subtype.val : O → X) ⁻¹' S ∧
        IsCanonical Qₒ ((canonicalInvariant (n+1)).inv Qₒ) (.step .refl C π hπ) ∧
        IsCanonical A ((canonicalInvariant (n+1)).inv A) (.step .refl C π hπ) := by
  let R := canonicalInvariant (n+1)
  have hUsc := R.isInvValue.usc Q hQ (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at hUsc
  obtain ⟨V,hV,hVo,haV⟩ := mem_nhds_iff.mp (hUsc a ha)
  let O : Opens X := ⟨V,hVo⟩
  refine ⟨O,haV,?_⟩
  let Xo := CMfd.of (n := n+1) O
  let Qₒ : MarkedIdeal (n+1) Xo := MarkedIdeal.pullback (Subtype.val : O → X) Q
  let J := vanishingIdeal (n := n+1) ((Subtype.val : O → X) ⁻¹' W)
  let A : MarkedIdeal (n+1) Xo := ⟨univ,[],J,1⟩
  have hQo := InvDomainTowerAlong.isInvDomain_pullback_val O hQ
  have hCos := cosupp_pullback_val Q
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg) O
  let aₒ : O := ⟨a,haV⟩
  have haₒ : aₒ ∈ Qₒ.cosupp := hCos.symm ▸ ha
  have hAttain : (maxLocus (R.inv Qₒ (.refl : BlowupTower Xo Xo)) Qₒ.cosupp).Nonempty := by
    refine ⟨aₒ,haₒ,fun y hy => ?_⟩
    have hy' : y ∈ (Subtype.val : O → X) ⁻¹' Q.cosupp := hCos ▸ hy
    have hv (x : O) (hx : x.val ∈ Q.cosupp) :
        R.inv Qₒ (.refl : BlowupTower Xo Xo) x = R.inv Q (.refl : BlowupTower X X) x.val :=
      R.isInvValue.restrictOpen Q hQ O (.refl : BlowupTower X X) trivial x hx
    rw [hv y hy',hv aₒ ha]
    exact hV y.property hy'
  have hNo : Qₒ.N = univ := by
    change (Subtype.val : O → X) ⁻¹' Q.N = univ
    rw [hN,preimage_univ]
  have hEo : Qₒ.E = [] := by
    change Q.E.map ((Subtype.val : O → X) ⁻¹' ·) = []
    rw [hE,List.map_nil]
  have hJo : Qₒ.ideal = J := by
    change GermIdeal.pullback (m := n+1) (Subtype.val : O → X) Q.ideal = J
    rw [hJ]
    exact congrArg MarkedIdeal.ideal
      (HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal O [] W)
  let Qhi : MarkedIdeal (n+1) X := { Q with d := Q.d+1 }
  have hCosHi := cosupp_pullback_val Qhi
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg) O
  have hBoundO : IsMaximalOrderAlong Qₒ.N Qₒ.ideal Qₒ.d := by
    intro x hx
    have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : O → X) Qhi).cosupp := hx
    have hx'' : x ∈ (Subtype.val : O → X) ⁻¹' Qhi.cosupp := hCosHi ▸ hx'
    exact hBound x.val hx''
  have hMax := maximum_of_same_ideal_maximal_order (U := Xo) J Qₒ hNo hEo hJo hQo
    ⟨aₒ,haₒ⟩ hBoundO
  have hSingO : Qₒ.cosupp ⊆ (Subtype.val : O → X) ⁻¹' S := by
    intro x hx
    have hx' : x ∈ (Subtype.val : O → X) ⁻¹' Q.cosupp := hCos ▸ hx
    exact hSing hx'
  exact exists_singular_blowup_of_initial_shared_maximum A Qₒ hQo _ hSingO hMax.2 hAttain

/-- The genuine singular-HS initialization at a principal adapted germ
produces a full PHS chart where the native and whole mark-one initial
maxima agree. Its attained HS reference and its singular support are
the ones returned by the existing provider. -/
theorem exists_principal_native_initial_maximum
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (n+1)) M]
    [IsComplexManifold (n+1) M]
    (W : Set M) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (a : M) (ha : a ∈ singularSet (n := n+1) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) a a))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (n+1)) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (n+1)) a a) = 0)
    (hPrincipal : ∀ (Ψ : LocalHolomorphicEquivAt (n := n+1) (0 : ComplexModel (n+1)))
      (hΨ0 : Ψ.toFun 0 = 0),
      let Ξ := currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
      ∃ g : HolGerm (ComplexModel (n+1)), g ≠ 0 ∧
        originalCoherentOriginIdeal (vanishingIdeal (n := n+1) (actualFixedFlatteningSet a Ξ W)) =
          Ideal.span {g}) :
    ∃ (U : Opens (ComplexModel (n+1))) (V : Opens M)
      (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯ V)
      (Q : MarkedIdeal (n+1) U) (z : U),
      (η z : M) = a ∧
      IsInvDomain (n+1) Q ∧ z ∈ Q.cosupp ∧
      Q.cosupp = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n+1) W) (η x : M) ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n+1) W) a ℓ} ∧
      Q.cosupp ⊆ (fun y : U => (η y : M)) ⁻¹' singularSet (n := n+1) W ∧
      let A : MarkedIdeal (n+1) U :=
        ⟨univ,[],vanishingIdeal (n := n+1) ((fun y : U => (η y : M)) ⁻¹' W),1⟩
      IsInvDomain (n+1) A ∧
      (maxLocus ((canonicalInvariant (n+1)).inv (X := CMfd.of (n := n+1) U) A .refl) A.cosupp =
        maxLocus ((canonicalInvariant (n+1)).inv (X := CMfd.of (n := n+1) U) Q .refl) Q.cosupp) ∧
      ∃ (O : Opens U), z ∈ O ∧
        let Xo := CMfd.of (n := n+1) O
        let Qₒ := MarkedIdeal.pullback (Subtype.val : O → U) Q
        let Aₒ : MarkedIdeal (n+1) Xo :=
          ⟨univ,[],vanishingIdeal (n := n+1) ((fun y : O => (η y.val : M)) ⁻¹' W),1⟩
        ∃ (C : Set Xo) (Y : CMfd.{0} (n+1)) (π : Y → Xo) (hπ : IsBlowupAlong (n+1) C π),
          C.Nonempty ∧ C ⊆ (fun y : O => (η y.val : M)) ⁻¹' singularSet (n := n+1) W ∧
          IsCanonical Qₒ ((canonicalInvariant (n+1)).inv Qₒ) (.step .refl C π hπ) ∧
          IsCanonical Aₒ ((canonicalInvariant (n+1)).inv Aₒ) (.step .refl C π hπ) := by
  obtain ⟨Ψ,hΨ0,_hΞsrc,hΞ0,G,S,P,hSpan,_hMem,hw,_hPrefix,_hContact,_hJac,hU,hRef,
    V,η,_haV,hη,_hCov,hDom,hCos,hSing,hZero,_hTerminal⟩ :=
    exists_original_initial_hs_phase W hW a ha [] NormalCrossings.isSNCDivisor_nil Φ hsrc hΦ0
  let Ξ := currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
  let W₀ := actualFixedFlatteningSet a Ξ W
  let U := presentationOpen P
  let z : U := ⟨0,P.zero_mem⟩
  let b : U → M := fun x => (η x : M)
  let Q : MarkedIdeal (n+1) U := initialWeightedRecord P b []
  obtain ⟨g,hg,hI⟩ := hPrincipal Ψ hΨ0
  have hz : b z = a := by
    change (η z : M) = a
    rw [hη]
    exact actualFlatteningInverseMap_zero a Ξ hΞ0
  have hSet : (Subtype.val : U → ComplexModel (n+1)) ⁻¹' W₀ = b ⁻¹' W := by
    ext x
    change (x.val ∈ Ξ.target ∧ actualFlatteningInverseMap a Ξ x.val ∈ W) ↔ (η x : M) ∈ W
    rw [hη]
    exact and_iff_right (hU x.property)
  have hMaximum := principal_initialWeightedRecord_markOne_maximum P g hg hI hSpan hRef hw b hDom
    ⟨z,hZero⟩
  dsimp only at hMaximum
  rw [hSet] at hMaximum
  have hIdeal : Q.ideal = vanishingIdeal (n := n+1) (b ⁻¹' W) := by
    rw [← hSet]
    exact principal_initialWeightedRecord_ideal P g hg hI hw b
  have hBound : IsMaximalOrderAlong Q.N Q.ideal Q.d :=
    initialWeightedRecord_maximalOrder P hSpan hRef hw b [] hDom
  refine ⟨U,V,η,Q,z,hz,hDom,hZero,hCos,hSing,hMaximum.1,hMaximum.2,?_⟩
  exact exists_local_singular_blowup_of_native_whole_initial
    (X := CMfd.of (n := n+1) U) (b ⁻¹' W) (b ⁻¹' singularSet (n := n+1) W)
    Q rfl rfl hIdeal hDom hBound hSing z hZero


end
end Hironaka.HironakaG8PrincipalNativeInitialization
