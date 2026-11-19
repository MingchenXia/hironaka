import Hironaka.Resolution.HironakaG8NativeRestartQuotientChartProvider

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedQuotientAtlasRestart
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec RelativePrincipalizationSpan
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaG8NativeCommonDenominatorReduction HironakaG8ChronologicalNativeClassAtlas
  HironakaG8PrincipalRetainedEpochFinite DivisorExponentAlong MonomialPartAlong
  InvertibleIdealQuotient CompanionReduction HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8NativeRestartQuotientChartProvider HironakaG8ActualQuotientResidualRestart
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualChronologicalResidualDictionary
  HironakaActualWeightedNormalPadding IdealWeightPowers GermIdealOrder NonmonomialOrderLocal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre
  ResolutionDriver CanonicalCentres NonmonomialOrderRegime HomogenizedIdealAlong

private theorem principal_mul_generated_family
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (u : X → ℂ) (f : ι → X → ℂ) (hu : ∀ x, HolomorphicAt n u x)
    (hf : ∀ x i, HolomorphicAt n (f i) x) :
    (finiteFunctionIdeal (n := n) (fun _ : Unit => u)).mul (finiteFunctionIdeal f) =
      finiteFunctionIdeal (fun i => u * f i) := by
  ext x g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hg)
    rintro _ ⟨a,b,ha,hb,rfl⟩
    have ha' : IsInSpanAt (n := n) (fun z => z ∈ range (fun _ : Unit => u)) x a := ha
    have hb' : IsInSpanAt (n := n) (fun z => z ∈ range f) x b := hb
    obtain ⟨N,s,c,hs,hc,hEq⟩ := MarkedIdealOperationsAlong.IsInSpanOnAt.mul (W := univ)
      (IsInSpanAt.restrict ha') (IsInSpanAt.restrict hb')
    refine ⟨ha'.1.mul hb'.1,N,s,c,?_,hc,hEq.mono fun _ h => h trivial⟩
    intro i
    obtain ⟨_,_,⟨_,rfl⟩,⟨j,rfl⟩,h⟩ := hs i
    exact ⟨j,h.symm⟩
  · intro hg
    apply mem_mul_iff.mpr
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    exact ⟨u,f i,isInSpanAt_self ⟨(),rfl⟩ (hu x),isInSpanAt_self ⟨i,rfl⟩ (hf x i),rfl⟩

private theorem denominator_power_ideal_of_generator
    {n : ℕ} {Y : CMfd.{0} n} (D : GermIdeal n Y)
    (u : Y → ℂ) (hu : ∀ y, HolomorphicAt n u y) (d : ℕ)
    (hU : finiteFunctionIdeal (n := n) (fun _ : Unit => u) = D) :
    IdealWeightPowers.idealPow D d = finiteFunctionIdeal (n := n) (fun _ : Unit => u^d) := by
  ext x a
  have huGen (g : Y → ℂ) :
      D.mem x g ↔
        IsInSpanAt (n := n) (· = u) x g := by
    rw [← hU]
    change IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u)) x g ↔ _
    exact ⟨IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm),
      IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩)⟩
  change _ ↔ IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u^d)) x a
  rw [HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff (hu x) huGen]
  exact ⟨IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩),
    IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm)⟩


/-- The local pulled exceptional factor determines the entire normalized
quotient ideal on any genuine target subwindow of the same occupied step. -/
theorem occupied_cut_controlled_quotient_nmPart
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (P : MarkedIdeal n X) (hp : IsInvDomain n P) (hPN : P.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hC : P.IsAdmissibleCentre C)
    (U : Opens X) (V : Opens Y) (hMap : ∀ y : V, π y.val ∈ U)
    (w : ι → ℕ) (d : ℕ) (hd : P.d ≤ d) (hWeights : ∀ i, w i ∣ d)
    (F : ι → U → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : (MarkedIdeal.pullback (Subtype.val : U → X) P).ideal =
      finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (q : ι → V → ℂ) (hq : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : V → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (huIdeal : finiteFunctionIdeal (n := n) (fun _ : Unit => u) =
      GermIdeal.pullback (m := n) (Subtype.val : V → Y) (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i ⟨π y.val,hMap y⟩ = u y ^ w i * q i y) :
    let A := MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)
    let R := finiteFunctionIdeal (n := n) (fun i => q i ^ (d/w i))
    (∀ y ∈ (univ : Set V), IsNonzeroAlongAt (n := n) univ R y) →
    (∀ y : V, ∀ j : Fin A.E.length, y ∈ A.E.get j →
      ∃ i, ∃ᶠ z in 𝓝 y, z ∈ A.E.get j ∧ q i z ≠ 0) →
    nmPart (M := CMfd.of (n := n) V) A = R := by
  intro A R hNZR hTrace
  let A₀ := P.geoTransform C π
  let D := (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  let L := GermIdeal.pullback (m := n) (Subtype.val : V → Y) D
  let v : V → U := fun y => ⟨π y.val,hMap y⟩
  have hv : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ v :=
    BlowupRestrictOpen.contMDiff_opens_mk (hπ.contMDiff.comp contMDiff_subtype_val) hMap
  have hA0 : A₀.IsWellFormed := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hp (.step .refl C π hπ) ⟨trivial,hC⟩).isWellFormed
  have hA : A.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hA0 V
  have hAN₀ : A₀.N = univ := geoTransform_N_eq_univ hPN hπ
  have hAN : A.N = univ := by
    change (Subtype.val : V → Y) ⁻¹' A₀.N = univ
    rw [hAN₀,preimage_univ]
  have hR : R.IsCoherent := isCoherent_finiteFunctionIdeal _ (fun i => (hq i).pow _)
  have hD : D.IsCoherent := DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
  have hL : L.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hD
  have hInv : L.IsInvertible := by
    exact GermIdealTotalTransform.isInvertible_pullback (g := (Subtype.val : V → Y)) contMDiff_subtype_val
      (by rw [HironakaBaseChange.exceptionalLocus_val, interior_empty])
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
  have hu' (y : V) : HolomorphicAt n u y := Eventually.of_forall fun z => hu z
  have hPow := denominator_power_ideal_of_generator (n := n) (Y := CMfd.of (n := n) V) L u hu' d huIdeal
  have hTot : GermIdeal.pullback (m := n) v
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) P.ideal) =
      (idealPow L d).mul R := by
    change GermIdeal.pullback (m := n) v (MarkedIdeal.pullback (Subtype.val : U → X) P).ideal = _
    rw [hGen,hPow,finiteFunctionIdeal_pullback _ (fun i => (hF i).pow _) v hv]
    change _ = (finiteFunctionIdeal (n := n) (fun _ : Unit => u^d)).mul
      (finiteFunctionIdeal (n := n) (fun i => q i ^ (d/w i)))
    have hq' (y : V) (i : ι) : HolomorphicAt n (q i ^ (d/w i)) y :=
      Eventually.of_forall fun z => ((hq i).pow _) z
    rw [principal_mul_generated_family (X := CMfd.of (n := n) V) (u^d) (fun i => q i ^ (d/w i))
      (fun x => CompanionReduction.holomorphicAt_pow_of (hu' x) _) hq']
    apply congrArg (finiteFunctionIdeal (n := n))
    funext i y
    change F i (v y) ^ (d/w i) = u y ^ d * q i y ^ (d/w i)
    change F i ⟨π y.val,hMap y⟩ ^ (d/w i) = _
    rw [hQuot,mul_pow,← pow_mul,Nat.mul_div_cancel' (hWeights i)]
  have hTotPull : GermIdeal.pullback (m := n) (Subtype.val : V → Y)
      (GermIdeal.pullback (m := n) π P.ideal) = (idealPow L d).mul R := by
    rw [← GermIdealTotalTransform.pullback_comp hπ.contMDiff contMDiff_subtype_val hp.isWellFormed.isCoherent]
    rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val hv hp.isWellFormed.isCoherent] at hTot
    exact hTot
  have hInit := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hPN hp.isWellFormed.isCoherent hC
  have hCtl := BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hp.isWellFormed.isCoherent hInit
  rw [← geoTransform_ideal_eq_controlledTransform hPN hp.isWellFormed.isCoherent hπ] at hCtl
  rw [hCtl, GermIdealTotalTransform.pullback_mul contMDiff_subtype_val
    (GermIdealPullbackCalculus.isCoherent_idealPow hD _) hA0.isCoherent,
    BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val hD] at hTotPull
  change (idealPow L P.d).mul A.ideal = (idealPow L d).mul R at hTotPull
  let M := idealPow L (d - P.d)
  have hM : M.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow hL _
  have hFactor : A.ideal = M.mul R := by
    have hRearrange : (idealPow L P.d).mul (M.mul R) = (idealPow L d).mul R := by
      rw [← GermIdealTotalTransform.mul_assoc (GermIdealPullbackCalculus.isCoherent_idealPow hL _) hM hR]
      change ((idealPow L P.d).mul (idealPow L (d-P.d))).mul R = _
      rw [← RestrictLeCalculus.idealPow_add hL,Nat.add_sub_of_le hd]
    rw [← hRearrange] at hTotPull
    have hCan := congrArg (fun J => InvertibleIdealQuotient.colon J (idealPow L P.d)) hTotPull
    have hi := BlowupExceptionalDivisor.isInvertible_idealPow hInv P.d
    rw [BlowupControlledTransform.colon_mul_eq hi hA.isCoherent,
      BlowupControlledTransform.colon_mul_eq hi (isCoherent_mul hM hR)] at hCan
    exact hCan
  obtain ⟨hDC,hDN,hDM⟩ := HironakaSharpActualMonomialDivisionResidual.actual_new_exceptional_power_monomial
    hn hp.isWellFormed.isClosedSubmanifold_N hp.isWellFormed.isSNCDivisor hp.isWellFormed.isTransverse
    hπ hC.subset_N hC.2.2 (d-P.d)
  let M₀ : MarkedIdeal n Y := ⟨A₀.N,A₀.E,idealPow D (d-P.d),0⟩
  have hDN' := MonomialCaseLocal.isNonzeroAlongAt_pullback_val (𝔪 := M₀) hDC hDN V
  have hDM' := MonomialCaseLocal.isMonomialAlong_pullback_val_of_isMonomialAlong (𝔪 := M₀) hDC hDM V
  change (∀ y ∈ A.N, IsNonzeroAlongAt A.N
    (GermIdeal.pullback (m := n) (Subtype.val : V → Y) (idealPow D (d-P.d))) y) at hDN'
  change IsMonomialAlong n A.N
    (GermIdeal.pullback (m := n) (Subtype.val : V → Y) (idealPow D (d-P.d))) A.E at hDM'
  rw [BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val hD] at hDN' hDM'
  change (∀ y ∈ A.N, IsNonzeroAlongAt A.N M y) at hDN'
  change IsMonomialAlong n A.N M A.E at hDM'
  rw [hAN] at hDN' hDM'
  have hTrans : NormalCrossings.IsTransverse n univ A.E := hAN ▸ hA.isTransverse
  have hU := HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := V)
  have hNo : ∀ y ∈ (univ : Set V), ∀ i : Fin A.E.length, y ∈ A.E.get i →
      ∃ f, R.mem y f ∧ ¬ IsInSpanOnAt (n := n) univ ((vanishingIdeal (n := n) (A.E.get i)).mem y) y f := by
    intro y _ j hy
    obtain ⟨i,hi⟩ := hTrace y j hy
    have hHol : HolomorphicAt n (q i) y := Eventually.of_forall fun z => hq i z
    exact ⟨q i ^ (d/w i),isInSpanAt_self ⟨i,rfl⟩ (CompanionReduction.holomorphicAt_pow_of hHol _),
      quotient_power_not_boundary_factor (X := CMfd.of (n := n) V) A hA hAN y j (q i) hHol _ hi⟩
  have hStrip := actual_normalized_monomial_product_nonmonomial_eq (X := CMfd.of (n := n) V) hn hU hA.isSNCDivisor hTrans
    hM hR hDN' hNZR hDM'
  rw [BlowupTowerTransforms.restrictOn_univ (isCoherent_mul hM hR)] at hStrip
  have hRes := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor (X := CMfd.of (n := n) V) hU hA.isSNCDivisor hTrans hR hNo
  rw [BlowupTowerTransforms.restrictOn_univ hR] at hRes
  change nonmonomialPartAlong n A.N A.ideal A.E = R
  rw [hAN,hFactor,hStrip,hRes]

/-- Source and quotient data on a target subwindow of one fixed physical
occupied cut. The target need only project into the source window. -/
structure OccupiedCutNativeChart
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P : MarkedIdeal (n+1) X) {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π)
    (V : Opens Y) (Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V)) (d : ℕ) where
  U : Opens X
  mapsTo : ∀ y : V, π y.val ∈ U
  weight : ι → ℕ
  weightPositive : ∀ j, 0 < weight j
  weightDvd : ∀ j, weight j ∣ d
  commonDvd : d ∣ weightedCommonMark weight
  sourceFn : ι → U → ℂ
  sourceHol : ∀ j, MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (sourceFn j)
  sourceGen : (MarkedIdeal.pullback (Subtype.val : U → X) P).ideal =
    finiteFunctionIdeal (fun j => sourceFn j ^ (d/weight j))
  fn : ι → V → ℂ
  fnHol : ∀ j, MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) (fn j)
  denominator : V → ℂ
  denominatorHol : MDifferentiable 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) denominator
  denominatorIdeal : finiteFunctionIdeal (n := n+1) (fun _ : Unit => denominator) =
    GermIdeal.pullback (m := n+1) (Subtype.val : V → Y) (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  quotient : ∀ j (y : V), sourceFn j ⟨π y.val,mapsTo y⟩ = denominator y ^ weight j * fn j y
  raw : Q = ⟨univ,(MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)).E,
    weightedFunctionIdeal weight fn,weightedCommonMark weight⟩
  rawNoFactor : HasNoBoundaryFactor Q

/-- Every actual chart of the occupied cut supplies the normalized low
residual. The native domain and its whole ordered boundary witnesses
supply the two quotient-side geometric conditions. -/
theorem OccupiedCutNativeChart.nmPart_eq
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    {P : MarkedIdeal (n+1) X} (hp : IsInvDomain (n+1) P) (hPN : P.N = univ)
    {C : Set X} {π : Y → X} {hπ : IsBlowupAlong (n+1) C π} (hC : P.IsAdmissibleCentre C)
    {V : Opens Y} {Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V)} (hq : IsInvDomain (n+1) Q)
    {d : ℕ} (hd : P.d ≤ d) (C₀ : OccupiedCutNativeChart (ι := ι) P hπ V Q d) :
    nmPart (M := CMfd.of (n := n+1) V) (MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)) =
      finiteFunctionIdeal (fun i => C₀.fn i ^ (d/C₀.weight i)) := by
  let A := MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)
  have hQN : Q.N = univ := congrArg MarkedIdeal.N C₀.raw
  have hQE : Q.E = A.E := by
    have h := congrArg (fun R : MarkedIdeal (n+1) (CMfd.of (n := n+1) V) => R.E) C₀.raw
    exact h
  have hQI : Q.ideal = weightedFunctionIdeal C₀.weight C₀.fn := congrArg MarkedIdeal.ideal C₀.raw
  have hHol (y : V) (i : ι) : HolomorphicAt (n+1) (C₀.fn i) y :=
    Eventually.of_forall fun z => C₀.fnHol i z
  have hLe := weightedFunctionIdeal_le_common_denominator (X := CMfd.of (n := n+1) V)
    C₀.weight C₀.weightPositive C₀.fn hHol d (Nat.zero_lt_of_lt (hp.one_le_d.trans hd)) C₀.weightDvd C₀.commonDvd
  apply occupied_cut_controlled_quotient_nmPart (Nat.succ_pos n) P hp hPN hπ hC
    C₀.U V C₀.mapsTo C₀.weight d hd C₀.weightDvd C₀.sourceFn C₀.sourceHol C₀.sourceGen
    C₀.fn C₀.fnHol C₀.denominator C₀.denominatorHol C₀.denominatorIdeal C₀.quotient
  · intro y hy
    obtain ⟨g,hg,hn⟩ := hq.isNonzeroAlongAt y (hQN ▸ hy)
    exact ⟨g,hLe y g (hQI ▸ hg),hQN ▸ hn⟩
  · have h : ∀ y : V, ∀ j : Fin Q.E.length, y ∈ Q.E.get j →
        ∃ i, ∃ᶠ z in 𝓝 y, z ∈ Q.E.get j ∧ C₀.fn i z ≠ 0 := by
      intro y j hy
      exact native_quotient_not_vanishing_on_boundary (X := CMfd.of (n := n+1) V)
        Q hq.isWellFormed hQN C₀.weight C₀.weightPositive C₀.fn hHol hQI C₀.rawNoFactor y j hy
    rw [hQE] at h
    exact h

private theorem native_active_ordinary_order_of_large_mark
    {n : ℕ} {X : CMfd.{0} n} {Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}
    (hNative : HironakaG11PresLineState.NativeHSState Q W H) (hLarge : 1 < Q.d) :
    ∀ x ∈ Q.cosupp, HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder Q.N Q.ideal x = Q.d := by
  obtain ⟨_, _, hN, hI, V, S, k, a, w, hw, _, _, hMark, _, _, hAt⟩ := hNative
  have hv : V.Nonempty := by
    by_contra hNo
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
    have hOne : Q.d = 1 := by
      rw [hMark]
      subst V
      simp [weightedCommonMark]
    omega
  intro x hx
  have hOrd := (HironakaActualHistoricalNativeOrdinaryOrder.actual_native_point_ordinary_order
    S hv a w hw W Q hN hI hMark x hx (hAt x hx)).1
  rwa [hN,hMark]

/-- At a genuine occupied chronological cut every adopted target window
may use its own actual coordinate equation. The subsequent covered
native atlas certifies the original chronological history. -/
theorem append_chronological_canonical_of_occupied_quotient_atlas
    {n : ℕ} {Z X Y B : CMfd.{0} (n+1)} {I : Type} {ι : I → Type} [∀ i, Fintype (ι i)]
    {W D : Set Y} {E : List (Set Y)} {H : ℕ → ℕ}
    (A : NativeWindows Y I W E H D)
    (M : MarkedIdeal (n+1) Z) (hM : IsInvDomain (n+1) M) (hMN : M.N = univ)
    (P₀ : BlowupTower Z X) (hCan₀ : IsCanonical M ((canonicalInvariant (n+1)).inv M) P₀)
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hCut : C.Nonempty ∧ C = maxLocus ((canonicalInvariant (n+1)).inv M P₀)
      (geoTransformAlong M P₀).cosupp)
    (d e : ℕ) (hd : M.d ≤ d) (hdLarge : 1 < d) (he : 1 ≤ e) (hMark : A.mark = d*e)
    (hHigher₀ : CentresOrdGt M d P₀)
    (hCutHigh : C ⊆ ordGe (geoTransformAlong M P₀) (d+1))
    (T : BlowupTower Y B)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered T)
    (hContains : cosupport (n+1) univ (nmPart (geoTransformAlong M (.step P₀ C π hπ))) d ⊆ D)
    (hChart : ∀ i, OccupiedCutNativeChart (ι := ι i) (geoTransformAlong M P₀) hπ
      (A.openSet i) (A.record i) d) :
    IsCanonical M ((canonicalInvariant (n+1)).inv M) ((BlowupTower.step P₀ C π hπ).append T) := by
  let P : BlowupTower Z Y := .step P₀ C π hπ
  have hCanP : IsCanonical M ((canonicalInvariant (n+1)).inv M) P := ⟨hCan₀,Or.inr hCut.2⟩
  have hHigher : CentresOrdGt M d P := ⟨hHigher₀,hCutHigh⟩
  let L := geoTransformAlong M P
  let F : MarkedIdeal (n+1) Y := ⟨univ,L.E,nmPart L,d⟩
  have hTP := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hM P hCanP
  have hOld := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P₀ hTP.1
  have hOldN := (pullback_eq_mul_geoTransformAlong (𝔪 := M)
    hMN hM.isWellFormed.isCoherent P₀ hTP.1).1
  have hOldd : (geoTransformAlong M P₀).d ≤ d := (d_geoTransformAlong M P₀).trans_le hd
  have hLD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTP
  have hLN : L.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := M)
    hMN hM.isWellFormed.isCoherent P hTP).1
  have hPart := NonmonomialTransformAlong.parts_hypotheses (Nat.succ_pos n)
    L hLD.isWellFormed hLD.isNonzeroAlongAt
  have hF : IsInvDomain (n+1) F := by
    refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hPart.1,hLD.isWellFormed.isSNCDivisor,?_⟩,
      ?_,hM.one_le_d.trans hd,?_⟩
    · change NormalCrossings.IsTransverse (n+1) univ L.E
      rw [← hLN]
      exact hLD.isWellFormed.isTransverse
    · change DimLE (n+1) (univ : Set Y) (n+1)
      rw [← hLN]
      exact hLD.dimLE
    · change ∀ x ∈ (univ : Set Y), IsNonzeroAlongAt univ (nmPart L) x
      rw [← hLN]
      exact hPart.2.2.2.2.2.1
  have hNo : HasNoBoundaryFactor F := by
    have h := hPart.2.2.2.2.1
    change ∀ x ∈ L.N, ∀ i : Fin L.E.length, x ∈ L.E.get i →
      ∃ q, (nmPart L).mem x q ∧
        ¬ IsInSpanOnAt (n := n+1) L.N ((vanishingIdeal (n := n+1) (L.E.get i)).mem x) x q at h
    rw [hLN] at h
    exact h
  let R (i : I) := MarkedIdeal.pullback (Subtype.val : A.openSet i → Y) F
  have hClassExp (i : I) : LocWPEquiv (A.record i) (R i) ∧
      ∀ H x, F.d * divExpAlong (n+1) (A.record i).N (A.record i).ideal H x =
        (A.record i).d * divExpAlong (n+1) (R i).N (R i).ideal H x := by
    let C := hChart i
    let l := MarkedIdeal.pullback (Subtype.val : A.openSet i → Y) L
    have hChartI : (R i).ideal = nmPart (M := CMfd.of (n := n+1) (A.openSet i)) l := by
      exact MonomialPartEtale.pullback_nonmonomialPartAlong
        (fun y => ⟨DerivativeIdealAlongEtale.openInv (A.openSet i) y,
          DerivativeIdealAlongEtale.isLocalInverseAt_val (A.openSet i) y⟩)
        hLD.isWellFormed.isCoherent hPart.2.1 hPart.1
    have hRShape : R i = ⟨univ,l.E,finiteFunctionIdeal (fun j => C.fn j ^ (d/C.weight j)),d⟩ :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
        (hChartI.trans (C.nmPart_eq hOld hOldN hTP.2 (A.domain i) hOldd)) rfl
    have hRd : IsInvDomain (n+1) (R i) := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
    have hQd := A.domain i
    rw [hRShape] at hRd
    rw [C.raw] at hQd
    have hCmp := common_denominator_native_boundary_class (X := CMfd.of (n := n+1) (A.openSet i))
      C.weight C.weightPositive C.fn C.fnHol d (Nat.zero_lt_of_lt (hM.one_le_d.trans hd))
      C.weightDvd C.commonDvd l.E hRd hQd
    let R₁ : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,l.E,finiteFunctionIdeal (fun j => C.fn j ^ (d/C.weight j)),d⟩
    let Q₁ : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) :=
      ⟨univ,l.E,weightedFunctionIdeal C.weight C.fn,weightedCommonMark C.weight⟩
    change LocWPEquiv Q₁ R₁ ∧
      ∀ H x, R₁.d * divExpAlong (n+1) Q₁.N Q₁.ideal H x =
        Q₁.d * divExpAlong (n+1) R₁.N R₁.ideal H x at hCmp
    have hR₁ : R i = R₁ := hRShape
    have hQ₁ : A.record i = Q₁ := C.raw
    rw [← hR₁, ← hQ₁] at hCmp
    exact hCmp
  have hNClass (i : I) : (A.record i).N = (Subtype.val : A.openSet i → Y) ⁻¹' F.N := by
    rw [(hChart i).raw]
    exact preimage_univ.symm
  have hCap : IsMaximalOrderAlong F.N F.ideal F.d := by
    intro x hx
    have hxF : x ∈ F.cosupp := cosupport_anti (Nat.le_succ F.d) hx
    obtain ⟨i,hi⟩ := A.covers x (hContains hxF)
    let z : A.openSet i := ⟨x,hi⟩
    have hRDomain : IsInvDomain (n+1) (R i) := InvDomainTowerAlong.isInvDomain_pullback_val (A.openSet i) hF
    have hLargeQ : 1 < (A.record i).d := by
      let C := hChart i
      have hc : (A.record i).d = weightedCommonMark C.weight := congrArg MarkedIdeal.d C.raw
      rw [hc]
      exact hdLarge.trans_le (Nat.le_of_dvd (weightedCommonMark_pos C.weight C.weightPositive) C.commonDvd)
    have hActive := native_active_ordinary_order_of_large_mark (A.native i) hLargeQ
    have hRCap := HironakaG8EqualWeightNativeThresholds.reference_cap_of_native_active_order
      (X := CMfd.of (n := n+1) (A.openSet i)) (A.record i) (R i) (A.domain i) hRDomain
      (SameCarrierDim.of_N_eq (hNClass i)) (hClassExp i).1 hActive
    apply hRCap z
    let Fplus := {F with d := F.d + 1}
    have hPull := MarkedIdealRestrictOpen.cosupp_pullback_val Fplus
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hF.isWellFormed.isCoherent hg)
      (A.openSet i)
    change z ∈ (MarkedIdeal.pullback (Subtype.val : A.openSet i → Y) Fplus).cosupp
    rw [hPull]
    exact hx
  exact append_chronological_canonical_of_native_class_cover A M hM P hCanP F hF rfl hNo hCap hHigher
    e he hMark hContains (fun i => (hClassExp i).1) hNClass (fun i => (hClassExp i).2)
    T hSync hLN rfl ((d_geoTransformAlong M P).trans_le hd) rfl

/-- On each adopted occupied-cut chart, the active original low order
stratum is exactly the genuine native Hilbert–Samuel profile stratum. -/
theorem OccupiedCutNativeChart.order_and_profile
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    {P : MarkedIdeal (n+1) X} (hp : IsInvDomain (n+1) P) (hPN : P.N = univ)
    {C : Set X} {π : Y → X} {hπ : IsBlowupAlong (n+1) C π} (hC : P.IsAdmissibleCentre C)
    {V : Opens Y} {Q : MarkedIdeal (n+1) (CMfd.of (n := n+1) V)} (hq : IsInvDomain (n+1) Q)
    {d : ℕ} (hd : P.d ≤ d) (hdLarge : 1 < d) (D : OccupiedCutNativeChart (ι := ι) P hπ V Q d)
    {W : Set V} {H : ℕ → ℕ} (hNative : HironakaG11PresLineState.NativeHSState Q W H) :
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (P.geoTransform C π)
    (∀ x : V, nmOrd (M := CMfd.of (n := n+1) V) L x ≤ d) ∧
    (∀ x : V, nmOrd (M := CMfd.of (n := n+1) V) L x = d ↔
      ∀ k, HironakaHolomorphicJetChartInvariance.hilbertSamuelAt (vanishingIdeal (n := n+1) W) x k = H k) := by
  intro L
  let B := CMfd.of (n := n+1) V
  let I := nmPart (M := B) L
  have hLD : IsInvDomain (n+1) L :=
    InvDomainTowerAlong.isInvDomain_pullback_val V
      (InvDomainTowerAlong.isInvDomain_geoTransformAlong hp (.step .refl C π hπ) ⟨trivial,hC⟩)
  have hLN : L.N = univ := by
    change (Subtype.val : V → Y) ⁻¹' (P.geoTransform C π).N = univ
    rw [geoTransform_N_eq_univ hPN hπ,preimage_univ]
  have hPart := NonmonomialTransformAlong.parts_hypotheses (Nat.succ_pos n)
    (M := B) L hLD.isWellFormed hLD.isNonzeroAlongAt
  have hI : I.IsCoherent := hPart.1
  have hINZ : ∀ y ∈ (univ : Set V), IsNonzeroAlongAt (n := n+1) univ I y := by
    have hx : ∀ y ∈ L.N, IsNonzeroAlongAt (n := n+1) L.N I y := hPart.2.2.2.2.2.1
    rwa [hLN] at hx
  have hIEq : I = finiteFunctionIdeal (fun i => D.fn i ^ (d/D.weight i)) :=
    D.nmPart_eq hp hPN hC hq hd
  have hQN : Q.N = univ := congrArg MarkedIdeal.N D.raw
  have hQd : Q.d = weightedCommonMark D.weight := congrArg MarkedIdeal.d D.raw
  have hQI : Q.ideal = weightedFunctionIdeal D.weight D.fn := congrArg MarkedIdeal.ideal D.raw
  let e := weightedCommonMark D.weight / d
  let r := Fintype.card ι * (e-1)
  have hm : d*e = Q.d := (Nat.mul_div_cancel' D.commonDvd).trans hQd.symm
  have hM := weightedCommonMark_pos D.weight D.weightPositive
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd hM D.commonDvd) (Nat.zero_lt_of_lt hdLarge)
  have hRed : (idealPow I r).mul Q.ideal = idealPow I (r+e) := by
    rw [hIEq,hQI,weightedFunctionIdeal_eq_common_denominator_power (X := B)
      D.weight D.weightPositive D.fn d D.weightDvd D.commonDvd]
    exact HironakaG8FinitePowerReductionLocalEquiv.finite_function_power_reduction (X := B)
      (fun i => D.fn i ^ (d/D.weight i)) (fun i => (D.fnHol i).pow _) r e he (by dsimp [r]; omega)
  have hCuts (j : ℕ) : cosupport (n+1) univ I j = cosupport (n+1) univ Q.ideal (j*e) :=
    HironakaG8FinitePowerReductionLocalEquiv.finite_power_reduction_cosupport (X := B)
      I Q.ideal hI hq.isWellFormed.isCoherent hINZ r e he hRed j
  have hMax := native_source_cap_of_state Q hNative
    (hdLarge.trans_le (Nat.le_of_dvd hM D.commonDvd |>.trans_eq hQd.symm))
  have hCap (x : V) : nmOrd (M := B) L x ≤ d := by
    apply nmOrd_le_of_notMem
    change x ∉ cosupport (n+1) L.N I (d+1)
    rw [hLN,hCuts]
    intro hx
    apply hMax x
    rw [hQN,←hm]
    exact cosupport_anti (by rw [Nat.add_mul,Nat.one_mul]; omega) hx
  refine ⟨hCap,fun x => ?_⟩
  have hCut : ordGe (M := B) L d = Q.cosupp := by
    change cosupport (n+1) L.N I d = cosupport (n+1) Q.N Q.ideal Q.d
    rw [hLN,hQN,hCuts,hm]
  have hxN : x ∈ L.N := hLN ▸ mem_univ x
  have hOrd := mem_ordGe_iff (M := B) (𝔪 := L) hLD.isWellFormed hLD.isNonzeroAlongAt hxN d
  constructor
  · intro hx
    have hxQ : x ∈ Q.cosupp := hCut ▸ hOrd.mpr (le_of_eq hx.symm)
    rwa [hNative.cosupp_eq] at hxQ
  · intro hx
    have hxQ : x ∈ Q.cosupp := by rwa [hNative.cosupp_eq]
    exact le_antisymm (hCap x) (hOrd.mp (hCut ▸ hxQ))

end
end Hironaka.HironakaG8OccupiedQuotientAtlasRestart
