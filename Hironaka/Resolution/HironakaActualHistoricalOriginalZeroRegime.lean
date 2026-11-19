import Hironaka.Resolution.HironakaActualHistoricalInitialCompanionRecursion

/-! Actual original-bar zero regimes and actual original lowerMarkedB
recursion for genuine weighted HS histories. No current-bar reset, incoming
zero regime/contact CAN or normal-padding CAN. Blueprint FIRST. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalOriginalZeroRegime
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalInitialCompanionRecursion HironakaActualHistoricalOriginalNativePhase
  HironakaActualHistoricalNativeFunctionTower HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalSortedPrefixFrames HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualFixedInheritedSelector
  HironakaActualInheritedNestedContactFlag HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaActualInheritedSmallTails
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalHSMarkedDomain HironakaActualPrescribedCentreRebasing
  HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaSmoothSubmersionGermIdealColon HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalScaledAnalyticDivision HironakaActualWeightedCoefficientCompression
  HironakaEmbeddedAnalytic HironakaGeneralSingularCentreCodimension
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres CompanionRebase CompanionReductionAlong GeneralCompare
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneRegime
  StepOneValueMasked StepOneLowerDomain CodimOneSupportAlong NonmonomialOrderTail
  NonmonomialOrderRegime BoundaryCount MarkedIdealEquivalence.MarkedIdeal

variable {n : ℕ} {X : CMfd.{0} n}

/-- Genuine mixed-dimensional singular geometry excludes the ACTUAL native
codimension-one part of the SAME whole cosupport. -/
theorem codimOnePartAlong_eq_empty_of_singular_cosupp
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hN : Q.N=univ)
    (hSing : Q.cosupp⊆singularSet (n:=n) W) :
    codimOnePartAlong Q.N Q.ideal Q.d=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨r,hNr,hSr⟩ := hx
  have hUniv : RegularAtDim (n:=n) (univ : Set X) x n :=
    AnalyticIrreducibleComponents.regularAtDim_univ x
  have hDim := RegularPointDimension.eq_of_regularAtDim (hN ▸ hNr) hUniv
  have hBound := regular_intrinsic_singular_centre_add_two_le hW hSing hSr
  omega

private theorem current_carrier (Q : MarkedIdeal n X) (hN : Q.N=univ) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),(geoTransformAlong Q T).N=univ
  | _,.refl=>hN
  | _,.step T _ _ hπ=>by
    rw [geoTransformAlong_step]
    exact geoTransform_N_eq_univ (current_carrier Q hN T) hπ

private theorem level_zero (Q : MarkedIdeal n X) (hE : Q.E=[])
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(y : Y) : level Q T y=0 := by
  simp only [level,origMembers,hE,List.length_nil,List.take_zero]
  rfl

private theorem bar_history (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    IsGeoTestTower (barMarked Q) T ∧
      (geoTransformAlong (barMarked Q) T).cosupp=(geoTransformAlong Q T).cosupp ∧
      (geoTransformAlong (barMarked Q) T).E=(geoTransformAlong Q T).E := by
  have he := coeff_homAlong_wEquiv Q hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent hQ.one_le_d
  have hb := (he.2 T).1.mpr hT
  exact ⟨hb,(he.2 T).2 hb,E_geoTransformAlong_congr he.1 T⟩

private theorem zero_geometry (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hN : Q.N=univ) (hE : Q.E=[])
    (hState : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∃W : Set Y,IsComplexAnalyticSubset (n:=n) W ∧
        (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) W)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    codimOnePartAlong (geoTransformAlong (barMarked Q) T).N
        (geoTransformAlong (barMarked Q) T).ideal (geoTransformAlong (barMarked Q) T).d=∅ ∧
      ∀y : Y,level Q T y=0 ∧ ¬ IsSpecial Q T y ∧ stepRegime Q 0 T y := by
  obtain ⟨W,hW,hSing⟩ := hState T hT
  have hCos := (bar_history Q hQ T hT).2.1
  have hBarN : (barMarked Q).N=univ := hN
  have hZero := codimOnePartAlong_eq_empty_of_singular_cosupp W hW
    (geoTransformAlong (barMarked Q) T) (current_carrier (barMarked Q) hBarN T)
    (fun y hy=>hSing (hCos ▸ hy))
  refine ⟨hZero,fun y=>?_⟩
  have hL := level_zero Q hE T y
  have hNot : ¬ IsSpecial Q T y := by
    rintro (⟨_hL,hZ⟩ | ⟨hPos,_hMember⟩)
    · rw [hZero] at hZ
      exact notMem_empty y hZ
    · rw [hL] at hPos
      omega
  exact ⟨hL,hNot,hL,hNot⟩

private theorem zero_run (Q : MarkedIdeal n X)
    (hZero : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀y : Y,stepRegime Q 0 T y) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀y : Y,regimeRun (stepRegime Q 0) T y=T.length
  | _,.refl,_,_=>rfl
  | _,.step T C π hπ,hT,y=>by
    rw [regimeRun_step_of (stepRegime Q 0) T C π hπ (hZero T hT.1 (π y)),
      zero_run Q hZero T hT.1 (π y)]
    rfl

private theorem restricted_zero (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hN : Q.N=univ) (hE : Q.E=[])
    (hState : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∃W : Set Y,IsComplexAnalyticSubset (n:=n) W ∧
        (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) W)
    (U : Opens X) {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    ∀p : openPreimage T U,
      level (MarkedIdeal.pullback (Subtype.val : U→X) Q) (restrict U T) p=0 ∧
      ¬ IsSpecial (MarkedIdeal.pullback (Subtype.val : U→X) Q) (restrict U T) p ∧
      regimeRun (stepRegime (MarkedIdeal.pullback (Subtype.val : U→X) Q) 0) (restrict U T) p=
        (restrict U T).length := by
  have hb := (bar_history Q hQ T hT).1
  have hHere := (zero_geometry Q hQ hN hE hState T hT).2
  have hFull := zero_run Q (fun S hS y=>((zero_geometry Q hQ hN hE hState S hS).2 y).2.2) T hT
  intro p
  obtain ⟨hL,hSp,_hReg⟩ := (StepOneRestrictOpen.restrict_facts Q U hQ.isWellFormed hQ.one_le_d T hb).2.2 p
  refine ⟨hL.trans (hHere p.val).1,fun h=>(hHere p.val).2.1 (hSp.mp h),?_⟩
  have hRun := NonmonomialOrderRegime.regimeRun_restrict_of U (stepRegime Q 0)
    (stepRegime (MarkedIdeal.pullback (Subtype.val : U→X) Q) 0)
    (fun S=>IsGeoTestTower (barMarked Q) S) (fun _ _ _ _ h=>h.1)
    (fun S hS z=>((StepOneRestrictOpen.restrict_facts Q U hQ.isWellFormed hQ.one_le_d S hS).2.2 z).2.2 0)
    T hb p
  exact hRun.trans ((hFull p.val).trans (length_restrict U T).symm)

private theorem split_full : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),
    split T T.length=⟨X,.refl,T⟩
  | _,.refl=>rfl
  | _,.step T C π hπ=>by
    change (⟨(split T T.length).1,(split T T.length).2.1,
      .step (split T T.length).2.2 C π hπ⟩ : Σ A : CMfd.{0} n,BlowupTower X A × BlowupTower A _)=_
    rw [split_full T]

private theorem full_zero_value {k : ℕ} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ) (J : MarkedIdeal n X)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(p : Y)
    (hL : level J T p=0) (hNsp : ¬ IsSpecial J T p)
    (hRun : regimeRun (stepRegime J 0) T p=T.length)
    (hm : T.proj p∈maskB J (.refl : BlowupTower X X) (T.proj p)) :
    Seq.StepOneValueMasked.stepOneInvM R J T p=toLex (0,
      ((R.inv (lowerMarkedB J (.refl : BlowupTower X X) (T.proj p))
        (restrict (maskB J (.refl : BlowupTower X X) (T.proj p)) T) ⟨p,hm⟩ : Λ) : WithTop Λ)) := by
  change Seq.StepOneValueMasked.stepOneInvL R J (lowerMarkedM J) T p=_
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J (lowerMarkedM J) T hNsp,hL,hRun]
  unfold head tail
  rw [split_full T]
  have hm' : T.proj p∈lowerMask J 0 (.refl : BlowupTower X X) (T.proj p) := hm
  rw [Seq.StepOneValueMasked.lowerValueL_eq_of_mem (s:=0) (T₀:=(.refl : BlowupTower X X))
    (T₁:=T) R J (lowerMarkedM J) hm']
  rfl

private theorem original_lower_data (hn : 0<n) (k : ℕ) (J : MarkedIdeal n X)
    (hJ : IsInvDomain (k+1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (hZero : ∀p : Y,level J T p=0 ∧ ¬ IsSpecial J T p ∧
      regimeRun (stepRegime J 0) T p=T.length)
    (p : Y)(hp : p∈(geoTransformAlong J T).cosupp) :
    ∃hm : T.proj p∈maskB J (.refl : BlowupTower X X) (T.proj p),
      let V:=maskB J (.refl : BlowupTower X X) (T.proj p)
      let B:=lowerMarkedB J (.refl : BlowupTower X X) (T.proj p)
      IsInvDomain k B ∧ IsCanonical B ((invFamily hn k).inv B) (restrict V T) ∧
      IsGeoTestTower B (restrict V T) ∧
      (⟨p,hm⟩ : openPreimage T V)∈(geoTransformAlong B (restrict V T)).cosupp ∧
      (geoTransformAlong B (restrict V T)).cosupp=
        (Subtype.val : openPreimage T V→Y) ⁻¹' (geoTransformAlong (barMarked J) T).cosupp ∧
      (geoTransformAlong B (restrict V T)).E=(geoTransformAlong (barMarked J) T).E.map
        ((Subtype.val : openPreimage T V→Y) ⁻¹' ·) ∧
      B.d=(coeffMarkedAlong (barMarked J)).d ∧ (restrict V T).length=T.length ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T p=toLex (0,
        (((invFamily hn k).inv B (restrict V T) ⟨p,hm⟩ : ValTy k) : WithTop (ValTy k))) := by
  dsimp only
  obtain ⟨hbT,_hJT,hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn k) J hJ hMax hn T hCan
  have hbCan := (Seq.StepOneBridge.isCanonical_iff (invFamily hn k) J hJ hMax hn T).mp hCan
  have hpBar : p∈(geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hp
  obtain ⟨hL,hNsp,hRun⟩ := hZero p
  have hData := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical J (k:=k+1)
    (invFamily hn k) hJ.isWellFormed hJ.one_le_d hn hMax hJ.dimLE T hbT hbCan p hpBar hNsp
  rw [hL,hRun] at hData
  unfold head tail at hData
  rw [split_full T] at hData
  change ∃hm : T.proj p∈maskB J (.refl : BlowupTower X X) (T.proj p),
    IsInvDomain k (lowerMarkedB J (.refl : BlowupTower X X) (T.proj p)) ∧
    IsCanonical (lowerMarkedB J (.refl : BlowupTower X X) (T.proj p))
      ((invFamily hn k).inv (lowerMarkedB J (.refl : BlowupTower X X) (T.proj p)))
      (restrict (maskB J (.refl : BlowupTower X X) (T.proj p)) T) ∧
    (⟨p,hm⟩ : openPreimage T (maskB J (.refl : BlowupTower X X) (T.proj p)))∈
      (geoTransformAlong (lowerMarkedB J (.refl : BlowupTower X X) (T.proj p))
        (restrict (maskB J (.refl : BlowupTower X X) (T.proj p)) T)).cosupp at hData
  obtain ⟨hm,hDom,hCanB,hpB⟩ := hData
  let V:=maskB J (.refl : BlowupTower X X) (T.proj p)
  let B:=lowerMarkedB J (.refl : BlowupTower X X) (T.proj p)
  have hBar := isWellFormed_barMarked J hJ.isWellFormed
  have ha := proj_mem_cosupp_of_mem_cosupp hBar.isClosedSubmanifold_N hBar.isCoherent T hbT hpBar
  have hAppend : IsGeoTestTower (barMarked J) ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hbT
  have hBCos := StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB J hJ.isWellFormed hJ.one_le_d hMax
    (.refl : BlowupTower X X) T hAppend ha
  simp only [BlowupTower.refl_append] at hBCos
  have hE : B.E=(MarkedIdeal.pullback (Subtype.val : V→X) (barMarked J)).E := rfl
  have hEt := E_geoTransformAlong_congr hE (restrict V T)
  have hBarRestrict := geoTransformAlong_restrict V hBar.isClosedSubmanifold_N hBar.isCoherent T hbT
  refine ⟨hm,hDom,hCanB,hBCos.1,hpB,hBCos.2,?_,rfl,length_restrict V T,?_⟩
  · exact hEt.trans (congrArg MarkedIdeal.E hBarRestrict)
  · exact full_zero_value (invFamily hn k) J T p hL hNsp hRun hm

private theorem lower_history (hn : 0<n) (k : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hState : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∃W : Set Y,IsComplexAnalyticSubset (n:=n) W ∧
        (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) W)
    (U : Opens X) (J : MarkedIdeal n (CMfd.of (n:=n) U))
    (hJeq : J=MarkedIdeal.pullback (Subtype.val : U→X) Q)
    (hJ : IsInvDomain (k+1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T)) :
    let R:=restrict U T
    IsGeoTestTower (barMarked J) R ∧
      (geoTransformAlong (barMarked J) R).cosupp=
        (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
      (geoTransformAlong (barMarked J) R).E=(geoTransformAlong Q T).E.map
        ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
      (R.length=T.length) ∧
      (∀p : openPreimage T U,level J R p=0 ∧ ¬ IsSpecial J R p ∧
        regimeRun (stepRegime J 0) R p=R.length) ∧
      ∀p∈(geoTransformAlong J R).cosupp,
        ∃hm : R.proj p∈maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p),
          let V:=maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
          let B:=lowerMarkedB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
          IsInvDomain k B ∧ IsCanonical B ((invFamily hn k).inv B) (restrict V R) ∧
          IsGeoTestTower B (restrict V R) ∧
          (⟨p,hm⟩ : openPreimage R V)∈(geoTransformAlong B (restrict V R)).cosupp ∧
          (geoTransformAlong B (restrict V R)).cosupp=
            (Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' (geoTransformAlong (barMarked J) R).cosupp ∧
          (geoTransformAlong B (restrict V R)).E=(geoTransformAlong (barMarked J) R).E.map
            ((Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' ·) ∧
          B.d=(coeffMarkedAlong (barMarked J)).d ∧ (restrict V R).length=R.length ∧
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J R p=toLex (0,
            (((invFamily hn k).inv B (restrict V R) ⟨p,hm⟩ : ValTy k) : WithTop (ValTy k))) := by
  dsimp only
  obtain ⟨hbT,hCosQ,_hEQ⟩ := bar_history Q hQ T hT
  obtain ⟨hJT,hJCos,_hFacts⟩ := StepOneRestrictOpen.restrict_facts Q U hQ.isWellFormed hQ.one_le_d T hbT
  rw [←hJeq] at hJT hJCos
  have hZ := restricted_zero Q hQ hN hE hState U T hT
  rw [←hJeq] at hZ
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hJ.one_le_d
  have hJE := E_geoTransformAlong_congr he.1 (restrict U T)
  have hTransform := (congrArg (fun L : MarkedIdeal n (CMfd.of (n:=n) U)=>geoTransformAlong L (restrict U T)) hJeq).trans
    (geoTransformAlong_restrict U hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent T hT)
  refine ⟨hJT,hJCos.trans (congrArg (fun A : Set Y=>(Subtype.val : openPreimage T U→Y) ⁻¹' A) hCosQ),
    hJE.trans (congrArg MarkedIdeal.E hTransform),length_restrict U T,hZ,?_⟩
  intro p hp
  exact original_lower_data (X:=CMfd.of (n:=n) U) hn k J hJ hMax (restrict U T) hCan hZ p hp

private theorem native_lower_history (hn : 0<n) (k : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hState : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∃W : Set Y,IsComplexAnalyticSubset (n:=n) W ∧
        (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) W)
    (U : Opens X) (J : MarkedIdeal n (CMfd.of (n:=n) U))
    (hJeq : J=MarkedIdeal.pullback (Subtype.val : U→X) Q)
    (hJ : IsInvDomain (k+1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T)) :
    let R : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) (openPreimage T U)):=restrict U T
    let F : ResolutionInvariantSeq.ResolutionInvariant n k (ValTy k):=invFamily hn k
    IsGeoTestTower (barMarked J) R ∧
      (geoTransformAlong (barMarked J) R).cosupp=
        (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
      (geoTransformAlong (barMarked J) R).E=(geoTransformAlong Q T).E.map
        ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
      R.length=T.length ∧
      (∀p : openPreimage T U,level J R p=0 ∧ ¬ IsSpecial J R p ∧
        regimeRun (stepRegime J 0) R p=R.length) ∧
      ∀p∈(geoTransformAlong J R).cosupp,
        let V : Opens (CMfd.of (n:=n) U):=maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
        let B : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
        Seq.StepOneValueMasked.LowerDataL F J (lowerMarkedM J) 0
          (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p ∧
        IsGeoTestTower B (restrict V R) ∧
        (geoTransformAlong B (restrict V R)).cosupp=
          (Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' (geoTransformAlong (barMarked J) R).cosupp ∧
        (geoTransformAlong B (restrict V R)).E=(geoTransformAlong (barMarked J) R).E.map
          ((Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' ·) ∧
        B.d=(coeffMarkedAlong (barMarked J)).d ∧ (restrict V R).length=R.length ∧
        Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
          (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p≠⊤ ∧
        Seq.StepOneValueMasked.stepOneInvM F J R p=toLex (0,
          Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
            (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p) ∧
        ∀hm : R.proj p∈V,Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
          (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p=
          (((F.inv B (restrict V R) ⟨p,hm⟩ : ValTy k) : WithTop (ValTy k))) := by
  dsimp only
  obtain ⟨hb,hCos,hE,hLen,hZ,hPoint⟩:=lower_history hn k Q hQ hN hE hState U J hJeq hJ hMax T hT hCan
  refine ⟨hb,hCos,hE,hLen,hZ,fun p hp=>?_⟩
  obtain ⟨hm,hDom,hCanB,hTestB,hpB,hCosB,hEB,hMark,hLength,hValue⟩:=hPoint p hp
  let R : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) (openPreimage T U)):=restrict U T
  let V : Opens (CMfd.of (n:=n) U):=maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
  let B : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
  have hData : Seq.StepOneValueMasked.LowerDataL (invFamily hn k) J (lowerMarkedM J) 0
      (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p :=
    ⟨hm,hDom,hCanB,hpB⟩
  have hLV (ha : R.proj p∈V) :
      Seq.StepOneValueMasked.lowerValueL (invFamily hn k) J (lowerMarkedM J) 0
        (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p=
      ((((invFamily hn k).inv (X:=CMfd.of (n:=n) V) B (restrict V R) ⟨p,ha⟩ : ValTy k) : WithTop (ValTy k))) := by
    exact Seq.StepOneValueMasked.lowerValueL_eq_of_mem (s:=0)
      (T₀:=(.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U))) (T₁:=R)
      (invFamily hn k) J (lowerMarkedM J) ha
  refine ⟨hData,hTestB,hCosB,hEB,hMark,hLength,?_,?_,hLV⟩
  · rw [hLV hm]
    exact WithTop.coe_ne_top
  · exact hValue.trans (congrArg (fun z : WithTop (ValTy k)=>toLex ((0 : ℕ),z)) (hLV hm).symm)

private theorem geometry_from_original_functions
    {m : ℕ} {Xref : Type} [TopologicalSpace Xref]
    [ChartedSpace (ComplexModel m) Xref] [IsComplexManifold m Xref]
    (Wref : Set Xref) (hWref : IsComplexAnalyticSubset (n:=m) Wref)
    (aref : Xref) (hSing : aref∈singularSet (n:=m) Wref)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hN : Q.N=univ) (hI : Q.ideal.IsCoherent)
    {L : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector L)
    {r : ℕ} (a : Fin r ≃ L) (w : Fin r→CoordinateWord n)
    (hWords : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : L,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hMark : Q.d=weightedCommonMark (fun v : L=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ)
    {B : Type} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]
    (F₀ : L→B→ℂ) (hF₀ : ∀v x,HolomorphicAt n (F₀ v) x)
    (ρ : X→B) (hρ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ρ)
    (hHist : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ActualNativeOriginalFunctionTowerHistory S a w W Q F₀ hF₀ ρ hρ T) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj W) ∧
      (geoTransformAlong Q T).cosupp={z | ∀ℓ,
        hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ} ∧
      (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) (strictTransform n T.proj W) := by
  have hAt (x : X) (hx : x∈Q.cosupp) : ActualHistoricalNativePointPresentation S a w W Q x := by
    have hF := (hHist (.refl : BlowupTower X X) trivial).1 x hx
    obtain ⟨Θ,hΘsrc,hΘ0,Γ,_d,hFive,hSpan,hCompression,_hd,_hEq⟩ := hF
    have hid : strictTransform n (id : X→X) W=W := by
      rw [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hW.isClosed.closure_eq]
    exact hid ▸ ⟨Θ,hΘsrc,hΘ0,Γ,hFive,hSpan,hCompression⟩
  intro Y T hT
  obtain ⟨⟨hWT,_hNT,_hIT,_hMarkT,_hUpperT,hCutT,_hAtT,hSingT⟩,_hCentres⟩ :=
    actual_native_given_test_tower_state Wref hWref aref hSing W hW Q hN hI S a w hWords
      hPositive hOwn hMark hCut hUpper hAt T hT
  exact ⟨hWT,hCutT,hSingT⟩




section Original
variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- ORIGINAL-only zero regimes and actual original lowerMarkedB recursion on the SAME given histories. -/
theorem exists_original_zero_regime_phase
    (hn : 0<n) (W : Set M) (hW : IsComplexAnalyticSubset (n:=n) W) (a₀ : M)
    (ha₀ : a₀∈singularSet (n:=n) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a₀ a₀))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) a₀).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a₀ a₀)=0) :
    ∃(Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))(hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
      let Bset:=actualFixedFlatteningSet a₀ Ξ W
      let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
      ∃(G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) Bset) I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ))
        (V : Opens M)(η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        Ideal.span (range G.germs)=I ∧ PHS.neighborhood⊆Ξ.target ∧
        (∀z,(η z : M)=actualFlatteningInverseMap a₀ Ξ z.val) ∧
        ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
          (_hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
          (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
            (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
          let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
            actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
            (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
              (actualVertexEnumeration n I)
          let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
          let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
            (x : presentationOpen PHS)=>
              (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
          ∃hF₀ : ∀v x,HolomorphicAt n (F₀ v) x,
          ∃O : Opens (presentationOpen PHS),
            (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈O ∧
            (∃K : Set (presentationOpen PHS),IsCompact K ∧ (O : Set (presentationOpen PHS))⊆K) ∧
            (∀x∈O,x.val∈historicalNativeJetWindow P s hs0 δ) ∧
            let ι : O → M:=fun x=>(η x.val : M)
            let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS)
              (initialWeightedRecord PHS (fun z=>(η z : M)) ([] : List (Set M)))
            let Wphase:=(Subtype.val : O → presentationOpen PHS) ⁻¹'
              ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' Bset)
            ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι ∧
            Topology.IsOpenEmbedding ι ∧ a₀∈range ι ∧
            IsInvDomain n Q ∧ Q.N=univ ∧ Q.E=([] : List (Set M)).map (ι ⁻¹' ·) ∧
            Q.d=weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val) ∧
            IsComplexAnalyticSubset (n:=n) Wphase ∧
            Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
            (∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ≤
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ) ∧
            (∃(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
              IsCanonical Q ((CanonicalCentres.canonicalInvariant n).inv Q) T ∧ IsGeoResolution Q T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
              ActualNativeOriginalFunctionTowerHistory S aFull wFull Wphase Q F₀ hF₀
                (Subtype.val : O → presentationOpen PHS) contMDiff_subtype_val T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoResolution Q T →
              ActualHistoricalNativeTowerCentres Wphase T ∧
              ∀z : Y,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z)<
                toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀)) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
              IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj Wphase) ∧
              (geoTransformAlong Q T).cosupp={z | ∀ℓ,
                hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z ℓ=
                  hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
              IsGeoTestTower (barMarked Q) T ∧
              (geoTransformAlong (barMarked Q) T).cosupp=(geoTransformAlong Q T).cosupp ∧
              (geoTransformAlong (barMarked Q) T).E=(geoTransformAlong Q T).E ∧
              codimOnePartAlong (geoTransformAlong (barMarked Q) T).N
                (geoTransformAlong (barMarked Q) T).ideal (geoTransformAlong (barMarked Q) T).d=∅ ∧
              ∀y : Y,level Q T y=0 ∧ ¬ IsSpecial Q T y ∧
                regimeRun (stepRegime Q 0) T y=T.length) ∧
            (∀(k : ℕ),n≤k+1 → ∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
              IsCanonical Q ((invFamily hn (k+1)).inv Q) T →
              let U:=NonmonomialOrderTail.ordMask Q Q.d
              let J : MarkedIdeal n (CMfd.of (n:=n) U):=companionOf n (M:=CMfd.of (n:=n) U)
                (MarkedIdeal.pullback (Subtype.val : U→O) Q) Q.d
              J=MarkedIdeal.pullback (Subtype.val : U→O) Q ∧
              IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
              IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T) ∧
              let R : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) (openPreimage T U)):=restrict U T
              let F : ResolutionInvariantSeq.ResolutionInvariant n k (ValTy k):=invFamily hn k
              IsGeoTestTower (barMarked J) R ∧
                (geoTransformAlong (barMarked J) R).cosupp=
                  (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
                (geoTransformAlong (barMarked J) R).E=(geoTransformAlong Q T).E.map
                  ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
                R.length=T.length ∧
                (∀p : openPreimage T U,level J R p=0 ∧ ¬ IsSpecial J R p ∧
                  regimeRun (stepRegime J 0) R p=R.length) ∧
                ∀p∈(geoTransformAlong J R).cosupp,
                  let V : Opens (CMfd.of (n:=n) U):=maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
                  let B : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
                  Seq.StepOneValueMasked.LowerDataL F J (lowerMarkedM J) 0
                    (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p ∧
                  IsGeoTestTower B (restrict V R) ∧
                  (geoTransformAlong B (restrict V R)).cosupp=
                    (Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' (geoTransformAlong (barMarked J) R).cosupp ∧
                  (geoTransformAlong B (restrict V R)).E=(geoTransformAlong (barMarked J) R).E.map
                    ((Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' ·) ∧
                  B.d=(coeffMarkedAlong (barMarked J)).d ∧ (restrict V R).length=R.length ∧
                  Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                    (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p≠⊤ ∧
                  Seq.StepOneValueMasked.stepOneInvM F J R p=toLex (0,
                    Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                      (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p) ∧
                  ∀hm : R.proj p∈V,Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                    (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p=
                    (((F.inv B (restrict V R) ⟨p,hm⟩ : ValTy k) : WithTop (ValTy k)))) := by
  -- Share the fixed result proposition while choosing the independent source witnesses.
  let g1ZeroGoalProp : Prop:=
      ∃(Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))(hΨ0 : Ψ.toFun 0=0),
        let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
        let Bset:=actualFixedFlatteningSet a₀ Ξ W
        let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
        ∃(G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
          (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
          (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) Bset) I G
            (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ))
          (V : Opens M)(η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
          Ideal.span (range G.germs)=I ∧ PHS.neighborhood⊆Ξ.target ∧
          (∀z,(η z : M)=actualFlatteningInverseMap a₀ Ξ z.val) ∧
          ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
            (_hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
            (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
              (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
            let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
              actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
              (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
                (actualVertexEnumeration n I)
            let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
            let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
              (x : presentationOpen PHS)=>
                (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
            ∃hF₀ : ∀v x,HolomorphicAt n (F₀ v) x,
            ∃O : Opens (presentationOpen PHS),
              (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈O ∧
              (∃K : Set (presentationOpen PHS),IsCompact K ∧ (O : Set (presentationOpen PHS))⊆K) ∧
              (∀x∈O,x.val∈historicalNativeJetWindow P s hs0 δ) ∧
              let ι : O → M:=fun x=>(η x.val : M)
              let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS)
                (initialWeightedRecord PHS (fun z=>(η z : M)) ([] : List (Set M)))
              let Wphase:=(Subtype.val : O → presentationOpen PHS) ⁻¹'
                ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' Bset)
              ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι ∧
              Topology.IsOpenEmbedding ι ∧ a₀∈range ι ∧
              IsInvDomain n Q ∧ Q.N=univ ∧ Q.E=([] : List (Set M)).map (ι ⁻¹' ·) ∧
              Q.d=weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
                (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val) ∧
              IsComplexAnalyticSubset (n:=n) Wphase ∧
              Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
                hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
              (∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ≤
                hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ) ∧
              (∃(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
                IsCanonical Q ((CanonicalCentres.canonicalInvariant n).inv Q) T ∧ IsGeoResolution Q T) ∧
              (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
                ActualNativeOriginalFunctionTowerHistory S aFull wFull Wphase Q F₀ hF₀
                  (Subtype.val : O → presentationOpen PHS) contMDiff_subtype_val T) ∧
              (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoResolution Q T →
                ActualHistoricalNativeTowerCentres Wphase T ∧
                ∀z : Y,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z)<
                  toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀)) ∧
              (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
                IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj Wphase) ∧
                (geoTransformAlong Q T).cosupp={z | ∀ℓ,
                  hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z ℓ=
                    hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
                IsGeoTestTower (barMarked Q) T ∧
                (geoTransformAlong (barMarked Q) T).cosupp=(geoTransformAlong Q T).cosupp ∧
                (geoTransformAlong (barMarked Q) T).E=(geoTransformAlong Q T).E ∧
                codimOnePartAlong (geoTransformAlong (barMarked Q) T).N
                  (geoTransformAlong (barMarked Q) T).ideal (geoTransformAlong (barMarked Q) T).d=∅ ∧
                ∀y : Y,level Q T y=0 ∧ ¬ IsSpecial Q T y ∧
                  regimeRun (stepRegime Q 0) T y=T.length) ∧
              (∀(k : ℕ),n≤k+1 → ∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
                IsCanonical Q ((invFamily hn (k+1)).inv Q) T →
                let U:=NonmonomialOrderTail.ordMask Q Q.d
                let J : MarkedIdeal n (CMfd.of (n:=n) U):=companionOf n (M:=CMfd.of (n:=n) U)
                  (MarkedIdeal.pullback (Subtype.val : U→O) Q) Q.d
                J=MarkedIdeal.pullback (Subtype.val : U→O) Q ∧
                IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
                IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T) ∧
                let R : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) (openPreimage T U)):=restrict U T
                let F : ResolutionInvariantSeq.ResolutionInvariant n k (ValTy k):=invFamily hn k
                IsGeoTestTower (barMarked J) R ∧
                  (geoTransformAlong (barMarked J) R).cosupp=
                    (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
                  (geoTransformAlong (barMarked J) R).E=(geoTransformAlong Q T).E.map
                    ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
                  R.length=T.length ∧
                  (∀p : openPreimage T U,level J R p=0 ∧ ¬ IsSpecial J R p ∧
                    regimeRun (stepRegime J 0) R p=R.length) ∧
                  ∀p∈(geoTransformAlong J R).cosupp,
                    let V : Opens (CMfd.of (n:=n) U):=maskB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
                    let B : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB J (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) (R.proj p)
                    Seq.StepOneValueMasked.LowerDataL F J (lowerMarkedM J) 0
                      (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p ∧
                    IsGeoTestTower B (restrict V R) ∧
                    (geoTransformAlong B (restrict V R)).cosupp=
                      (Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' (geoTransformAlong (barMarked J) R).cosupp ∧
                    (geoTransformAlong B (restrict V R)).E=(geoTransformAlong (barMarked J) R).E.map
                      ((Subtype.val : openPreimage R V→ openPreimage T U) ⁻¹' ·) ∧
                    B.d=(coeffMarkedAlong (barMarked J)).d ∧ (restrict V R).length=R.length ∧
                    Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                      (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p≠⊤ ∧
                    Seq.StepOneValueMasked.stepOneInvM F J R p=toLex (0,
                      Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                        (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p) ∧
                    ∀hm : R.proj p∈V,Seq.StepOneValueMasked.lowerValueL F J (lowerMarkedM J) 0
                      (.refl : BlowupTower (CMfd.of (n:=n) U) (CMfd.of (n:=n) U)) R p=
                      (((F.inv B (restrict V R) ⟨p,hm⟩ : ValTy k) : WithTop (ValTy k))))
  change g1ZeroGoalProp
  obtain ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
      hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop,hInitial⟩ :=
    exists_original_initial_companion_recursion (n:=n) (M:=M) hn W hW a₀ ha₀ Φ hΦsrc hΦ0
  let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
  let Bset:=actualFixedFlatteningSet a₀ Ξ W
  let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
      (x : presentationOpen PHS)=>
    (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
  let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS)
    (initialWeightedRecord PHS (fun z=>(η z : M)) [])
  let Wphase:=(Subtype.val : O→presentationOpen PHS) ⁻¹'
    ((Subtype.val : presentationOpen PHS→ComplexModel n) ⁻¹' Bset)
  have hEmpty : Q.E=[] := by simpa only [List.map_nil] using hBoundary
  have hWords (j : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound)) :
      wordExponent (wFull j)=(aFull j).val := by
    let v:=actualVertexEnumeration n I (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j)
    change wordExponent (wordOfExponent v.val)=v.val
    exact wordExponent_wordOfExponent v.val
  have hOwn:=HironakaActualHistoricalInitialFiveLawWindow.actual_initial_vertex_heads_have_historical_owner
    MonomialOrder.degLex (analyticZeroTaylorIdeal n I) aFull wFull hWords
  have hProduct : weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val)≠0 := by
    rw [←hQMark]
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hDom.one_le_d)
  have hPositive (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      0<normalExponentDegree v.val :=
    Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp hProduct) v (Finset.mem_univ v))
  have hGeom : ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
      IsComplexAnalyticSubset (n:=n) (strictTransform n T.proj Wphase) ∧
      (geoTransformAlong Q T).cosupp={z | ∀ℓ,
        hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
      (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) (strictTransform n T.proj Wphase) := by
    intro Y T hT
    exact geometry_from_original_functions (X:=CMfd.of (n:=n) O) W hW a₀ ha₀ Wphase hWphase Q hN
      hDom.isWellFormed.isCoherent S aFull wFull hWords hPositive hOwn hQMark hCut hUpper F₀ hF₀
      (Subtype.val : O→presentationOpen PHS) contMDiff_subtype_val (fun {Y} S hS=>hHist Y S hS) T hT
  have hState : ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
      ∃A : Set Y,IsComplexAnalyticSubset (n:=n) A ∧
        (geoTransformAlong Q T).cosupp⊆singularSet (n:=n) A := by
    intro Y T hT
    exact ⟨strictTransform n T.proj Wphase,(hGeom T hT).1,(hGeom T hT).2.2⟩
  have hZero : ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
      ∀y : Y,stepRegime Q 0 T y := by
    intro Y T hT y
    exact ((zero_geometry (X:=CMfd.of (n:=n) O) Q hDom hN hEmpty hState T hT).2 y).2.2
  dsimp only [g1ZeroGoalProp]
  refine ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
    hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop,?_,?_⟩
  · intro Y T hT
    obtain ⟨hWT,hCutT,_hSingT⟩:=hGeom T hT
    obtain ⟨hbT,hbCos,hbE⟩:=bar_history (X:=CMfd.of (n:=n) O) Q hDom T hT
    obtain ⟨hZ,hCurrent⟩:=zero_geometry (X:=CMfd.of (n:=n) O) Q hDom hN hEmpty hState T hT
    refine ⟨hWT,hCutT,hbT,hbCos,hbE,hZ,fun y=>?_⟩
    exact ⟨(hCurrent y).1,(hCurrent y).2.1,zero_run (X:=CMfd.of (n:=n) O) Q hZero T hT y⟩
  · intro k hnk Y T hCanT
    have hInitialData:=hInitial k hnk Y T hCanT
    have hJ:=hInitialData.1
    have hJD:=hInitialData.2.1
    have hMax:=hInitialData.2.2.1
    have hStepCan:=hInitialData.2.2.2.2.2.1
    have hDomk : IsInvDomain (k+1) Q := by
      refine ⟨hDom.isWellFormed,?_,hDom.one_le_d,hDom.isNonzeroAlongAt⟩
      intro x hx
      obtain ⟨j,hj,hReg⟩:=hDom.dimLE x hx
      exact ⟨j,hj.trans hnk,hReg⟩
    have hTest:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
      (invFamily hn (k+1)).isInvValue hDomk T hCanT
    refine ⟨hJ,hJD,hMax,hStepCan,?_⟩
    let U : Opens (CMfd.of (n:=n) O):=NonmonomialOrderTail.ordMask Q Q.d
    let J : MarkedIdeal n (CMfd.of (n:=n) U):=companionOf n (M:=CMfd.of (n:=n) U)
      (MarkedIdeal.pullback (Subtype.val : U→O) Q) Q.d
    exact native_lower_history (X:=CMfd.of (n:=n) O) hn k Q hDom hN hEmpty hState
      U J hJ hJD hMax T hTest hStepCan

end Original

end
end Hironaka.HironakaActualHistoricalOriginalZeroRegime
