import Hironaka.Resolution.HironakaG1LocalizedLaterBornCanonical
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Resolution.HironakaG3RRawRegimeLocality

/-! The literal finite Step One read and recursive comparisons at the next localized born cut. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
namespace Hironaka.HironakaG1LocalizedLaterBornRead

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain StepOneEmptyPrefix
  BlowupTowerIsomorphism InvDomainMemberRestriction HomogenizedIdealAlong CoefficientIdealRestriction DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG1OriginalUnequalMarkCanonical
  HironakaG1RecursiveMemberValueTransport HironakaG1LocalizedLaterBornCanonical
open HironakaG3RRawRegimeLocality RelativePrincipalizationSpan
open Hironaka.HolomorphicIdealSheaves

set_option maxHeartbeats 1200000 in
/-- An original Step One positive run starting at the base reads the actual
positive-member invariant on every smaller window through its anchor. The
restricted history is canonical for that literal selected record. -/
theorem localized_positive_stepOne_finite_read {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J : MarkedIdeal n X) (hJ : IsInvDomain (k + 1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hl : level J T y = b + 1) (hNS : ¬ IsSpecial J T y)
    (hRun : regimeRun (stepRegime J (b + 1)) T y = T.length)
    (W : Opens X) (hW : W ≤ maskA J (.refl : BlowupTower X X) (T.proj y))
    (hpW : T.proj y ∈ W) :
    let K := positiveMemberOn J (.refl : BlowupTower X X) (T.proj y) W
    let V := BlowupTowerTransforms.restrict W T
    let z : openPreimage T W := ⟨y, hpW⟩
    IsInvDomain k K ∧ IsCanonical K ((invFamily hn k).inv K) V ∧
      z ∈ (geoTransformAlong K V).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
        toLex (b + 1, ((invFamily hn k).inv K V z : WithTop (ValTy k))) := by
  intro K V z
  let R := invFamily hn k
  let O := maskA J (.refl : BlowupTower X X) (T.proj y)
  let B := barMarked (X := X) J
  let K₀ := memberRestrict B (membersThrough B.E (origMembers J (.refl : BlowupTower X X)) (T.proj y))
  obtain ⟨hBT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R J hJ hMax hn T hCan
  have hBC := (Seq.StepOneBridge.isCanonical_iff R J hJ hMax hn T).mp hCan
  have hLower := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := k + 1) J R hJ.isWellFormed hJ.one_le_d
    hn hMax hJ.dimLE T hBT hBC y (hCos.symm ▸ hy) hNS
  have hSplit := split_of_length_le T T.length le_rfl
  have hAtBase : Seq.StepOneValueMasked.LowerDataL R J (lowerMarkedM J) (b + 1) (.refl : BlowupTower X X) T y := by
    rw [hl, hRun] at hLower
    change Seq.StepOneValueMasked.LowerDataL R J (lowerMarkedM J) (b + 1) (split T T.length).2.1 (split T T.length).2.2 y at hLower
    rw [hSplit] at hLower
    exact hLower
  obtain ⟨hp, hDom, hLowerCan, hz⟩ := hAtBase
  have hB : B.IsWellFormed := isWellFormed_barMarked J hJ.isWellFormed
  have hK₀ : K₀.IsWellFormed := isWellFormed_memberRestrict hn hB _
  have hDomO : IsInvDomain k (positiveMemberOn J (.refl : BlowupTower X X) (T.proj y) O) := hDom
  have hCanO : IsCanonical (positiveMemberOn J (.refl : BlowupTower X X) (T.proj y) O)
      (R.inv (positiveMemberOn J (.refl : BlowupTower X X) (T.proj y) O))
      (BlowupTowerTransforms.restrict O T) := hLowerCan
  obtain ⟨hKW, hCanW, hVal⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hK₀.isCoherent hW hDomO T hCanO
  have hHol : ∀ x f, K₀.ideal.mem x f → HolomorphicAt n f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf
  have hzO : (⟨y, hp⟩ : openPreimage T O) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) K₀)
        (BlowupTowerTransforms.restrict O T)).cosupp := hz
  rw [cosupp_restrict_raw K₀ hHol O T] at hzO
  have hzW : z ∈ (geoTransformAlong K V).cosupp := by
    change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K₀)
      (BlowupTowerTransforms.restrict W T)).cosupp
    rw [cosupp_restrict_raw K₀ hHol W T]
    exact hzO
  refine ⟨hKW, hCanW, hzW, ?_⟩
  have hRead := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R J (lowerMarkedM J) T hNS
  rw [hl, hRun] at hRead
  change _ = toLex (b + 1, Seq.StepOneValueMasked.lowerValueL R J (lowerMarkedM J) (b + 1)
    (split T T.length).2.1 (split T T.length).2.2 y) at hRead
  rw [hSplit, Seq.StepOneValueMasked.lowerValueL_eq_of_mem R J (lowerMarkedM J) hp] at hRead
  exact hRead.trans (congrArg (fun v : ValTy k => toLex (b + 1, (v : WithTop (ValTy k))))
    (hVal z hzW).symm)

/-- The two literal recursive contact records give identical strict order
cuts, even across different canonical continuations. Canonicality on the
supported side follows from the normalized comparisons. -/
theorem contact_recursive_strict_order_on_canonical_suffixes {n k : ℕ} (hn : 0 < n)
    {X Y Z : CMfd.{0} n} (C S : MarkedIdeal n X)
    (hC : IsInvDomain k C) (hS : IsInvDomain k S) (hClass : LocWPEquiv C S) (hN : C.N = S.N)
    (hExp : ∀ F ∈ C.E, ∀ z ∈ C.cosupp, z ∈ F →
      S.d * divExpAlong n C.N C.ideal F z =
        C.d * divExpAlong n S.N S.ideal F z)
    (T : BlowupTower X Y) (V : BlowupTower X Z)
    (hTC : IsCanonical C ((invFamily hn k).inv C) T)
    (hVC : IsCanonical C ((invFamily hn k).inv C) V) :
    IsCanonical S ((invFamily hn k).inv S) T ∧ IsCanonical S ((invFamily hn k).inv S) V ∧
      ∀ y ∈ (geoTransformAlong C T).cosupp, ∀ z ∈ (geoTransformAlong C V).cosupp,
        ((invFamily hn k).inv C T y < (invFamily hn k).inv C V z ↔
          (invFamily hn k).inv S T y < (invFamily hn k).inv S V z) := by
  have hDim := SameCarrierDim.of_N_eq hN
  have hTS := (invFamily_isCanonical_iff_of_local hn C S hC hS hClass hDim hExp T).mp hTC
  have hVS := (invFamily_isCanonical_iff_of_local hn C S hC hS hClass hDim hExp V).mp hVC
  exact ⟨hTS, hVS, canonicalTwoPairCuts_invFamily hn k C S C S hC hS hC hS
    hClass hDim hExp hClass hDim hExp rfl rfl trivial trivial trivial trivial T V hTC hTS hVC hVS⟩

set_option maxHeartbeats 1000000 in
/-- Apply the literal finite read to the geometric next-born witness. The
same actual restricted tower also transfers strict recursive contact comparisons
whenever it is a canonical contact continuation. -/
theorem localized_born_witness_read {n k q b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (u : X → ℂ)
    (hJ : IsInvDomain (k + 1) J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hl : level J T y = b + 1) (hNS : ¬ IsSpecial J T y)
    (hRun : regimeRun (stepRegime J (b + 1)) T y = T.length)
    (hWitness : LocalizedBornWitness (k := k + 1) (l := q + 1) hn J R (T.proj y) u) :
    let H : BlowupTower X X := .refl
    ∃ (W : Opens X) (hpW : T.proj y ∈ W), W ≤ maskA J H (T.proj y) ∧
      W ≤ maskA R H (T.proj y) ∧
      let K := positiveMemberOn J H (T.proj y) W
      let S := positiveMemberOn R H (T.proj y) W
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      let V := BlowupTowerTransforms.restrict W T
      let z : openPreimage T W := ⟨y, hpW⟩
      IsCanonical K ((invFamily hn k).inv K) V ∧
      z ∈ (geoTransformAlong K V).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y =
        toLex (b + 1, ((invFamily hn k).inv K V z : WithTop (ValTy k))) ∧
      (IsCanonical C ((invFamily hn q).inv C) V →
        IsCanonical S ((invFamily hn q).inv S) V ∧
        ∀ x ∈ (geoTransformAlong C V).cosupp, ∀ x' ∈ (geoTransformAlong C V).cosupp,
          ((invFamily hn q).inv C V x < (invFamily hn q).inv C V x' ↔
            (invFamily hn q).inv S V x < (invFamily hn q).inv S V x')) := by
  intro H
  obtain ⟨W, hpW, hWJ, hWR, _, _, hN, _, hClass, _, _, _, hC, hS, hExp, _⟩ := hWitness
  obtain ⟨_, hKCan, hz, hRead⟩ :=
    localized_positive_stepOne_finite_read hn J hJ hMax T hCan y hy hl hNS hRun W hWJ hpW
  refine ⟨W, hpW, hWJ, hWR, hKCan, hz, hRead, ?_⟩
  intro hCCan
  obtain ⟨hSCan, _, hOrd⟩ := contact_recursive_strict_order_on_canonical_suffixes hn _ _
    hC hS hClass hN hExp _ _ hCCan hCCan
  exact ⟨hSCan, hOrd⟩

end Hironaka.HironakaG1LocalizedLaterBornRead
