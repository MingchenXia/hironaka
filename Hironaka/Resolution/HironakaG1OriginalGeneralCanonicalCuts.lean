import Hironaka.Resolution.HironakaG1OriginalTwoPairCanonicalCuts
import Hironaka.Resolution.HironakaG1DifferentCarrierCompanions
import Hironaka.Resolution.HironakaG1CrossHeadGammaCuts
import Hironaka.Invariant.GeneralCompare
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralAdmissible

/-! The genuine general-value layer of unequal-native-mark canonical cuts.
Blueprint FIRST: hironaka-g1-original-general-canonical-cuts.tex.
Actual canonical histories for BOTH paired records remain explicit. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalGeneralCanonicalCuts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  HomogenizedIdealAlong NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime StepOneRegime
  CompanionRebase CompanionReductionAlong GeneralValue GeneralCompare MaxOrderValue
  InvDomainTowerAlong InvDomainCompanion HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8SpecialLoci HironakaG1IndependentContactScaledHistory
  HironakaG1DifferentCarrierCompanions HironakaG1OriginalTwoPairCanonicalCuts
  HironakaG1CrossHeadGammaCuts DivisorExponentAlong MonomialCaseAlong

variable {n k : ℕ} {Λ : Type} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)

private theorem companion_on_common_open (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    {X Z Y : CMfd.{0} n} (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (o : ℕ) (ho : 1 ≤ o) (H : BlowupTower X Z) (hH : IsGeoTestTower P H)
    (T : BlowupTower Z Y) (x : Y) (hL : GenLowerData M k P o H T x)
    (W : Opens Z) (hW : W ≤ ordMask (geoTransformAlong P H) o) (hxW : T.proj x ∈ W) :
    let C := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Z) (geoTransformAlong P H)) o
    IsInvDomain k C ∧ IsMaximalOrderAlong C.N C.ideal C.d ∧
      IsCanonical C (M C) (restrict W T) ∧
      (⟨x, hxW⟩ : openPreimage T W) ∈ (geoTransformAlong C (restrict W T)).cosupp ∧
      genLowerValue M P o H T x = ((M C (restrict W T) ⟨x, hxW⟩ : Λ) : WithTop Λ) := by
  obtain ⟨hx, hDom, hMax, hCan, hCos⟩ := hL
  have hPH := isInvDomain_geoTransformAlong hP H hH
  have hWF := (isInvDomain_companionAlong hn hPH ho).isWellFormed
  have e := compAt_eq_pullback hn (𝔪 := P) o H hPH
  rw [e] at hDom hMax hCan hCos
  obtain ⟨hDomW, hMaxW, hCanW, _⟩ := value_restrict_nestedOpens hM hWF.isCoherent hW
    hDom hMax T hCan
  obtain ⟨hVal, hCosW⟩ := value_eq_of_two_opens hM hWF.isClosedSubmanifold_N hWF.isCoherent T
    hDom hMax hCan hDomW hMaxW hCanW hx hxW hCos
  have eW := pullback_val_companionOf hn hPH.isWellFormed hPH.isNonzeroAlongAt W o
  rw [eW] at hDomW hMaxW hCanW hCosW hVal
  refine ⟨hDomW, hMaxW, hCanW, hCosW, ?_⟩
  rw [genLowerValue_eq_of_mem M P hx, e]
  exact congrArg (fun v : Λ => (v : WithTop Λ)) hVal

/-- Four ACTUAL companion canonical tails compare on the genuine two mask
intersections, using only the honest maximal-order two-pair cut IH. -/
theorem genLowerValue_twoPair_cut (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hCuts : CanonicalMaxOrderTwoPairCuts k M)
    {X₁ X₂ Z₁ Z₂ Y₁ Y₂ : CMfd.{0} n}
    (P Q : MarkedIdeal n X₁) (R S : MarkedIdeal n X₂)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q) (hR : IsInvDomain k R) (hS : IsInvDomain k S)
    (hPQ : LocWPEquiv P Q) (hDimPQ : SameCarrierDim P Q)
    (hXPQ : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (hRS : LocWPEquiv R S) (hDimRS : SameCarrierDim R S)
    (hXRS : ∀ H ∈ R.E, ∀ x ∈ R.cosupp, x ∈ H →
      S.d * divExpAlong n R.N R.ideal H x = R.d * divExpAlong n S.N S.ideal H x)
    (hdPR : P.d = R.d) (hdQS : Q.d = S.d)
    (o p : ℕ) (ho : 1 ≤ o) (hp : 1 ≤ p) (hscale : Q.d * o = P.d * p)
    (H₁ : BlowupTower X₁ Z₁) (H₂ : BlowupTower X₂ Z₂)
    (hH₁ : IsGeoTestTower P H₁) (hH₂ : IsGeoTestTower R H₂)
    (T₁ : BlowupTower Z₁ Y₁) (T₂ : BlowupTower Z₂ Y₂) (x : Y₁) (y : Y₂)
    (hLP : GenLowerData M k P o H₁ T₁ x) (hLQ : GenLowerData M k Q p H₁ T₁ x)
    (hLR : GenLowerData M k R o H₂ T₂ y) (hLS : GenLowerData M k S p H₂ T₂ y) :
    (genLowerValue M P o H₁ T₁ x < genLowerValue M R o H₂ T₂ y ↔
      genLowerValue M Q p H₁ T₁ x < genLowerValue M S p H₂ T₂ y) := by
  let P₀ := geoTransformAlong P H₁
  let Q₀ := geoTransformAlong Q H₁
  let R₀ := geoTransformAlong R H₂
  let S₀ := geoTransformAlong S H₂
  let W₁ := ordMask P₀ o ⊓ ordMask Q₀ p
  let W₂ := ordMask R₀ o ⊓ ordMask S₀ p
  let C₁ := companionOf n (M := CMfd.of (n := n) W₁) (MarkedIdeal.pullback (Subtype.val : W₁ → Z₁) P₀) o
  let D₁ := companionOf n (M := CMfd.of (n := n) W₁) (MarkedIdeal.pullback (Subtype.val : W₁ → Z₁) Q₀) p
  let C₂ := companionOf n (M := CMfd.of (n := n) W₂) (MarkedIdeal.pullback (Subtype.val : W₂ → Z₂) R₀) o
  let D₂ := companionOf n (M := CMfd.of (n := n) W₂) (MarkedIdeal.pullback (Subtype.val : W₂ → Z₂) S₀) p
  have hxW : T₁.proj x ∈ W₁ := ⟨hLP.choose, hLQ.choose⟩
  have hyW : T₂.proj y ∈ W₂ := ⟨hLR.choose, hLS.choose⟩
  obtain ⟨hC₁, hmC₁, hcC₁, hxC₁, hvP⟩ := companion_on_common_open M hM hn P hP o ho H₁ hH₁ T₁ x hLP W₁ inf_le_left hxW
  have hH₁Q : IsGeoTestTower Q H₁ := (hPQ.wEquiv.2 H₁).1.mp hH₁
  obtain ⟨hD₁, hmD₁, hcD₁, _hxD₁, hvQ⟩ := companion_on_common_open M hM hn Q hQ p hp H₁ hH₁Q T₁ x hLQ W₁ inf_le_right hxW
  obtain ⟨hC₂, hmC₂, hcC₂, hyC₂, hvR⟩ := companion_on_common_open M hM hn R hR o ho H₂ hH₂ T₂ y hLR W₂ inf_le_left hyW
  have hH₂S : IsGeoTestTower S H₂ := (hRS.wEquiv.2 H₂).1.mp hH₂
  obtain ⟨hD₂, hmD₂, hcD₂, _hyD₂, hvS⟩ := companion_on_common_open M hM hn S hS p hp H₂ hH₂S T₂ y hLS W₂ inf_le_right hyW
  have hP₀ := isInvDomain_geoTransformAlong hP H₁ hH₁
  have hQ₀ := isInvDomain_geoTransformAlong hQ H₁ hH₁Q
  have hR₀ := isInvDomain_geoTransformAlong hR H₂ hH₂
  have hS₀ := isInvDomain_geoTransformAlong hS H₂ hH₂S
  have hPQ₀ := hPQ.geoTransformAlong H₁ hH₁
  have hRS₀ := hRS.geoTransformAlong H₂ hH₂
  have hDimPQ₀ := sameCarrierDim_geoTransformAlong hP.isWellFormed hQ.isWellFormed hPQ.wEquiv hDimPQ H₁ hH₁
  have hDimRS₀ := sameCarrierDim_geoTransformAlong hR.isWellFormed hS.isWellFormed hRS.wEquiv hDimRS H₂ hH₂
  have hXPQ₀ : ∀ H ∈ P₀.E, ∀ z ∈ P₀.cosupp, z ∈ H →
      Q₀.d * divExpAlong n P₀.N P₀.ideal H z = P₀.d * divExpAlong n Q₀.N Q₀.ideal H z := by
    simpa only [P₀, Q₀, d_geoTransformAlong] using
      scaled_exponents_sameCarrierDim P Q hP hQ hPQ hDimPQ hXPQ H₁ hH₁
  have hXRS₀ : ∀ H ∈ R₀.E, ∀ z ∈ R₀.cosupp, z ∈ H →
      S₀.d * divExpAlong n R₀.N R₀.ideal H z = R₀.d * divExpAlong n S₀.N S₀.ideal H z := by
    simpa only [R₀, S₀, d_geoTransformAlong] using
      scaled_exponents_sameCarrierDim R S hR hS hRS hDimRS hXRS H₂ hH₂
  have hscale₁ : Q₀.d * o = P₀.d * p := by simpa only [P₀, Q₀, d_geoTransformAlong] using hscale
  have hscale₂ : S₀.d * o = R₀.d * p := by simpa only [R₀, S₀, d_geoTransformAlong, ← hdPR, ← hdQS] using hscale
  obtain ⟨_, _, hCD₁, hDimCD₁, _hECD₁, hXCD₁⟩ :=
    masked_companion_class_sameCarrierDim hn P₀ Q₀ hP₀ hQ₀ hPQ₀ hDimPQ₀ hXPQ₀ o p ho hp hscale₁
  obtain ⟨_, _, hCD₂, hDimCD₂, _hECD₂, hXCD₂⟩ :=
    masked_companion_class_sameCarrierDim hn R₀ S₀ hR₀ hS₀ hRS₀ hDimRS₀ hXRS₀ o p ho hp hscale₂
  have hCC : C₁.d = C₂.d := by
    simp only [C₁, C₂, companionOf, companionAlong_d]
    change (if o < P₀.d then o * (P₀.d-o) else o) = (if o < R₀.d then o * (R₀.d-o) else o)
    simp only [P₀, R₀, d_geoTransformAlong, hdPR]
  have hDD : D₁.d = D₂.d := by
    simp only [D₁, D₂, companionOf, companionAlong_d]
    change (if p < Q₀.d then p * (Q₀.d-p) else p) = (if p < S₀.d then p * (S₀.d-p) else p)
    simp only [Q₀, S₀, d_geoTransformAlong, hdQS]
  have hCut := hCuts C₁ D₁ C₂ D₂ hC₁ hD₁ hC₂ hD₂ hCD₁ hDimCD₁ hXCD₁ hCD₂ hDimCD₂ hXCD₂ hCC hDD
    hmC₁ hmD₁ hmC₂ hmD₂ (restrict W₁ T₁) (restrict W₂ T₂) hcC₁ hcD₁ hcC₂ hcD₂ ⟨x, hxW⟩ hxC₁ ⟨y, hyW⟩ hyC₂
  rw [hvP, hvQ, hvR, hvS]
  simpa only [WithTop.coe_lt_coe] using hCut

/-- The genuine general value preserves the ordinary two-pair cut
property on ACTUAL canonical histories, with no lower-output packet. -/
theorem canonicalTwoPairCuts_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hCuts : CanonicalMaxOrderTwoPairCuts k M) : CanonicalTwoPairCuts k (genInv M) := by
  intro X₁ X₂ P Q R S hP hQ hR hS hPQ hDimPQ hXPQ hRS hDimRS hXRS hdPR hdQS _ _ _ _
    Y₁ Y₂ T₁ T₂ hcP hcQ hcR hcS x hx y hy
  change (genInv M P T₁ x < genInv M R T₂ y ↔ genInv M Q T₁ x < genInv M S T₂ y)
  have hTP := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hP T₁ hcP
  have hTQ := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hQ T₁ hcQ
  have hTR := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hR T₂ hcR
  have hTS := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hS T₂ hcS
  have hxQ : x ∈ (geoTransformAlong Q T₁).cosupp := (hPQ.geoTransformAlong T₁ hTP).cosupp_eq_base ▸ hx
  have hyS : y ∈ (geoTransformAlong S T₂).cosupp := (hRS.geoTransformAlong T₂ hTR).cosupp_eq_base ▸ hy
  have hRaw₁ := scaled_raw_sameCarrierDim hn P Q hP hQ hPQ hDimPQ hXPQ T₁ hTP x hx
  have hRaw₂ := scaled_raw_sameCarrierDim hn R S hR hS hRS hDimRS hXRS T₂ hTR y hy
  rw [← hdPR, ← hdQS] at hRaw₂
  have hd := hP.one_le_d
  have he := hQ.one_le_d
  have hLt : nmOrd (geoTransformAlong P T₁) x < nmOrd (geoTransformAlong R T₂) y ↔
      nmOrd (geoTransformAlong Q T₁) x < nmOrd (geoTransformAlong S T₂) y := by
    constructor <;> intro h <;> nlinarith only [hRaw₁, hRaw₂, hd, he, h]
  have hGt : nmOrd (geoTransformAlong R T₂) y < nmOrd (geoTransformAlong P T₁) x ↔
      nmOrd (geoTransformAlong S T₂) y < nmOrd (geoTransformAlong Q T₁) x := by
    constructor <;> intro h <;> nlinarith only [hRaw₁, hRaw₂, hd, he, h]
  rcases lt_trichotomy (nmOrd (geoTransformAlong P T₁) x) (nmOrd (geoTransformAlong R T₂) y) with h | htie | h
  · have hA : genInv M P T₁ x < genInv M R T₂ y := by
      rw [genInv, genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl h
    have hB : genInv M Q T₁ x < genInv M S T₂ y := by
      rw [genInv, genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl (hLt.mp h)
    exact iff_of_true hA hB
  · by_cases hz : nmOrd (geoTransformAlong P T₁) x = 0
    · have hw : nmOrd (geoTransformAlong R T₂) y = 0 := htie.symm.trans hz
      have hzQ : nmOrd (geoTransformAlong Q T₁) x = 0 := by
        rw [hz, Nat.mul_zero] at hRaw₁
        nlinarith only [hRaw₁, hd]
      have hwS : nmOrd (geoTransformAlong S T₂) y = 0 := by
        rw [hw, Nat.mul_zero] at hRaw₂
        nlinarith only [hRaw₂, hd]
      have hPT := isInvDomain_geoTransformAlong hP T₁ hTP
      have hQT := isInvDomain_geoTransformAlong hQ T₁ hTQ
      have hRT := isInvDomain_geoTransformAlong hR T₂ hTR
      have hET₁ := E_geoTransformAlong_eq hPQ.wEquiv.1 T₁
      have hET₂ := E_geoTransformAlong_eq hRS.wEquiv.1 T₂
      have hDTP : (geoTransformAlong P T₁).d = (geoTransformAlong R T₂).d := by
        simpa only [d_geoTransformAlong] using hdPR
      have hDTQ : (geoTransformAlong Q T₁).d = (geoTransformAlong S T₂).d := by
        simpa only [d_geoTransformAlong] using hdQS
      have hIX₁ := scaled_indexed_exponents_sameCarrierDim P Q hP hQ hPQ hDimPQ hXPQ T₁ hTP x hx
      have hIX₂ := scaled_indexed_exponents_sameCarrierDim R S hR hS hRS hDimRS hXRS T₂ hTR y hy
      have hGamma := gamma_cut_iff_across_heads hn (geoTransformAlong P T₁) (geoTransformAlong Q T₁)
        (geoTransformAlong R T₂) (geoTransformAlong S T₂) hPT hQT hRT hET₁ hET₂ hDTP hDTQ
        x y hx hy hz hw (by simpa only [d_geoTransformAlong] using hIX₁)
        (by simpa only [d_geoTransformAlong] using hIX₂)
      rw [genInv_of_nmOrd_eq_zero M P T₁ hz, genInv_of_nmOrd_eq_zero M R T₂ hw,
        genInv_of_nmOrd_eq_zero M Q T₁ hzQ, genInv_of_nmOrd_eq_zero M S T₂ hwS]
      simpa only [Prod.Lex.toLex_lt_toLex, lt_irrefl, true_and, false_or,
        Sum.Lex.toLex_lt_toLex, Sum.lex_inl_inl] using hGamma
    · let o := nmOrd (geoTransformAlong P T₁) x
      let p := nmOrd (geoTransformAlong Q T₁) x
      let r₁ := regimeRun (OrdRegime P o) T₁ x
      let r₂ := regimeRun (OrdRegime R o) T₂ y
      have ho : 1 ≤ o := Nat.one_le_iff_ne_zero.mpr hz
      have hscale : Q.d * o = P.d * p := hRaw₁
      have hp : 1 ≤ p := by nlinarith only [hscale, hd, he, ho]
      have hRraw : nmOrd (geoTransformAlong R T₂) y = o := htie.symm
      have hSraw : nmOrd (geoTransformAlong S T₂) y = p := by
        change o = nmOrd (geoTransformAlong R T₂) y at htie
        rw [← htie] at hRaw₂
        nlinarith only [hRaw₂, hscale, hd]
      have hscale₂ : S.d * o = R.d * p := by simpa only [← hdPR, ← hdQS] using hscale
      have hClock₁ : regimeRun (OrdRegime Q p) T₁ x = r₁ :=
        (scaled_regime_run_sameCarrierDim hn P Q hP hQ hPQ hDimPQ hXPQ o p hscale T₁ hTP x).symm
      have hClock₂ : regimeRun (OrdRegime S p) T₂ y = r₂ :=
        (scaled_regime_run_sameCarrierDim hn R S hR hS hRS hDimRS hXRS o p hscale₂ T₂ hTR y).symm
      have hLP := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hP T₁ hTP hcP x hx o rfl ho
      have hLQ := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hQ T₁ hTQ hcQ x hxQ p rfl hp
      have hLR := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hR T₂ hTR hcR y hy o hRraw ho
      have hLS := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hS T₂ hTS hcS y hyS p hSraw hp
      rw [hClock₁] at hLQ
      rw [hClock₂] at hLS
      have hHead₁ := ((isGeoTestTower_iff_head_tail P T₁ r₁).mp hTP).1
      have hHead₂ := ((isGeoTestTower_iff_head_tail R T₂ r₂).mp hTR).1
      have hLower := genLowerValue_twoPair_cut M hM hn hCuts P Q R S hP hQ hR hS hPQ hDimPQ hXPQ
        hRS hDimRS hXRS hdPR hdQS o p ho hp hscale (head T₁ r₁) (head T₂ r₂) hHead₁ hHead₂
        (tail T₁ r₁) (tail T₂ r₂) x y hLP hLQ hLR hLS
      rw [genInv_of_nmOrd_ne_zero M P T₁ (show nmOrd (geoTransformAlong P T₁) x = o from rfl) (Nat.ne_of_gt ho),
        genInv_of_nmOrd_ne_zero M R T₂ hRraw (Nat.ne_of_gt ho),
        genInv_of_nmOrd_ne_zero M Q T₁ (show nmOrd (geoTransformAlong Q T₁) x = p from rfl) (Nat.ne_of_gt hp),
        genInv_of_nmOrd_ne_zero M S T₂ hSraw (Nat.ne_of_gt hp)]
      simp only [Prod.Lex.toLex_lt_toLex, lt_irrefl, true_and, false_or,
        Sum.Lex.toLex_lt_toLex, Sum.lex_inr_inr]
      rw [hClock₁, hClock₂]
      exact hLower
  · have hA : genInv M R T₂ y < genInv M P T₁ x := by
      rw [genInv, genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl h
    have hB : genInv M S T₂ y < genInv M Q T₁ x := by
      rw [genInv, genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl (hGt.mp h)
    exact iff_of_false (not_lt_of_ge hA.le) (not_lt_of_ge hB.le)

end
end Hironaka.HironakaG1OriginalGeneralCanonicalCuts
