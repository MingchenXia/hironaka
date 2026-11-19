import Hironaka.Resolution.HironakaG1GenericPositiveSuffixRaw
import Hironaka.Resolution.HironakaG1ScaledExpData
import Hironaka.Resolution.HironakaG1CrossHeadGammaCuts
import Hironaka.Resolution.HironakaG8PowerLowerMarks
import Hironaka.Invariant.GeneralValue

/-! Complete actual member-suffix general-value cuts outside positive raw ties.
Arbitrary original boundaries and unequal native marks are retained. Positive
ties, weighted GIVEN-Q recoding and full canonical prefix transport remain open.
Blueprint FIRST: hironaka-g1-recursive-member-value-transport.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveMemberValueTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  StepOneValue StepOneValueMasked HomogenizedIdealAlong CoefficientIdeal
  InvDomainMemberRestriction InvDomainTowerAlong HironakaG8LocalHistory
  HironakaG1GenericPositiveClassData HironakaG1GenericPositiveSuffixRaw
  HironakaG1ScaledExpData HironakaG1CrossHeadGammaCuts HironakaG8PowerLowerMarks
  NonmonomialOrderLocal GeneralValue

/-- The literal full positive-member record on the specified original mask.
The second member of a comparison is evaluated on the SAME first-side mask. -/
abbrev positiveMemberOn {n : ℕ} {X Y : CMfd.{0} n}
    (A : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (O : Opens Y) :
    MarkedIdeal n (CMfd.of (n := n) O) :=
  MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y)
    (memberRestrict (geoTransformAlong (barMarked A) T)
      (membersThrough (geoTransformAlong (barMarked A) T).E (origMembers A T) y))

/-- The complete general-value strict cuts of genuine positive-member
suffixes agree when their first-side raw orders differ or the first vanishes.
All native marks, full ideals, proper carriers and ordered old/born boundaries
are inherited from the original records; none is a caller comparison packet. -/
theorem positive_member_generalValue_cuts_of_unequal_or_zero
    {n kA kB : ℕ} (hn : 0 < n) {X Y₁ Y₂ : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B)
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (hT₁ : IsGeoTestTower A T₁) (hT₂ : IsGeoTestTower A T₂)
    (y₁ : Y₁) (s₁ : ℕ) (hl₁ : level A T₁ y₁ = s₁+1)
    (y₂ : Y₂) (s₂ : ℕ) (hl₂ : level A T₂ y₂ = s₂+1)
    {Λ : Type*} [LinearOrder Λ]
    (M : ∀ {V : CMfd.{0} n}, MarkedIdeal n V → ∀ {W : CMfd.{0} n}, BlowupTower V W → W → Λ) :
    let O₁ := maskA A T₁ y₁
    let O₂ := maskA A T₂ y₂
    let A₁ := positiveMemberOn A T₁ y₁ O₁
    let B₁ := positiveMemberOn B T₁ y₁ O₁
    let A₂ := positiveMemberOn A T₂ y₂ O₂
    let B₂ := positiveMemberOn B T₂ y₂ O₂
    ∀ {Z₁ Z₂ : CMfd.{0} n} (S₁ : BlowupTower (CMfd.of (n := n) O₁) Z₁)
      (S₂ : BlowupTower (CMfd.of (n := n) O₂) Z₂),
      IsGeoTestTower A₁ S₁ → IsGeoTestTower A₂ S₂ →
      ∀ z₁ ∈ (geoTransformAlong A₁ S₁).cosupp, ∀ z₂ ∈ (geoTransformAlong A₂ S₂).cosupp,
        (nmOrd (geoTransformAlong A₁ S₁) z₁ ≠ nmOrd (geoTransformAlong A₂ S₂) z₂ ∨
          nmOrd (geoTransformAlong A₁ S₁) z₁ = 0) →
        (genInv M A₁ S₁ z₁ < genInv M A₂ S₂ z₂ ↔
          genInv M B₁ S₁ z₁ < genInv M B₂ S₂ z₂) := by
  let O₁ := maskA A T₁ y₁
  let O₂ := maskA A T₂ y₂
  let A₁ := positiveMemberOn A T₁ y₁ O₁
  let B₁ := positiveMemberOn B T₁ y₁ O₁
  let A₂ := positiveMemberOn A T₂ y₂ O₂
  let B₂ := positiveMemberOn B T₂ y₂ O₂
  obtain ⟨hA₁,hB₁,hN₁,hE₁,hL₁,hI₁⟩ := positive_member_class_data hn A B hA hB hN hL T₁ hT₁ y₁ s₁ hl₁
  obtain ⟨hA₂,hB₂,hN₂,hE₂,hL₂,hI₂⟩ := positive_member_class_data hn A B hA hB hN hL T₂ hT₂ y₂ s₂ hl₂
  change IsInvDomain (kA-1) A₁ at hA₁
  change IsInvDomain (kB-1) B₁ at hB₁
  change IsInvDomain (kA-1) A₂ at hA₂
  change IsInvDomain (kB-1) B₂ at hB₂
  change A₁.N = B₁.N at hN₁
  change A₂.N = B₂.N at hN₂
  change A₁.E = B₁.E at hE₁
  change A₂.E = B₂.E at hE₂
  change LocWPEquiv A₁ B₁ at hL₁
  change LocWPEquiv A₂ B₂ at hL₂
  have hMA : A₁.d = A₂.d := by
    change (coeffMarkedAlong (geoTransformAlong (barMarked A) T₁)).d =
      (coeffMarkedAlong (geoTransformAlong (barMarked A) T₂)).d
    simp only [coeffMarkedAlong_mark,d_geoTransformAlong]
  have hMB : B₁.d = B₂.d := by
    change (coeffMarkedAlong (geoTransformAlong (barMarked B) T₁)).d =
      (coeffMarkedAlong (geoTransformAlong (barMarked B) T₂)).d
    simp only [coeffMarkedAlong_mark,d_geoTransformAlong]
  dsimp only
  intro Z₁ Z₂ S₁ S₂ hS₁ hS₂ z₁ hz₁ z₂ hz₂ hBranch
  change (genInv M A₁ S₁ z₁ < genInv M A₂ S₂ z₂ ↔ genInv M B₁ S₁ z₁ < genInv M B₂ S₂ z₂)
  change (nmOrd (geoTransformAlong A₁ S₁) z₁ ≠ nmOrd (geoTransformAlong A₂ S₂) z₂ ∨
    nmOrd (geoTransformAlong A₁ S₁) z₁ = 0) at hBranch
  have hRaw₁ := positive_member_scaled_nmOrd_along hn A B hA hB hN hL T₁ hT₁ y₁ s₁ hl₁ S₁ hS₁ z₁ hz₁
  have hRaw₂ := positive_member_scaled_nmOrd_along hn A B hA hB hN hL T₂ hT₂ y₂ s₂ hl₂ S₂ hS₂ z₂ hz₂
  change B₁.d * nmOrd (geoTransformAlong A₁ S₁) z₁ = A₁.d * nmOrd (geoTransformAlong B₁ S₁) z₁ at hRaw₁
  change B₂.d * nmOrd (geoTransformAlong A₂ S₂) z₂ = A₂.d * nmOrd (geoTransformAlong B₂ S₂) z₂ at hRaw₂
  rw [←hMA,←hMB] at hRaw₂
  have hd := hA₁.one_le_d
  have he := hB₁.one_le_d
  have hlt : nmOrd (geoTransformAlong A₁ S₁) z₁ < nmOrd (geoTransformAlong A₂ S₂) z₂ ↔
      nmOrd (geoTransformAlong B₁ S₁) z₁ < nmOrd (geoTransformAlong B₂ S₂) z₂ := by
    constructor <;> intro h <;> nlinarith
  have hgt : nmOrd (geoTransformAlong A₂ S₂) z₂ < nmOrd (geoTransformAlong A₁ S₁) z₁ ↔
      nmOrd (geoTransformAlong B₂ S₂) z₂ < nmOrd (geoTransformAlong B₁ S₁) z₁ := by
    constructor <;> intro h <;> nlinarith
  by_cases hne : nmOrd (geoTransformAlong A₁ S₁) z₁ ≠ nmOrd (geoTransformAlong A₂ S₂) z₂
  · rcases lt_or_gt_of_ne hne with h | h
    · have hAlt : genInv M A₁ S₁ z₁ < genInv M A₂ S₂ z₂ := by
        rw [genInv,genInv,Prod.Lex.toLex_lt_toLex]
        exact Or.inl h
      have hBlt : genInv M B₁ S₁ z₁ < genInv M B₂ S₂ z₂ := by
        rw [genInv,genInv,Prod.Lex.toLex_lt_toLex]
        exact Or.inl (hlt.mp h)
      exact iff_of_true hAlt hBlt
    · have hAgt : genInv M A₂ S₂ z₂ < genInv M A₁ S₁ z₁ :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
      have hBgt : genInv M B₂ S₂ z₂ < genInv M B₁ S₁ z₁ :=
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hgt.mp h))
      exact iff_of_false (not_lt_of_ge (le_of_lt hAgt)) (not_lt_of_ge (le_of_lt hBgt))
  · have hz₀ : nmOrd (geoTransformAlong A₁ S₁) z₁ = 0 := hBranch.resolve_left hne
    have hw₀ : nmOrd (geoTransformAlong A₂ S₂) z₂ = 0 := (not_ne_iff.mp hne).symm.trans hz₀
    have hzB₀ : nmOrd (geoTransformAlong B₁ S₁) z₁ = 0 := by nlinarith
    have hwB₀ : nmOrd (geoTransformAlong B₂ S₂) z₂ = 0 := by nlinarith
    have hSB₁ := (hL₁.wEquiv.2 S₁).1.mp hS₁
    have hAS₁ := isInvDomain_geoTransformAlong hA₁ S₁ hS₁
    have hBS₁ := isInvDomain_geoTransformAlong hB₁ S₁ hSB₁
    have hAS₂ := isInvDomain_geoTransformAlong hA₂ S₂ hS₂
    have hExp₁ := scaled_expData_of_initial A₁ B₁ hA₁ hB₁ hN₁.symm hE₁.symm hL₁ hI₁ S₁ hS₁ z₁ hz₁
    have hExp₂ := scaled_expData_of_initial A₂ B₂ hA₂ hB₂ hN₂.symm hE₂.symm hL₂ hI₂ S₂ hS₂ z₂ hz₂
    have hMSA : (geoTransformAlong A₁ S₁).d = (geoTransformAlong A₂ S₂).d := by
      simpa only [d_geoTransformAlong] using hMA
    have hMSB : (geoTransformAlong B₁ S₁).d = (geoTransformAlong B₂ S₂).d := by
      simpa only [d_geoTransformAlong] using hMB
    have hGamma := gamma_cut_iff_across_heads hn (geoTransformAlong A₁ S₁) (geoTransformAlong B₁ S₁)
      (geoTransformAlong A₂ S₂) (geoTransformAlong B₂ S₂) hAS₁ hBS₁ hAS₂
      (E_geoTransformAlong_eq hE₁ S₁) (E_geoTransformAlong_eq hE₂ S₂) hMSA hMSB
      z₁ z₂ hz₁ hz₂ hz₀ hw₀ hExp₁ hExp₂
    rw [genInv_of_nmOrd_eq_zero M A₁ S₁ hz₀,genInv_of_nmOrd_eq_zero M A₂ S₂ hw₀,
      genInv_of_nmOrd_eq_zero M B₁ S₁ hzB₀,genInv_of_nmOrd_eq_zero M B₂ S₂ hwB₀]
    simpa only [Prod.Lex.toLex_lt_toLex,lt_irrefl,true_and,false_or,
      Sum.Lex.toLex_lt_toLex,Sum.lex_inl_inl] using hGamma

end
end Hironaka.HironakaG1RecursiveMemberValueTransport
