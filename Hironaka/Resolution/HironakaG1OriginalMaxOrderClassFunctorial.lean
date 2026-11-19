import Hironaka.Resolution.HironakaG1IndependentContactScaledHistory
import Hironaka.Resolution.HironakaG1DifferentCarrierMemberClassData
import Hironaka.Resolution.HironakaG8BFamilyClassStep
import Hironaka.Invariant.StepOneSeq

/-!
# Class functoriality of the LITERAL ORIGINAL maximal-order evaluator

The sole numerical induction input is lower ClassFunctorialFor for the
actual per-sequence invariant R. Actual kept-contact/member class data,
true double marks, full boundaries and ORIGINAL canonical tails are
internally produced. Generic Seq two-open comparison is reused; no BM
lower evaluator or caller lower/anchor-change packet is substituted.
Blueprint FIRST: `hironaka-g1-original-max-order-class-functorial.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalMaxOrderClassFunctorial
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  ResolutionInvariantSpec HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealRestriction StepOneValue StepOneValueMasked StepOneRegime
  StepOneLowerDomain StepOneMaskTower InvDomainMemberRestriction InvDomainRebase
  ContactStageKept HironakaG8LocalHistory HironakaG8MemberLoci
  HironakaG11InvBMClass HironakaG8P1GenInv
  HironakaG1IndependentContactClassData HironakaG1IndependentContactScaledHistory
  HironakaG1DifferentCarrierMemberClassData HironakaG1RecursiveMemberValueTransport
  HironakaG8PowerLowerMarks
open HomogenizedGlueingTower (strictAlong)
open ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-- Full-stage ACTUAL ORIGINAL lower record. Zero KEEPS the full original
bar boundary; positive uses the literal original member restriction. -/
def originalLowerRecord {X Y : CMfd.{0} n} (A : MarkedIdeal n X) (s : ℕ)
    (T : BlowupTower X Y) (y : Y) : MarkedIdeal n Y :=
  match s with
  | 0 => withN (coeffMarkedAlong (geoTransformAlong (barMarked A) T))
      (strictAlong T (A.N ∩ {x | (tangentChoice A (T.proj y)).2 x = 0}))
  | _ + 1 => memberRestrict (geoTransformAlong (barMarked A) T)
      (membersThrough (geoTransformAlong (barMarked A) T).E (origMembers A T) y)

/-- WHOLE literal record identity, including actual original scalar
pullback, carrier, every ordered boundary slot and true native mark. -/
theorem pullback_originalLowerRecord {X Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    MarkedIdeal.pullback (M' := CMfd.of (n := n) (lowerMask A s T y))
      (Subtype.val : lowerMask A s T y → Y) (originalLowerRecord A s T y) =
        lowerMarkedM A s T y := by
  cases s <;> rfl

private theorem raw_mark {X Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    (originalLowerRecord A s T y).d = (coeffMarkedAlong (geoTransformAlong (barMarked A) T)).d := by
  cases s <;> rfl

private theorem raw_mark_eq {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} (hd : A.d = B.d)
    (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    (originalLowerRecord A s T y).d = (originalLowerRecord B s T y).d := by
  have hbar : (barMarked A).d = (barMarked B).d := by
    change (coeffMarkedAlong (homMarkedAlong A)).d = (coeffMarkedAlong (homMarkedAlong B)).d
    simp only [coeffMarkedAlong_mark,homMarkedAlong,hd]
  rw [raw_mark,raw_mark,coeffMarkedAlong_mark,coeffMarkedAlong_mark,
    d_geoTransformAlong,d_geoTransformAlong,hbar]

private theorem raw_boundary_eq {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} (hE : A.E = B.E)
    (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    (originalLowerRecord A s T y).E = (originalLowerRecord B s T y).E := by
  have hEt : (geoTransformAlong (barMarked A) T).E = (geoTransformAlong (barMarked B) T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked A) (𝔫 := barMarked B) hE T
  have hOrig := origMembers_eq_of_E_eq hE T
  cases s with
  | zero => exact hEt
  | succ s =>
    simp only [originalLowerRecord,memberRestrict_membersThrough_E,hEt,hOrig]

private theorem raw_coherent {X Y : CMfd.{0} n} (A : MarkedIdeal n X) (hA : A.IsWellFormed)
    (s : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) (y : Y) :
    (originalLowerRecord A s T y).ideal.IsCoherent := by
  have hbar := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked A hA) T hT
  cases s <;> exact isCoherent_coeffMarkedAlong hbar.isCoherent hbar.isClosedSubmanifold_N

private def NormalizedClass {X : CMfd.{0} n} (P Q : MarkedIdeal n X) : Prop :=
  LocWPEquiv P Q ∧ SameCarrierDim P Q ∧
    (∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * DivisorExponentAlong.divExpAlong n P.N P.ideal H x =
        P.d * DivisorExponentAlong.divExpAlong n Q.N Q.ideal H x)

/-- Ordinary original source data derive the ENTIRE actual lower class
on the genuine intersection; no lower-class/geometry packet is input. -/
theorem original_lower_class_on_intersection {k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (hL : LocWPEquiv A B) (hd : A.d = B.d) (hDim : SameCarrierDim A B)
    (s : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (barMarked A) T).cosupp) (hreg : stepRegime A s T y) :
    let O := lowerMask A s T y ⊓ lowerMask B s T y
    let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord A s T y)
    let Q := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord B s T y)
    LocWPEquiv P Q ∧ SameCarrierDim P Q ∧ ExpAgree P Q := by
  let O := lowerMask A s T y ⊓ lowerMask B s T y
  let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord A s T y)
  let Q := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord B s T y)
  have hTA : IsGeoTestTower A T := ((StepOneBridge.barMarked_wEquiv A hA).2 T).1.mp hT
  have hData : NormalizedClass P Q := by
    cases s with
    | zero =>
      obtain ⟨_,_,_,hPQ,hD,_,hInitial⟩ := independent_two_source_contact_class
        hn A B hA hB hDim hL hmA hmB T hTA y hy hreg
      exact ⟨hPQ,hD,hInitial⟩
    | succ s =>
      have hMask := positive_mask_eq_sameCarrierDim hn A B hA hB hL.wEquiv hDim T hTA y
      obtain ⟨_,_,_,hPQ,hD,hInitial⟩ := positive_member_class_data_sameCarrierDim
        hn A B hA hB hL hDim T hTA y s hreg.1
      have hO : O = maskA A T y := by
        change maskA A T y ⊓ maskA B T y = maskA A T y
        rw [← hMask,inf_idem]
      have hTransport : ∀ V : Opens Y, V = maskA A T y →
          NormalizedClass
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → Y) (originalLowerRecord A (s+1) T y))
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → Y) (originalLowerRecord B (s+1) T y)) := by
        intro V hV
        subst V
        exact ⟨hPQ,hD,hInitial⟩
      exact hTransport O hO
  obtain ⟨hPQ,hD,hInitial⟩ := hData
  have hPQmark : P.d = Q.d := raw_mark_eq hd s T y
  have hPd : 1 ≤ P.d := by
    change 1 ≤ (originalLowerRecord A s T y).d
    rw [raw_mark]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  refine ⟨hPQ,hD,?_⟩
  intro H hH x hx hxH
  have hCross := hInitial H hH x hx hxH
  rw [← hPQmark] at hCross
  exact Nat.eq_of_mul_eq_mul_left hPd hCross

variable {k : ℕ} {Λ : Type} [LinearOrder Λ]

/-- Actual ORIGINAL values agree along common actual canonical tests;
the ONLY numerical induction input is lower Seq class functoriality. -/
theorem stepOneInvM_eq_of_isCanonical (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k-1) R.inv)
    {X : CMfd.{0} n} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hDim : SameCarrierDim A B)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hcA : IsCanonical A (Seq.StepOneValueMasked.stepOneInvM R A) T)
    (hcB : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM R B) T)
    {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM R A T y = Seq.StepOneValueMasked.stepOneInvM R B T y := by
  obtain ⟨hJA,hTA,hcosA⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R A hA hmA hn T hcA
  obtain ⟨hJB,_,hcosB⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R B hB hmB hn T hcB
  have hlev : ∀ {Z : CMfd.{0} n} (T' : BlowupTower X Z) (z : Z), level A T' z = level B T' z :=
    fun T' z => level_eq_of_E_eq hE T' z
  have hsp : ∀ {Z : CMfd.{0} n} (T' : BlowupTower X Z), IsGeoTestTower A T' → ∀ z : Z,
      IsSpecial A T' z ↔ IsSpecial B T' z :=
    fun T' hT' z => isSpecial_iff_of_wEquiv hn hA hB h.wEquiv hDim T' hT' z
  have hrg : ∀ (s : ℕ) {Z : CMfd.{0} n} (T' : BlowupTower X Z), IsGeoTestTower A T' → ∀ z : Z,
      stepRegime A s T' z ↔ stepRegime B s T' z := by
    intro s Z T' hT' z
    show (level A T' z = s ∧ ¬ IsSpecial A T' z) ↔ (level B T' z = s ∧ ¬ IsSpecial B T' z)
    rw [hlev T' z,hsp T' hT' z]
  have hyJA : y ∈ (geoTransformAlong (barMarked A) T).cosupp := hcosA ▸ hy
  have hyJB : y ∈ (geoTransformAlong (barMarked B) T).cosupp := by
    rw [hcosB,← (h.wEquiv.2 T).2 hTA]
    exact hy
  obtain ⟨s,hs⟩ : ∃ s, level A T y = s := ⟨_,rfl⟩
  have hsB : level B T y = s := (hlev T y).symm.trans hs
  have hrun : regimeRun (stepRegime B s) T y = regimeRun (stepRegime A s) T y :=
    (HironakaG8ClassStep.regimeRun_congr_of_test A (stepRegime A s) (stepRegime B s)
      (fun T' hT' z => hrg s T' hT' z) T hTA y).symm
  by_cases hspA : IsSpecial A T y
  · have hspB : IsSpecial B T y := (hsp T hTA y).mp hspA
    change Seq.StepOneValueMasked.stepOneInvL R A (lowerMarkedM A) T y =
      Seq.StepOneValueMasked.stepOneInvL R B (lowerMarkedM B) T y
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R A _ T hspA,
      Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R B _ T hspB,hs,hsB]
  · have hspB : ¬ IsSpecial B T y := fun h' => hspA ((hsp T hTA y).mpr h')
    have hLDA := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical A R
      hA.isWellFormed hA.one_le_d hn hmA hA.dimLE T
      ((Seq.StepOneBridge.isCanonical_iff R A hA hmA hn T).mp hcA) y hyJA hspA
    have hLDB := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical B R
      hB.isWellFormed hB.one_le_d hn hmB hB.dimLE T
      ((Seq.StepOneBridge.isCanonical_iff R B hB hmB hn T).mp hcB) y hyJB hspB
    obtain ⟨hregA,hy₀A⟩ := stepRegime_and_mem_cosupp_head A hA.isWellFormed T hJA hyJA hspA
    rw [hs] at hLDA hregA hy₀A
    rw [hsB,hrun] at hLDB
    obtain ⟨hmemA,hdomA,hcanA,hcosLA⟩ := hLDA
    obtain ⟨hmemB,hdomB,hcanB,_⟩ := hLDB
    have hT₀A : IsGeoTestTower (barMarked A) (head T (regimeRun (stepRegime A s) T y)) :=
      ((isGeoTestTower_iff_head_tail (barMarked A) T _).mp hJA).1
    have hT₀B : IsGeoTestTower (barMarked B) (head T (regimeRun (stepRegime A s) T y)) :=
      ((isGeoTestTower_iff_head_tail (barMarked B) T _).mp hJB).1
    rw [← pullback_originalLowerRecord A s _ _] at hdomA hcanA hcosLA
    rw [← pullback_originalLowerRecord B s _ _] at hdomB hcanB
    have hval := Seq.HironakaG8ClassStep.inv_eq_on_inter R hR
      (tail T (regimeRun (stepRegime A s) T y))
      (raw_coherent A hA.isWellFormed s _ hT₀A _) (raw_coherent B hB.isWellFormed s _ hT₀B _)
      (raw_mark_eq hd s _ _) (raw_boundary_eq hE s _ _) hdomA hdomB hcanA hcanB
      (fun _ _ => original_lower_class_on_intersection hn A B hA hB hmA hmB h hd hDim
        s _ hT₀A _ hy₀A hregA) hmemA hmemB hcosLA
    change Seq.StepOneValueMasked.stepOneInvL R A (lowerMarkedM A) T y =
      Seq.StepOneValueMasked.stepOneInvL R B (lowerMarkedM B) T y
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R A _ T hspA,
      Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R B _ T hspB,hs,hsB,hrun,
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem R A _ hmemA,
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem R B _ hmemB,
      ← pullback_originalLowerRecord A s _ _,← pullback_originalLowerRecord B s _ _]
    exact congrArg (fun t : WithTop Λ => toLex (s,t)) (congrArg WithTop.some hval)

/-- Actual ORIGINAL canonical towers agree, proved by actual max-locus
induction from the derived values, with no comparison packet. -/
theorem isCanonical_stepOneInvM_iff (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k-1) R.inv)
    {X : CMfd.{0} n} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hDim : SameCarrierDim A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsCanonical A (Seq.StepOneValueMasked.stepOneInvM R A) T ↔
        IsCanonical B (Seq.StepOneValueMasked.stepOneInvM R B) T
  | _,.refl => Iff.rfl
  | _,.step T C π hπ => by
    have ih := isCanonical_stepOneInvM_iff hn R hR hA hB hmA hmB h hd hE hDim T
    show (IsCanonical A (Seq.StepOneValueMasked.stepOneInvM R A) T ∧
        (C = ∅ ∨ C = maxLocus (Seq.StepOneValueMasked.stepOneInvM R A T) (geoTransformAlong A T).cosupp)) ↔
      (IsCanonical B (Seq.StepOneValueMasked.stepOneInvM R B) T ∧
        (C = ∅ ∨ C = maxLocus (Seq.StepOneValueMasked.stepOneInvM R B T) (geoTransformAlong B T).cosupp))
    have key : IsCanonical A (Seq.StepOneValueMasked.stepOneInvM R A) T →
        maxLocus (Seq.StepOneValueMasked.stepOneInvM R A T) (geoTransformAlong A T).cosupp =
          maxLocus (Seq.StepOneValueMasked.stepOneInvM R B T) (geoTransformAlong B T).cosupp := by
      intro hcA
      have hTA := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical R A hA hmA hn T hcA).2.1
      rw [← (h.wEquiv.2 T).2 hTA]
      exact ResolutionInvariantExt.maxLocus_congr fun y hy =>
        stepOneInvM_eq_of_isCanonical hn R hR hA hB hmA hmB h hd hE hDim T hcA (ih.mp hcA) hy
    constructor
    · rintro ⟨hcA,hC⟩
      exact ⟨ih.mp hcA,hC.imp id fun hC' => hC'.trans (key hcA)⟩
    · rintro ⟨hcB,hC⟩
      have hcA := ih.mpr hcB
      exact ⟨hcA,hC.imp id fun hC' => hC'.trans (key hcA).symm⟩

/-- The LITERAL ORIGINAL per-sequence maximal-order Step-1 evaluator is
class functorial from the honest lower class IH alone. -/
theorem classFunctorialMaxOrder_stepOneInvM (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k-1) R.inv) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} A {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R A (Y := Y) T y) where
  canonical_iff := by
    intro X A B hA hB hmA hmB h hd hE hDim _ Y T
    exact isCanonical_stepOneInvM_iff hn R hR hA hB hmA hmB h hd hE hDim T
  inv_eq := by
    intro X A B hA hB hmA hmB h hd hE hDim _ Y T hcA y hy
    exact stepOneInvM_eq_of_isCanonical hn R hR hA hB hmA hmB h hd hE hDim T hcA
      ((isCanonical_stepOneInvM_iff hn R hR hA hB hmA hmB h hd hE hDim T).mp hcA) hy

end
end Hironaka.HironakaG1OriginalMaxOrderClassFunctorial
