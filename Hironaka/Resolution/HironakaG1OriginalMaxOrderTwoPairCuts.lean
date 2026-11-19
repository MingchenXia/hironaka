import Hironaka.Resolution.HironakaG1OriginalTwoPairCanonicalCuts
import Hironaka.Resolution.HironakaG1OriginalMaxOrderClassFunctorial

/-!
# Two-pair cuts for the LITERAL ORIGINAL maximal-order evaluator

The ONLY numerical input is the honest lower-family ordinary two-pair
cut IH. All four actual canonical histories stay explicit. Each genuine
original lower tail is restricted to the pair's actual common mask; its
native records, domains, CAN, cosupp and values are internally constructed.
No same-mark class IH, all-test lower-CAN or desired comparison packet.
Blueprint FIRST: `hironaka-g1-original-max-order-two-pair-cuts.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalMaxOrderTwoPairCuts
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit ResolutionInvariantSpec
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain StepOneMaskTower
  InvDomainMemberRestriction InvDomainRebase ContactStageKept HironakaG8LocalHistory
  HironakaG8MemberLoci HironakaG11InvBMClass HironakaG8PowerLowerMarks
  HironakaG1IndependentContactClassData HironakaG1IndependentContactScaledHistory
  HironakaG1DifferentCarrierMemberClassData HironakaG1RecursiveMemberValueTransport
  HironakaG1OriginalMaxOrderClassFunctorial HironakaG1OriginalTwoPairCanonicalCuts
  DivisorExponentAlong MaxLocusLocal
open HomogenizedGlueingTower (strictAlong)
noncomputable section
variable {n : ℕ}

private abbrev ScaledExponents {X : CMfd.{0} n} (P Q : MarkedIdeal n X) : Prop :=
  ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
    Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x

private def NormalizedClass {k : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X) : Prop :=
  IsInvDomain (k-1) P ∧ IsInvDomain (k-1) Q ∧ LocWPEquiv P Q ∧ SameCarrierDim P Q ∧ ScaledExponents P Q

/-- Genuine actual ORIGINAL lower domains/class at their true common
mask, keeping unequal marks and normalized exponents without cancellation. -/
theorem original_lower_normalized_class_on_intersection {k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (hL : LocWPEquiv A B) (hDim : SameCarrierDim A B)
    (s : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (barMarked A) T).cosupp) (hreg : stepRegime A s T y) :
    let O := lowerMask A s T y ⊓ lowerMask B s T y
    let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord A s T y)
    let Q := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord B s T y)
    IsInvDomain (k-1) P ∧ IsInvDomain (k-1) Q ∧ LocWPEquiv P Q ∧ SameCarrierDim P Q ∧
      (∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
        Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x) := by
  let O := lowerMask A s T y ⊓ lowerMask B s T y
  let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord A s T y)
  let Q := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (originalLowerRecord B s T y)
  have hTA : IsGeoTestTower A T := ((StepOneBridge.barMarked_wEquiv A hA).2 T).1.mp hT
  have hData : NormalizedClass (k := k) P Q := by
    cases s with
    | zero =>
      obtain ⟨_,hP,hQ,hPQ,hD,_,hInitial⟩ := independent_two_source_contact_class
        hn A B hA hB hDim hL hmA hmB T hTA y hy hreg
      exact ⟨hP,hQ,hPQ,hD,hInitial⟩
    | succ s =>
      have hMask := positive_mask_eq_sameCarrierDim hn A B hA hB hL.wEquiv hDim T hTA y
      obtain ⟨hP,hQ,_,hPQ,hD,hInitial⟩ := positive_member_class_data_sameCarrierDim
        hn A B hA hB hL hDim T hTA y s hreg.1
      have hO : O = maskA A T y := by
        change maskA A T y ⊓ maskA B T y = maskA A T y
        rw [← hMask,inf_idem]
      have hTransport : ∀ V : Opens Y, V = maskA A T y →
          NormalizedClass (k := k)
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → Y) (originalLowerRecord A (s+1) T y))
            (MarkedIdeal.pullback (M' := CMfd.of (n := n) V) (Subtype.val : V → Y) (originalLowerRecord B (s+1) T y)) := by
        intro V hV
        subst V
        exact ⟨hP,hQ,hPQ,hD,hInitial⟩
      exact hTransport O hO
  exact hData

private abbrev coeffMark := coefficientMark

private theorem raw_mark_formula {X Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (s : ℕ) (T : BlowupTower X Y) (y : Y) :
    (originalLowerRecord A s T y).d = coeffMark (coeffMark A.d) := by
  have hmark : (originalLowerRecord A s T y).d = (coeffMarkedAlong (geoTransformAlong (barMarked A) T)).d := by
    cases s <;> rfl
  rw [hmark,coeffMarkedAlong_mark,d_geoTransformAlong]
  rfl

private theorem raw_coherent {X Y : CMfd.{0} n} (A : MarkedIdeal n X) (hA : A.IsWellFormed)
    (s : ℕ) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) (y : Y) :
    (originalLowerRecord A s T y).ideal.IsCoherent := by
  have hbar := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked A hA) T hT
  cases s <;> exact isCoherent_coeffMarkedAlong hbar.isCoherent hbar.isClosedSubmanifold_N

variable {k : ℕ} {Λ : Type} [LinearOrder Λ]

/-- PRIVATE observations package only actual internally constructed
common-open records/tails and their value identities; never caller input. -/
private structure LowerRow (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    (a b s : ℕ) (v w : ℕ ×ₗ WithTop Λ) where
  source : CMfd.{0} n
  target : CMfd.{0} n
  left : MarkedIdeal n source
  right : MarkedIdeal n source
  tower : BlowupTower source target
  point : target
  domLeft : IsInvDomain (k-1) left
  domRight : IsInvDomain (k-1) right
  localClass : LocWPEquiv left right
  carrierDim : SameCarrierDim left right
  exponents : ScaledExponents left right
  markLeft : left.d = coeffMark (coeffMark a)
  markRight : right.d = coeffMark (coeffMark b)
  canonicalLeft : IsCanonical left (R.inv left) tower
  canonicalRight : IsCanonical right (R.inv right) tower
  cosLeft : point ∈ (geoTransformAlong left tower).cosupp
  valueLeft : v = toLex (s, (R.inv left tower point : WithTop Λ))
  valueRight : w = toLex (s, (R.inv right tower point : WithTop Λ))

private theorem exists_lower_row (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    {X Y : CMfd.{0} n} (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hDim : SameCarrierDim A B) (T : BlowupTower X Y)
    (hcA : IsCanonical A (Seq.StepOneValueMasked.stepOneInvM R A) T)
    (hcB : IsCanonical B (Seq.StepOneValueMasked.stepOneInvM R B) T)
    (y : Y) (hy : y ∈ (geoTransformAlong A T).cosupp) (hspA : ¬ IsSpecial A T y) :
    Nonempty (LowerRow R A.d B.d (level A T y)
      (Seq.StepOneValueMasked.stepOneInvM R A T y) (Seq.StepOneValueMasked.stepOneInvM R B T y)) := by
  obtain ⟨hJA,hTA,hcosA⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R A hA hmA hn T hcA
  obtain ⟨hJB,_,hcosB⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical R B hB hmB hn T hcB
  have hE : A.E = B.E := h.wEquiv.1
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
  have hspB : ¬ IsSpecial B T y := fun h' => hspA ((hsp T hTA y).mpr h')
  have hyJA : y ∈ (geoTransformAlong (barMarked A) T).cosupp := hcosA ▸ hy
  have hyJB : y ∈ (geoTransformAlong (barMarked B) T).cosupp := by
    rw [hcosB,← (h.wEquiv.2 T).2 hTA]
    exact hy
  obtain ⟨s,hs⟩ : ∃ s, level A T y = s := ⟨_,rfl⟩
  rw [hs]
  have hsB : level B T y = s := (hlev T y).symm.trans hs
  have hrun : regimeRun (stepRegime B s) T y = regimeRun (stepRegime A s) T y :=
    (HironakaG8ClassStep.regimeRun_congr_of_test A (stepRegime A s) (stepRegime B s)
      (fun T' hT' z => hrg s T' hT' z) T hTA y).symm
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
  obtain ⟨hmemB,hdomB,hcanB,hcosLB⟩ := hLDB
  let T₀ := head T (regimeRun (stepRegime A s) T y)
  let V := tail T (regimeRun (stepRegime A s) T y)
  let a₀ := V.proj y
  let WA := lowerMask A s T₀ a₀
  let WB := lowerMask B s T₀ a₀
  let O := WA ⊓ WB
  let AP := originalLowerRecord A s T₀ a₀
  let BP := originalLowerRecord B s T₀ a₀
  let P := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → _) AP
  let Q := MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → _) BP
  have hT₀A : IsGeoTestTower (barMarked A) T₀ :=
    ((isGeoTestTower_iff_head_tail (barMarked A) T _).mp hJA).1
  have hT₀B : IsGeoTestTower (barMarked B) T₀ :=
    ((isGeoTestTower_iff_head_tail (barMarked B) T _).mp hJB).1
  have hcohA := raw_coherent A hA.isWellFormed s T₀ hT₀A a₀
  have hcohB := raw_coherent B hB.isWellFormed s T₀ hT₀B a₀
  rw [← pullback_originalLowerRecord A s _ _] at hdomA hcanA hcosLA
  rw [← pullback_originalLowerRecord B s _ _] at hdomB hcanB hcosLB
  obtain ⟨hdomPO,hcanPO,hvalP⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hcohA
    (show O ≤ WA from inf_le_left) hdomA V hcanA
  obtain ⟨hdomQO,hcanQO,hvalQ⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hcohB
    (show O ≤ WB from inf_le_right) hdomB V hcanB
  let q : openPreimage V O := ⟨y,⟨hmemA,hmemB⟩⟩
  have htestA := Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hdomA _ hcanA
  have htestB := Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical R hdomB _ hcanB
  have hcosP : q ∈ (geoTransformAlong P (restrict O V)).cosupp :=
    (HironakaG8ClassStep.mem_cosupp_restrict_nested_iff' hdomA.isWellFormed.isClosedSubmanifold_N
      hcohA (show O ≤ WA from inf_le_left) V htestA q).mpr hcosLA
  have hcosQ : q ∈ (geoTransformAlong Q (restrict O V)).cosupp :=
    (HironakaG8ClassStep.mem_cosupp_restrict_nested_iff' hdomB.isWellFormed.isClosedSubmanifold_N
      hcohB (show O ≤ WB from inf_le_right) V htestB q).mpr hcosLB
  obtain ⟨_,_,hClass,hLowerDim,hExp⟩ := original_lower_normalized_class_on_intersection
    hn A B hA hB hmA hmB h hDim s T₀ hT₀A a₀ hy₀A hregA
  refine ⟨{ source := CMfd.of (n := n) O
            target := CMfd.of (n := n) (openPreimage V O)
            left := P
            right := Q
            tower := restrict O V
            point := q
            domLeft := hdomPO
            domRight := hdomQO
            localClass := hClass
            carrierDim := hLowerDim
            exponents := hExp
            markLeft := raw_mark_formula A s T₀ a₀
            markRight := raw_mark_formula B s T₀ a₀
            canonicalLeft := hcanPO
            canonicalRight := hcanQO
            cosLeft := hcosP
            valueLeft := ?_
            valueRight := ?_ }⟩
  · change Seq.StepOneValueMasked.stepOneInvL R A (lowerMarkedM A) T y = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R A _ T hspA,hs,
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem R A _ hmemA,← pullback_originalLowerRecord A s _ _]
    exact congrArg (fun t : Λ => toLex (s,(t : WithTop Λ))) (hvalP q hcosP).symm
  · change Seq.StepOneValueMasked.stepOneInvL R B (lowerMarkedM B) T y = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R B _ T hspB,hsB,hrun,
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem R B _ hmemB,← pullback_originalLowerRecord B s _ _]
    exact congrArg (fun t : Λ => toLex (s,(t : WithTop Λ))) (hvalQ q hcosQ).symm

private theorem lex_same_level {s t : ℕ} (h : s = t) (a b : WithTop Λ) :
    toLex (s,a) < toLex (t,b) ↔ a < b := by
  subst t
  simp only [Prod.Lex.lt_iff,ofLex_toLex,lt_self_iff_false,true_and,false_or]

/-- LITERAL ORIGINAL maximal-order cross-head cuts from ONLY the honest
lower ordinary cut IH. All four actual upper canonicalities remain explicit. -/
theorem canonicalMaxOrderTwoPairCuts_stepOneInvM (hn : 0 < n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n (k-1) Λ)
    (hCuts : CanonicalTwoPairCuts (k-1) R.inv) :
    CanonicalMaxOrderTwoPairCuts k
      (fun {X} A {Y} T y => Seq.StepOneValueMasked.stepOneInvM (X := X) R A (Y := Y) T y) := by
  intro X₁ X₂ A B C D hA hB hC hD hAB hDimAB _ hCD hDimCD _ hdAC hdBD
    hmA hmB hmC hmD Y₁ Y₂ T₁ T₂ hcA hcB hcC hcD x hx y hy
  change Seq.StepOneValueMasked.stepOneInvM R A T₁ x < Seq.StepOneValueMasked.stepOneInvM R C T₂ y ↔
    Seq.StepOneValueMasked.stepOneInvM R B T₁ x < Seq.StepOneValueMasked.stepOneInvM R D T₂ y
  have hTA := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical R A hA hmA hn T₁ hcA).2.1
  have hTC := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical R C hC hmC hn T₂ hcC).2.1
  have hlAB := level_eq_of_E_eq hAB.wEquiv.1 T₁ x
  have hlCD := level_eq_of_E_eq hCD.wEquiv.1 T₂ y
  by_cases hlevels : level A T₁ x = level C T₂ y
  · have hspAB := isSpecial_iff_of_wEquiv hn hA hB hAB.wEquiv hDimAB T₁ hTA x
    have hspCD := isSpecial_iff_of_wEquiv hn hC hD hCD.wEquiv hDimCD T₂ hTC y
    by_cases hspA : IsSpecial A T₁ x
    · have htopA := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R A (lowerMarkedM A) T₁ hspA
      have htopB := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R B (lowerMarkedM B) T₁ (hspAB.mp hspA)
      change Seq.StepOneValueMasked.stepOneInvM R A T₁ x = _ at htopA
      change Seq.StepOneValueMasked.stepOneInvM R B T₁ x = _ at htopB
      rw [← hlAB] at htopB
      by_cases hspC : IsSpecial C T₂ y
      · have htopC := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R C (lowerMarkedM C) T₂ hspC
        have htopD := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R D (lowerMarkedM D) T₂ (hspCD.mp hspC)
        change Seq.StepOneValueMasked.stepOneInvM R C T₂ y = _ at htopC
        change Seq.StepOneValueMasked.stepOneInvM R D T₂ y = _ at htopD
        rw [← hlCD] at htopD
        rw [htopA,htopB,htopC,htopD,lex_same_level hlevels]
      · obtain ⟨r₂⟩ := exists_lower_row hn R C D hC hD hmC hmD hCD hDimCD T₂ hcC hcD y hy hspC
        rw [htopA,htopB]
        conv_lhs => rhs; rw [r₂.valueLeft]
        conv_rhs => rhs; rw [r₂.valueRight]
        rw [lex_same_level hlevels,lex_same_level hlevels]
        simp only [WithTop.not_top_lt]
    · obtain ⟨r₁⟩ := exists_lower_row hn R A B hA hB hmA hmB hAB hDimAB T₁ hcA hcB x hx hspA
      by_cases hspC : IsSpecial C T₂ y
      · have htopC := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R C (lowerMarkedM C) T₂ hspC
        have htopD := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R D (lowerMarkedM D) T₂ (hspCD.mp hspC)
        change Seq.StepOneValueMasked.stepOneInvM R C T₂ y = _ at htopC
        change Seq.StepOneValueMasked.stepOneInvM R D T₂ y = _ at htopD
        rw [← hlCD] at htopD
        rw [htopC,htopD]
        conv_lhs => lhs; rw [r₁.valueLeft]
        conv_rhs => lhs; rw [r₁.valueRight]
        rw [lex_same_level hlevels,lex_same_level hlevels]
        simp only [WithTop.coe_lt_top]
      · obtain ⟨r₂⟩ := exists_lower_row hn R C D hC hD hmC hmD hCD hDimCD T₂ hcC hcD y hy hspC
        have hLeftMark : r₁.left.d = r₂.left.d :=
          r₁.markLeft.trans ((congrArg (fun d => coeffMark (coeffMark d)) hdAC).trans r₂.markLeft.symm)
        have hRightMark : r₁.right.d = r₂.right.d :=
          r₁.markRight.trans ((congrArg (fun d => coeffMark (coeffMark d)) hdBD).trans r₂.markRight.symm)
        have hCut := hCuts r₁.left r₁.right r₂.left r₂.right
          r₁.domLeft r₁.domRight r₂.domLeft r₂.domRight
          r₁.localClass r₁.carrierDim r₁.exponents r₂.localClass r₂.carrierDim r₂.exponents
          hLeftMark hRightMark trivial trivial trivial trivial r₁.tower r₂.tower
          r₁.canonicalLeft r₁.canonicalRight r₂.canonicalLeft r₂.canonicalRight
          r₁.point r₁.cosLeft r₂.point r₂.cosLeft
        conv_lhs => lhs; rw [r₁.valueLeft]
        conv_lhs => rhs; rw [r₂.valueLeft]
        conv_rhs => lhs; rw [r₁.valueRight]
        conv_rhs => rhs; rw [r₂.valueRight]
        rw [lex_same_level hlevels,lex_same_level hlevels]
        exact (WithTop.coe_lt_coe.trans hCut).trans WithTop.coe_lt_coe.symm
  · have hfA : (ofLex (Seq.StepOneValueMasked.stepOneInvM R A T₁ x)).1 = level A T₁ x :=
      Seq.StepOneValueMasked.stepOneInvL_fst R A (lowerMarkedM A) T₁ x
    have hfB : (ofLex (Seq.StepOneValueMasked.stepOneInvM R B T₁ x)).1 = level B T₁ x :=
      Seq.StepOneValueMasked.stepOneInvL_fst R B (lowerMarkedM B) T₁ x
    have hfC : (ofLex (Seq.StepOneValueMasked.stepOneInvM R C T₂ y)).1 = level C T₂ y :=
      Seq.StepOneValueMasked.stepOneInvL_fst R C (lowerMarkedM C) T₂ y
    have hfD : (ofLex (Seq.StepOneValueMasked.stepOneInvM R D T₂ y)).1 = level D T₂ y :=
      Seq.StepOneValueMasked.stepOneInvL_fst R D (lowerMarkedM D) T₂ y
    rw [Prod.Lex.lt_iff,Prod.Lex.lt_iff,hfA,hfB,hfC,hfD,← hlAB,← hlCD]
    simp only [hlevels,false_and,or_false]

end
end Hironaka.HironakaG1OriginalMaxOrderTwoPairCuts
