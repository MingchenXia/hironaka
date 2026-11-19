import Hironaka.Resolution.HironakaG1InitialPositiveFiniteCentres
import Hironaka.Resolution.HironakaG1InitialCompanionSectionComparison
import Hironaka.Resolution.HironakaG8PowerLowerMarks

/-! The original two-pair invariant on the actual initial finite section cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSectionPairOrder
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  StepOneValue StepOneValueMasked GeneralValue NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  CanonicalCentres InvDomainMemberRestriction HomogenizedIdealAlong ContactStageKept
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialSelectedOrderPhase HironakaG1InitialCompanionSectionComparison
  HironakaG8PowerLowerMarks HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG1OriginalUnequalMarkCanonical HironakaG1InitialPositiveFiniteCentres ResolutionDriver
  HironakaG1PositiveNormalRepairCentres MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen RestrictedIdealExtension
  RelativePrincipalizationSpan

private theorem contact_refl_mark {n : ℕ} {X : CMfd.{0} n}
    (A : MarkedIdeal n X) (u : X → ℂ) (W : Opens X) :
    (contactMarkedKept A u (.refl (X := X)) W).d = coefficientMark (coefficientMark A.d) := rfl

/-- The class and native marks required by the original two-pair cut, on
one actual initial finite lower window. -/
structure FiniteSectionPair {n : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    (k : ℕ) {X : CMfd.{0} (n+1)} (K R : MarkedIdeal (n+1) X) (x : X) : Prop where
  contactDomain : IsInvDomain k K
  sectionDomain : IsInvDomain k R
  locallyEquivalent : LocWPEquiv K R
  carrier : K.N = R.N
  emptySlots : ∀ D ∈ K.E, D = ∅
  survives : x ∈ K.cosupp
  contactMark : K.d = coefficientMark (coefficientMark (coefficientMark (coefficientMark Q.d)))
  sectionMark : R.d = coefficientMark (coefficientMark Q.d)

set_option maxHeartbeats 900000 in
/-- The actual finite branch supplies a two-pair input on the literal zero
mask, including marks depending only on the original source. -/
theorem initial_finite_section_records {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ (y : O) (hyC : y ∈ C),
      let z : C := ⟨y, hyC⟩
      let W := maskB J (.refl (X := Y)) z
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      y ∈ L.cosupp → ¬ IsSpecial J (.refl (X := Y)) z →
      ∃ hz : z ∈ W,
        let r : W := ⟨z, hz⟩
        let T := BlowupTower.refl (X := CMfd.of (n := n+1) W)
        FiniteSectionPair (X := CMfd.of (n := n+1) W) Q k K R r ∧
        Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) J (.refl (X := Y)) z =
          toLex (0, ((invFamily (Nat.succ_pos n) k).inv K T r : WithTop (ValTy k))) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hy hNS
  obtain ⟨hz, hK, hR, hrR, _, hV⟩ :=
    initial_companion_normal_section_finite_refl Q hQ p hLevel hpO y hyC hy hNS
  let r : W := ⟨z, hz⟩
  let Z := CMfd.of (n := n+1) W
  obtain ⟨hClass, hN, hEmpty⟩ := initial_companion_normal_section_contact Q hQ p hLevel hpO W
  have hLoc : LocWPEquiv (X := Z) K R := hClass
  have hrK : r ∈ K.cosupp := hLoc.cosupp_eq_base.symm ▸ hrR
  have hJd : J.d = L.d := by
    change (companionOf (n+1) (M := Y) (MarkedIdeal.pullback (Subtype.val : C → X) L) L.d).d = L.d
    unfold companionOf companionAlong
    split
    next hlt => exact False.elim ((Nat.lt_irrefl L.d) hlt)
    next => rfl
  have hRd : R.d = coefficientMark (coefficientMark Q.d) := rfl
  have hLd : L.d = R.d := rfl
  have hKd : K.d = coefficientMark (coefficientMark (coefficientMark (coefficientMark Q.d))) := by
    have hCd : K.d = coefficientMark (coefficientMark J.d) := contact_refl_mark J u W
    rw [hCd, hJd, hLd, hRd]
  exact ⟨hz, ⟨hK, hR, hLoc, hN, hEmpty, hrK, hKd, hRd⟩, hV⟩

private theorem FiniteSectionPair.exponents {n k : ℕ} {U : Opens (ComplexModel n)}
    {Q : MarkedIdeal n U} {X : CMfd.{0} (n+1)} {K R : MarkedIdeal (n+1) X} {x : X}
    (h : FiniteSectionPair Q k K R x) :
    ∀ D ∈ K.E, ∀ y ∈ K.cosupp, y ∈ D →
      R.d * divExpAlong (n+1) K.N K.ideal D y = K.d * divExpAlong (n+1) R.N R.ideal D y := by
  intro D hD y _ hy
  rw [h.emptySlots D hD] at hy
  exact False.elim hy

/-- Two initial finite anchors compare in the actual original recursive
orders. Each pair keeps its own unequal marks, and both same-side marks
are derived from the original source. -/
theorem FiniteSectionPair.lt_iff {n k : ℕ} {U : Opens (ComplexModel n)}
    {Q : MarkedIdeal n U} {X₁ X₂ : CMfd.{0} (n+1)}
    {K₁ R₁ : MarkedIdeal (n+1) X₁} {K₂ R₂ : MarkedIdeal (n+1) X₂}
    {x₁ : X₁} {x₂ : X₂}
    (h₁ : FiniteSectionPair Q k K₁ R₁ x₁) (h₂ : FiniteSectionPair Q k K₂ R₂ x₂) :
    let V := invFamily (Nat.succ_pos n) k
    (V).inv K₁ (.refl (X := X₁)) x₁ < (V).inv K₂ (.refl (X := X₂)) x₂ ↔
    (V).inv R₁ (.refl (X := X₁)) x₁ < (V).inv R₂ (.refl (X := X₂)) x₂ :=
  canonicalTwoPairCuts_invFamily (Nat.succ_pos n) k K₁ R₁ K₂ R₂
    h₁.contactDomain h₁.sectionDomain h₂.contactDomain h₂.sectionDomain
    h₁.locallyEquivalent (SameCarrierDim.of_N_eq h₁.carrier) h₁.exponents
    h₂.locallyEquivalent (SameCarrierDim.of_N_eq h₂.carrier) h₂.exponents
    (h₁.contactMark.trans h₂.contactMark.symm) (h₁.sectionMark.trans h₂.sectionMark.symm)
    trivial trivial trivial trivial (.refl (X := X₁)) (.refl (X := X₂))
    trivial trivial trivial trivial x₁ h₁.survives x₂ h₂.survives

section Stratum

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (k+1) Q) {A : Type*} (i : A → productOpen U)

local notation "T₀" => BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))
local notation "V" => invFamily (Nat.succ_pos n) k
local notation "f" => Seq.StepOneValueMasked.stepOneInvM
  (invFamily (Nat.succ_pos n) (k+1)) (properNormalMarked Q) T₀

include hQ in
private theorem selected_survives_of_initial_finite_read {p : productOpen U}
    (F : InitialFiniteRead Q T₀ p k s) :
    (⟨p, F.head_mem⟩ : initialMask Q T₀ p) ∈ (initialSelected Q T₀ p s).cosupp := by
  let O := initialMask Q T₀ p
  let X := CMfd.of (n := n+1) O
  let L := initialSelected Q T₀ p s
  let C := initialCompanionMask Q T₀ p s
  let J := initialCompanion Q T₀ p s
  let B := companionOf (n+1) (M := X) L L.d
  let z : C := F.point
  have hL : IsInvDomain (k+1) L := padded_lower_isInvDomain Q hQ T₀ trivial p F.initial_level
  have hB := (original_initial_positive_lower_companion_recursion Q hQ p F.initial_level).1
  have hEq : MarkedIdeal.pullback (Subtype.val : C → X) B = J :=
    pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have hLB : RestrictEquiv L B := by
    rw [show B = ⟨L.N, L.E, restrictOn (n+1) L.N L.ideal, L.d⟩ from
      (original_initial_positive_lower_companion_eq Q hQ p F.initial_level).2]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hCos := (RestrictEquiv.wEquiv hLB hL.isWellFormed.isClosedSubmanifold_N.1
    hL.isWellFormed.isCoherent hB.isWellFormed.isCoherent).cosupp_eq
  have hz : z ∈ J.cosupp := F.cosupp
  rw [← hEq, cosupp_pullback_val B
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg) C] at hz
  exact hCos.symm ▸ hz

include hQ in
set_option maxHeartbeats 1500000 in
/-- On the initial finite stratum the maxima of the actual padded upper
values are those of the supported section reads. The nonspecial hypothesis
refers to the actual companion at each anchor, and no normalized records are supplied. -/
theorem initial_finite_section_stratum_max_loci
    (F : ∀ a : A, InitialFiniteRead Q T₀ (i a) k s)
    (hNS : ∀ a : A, ¬ IsSpecial (initialCompanion Q T₀ (i a) s)
      (initialCompanionTower Q T₀ (i a) s) (F a).point) :
    ∃ g : A → ValTy k,
      (∀ a : A, ∃ (Z : CMfd.{0} (n+1)) (K R : MarkedIdeal (n+1) Z) (r : Z),
        FiniteSectionPair (X := Z) Q k K R r ∧
          g a = (V).inv R (.refl (X := Z)) r ∧
          (F a).value = toLex (0, ((V).inv K (.refl (X := Z)) r : WithTop (ValTy k)))) ∧
      i '' maxLocus g univ = maxLocus f (range i) ∧
      i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
  have hRead (a : A) : ∃ (Z : CMfd.{0} (n+1)) (K R : MarkedIdeal (n+1) Z) (r : Z),
      FiniteSectionPair (X := Z) Q k K R r ∧
        (F a).value = toLex (0, ((V).inv K (.refl (X := Z)) r : WithTop (ValTy k))) := by
    obtain ⟨hz, hPair, hV⟩ := initial_finite_section_records Q hQ (i a)
      (F a).initial_level (F a).head_mem ⟨i a, (F a).head_mem⟩ (F a).companion_mem
      (selected_survives_of_initial_finite_read Q hQ (F a)) (hNS a)
    exact ⟨_, _, _, _, hPair, hV⟩
  choose Z K R r hp hv using hRead
  let g (a : A) := (V).inv (R a) (.refl (X := Z a)) (r a)
  have hEmbed : StrictMono (fun v : ValTy k =>
      (toLex (0, (v : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k))) := by
    intro u v huv
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr huv⟩)
  have hLt (a b : A) : f (i a) < f (i b) ↔ g a < g b := by
    have hF := InitialFiniteRead.upper_lt_iff (F a) (F b)
    rw [hv a, hv b] at hF
    exact hF.trans (hEmbed.lt_iff_lt.trans ((hp a).lt_iff (hp b)))
  have hLe (a b : A) : f (i a) ≤ f (i b) ↔ g a ≤ g b := by
    simpa only [not_lt] using not_congr (hLt b a)
  have hPre : i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
    ext a
    constructor
    · intro ha
      have hm : i a ∈ maxLocus f (range i) := ha
      exact ⟨mem_univ a, fun b _ => (hLe b a).mp (hm.2 (i b) (mem_range_self b))⟩
    · intro ha
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (hLe b a).mpr (ha.2 b (mem_univ b))
  refine ⟨g, fun a => ⟨Z a, K a, R a, r a, hp a, rfl, hv a⟩, ?_, hPre⟩
  rw [← hPre, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr (fun _ h => h.1)

end Stratum

end
end Hironaka.HironakaG1InitialCompanionSectionPairOrder
