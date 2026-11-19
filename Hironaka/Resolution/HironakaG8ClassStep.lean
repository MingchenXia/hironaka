import Hironaka.Resolution.HironakaG11InvBMBridge
import Hironaka.Resolution.HironakaG11InvBMTangentIndep
import Hironaka.Resolution.HironakaG8P1GenInv
import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Invariant.StepOneNearby

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Class functoriality of Bierstone--Milman's Step 1 value: the skeleton (G8C lane, run 0080, round 2; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-skeleton.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §1 module 10 and §6c ("Modules 10--13");
the statement is the one lane G11B's module 12 consumes (inbox I-1361).  Source: Bierstone--Milman 2008, §5 Step I.A ("the
marked ideals `𝒞_U(ℐ)` and `𝒞_V(ℐ)` ... are equivalent in `U ∩ V` (since both are equivalent to `ℐ_{U∩V}`); therefore, by
functoriality in dimension `n − 1`, their resolution sequences are the same"), Step I.B ("the equivalence class of `𝒥` depends
only on that of `ℐ|_U`") and Theorem 7.1(4).

For two marked ideals `A ≈ B` of maximal order in the domain (`LocWPEquiv`, the same mark and divisor, carriers of the same
dimension on the cosupport, agreeing boundary exponents), Bierstone--Milman's Step 1 values `stepOneInvBM R A`,
`stepOneInvBM R B` have the same canonical segments and, along them, the same values on the cosupport, as soon as the lower
invariant `R` is class functorial.  The levels agree (the same divisor), the special points agree (lane G8's
`HironakaG8MemberLoci.isSpecial_iff_of_wEquiv`), hence the regimes and their runs agree along the test towers; at a
non-special point both lower values are values of `R` on lower ideals restricted to masks, which are moved to the intersection
`O` of the two masks (`MaxLocusLocal.restrict_nestedOpens`); there the two lower ideals carry the class data, and `R`'s class
functoriality gives the equality.

The class data of the two restricted lower ideals is an `R`-free statement about `A` and `B`, isolated here as the predicate
`LowerPairs A B Φ` (for `Φ` the conjunction `LocWPEquiv ∧ SameCarrierDim ∧ ExpAgree`: `LowerClassBM A B`); the mark and the
divisor of the two lower ideals are proved to agree.

* `regimeRun_congr_of_test`: runs of regimes agreeing along the multiple test blow-ups of a marked ideal agree along them;
* `mem_cosupp_restrict_nested_iff'`: the cosupport along nested opens, with the carrier closed only on the larger open;
* `LowerPairs`, `LowerClassBM`, `lowerIdealBM_d_eq`, `lowerIdealBM_E_eq`;
* `inv_eq_on_inter`: values of a class-functorial `R` on two restricted marked ideals agree at the common points, given the
  class data on the intersection of the opens;
* **`stepOneInvBM_eq_of_isCanonical`**, **`isCanonical_stepOneInvBM_iff`**;
* **`classFunctorialMaxOrder_stepOneInvBM_of_lowerClass`**: module 10's statement given `LowerClassBM` for all class-equivalent
  pairs.

Sorry-free.  Universe `0` for the manifolds (lane G8's local equivalence calculus is used in `CMfd.{0}`); values in any
universe.  Only the fields `inv`, `restrictOpen`, `towerIso` (through `MaxLocusLocal`) and the properties used by lane G11B's BM
modules of `ResolutionInvariantExt.ResolutionInvariant` are used (not property (8)).  Import discipline: no import of
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG8ClassStep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneValueMasked
  Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowerIsomorphism
  Hironaka.MaxLocusLocal Hironaka.MarkedIdealRestrictOpen
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)

noncomputable section

variable {n : ℕ}

/-! ### Tools -/

section Tools

/-- **Runs of regimes agreeing along the multiple test blow-ups of `𝔪` agree along them.** -/
theorem regimeRun_congr_of_test {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (Q Q' : Regime X)
    (hQ : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → ∀ y : Y, Q T y ↔ Q' T y) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → ∀ z : Y, regimeRun Q T z = regimeRun Q' T z
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
      have hT' : IsGeoTestTower 𝔪 T := ((isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT).1
      by_cases hq : Q T (π z)
      · rw [regimeRun_step_of Q T C π hπ hq, regimeRun_step_of Q' T C π hπ ((hQ T hT' (π z)).mp hq),
          regimeRun_congr_of_test 𝔪 Q Q' hQ T hT' (π z)]
      · rw [regimeRun_step_of_not Q T C π hπ hq,
          regimeRun_step_of_not Q' T C π hπ (fun h => hq ((hQ T hT' (π z)).mpr h))]

/-- **The cosupport along nested open sets** (`StepOneNearby.mem_cosupp_restrict_nested_iff` with the carrier closed only on
the larger open `W`). -/
theorem mem_cosupp_restrict_nested_iff' {X : CMfd.{u} n} {𝔫 : MarkedIdeal n X} {W V : Opens X}
    (hNW : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).N)
    (h𝔫 : 𝔫.ideal.IsCoherent) (hVW : V ≤ W) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)) (p : openPreimage T V) :
    p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp ↔
      (⟨(p : Y), openPreimage_mono T hVW p.2⟩ : openPreimage T W) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)).cosupp := by
  have hcW : (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔫
  have hN' : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W)
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNW _
  have hc' : (MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W)
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcW
  have hT' := isGeoTestTower_restrict (nestedOpens W V) hNW hcW (restrict W T) hT
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm hN' hc' hiso hT'
  rw [pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW] at hcos
  rw [hcos, mem_preimage, ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNW hcW (nestedOpens W V)
    (restrict W T) hT, mem_preimage]
  rfl

end Tools

/-! ### The class data of the lower ideals -/

section LowerClass

variable {X : CMfd.{0} n}

/-- **A property `Φ` of the pairs of lower ideals of `A` and `B`** restricted to a common open subset of their masks: along
every multiple test blow-up `T₀` of `J̄_A`, at every point `y₀` of the cosupport in the regime of level `s`, for every open
`O` of the stage inside both masks on which both restricted lower ideals lie in the domain (of any dimension bounds),
`Φ` holds for the two restricted lower ideals. -/
def LowerPairs (A B : MarkedIdeal n X)
    (Φ : ∀ {Z : CMfd.{0} n}, MarkedIdeal n Z → MarkedIdeal n Z → Prop) : Prop :=
  ∀ {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀), IsGeoTestTower (barMarked A) T₀ →
    ∀ (s : ℕ) (y₀ : Y₀), y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp → stepRegime A s T₀ y₀ →
    ∀ (O : Opens Y₀), O ≤ maskBM A s T₀ y₀ → O ≤ maskBM B s T₀ y₀ → ∀ (r r' : ℕ),
      IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀)) →
      IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀)) →
      Φ (Z := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀))
        (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀))

/-- **The class data of the lower ideals of `A` and `B`** (`R`-free): on every common open of the masks, the two restricted
lower ideals are `LocWPEquiv`, with carriers of the same dimension on the cosupport and agreeing boundary exponents (BM08 §5
Step I.A, I.B; the mark and the divisor agree by `lowerIdealBM_d_eq`, `lowerIdealBM_E_eq`). -/
def LowerClassBM (A B : MarkedIdeal n X) : Prop :=
  LowerPairs A B fun {_} P Q => LocWPEquiv P Q ∧ SameCarrierDim P Q ∧ ExpAgree P Q

/-- `LowerClassBM` from its three parts. -/
theorem lowerClassBM_of_parts {A B : MarkedIdeal n X} (h₁ : LowerPairs A B fun {_} P Q => LocWPEquiv P Q)
    (h₂ : LowerPairs A B fun {_} P Q => SameCarrierDim P Q) (h₃ : LowerPairs A B fun {_} P Q => ExpAgree P Q) :
    LowerClassBM A B := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB
  exact ⟨h₁ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB, h₂ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB,
    h₃ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB⟩

/-- **The lower ideals of two marked ideals with the same mark have the same mark.** -/
theorem lowerIdealBM_d_eq {A B : MarkedIdeal n X} (hd : A.d = B.d) (s : ℕ) {Y₀ : CMfd.{0} n}
    (T₀ : BlowupTower X Y₀) (a b : Y₀) : (lowerIdealBM A s T₀ a).d = (lowerIdealBM B s T₀ b).d := by
  rw [lowerIdealBM_d, lowerIdealBM_d, coeffEmptyBM_d, coeffEmptyBM_d, hd]

/-- **The lower ideals along the same tower have the same divisor** (the members born along `T₀`). -/
theorem lowerIdealBM_E_eq (A B : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (a b : Y₀) :
    (lowerIdealBM A s T₀ a).E = (lowerIdealBM B s T₀ b).E := by
  rw [lowerIdealBM_E, lowerIdealBM_E]
  exact MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := coeffEmptyBM A) (𝔫 := coeffEmptyBM B) rfl T₀

end LowerClass

/-! ### Values of a class-functorial invariant on two opens -/

section TwoOpens

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Values of a class-functorial `R` on two restricted marked ideals**: let `𝔞`, `𝔟` (coherent ideals, the same mark and
divisor) be restricted to opens `Wa`, `Wb` of the domain of `R` with `T₁|_{Wa}`, `T₁|_{Wb}` canonical segments.  If on
`Wa ∩ Wb` the two restrictions carry the class data, then at every common point of the cosupport the two values agree. -/
theorem inv_eq_on_inter (R : ResolutionInvariant.{0, v} n k Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv) {Y₀ Y : CMfd.{0} n}
    (T₁ : BlowupTower Y₀ Y) {𝔞 𝔟 : MarkedIdeal n Y₀} (h𝔞 : 𝔞.ideal.IsCoherent) (h𝔟 : 𝔟.ideal.IsCoherent)
    (hdd : 𝔞.d = 𝔟.d) (hEE : 𝔞.E = 𝔟.E) {Wa Wb : Opens Y₀}
    (hda : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : Wa → Y₀) 𝔞))
    (hdb : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : Wb → Y₀) 𝔟))
    (hca : IsCanonical (MarkedIdeal.pullback (Subtype.val : Wa → Y₀) 𝔞)
      (R.inv (MarkedIdeal.pullback (Subtype.val : Wa → Y₀) 𝔞)) (restrict Wa T₁))
    (hcb : IsCanonical (MarkedIdeal.pullback (Subtype.val : Wb → Y₀) 𝔟)
      (R.inv (MarkedIdeal.pullback (Subtype.val : Wb → Y₀) 𝔟)) (restrict Wb T₁))
    (hcl : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞) →
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟) →
      LocWPEquiv (X := CMfd.of (n := n) (Wa ⊓ Wb : Opens Y₀))
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞)
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟) ∧
        SameCarrierDim (X := CMfd.of (n := n) (Wa ⊓ Wb : Opens Y₀))
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞)
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟) ∧
        ExpAgree (X := CMfd.of (n := n) (Wa ⊓ Wb : Opens Y₀))
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞)
          (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟))
    {y : Y} (hya : T₁.proj y ∈ Wa) (hyb : T₁.proj y ∈ Wb)
    (hcos : (⟨y, hya⟩ : openPreimage T₁ Wa) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Wa → Y₀) 𝔞) (restrict Wa T₁)).cosupp) :
    R.inv (MarkedIdeal.pullback (Subtype.val : Wa → Y₀) 𝔞) (restrict Wa T₁) ⟨y, hya⟩ =
      R.inv (MarkedIdeal.pullback (Subtype.val : Wb → Y₀) 𝔟) (restrict Wb T₁) ⟨y, hyb⟩ := by
  have hVa : Wa ⊓ Wb ≤ Wa := inf_le_left
  have hVb : Wa ⊓ Wb ≤ Wb := inf_le_right
  obtain ⟨hdaO, hcaO, hvalA⟩ := restrict_nestedOpens R h𝔞 hVa hda T₁ hca
  obtain ⟨hdbO, hcbO, hvalB⟩ := restrict_nestedOpens R h𝔟 hVb hdb T₁ hcb
  let q : openPreimage T₁ (Wa ⊓ Wb) := ⟨y, show T₁.proj y ∈ ((Wa ⊓ Wb : Opens Y₀) : Set Y₀) from ⟨hya, hyb⟩⟩
  have hTa := isGeoTestTower_of_isCanonical R hda _ hca
  have hqa : q ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞)
      (restrict (Wa ⊓ Wb) T₁)).cosupp :=
    (mem_cosupp_restrict_nested_iff' hda.isWellFormed.isClosedSubmanifold_N h𝔞 hVa T₁ hTa q).mpr hcos
  obtain ⟨hloc, hsd, hexp⟩ := hcl hdaO hdbO
  have hEO : (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔞).E =
      (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟).E := by
    show 𝔞.E.map _ = 𝔟.E.map _
    rw [hEE]
  have key := hR.inv_eq _ _ hdaO hdbO hloc hdd hEO hsd hexp (restrict (Wa ⊓ Wb) T₁) hcaO q hqa
  have hTaO := isGeoTestTower_of_isCanonical R hdaO _ hcaO
  have hqb : q ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : (Wa ⊓ Wb : Opens Y₀) → Y₀) 𝔟)
      (restrict (Wa ⊓ Wb) T₁)).cosupp := by
    rw [← ((LocEquiv.wEquiv hloc).2 (restrict (Wa ⊓ Wb) T₁)).2 hTaO]
    exact hqa
  exact (hvalA q hqa).symm.trans (key.trans (hvalB q hqb))

end TwoOpens

/-! ### The values along common canonical segments -/

section Values

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{0} n}

/-- **The Step 1 values of `A ≈ B` agree along towers canonical for both**, on the cosupport (given the anchor changes and
the class data of the lower ideals). -/
theorem stepOneInvBM_eq_of_isCanonical (hn : 0 < n) (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (hACA : AnchorChangeBM A R) (hACB : AnchorChangeBM B R) (h : LocWPEquiv A B) (hd : A.d = B.d)
    (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hLC : LowerClassBM A B) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hcA : IsCanonical A (stepOneInvBM R A) T) (hcB : IsCanonical B (stepOneInvBM R B) T)
    {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    stepOneInvBM R A T y = stepOneInvBM R B T y := by
  obtain ⟨hJA, hTA, hcosA⟩ := HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R A hACA hA hmA hn T hcA
  obtain ⟨hJB, -, hcosB⟩ := HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R B hACB hB hmB hn T hcB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hlev : ∀ {Z : CMfd.{0} n} (T' : BlowupTower X Z) (z : Z), level A T' z = level B T' z :=
    fun T' z => HironakaG8MemberLoci.level_eq_of_E_eq hE T' z
  have hsp : ∀ {Z : CMfd.{0} n} (T' : BlowupTower X Z), IsGeoTestTower A T' → ∀ z : Z,
      IsSpecial A T' z ↔ IsSpecial B T' z :=
    fun T' hT' z => HironakaG8MemberLoci.isSpecial_iff_of_wEquiv hn hA hB hW hdim T' hT' z
  have hrg : ∀ (s : ℕ) {Z : CMfd.{0} n} (T' : BlowupTower X Z), IsGeoTestTower A T' → ∀ z : Z,
      stepRegime A s T' z ↔ stepRegime B s T' z := by
    intro s Z T' hT' z
    show (level A T' z = s ∧ ¬ IsSpecial A T' z) ↔ (level B T' z = s ∧ ¬ IsSpecial B T' z)
    rw [hlev T' z, hsp T' hT' z]
  have hyJA : y ∈ (geoTransformAlong (barMarked A) T).cosupp := hcosA ▸ hy
  have hyJB : y ∈ (geoTransformAlong (barMarked B) T).cosupp := by
    rw [hcosB, ← (hW.2 T).2 hTA]
    exact hy
  obtain ⟨s, hs⟩ : ∃ s, level A T y = s := ⟨_, rfl⟩
  have hsB : level B T y = s := (hlev T y).symm.trans hs
  have hrun : regimeRun (stepRegime B s) T y = regimeRun (stepRegime A s) T y :=
    (regimeRun_congr_of_test A (stepRegime A s) (stepRegime B s) (fun T' hT' z => hrg s T' hT' z) T hTA y).symm
  by_cases hspA : IsSpecial A T y
  · have hspB : IsSpecial B T y := (hsp T hTA y).mp hspA
    show stepOneInvG R A (maskBM A) (lowerBM A) T y = stepOneInvG R B (maskBM B) (lowerBM B) T y
    rw [stepOneInvG_of_isSpecial R A _ _ T hspA, stepOneInvG_of_isSpecial R B _ _ T hspB, hs, hsB]
  · have hspB : ¬ IsSpecial B T y := fun h' => hspA ((hsp T hTA y).mpr h')
    -- the lower data of both, at the common split
    have hLDA := HironakaG11InvBMAdmissible.hasLowerDataG_stepOneInvBM_of_isCanonical A R hACA hA.isWellFormed hA.one_le_d hn hmA hA.dimLE T
      ((HironakaG11InvBMBridge.isCanonical_iff R A hACA hA hmA hn T).mp hcA) y hyJA hspA
    have hLDB := HironakaG11InvBMAdmissible.hasLowerDataG_stepOneInvBM_of_isCanonical B R hACB hB.isWellFormed hB.one_le_d hn hmB hB.dimLE T
      ((HironakaG11InvBMBridge.isCanonical_iff R B hACB hB hmB hn T).mp hcB) y hyJB hspB
    obtain ⟨hregA, hy₀A⟩ := stepRegime_and_mem_cosupp_head A hA.isWellFormed T hJA hyJA hspA
    rw [hs] at hLDA hregA hy₀A
    rw [hsB, hrun] at hLDB
    obtain ⟨hmemA, hdomA, hcanA, hcosLA⟩ := hLDA
    obtain ⟨hmemB, hdomB, hcanB, -⟩ := hLDB
    show stepOneInvG R A (maskBM A) (lowerBM A) T y = stepOneInvG R B (maskBM B) (lowerBM B) T y
    rw [stepOneInvG_of_not_isSpecial R A _ _ T hspA, stepOneInvG_of_not_isSpecial R B _ _ T hspB, hs, hsB, hrun,
      lowerValueG_eq_of_mem R A _ _ hmemA, lowerValueG_eq_of_mem R B _ _ hmemB]
    -- the split
    have hT₀A : IsGeoTestTower (barMarked A) (head T (regimeRun (stepRegime A s) T y)) :=
      ((isGeoTestTower_iff_head_tail (barMarked A) T _).mp hJA).1
    have hT₀B : IsGeoTestTower (barMarked B) (head T (regimeRun (stepRegime A s) T y)) :=
      ((isGeoTestTower_iff_head_tail (barMarked B) T _).mp hJB).1
    have hval := inv_eq_on_inter R hR (tail T (regimeRun (stepRegime A s) T y))
      (HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn _ hT₀A _ s)
      (HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn _ hT₀B _ s)
      (lowerIdealBM_d_eq hd s _ _ _) (lowerIdealBM_E_eq A B s _ _ _) hdomA hdomB hcanA hcanB
      (fun hdA hdB => hLC _ hT₀A s _ hy₀A hregA _ inf_le_left inf_le_right _ _ hdA hdB) hmemA hmemB hcosLA
    exact congrArg (fun t : WithTop Λ => toLex (s, t)) (congrArg WithTop.some hval)

/-- **The canonical segments of `stepOneInvBM R A` and `stepOneInvBM R B` agree** for `A ≈ B` (given the anchor changes and
the class data of the lower ideals): induction along the tower, the maximum loci agreeing by the values. -/
theorem isCanonical_stepOneInvBM_iff (hn : 0 < n) (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (hACA : AnchorChangeBM A R) (hACB : AnchorChangeBM B R) (h : LocWPEquiv A B) (hd : A.d = B.d)
    (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hLC : LowerClassBM A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsCanonical A (stepOneInvBM R A) T ↔ IsCanonical B (stepOneInvBM R B) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      have ih := isCanonical_stepOneInvBM_iff hn R hR hA hB hmA hmB hACA hACB h hd hE hdim hLC T
      show (IsCanonical A (stepOneInvBM R A) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R A T) (geoTransformAlong A T).cosupp)) ↔
        (IsCanonical B (stepOneInvBM R B) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R B T) (geoTransformAlong B T).cosupp))
      have key : IsCanonical A (stepOneInvBM R A) T →
          maxLocus (stepOneInvBM R A T) (geoTransformAlong A T).cosupp =
            maxLocus (stepOneInvBM R B T) (geoTransformAlong B T).cosupp := by
        intro hcA
        have hTA := (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R A hACA hA hmA hn T hcA).2.1
        rw [← ((LocEquiv.wEquiv h).2 T).2 hTA]
        exact ResolutionInvariantExt.maxLocus_congr fun y hy =>
          stepOneInvBM_eq_of_isCanonical hn R hR hA hB hmA hmB hACA hACB h hd hE hdim hLC T hcA (ih.mp hcA) hy
      constructor
      · rintro ⟨hcA, hC⟩
        exact ⟨ih.mp hcA, hC.imp id fun hC' => hC'.trans (key hcA)⟩
      · rintro ⟨hcB, hC⟩
        have hcA := ih.mpr hcB
        exact ⟨hcA, hC.imp id fun hC' => hC'.trans (key hcA).symm⟩

end Values

/-! ### Module 10, given the class data of the lower ideals -/

section Main

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Class functoriality of Bierstone--Milman's Step 1 value on the marked ideals of maximal order, given the class data of
the lower ideals** ((B') plan module 10 in lane G11B's shape, I-1361, with the extra hypothesis `hLC`): if the lower invariant
`R` is class functorial (`hR`) and has the independence of the hypersurface of maximal contact on the marked ideals of the
domain of maximal order (`hTI`, used for the lower data along canonical segments), and the lower ideals of class-equivalent
marked ideals carry the class data (`hLC`, an `R`-free statement), then `stepOneInvBM R` is class functorial on the marked
ideals of maximal order. -/
theorem classFunctorialMaxOrder_stepOneInvBM_of_lowerClass (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    (hTI : ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R)
    (hLC : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerClassBM A B) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) where
  canonical_iff := by
    intro X A B hA hB hmA hmB h hd hE hdim h0 Y T
    exact isCanonical_stepOneInvBM_iff hn R hR hA hB hmA hmB
      (HironakaG11InvBMTangentIndep.anchorChangeBM_of_tangentIndepBM A R (hTI A hA hmA))
      (HironakaG11InvBMTangentIndep.anchorChangeBM_of_tangentIndepBM B R (hTI B hB hmB)) h hd hE hdim
      (hLC A B hA hB hmA hmB h hd hE hdim h0) T
  inv_eq := by
    intro X A B hA hB hmA hmB h hd hE hdim h0 Y T hcan y hy
    have hACA : AnchorChangeBM A R :=
      HironakaG11InvBMTangentIndep.anchorChangeBM_of_tangentIndepBM A R (hTI A hA hmA)
    have hACB : AnchorChangeBM B R :=
      HironakaG11InvBMTangentIndep.anchorChangeBM_of_tangentIndepBM B R (hTI B hB hmB)
    have hLC' : LowerClassBM A B := hLC A B hA hB hmA hmB h hd hE hdim h0
    exact stepOneInvBM_eq_of_isCanonical hn R hR hA hB hmA hmB hACA hACB h hd hE hdim hLC' T hcan
      ((isCanonical_stepOneInvBM_iff hn R hR hA hB hmA hmB hACA hACB h hd hE hdim hLC' T).mp hcan) hy

end Main

end

end Hironaka.HironakaG8ClassStep
