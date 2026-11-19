import Hironaka.Resolution.HironakaG8E4cCompanion
import Hironaka.Invariant.GeneralCompare

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# E4c at the level of values: the companion entries of class-equivalent marked ideals agree (G8C lane, run 0080; (B') P5)

Blueprint: `hironaka-g8-e4c-value.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 11
(`classFunctorial_genInv`: "E4: companion, P5") and §2 P5.  Source: Bierstone--Milman 2008, Corollary 5.3 and §5 Step II.B.

The second entry of the general value (`GeneralValue.genSecond`) at a point of positive order `o` is the companion value
`genLowerValue M 𝔪 o T₀ T₁ y = M (compAt 𝔪 o T₀) (T₁|_{mask}) y`, where `compAt 𝔪 o T₀` is the companion ideal formed at the
stage `T₀` on the mask `{ν_{𝔪_{T₀}} ≤ o}`.  For two class-equivalent marked ideals `A`, `B` the two masks may differ off the
cosupport, so the two companion values are values of `M` on DIFFERENT open sets.  This module compares them:

* `MaxOrderClassValue k M`: the value part of class functoriality of a maximal-order value function `M` for `LocWPEquiv`
  (the hypotheses of `HironakaG11InvBMClass.ClassFunctorialFor.inv_eq`, plus maximal order of both ideals);
  `MaxOrderClassValue.of_classFunctorialFor` (a class-functorial value function has it);
* **`genLowerValue_eq_of_classData`**: if `M` is a maximal-order value (`MaxOrderValue.IsMaxOrderValue`) with
  `MaxOrderClassValue k M`, `A ≈ B` (`LocWPEquiv`, native domain, same carrier and mark, agreeing exponents, `n > 0`,
  `o ≥ 1`), `T₀` a common test tower, and both `A` and `B` have lower data at the split `T₀ T₁` at `y`
  (`GeneralValue.GenLowerData`), then the companion values agree:
  `genLowerValue M A o T₀ T₁ y = genLowerValue M B o T₀ T₁ y`.

Proof: both values equal the values on the intersection `W` of the two masks (TN3's `GeneralCompare.value_eq_of_two_opens`
for the companion of `𝔪_{T₀}` on the whole stage, restricted to the mask and to `W`); on `W` the two companions carry the class
data (`HironakaG8E4cCompanion.companionOf_classData_maskInter`, E4c), and `MaxOrderClassValue` concludes.  Sorry-free.
Universe `0`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8E4cValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowerTransforms
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.NonmonomialOrderTail (ordMask)
open Hironaka.NonmonomialOrderLocal (ordGe)
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.GeneralValue (compAt genLowerValue GenLowerData)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ClassFunctorialFor)

noncomputable section

variable {n : ℕ}

/-- **The value part of class functoriality of a maximal-order value function** for `LocWPEquiv`: two maximal-order marked
ideals of the domain which are locally `s(i,ii)`-equivalent, with the same mark, boundary, carrier dimension and boundary
exponents, have the same values along the canonical segments of the first, on its cosupport. -/
def MaxOrderClassValue {Λ : Type v} [LinearOrder Λ] (k : ℕ)
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {W : CMfd.{0} n} (P Q : MarkedIdeal n W), IsInvDomain k P → IsInvDomain k Q →
    IsMaximalOrderAlong P.N P.ideal P.d → IsMaximalOrderAlong Q.N Q.ideal Q.d → LocWPEquiv P Q → P.d = Q.d →
    P.E = Q.E → SameCarrierDim P Q → HironakaG11InvBMClass.ExpAgree P Q →
    ∀ {Y : CMfd.{0} n} (T : BlowupTower W Y), IsCanonical P (M P) T → ∀ y ∈ (geoTransformAlong P T).cosupp,
      M P T y = M Q T y

/-- **A class-functorial value function has the value part** (maximal order is not needed). -/
theorem MaxOrderClassValue.of_classFunctorialFor {Λ : Type v} [LinearOrder Λ] {k : ℕ}
    {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
    (h : ClassFunctorialFor (fun {X} P Q => LocWPEquiv (n := n) (X := X) P Q) k M) : MaxOrderClassValue k M :=
  fun P Q hP hQ _ _ hPQ hd hE hS hX _ T hT y hy => h.inv_eq P Q hP hQ hPQ hd hE hS hX T hT y hy

variable {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X} {o : ℕ}

/-- **The companion values of class-equivalent marked ideals agree** (E4 of the class-functoriality induction): with lower
data for `A` and for `B` at the split `T₀ T₁` at `y`, `genLowerValue M A o T₀ T₁ y = genLowerValue M B o T₀ T₁ y`. -/
theorem genLowerValue_eq_of_classData {Λ : Type v} [LinearOrder Λ] {k : ℕ}
    {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
    (hM : IsMaxOrderValue n k M) (hcl : MaxOrderClassValue k M) (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    {Y₀ Y : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (T₁ : BlowupTower Y₀ Y) (y : Y)
    (hLA : GenLowerData M k A o T₀ T₁ y) (hLB : GenLowerData M k B o T₀ T₁ y) :
    genLowerValue M A o T₀ T₁ y = genLowerValue M B o T₀ T₁ y := by
  obtain ⟨hyA, hdomA, hmaxA, hcanA, hcosA⟩ := hLA
  obtain ⟨hyB, hdomB, hmaxB, hcanB, hcosB⟩ := hLB
  have hTB : IsGeoTestTower B T₀ := (h.wEquiv.2 T₀).1.mp hT₀
  have hdA0 := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T₀ hT₀
  have hdB0 := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T₀ hTB
  have hwfA := (InvDomainCompanion.isInvDomain_companionAlong hn hdA0 ho).isWellFormed
  have hwfB := (InvDomainCompanion.isInvDomain_companionAlong hn hdB0 ho).isWellFormed
  have eA := GeneralCompare.compAt_eq_pullback hn (𝔪 := A) o T₀ hdA0
  have eB := GeneralCompare.compAt_eq_pullback hn (𝔪 := B) o T₀ hdB0
  set W : Opens Y₀ := ordMask (geoTransformAlong A T₀) o ⊓ ordMask (geoTransformAlong B T₀) o with hW
  have hyW : T₁.proj y ∈ W := ⟨hyA, hyB⟩
  rw [eA] at hdomA hmaxA hcanA hcosA
  rw [eB] at hdomB hmaxB hcanB hcosB
  obtain ⟨hdomWA, hmaxWA, hcanWA, -⟩ := GeneralCompare.value_restrict_nestedOpens hM hwfA.isCoherent
    (inf_le_left : W ≤ ordMask (geoTransformAlong A T₀) o) hdomA hmaxA T₁ hcanA
  obtain ⟨hdomWB, hmaxWB, hcanWB, -⟩ := GeneralCompare.value_restrict_nestedOpens hM hwfB.isCoherent
    (inf_le_right : W ≤ ordMask (geoTransformAlong B T₀) o) hdomB hmaxB T₁ hcanB
  obtain ⟨hvalA, hcosWA⟩ := GeneralCompare.value_eq_of_two_opens hM hwfA.isClosedSubmanifold_N hwfA.isCoherent T₁
    hdomA hmaxA hcanA hdomWA hmaxWA hcanWA hyA hyW hcosA
  obtain ⟨hvalB, -⟩ := GeneralCompare.value_eq_of_two_opens hM hwfB.isClosedSubmanifold_N hwfB.isCoherent T₁
    hdomB hmaxB hcanB hdomWB hmaxWB hcanWB hyB hyW hcosB
  have ePA := CompanionRebase.pullback_val_companionOf hn hdA0.isWellFormed hdA0.isNonzeroAlongAt W o
  have ePB := CompanionRebase.pullback_val_companionOf hn hdB0.isWellFormed hdB0.isNonzeroAlongAt W o
  have hcls := HironakaG8E4cCompanion.companionOf_classData_maskInter h hA hB hN hd h0 hn ho T₀ hT₀
  obtain ⟨hL, -, -, hdPQ, hEPQ, hSCD, hexp⟩ := hcls
  rw [ePA] at hdomWA hmaxWA hcanWA hcosWA
  rw [ePB] at hdomWB hmaxWB
  have hval := hcl _ _ hdomWA hdomWB hmaxWA hmaxWB hL hdPQ hEPQ hSCD hexp (restrict W T₁) hcanWA ⟨y, hyW⟩ hcosWA
  rw [← ePA, ← ePB] at hval
  unfold genLowerValue
  rw [dif_pos hyA, dif_pos hyB]
  refine congrArg _ ?_
  show M (compAt A o T₀) (restrict (ordMask (geoTransformAlong A T₀) o) T₁) ⟨y, hyA⟩ =
    M (compAt B o T₀) (restrict (ordMask (geoTransformAlong B T₀) o) T₁) ⟨y, hyB⟩
  rw [eA, eB]
  exact (hvalA.trans hval).trans hvalB.symm

end

end Hironaka.HironakaG8E4cValue
