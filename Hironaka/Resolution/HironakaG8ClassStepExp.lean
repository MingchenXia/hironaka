import Hironaka.Resolution.HironakaG8ClassStepDim
import Hironaka.Resolution.HironakaG8BornExponents
import Hironaka.Resolution.HironakaG8P1ForeignCount
import Hironaka.MarkedIdeal.CodimOneSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents at or above the mark are class invariants (G8C lane, run 0080, round 3; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-exp.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §6c (module 10) and §6d; this lane's
`REPORT-r2.md` ("The remaining hypothesis `hExp`").  Source: Bierstone--Milman 2008, Theorem 6.1 (the order `μ_a = ord_a/d` is an
invariant of the `s(i,ii)`-class for carriers of equal dimension; lane G8B's port P1) and the definition of `ord_{H,a}` in §5,
(5.3).

The exponent of a marked ideal `P` along a member `H` of its divisor at a point `y` is the largest `e` such that near `y` every
point of the trace `P.N ∩ H` has order `≥ e` (`DivisorExponentAlong.divExpAlong`).  **When this exponent is at least the mark**,
i.e. near `y` the whole trace `P.N ∩ H` lies in the cosupport, every order entering it is the order at a cosupport point, which
is a class invariant for carriers of equal dimension (BM08 Theorem 6.1); and the trace of `H` on the other carrier is the same
germ (it contains the trace on the first carrier, which lies in the common cosupport, and has the same dimension).  Hence:

* **`divExpAlong_eq_of_isDivNearAlong_mark`** (generic, the shared core lemma): for `P ≈ Q` (`LocWPEquiv`) in the native domain
  with carriers of the same dimension on the cosupport and the same mark, at a cosupport point `y` on a member `H` where `P` is
  divisible by `𝓘_H^{d}` along its carrier near `y`, the exponents of `P` and `Q` along `H` at `y` agree;
* `ExpAgreeBelowMark P Q`: agreement of the exponents only at the points where the exponent of `P` is below the mark;
  **`expAgree_of_expAgreeBelowMark`**: `ExpAgree P Q` follows from it;
* **`lowerPairs_expAgree_of_belowMark`**: for the lower ideals of class-equivalent `A`, `B` (`HironakaG8ClassStep.LowerPairs`),
  the boundary-exponent part of the class data reduces to the exponents below the mark;
* **`classFunctorialMaxOrder_stepOneInvBM_of_belowMark`**: (B') plan module 10 (lane G11B's statement, I-1361) with the extra
  hypothesis `hExp` of `HironakaG8ClassStepDim.classFunctorialMaxOrder_stepOneInvBM_of_exp` weakened to the exponents below the
  mark.

Sorry-free.  Universe `0` (lane G8B's P1 is stated there).  Import discipline: no import of `Hironaka.RelativePrincipalization`
or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8ClassStepExp

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.DivisorExponentAlong Hironaka.HironakaG8LocalHistory
  Hironaka.MarkedIdealBiholomorphism Hironaka.HironakaG11InvBMLower
  Hironaka.GermIdealOrder
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)

noncomputable section

variable {n : ℕ}

/-! ### The core lemma -/

section Core

variable {X : CMfd.{0} n}

/-- **Exponents at or above the mark are class invariants** (BM08 Theorem 6.1 on the trace of the member): for `P ≈ Q`
(`LocWPEquiv`) in the native domain with carriers of the same dimension on the cosupport and the same mark, at a cosupport
point `y` on a member `H` of the divisor of `P` such that near `y` the trace `P.N ∩ H` lies in the cosupport
(`IsDivNearAlong n P.N P.ideal H P.d y`, i.e. the exponent of `P` along `H` at `y` is `≥ P.d`), the exponents of `P` and `Q`
along `H` at `y` agree. -/
theorem divExpAlong_eq_of_isDivNearAlong_mark (hn : 0 < n) {kP kQ : ℕ} {P Q : MarkedIdeal n X}
    (h : LocWPEquiv P Q) (hP : IsInvDomain kP P) (hQ : IsInvDomain kQ Q) (hdim : SameCarrierDim P Q)
    (hd : Q.d = P.d) {H : Set X} (hHP : H ∈ P.E) {y : X} (hy : y ∈ P.cosupp) (hyH : y ∈ H)
    (hsub : IsDivNearAlong n P.N P.ideal H P.d y) :
    divExpAlong n P.N P.ideal H y = divExpAlong n Q.N Q.ideal H y := by
  have hcos : P.cosupp = Q.cosupp := LocEquiv.cosupp_eq_base h
  have hHQ : H ∈ Q.E := (LocEquiv.E_eq h).symm ▸ hHP
  have hOrd : HironakaG8ProjEquiv.TowerOrdAgree P Q :=
    HironakaG8BornExponents.projEquiv_towerOrdAgree_of_sameCarrierDim (LocEquiv.projEquiv h) hP hQ hdim hd
  have hord : ∀ z ∈ P.cosupp, ordinaryTraceOrder P.N P.ideal z = ordinaryTraceOrder Q.N Q.ideal z :=
    fun z hz => hOrd (BlowupTower.refl : BlowupTower X X) trivial z hz
  have iffP : ∀ {z : X}, z ∈ P.N → ∀ e : ℕ, z ∈ cosupport n P.N P.ideal e ↔ e ≤ ordinaryTraceOrder P.N P.ideal z :=
    fun hz e => ordinaryTraceOrder_cosupport_iff hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent
      hP.isNonzeroAlongAt hz e
  have iffQ : ∀ {z : X}, z ∈ Q.N → ∀ e : ℕ, z ∈ cosupport n Q.N Q.ideal e ↔ e ≤ ordinaryTraceOrder Q.N Q.ideal z :=
    fun hz e => ordinaryTraceOrder_cosupport_iff hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent
      hQ.isNonzeroAlongAt hz e
  -- the traces of `H` on the two carriers agree near `y` (filling)
  have hyP : y ∈ P.N := P.cosupp_subset_N hy
  have hyQ : y ∈ Q.N := Q.cosupp_subset_N (hcos ▸ hy)
  obtain ⟨a, ha⟩ := hP.isWellFormed.isClosedSubmanifold_N.2 y hyP
  have haQ : RegularAtDim (n := n) Q.N y a := (hdim y hy a).mp ha
  have hPH := (HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hP.isWellFormed.isTransverse hHP hyP hyH ha).2
  have hQH := (HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hQ.isWellFormed.isTransverse hHQ hyQ hyH haQ).2
  obtain ⟨i, hi⟩ := List.get_of_mem hHP
  have hPHc : IsClosedSubmanifold n (P.N ∩ H) := by
    have h1 := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hP.isWellFormed.isClosedSubmanifold_N.1
      hP.isWellFormed.isSNCDivisor hP.isWellFormed.isTransverse {i}
    rwa [memberInter_singleton, hi] at h1
  have hfill : ∀ᶠ z in 𝓝 y, z ∈ Q.N ∩ H → z ∈ P.N ∩ H :=
    CodimOneSupport.eventually_mem_of_locDimGE
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hPHc) hQH
      (Filter.Eventually.mono hsub fun z hz hzPH => ⟨Q.cosupp_subset_N (hcos ▸ hz hzPH.1 hzPH.2), hzPH.2⟩)
      (AnalyticDimensionBasics.locDimGE_of_regularAtDim hPH)
  refine HironakaG8MixedBoundaryExponents.divExpAlong_congr fun e => ?_
  unfold IsDivNearAlong
  constructor
  · intro h1
    filter_upwards [h1, hsub, hfill] with z hz hzs hzf hzQ hzH
    have hzP : z ∈ P.N := (hzf ⟨hzQ, hzH⟩).1
    have hzc : z ∈ P.cosupp := hzs hzP hzH
    refine (iffQ hzQ e).mpr ?_
    rw [← hord z hzc]
    exact (iffP hzP e).mp (hz hzP hzH)
  · intro h1
    filter_upwards [h1, hsub] with z hz hzs hzP hzH
    have hzc : z ∈ P.cosupp := hzs hzP hzH
    have hzQ : z ∈ Q.N := Q.cosupp_subset_N (hcos ▸ hzc)
    refine (iffP hzP e).mpr ?_
    rw [hord z hzc]
    exact (iffQ hzQ e).mp (hz hzQ hzH)

end Core

/-! ### Agreement below the mark suffices -/

section BelowMark

variable {Y : CMfd.{0} n}

/-- **Agreement of the boundary exponents below the mark**: at every cosupport point `y` of `P` on a member `H` of the divisor
of `P` at which `P` is NOT divisible by `𝓘_H^{P.d}` along its carrier near `y` (the exponent of `P` along `H` at `y` is below the
mark), the exponents of `P` and `Q` along `H` at `y` agree. -/
def ExpAgreeBelowMark (P Q : MarkedIdeal n Y) : Prop :=
  ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H → ¬ IsDivNearAlong n P.N P.ideal H P.d y →
    divExpAlong n P.N P.ideal H y = divExpAlong n Q.N Q.ideal H y

/-- `ExpAgree` implies its restriction below the mark. -/
theorem ExpAgree.belowMark {P Q : MarkedIdeal n Y} (h : ExpAgree P Q) : ExpAgreeBelowMark P Q :=
  fun H hH y hy hyH _ => h H hH y hy hyH

/-- **Agreement below the mark suffices** (BM08 Theorem 6.1 above the mark): for `P ≈ Q` in the native domain with carriers of
the same dimension on the cosupport and the same mark, `ExpAgree P Q` follows from `ExpAgreeBelowMark P Q`. -/
theorem expAgree_of_expAgreeBelowMark (hn : 0 < n) {kP kQ : ℕ} {P Q : MarkedIdeal n Y} (h : LocWPEquiv P Q)
    (hP : IsInvDomain kP P) (hQ : IsInvDomain kQ Q) (hdim : SameCarrierDim P Q) (hd : Q.d = P.d)
    (hres : ExpAgreeBelowMark P Q) : ExpAgree P Q := by
  intro H hH y hy hyH
  by_cases hsub : IsDivNearAlong n P.N P.ideal H P.d y
  · exact divExpAlong_eq_of_isDivNearAlong_mark hn h hP hQ hdim hd hH hy hyH hsub
  · exact hres H hH y hy hyH hsub

end BelowMark

/-! ### The lower ideals of class-equivalent marked ideals -/

section Lower

variable {X : CMfd.{0} n}

/-- **The boundary-exponent part of the class data of the lower ideals reduces to the exponents below the mark**: for
class-equivalent marked ideals `A ≈ B` of the domain of maximal order (`LocWPEquiv`, the same mark and divisor, carriers of the
same dimension on the cosupport), if on every common open of the masks the two restricted lower ideals have the same exponents
below the mark, they have the same boundary exponents. -/
theorem lowerPairs_expAgree_of_belowMark (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (hres : LowerPairs A B fun {_} P Q => ExpAgreeBelowMark P Q) :
    LowerPairs A B fun {_} P Q => ExpAgree P Q := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB
  have hloc := HironakaG8ClassStepCut.lowerPairs_locWPEquiv hn hA hB hmA hmB h hE T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r'
    hdA hdB
  have hsd := HironakaG8ClassStepDim.lowerPairs_sameCarrierDim hn hA hB hmA hmB h hE hdim T₀ hT₀ s y₀ hy₀ hreg O hOA hOB
    r r' hdA hdB
  have hdd : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀)).d =
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀)).d :=
    HironakaG8ClassStep.lowerIdealBM_d_eq hd.symm s T₀ y₀ y₀
  exact expAgree_of_expAgreeBelowMark hn hloc hdA hdB hsd hdd (hres T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **(B') plan module 10, given the boundary exponents of the lower ideals below the mark**: lane G11B's statement (I-1361)
with the extra hypothesis `hExp` of `HironakaG8ClassStepDim.classFunctorialMaxOrder_stepOneInvBM_of_exp` weakened to the points
where the exponent of the lower ideal of `A` along a born member is below the mark of the lower ideals. -/
theorem classFunctorialMaxOrder_stepOneInvBM_of_belowMark (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    (hTI : ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R)
    (hExpB : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
      LowerPairs A B fun {_} P Q => ExpAgreeBelowMark P Q) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) :=
  HironakaG8ClassStepDim.classFunctorialMaxOrder_stepOneInvBM_of_exp hn R hR hTI
    fun A B hA hB hmA hmB h hd hE hdim h0 =>
      lowerPairs_expAgree_of_belowMark hn hA hB hmA hmB h hd hE hdim (hExpB A B hA hB hmA hmB h hd hE hdim h0)

end Lower

end

end Hironaka.HironakaG8ClassStepExp
