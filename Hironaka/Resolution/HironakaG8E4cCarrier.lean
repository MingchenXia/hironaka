import Hironaka.Resolution.HironakaG8E4cGeneric
import Hironaka.Resolution.HironakaG8E4cValue
import Hironaka.Resolution.HironakaG8P1ArcTower
import Hironaka.Resolution.HironakaActualOldDivisorExponentTransport
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaOriginalSmoothIntrinsicRegularLoci
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.Analytic.AnalyticSubsetOpens

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# E4c for DIFFERENT carriers of equal dimension (G8C lane, run 0080; (B') P5 with D2)

Blueprint: `hironaka-g8-e4c-carrier.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §0 D2 ("carriers may
differ (equal local dimension)"), §2 P1, P5, P6; `HironakaG11InvBMClass.ClassFunctorialFor` (hypothesis `SameCarrierDim`,
not equal carriers).  Source: Bierstone--Milman 2008, Theorem 6.1 (the order is a class invariant for carriers of the same
dimension), Corollary 5.3, §5 Step II.B.

`HironakaG8E4cCompanion` proves E4c for the same carrier.  The class-functoriality induction compares marked ideals whose
carriers may differ (BM's maximal-contact hypersurfaces of two equivalent ideals).  With lane G8B's port P1
(`HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv`: the normalized order is a class invariant for carriers of
the same dimension) the comparison carries over node by node:

* `ord_eq_of_carrierBase`, `nmOrd_eq_of_carrierBase` (E1 at a node): `LocWPEquiv`, native domain, `SameCarrierDim`, same mark
  ⇒ equal orders on the cosupport; with agreeing exponents also equal orders of the nonmonomial parts (`whole_factor_order`);
* `divExpAlong_centre_eq_of_carrier`: the exponents along a subset of the common cosupport agree (equal orders there);
* `regularAtDim_iff_of_common`, **`carrierBase_geoTransform`** (P6 for one blowup): `LocWPEquiv`, domain, `SameCarrierDim` and
  agreeing exponents survive one admissible blowup (old exponents are kept, `original_history_old_exponent`; the born
  exponent is the exponent along the centre minus the mark, `original_history_born_exponent`; carriers: strict transforms of
  regular sets keep their dimension), `carrierBase_geoTransformAlong` (along test towers);
* `expAgree_projectionTest_of_mem`, `carrierBase_projectionTest`, `carrierBase_pullback_val`: products with a line, open
  restrictions;
* `CarrierData o A B`, **`compClass_carrierData`**: an instance of `HironakaG8E4cGeneric.CompClass`;
* **`locWPEquiv_companionOf_carrier`**, **`companionOf_classData_carrier`**, `companionOf_classData_stage_restrict_carrier`,
  **`companionOf_classData_maskInter_carrier`** (E4c for different carriers, with the class data of `ClassFunctorialFor`);
* **`genLowerValue_eq_of_carrierData`**: the companion values agree (E4 of plan module 11, different carriers).

Sorry-free.  Universe `0`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8E4cCarrier

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.DivisorExponentAlong
  Hironaka.GermIdealOrder Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.CompanionReductionAlong (companionAlong companionAlong_N companionAlong_E)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal
  projection_test_isInvDomain)
open Hironaka.NonmonomialOrderLocal (ordGe nmOrd)
open Hironaka.NonmonomialOrderTail (ordMask mem_ordMask_iff)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform geoStrictTransform_subset_preimage)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.GeneralValue (compAt genLowerValue GenLowerData)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaG8E4cGeneric (CompClass locWPEquiv_companionOf_of
  expAgree_companionOf_of_mem)
open Hironaka.HironakaG8E4cCompanion (companion_wf)
open Hironaka.HironakaG8E4cMonomialStep (companion_step_facts
  restrictEquiv_nonmonomial_geoTransform)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-! ### Dimensions -/

/-- Two sets regular at `p` of one common dimension have the same regular dimensions at `p`. -/
theorem regularAtDim_iff_of_common {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel m) M]
    {S S' : Set M} {p : M} {a : ℕ} (h : RegularAtDim (n := m) S p a) (h' : RegularAtDim (n := m) S' p a) (j : ℕ) :
    RegularAtDim (n := m) S p j ↔ RegularAtDim (n := m) S' p j :=
  ⟨fun hj => (RegularPointDimension.eq_of_regularAtDim h hj) ▸ h',
    fun hj => (RegularPointDimension.eq_of_regularAtDim h' hj) ▸ h⟩

section Node

variable {m : ℕ} {Y : CMfd.{0} m} {kA kB : ℕ} {A B : MarkedIdeal m Y}

/-! ### E1 at a node -/

/-- **Equal orders on the cosupport** (lane G8B's P1 for the same mark). -/
theorem ord_eq_of_carrierBase (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) {x : Y} (hx : x ∈ A.cosupp) :
    ordinaryTraceOrder A.N A.ideal x = ordinaryTraceOrder B.N B.ideal x := by
  have hxB : x ∈ B.cosupp := h.cosupp_eq_base ▸ hx
  have hW : WEquiv (projectionTest A) (projectionTest B) :=
    ((isLocStable_locEquiv Kinds.wp).projection rfl h).wEquiv
  have h1 := HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv A B hA hB x hx hxB hW hdim
  rw [hd] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

/-- **Equal orders of the nonmonomial parts on the cosupport** (E1 at a node, different carriers). -/
theorem nmOrd_eq_of_carrierBase (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < m) {x : Y} (hx : x ∈ A.cosupp) :
    nmOrd A x = nmOrd B x := by
  have hxB : x ∈ B.cosupp := h.cosupp_eq_base ▸ hx
  obtain ⟨-, -, hoA, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hn A
    hA.isWellFormed hA.isNonzeroAlongAt x (A.cosupp_subset_N hx)
  obtain ⟨-, -, hoB, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hn B
    hB.isWellFormed hB.isNonzeroAlongAt x (B.cosupp_subset_N hxB)
  have hs : (∑ i ∈ MonomialCase.memberIdx B.E x, MonomialCaseAlong.expDataAlong m B.N B.ideal B.E x i) =
      ∑ i ∈ MonomialCase.memberIdx A.E x, MonomialCaseAlong.expDataAlong m A.N A.ideal A.E x i := by
    rw [h.E_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi', hxi⟩ := (MonomialCase.mem_memberIdx A.E).mp hi
    simp only [MonomialCaseAlong.expDataAlong, dif_pos hi']
    exact (h0 _ (List.get_mem _ _) x hx hxi).symm
  have hord := ord_eq_of_carrierBase h hA hB hdim hd hx
  rw [hs] at hoB
  omega

/-- **The exponents along a subset of the common cosupport agree** (equal orders there). -/
theorem divExpAlong_centre_eq_of_carrier (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hcos : A.cosupp = B.cosupp)
    (hord : ∀ x ∈ A.cosupp, ordinaryTraceOrder A.N A.ideal x = ordinaryTraceOrder B.N B.ideal x) {C : Set Y}
    (hC : C ⊆ A.cosupp) (x : Y) : divExpAlong m A.N A.ideal C x = divExpAlong m B.N B.ideal C x := by
  refine HironakaG8E4cProduct.divExpAlong_congr_of_iff fun e => ?_
  unfold IsDivNearAlong
  refine eventually_congr (Eventually.of_forall fun z => ?_)
  constructor
  · intro hz hzB hzC
    have hzA : z ∈ A.cosupp := hC hzC
    have hzNA := A.cosupp_subset_N hzA
    have h1 := (ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      hA.isNonzeroAlongAt hzNA e).mp (hz hzNA hzC)
    rw [hord z hzA] at h1
    exact (ordinaryTraceOrder_cosupport_iff hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent
      hB.isNonzeroAlongAt hzB e).mpr h1
  · intro hz hzA hzC
    have hzA' : z ∈ A.cosupp := hC hzC
    have hzNB := B.cosupp_subset_N (hcos ▸ hzA')
    have h1 := (ordinaryTraceOrder_cosupport_iff hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent
      hB.isNonzeroAlongAt hzNB e).mp (hz hzNB hzC)
    rw [← hord z hzA'] at h1
    exact (ordinaryTraceOrder_cosupport_iff hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      hA.isNonzeroAlongAt hzA e).mpr h1

/-! ### One admissible blowup -/

/-- **The base class data survive one admissible blowup** (P6 for one step): `LocWPEquiv`, the domain, `SameCarrierDim`
and agreeing exponents (same mark). -/
theorem carrierBase_geoTransform (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) {C : Set Y} {Z : CMfd.{0} m} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hC : A.IsAdmissibleCentre C) :
    LocWPEquiv (A.geoTransform C π) (B.geoTransform C π) ∧ IsInvDomain kA (A.geoTransform C π) ∧
      IsInvDomain kB (B.geoTransform C π) ∧ SameCarrierDim (A.geoTransform C π) (B.geoTransform C π) ∧
      ExpAgree (A.geoTransform C π) (B.geoTransform C π) := by
  have hcos0 : A.cosupp = B.cosupp := h.cosupp_eq_base
  have hCB : B.IsAdmissibleCentre C := (isAdmissibleCentre_congr h.E_eq.symm hcos0 C).mp hC
  have hL := (isLocStable_locEquiv Kinds.wp).controlled h C π hπ hC
  have hcos' : (A.geoTransform C π).cosupp = (B.geoTransform C π).cosupp := hL.cosupp_eq_base
  have hA' : IsInvDomain kA (A.geoTransform C π) :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hA (.step .refl C π hπ) ⟨trivial, hC⟩
  have hB' : IsInvDomain kB (B.geoTransform C π) :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hB (.step .refl C π hπ) ⟨trivial, hCB⟩
  have hholA : ∀ x g, A.ideal.mem x g → HolomorphicAt m g x :=
    fun _ _ hg => Hironaka.RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg
  have hproj : ∀ z ∈ (A.geoTransform C π).cosupp, π z ∈ A.cosupp := fun z hz =>
    TransformOffCentre.cosupp_geoTransform_subset_preimage A hA.isWellFormed.isClosedSubmanifold_N.1 hholA hπ hC.2.1 hz
  have hCNB : C ⊆ B.N := fun x hx => B.cosupp_subset_N (hcos0 ▸ hC.2.1 hx)
  refine ⟨hL, hA', hB', ?_, ?_⟩
  · -- carriers: strict transforms keep the dimension
    intro z hz j
    have hzB : z ∈ (B.geoTransform C π).cosupp := hcos' ▸ hz
    have hπz := hproj z hz
    obtain ⟨a, ha⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 (π z) (A.cosupp_subset_N hπz)
    have hb : RegularAtDim (n := m) B.N (π z) a := (hdim (π z) hπz a).mp ha
    have key : ∀ N : Set Y, IsClosed N → C ⊆ N → RegularAtDim (n := m) N (π z) a →
        z ∈ geoStrictTransform π C N → RegularAtDim (n := m) (geoStrictTransform π C N) z a := by
      intro N hNc hCN hNa hzN
      by_cases hzC : π z ∈ C
      · obtain ⟨c, hc⟩ := hπ.1.2 (π z) hzC
        exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform_of_mem hπ
          (BlowupStrictSubmanifold.le_of_regularAtDim_subset hc hNa hCN) hc hNa hCN hzN
      · exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform_of_notMem hπ hNc hzC hNa
    exact regularAtDim_iff_of_common
      (key A.N hA.isWellFormed.isClosedSubmanifold_N.1 hC.subset_N ha
        ((A.geoTransform C π).cosupp_subset_N hz))
      (key B.N hB.isWellFormed.isClosedSubmanifold_N.1 hCNB hb ((B.geoTransform C π).cosupp_subset_N hzB)) j
  · -- exponents: old members keep theirs, the born member gets the exponent along the centre minus the mark
    intro H hH z hz hzH
    have hzB : z ∈ (B.geoTransform C π).cosupp := hcos' ▸ hz
    have hzNA : z ∈ (A.geoTransform C π).N := (A.geoTransform C π).cosupp_subset_N hz
    have hzNB : z ∈ (B.geoTransform C π).N := (B.geoTransform C π).cosupp_subset_N hzB
    have hπz := hproj z hz
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH₀
      have hH₀B : A.E.get i ∈ B.E := by
        rw [h.E_eq]
        exact List.get_mem _ _
      obtain ⟨i', hi'⟩ := List.mem_iff_get.mp hH₀B
      have eA : divExpAlong m (A.geoTransform C π).N (A.geoTransform C π).ideal
          (geoStrictTransform π C (A.E.get i)) z = divExpAlong m A.N A.ideal (A.E.get i) (π z) :=
        HironakaActualOldDivisorExponentTransport.original_history_old_exponent A hA .refl trivial hC hπ i hzNA hzH
      have eB : divExpAlong m (B.geoTransform C π).N (B.geoTransform C π).ideal
          (geoStrictTransform π C (B.E.get i')) z = divExpAlong m B.N B.ideal (B.E.get i') (π z) :=
        HironakaActualOldDivisorExponentTransport.original_history_old_exponent B hB .refl trivial hCB hπ i' hzNB
          (by show z ∈ geoStrictTransform π C (B.E.get i'); rw [hi']; exact hzH)
      rw [hi'] at eB
      rw [eA, eB]
      have hπzH : π z ∈ A.E.get i :=
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous
          (hA.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _)) hzH
      exact h0 _ (List.get_mem _ _) (π z) hπz hπzH
    · rw [List.mem_singleton.mp hH] at hzH ⊢
      have bA : divExpAlong m (A.geoTransform C π).N (A.geoTransform C π).ideal (π ⁻¹' C) z =
          divExpAlong m A.N A.ideal C (π z) - A.d :=
        (HironakaActualLocalBornExponent.original_history_born_exponent A hA .refl trivial hC hπ hzNA hzH).2
      have bB : divExpAlong m (B.geoTransform C π).N (B.geoTransform C π).ideal (π ⁻¹' C) z =
          divExpAlong m B.N B.ideal C (π z) - B.d :=
        (HironakaActualLocalBornExponent.original_history_born_exponent B hB .refl trivial hCB hπ hzNB hzH).2
      rw [bA, bB, hd, divExpAlong_centre_eq_of_carrier hA hB hcos0
        (fun x hx => ord_eq_of_carrierBase h hA hB hdim hd hx) hC.2.1 (π z)]

/-- **Along test towers of `A`** the base class data survive. -/
theorem carrierBase_geoTransformAlong (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) :
    ∀ {Y₀ : CMfd.{0} m} (T₀ : BlowupTower Y Y₀), IsGeoTestTower A T₀ →
      LocWPEquiv (geoTransformAlong A T₀) (geoTransformAlong B T₀) ∧ IsInvDomain kA (geoTransformAlong A T₀) ∧
        IsInvDomain kB (geoTransformAlong B T₀) ∧ SameCarrierDim (geoTransformAlong A T₀) (geoTransformAlong B T₀) ∧
        ExpAgree (geoTransformAlong A T₀) (geoTransformAlong B T₀)
  | _, .refl, _ => ⟨h, hA, hB, hdim, h0⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    obtain ⟨h', hA', hB', hdim', h0'⟩ := carrierBase_geoTransformAlong h hA hB hdim hd h0 T hTT
    have hd' : (geoTransformAlong B T).d = (geoTransformAlong A T).d := by
      rw [d_geoTransformAlong, d_geoTransformAlong, hd]
    exact carrierBase_geoTransform h' hA' hB' hdim' hd' h0' hπ hC

/-! ### Products with a line and open restrictions -/

/-- **Agreement of boundary exponents passes to products with a line** (the second carrier contains the first cosupport;
no equality of carriers). -/
theorem expAgree_projectionTest_of_mem (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    (hneA : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) (hneB : ∀ y ∈ B.N, IsNonzeroAlongAt B.N B.ideal y)
    (hNB : ∀ y ∈ A.cosupp, y ∈ B.N) (h : ExpAgree A B) : ExpAgree (projectionTest A) (projectionTest B) := by
  intro H hH y hy hyH
  have hy' : y.1 ∈ A.cosupp := by
    have := hy
    rw [HironakaG8E4cProduct.cosupp_projectionTest hA] at this
    exact this
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    show divExpAlong (m + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' A.N)
        (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) A.ideal)
        ((Prod.fst : projectionAmbient Y → Y) ⁻¹' H₀) y =
      divExpAlong (m + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' B.N)
        (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) B.ideal)
        ((Prod.fst : projectionAmbient Y → Y) ⁻¹' H₀) y
    rw [HironakaG8E4cProduct.divExpAlong_fst hA, HironakaG8E4cProduct.divExpAlong_fst hB]
    exact h H₀ hH₀ y.1 hy' hyH
  · rw [List.mem_singleton.mp hH] at hyH ⊢
    show divExpAlong (m + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' A.N)
        (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) A.ideal) (horizontal Y) y =
      divExpAlong (m + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' B.N)
        (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) B.ideal) (horizontal Y) y
    rw [HironakaG8E4cProduct.horizontal_exp_zero hA hneA y (A.cosupp_subset_N hy') hyH,
      HironakaG8E4cProduct.horizontal_exp_zero hB hneB y (hNB _ hy') hyH]

/-- **The base class data pass to products with a line.** -/
theorem carrierBase_projectionTest (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (h0 : ExpAgree A B) :
    LocWPEquiv (projectionTest A) (projectionTest B) ∧ IsInvDomain (kA + 1) (projectionTest A) ∧
      IsInvDomain (kB + 1) (projectionTest B) ∧ SameCarrierDim (projectionTest A) (projectionTest B) ∧
      ExpAgree (projectionTest A) (projectionTest B) := by
  have hcos0 : A.cosupp = B.cosupp := h.cosupp_eq_base
  have hsub := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
  refine ⟨(isLocStable_locEquiv Kinds.wp).projection rfl h, projection_test_isInvDomain A hA,
    projection_test_isInvDomain B hB, ?_,
    expAgree_projectionTest_of_mem hA.isWellFormed.isCoherent hB.isWellFormed.isCoherent hA.isNonzeroAlongAt
      hB.isNonzeroAlongAt (fun y hy => B.cosupp_subset_N (hcos0 ▸ hy)) h0⟩
  intro p hp j
  have hp' : p.1 ∈ A.cosupp := by
    have := hp
    rw [HironakaG8E4cProduct.cosupp_projectionTest hA.isWellFormed.isCoherent] at this
    exact this
  obtain ⟨a, ha⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 p.1 (A.cosupp_subset_N hp')
  have hb : RegularAtDim (n := m) B.N p.1 a := (hdim p.1 hp' a).mp ha
  exact regularAtDim_iff_of_common
    ((HironakaOriginalSmoothIntrinsicRegularLoci.regularAtDim_preimage_iff (Y := projectionAmbient Y)
      (b := Prod.fst) (hsub.isSubmersionAt p) A.N a).mpr ha)
    ((HironakaOriginalSmoothIntrinsicRegularLoci.regularAtDim_preimage_iff (Y := projectionAmbient Y)
      (b := Prod.fst) (hsub.isSubmersionAt p) B.N a).mpr hb) j

/-- **The base class data restrict to open subsets.** -/
theorem carrierBase_pullback_val (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (h0 : ExpAgree A B) (U : Opens Y) :
    LocWPEquiv (X := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) A)
        (MarkedIdeal.pullback (Subtype.val : U → Y) B) ∧
      IsInvDomain kA (MarkedIdeal.pullback (Subtype.val : U → Y) A) ∧
      IsInvDomain kB (MarkedIdeal.pullback (Subtype.val : U → Y) B) ∧
      SameCarrierDim (X := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) A)
        (MarkedIdeal.pullback (Subtype.val : U → Y) B) ∧
      ExpAgree (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) A)
        (MarkedIdeal.pullback (Subtype.val : U → Y) B) := by
  have hholA : ∀ x g, A.ideal.mem x g → HolomorphicAt m g x :=
    fun _ _ hg => Hironaka.RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg
  have hholB : ∀ x g, B.ideal.mem x g → HolomorphicAt m g x :=
    fun _ _ hg => Hironaka.RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
  refine ⟨h.restrict U, InvDomainTowerAlong.isInvDomain_pullback_val U hA,
    InvDomainTowerAlong.isInvDomain_pullback_val U hB, ?_,
    HironakaG8LocalCompanion.expAgree_pullback_val hholA hholB h0 U⟩
  intro x hx j
  have hx' : (x : Y) ∈ A.cosupp := by
    have h1 := MarkedIdealRestrictOpen.cosupp_pullback_val A hholA U
    have h2 : x ∈ (MarkedIdeal.pullback (Subtype.val : U → Y) A).cosupp := hx
    rw [h1] at h2
    exact h2
  show RegularAtDim (n := m) ((Subtype.val : U → Y) ⁻¹' A.N) x j ↔
    RegularAtDim (n := m) ((Subtype.val : U → Y) ⁻¹' B.N) x j
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff]
  exact hdim x hx' j

end Node

/-! ### The class data and E4c -/

section Class

/-- **The class data for different carriers**: locally `s(i,ii)`-equivalent, native domain, carriers of the same dimension
on the cosupport, same mark, agreeing exponents, positive dimension, `o ≥ 1`, `ord(𝓝) ≤ o` on both cosupports. -/
structure CarrierData {m : ℕ} {Y : CMfd.{0} m} (o : ℕ) (A B : MarkedIdeal m Y) : Prop where
  equiv : LocWPEquiv A B
  invA : ∃ k, IsInvDomain k A
  invB : ∃ k, IsInvDomain k B
  dim : SameCarrierDim A B
  d_eq : B.d = A.d
  exp : ExpAgree A B
  pos : 0 < m
  one_le : 1 ≤ o
  boundA : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)
  boundB : ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1)

variable {m : ℕ} {Y : CMfd.{0} m} {o : ℕ} {A B : MarkedIdeal m Y}

/-- **The companions of class data have the same cosupport** (E1 at the node). -/
theorem CarrierData.cosupp_eq (hD : CarrierData o A B) :
    (companionOf m A o).cosupp = (companionOf m B o).cosupp := by
  obtain ⟨kA, hA⟩ := hD.invA
  obtain ⟨kB, hB⟩ := hD.invB
  have hcA := (HironakaG8CompanionEquiv.cosupp_companionOf_geoTransformAlong hA hD.pos hD.one_le hD.boundA
    (.refl : BlowupTower Y Y) trivial).2
  have hcB := (HironakaG8CompanionEquiv.cosupp_companionOf_geoTransformAlong hB hD.pos hD.one_le hD.boundB
    (.refl : BlowupTower Y Y) trivial).2
  have hcA' : (companionOf m A o).cosupp = ordGe A o ∩ A.cosupp := hcA
  have hcB' : (companionOf m B o).cosupp = ordGe B o ∩ B.cosupp := hcB
  have hcos0 : A.cosupp = B.cosupp := hD.equiv.cosupp_eq_base
  rw [hcA', hcB']
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    have hxB : x ∈ B.cosupp := hcos0 ▸ h2
    have hν := nmOrd_eq_of_carrierBase hD.equiv hA hB hD.dim hD.d_eq hD.exp hD.pos h2
    refine ⟨(NonmonomialOrderLocal.mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hxB) o).mpr
      ?_, hxB⟩
    rw [← hν]
    exact (NonmonomialOrderLocal.mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt (A.cosupp_subset_N h2) o).mp h1
  · rintro ⟨h1, h2⟩
    have hxA : x ∈ A.cosupp := hcos0.symm ▸ h2
    have hν := nmOrd_eq_of_carrierBase hD.equiv hA hB hD.dim hD.d_eq hD.exp hD.pos hxA
    refine ⟨(NonmonomialOrderLocal.mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt (A.cosupp_subset_N hxA) o).mpr
      ?_, hxA⟩
    rw [hν]
    exact (NonmonomialOrderLocal.mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N h2) o).mp h1

/-- The companions of class data have the same boundary. -/
theorem CarrierData.E_eq (hD : CarrierData o A B) : (companionOf m B o).E = (companionOf m A o).E := by
  simp only [companionOf, companionAlong_E]
  exact hD.equiv.E_eq

/-- **The class data for different carriers are an instance of `CompClass`.** -/
theorem compClass_carrierData (o : ℕ) :
    CompClass o (fun {m} {Y} A B => CarrierData (m := m) (Y := Y) o A B) where
  data hD := ⟨hD.invA, hD.invB, hD.pos, hD.one_le, hD.boundA, hD.boundB⟩
  E_eq hD := hD.equiv.E_eq
  cosupp_eq hD := hD.cosupp_eq
  geoTransform := by
    intro m Y A B hD C Z π hπ hC
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    have hCB : (companionOf m B o).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hD.E_eq.symm hD.cosupp_eq C).mp hC
    have hCA' := (companion_step_facts hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.one_le hD.boundA hπ hC).1
    obtain ⟨hL, hA', hB', hdim', h0'⟩ := carrierBase_geoTransform hD.equiv hA hB hD.dim hD.d_eq hD.exp hπ hCA'
    exact ⟨hL, ⟨kA, hA'⟩, ⟨kB, hB'⟩, hdim', hD.d_eq, h0', hD.pos, hD.one_le,
      (restrictEquiv_nonmonomial_geoTransform hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.one_le hD.boundA hπ hC).2,
      (restrictEquiv_nonmonomial_geoTransform hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.one_le hD.boundB hπ hCB).2⟩
  projectionTest := by
    intro m Y A B hD
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    obtain ⟨hL, hA', hB', hdim', h0'⟩ := carrierBase_projectionTest hD.equiv hA hB hD.dim hD.exp
    exact ⟨hL, ⟨_, hA'⟩, ⟨_, hB'⟩, hdim', hD.d_eq, h0', Nat.succ_pos m, hD.one_le,
      HironakaG8E4cProduct.bound_projectionTest hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.boundA,
      HironakaG8E4cProduct.bound_projectionTest hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.boundB⟩
  restrict := by
    intro m Y A B hD U
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    obtain ⟨hL, hA', hB', hdim', h0'⟩ := carrierBase_pullback_val hD.equiv hA hB hD.dim hD.exp U
    exact ⟨hL, ⟨_, hA'⟩, ⟨_, hB'⟩, hdim', hD.d_eq, h0', hD.pos, hD.one_le,
      CompanionOpen.bound_pullback_val hD.pos hA.isWellFormed hA.isNonzeroAlongAt U fun x hx _ => hD.boundA x hx,
      CompanionOpen.bound_pullback_val hD.pos hB.isWellFormed hB.isNonzeroAlongAt U fun x hx _ => hD.boundB x hx⟩

end Class

section Main

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X} {o : ℕ}

/-- **The bound passes to an equivalent marked ideal** (different carriers). -/
theorem bound_of_carrierBase (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1) := by
  intro x hx hxo
  have hxA : x ∈ A.cosupp := h.cosupp_eq_base ▸ hx
  have hν := nmOrd_eq_of_carrierBase h hA hB hdim hd h0 hn hxA
  refine hbound x hxA ((NonmonomialOrderLocal.mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt
    (A.cosupp_subset_N hxA) (o + 1)).mpr ?_)
  have h1 := (NonmonomialOrderLocal.mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hx)
    (o + 1)).mp hxo
  exact h1.trans_eq hν.symm

/-- **E4c for different carriers**: the companions of locally `s(i,ii)`-equivalent marked ideals of the native domain with
carriers of the same dimension (`SameCarrierDim`), the same mark and agreeing exponents are locally `s(i,ii)`-equivalent
(`n > 0`, `o ≥ 1`, `ord(𝓝_A) ≤ o` on the cosupport). -/
theorem locWPEquiv_companionOf_carrier (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : LocWPEquiv (companionOf n A o) (companionOf n B o) :=
  locWPEquiv_companionOf_of (compClass_carrierData o)
    (⟨h, ⟨kA, hA⟩, ⟨kB, hB⟩, hdim, hd, h0, hn, ho, hbound,
      bound_of_carrierBase h hA hB hdim hd h0 hn hbound⟩ : CarrierData o A B)

/-- **E4c for different carriers, with the class data of `ClassFunctorialFor`.** -/
theorem companionOf_classData_carrier (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) :
    LocWPEquiv (companionOf n A o) (companionOf n B o) ∧ IsInvDomain kA (companionOf n A o) ∧
      IsInvDomain kB (companionOf n B o) ∧ (companionOf n A o).d = (companionOf n B o).d ∧
      (companionOf n A o).E = (companionOf n B o).E ∧ SameCarrierDim (companionOf n A o) (companionOf n B o) ∧
      HironakaG11InvBMClass.ExpAgree (companionOf n A o) (companionOf n B o) := by
  have hcos0 : A.cosupp = B.cosupp := h.cosupp_eq_base
  have hsub : (companionOf n A o).cosupp ⊆ A.cosupp := by
    have hcA := (HironakaG8CompanionEquiv.cosupp_companionOf_geoTransformAlong hA hn ho hbound
      (.refl : BlowupTower X X) trivial).2
    have hcA' : (companionOf n A o).cosupp = ordGe A o ∩ A.cosupp := hcA
    rw [hcA']
    exact inter_subset_right
  refine ⟨locWPEquiv_companionOf_carrier h hA hB hdim hd h0 hn ho hbound,
    InvDomainCompanion.isInvDomain_companionAlong hn hA ho, InvDomainCompanion.isInvDomain_companionAlong hn hB ho,
    ?_, ?_, ?_,
    expAgree_companionOf_of_mem hn hA.isWellFormed hA.isNonzeroAlongAt hB.isWellFormed hB.isNonzeroAlongAt
      (fun y hy => B.cosupp_subset_N (hcos0 ▸ hsub hy)) h.E_eq⟩
  · simp only [companionOf, CompanionRebase.companionAlong_d, hd]
  · simp only [companionOf, companionAlong_E]
    exact h.E_eq.symm
  · intro x hx j
    have h1 := hdim x (hsub hx) j
    simpa only [companionOf, companionAlong_N] using h1

/-- **E4c at a common test stage, on an open subset of the mask** (different carriers). -/
theorem companionOf_classData_stage_restrict_carrier (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n)
    (ho : 1 ≤ o) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (W : Opens Y₀)
    (hW : (W : Set Y₀) ⊆ ordMask (geoTransformAlong A T₀) o) :
    let P := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o
    let Q := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o
    LocWPEquiv P Q ∧ IsInvDomain kA P ∧ IsInvDomain kB Q ∧ P.d = Q.d ∧ P.E = Q.E ∧ SameCarrierDim P Q ∧
      HironakaG11InvBMClass.ExpAgree P Q := by
  obtain ⟨hT, hAT, hBT, hdimT, h0T⟩ := carrierBase_geoTransformAlong h hA hB hdim hd h0 T₀ hT₀
  obtain ⟨hL, hdP, hdQ, hdimW, hexpW⟩ := carrierBase_pullback_val hT hAT hBT hdimT h0T W
  have hdW : (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)).d =
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)).d := by
    show (geoTransformAlong B T₀).d = (geoTransformAlong A T₀).d
    rw [d_geoTransformAlong, d_geoTransformAlong, hd]
  refine companionOf_classData_carrier (X := CMfd.of (n := n) W) hL hdP hdQ hdimW hdW hexpW hn ho ?_
  intro x _ hxo
  have hx : (x : Y₀) ∈ ordGe (geoTransformAlong A T₀) (o + 1) :=
    (NonmonomialOrderLocal.mem_ordGe_pullback_val_iff hn hAT.isWellFormed hAT.isNonzeroAlongAt W (o + 1) x).mp hxo
  exact (mem_ordMask_iff hn hAT.isWellFormed hAT.isNonzeroAlongAt o (x : Y₀)).mp (hW x.2) hx

/-- **E4c on the intersection of the two masks** (different carriers). -/
theorem companionOf_classData_maskInter_carrier (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n)
    (ho : 1 ≤ o) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) :
    let W : Opens Y₀ := ordMask (geoTransformAlong A T₀) o ⊓ ordMask (geoTransformAlong B T₀) o
    let P := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o
    let Q := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o
    LocWPEquiv P Q ∧ IsInvDomain kA P ∧ IsInvDomain kB Q ∧ P.d = Q.d ∧ P.E = Q.E ∧ SameCarrierDim P Q ∧
      HironakaG11InvBMClass.ExpAgree P Q :=
  companionOf_classData_stage_restrict_carrier h hA hB hdim hd h0 hn ho T₀ hT₀ _ fun _ hx => hx.1

open Hironaka.HironakaG8E4cValue (MaxOrderClassValue) in
/-- **The companion values of class-equivalent marked ideals agree** (different carriers of the same dimension). -/
theorem genLowerValue_eq_of_carrierData {Λ : Type v} [LinearOrder Λ] {k : ℕ}
    {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
    (hM : IsMaxOrderValue n k M) (hcl : MaxOrderClassValue k M) (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n)
    (ho : 1 ≤ o) {Y₀ Y : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (T₁ : BlowupTower Y₀ Y)
    (y : Y) (hLA : GenLowerData M k A o T₀ T₁ y) (hLB : GenLowerData M k B o T₀ T₁ y) :
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
  have hcls := companionOf_classData_maskInter_carrier h hA hB hdim hd h0 hn ho T₀ hT₀
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

end Main

end

end Hironaka.HironakaG8E4cCarrier
