import Hironaka.Resolution.HironakaSharpActualCurveOffCentreOrders
import Hironaka.Resolution.HironakaSharpActualRelativeSaturationOpenNaturality
import Hironaka.Resolution.HironakaG4UnitRowGeoTransform

set_option autoImplicit false

/-! Actual individual relative strict order at a locally equimultiple centre.
Complete source-first proof: `hironaka-g4-equimultiple-relative-order.tex`.
Full historical old-boundary compatibility is a separate consumer. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4EquimultipleRelativeOrder

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualMonomialDivisionResidual
  HironakaSharpActualCurveOffCentreOrders HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualCurveExceptionalDifference HironakaSharpOriginalFirstBlowupOpenComparison
  HironakaSharpActualRelativeSaturationOpenNaturality HironakaCoherentTransformExtension
  HironakaG4UnitRowGeoTransform RelativePrincipalizationSpan RestrictedIdealExtension
  RestrictedIdealWeight RestrictedIdealQuotient InvertibleIdealQuotient
  DivisorExponentAlong GermIdealOrder MonomialPartAlong NormalCrossings
  NonmonomialOrderLocal NonmonomialOrderCanonical MarkedIdealRestrictOpen MarkedIdealBiholomorphism

open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem zero_mark_admissible {N C : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) :
    (⟨N,[],I,0⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
  refine ⟨hπ.1,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
  change C ⊆ cosupport n N I 0
  rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
  exact hCN

private theorem ordinary_domain {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x) :
    IsInvDomain (n+1) (ordinaryTraceMarked N I) where
  isWellFormed := ordinaryTraceMarked_isWellFormed hN hI
  dimLE := by
    intro x hx
    obtain ⟨k,hk⟩ := hN.2 x hx
    exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := hnz

private theorem ordinary_order_eq_nmOrd_of_residual {M : MarkedIdeal n X} {S : GermIdeal n X}
    (hS : S.IsCoherent) (hEq : S=nonmonomialPartAlong n M.N M.ideal M.E) (x : X) :
    ordinaryTraceOrder M.N S x=nmOrd M x := by
  symm
  apply nmOrd_congr
  intro q
  change x ∈ cosupport n M.N (nonmonomialPartAlong n M.N M.ideal M.E) q ↔
    x ∈ cosupport n M.N (nonmonomialPartAlong n M.N S []) q
  rw [←hEq,nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨fun hx => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
      (𝔞 := restrictOn n M.N S) (𝔟 := S) restrictLe_restrictOn q hx,
    fun hx => MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe
      (restrictLe_self_restrictOn hS) q hx⟩

private theorem one_mem_of_order_zero {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x) {x : X} (hx : x ∈ N)
    (hzero : ordinaryTraceOrder N I x=0) : I.mem x (fun _ => (1 : ℂ)) := by
  have hnot : x ∉ cosupport n N I 1 := by
    intro hcos
    have hpos := (ordinaryTraceOrder_cosupport_iff hN hI hnz hx 1).mp hcos
    omega
  have hbad : ¬∀ f : X → ℂ,I.mem x f → VanishesToOrderOn n N x 1 f :=
    fun h => hnot ⟨hx,h⟩
  push Not at hbad
  obtain ⟨f,hf,hvan⟩ := hbad
  have hfx : f x ≠ 0 := by
    intro hzero
    exact hvan ((vanishesToOrderOn_one_iff hx (GermIdeal.IsCoherent.holomorphicAt_mem hI hf)).mpr hzero)
  exact CompanionReduction.one_mem_of_apply_ne_zero hI hf hfx

private theorem strict_order_zero_of_one_mem (hn : 0 < n) {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) {z : Y}
    (hz : z ∈ (nextTotalMarked N I C π).N) (hunit : I.mem (π z) (fun _ => (1 : ℂ))) :
    ordinaryTraceOrder (nextTotalMarked N I C π).N (nextRelativeStrict N I C π) z=0 := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  let P := nextTotalMarked N I C π
  have hw : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw
    (zero_mark_admissible hI hπ hCN) hπ
  obtain ⟨hEq,hS,hSNz,_⟩ := nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN
  have hPone : P.ideal.mem z (fun _ => (1 : ℂ)) :=
    (geoTransform_mem_iff_holomorphic_of_one_mem (M := M) (C := C) hunit
      (fun _ => (1 : ℂ))).mpr (holomorphicAt_const 1)
  have hSone : (nextRelativeStrict N I C π).mem z (fun _ => (1 : ℂ)) := by
    rw [hEq]
    exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hwP.isCoherent z _ hPone
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hcos := (ordinaryTraceOrder_cosupport_iff hwP.isClosedSubmanifold_N hS hSNz hz 1).mpr hpos
  have hvan := hcos.2 (fun _ => (1 : ℂ)) hSone
  have hzero := (vanishesToOrderOn_one_iff hz (holomorphicAt_const 1)).mp hvan
  exact one_ne_zero hzero

/-- Every actual current relative principal row has its original ordinary order
off the actual centre, without assigning a positive admissible row mark. -/
theorem nextRelativeStrict_order_eq_off_centre (hn : 0 < n) {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) {z : Y}
    (hz : z ∈ (nextTotalMarked N I C π).N) (hzC : π z ∉ C) :
    ordinaryTraceOrder (nextTotalMarked N I C π).N (nextRelativeStrict N I C π) z=
      ordinaryTraceOrder N I (π z) := by
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  let P := nextTotalMarked N I C π
  let S := nextRelativeStrict N I C π
  have hw : M.IsWellFormed := ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hC := zero_mark_admissible hI hπ hCN
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  obtain ⟨hEq,hS,_hSNz,_⟩ := nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN
  have hTotal : P.ideal=restrictOn n P.N (GermIdeal.pullback (m := n) π I) :=
    HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  have hOff : z ∉ ⋃ D ∈ [π ⁻¹' C],D := by simpa using hzC
  have hMem (g : Y → ℂ) : S.mem z g ↔ P.ideal.mem z g := by
    change (nextRelativeStrict N I C π).mem z g ↔ P.ideal.mem z g
    rw [hEq,hTotal]
    exact actual_normalized_nonmonomial_off_family_iff _ hOff g
  have hOrd : ordinaryTraceOrder P.N S z=ordinaryTraceOrder P.N P.ideal z := by
    apply nmOrd_congr
    intro q
    rw [ordGe_ordinaryTraceMarked_eq_cosupport P.N S hS,
      ordGe_ordinaryTraceMarked_eq_cosupport P.N P.ideal hwP.isCoherent]
    exact ⟨fun ⟨hzN,ho⟩ => ⟨hzN,fun g hg => ho g ((hMem g).mpr hg)⟩,
      fun ⟨hzN,ho⟩ => ⟨hzN,fun g hg => ho g ((hMem g).mp hg)⟩⟩
  exact hOrd.trans (actual_controlled_ordinary_order_off_centre M hw hnz hC hπ hz hzC)

private theorem mem_cosupp_of_mark_le_nmOrd {M : MarkedIdeal n X} {k : ℕ}
    (hM : IsInvDomain k M) {x : X} (hx : x ∈ M.N) (hν : M.d ≤ nmOrd M x) :
    x ∈ M.cosupp := by
  have hle : RestrictLe M.N M.ideal (nonmonomialPartAlong n M.N M.ideal M.E) := by
    intro y _ f hf
    exact IsInSpanAt.restrict (isInSpanAt_self
      (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hM.isWellFormed.isCoherent y f hf)
      (GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf))
  exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hle M.d
    ((mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hx M.d).mpr hν)

private theorem strict_order_le_of_positive_open_level (hn : 0 < n)
    {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) {z : Y}
    (hz : z ∈ (nextTotalMarked N I C π).N) (hzC : π z ∈ C)
    (U : Opens X) (hzU : π z ∈ U) {m : ℕ} (hm : 0 < m)
    (hlevel : ∀ x ∈ C,x ∈ U → ordinaryTraceOrder N I x=m) :
    ordinaryTraceOrder (nextTotalMarked N I C π).N (nextRelativeStrict N I C π) z ≤ m := by
  let M := ordinaryTraceMarked N I
  let M0 : MarkedIdeal n X := ⟨N,[],I,0⟩
  let P := nextTotalMarked N I C π
  let V := firstBlowupSourceOpen hπ U
  let r := firstBlowupOpenProjection hπ U
  let CU : Set U := (Subtype.val : U → X) ⁻¹' C
  let R : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback Subtype.val M
  let R0 : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback Subtype.val M0
  let Q := R.geoTransform CU r
  let Q0 := R0.geoTransform CU r
  let zU : V := ⟨z,hzU⟩
  have hr : IsBlowupAlong n CU r := BlowupRestrictOpen.isBlowupAlong_restrict hπ U _
  have hM : IsInvDomain (n+1) M := ordinary_domain hN hI hnz
  have hR : IsInvDomain (n+1) R := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hRC : R.IsAdmissibleCentre CU := by
    refine ⟨hr.1,?_,?_⟩
    · intro c hc
      change c ∈ (MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp
      rw [cosupp_pullback_val M (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) U]
      change c.val ∈ cosupport n N I 1
      apply (ordinaryTraceOrder_cosupport_iff hN hI hnz (hCN hc) 1).mpr
      rw [hlevel c.val hc c.property]
      exact hm
    · change HasNormalCrossings n CU []
      exact hasNormalCrossings_nil_of_isClosedSubmanifold hr.1
  have hRlevel : ∀ c ∈ CU,nmOrd R c=m := by
    intro c hc
    exact (nmOrd_pullback_val hn hM.isWellFormed hnz U c).trans
      (hlevel c.val hc c.property)
  have hw0 : M0.IsWellFormed :=
    ⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩
  have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw0
    (zero_mark_admissible hI hπ hCN) hπ
  have hnzP : ∀ y ∈ P.N,IsNonzeroAlongAt P.N P.ideal y :=
    isNonzeroAlongAt_geoTransform_without_admissibility M0 hN hI hπ hCN hnz
  have hOpen : Q0=MarkedIdeal.pullback (Subtype.val : V → Y) P :=
    geoTransform_pullback_val hI hπ hwP.isCoherent U V.isOpen
  have hControlled := actual_geoTransform_nonmonomial_eq_total hn R hR.isWellFormed
    hR.isNonzeroAlongAt hRC hr
  have hOrders : nmOrd Q zU=nmOrd Q0 zU := by
    apply nmOrd_congr
    intro q
    change zU ∈ cosupport n Q.N (nonmonomialPartAlong n Q.N Q.ideal Q.E) q ↔
      zU ∈ cosupport n Q0.N (nonmonomialPartAlong n Q0.N Q0.ideal Q0.E) q
    rw [hControlled]
    rfl
  have hOrder0 : nmOrd Q0 zU=nmOrd P z := by
    rw [hOpen]
    exact nmOrd_pullback_val hn hwP hnzP V zU
  obtain ⟨hEq,hS,_hSNz,_⟩ := nextRelativeStrict_actual_geometry hn hN hI hnz hpr hπ hCN
  have hStrict : ordinaryTraceOrder P.N (nextRelativeStrict N I C π) z=nmOrd P z :=
    ordinary_order_eq_nmOrd_of_residual hS hEq z
  have hOrd : nmOrd Q zU=ordinaryTraceOrder P.N (nextRelativeStrict N I C π) z :=
    hOrders.trans (hOrder0.trans hStrict.symm)
  have hzQ : zU ∈ Q.N := by
    change zU ∈ Q0.N
    rw [hOpen]
    exact hz
  have hzCU : r zU ∈ CU := hzC
  have hQ : IsInvDomain (n+1) Q := by
    exact InvDomainTowerAlong.isInvDomain_geoTransformAlong hR
      (.step .refl CU r hr) ⟨trivial,hRC⟩
  by_cases hzero : nmOrd Q zU=0
  · rw [←hOrd,hzero]
    exact Nat.zero_le m
  · have hpos : Q.d ≤ nmOrd Q zU := by
      change 1 ≤ nmOrd Q zU
      omega
    have hzcos := mem_cosupp_of_mark_le_nmOrd hQ hzQ hpos
    rw [←hOrd]
    exact nmOrd_geoTransform_le_of_level hn hR hRC hr hRlevel hzcos hzCU

/-- Local equimultiplicity along the actual CURRENT centre produces the
pointwise source-order bound for the independently saturated next ideal.
There is no global source-order bound, transformed comparison or future
history assumption. -/
theorem nextRelativeStrict_order_le_of_locally_constant_on_centre (hn : 0 < n)
    {N C : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (hloc : ∀ x ∈ C,∀ᶠ x' in 𝓝 x,x' ∈ C →
      ordinaryTraceOrder N I x'=ordinaryTraceOrder N I x)
    {z : Y} (hz : z ∈ (nextTotalMarked N I C π).N) :
    ordinaryTraceOrder (nextTotalMarked N I C π).N (nextRelativeStrict N I C π) z ≤
      ordinaryTraceOrder N I (π z) := by
  by_cases hzC : π z ∈ C
  · by_cases hzero : ordinaryTraceOrder N I (π z)=0
    · have hunit := one_mem_of_order_zero hN hI hnz (hCN hzC) hzero
      rw [strict_order_zero_of_one_mem hn hN hI hnz hpr hπ hCN hz hunit,hzero]
    · have hm : 0 < ordinaryTraceOrder N I (π z) := Nat.pos_of_ne_zero hzero
      obtain ⟨A,hA,hAo,hxA⟩ := mem_nhds_iff.mp (hloc (π z) hzC)
      exact strict_order_le_of_positive_open_level hn hN hI hnz hpr hπ hCN hz hzC
        ⟨A,hAo⟩ hxA hm (fun x hx hxA => hA hxA hx)
  · exact (nextRelativeStrict_order_eq_off_centre hn hN hI hnz hpr hπ hCN hz hzC).le

end

end Hironaka.HironakaG4EquimultipleRelativeOrder
