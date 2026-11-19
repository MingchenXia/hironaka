import Hironaka.Resolution.HironakaG8ResidualTraceReduction
import Hironaka.Resolution.HironakaG11ResidualCoefficientNonzero
import Hironaka.Resolution.HironakaG8ExceptionalDivisibility

/-! # Actual nonzero coefficients from the successor residual trace -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ResidualActualNonzero
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen GermIdealOrder DivisorExponentAlong
  HironakaG8LocalHistory HironakaG11InvBMLower HironakaG11InvBMMask HironakaG11InvBMLowerTailSucc
  HironakaG8ClassStepCut HironakaG8ClassStepExp HironakaG8SpecialLoci HironakaG8ExceptionalDivisibility
  HironakaG11ResidualCoefficientNonzero StepOneValue StepOneLowerDomain ResolutionInvariantSpec HomogenizedIdealAlong
  MarkedIdealOperationsAlong.MarkedIdeal
open HironakaG11InvBMClass (SameCarrierDim)

/-- Below-mark failure transfers to the other locally equivalent domain
record; this is the contrapositive of the high-mark exponent comparison. -/
theorem other_not_divisible_mark
    {n : ℕ} {X : CMfd.{0} n} (hn : 0 < n) {P Q : MarkedIdeal n X} {k k' : ℕ}
    (hP : IsInvDomain k P) (hQ : IsInvDomain k' Q) (h : LocWPEquiv P Q)
    (hdim : SameCarrierDim P Q) (hd : Q.d = P.d)
    {H : Set X} (hH : H ∈ P.E) {y : X} (hy : y ∈ P.cosupp) (hyH : y ∈ H)
    (hbelow : ¬ IsDivNearAlong n P.N P.ideal H P.d y) :
    ¬ IsDivNearAlong n Q.N Q.ideal H Q.d y := by
  intro hdivQ
  have hyQ : y ∈ Q.cosupp := h.cosupp_eq_base ▸ hy
  have hHQ : H ∈ Q.E := h.E_eq.symm ▸ hH
  have hdim' := SameCarrierDim.symm_of_cosupp_eq h.cosupp_eq_base hdim
  have hexp := divExpAlong_eq_of_isDivNearAlong_mark hn h.symm hQ hP hdim' hd.symm hHQ hyQ hyH hdivQ
  obtain ⟨j, hj⟩ := hQ.isWellFormed.isClosedSubmanifold_N.2 y (Q.cosupp_subset_N hyQ)
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hj
  have hholQ := hol_of_isCoherent hQ.isWellFormed.isCoherent
  have hle := (isDivNearAlong_iff_le_divExpAlong hr hyH (hQ.isNonzeroAlongAt _ (Q.cosupp_subset_N hyQ)) hholQ).mp hdivQ
  rw [hexp, hd] at hle
  exact hbelow ((isDivNearAlong_divExpAlong (hol_of_isCoherent hP.isWellFormed.isCoherent) y).mono hle)

/-- On the actual common successor mask, below-mark failure for the first
lower ideal also holds for the second. -/
theorem actual_other_not_divisible_mark
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (hreg : stepRegime A (s+1) T a)
    (O : Opens Y) (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)))
    (hyO : y ∈ O) {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hy : y ∈ (lowerIdealBM A (s+1) T a).cosupp) (hyH : y ∈ H)
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y) :
    ¬ IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (lowerIdealBM B (s+1) T a).ideal H (lowerIdealBM B (s+1) T a).d y := by
  let P := MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)
  let Q := MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)
  let p : O := ⟨y,hyO⟩
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have hCA := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T hT a (s+1)
  have hCB := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T hTJB a (s+1)
  have hloc : LocWPEquiv (X := CMfd.of (n := n) O) P Q :=
    locWPEquiv_lowerIdealBM_succ hn hA hB hmA hmB h hE T hT ha s O hOA hOB
  have hPQdim : SameCarrierDim (X := CMfd.of (n := n) O) P Q :=
    HironakaG8ClassStepDim.lowerPairs_sameCarrierDim hn hA hB hmA hmB h hE hdim T hT (s+1) a ha hreg O hOA hOB r r' hdA hdB
  have hmap : Filter.map (Subtype.val : O → Y) (𝓝 p) = 𝓝 (p : Y) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (O : Set Y)) p.2 (O.isOpen.mem_nhds p.2)
  have hcosA : ∀ e, cosupport n ((Subtype.val : O → Y) ⁻¹' (lowerIdealBM A (s+1) T a).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a).ideal) e =
      (Subtype.val : O → Y) ⁻¹' cosupport n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal e :=
    fun e => cosupp_pullback_val (⟨(lowerIdealBM A (s+1) T a).N, [], (lowerIdealBM A (s+1) T a).ideal, e⟩ : MarkedIdeal n Y) (hol_of_isCoherent hCA) O
  have hcosB : ∀ e, cosupport n ((Subtype.val : O → Y) ⁻¹' (lowerIdealBM B (s+1) T a).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a).ideal) e =
      (Subtype.val : O → Y) ⁻¹' cosupport n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal e :=
    fun e => cosupp_pullback_val (⟨(lowerIdealBM B (s+1) T a).N, [], (lowerIdealBM B (s+1) T a).ideal, e⟩ : MarkedIdeal n Y) (hol_of_isCoherent hCB) O
  have hyp : p ∈ P.cosupp := by
    rw [cosupp_pullback_val _ (hol_of_isCoherent hCA) O]
    exact hy
  have hpH : (Subtype.val : O → Y) ⁻¹' H ∈ P.E := List.mem_map.mpr ⟨H,hH,rfl⟩
  have hdd : Q.d = P.d := by
    change (lowerIdealBM B (s+1) T a).d = (lowerIdealBM A (s+1) T a).d
    rw [lowerIdealBM_d, lowerIdealBM_d, coeffEmptyBM_d, coeffEmptyBM_d, hd]
  have hbelowP : ¬ IsDivNearAlong n P.N P.ideal ((Subtype.val : O → Y) ⁻¹' H) P.d p := by
    intro h'
    exact hbelow ((MonomialInvariantFunctorialAlong.isDivNearAlong_pullback_iff hcosA hmap H _).mp h')
  have hbelowQ := other_not_divisible_mark hn hdA hdB hloc hPQdim hdd hpH hyp hyH hbelowP
  intro hdivB
  apply hbelowQ
  exact (MonomialInvariantFunctorialAlong.isDivNearAlong_pullback_iff hcosB hmap H _).mpr hdivB

/-- The full successor residual follows from the original hypotheses and
one equivalence of actual contact trace conditions. -/
theorem actual_successor_exp_eq_of_trace_only
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked A) T) {a y : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ) (hreg : stepRegime A (s+1) T a)
    (O : Opens Y) (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM A (s+1) T a)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y) (lowerIdealBM B (s+1) T a)))
    (hyO : y ∈ O) {H : Set Y} (hH : H ∈ (lowerIdealBM A (s+1) T a).E)
    (hy : y ∈ (lowerIdealBM A (s+1) T a).cosupp) (hyH : y ∈ H)
    (hbelow : ¬ IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (lowerIdealBM A (s+1) T a).ideal H (lowerIdealBM A (s+1) T a).d y)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y)
    (htrace : (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM A (tangentChoice A (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ (contactCoeffBM B (tangentChoice B (T.proj a)).2 T).N → z ∈ H →
      ∀ D ∈ throughMembers A T a, z ∈ D)) :
    divExpAlong n (lowerIdealBM A (s+1) T a).N (lowerIdealBM A (s+1) T a).ideal H y =
      divExpAlong n (lowerIdealBM B (s+1) T a).N (lowerIdealBM B (s+1) T a).ideal H y := by
  have hS : ∀ D ∈ throughMembers A T a, IsClosed D := fun D hD =>
    (isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a D hD).1
  have hpos : 1 ≤ (coeffEmptyBM A).d := HironakaG8ClassStepCut.one_le_coeffEmptyBM_d A
  have hdiviff : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y ↔
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers A T a) (coeffEmptyBM A).d) H 1 y := by
    have htrace' : (∀ᶠ z in 𝓝 y, z ∈ (lowerIdealBM A (s+1) T a).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D) ↔
        (∀ᶠ z in 𝓝 y, z ∈ (lowerIdealBM B (s+1) T a).N → z ∈ H →
        ∀ D ∈ throughMembers A T a, z ∈ D) := by
      simpa only [lowerIdealBM_N, contactCoeffBM_N] using htrace
    exact (exceptionalTerm_divisible_below_iff_trace hS (le_refl 1) hpos y).trans
      (htrace'.trans (exceptionalTerm_divisible_below_iff_trace hS (le_refl 1) hpos y).symm)
  have hdivA := hdiv.elim id hdiviff.mpr
  have hdivB := hdiviff.mp hdivA
  have hnzA := actual_residual_coefficient_nonzero hn A hA.isWellFormed hA.one_le_d T hT a y s H hdivA hbelow
  have hbelowB := actual_other_not_divisible_mark hn hA hB hmA hmB h hd hE hdim T hT ha s hreg O hOA hOB hdA hdB hyO hH hy hyH hbelow
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have hEq : exceptionalTermBM (throughMembers B T a) (coeffEmptyBM B).d =
      exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d := by
    rw [HironakaG8ClassStepResidual.throughMembers_eq_of_E_eq hE T a, coeffEmptyBM_d B, coeffEmptyBM_d A, hd]
  have hdivB' : IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (throughMembers B T a) (coeffEmptyBM B).d) H 1 y := by rwa [hEq]
  have hnzB := actual_residual_coefficient_nonzero hn B hB.isWellFormed hB.one_le_d T hTJB a y s H hdivB' hbelowB
  exact HironakaG8ResidualTraceReduction.actual_successor_exp_eq_of_trace hn hA hB hmA hmB h hd hE hdim
    T hT ha s O hOA hOB hyO hH hy hyH hnzA hnzB htrace hbelow

end
end Hironaka.HironakaG8ResidualActualNonzero
