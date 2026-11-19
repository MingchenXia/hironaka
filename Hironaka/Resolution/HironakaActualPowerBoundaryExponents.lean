import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder

/-! Whole ideal powers on the actual proper carrier: sharp thresholds and
every literal ordered-boundary exponent. Raw nmOrd/CAN compatibility is not
inferred from ordinary order. Blueprint: hironaka-actual-power-boundary-exponents.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPowerBoundaryExponents
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers GermIdealOrder
  DivisorExponentAlong MarkedIdealOperationsAlong OrderTaylor
  OrderMultiplicativity CompanionReduction GermIdealPullbackCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec BlowupTowers
  HironakaSharpOriginalProductTraceOrder BlowupTowerTransforms

variable {n : ℕ} {X : CMfd.{u} n}

/-- A source-constructed whole ideal power, retaining every actual boundary position. -/
def powerMarked (M : MarkedIdeal n X) (e : ℕ) : MarkedIdeal n X :=
  ⟨M.N,M.E,idealPow M.ideal e,M.d*e⟩

/-- The genuine sharp threshold, on the actual proper carrier. -/
theorem cosupport_idealPow_mul_succ_eq_along {N : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    {e : ℕ} (he : 1≤e) (q : ℕ) :
    cosupport n N (idealPow I e) (e*q+1)=cosupport n N I (q+1) := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1,fun g hg=>?_⟩
    obtain ⟨k,hReg⟩:=hN.2 x hx.1
    obtain ⟨r,hr⟩:=exists_isLocalRetraction hReg
    have hghol:=GermIdeal.IsCoherent.holomorphicAt_mem hI hg
    by_contra hNot
    have hNotR : ¬(idealPow (pointIdeal n x) (q+1)).mem x (g∘r) :=
      fun h=>hNot (hr.vanishesToOrderOn_iff.mpr h)
    have hPow:=hx.2 _ (OrderMultiplicativity.pow_mem_idealPow hg hghol e)
    exact CompanionReduction.pow_notMem_idealPow (hr.holomorphicAt_comp hghol) hNotR e
      (hr.vanishesToOrderOn_iff.mp hPow)
  · intro hx
    have hPow : x∈cosupport n N (idealPow I e) ((q+1)*e) := by
      rw [cosupport_idealPow_mul_eq_along hN.2
        (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg) he]
      exact hx
    have hLe : e*q+1≤(q+1)*e := by
      calc
        e*q+1≤e*q+e:=Nat.add_le_add_left he _
        _=(q+1)*e:=by ring
    exact cosupport_anti hLe hPow

private theorem isDivNearAlong_power_mul_iff {N H : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    {e : ℕ} (he : 1≤e) (q : ℕ) (x : X) :
    IsDivNearAlong n N (idealPow I e) H (q*e) x ↔ IsDivNearAlong n N I H q x := by
  unfold IsDivNearAlong
  rw [cosupport_idealPow_mul_eq_along hN.2
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg) he]

private theorem isDivNearAlong_power_succ_iff {N H : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    {e : ℕ} (he : 1≤e) (q : ℕ) (x : X) :
    IsDivNearAlong n N (idealPow I e) H (e*q+1) x ↔ IsDivNearAlong n N I H (q+1) x := by
  unfold IsDivNearAlong
  rw [cosupport_idealPow_mul_succ_eq_along hN hI he]

/-- Powers retain nonzero source germs on the actual carrier. -/
theorem isNonzeroAlongAt_idealPow {N : Set X} {I : GermIdeal n X} (hI : I.IsCoherent)
    {x : X} (hx : IsNonzeroAlongAt N I x) (e : ℕ) :
    IsNonzeroAlongAt N (idealPow I e) x := by
  obtain ⟨g,hg,hFreq⟩:=hx
  refine ⟨fun y=>g y^e,OrderMultiplicativity.pow_mem_idealPow hg
    (GermIdeal.IsCoherent.holomorphicAt_mem hI hg) e,?_⟩
  exact hFreq.mono fun y ⟨hy,hne⟩=>⟨hy,pow_ne_zero _ hne⟩

/-- The original whole positive power is again a native invariant-domain record. -/
theorem powerMarked_isInvDomain {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) : IsInvDomain k (powerMarked M e) := by
  refine ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,
    isCoherent_idealPow hM.isWellFormed.isCoherent e,
    hM.isWellFormed.isSNCDivisor,hM.isWellFormed.isTransverse⟩,hM.dimLE,?_,?_⟩
  · exact Nat.mul_pos hM.one_le_d he
  · intro x hx
    exact isNonzeroAlongAt_idealPow hM.isWellFormed.isCoherent (hM.isNonzeroAlongAt x hx) e

theorem powerMarked_cosupp {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) : (powerMarked M e).cosupp=M.cosupp := by
  exact cosupport_idealPow_mul_eq_along hM.isWellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) he M.d

/-- Every actual trace exponent of a WHOLE ideal power, including the native
zero default, is derived from the original divisibility tests. -/
theorem divExpAlong_idealPow {N H : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) {e : ℕ} (he : 1≤e) (x : X) :
    divExpAlong n N (idealPow I e) H x=e*divExpAlong n N I H x := by
  classical
  let a:=divExpAlong n N I H x
  have hHol : ∀y g,I.mem y g→HolomorphicAt n g y :=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  by_cases hFin : ∃q,¬IsDivNearAlong n N I H (q+1) x
  · have hNot : ¬IsDivNearAlong n N I H (a+1) x := by
      dsimp only [a,divExpAlong]
      rw [dif_pos hFin]
      exact Nat.find_spec hFin
    have hLower : IsDivNearAlong n N (idealPow I e) H (e*a) x := by
      rw [Nat.mul_comm e a]
      exact (isDivNearAlong_power_mul_iff hN hI he a x).mpr (isDivNearAlong_divExpAlong hHol x)
    have hNotPower : ¬IsDivNearAlong n N (idealPow I e) H (e*a+1) x :=
      fun h=>hNot ((isDivNearAlong_power_succ_iff hN hI he a x).mp h)
    have hFinPower : ∃q,¬IsDivNearAlong n N (idealPow I e) H (q+1) x:=⟨e*a,hNotPower⟩
    have hDef : divExpAlong n N (idealPow I e) H x=Nat.find hFinPower := by
      simp only [divExpAlong,dif_pos hFinPower]
    rw [hDef]
    change Nat.find hFinPower=e*a
    apply le_antisymm (Nat.find_min' hFinPower hNotPower)
    by_contra hlt
    have hle : Nat.find hFinPower+1≤e*a := by omega
    exact Nat.find_spec hFinPower (hLower.mono hle)
  · have hFinPower : ¬∃q,¬IsDivNearAlong n N (idealPow I e) H (q+1) x := by
      rintro ⟨q,hNot⟩
      apply hNot
      have hA : IsDivNearAlong n N I H (q+1) x := by
        by_contra h
        exact hFin ⟨q,h⟩
      have hB:=(isDivNearAlong_power_mul_iff hN hI he (q+1) x).mpr hA
      exact hB.mono (by simpa using Nat.mul_le_mul_left (q+1) he)
    simp only [divExpAlong,dif_neg hFinPower,dif_neg hFin,Nat.mul_zero]

/-- Ordinary carrier order scales under a WHOLE ideal power. This is not
an ordinary-to-raw nonmonomial-order inference. -/
theorem ordinaryTraceOrder_idealPow {N : Set X} (hN : IsClosedSubmanifold n N)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hNZ : ∀x∈N,IsNonzeroAlongAt N I x)
    {e : ℕ} (he : 1≤e) {x : X} (hx : x∈N) :
    ordinaryTraceOrder N (idealPow I e) x=e*ordinaryTraceOrder N I x := by
  let a:=ordinaryTraceOrder N I x
  have hIP:=isCoherent_idealPow hI e
  have hNP : ∀y∈N,IsNonzeroAlongAt N (idealPow I e) y :=
    fun y hy=>isNonzeroAlongAt_idealPow hI (hNZ y hy) e
  have hLower : x∈cosupport n N (idealPow I e) (a*e) := by
    rw [cosupport_idealPow_mul_eq_along hN.2
      (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg) he]
    exact (ordinaryTraceOrder_cosupport_iff hN hI hNZ hx a).mpr le_rfl
  have hUpper : x∉cosupport n N (idealPow I e) (e*a+1) := by
    rw [cosupport_idealPow_mul_succ_eq_along hN hI he]
    exact fun h=>Nat.not_succ_le_self a ((ordinaryTraceOrder_cosupport_iff hN hI hNZ hx (a+1)).mp h)
  apply le_antisymm
  · by_contra h
    have hle : e*a+1≤ordinaryTraceOrder N (idealPow I e) x :=
      Nat.succ_le_of_lt (lt_of_not_ge h)
    exact hUpper ((ordinaryTraceOrder_cosupport_iff hN hIP hNP hx (e*a+1)).mpr hle)
  · rw [Nat.mul_comm e a]
    exact (ordinaryTraceOrder_cosupport_iff hN hIP hNP hx (a*e)).mp hLower

/-- Actual native whole-power data for EVERY retained ordered E position;
all field/domain/cosupport/exponent conclusions are produced internally. -/
theorem powerMarked_native_boundary_data {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {e : ℕ} (he : 1≤e) :
    IsInvDomain k (powerMarked M e) ∧
      (powerMarked M e).N=M.N ∧ (powerMarked M e).E=M.E ∧
      (powerMarked M e).d=M.d*e ∧ (powerMarked M e).cosupp=M.cosupp ∧
      ∀i : Fin M.E.length,∀x,
        divExpAlong n (powerMarked M e).N (powerMarked M e).ideal ((powerMarked M e).E.get i) x=
          e*divExpAlong n M.N M.ideal (M.E.get i) x := by
  refine ⟨powerMarked_isInvDomain M hM he,rfl,rfl,rfl,powerMarked_cosupp M hM he,?_⟩
  intro i x
  exact divExpAlong_idealPow hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent he x

/-- EVERY given actual native prefix supplies its current whole-power
domain, cosupport, ordinary order and ALL old/born/empty E-position data.
This does not identify an original powered transform with the current power. -/
theorem actual_test_prefix_power_boundary_data {k : ℕ} {Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) {e : ℕ} (he : 1≤e) :
    let C:=geoTransformAlong M T
    IsInvDomain k (powerMarked C e) ∧
      (powerMarked C e).N=C.N ∧ (powerMarked C e).E=C.E ∧
      (powerMarked C e).d=M.d*e ∧ (powerMarked C e).cosupp=C.cosupp ∧
      (∀x∈C.N,ordinaryTraceOrder C.N (powerMarked C e).ideal x=
        e*ordinaryTraceOrder C.N C.ideal x) ∧
      ∀i : Fin C.E.length,∀x,
        divExpAlong n (powerMarked C e).N (powerMarked C e).ideal ((powerMarked C e).E.get i) x=
          e*divExpAlong n C.N C.ideal (C.E.get i) x := by
  let C:=geoTransformAlong M T
  have hC:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  refine ⟨powerMarked_isInvDomain C hC he,rfl,rfl,?_,powerMarked_cosupp C hC he,?_,?_⟩
  · change (geoTransformAlong M T).d*e=M.d*e
    rw [d_geoTransformAlong]
  · intro x hx
    exact ordinaryTraceOrder_idealPow hC.isWellFormed.isClosedSubmanifold_N
      hC.isWellFormed.isCoherent hC.isNonzeroAlongAt he hx
  · intro i x
    exact divExpAlong_idealPow hC.isWellFormed.isClosedSubmanifold_N hC.isWellFormed.isCoherent he x

end
end Hironaka.HironakaActualPowerBoundaryExponents
