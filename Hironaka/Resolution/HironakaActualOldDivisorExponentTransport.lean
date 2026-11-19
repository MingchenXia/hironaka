import Hironaka.Resolution.HironakaActualLocalBornExponent
import Hironaka.Invariant.MonomialPartEtale

/-! Actual old strict-divisor exponents on the SAME proper carrier.
Blueprint FIRST. Chronological empty members and every actual step retained;
raw nonmonomial order and full true-mark suffixes remain separate. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOldDivisorExponentTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder IdealWeightPowers
  DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealOpenBiholomorphism
  BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupSNCTransform NormalCrossings
  ExceptionalPushforwardAlong ResolutionInvariantSpec InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal DerivativeIdealAlong
  MonomialPartEtale DerivativeIdealAlongEtale MarkedIdealOpenBiholomorphism
  IdealOrderArithmetic
  HironakaActualLocalBornExponent

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem local_inverse_off {C : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : π z∉C) : ∃ψ : X→Y,IsLocalInverseAt n π ψ z := by
  obtain ⟨s,hs,hsπ,hsec⟩:=BlowupIsomorphismOff.exists_section_compl hπ
  let U : Opens X:=⟨Cᶜ,hπ.1.1.isOpen_compl⟩
  let x₀ : U:=⟨π z,hz⟩
  have hVal:=isLocalInverseAt_val (n:=n) U x₀
  refine ⟨s∘openInv U x₀,⟨Eventually.of_forall fun p=>(hπ.contMDiff p).mdifferentiableAt (by simp),?_,?_,?_⟩⟩
  · filter_upwards [hVal.mdiff_inv] with q hq
    exact ((hs _).mdifferentiableAt (by simp)).comp q hq
  · filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually
      (hπ.1.1.isOpen_compl.mem_nhds hz)] with p hp
    have hOpen : openInv U x₀ (π p)=⟨π p,hp⟩:=by simp [openInv,U,hp]
    simp only [Function.comp_apply,hOpen]
    exact hsec p hp
  · filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hz] with q hq
    have hOpen : openInv U x₀ q=⟨q,hq⟩:=by simp [openInv,U,hq]
    simp only [Function.comp_apply,hOpen]
    exact congrFun hsπ ⟨q,hq⟩

private theorem pullback_cosupport_point {I : GermIdeal n X}
    (hI : ∀x f,I.mem x f→HolomorphicAt n f x) {φ : Y→X} {ψ : X→Y} {z : Y}
    (hψ : IsLocalInverseAt n φ ψ z) (N : Set X) (r : ℕ) :
    z∈cosupport n (φ ⁻¹' N) (GermIdeal.pullback (m:=n) φ I) r ↔φ z∈cosupport n N I r := by
  have hzψ : ψ (φ z)=z:=hψ.left_inv.self_of_nhds
  constructor
  · rintro ⟨hzN,hOrder⟩
    refine ⟨hzN,fun f hf=>?_⟩
    have hfφ:=DerivativeIdealAlongEtale.comp_mem_pullback hψ.mdiff hf (hI _ _ hf)
    obtain ⟨g,hg,hEq⟩:=hOrder _ hfφ
    have hg' : (idealPow (pointIdeal n (ψ (φ z))) r).mem (ψ (φ z)) g:=by rw [hzψ];exact hg
    refine ⟨g∘ψ,HadamardBridge.comp_mem_idealPow_pointIdeal hψ.mdiff_inv r hg',?_⟩
    filter_upwards [hψ.tendsto.eventually hEq,hψ.right_inv] with q hq hqr hqN
    have h:=hq (show φ (ψ q)∈N by rw [hqr];exact hqN)
    simpa [Function.comp_apply,hqr] using h
  · rintro ⟨hzN,hOrder⟩
    refine ⟨hzN,fun f hf=>?_⟩
    refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hf) ?_
    rintro _ ⟨g,hg,rfl⟩
    exact MonomialPartEtale.vanishesToOrderOn_comp hψ.mdiff (hOrder g hg)

private theorem carrier_vanishing {W P : Set Y} {z : Y} {f : Y→ℂ} {r : ℕ}
    (hWP : ∀ᶠy in 𝓝 z,y∈W↔y∈P) :
    VanishesToOrderOn n W z r f↔VanishesToOrderOn n P z r f := by
  constructor
  · rintro ⟨g,hg,hEq⟩
    refine ⟨g,hg,?_⟩
    filter_upwards [hEq,hWP] with y hy hyWP hyP
    exact hy (hyWP.mpr hyP)
  · rintro ⟨g,hg,hEq⟩
    refine ⟨g,hg,?_⟩
    filter_upwards [hEq,hWP] with y hy hyWP hyW
    exact hy (hyWP.mp hyW)

private theorem span_vanishing {W : Set Y} {I : GermIdeal n Y} {z : Y} {f : Y→ℂ} {r : ℕ}
    (h : IsInSpanOnAt (n:=n) W (I.mem z) z f) (hOrder : OrderGE n W I z r) :
    VanishesToOrderOn n W z r f := by
  obtain ⟨K,s,a,hs,ha,hEq⟩:=h
  obtain ⟨g,hg,hEqg⟩:=vanishesToOrderOn_sum_mul ha fun i=>hOrder _ (hs i)
  refine ⟨g,hg,?_⟩
  filter_upwards [hEq,hEqg] with y hy hyg hyW
  rw [hy hyW,hyg hyW]

private theorem off_cosupport (S : MarkedIdeal n X) (hN : IsClosed S.N)
    (hI : S.ideal.IsCoherent) {C : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : π z∉C) (r : ℕ) :
    z∈cosupport n (S.geoTransform C π).N (S.geoTransform C π).ideal r ↔
      π z∈cosupport n S.N S.ideal r := by
  obtain ⟨ψ,hψ⟩:=local_inverse_off hπ hz
  have hCarrier : ∀ᶠy in 𝓝 z,y∈(S.geoTransform C π).N↔y∈π ⁻¹' S.N := by
    filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually
      (hπ.1.1.isOpen_compl.mem_nhds hz)] with y hy
    exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hy
  have hPoint := mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hz
  have hControlled :
      z∈cosupport n (S.geoTransform C π).N (S.geoTransform C π).ideal r ↔
      z∈cosupport n (S.geoTransform C π).N (GermIdeal.pullback (m:=n) π S.ideal) r := by
    constructor
    · rintro ⟨hzN,hOrder⟩
      refine ⟨hzN,fun f hf=>span_vanishing ?_ hOrder⟩
      apply (MonomialBlowupAlongChart.isInSpanOnAt_geoTransform_iff_pullback_of_notMem hπ S hz f).mpr
      exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hf (GermIdeal.mem_pullback_iff.mp hf).1)
    · rintro ⟨hzN,hOrder⟩
      refine ⟨hzN,fun f hf=>span_vanishing ?_ hOrder⟩
      apply (MonomialBlowupAlongChart.isInSpanOnAt_geoTransform_iff_pullback_of_notMem hπ S hz f).mp
      exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hf hf.1)
  have hCarCos :
      z∈cosupport n (S.geoTransform C π).N (GermIdeal.pullback (m:=n) π S.ideal) r ↔
      z∈cosupport n (π ⁻¹' S.N) (GermIdeal.pullback (m:=n) π S.ideal) r := by
    constructor
    · rintro ⟨hzN,hOrder⟩
      exact ⟨hPoint.mp hzN,fun f hf=>(carrier_vanishing hCarrier).mp (hOrder f hf)⟩
    · rintro ⟨hzN,hOrder⟩
      exact ⟨hPoint.mpr hzN,fun f hf=>(carrier_vanishing hCarrier).mpr (hOrder f hf)⟩
  exact hControlled.trans (hCarCos.trans (pullback_cosupport_point (hol hI) hψ S.N r))

/-- Every local divisibility threshold at this ACTUAL off-centre point,
retaining the proper carrier and the original controlled transform. -/
theorem off_centre_divisibility (S : MarkedIdeal n X) (hN : IsClosed S.N)
    (hI : S.ideal.IsCoherent) {C : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : π z∉C) (H : Set X) (hH : IsClosed H) (r : ℕ) :
    IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (geoStrictTransform π C H) r z ↔IsDivNearAlong n S.N S.ideal H r (π z) := by
  obtain ⟨ψ,hψ⟩:=local_inverse_off hπ hz
  unfold IsDivNearAlong
  rw [←map_nhds_eq_of_local hψ,Filter.eventually_map]
  apply eventually_congr
  filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually
    (hπ.1.1.isOpen_compl.mem_nhds hz)] with y hy
  change (y∈geoStrictTransform π C S.N→y∈geoStrictTransform π C H→
    y∈cosupport n (S.geoTransform C π).N (S.geoTransform C π).ideal r)↔_
  rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hN hy,
    mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH hy,off_cosupport S hN hI hπ hy r]

private theorem off_exponent (S : MarkedIdeal n X) (hN : IsClosed S.N)
    (hI : S.ideal.IsCoherent) {C : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : π z∉C) (H : Set X) (hH : IsClosed H) :
    divExpAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal (geoStrictTransform π C H) z=
      divExpAlong n S.N S.ideal H (π z) := by
  have hP : (fun r=>IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (geoStrictTransform π C H) r z)=(fun r=>IsDivNearAlong n S.N S.ideal H r (π z)):=
    funext fun r=>propext (off_centre_divisibility S hN hI hπ hz H hH r)
  unfold divExpAlong
  show (if h : ∃a,¬(fun r=>IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (geoStrictTransform π C H) r z) (a+1) then Nat.find h else 0)=
    (if h : ∃a,¬(fun r=>IsDivNearAlong n S.N S.ideal H r (π z)) (a+1) then Nat.find h else 0)
  rw [hP]

private theorem old_exponent (S : MarkedIdeal n X) (hS : S.IsWellFormed)
    (hne : ∀x∈S.N,IsNonzeroAlongAt S.N S.ideal x)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    (i : Fin S.E.length) {z : Y} (hzN : z∈(S.geoTransform C π).N)
    (hzH : z∈geoStrictTransform π C (S.E.get i)) :
    divExpAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (geoStrictTransform π C (S.E.get i)) z=
      divExpAlong n S.N S.ideal (S.E.get i) (π z) := by
  have hN:=hS.isClosedSubmanifold_N
  have hH : IsClosed (S.E.get i):=hS.isSNCDivisor.1 _ (List.get_mem _ _)
  have hxN : π z∈S.N:=geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hzN
  have hxH : π z∈S.E.get i:=geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH hzH
  obtain ⟨F,_hCoord,hCard,_hInjective⟩:=hS.isSNCDivisor.2 (π z)
  have hCardPos : 0<(F i).card:=by rw [hCard i hxH];decide
  obtain ⟨a,_ha⟩:=Finset.card_pos.mp hCardPos
  have hn : 0<n:=lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
  have hS':=GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hS hC hπ
  have hne':=isNonzeroAlongAt_geoTransform_of_isAdmissibleCentre hπ S hN hS.isCoherent hC hne
  let j : Fin (S.E.map (geoStrictTransform π C)++[π ⁻¹' C]).length:=⟨i.val,by
    simpa only [List.length_append,List.length_map,List.length_singleton] using Nat.lt_succ_of_lt i.isLt⟩
  have hGet : (S.geoTransform C π).E.get j=geoStrictTransform π C (S.E.get i) := by
    change (S.E.map (geoStrictTransform π C)++[π ⁻¹' C]).get j=_
    simpa only [j,dif_pos i.isLt] using
      get_map_append_singleton S.E (geoStrictTransform π C) (π ⁻¹' C) j
  have hSource:=eventually_divExpAlong_get_eq hn hN hS.isSNCDivisor hS.isTransverse
    hS.isCoherent hne i hxN hxH
  have hTarget:=eventually_divExpAlong_get_eq hn hS'.isClosedSubmanifold_N hS'.isSNCDivisor
    hS'.isTransverse hS'.isCoherent hne' j hzN (hGet.symm ▸ hzH)
  rw [hGet] at hTarget
  have hTrace : z∈geoStrictTransform π C (S.E.get i∩S.N) := by
    rw [ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hπ hN.1 hC.subset_N
      hS.isSNCDivisor hS.isTransverse hC.2.2 i]
    exact ⟨hzH,hzN⟩
  have hFreq : ∃ᶠw in 𝓝 z,π w∈(S.E.get i∩S.N)\C:=mem_closure_iff_frequently.mp hTrace
  have hSourcePull:=hπ.contMDiff.continuous.continuousAt.eventually hSource
  obtain ⟨w,hw,hwSource,hwTarget⟩:=(hFreq.and_eventually (hSourcePull.and hTarget)).exists
  have hwN : w∈(S.geoTransform C π).N:=subset_closure ⟨hw.1.2,hw.2⟩
  have hwH : w∈geoStrictTransform π C (S.E.get i):=subset_closure ⟨hw.1.1,hw.2⟩
  calc
    _=divExpAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
        (geoStrictTransform π C (S.E.get i)) w:=(hwTarget hwN hwH).symm
    _=divExpAlong n S.N S.ideal (S.E.get i) (π w):=off_exponent S hN.1 hS.isCoherent hπ hw.2 _ hH
    _=divExpAlong n S.N S.ideal (S.E.get i) (π z):=hwSource hw.1.2 hw.1.1

/-- An actual OLD chronological member preserves its exponent on its SAME
proper strict trace. No equality is asserted off that old trace. -/
theorem original_history_old_exponent (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (T : BlowupTower X Y) (hT : IsGeoTestTower Q T)
    {C : Set Y} (hC : (geoTransformAlong Q T).IsAdmissibleCentre C)
    {Z : CMfd.{0} n} {π : Z→Y} (hπ : IsBlowupAlong n C π)
    (i : Fin (geoTransformAlong Q T).E.length) {z : Z}
    (hzN : z∈((geoTransformAlong Q T).geoTransform C π).N)
    (hzH : z∈geoStrictTransform π C ((geoTransformAlong Q T).E.get i)) :
    divExpAlong n ((geoTransformAlong Q T).geoTransform C π).N
      ((geoTransformAlong Q T).geoTransform C π).ideal
      (geoStrictTransform π C ((geoTransformAlong Q T).E.get i)) z=
    divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal
      ((geoTransformAlong Q T).E.get i) (π z) := by
  have hCurrent:=isInvDomain_geoTransformAlong hQ T hT
  exact old_exponent (geoTransformAlong Q T) hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
    hC hπ i hzN hzH

private theorem same_carrier {P Q : MarkedIdeal n X} (hN : P.N=Q.N) :
    {Y : CMfd.{0} n}→(T : BlowupTower X Y)→(geoTransformAlong P T).N=(geoTransformAlong Q T).N
  | _,.refl=>hN
  | _,.step T C π _hπ=>congrArg (geoStrictTransform π C) (same_carrier hN T)

private theorem coefficient_nonzero (Q : MarkedIdeal n X) (hI : Q.ideal.IsCoherent)
    (hd : 1≤Q.d) (hne : ∀x∈Q.N,IsNonzeroAlongAt Q.N Q.ideal x) :
    ∀x∈(coeffMarkedAlong Q).N,IsNonzeroAlongAt (coeffMarkedAlong Q).N (coeffMarkedAlong Q).ideal x := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  intro x hx
  obtain ⟨g,hg,hFreq⟩:=hne x hx
  have hPower:=MonomialPart.pow_mem_idealPow hg (hol hI _ _ hg) e
  have hZero : (idealPow (derivMarkedAlong Q 0).ideal
      (sumExp (fun j=>(derivMarkedAlong Q j).d) Q.d 0)).mem x (fun y=>g y^e) := by
    simpa only [derivMarkedAlong_zero,derivMarkedAlong_d,e] using hPower
  have hCoefficient : (coeffMarkedAlong Q).ideal.mem x (fun y=>g y^e) := by
    change IsInSpanAt (n:=n) (fun s=>∃i,i<Q.d ∧
      (idealPow (derivMarkedAlong Q i).ideal (sumExp (fun j=>(derivMarkedAlong Q j).d) Q.d i)).mem x s)
      x (fun y=>g y^e)
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨0,hd,hZero⟩ (holomorphicAt_of_mem_idealPow hPower)
  exact ⟨fun y=>g y^e,hCoefficient,hFreq.mono fun y hy=>⟨hy.1,pow_ne_zero e hy.2⟩⟩

private theorem coefficient_domain (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) : IsInvDomain k (coeffMarkedAlong Q) where
  isWellFormed := {
    isClosedSubmanifold_N:=hQ.isWellFormed.isClosedSubmanifold_N
    isCoherent:=isCoherent_coeffMarkedAlong hQ.isWellFormed.isCoherent hQ.isWellFormed.isClosedSubmanifold_N
    isSNCDivisor:=hQ.isWellFormed.isSNCDivisor
    isTransverse:=hQ.isWellFormed.isTransverse }
  dimLE:=hQ.dimLE
  one_le_d:=by
    change 1≤(Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d)
    have hd:=hQ.one_le_d
    have hPos : 0<(Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d) := by
      apply Finset.prod_pos
      intro j hj
      rw [derivMarkedAlong_d]
      have hlt:=Finset.mem_range.mp hj
      omega
    omega
  isNonzeroAlongAt:=coefficient_nonzero Q hQ.isWellFormed.isCoherent hQ.one_le_d hQ.isNonzeroAlongAt

private theorem off_member_zero {N H : Set X} {I : GermIdeal n X} {x : X}
    (hH : IsClosed H) (hx : x∉H) : divExpAlong n N I H x=0 := by
  have hAll (r : ℕ) : IsDivNearAlong n N I H r x := by
    filter_upwards [hH.isOpen_compl.mem_nhds hx] with y hy _hyN hyH
    exact False.elim (hy hyH)
  have hNone : ¬∃r,¬IsDivNearAlong n N I H (r+1) x:=fun ⟨r,hr⟩=>hr (hAll (r+1))
  simp only [divExpAlong,dif_neg hNone]

private theorem boundary_scale (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) :
    {Y : CMfd.{0} n}→(T : BlowupTower X Y)→IsGeoTestTower Q T→
      ∀(i : Fin (geoTransformAlong Q T).E.length)(z : Y),z∈(geoTransformAlong Q T).N→
      divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal
        ((geoTransformAlong Q T).E.get i) z=
      sumExp (fun j=>Q.d-j) Q.d 0*divExpAlong n (geoTransformAlong Q T).N
        (geoTransformAlong Q T).ideal ((geoTransformAlong Q T).E.get i) z
  | _,.refl,_hT,i,_z,_hzN=>by
    have hi:=i.isLt
    change i.val<Q.E.length at hi
    rw [hEmpty,List.length_nil] at hi
    omega
  | _,.step T C π hπ,hT,i,z,hzN=>by
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    let A:=geoTransformAlong Q T
    let B:=geoTransformAlong (coeffMarkedAlong Q) T
    have hA:=isInvDomain_geoTransformAlong hQ T hT.1
    have hCoeffQ:=coefficient_domain Q hQ
    have hFull : IsGeoTestTower (coeffMarkedAlong Q) (.step T C π hπ):=
      (coeffAlong_tower Q hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent
        hQ.one_le_d (.step T C π hπ)).1.mpr hT
    have hB:=isInvDomain_geoTransformAlong hCoeffQ T hFull.1
    have hNB : B.N=A.N:=same_carrier (P:=coeffMarkedAlong Q) (Q:=Q) rfl T
    have hBE : B.E=A.E:=E_geoTransformAlong_eq (𝔪:=coeffMarkedAlong Q) (𝔫:=Q) rfl T
    have hNextN : (B.geoTransform C π).N=(A.geoTransform C π).N:=
      congrArg (geoStrictTransform π C) hNB
    change divExpAlong n (A.geoTransform C π).N (B.geoTransform C π).ideal
        ((A.geoTransform C π).E.get i) z=
      e*divExpAlong n (A.geoTransform C π).N (A.geoTransform C π).ideal
        ((A.geoTransform C π).E.get i) z
    let iList : Fin (A.E.map (geoStrictTransform π C)++[π ⁻¹' C]).length:=⟨i.val,i.isLt⟩
    have hGet : (A.geoTransform C π).E.get i=
        if h : i.val<A.E.length then geoStrictTransform π C (A.E.get ⟨i.val,h⟩) else π ⁻¹' C := by
      change (A.E.map (geoStrictTransform π C)++[π ⁻¹' C]).get iList=
        if h : iList.val<A.E.length then geoStrictTransform π C (A.E.get ⟨iList.val,h⟩) else π ⁻¹' C
      exact get_map_append_singleton A.E (geoStrictTransform π C) (π ⁻¹' C) iList
    rw [hGet]
    by_cases hi : i.val<A.E.length
    · rw [dif_pos hi]
      let j : Fin A.E.length:=⟨i.val,hi⟩
      change divExpAlong n (A.geoTransform C π).N (B.geoTransform C π).ideal
          (geoStrictTransform π C (A.E.get j)) z=
        e*divExpAlong n (A.geoTransform C π).N (A.geoTransform C π).ideal
          (geoStrictTransform π C (A.E.get j)) z
      by_cases hzH : z∈geoStrictTransform π C (A.E.get j)
      · have hxN : π z∈A.N:=geoStrictTransform_subset_preimage hπ.contMDiff.continuous
          hA.isWellFormed.isClosedSubmanifold_N.1 hzN
        have hInd:=boundary_scale Q hQ hEmpty T hT.1 j (π z) hxN
        have hOldA:=old_exponent A hA.isWellFormed hA.isNonzeroAlongAt hT.2 hπ j hzN hzH
        let jB : Fin B.E.length:=⟨j.val,by rw [hBE];exact j.isLt⟩
        have hBGet : B.E.get jB=A.E.get j:=by simp [List.get_eq_getElem,jB,hBE]
        have hOldB :=old_exponent B hB.isWellFormed hB.isNonzeroAlongAt hFull.2 hπ jB
          (hNextN.symm ▸ hzN) (hBGet.symm ▸ hzH)
        rw [hNextN,hNB,hBGet] at hOldB
        calc
          _=divExpAlong n A.N B.ideal (A.E.get j) (π z):=hOldB
          _=e*divExpAlong n A.N A.ideal (A.E.get j) (π z):=hInd
          _=e*divExpAlong n (A.geoTransform C π).N (A.geoTransform C π).ideal
              (geoStrictTransform π C (A.E.get j)) z:=congrArg (fun v=>e*v) hOldA.symm
      · have hZeroB:=off_member_zero (N:=(A.geoTransform C π).N)
          (H:=geoStrictTransform π C (A.E.get j)) (I:=(B.geoTransform C π).ideal) isClosed_closure hzH
        have hZeroA:=off_member_zero (N:=(A.geoTransform C π).N)
          (H:=geoStrictTransform π C (A.E.get j)) (I:=(A.geoTransform C π).ideal) isClosed_closure hzH
        rw [hZeroB,hZeroA,Nat.mul_zero]
    · rw [dif_neg hi]
      by_cases hzC : π z∈C
      · exact original_coefficient_born_exponent Q hQ T hT.1 hT.2 hπ hzN hzC
      · have hzD : z∉π ⁻¹' C:=hzC
        have hDClosed : IsClosed (π ⁻¹' C):=hπ.1.1.preimage hπ.contMDiff.continuous
        have hZeroB:=off_member_zero (N:=(A.geoTransform C π).N)
          (I:=(B.geoTransform C π).ideal) hDClosed hzD
        have hZeroA:=off_member_zero (N:=(A.geoTransform C π).N)
          (I:=(A.geoTransform C π).ideal) hDClosed hzD
        rw [hZeroB,hZeroA,Nat.mul_zero]

/-- EVERY chronological boundary exponent of the ORIGINAL coefficient
history is e-scaled. Empty steps/members retain their literal positions. -/
theorem original_coefficient_all_boundary_exponents (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    let A:=geoTransformAlong Q T
    let B:=geoTransformAlong (coeffMarkedAlong Q) T
    IsInvDomain k B ∧ B.N=A.N ∧ B.E=A.E ∧ A.E.length=T.length ∧ B.E.length=T.length ∧
      ∀(i : Fin A.E.length)(z : Y),z∈A.N→
        divExpAlong n A.N B.ideal (A.E.get i) z=e*divExpAlong n A.N A.ideal (A.E.get i) z := by
  have hN:=(same_carrier (P:=coeffMarkedAlong Q) (Q:=Q) rfl T)
  have hE:=E_geoTransformAlong_eq (𝔪:=coeffMarkedAlong Q) (𝔫:=Q) rfl T
  have hCT:=(coeffAlong_tower Q hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent
    hQ.one_le_d T).1.mpr hT
  have hB:=isInvDomain_geoTransformAlong (coefficient_domain Q hQ) T hCT
  refine ⟨hB,hN,hE,?_,?_,boundary_scale Q hQ hEmpty T hT⟩
  · rw [length_E_geoTransformAlong,hEmpty,List.length_nil,Nat.zero_add]
  · rw [hE,length_E_geoTransformAlong,hEmpty,List.length_nil,Nat.zero_add]

end
end Hironaka.HironakaActualOldDivisorExponentTransport
