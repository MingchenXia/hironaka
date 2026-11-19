import Hironaka.Resolution.HironakaActualLocalBornExponent
import Hironaka.Invariant.MemberTraceIdealAlong

/-!
# Native local born divisibility in arbitrary manifold universes

The actual restricted whole-ideal birth proof uses polymorphic retraction,
exceptional pushforward and cancellation APIs. Its native local predicate and
finite born exponent are therefore proved for CMfd.{u}. The accepted
universe-zero mother and its separate coefficient-history tail are retained.
Blueprint FIRST: `hironaka-actual-polymorphic-born-exponent.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPolymorphicBornExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder IdealWeightPowers
  DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealRestrictOpen
  BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupSNCTransform MemberTraceIdealAlong
  ExceptionalPushforwardAlong RestrictedIdealExtension RestrictedIdealQuotient RestrictedIdealWeight
  HadamardBridgeAlong ResolutionInvariantSpec InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal
  DerivativeIdealAlong
  HironakaActualOriginalCoefficientCentreExponent

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem span_power_factor {W : Set X} {I : GermIdeal n X}
    {x : X} {τ f : X→ℂ} (hτ : ∀g,I.mem x g→IsInSpanAt (n:=n) (·=τ) x g)
    {k : ℕ} (h : IsInSpanOnAt (n:=n) W ((idealPow I k).mem x) x f) :
    ∃c,HolomorphicAt n c x ∧ ∀ᶠy in 𝓝 x,y∈W→f y=c y*τ y^k := by
  obtain ⟨K,s,a,hs,ha,hEq⟩:=h
  choose c hc hceq using fun i=>MonomialPart.exists_eq_mul_pow_of_mem_idealPow hτ (hs i)
  refine ⟨fun y=>∑i,a i y*c i y,HolomorphicAt.sum _ fun i _=>(ha i).mul (hc i),?_⟩
  filter_upwards [hEq,eventually_all.mpr hceq] with y hy hyc hyW
  rw [hy hyW,Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _=>by rw [hyc i];ring

private theorem pulled_centre_span (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (_hzN : z∈geoStrictTransform π C S.N) (hzC : π z∈C)
    (k : ℕ) (hDiv : IsDivNearAlong n S.N S.ideal C k (π z)) :
    ∀F,(GermIdeal.pullback (m:=n) π S.ideal).mem z F→
      IsInSpanOnAt (n:=n) (geoStrictTransform π C S.N)
        ((idealPow (exceptionalDivisor hπ).ideal k).mem z) z F := by
  obtain ⟨rN,hrN⟩:=hN.2 (π z) (hC.subset_N hzC)
  obtain ⟨ρ,hρ⟩:=exists_isLocalRetraction hrN
  obtain ⟨rC,hrC⟩:=hC.1.2 (π z) hzC
  have hInter : S.N∩C=C:=inter_eq_right.mpr hC.subset_N
  have hNC : RegularAtDim (n:=n) (S.N∩C) (π z) rC:=by rw [hInter];exact hrC
  have hπat : ∀ᶠw in 𝓝 z,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π w:=
    Eventually.of_forall fun _=>hπ.contMDiff.contMDiffAt
  intro F hF
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hF))
  rintro _ ⟨f,hf,rfl⟩
  obtain ⟨g,hg,hEq⟩:=(isDivNearAlong_iff hI hρ hNC).mp hDiv f hf
  rw [hInter] at hg
  have hgπ : (idealPow (exceptionalDivisor hπ).ideal k).mem z (g∘π) := by
    rw [←pullback_idealPow_vanishingIdeal hπ k]
    exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨g,hg,rfl⟩ ((holomorphicAt_of_mem_idealPow hg).comp_contMDiff hπat))
  refine ⟨1,fun _=>g∘π,fun _=>1,fun _=>hgπ,fun _=>holomorphicAt_const 1,?_⟩
  filter_upwards [hπ.contMDiff.continuous.continuousAt.eventually hEq] with y hy hyN
  simpa using hy (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hyN)

private theorem born_divisibility_span (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hzN : z∈geoStrictTransform π C S.N) (hzC : π z∈C)
    (b : ℕ) (hDiv : IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (π ⁻¹' C) b z) :
    ∀f,(S.geoTransform C π).ideal.mem z f→
      IsInSpanOnAt (n:=n) (geoStrictTransform π C S.N)
        ((idealPow (exceptionalDivisor hπ).ideal b).mem z) z f := by
  have hN':=isClosedSubmanifold_geoTransform_N hN hC hπ
  have hI':=isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hC hπ
  obtain ⟨rN,hrN⟩:=hN'.2 z hzN
  obtain ⟨ρ,hρ⟩:=exists_isLocalRetraction hrN
  have hn:=SimultaneousNormalCrossings.pos_of_isBlowupAlong hπ hzC
  obtain ⟨rD,hrD⟩:=regularAtDim_inter_get hn hN'.1 (isSNCDivisor_preimage_centre hπ)
    (isTransverse_preimage_centre hπ hN hC.subset_N) ⟨0,by simp⟩ hzN hzC
  change RegularAtDim (n:=n) (geoStrictTransform π C S.N∩π ⁻¹' C) z rD at hrD
  intro f hf
  obtain ⟨g,hg,hEq⟩:=(isDivNearAlong_iff hI' hρ hrD).mp hDiv f hf
  apply (isInSpanOnAt_idealPow_exceptionalDivisor_iff hπ hN hC.subset_N hzC hzN b f).mpr
  exact ⟨1,fun _=>g,fun _=>1,fun _=>hg,fun _=>holomorphicAt_const 1,
    hEq.mono fun y hy hyN=>by simpa using hy hyN⟩

private theorem pushed_centre_divisibility (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hzN : z∈geoStrictTransform π C S.N) (hzC : π z∈C)
    (b : ℕ) (hDiv : IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal
      (π ⁻¹' C) b z) : IsDivNearAlong n S.N S.ideal C (S.d+b) (π z) := by
  have hSpan:=born_divisibility_span S hN hI hC hπ hzN hzC b hDiv
  have hRel:=ExceptionalPushforwardAlong.restrictLe_pullback_geoTransform hπ hN hI hC.2.1
  have hD:=(BlowupExceptionalDivisor.isCoherent_ideal (exceptionalDivisor hπ))
  have hπat : ∀ᶠw in 𝓝 z,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π w:=
    Eventually.of_forall fun _=>hπ.contMDiff.contMDiffAt
  apply isDivNearAlong_of_forall_mem hI (A:=C) (fun _ _hyN hyC=>hyC)
  intro f hf
  have hfπ : (GermIdeal.pullback (m:=n) π S.ideal).mem z (f∘π):=
    GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨f,hf,rfl⟩ ((hol hI _ _ hf).comp_contMDiff hπat))
  have hPower : IsInSpanOnAt (n:=n) (geoStrictTransform π C S.N)
      ((idealPow (exceptionalDivisor hπ).ideal (S.d+b)).mem z) z (f∘π) := by
    refine IsInSpanOnAt.trans (fun s hs=>?_) (hRel z hzN (f∘π) hfπ)
    refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (InvertibleIdealQuotient.mem_mul_iff.mp hs))
    rintro _ ⟨p,q,hp,hq,rfl⟩
    have hpSpan:=IsInSpanAt.restrict (W:=geoStrictTransform π C S.N) (InvertibleIdealQuotient.isInSpanAt_self hp
      (holomorphicAt_of_mem_idealPow hp))
    refine IsInSpanOnAt.mono ?_ (MarkedIdealOperationsAlong.IsInSpanOnAt.mul hpSpan (hSpan q hq))
    rintro _ ⟨u,v,hu,hv,rfl⟩
    rw [RestrictLeCalculus.idealPow_add hD]
    exact IdealOrderArithmetic.mul_mem_mul hu hv
      ((holomorphicAt_of_mem_idealPow hu).mul (holomorphicAt_of_mem_idealPow hv))
  obtain ⟨K,s,a,hs,ha,hEq⟩:=mem_idealPow_vanishingIdeal_along_of_pullback
    hπ hN hC.subset_N hzC hzN (hol hI _ _ hf) hPower
  exact ⟨fun x=>∑i,a i x*s i x,OrderTaylor.mem_idealPow_sum Finset.univ
    (fun i _=>mul_mem_idealPow (ha i) (hs i)),hEq⟩

private theorem lowered_born_divisibility (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hzN : z∈geoStrictTransform π C S.N) (hzC : π z∈C)
    (b : ℕ) (hDiv : IsDivNearAlong n S.N S.ideal C (S.d+b) (π z)) :
    IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal (π ⁻¹' C) b z := by
  have hI':=isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hC hπ
  have hInv : IsInvertibleAlong n (geoStrictTransform π C S.N) (exceptionalDivisor hπ).ideal := by
    have h:=isInvertibleAlong_geoStrictTransform hπ S.N 1
    change IsInvertibleAlong n (geoStrictTransform π C S.N)
      (idealPow (exceptionalDivisor hπ).ideal 1) at h
    rwa [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at h
  obtain ⟨U,hU,hzU,τ,hτdiff,hnon,hGen⟩:=hInv z hzN
  have hτhol : HolomorphicAt n τ z:=holomorphicAt_of_mdifferentiableOn hU hτdiff hzU
  have hτD : (exceptionalDivisor hπ).ideal.mem z τ:=
    (hGen z hzU τ).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hτhol)
  have hτd:=MonomialPart.pow_mem_idealPow hτD hτhol S.d
  have hnonPow : ∀V : Set Y,IsOpen V→V⊆U→(V∩geoStrictTransform π C S.N).Nonempty→
      ∃y∈V∩geoStrictTransform π C S.N,τ y^S.d≠0 := by
    intro V hV hVU hVN
    obtain ⟨y,hy,hyτ⟩:=hnon V hV hVU hVN
    exact ⟨y,hy,pow_ne_zero _ hyτ⟩
  apply isDivNearAlong_of_forall_mem hI' (A:=π ⁻¹' C) (fun _ _hyN hyD=>hyD)
  intro f hf
  change HolomorphicAt n f z ∧ ∀g,(idealPow (exceptionalDivisor hπ).ideal S.d).mem z g→
    (restrictOn n (geoStrictTransform π C S.N) (GermIdeal.pullback (m:=n) π S.ideal)).mem z
      (fun y=>g y*f y) at hf
  have hSpan:=IsInSpanOnAt.trans (pulled_centre_span S hN hI hC hπ hzN hzC (S.d+b) hDiv)
    (hf.2 (fun y=>τ y^S.d) hτd).2
  obtain ⟨c,hc,hEq⟩:=span_power_factor (fun g hg=>(hGen z hzU g).mp hg) hSpan
  have hGamma : HolomorphicAt n (fun y=>c y*τ y^b) z:=
    hc.mul (CompanionReduction.holomorphicAt_pow_of hτhol b)
  have hCancel : ∀ᶠy in 𝓝 z,y∈geoStrictTransform π C S.N→
      τ y^S.d*f y=τ y^S.d*(c y*τ y^b) := by
    filter_upwards [hEq] with y hy hyN
    rw [hy hyN,pow_add]
    ring
  have hFinal:=eventuallyEq_within_of_mul_eventuallyEq_within hU hnonPow hzU hf.1 hGamma hCancel
  have hGammaD:=mul_mem_idealPow hc (MonomialPart.pow_mem_idealPow hτD hτhol b)
  have hGammaV := mem_idealPow_of_forall_mem (fun q hq=>
    (exceptionalDivisor_mem_iff_vanishingIdeal hπ hzC q).mp hq) b hGammaD
  exact ⟨fun y=>c y*τ y^b,hGammaV,hFinal⟩

/-- The exact LOCAL centre-adic and born-divisor divisibility predicates for
the actual controlled transform. No point ordinary order is substituted. -/
theorem controlled_born_divisibility (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hzN : z∈(S.geoTransform C π).N) (hzC : π z∈C) (b : ℕ) :
    IsDivNearAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal (π ⁻¹' C) b z ↔
      IsDivNearAlong n S.N S.ideal C (S.d+b) (π z) :=
  ⟨pushed_centre_divisibility S hN hI hC hπ hzN hzC b,
    lowered_born_divisibility S hN hI hC hπ hzN hzC b⟩

private theorem exponent_at_sharp (N C : Set X) (I : GermIdeal n X) (x : X) (k : ℕ)
    (hGood : IsDivNearAlong n N I C k x) (hBad : ¬IsDivNearAlong n N I C (k+1) x) :
    divExpAlong n N I C x=k := by
  have hExists : ∃q,¬IsDivNearAlong n N I C (q+1) x:=⟨k,hBad⟩
  unfold divExpAlong
  rw [dif_pos hExists]
  apply Nat.le_antisymm (Nat.find_min' hExists hBad)
  by_contra h
  exact Nat.find_spec hExists (hGood.mono (by omega))

private theorem born_exponent (S : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n S.N) (hI : S.ideal.IsCoherent)
    {C : Set X} (hC : S.IsAdmissibleCentre C) {π : Y→X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hzN : z∈(S.geoTransform C π).N) (hzC : π z∈C)
    (hne : IsNonzeroAlongAt S.N S.ideal (π z)) :
    S.d≤divExpAlong n S.N S.ideal C (π z) ∧
      divExpAlong n (S.geoTransform C π).N (S.geoTransform C π).ideal (π ⁻¹' C) z=
        divExpAlong n S.N S.ideal C (π z)-S.d := by
  let a:=divExpAlong n S.N S.ideal C (π z)
  obtain ⟨rN,hrN⟩:=hN.2 (π z) (hC.subset_N hzC)
  obtain ⟨ρ,hρ⟩:=exists_isLocalRetraction hrN
  have hGood : IsDivNearAlong n S.N S.ideal C a (π z):=isDivNearAlong_divExpAlong (hol hI) _
  have hBad : ¬IsDivNearAlong n S.N S.ideal C (a+1) (π z):=
    not_isDivNearAlong_divExpAlong_succ hρ hzC hne (hol hI)
  have hMark : IsDivNearAlong n S.N S.ideal C S.d (π z):=
    Eventually.of_forall fun y _hyN hyC=>hC.2.1 hyC
  have hda : S.d≤a:=(isDivNearAlong_iff_le_divExpAlong hρ hzC hne (hol hI)).mp hMark
  have hShift : S.d+(a-S.d)=a:=by omega
  have hShiftOne : S.d+(a-S.d+1)=a+1:=by omega
  refine ⟨hda,exponent_at_sharp _ _ _ _ (a-S.d) ?_ ?_⟩
  · apply (controlled_born_divisibility S hN hI hC hπ hzN hzC (a-S.d)).mpr
    rwa [hShift]
  · intro h
    apply hBad
    have hSource:=(controlled_born_divisibility S hN hI hC hπ hzN hzC (a-S.d+1)).mp h
    rwa [hShiftOne] at hSource

/-- The actual local C-adic exponent minus the literal mark is the actual
born exponent. All local finiteness and natural subtraction are derived. -/
theorem original_history_born_exponent (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (T : BlowupTower X Y) (hT : IsGeoTestTower Q T)
    {C : Set Y} (hC : (geoTransformAlong Q T).IsAdmissibleCentre C)
    {Z : CMfd.{u} n} {π : Z→Y} (hπ : IsBlowupAlong n C π)
    {z : Z} (hzN : z∈((geoTransformAlong Q T).geoTransform C π).N) (hzC : π z∈C) :
    Q.d≤divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal C (π z) ∧
      divExpAlong n ((geoTransformAlong Q T).geoTransform C π).N
        ((geoTransformAlong Q T).geoTransform C π).ideal (π ⁻¹' C) z=
      divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal C (π z)-Q.d := by
  have hCurrent:=isInvDomain_geoTransformAlong hQ T hT
  have hBirth:=born_exponent (geoTransformAlong Q T) hCurrent.isWellFormed.isClosedSubmanifold_N
    hCurrent.isWellFormed.isCoherent hC hπ hzN hzC
    (hCurrent.isNonzeroAlongAt (π z) (hC.subset_N hzC))
  simpa only [d_geoTransformAlong] using hBirth


end
end Hironaka.HironakaActualPolymorphicBornExponent
