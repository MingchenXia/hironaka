import Hironaka.Resolution.HironakaG8ChronologicalNativeClassAtlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeRestartQuotientChartProvider
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec RelativePrincipalizationSpan
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaG8NativeCommonDenominatorReduction HironakaG8ChronologicalNativeClassAtlas
  HironakaG8PrincipalRetainedEpochFinite DivisorExponentAlong MonomialPartAlong
  InvertibleIdealQuotient CompanionReduction HironakaG8LocalHistory

private theorem principal_mul_generated_family
    {n : ℕ} {X : CMfd.{0} n} {ι : Type}
    (u : X → ℂ) (f : ι → X → ℂ) (hu : ∀ x, HolomorphicAt n u x)
    (hf : ∀ x i, HolomorphicAt n (f i) x) :
    (finiteFunctionIdeal (n := n) (fun _ : Unit => u)).mul (finiteFunctionIdeal f) =
      finiteFunctionIdeal (fun i => u * f i) := by
  ext x g
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_mul_iff.mp hg)
    rintro _ ⟨a,b,ha,hb,rfl⟩
    have ha' : IsInSpanAt (n := n) (fun z => z ∈ range (fun _ : Unit => u)) x a := ha
    have hb' : IsInSpanAt (n := n) (fun z => z ∈ range f) x b := hb
    obtain ⟨N,s,c,hs,hc,hEq⟩ := MarkedIdealOperationsAlong.IsInSpanOnAt.mul (W := univ)
      (IsInSpanAt.restrict ha') (IsInSpanAt.restrict hb')
    refine ⟨ha'.1.mul hb'.1,N,s,c,?_,hc,hEq.mono fun _ h => h trivial⟩
    intro i
    obtain ⟨_,_,⟨_,rfl⟩,⟨j,rfl⟩,h⟩ := hs i
    exact ⟨j,h.symm⟩
  · intro hg
    apply mem_mul_iff.mpr
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    exact ⟨u,f i,isInSpanAt_self ⟨(),rfl⟩ (hu x),isInSpanAt_self ⟨i,rfl⟩ (hf x i),rfl⟩

/-- Separately powered native coefficients lie in their lower common-mark
reference ideal. In particular native nonzero germs already witness
nonzeroness of the lower normalized family. -/
theorem weightedFunctionIdeal_le_common_denominator
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (f : ι → X → ℂ) (hf : ∀ x i, HolomorphicAt n (f i) x)
    (d : ℕ) (hd : 0 < d) (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w) :
    (weightedFunctionIdeal (n := n) w f).Le (finiteFunctionIdeal (fun i => f i ^ (d/w i))) := by
  rw [weightedFunctionIdeal_eq_common_denominator_power w hw f d hWeights hDvd]
  intro x g hg
  refine IsInSpanAt.trans ?_ hg
  rintro _ ⟨i,rfl⟩
  let F := f i ^ (d/w i)
  let e := weightedCommonMark w / d
  have he : 0 < e := Nat.div_pos (Nat.le_of_dvd (weightedCommonMark_pos w hw) hDvd) hd
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  change IsInSpanAt (n := n) (fun g => g ∈ range (fun j => f j ^ (d/w j))) x (F^e)
  rw [hr,pow_succ]
  have hF : HolomorphicAt n F x := holomorphicAt_pow_of (hf x i) _
  exact IsInSpanAt.mul_left (holomorphicAt_pow_of hF r)
    (isInSpanAt_self ⟨i,rfl⟩ hF)

/-- An actual raw nonfactor witness on a touching slot produces a literal
coefficient that stays nonzero arbitrarily close on that slot. -/
theorem native_quotient_not_vanishing_on_boundary
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (Q : MarkedIdeal n X) (hq : Q.IsWellFormed) (hN : Q.N = univ)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (f : ι → X → ℂ) (hf : ∀ x i, HolomorphicAt n (f i) x)
    (hGen : Q.ideal = weightedFunctionIdeal w f)
    (hNo : ∀ y ∈ Q.N, ∀ i : Fin Q.E.length, y ∈ Q.E.get i →
      ∃ g, Q.ideal.mem y g ∧ ¬ IsInSpanOnAt (n := n) Q.N ((vanishingIdeal (n := n) (Q.E.get i)).mem y) y g)
    (x : X) (i : Fin Q.E.length) (hx : x ∈ Q.E.get i) :
    ∃ j, ∃ᶠ z in 𝓝 x, z ∈ Q.E.get i ∧ f j z ≠ 0 := by
  classical
  by_contra h
  have hV (j : ι) : ∀ᶠ z in 𝓝 x, z ∈ Q.E.get i → f j z = 0 := by
    have hNot : ¬ ∃ᶠ z in 𝓝 x, z ∈ Q.E.get i ∧ f j z ≠ 0 := fun hj => h ⟨j,hj⟩
    rw [Filter.not_frequently] at hNot
    exact hNot.mono fun z hz hzE => by by_contra hne; exact hz ⟨hzE,hne⟩
  have hxN : x ∈ Q.N := hN ▸ mem_univ x
  obtain ⟨g,hg,hNot⟩ := hNo x hxN i hx
  apply hNot
  rw [hGen] at hg
  refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict hg)
  obtain ⟨j,rfl⟩ := hs
  let e := weightedCommonMark w / w j
  have hHol : HolomorphicAt n (f j ^ e) x := holomorphicAt_pow_of (hf x j) e
  apply (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem_of_isWellFormed hq hxN i hHol).mpr
  refine ⟨hHol, ?_⟩
  filter_upwards [hV j] with z hz hzE
  have hpos := compressionExponent_pos w hw j
  change f j z ^ e = 0
  rw [hz hzE.2]
  exact zero_pow (Nat.ne_of_gt hpos)

private theorem denominator_power_ideal_of_exceptional_generator
    {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π)
    (u : Y → ℂ) (hu : ∀ y, HolomorphicAt n u y) (d : ℕ)
    (hU : finiteFunctionIdeal (n := n) (fun _ : Unit => u) =
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal) :
    IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d =
      finiteFunctionIdeal (n := n) (fun _ : Unit => u^d) := by
  ext x a
  have huGen (g : Y → ℂ) :
      ((BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal).mem x g ↔
        IsInSpanAt (n := n) (· = u) x g := by
    rw [← hU]
    change IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u)) x g ↔ _
    exact ⟨IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm),
      IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩)⟩
  change _ ↔ IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => u^d)) x a
  rw [HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff (hu x) huGen]
  exact ⟨IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩),
    IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm)⟩

/-- The literal controlled native coefficient quotient at one actual cut
constructs the restart chart. The actual exceptional equation supplies
denominator geometry, and native domain and complete boundary
nonfactor data supply all remaining normalized witnesses. -/
def native_restart_quotient_chart_of_single_cut
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (P : MarkedIdeal n X) (hp : IsInvDomain n P) (hN : P.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hC : P.IsAdmissibleCentre C)
    (Q : MarkedIdeal n Y) (hq : IsInvDomain n Q)
    (hNo : ∀ y ∈ Q.N, ∀ i : Fin Q.E.length, y ∈ Q.E.get i →
      ∃ g, Q.ideal.mem y g ∧ ¬ IsInSpanOnAt (n := n) Q.N ((vanishingIdeal (n := n) (Q.E.get i)).mem y) y g)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) (hd : 0 < d)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (q : ι → Y → ℂ) (hqHol : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (hU : finiteFunctionIdeal (n := n) (fun _ : Unit => u) = (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i (π y) = u y ^ w i * q i y)
    (hRaw : Q = ⟨univ,(P.geoTransform C π).E,weightedFunctionIdeal w q,weightedCommonMark w⟩) :
    NativeRestartQuotientChart (ι := ι) (P.geoTransform C π) Q d := by
  let A := P.geoTransform C π
  have hAN : A.N = univ := geoTransform_N_eq_univ hN hπ
  have hQN : Q.N = univ := congrArg MarkedIdeal.N hRaw
  have hQE : Q.E = A.E := by
    have hEq := congrArg (fun R : MarkedIdeal n Y => R.E) hRaw
    exact hEq
  have hQGen : Q.ideal = weightedFunctionIdeal w q := congrArg MarkedIdeal.ideal hRaw
  have hu' (y : Y) : HolomorphicAt n u y := Eventually.of_forall fun z => hu z
  have hq' (y : Y) (j : ι) : HolomorphicAt n (q j) y := Eventually.of_forall fun z => hqHol j z
  have hPow := denominator_power_ideal_of_exceptional_generator hπ u hu' d hU
  obtain ⟨_,hNZ,hMono⟩ := HironakaSharpActualMonomialDivisionResidual.actual_new_exceptional_power_monomial
    hn hp.isWellFormed.isClosedSubmanifold_N hp.isWellFormed.isSNCDivisor hp.isWellFormed.isTransverse
    hπ hC.subset_N hC.2.2 d
  change (∀ y ∈ A.N, IsNonzeroAlongAt A.N
    (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d) y) at hNZ
  change IsMonomialAlong n A.N (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d)
    A.E at hMono
  rw [hAN,hPow] at hNZ hMono
  refine ⟨X,P,hp,hN,.step .refl C π hπ,⟨trivial,hC⟩,rfl,w,hw,hWeights,hDvd,
    F,hF,hGen,q,hqHol,u,hu,hQuot,?_,hMono,?_,?_,hRaw⟩
  · intro y
    by_contra h
    rw [Filter.not_frequently] at h
    have hz : ∀ᶠ z in 𝓝 y, u z = 0 := h.mono fun _ hz => Classical.not_not.mp hz
    obtain ⟨g,hg,hF⟩ := hNZ y (mem_univ y)
    apply hF
    change IsInSpanAt (n := n) (fun s => s ∈ range (fun _ : Unit => u^d)) y g at hg
    obtain ⟨_,N,s,a,hs,ha,hSum⟩ := hg
    filter_upwards [hz,hSum] with z hzero heq
    rintro ⟨_,hne⟩
    apply hne
    rw [heq]
    apply Finset.sum_eq_zero
    intro j _
    obtain ⟨_,hj⟩ := hs j
    rw [← hj]
    change a j z * u z ^ d = 0
    rw [hzero,zero_pow (Nat.ne_of_gt hd),mul_zero]
  · have h : ∀ y : Y, ∀ j : Fin Q.E.length, y ∈ Q.E.get j →
        ∃ v, ∃ᶠ z in 𝓝 y, z ∈ Q.E.get j ∧ q v z ≠ 0 := by
      intro y j hy
      exact native_quotient_not_vanishing_on_boundary Q hq.isWellFormed hQN w hw q hq' hQGen hNo y j hy
    rw [hQE] at h
    exact h
  · intro y hy
    obtain ⟨g,hg,hFreq⟩ := hq.isNonzeroAlongAt y (hQN ▸ hy)
    have hLe := weightedFunctionIdeal_le_common_denominator w hw q hq' d hd hWeights hDvd
    exact ⟨g,hLe y g (hQGen ▸ hg),hQN ▸ hFreq⟩

/-- The true controlled transform of the entire native coefficient ideal
is the weighted span of the actual quotients on the chosen blowup chart. -/
theorem native_controlled_ideal_of_quotient_equations
    {n : ℕ} {X Y : CMfd.{0} n} {ι : Type} [Fintype ι]
    (Q : MarkedIdeal n X) (hq : Q.IsWellFormed) (hN : Q.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (w : ι → ℕ) (hMark : Q.d = weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (F i))
    (hGen : Q.ideal = weightedFunctionIdeal w F)
    (q : ι → Y → ℂ) (hqHol : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) u)
    (hU : finiteFunctionIdeal (n := n) (fun _ : Unit => u) = (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i (π y) = u y ^ w i * q i y) :
    (Q.geoTransform C π).ideal = weightedFunctionIdeal w q := by
  let d := weightedCommonMark w
  let e := fun i => d / w i
  have hu' (y : Y) : HolomorphicAt n u y := Eventually.of_forall fun z => hu z
  have hPow := denominator_power_ideal_of_exceptional_generator hπ u hu' d hU
  have hEq : GermIdeal.pullback (m := n) π Q.ideal =
      (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal d).mul
        (weightedFunctionIdeal w q) := by
    rw [hGen,hPow]
    change GermIdeal.pullback (m := n) π (finiteFunctionIdeal (fun i => F i ^ e i)) =
      (finiteFunctionIdeal (fun _ : Unit => u^d)).mul (finiteFunctionIdeal (fun i => q i ^ e i))
    rw [HironakaActualWeightedNormalPadding.finiteFunctionIdeal_pullback _ (fun i => (hF i).pow _) π hπ.contMDiff,
      principal_mul_generated_family (u^d) (fun i => q i ^ e i)
        (fun y => holomorphicAt_pow_of (hu' y) _) (fun _ i => Eventually.of_forall fun z => ((hqHol i).pow _) z)]
    apply congrArg (finiteFunctionIdeal (n := n))
    funext i y
    change F i (π y) ^ e i = u y ^ d * q i y ^ e i
    rw [hQuot,mul_pow,← pow_mul]
    change u y ^ (w i * (weightedCommonMark w / w i)) * q i y ^ e i = _
    rw [weight_mul_compressionExponent]
  rw [geoTransform_ideal_eq_controlledTransform hN hq.isCoherent hπ, hMark]
  exact (BlowupControlledTransform.eq_controlledTransform_of_eq_mul hπ
    (isCoherent_weightedFunctionIdeal w q hqHol) hEq).symm

/-- At a common actual cut, the native and low marks may differ.
The controlled native coefficient step supplies the restart chart and
its target weighted ideal and full nonfactor data. -/
def native_restart_chart_of_common_controlled_cut
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π) (hPC : P.IsAdmissibleCentre C) (hQC : Q.IsAdmissibleCentre C)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) (hd : 0 < d)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (hRaw : Q = ⟨univ,P.E,weightedFunctionIdeal w F,weightedCommonMark w⟩)
    (hQNo : HasNoBoundaryFactor Q)
    (hCap : HomogenizedIdealAlong.IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (q : ι → Y → ℂ) (hqHol : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) u)
    (hU : finiteFunctionIdeal (n := n+1) (fun _ : Unit => u) =
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i (π y) = u y ^ w i * q i y) :
    NativeRestartQuotientChart (ι := ι) (P.geoTransform C π) (Q.geoTransform C π) d := by
  have hQN : Q.N = univ := congrArg MarkedIdeal.N hRaw
  have hQE : Q.E = P.E := by
    have h := congrArg (fun R : MarkedIdeal (n+1) X => R.E) hRaw
    exact h
  have hQM := congrArg (fun R : MarkedIdeal (n+1) X => R.d) hRaw
  have hQI := congrArg (fun R : MarkedIdeal (n+1) X => R.ideal) hRaw
  have hI := native_controlled_ideal_of_quotient_equations Q hq.isWellFormed hQN hπ w hQM F hF hQI q hqHol u hu hU hQuot
  have hQ1 := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hQC⟩
  have hQ1No := hasNoBoundaryFactor_step Q hq.isWellFormed hQNo hπ hQC hCap
  have hR : Q.geoTransform C π = ⟨univ,(P.geoTransform C π).E,weightedFunctionIdeal w q,weightedCommonMark w⟩ := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (geoTransform_N_eq_univ hQN hπ) ?_ hI hQM
    change Q.E.map _ ++ _ = P.E.map _ ++ _
    rw [hQE]
  exact native_restart_quotient_chart_of_single_cut (Nat.succ_pos n) P hp hPN hπ hPC
    (Q.geoTransform C π) hQ1 hQ1No w hw d hd hWeights hDvd F hF hGen q hqHol u hu hU hQuot hR

/-- Starting with the two genuine marked source records, the actual
native controlled coefficient step supplies its restart quotient chart.
Target native ideal identity and target nonfactor are derived. -/
def native_restart_chart_of_controlled_native_step
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π) (hPC : P.IsAdmissibleCentre C)
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) (hd : 0 < d) (hPd : P.d = d)
    (hWeights : ∀ i, w i ∣ d) (hDvd : d ∣ weightedCommonMark w)
    (F : ι → X → ℂ) (hF : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (F i))
    (hGen : P.ideal = finiteFunctionIdeal (fun i => F i ^ (d/w i)))
    (hRaw : Q = ⟨univ,P.E,weightedFunctionIdeal w F,weightedCommonMark w⟩)
    (hQNo : HasNoBoundaryFactor Q)
    (hCap : HomogenizedIdealAlong.IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (q : ι → Y → ℂ) (hqHol : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (q i))
    (u : Y → ℂ) (hu : MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) u)
    (hU : finiteFunctionIdeal (n := n+1) (fun _ : Unit => u) =
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal)
    (hQuot : ∀ i y, F i (π y) = u y ^ w i * q i y) :
    NativeRestartQuotientChart (ι := ι) (P.geoTransform C π) (Q.geoTransform C π) d := by
  have hP0 : P = ⟨univ,P.E,finiteFunctionIdeal (fun i => F i ^ (d/w i)),d⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hPN rfl hGen hPd
  have hc : LocWPEquiv Q P := by
    have hP' := hp
    have hQ' := hq
    rw [hP0] at hP' ⊢
    rw [hRaw] at hQ' ⊢
    exact (common_denominator_native_boundary_class w hw F hF d hd hWeights hDvd P.E hP' hQ').1
  have hQC := (HironakaG8MixedEquiv.isAdmissibleCentre_congr hc.E_eq hc.cosupp_eq_base.symm C).mp hPC
  exact native_restart_chart_of_common_controlled_cut P Q hp hq hPN hπ hPC hQC
    w hw d hd hWeights hDvd F hF hGen hRaw hQNo hCap q hqHol u hu hU hQuot

/-- Complete boundary noncontainment of a literal source coefficient
family gives the source factor-free condition used by the actual cut. -/
theorem weighted_source_hasNoBoundaryFactor_of_generator_traces
    {n : ℕ} {X : CMfd.{0} (n+1)} {ι : Type} [Fintype ι]
    (Q : MarkedIdeal (n+1) X) (hq : Q.IsWellFormed) (hN : Q.N = univ)
    (w : ι → ℕ) (f : ι → X → ℂ) (hf : ∀ x i, HolomorphicAt (n+1) (f i) x)
    (hGen : Q.ideal = weightedFunctionIdeal w f)
    (hTrace : ∀ x : X, ∀ i : Fin Q.E.length, x ∈ Q.E.get i →
      ∃ j, ∃ᶠ z in 𝓝 x, z ∈ Q.E.get i ∧ f j z ≠ 0) :
    HasNoBoundaryFactor Q := by
  intro x _ i hx
  obtain ⟨j,hj⟩ := hTrace x i hx
  let e := weightedCommonMark w / w j
  refine ⟨f j ^ e, ?_, ?_⟩
  · rw [hGen]
    exact isInSpanAt_self ⟨j,rfl⟩ (holomorphicAt_pow_of (hf x j) e)
  · rw [hN]
    exact HironakaG8ActualQuotientResidualRestart.quotient_power_not_boundary_factor
      Q hq hN x i (f j) (hf x j) e hj

/-- Actual native HS point data give the source cap required by the one-cut
producer whenever the native mark exceeds one. -/
theorem native_source_cap_of_state
    {n : ℕ} {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ}
    (Q : MarkedIdeal n X) (hS : HironakaG11PresLineState.NativeHSState Q W H)
    (hLarge : 1 < Q.d) :
    HomogenizedIdealAlong.IsMaximalOrderAlong Q.N Q.ideal Q.d := by
  obtain ⟨_,_,hN,hQ,V,S,k,a,w,hw,_,_,hMark,_,_,hAt⟩ := hS
  have hv : V.Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    have hm : Q.d = 1 := by
      rw [hMark]
      subst V
      simp [weightedCommonMark]
    omega
  exact HironakaActualHistoricalNativeOrdinaryOrder.actual_native_current_maximal_order
    S hv a w hw W Q hN hQ hMark hAt

end
end Hironaka.HironakaG8NativeRestartQuotientChartProvider
