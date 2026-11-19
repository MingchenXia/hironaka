import Hironaka.Resolution.HironakaActualProjectionVerticalBlowupChart
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaActualPointNormalizedExponents
import Hironaka.Blowup.ExceptionalPushforwardAlong
import Hironaka.Blowup.BlowupTowers

/-! P05-A: exact coordinate-mask point powers and all original function
cuts in one actual projected vertical chart. The full native product and
ordered boundary are retained; whole-ideal order and quotient comparison
are separate consumers. Blueprint first. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualProjectionVerticalFunctionOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupSNCTransform BlowupMonomialCharts BlowupStrictSubmanifold
  HironakaSmoothSubmersionUniversalBlowupChartEquality HironakaActualProjectionTestRecord
  HironakaActualProjectionVerticalBlowupChart ProductComplexManifold MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec HironakaRelativeNormalIdeal
  NormalCrossings GiraudAlong GermIdealOrder IdealWeightPowers OrderTaylor
  HadamardBridge BlowupFlatCoordinates ExceptionalPushforwardAlong HolGerm
  HironakaActualOriginalFormalTaylor HironakaActualAnalyticFormalNormalPowers
  HironakaActualAnalyticBlowupTaylor HironakaActualTaylorCoordinateNaturality
  HironakaActualFormalMonomialBlowupReflection HironakaActualPointNormalizedExponents
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalCoordinatePowerDivision
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
open scoped ProductComplexManifold

/-- The literal continuous linear retraction zeroing precisely the finite mask. -/
def maskRetract {n : ℕ} (S : Finset (Fin n)) : ComplexModel n →L[ℂ] ComplexModel n :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n=>i∉S),
    (EuclideanSpace.proj (𝕜 := ℂ) i).smulRight (EuclideanSpace.single i (1 : ℂ))

private theorem maskRetract_apply {n : ℕ} (S : Finset (Fin n)) (w : ComplexModel n) (j : Fin n) :
    maskRetract S w j=if j∈S then 0 else w j := by
  simp only [maskRetract,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply,WithLp.ofLp_smul,PiLp.single_apply,Pi.smul_apply,smul_eq_mul,
    mul_ite,mul_one,mul_zero,EuclideanSpace.proj,PiLp.proj_apply]
  rw [Finset.sum_ite_eq]
  simp

private theorem maskRetract_mem {n : ℕ} (S : Finset (Fin n)) (w : ComplexModel n) :
    maskRetract S w∈coordSubspace S := by
  intro i hi
  rw [maskRetract_apply,if_pos hi]

private theorem maskRetract_of_mem {n : ℕ} {S : Finset (Fin n)} {w : ComplexModel n}
    (hw : w∈coordSubspace S) : maskRetract S w=w := by
  ext i
  rw [maskRetract_apply]
  split_ifs with hi
  · exact (hw i hi).symm
  · rfl

variable {n : ℕ} {X : CMfd.{u} n} {x : X}

/-- A genuine function obtained from the original function by the actual chart inverse and mask. -/
def maskFlatten (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n)) (f : X→ℂ) : ComplexModel n→ℂ :=
  fun w=>f (flatInv Φ (maskRetract S w))

private theorem masked_inverse_geometry
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (S : Finset (Fin n)) :
    let ν : ComplexModel n→X:=fun w=>flatInv Φ (maskRetract S w)
    ν 0=x ∧
      (∀ᶠw in 𝓝 0,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ν w) ∧
      Tendsto ν (𝓝 0) (𝓝 x) ∧
      ∀ᶠw in 𝓝 0,maskRetract S w∈Φ.target := by
  dsimp only
  have hν0 : flatInv Φ (maskRetract S 0)=x := by
    rw [map_zero,flatInv_zero h0]
  have hR : Tendsto (maskRetract S) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (maskRetract S).continuous.tendsto 0
  have hT : ∀ᶠw in 𝓝 (0 : ComplexModel n),maskRetract S w∈Φ.target :=
    hR.eventually (Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target h0))
  have hν : ∀ᶠw in 𝓝 (0 : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
        (fun w=>flatInv Φ (maskRetract S w)) w := by
    filter_upwards [hT] with w hw
    exact (ExceptionalPushforwardAlong.mdifferentiableAt_flatInv hsrc hw).comp w
      (maskRetract S).differentiableAt.mdifferentiableAt
  refine ⟨hν0,hν,?_,hT⟩
  have h:=hν.self_of_nhds.continuousAt.tendsto
  rwa [hν0] at h

private theorem maskFlatten_holomorphic
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (S : Finset (Fin n)) (f : X→ℂ) (hf : HolomorphicAt n f x) :
    HolomorphicAt n (maskFlatten Φ S f) 0 := by
  obtain ⟨hν0,hν,_,_⟩:=masked_inverse_geometry Φ hsrc h0 S
  dsimp only at hν0
  exact holomorphicAt_comp_map hν (by rw [hν0];exact hf)

private theorem mask_pair_point_power {N : Set X} (a : X)
    (ψ : X→ComplexModel n) (χ : ComplexModel n→X)
    (hψ0 : ψ a=0) (hχ0 : χ 0=a)
    (hψ : ∀ᶠy in 𝓝 a,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ψ y)
    (hχ : ∀ᶠw in 𝓝 (0 : ComplexModel n),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) χ w)
    (hχψ : ∀ᶠy in 𝓝 a,χ (ψ y)=y)
    (hψχ : ∀ᶠw in 𝓝 (0 : ComplexModel n),ψ (χ w)=w)
    (S : Finset (Fin n))
    (hflat : ∀ᶠy in 𝓝 a,y∈N ↔ ψ y∈coordSubspace S)
    (f : X→ℂ) (q : ℕ) :
    VanishesToOrderOn n N a q f ↔
      (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 (fun w=>f (χ (maskRetract S w))) := by
  let ν : ComplexModel n→X:=fun w=>χ (maskRetract S w)
  have hR : Tendsto (maskRetract S) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (maskRetract S).continuous.tendsto 0
  have hν0 : ν 0=a := by change χ (maskRetract S 0)=a;rw [map_zero,hχ0]
  have hν : ∀ᶠw in 𝓝 (0 : ComplexModel n),MDifferentiableAt
      𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ν w := by
    filter_upwards [hR.eventually hχ] with w hw
    exact hw.comp w (maskRetract S).differentiableAt.mdifferentiableAt
  have hνT : Tendsto ν (𝓝 0) (𝓝 a) := by
    have h:=hν.self_of_nhds.continuousAt.tendsto
    rwa [hν0] at h
  have hνN : ∀ᶠw in 𝓝 (0 : ComplexModel n),ν w∈N := by
    filter_upwards [hνT.eventually hflat,hR.eventually hψχ] with w hw hwEq
    apply hw.mpr
    change ψ (χ (maskRetract S w))∈coordSubspace S
    rw [hwEq]
    exact maskRetract_mem S w
  constructor
  · rintro ⟨g,hg,hfg⟩
    have hgν : (idealPow (pointIdeal n (ν 0)) q).mem (ν 0) g := by rw [hν0];exact hg
    have hcomp:=comp_mem_idealPow_pointIdeal hν q hgν
    apply mem_idealPow_congr hcomp
    filter_upwards [hνN,hνT.eventually hfg] with w hwN hwEq
    exact (hwEq hwN).symm
  · intro hF
    have hFψ : (idealPow (pointIdeal n (ψ a)) q).mem (ψ a) (fun w=>f (χ (maskRetract S w))) := by
      rw [hψ0]
      exact hF
    refine ⟨(fun w=>f (χ (maskRetract S w))) ∘ ψ,comp_mem_idealPow_pointIdeal hψ q hFψ,?_⟩
    filter_upwards [hflat,hχψ] with y hy hyInv hyN
    change f y=f (χ (maskRetract S (ψ y)))
    rw [maskRetract_of_mem (hy.mp hyN),hyInv]

/-- Actual centred source geometry, with no order/leading/retraction certificate,
identifies proper-carrier vanishing with the genuine retracted point power. -/
theorem vanishesToOrderOn_iff_mask_point_power
    {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (S : Finset (Fin n))
    (hflat : ∀{y : X},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Φ.source →
      (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace S))
    (f : X→ℂ) (_hf : HolomorphicAt n f x) (q : ℕ) :
    VanishesToOrderOn n N x q f ↔
      (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 (maskFlatten Φ S f) := by
  have hψ : ∀ᶠy in 𝓝 x,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
      (flatMap Φ) y := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    exact ExceptionalPushforwardAlong.mdifferentiableAt_flatMap hy
  have hχ : ∀ᶠw in 𝓝 (0 : ComplexModel n),MDifferentiableAt
      𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (flatInv Φ) w := by
    filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target h0)] with w hw
    exact ExceptionalPushforwardAlong.mdifferentiableAt_flatInv hsrc hw
  have hLeft : ∀ᶠy in 𝓝 x,flatInv Φ (flatMap Φ y)=y := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    exact flatInv_flatMap hy
  have hRight : ∀ᶠw in 𝓝 (0 : ComplexModel n),flatMap Φ (flatInv Φ w)=w := by
    filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target h0)] with w hw
    exact flatMap_flatInv hw hsrc
  have hFlat : ∀ᶠy in 𝓝 x,y∈N ↔ flatMap Φ y∈coordSubspace S := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    exact hflat hy.1 hy.2
  exact mask_pair_point_power x (flatMap Φ) (flatInv Φ) h0 (flatInv_zero h0)
    hψ hχ hLeft hRight S hFlat f q

private def verticalFormal (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin (n+1)) ℂ :=
  actualFormalBlowup Set.univ (Fin.last n) (fun _=>0) (MvPowerSeries.rename (Fin.castAdd 1) F)

private def verticalExponent (α : Fin n→₀ℕ) : Fin (n+1)→₀ℕ :=
  actualMonomialBlowupExponent Set.univ (Fin.last n) (Finsupp.embDomain (Fin.castAddEmb 1) α)

private theorem last_not_cast : Fin.last n∉Set.range (Fin.castAddEmb 1 : Fin n ↪ Fin (n+1)) := by
  rintro ⟨i,hi⟩
  have hv:=congrArg Fin.val hi
  change i.val=n at hv
  exact (Nat.ne_of_lt i.isLt) hv

private theorem vertical_degree (α : Fin n→₀ℕ) :
    normalExponentDegree (verticalExponent α)=2*normalExponentDegree α := by
  let β:=Finsupp.embDomain (Fin.castAddEmb 1) α
  have he : β (Fin.last n)=0:=Finsupp.embDomain_of_notMem_range _ _ _ last_not_cast
  have hd : normalExponentDegree β=normalExponentDegree α := by
    have h:=Finsupp.degree_mapDomain (Fin.castAddEmb 1) α
    simpa only [β,normalExponentDegree,Finsupp.embDomain_eq_mapDomain,Finsupp.degree_eq_sum] using h
  have hw : Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β=normalExponentDegree β := by
    rw [Finsupp.weight_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i=Fin.last n
    · subst i
      simp [actualCoordinateWeight,he]
    · simp [actualCoordinateWeight,hi]
  change normalExponentDegree (β+Finsupp.single (Fin.last n)
    (Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β))=2*normalExponentDegree α
  have hadd : normalExponentDegree (β+Finsupp.single (Fin.last n)
      (Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β))=
      normalExponentDegree β+Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β := by
    simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]
  rw [hadd,hw,hd]
  omega

private theorem vertical_coefficient (F : MvPowerSeries (Fin n) ℂ) (α : Fin n→₀ℕ) :
    MvPowerSeries.coeff (verticalExponent α) (verticalFormal F)=MvPowerSeries.coeff α F := by
  change MvPowerSeries.coeff (actualMonomialBlowupExponent Set.univ (Fin.last n)
    (Finsupp.embDomain (Fin.castAddEmb 1) α))
      (actualFormalBlowup Set.univ (Fin.last n) (fun _=>0)
        (MvPowerSeries.rename (Fin.castAddEmb 1) F))=_
  rw [actualFormalBlowup_zero_coefficient,MvPowerSeries.coeff_embDomain_rename]

private theorem vertical_coefficient_preimage (F : MvPowerSeries (Fin n) ℂ)
    (γ : Fin (n+1)→₀ℕ) (hγ : MvPowerSeries.coeff γ (verticalFormal F)≠0) :
    ∃α : Fin n→₀ℕ,verticalExponent α=γ ∧ MvPowerSeries.coeff α F≠0 := by
  have himage : γ∈Set.range (actualMonomialBlowupExponent Set.univ (Fin.last n)) := by
    by_contra h
    exact hγ (actualFormalBlowup_zero_coefficient_outside_image Set.univ (Fin.last n) _ γ h)
  obtain ⟨β,hβ⟩:=himage
  have hc : MvPowerSeries.coeff β (MvPowerSeries.rename (Fin.castAddEmb 1) F)≠0 := by
    rw [←actualFormalBlowup_zero_coefficient Set.univ (Fin.last n),hβ]
    exact hγ
  have hbase : β∈Set.range (Finsupp.embDomain (Fin.castAddEmb 1)) := by
    by_contra h
    apply hc
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨α,hα⟩
    exact h ⟨α,by simpa only [Finsupp.embDomain_eq_mapDomain] using hα⟩
  obtain ⟨α,rfl⟩:=hbase
  exact ⟨α,hβ,by simpa only [MvPowerSeries.coeff_embDomain_rename] using hc⟩

private theorem vertical_coefficient_kernel (F : MvPowerSeries (Fin n) ℂ) (t : ℕ) :
    (∀γ : Fin (n+1)→₀ℕ,normalExponentDegree γ<t→MvPowerSeries.coeff γ (verticalFormal F)=0) ↔
      ∀α : Fin n→₀ℕ,2*normalExponentDegree α<t→MvPowerSeries.coeff α F=0 := by
  constructor
  · intro h α hα
    rw [←vertical_coefficient F α]
    apply h
    rw [vertical_degree]
    exact hα
  · intro h γ hγ
    by_contra hne
    obtain ⟨α,hα,hc⟩:=vertical_coefficient_preimage F γ hne
    rw [←hα,vertical_degree] at hγ
    exact hc (h α hγ)

private theorem actual_maximal_pow_iff (q : ℕ) (g : HolGerm (ComplexModel n)) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      ∀α : Fin n→₀ℕ,normalExponentDegree α<q→MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=0 := by
  let P (s : ℕ) (f : HolGerm (ComplexModel s)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) : Prop:=
    ∀h : HolGerm (ComplexModel s),h∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel s))^q ↔
      ∀α : Fin n→₀ℕ,normalExponentDegree α<q→MvPowerSeries.coeff α (f h)=0
  have hP : P (0+n) (originalTaylorAlgHom n):=fun h=>
    mem_original_maximal_pow_iff_formal_coefficients_zero n q h
  have transport {s : ℕ} (hs : s=n)
      (f : HolGerm (ComplexModel s)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) (h : P s f) :
      P n (cast (congrArg (fun j=>HolGerm (ComplexModel j)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) hs) f) := by
    subst s
    exact h
  exact transport (Nat.zero_add n) (originalTaylorAlgHom n) hP g

private theorem point_power_coeff_iff {m : ℕ} (F : ComplexModel m→ℂ)
    (hF : ∀ᶠw in 𝓝 (0 : ComplexModel m),DifferentiableAt ℂ F w) (q : ℕ) :
    (idealPow (pointIdeal m (0 : ComplexModel m)) q).mem 0 F ↔
      ∀α : Fin m→₀ℕ,normalExponentDegree α<q→
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom m (HolGerm.mk F hF))=0 :=
  (mem_maximalIdeal_pow_iff_point_power hF q).symm.trans (actual_maximal_pow_iff q _)

private theorem model_vertical_point_cuts (F : ComplexModel n→ℂ)
    (hF : ∀ᶠw in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F w)
    (G : ComplexModel (n+1)→ℂ)
    (hG : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),DifferentiableAt ℂ G w)
    (heq : HolGerm.mk G hG=actualAnalyticBlowupPullback Set.univ (Fin.last n) (fun _=>0)
      (tangentPullback n 1 (HolGerm.mk F hF))) (q : ℕ) :
    ((idealPow (pointIdeal (n+1) (0 : ComplexModel (n+1))) (2*q)).mem 0 G ↔
      (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 F) ∧
    ((idealPow (pointIdeal (n+1) (0 : ComplexModel (n+1))) (2*q+1)).mem 0 G ↔
      (idealPow (pointIdeal n (0 : ComplexModel n)) (q+1)).mem 0 F) := by
  have hTaylor : actualUnshiftedTaylorAlgHom (n+1) (HolGerm.mk G hG)=
      verticalFormal (actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF)) := by
    rw [heq]
    have hB:=DFunLike.congr_fun (actualTaylor_analyticBlowupPullback Set.univ (Fin.last n) (fun _=>0))
      (tangentPullback n 1 (HolGerm.mk F hF))
    have hT:=DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n 1) (HolGerm.mk F hF)
    simp only [AlgHom.comp_apply] at hB hT
    change actualUnshiftedTaylorAlgHom (n+1) (actualAnalyticBlowupPullback Set.univ (Fin.last n)
      (fun _=>0) (tangentPullback n 1 (HolGerm.mk F hF)))=_ at hB
    rw [hB]
    change _=actualFormalBlowup Set.univ (Fin.last n) (fun _=>0)
      (MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF)))
    rw [hT]
  constructor
  · rw [point_power_coeff_iff G hG,point_power_coeff_iff F hF,hTaylor,vertical_coefficient_kernel]
    apply forall_congr'
    intro α
    have h : 2*normalExponentDegree α<2*q ↔ normalExponentDegree α<q := by omega
    rw [h]
  · rw [point_power_coeff_iff G hG,point_power_coeff_iff F hF,hTaylor,vertical_coefficient_kernel]
    apply forall_congr'
    intro α
    have h : 2*normalExponentDegree α<2*q+1 ↔ normalExponentDegree α<q+1 := by omega
    rw [h]

private def baseMask (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

private theorem mask_old (S : Finset (Fin (n+1))) (w : ComplexModel (n+1)) (i : Fin n) :
    maskRetract S w (i.castAdd 1)=maskRetract (baseMask S) (tangentProjection n 1 w) i := by
  simp only [maskRetract_apply,tangentProjection_apply,baseMask,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem mask_last (S : Finset (Fin (n+1))) (hS : Fin.last n∉S) (w : ComplexModel (n+1)) :
    maskRetract S w (Fin.last n)=w (Fin.last n) := by rw [maskRetract_apply,if_neg hS]

private theorem mask_membership_of_old (S : Finset (Fin (n+1)))
    (v : ComplexModel (n+1)) (a : ComplexModel n)
    (hOld : ∀i : Fin n,v (i.castAdd 1)=a i) (hLast : v (Fin.last n)=0) :
    v∈coordSubspace S ↔ a∈coordSubspace (baseMask S) := by
  constructor
  · intro h i hi
    rw [←hOld i]
    exact h (i.castAdd 1) (by simpa only [baseMask,Finset.mem_filter,Finset.mem_univ,true_and] using hi)
  · intro h j hj
    by_cases he : j=Fin.last n
    · rw [he];exact hLast
    · have hjn : j.val<n := by
        have hneq : j.val≠n:=fun hh=>he (Fin.ext hh)
        have hjlt:=j.isLt
        omega
      let i : Fin n:=⟨j.val,hjn⟩
      have hij : i.castAdd 1=j:=Fin.ext rfl
      rw [←hij,hOld]
      apply h
      simpa only [baseMask,Finset.mem_filter,Finset.mem_univ,true_and,hij] using hj

private theorem flat_pair_geometry
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    (∀ᶠy in 𝓝 x,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (flatMap Φ) y) ∧
    (∀ᶠw in 𝓝 (0 : ComplexModel n),MDifferentiableAt
      𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (flatInv Φ) w) ∧
    (∀ᶠy in 𝓝 x,flatInv Φ (flatMap Φ y)=y) ∧
    (∀ᶠw in 𝓝 (0 : ComplexModel n),flatMap Φ (flatInv Φ w)=w) := by
  refine ⟨?_,?_,?_,?_⟩
  · filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    exact ExceptionalPushforwardAlong.mdifferentiableAt_flatMap hy
  · filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target h0)] with w hw
    exact ExceptionalPushforwardAlong.mdifferentiableAt_flatInv hsrc hw
  · filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy
    exact flatInv_flatMap hy
  · filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target h0)] with w hw
    exact flatMap_flatInv hw hsrc

private theorem chart_inverse_mdifferentiable {m : ℕ} {A : CMfd.{u} m} {C : Set A}
    [Fact (IsClosedSubmanifold m C)] (c : FlatChart m C) (h0c : (0 : ComplexModel m)∈c.target) :
    ∀ᶠw in 𝓝 (0 : ComplexModel m),MDifferentiableAt
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) c.invFun w := by
  have ht : c.homeo.target=c.target:=congrArg (fun e=>e.target)
    (atlasHomeo_toPartialEquiv c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  have hmax:=IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel m)) (n := ∞)
    (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
  filter_upwards [c.isOpen_target.mem_nhds h0c] with w hw
  have hwh : w∈c.homeo.target:=by rw [ht];exact hw
  exact (contMDiffAt_symm_of_mem_maximalAtlas hmax hwh).mdifferentiableAt (by simp)

private theorem vertical_scalar_cuts {N : Set X} {C : Set (projectionAmbient X)}
    [Fact (IsClosedSubmanifold (n+1) C)]
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) C)
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (hcp : c.y₀=(x,0)) (hck : c.k=0) (hcj : c.j=Fin.last n)
    (hOld : ∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1)
    (_hLast : ∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0)
    (h0c : (0 : ComplexModel (n+1))∈c.target)
    (hzp : blowupProj (n+1) C (c.invFun 0)=(x,0))
    (SN : Finset (Fin (n+1))) (hSN : Fin.last n∉SN)
    (hSourceN : ∀y∈flatDomain c.Φ,y∈(Prod.fst : projectionAmbient X→X) ⁻¹' N ↔
      c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN)
    {N' : Set (BlowupSpace (n+1) C)}
    (hTargetN : ∀u∈c.source,u∈N' ↔ c.toFun u∈coordSubspace SN)
    (hWs : ∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u)
    (f : X→ℂ) (hf : HolomorphicAt n f x) (q : ℕ) :
    (VanishesToOrderOn (n+1) N' (c.invFun 0) (2*q)
        (f ∘ Prod.fst ∘ blowupProj (n+1) C) ↔ VanishesToOrderOn n N x q f) ∧
    (VanishesToOrderOn (n+1) N' (c.invFun 0) (2*q+1)
        (f ∘ Prod.fst ∘ blowupProj (n+1) C) ↔ VanishesToOrderOn n N x (q+1) f) := by
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let z : Y:=c.invFun 0
  let π : Y→projectionAmbient X:=blowupProj (n+1) C
  have hzp' : π z=(x,0):=hzp
  let S:=baseMask SN
  have hz : z∈c.source:=c.map_target h0c
  have hWz : c.toFun z=0:=c.right_inv h0c
  have hχ:=chart_inverse_mdifferentiable c h0c
  have hψ : ∀ᶠu in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel (n+1))
      𝓘(ℂ,ComplexModel (n+1)) c.toFun u := by
    filter_upwards [c.isOpen_source.mem_nhds hz] with u hu
    exact (hWs u hu).mdifferentiableAt (by simp)
  have hLeft : ∀ᶠu in 𝓝 z,c.invFun (c.toFun u)=u := by
    filter_upwards [c.isOpen_source.mem_nhds hz] with u hu
    exact c.left_inv hu
  have hRight : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),c.toFun (c.invFun w)=w := by
    filter_upwards [c.isOpen_target.mem_nhds h0c] with w hw
    exact c.right_inv hw
  have hTargetFlat : ∀ᶠu in 𝓝 z,u∈N' ↔ c.toFun u∈coordSubspace SN := by
    filter_upwards [c.isOpen_source.mem_nhds hz] with u hu
    exact hTargetN u hu
  have hpD : ((x,0) : projectionAmbient X)∈flatDomain c.Φ := by
    rw [←hcp]
    exact mem_flatDomain_self c.Φ
  have hZero : Continuous (fun y : X=>((y,0) : projectionAmbient X)):=continuous_id.prodMk continuous_const
  have hBaseFlat : ∀ᶠy in 𝓝 x,y∈N ↔ flatMap Φ y∈coordSubspace S := by
    filter_upwards [hZero.continuousAt.eventually ((isOpen_flatDomain c.Φ).mem_nhds hpD)] with y hy
    have hN:=hSourceN (y,0) hy
    have hLast : c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ (y,0)) (Fin.last n)=0 :=
      _hLast (y,0)
    exact hN.trans (mask_membership_of_old SN _ (flatMap Φ y) (fun i=>hOld (y,0) i) hLast)
  obtain ⟨hBaseψ,hBaseχ,hBaseLeft,hBaseRight⟩:=flat_pair_geometry Φ hsrc h0
  let F : ComplexModel n→ℂ:=maskFlatten Φ S f
  have hFhol : HolomorphicAt n F 0:=maskFlatten_holomorphic Φ hsrc h0 S f hf
  have hF : ∀ᶠw in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F w:=hFhol.mono fun _ h=>h.differentiableAt
  have hR : Tendsto (maskRetract SN) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (maskRetract SN).continuous.tendsto 0
  let ν : ComplexModel (n+1)→Y:=fun w=>c.invFun (maskRetract SN w)
  have hν0 : ν 0=z := by change c.invFun (maskRetract SN 0)=c.invFun 0;rw [map_zero]
  have hν : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),MDifferentiableAt
      𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ν w := by
    filter_upwards [hR.eventually hχ] with w hw
    exact hw.comp w (maskRetract SN).differentiableAt.mdifferentiableAt
  have hνT : Tendsto ν (𝓝 0) (𝓝 z) := by
    have h:=hν.self_of_nhds.continuousAt.tendsto
    rwa [hν0] at h
  have hMap : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞
      ((Prod.fst : projectionAmbient X→X) ∘ π) :=
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)).comp contMDiff_blowupProj
  let f' : Y→ℂ:=f ∘ Prod.fst ∘ π
  have hf' : HolomorphicAt (n+1) f' z:=holomorphicAt_comp_map
    (φ := (Prod.fst : projectionAmbient X→X) ∘ π) (f := f)
    (Eventually.of_forall fun u=>hMap.contMDiffAt.mdifferentiableAt (by simp)) (by
      change HolomorphicAt n f (π z).1
      rw [hzp']
      exact hf)
  let G : ComplexModel (n+1)→ℂ:=fun w=>f' (ν w)
  have hGhol : HolomorphicAt (n+1) G 0:=holomorphicAt_comp_map
    (φ := ν) (f := f') hν (by rw [hν0];exact hf')
  have hG : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),DifferentiableAt ℂ G w:=hGhol.mono fun _ h=>h.differentiableAt
  have hbt : Tendsto (fun w=>(π (ν w)).1) (𝓝 0) (𝓝 x) := by
    have h:=hMap.continuous.continuousAt.tendsto.comp hνT
    change Tendsto (fun w=>(π (ν w)).1) (𝓝 0) (𝓝 (π z).1) at h
    rwa [hzp'] at h
  have hBaseDom : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),(π (ν w)).1∈flatDomain Φ:=
    hbt.eventually ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ))
  have hMaskTarget : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),maskRetract SN w∈c.target:=
    hR.eventually (c.isOpen_target.mem_nhds h0c)
  have heq : HolGerm.mk G hG=actualAnalyticBlowupPullback Set.univ (Fin.last n) (fun _=>0)
      (tangentPullback n 1 (HolGerm.mk F hF)) := by
    rw [tangentPullback,compAlgHom_mk,actualAnalyticBlowupPullback,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hBaseDom,hMaskTarget] with w hb hw
    have hu : ν w∈c.source:=c.map_target hw
    have hmon:=c.monomial_toFun hu
    have hCW : c.toFun (ν w)=maskRetract SN w:=c.right_inv hw
    rw [hck,hcj,hCW] at hmon
    have hvec : flatMap Φ (π (ν w)).1=
        maskRetract S (tangentProjection n 1 (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0) w)) := by
      ext i
      have hiNe : i.castAdd 1≠Fin.last n:=fun he=>last_not_cast ⟨i,he⟩
      calc
        flatMap Φ (π (ν w)).1 i=flatCoord c.Φ (i.castAdd 1) (π (ν w)) := (hOld _ i).symm
        _=monomial 0 (Fin.last n) (maskRetract SN w) (i.castAdd 1) :=
          (congrArg (fun v : ComplexModel (n+1)=>v (i.castAdd 1)) hmon).symm
        _=_ := by
          by_cases hi : i.castAdd 1∈SN
          · simp [monomial_apply,hiNe,maskRetract_apply,hi,S,baseMask]
          · simp [monomial_apply,hiNe,maskRetract_apply,hi,hSN,S,baseMask,tangentProjection_apply,
              actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,mul_comm]
    change f (π (ν w)).1=F (tangentProjection n 1 (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _=>0) w))
    rw [←flatInv_flatMap hb,hvec]
    rfl
  have hModel:=model_vertical_point_cuts F hF G hG heq q
  have hSource (t : ℕ):=mask_pair_point_power x (flatMap Φ) (flatInv Φ) h0 (flatInv_zero h0)
    hBaseψ hBaseχ hBaseLeft hBaseRight S hBaseFlat f t
  have hTarget (t : ℕ):=mask_pair_point_power z c.toFun c.invFun hWz rfl
    hψ hχ hLeft hRight SN hTargetFlat f' t
  exact ⟨(hTarget (2*q)).trans (hModel.1.trans (hSource q).symm),
    (hTarget (2*q+1)).trans (hModel.2.trans (hSource (q+1)).symm)⟩

/-- Ordinary original data derive ONE actual vertical chart and ALL scalar cuts;
no source order, leading term, selected point or future comparison is input. -/
theorem exists_projection_vertical_function_order {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    let p : projectionAmbient X:=(x,0)
    let C : Set (projectionAmbient X):={p}
    let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
    let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
    let π : Y → projectionAmbient X:=blowupProj (n+1) C
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) C) (SN : Finset (Fin (n+1)))
      (SE : Fin M.E.length → Finset (Fin (n+1))),
      (Φ.source⊆(chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
      (∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1) ∧
      (∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
      (∀y∈flatDomain c.Φ,y∈(projectionTest M).N ↔
        c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) ∧
      (∀i,x∈M.E.get i → ∀y∈flatDomain c.Φ,
        y∈(Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i ↔
          c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace (SE i)) ∧
      Fin.last n∉SN ∧ (∀i,Fin.last n∉SE i) ∧
      (0 : ComplexModel (n+1))∈c.target ∧
      let z:=c.invFun 0
      z∈c.source ∧ π z=p ∧ c.toFun z=0 ∧
      IsBlowupAlong (n+1) C π ∧
      z∈((projectionTest M).geoTransform C π).N ∧
      (∀u∈c.source,ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun u) ∧
      ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ (flatParameterLift c) ∧
      (∀u∈c.source,monomial 0 (Fin.last n) (c.toFun u)=
        c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ (π u))) ∧
      (∀u∈c.source,u∈((projectionTest M).geoTransform C π).N ↔ c.toFun u∈coordSubspace SN) ∧
      (∀i,x∈M.E.get i → ∀u∈c.source,
        u∈geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i) ↔
          c.toFun u∈coordSubspace (SE i)) ∧
      (∀u∈c.source,u∉geoStrictTransform π C (horizontal X)) ∧
      (∀u∈c.source,u∈π ⁻¹' C ↔ c.toFun u (Fin.last n)=0) ∧
      (∃O : Set Y,IsOpen O ∧ z∈O ∧ O⊆c.source ∧
        ∀i,x∉M.E.get i → ∀u∈O,
          u∉geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' M.E.get i)) ∧
      IsInvDomain (k+1) ((projectionTest M).geoTransform C π) ∧
      ((projectionTest M).geoTransform C π).d=M.d ∧
      ((projectionTest M).geoTransform C π).E=
        M.E.map (fun H=>geoStrictTransform π C ((Prod.fst : projectionAmbient X → X) ⁻¹' H)) ++
          [geoStrictTransform π C (horizontal X),π ⁻¹' C] ∧
      ((projectionTest M).geoTransform C π).E.length=M.E.length+2) ∧
      let z:=c.invFun 0
      ∀(f : X→ℂ),HolomorphicAt n f x → ∀q : ℕ,
        (VanishesToOrderOn (n+1) ((projectionTest M).geoTransform C π).N z (2*q)
          (f ∘ Prod.fst ∘ π) ↔ VanishesToOrderOn n M.N x q f) ∧
        (VanishesToOrderOn (n+1) ((projectionTest M).geoTransform C π).N z (2*q+1)
          (f ∘ Prod.fst ∘ π) ↔ VanishesToOrderOn n M.N x (q+1) f) := by
  dsimp only
  let p : projectionAmbient X:=(x,0)
  let C : Set (projectionAmbient X):={p}
  let _ : Fact (IsClosedSubmanifold (n+1) C):=⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X:=blowupProj (n+1) C
  obtain ⟨Φ,c,SN,SE,hGeometry⟩:=exists_projection_vertical_blowup_chart M hM x hx
  refine ⟨Φ,c,SN,SE,hGeometry,?_⟩
  rcases hGeometry with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,_hSourceE,hSN,_hSE,h0c,
    _hzSource,hzp,_hWz,_hπ,_hzN,hWs,_hInv,_hMon,hTargetN,_hTargetE,_hEmptyH,_hBorn,
    _hWindow,_hDom,_hd,_hEword,_hLength⟩
  intro f hf q
  exact vertical_scalar_cuts Φ c hΦs hΦ0 hcp hck hcj hOld hLast h0c hzp SN hSN
    hSourceN hTargetN hWs f hf q

end
end Hironaka.HironakaActualProjectionVerticalFunctionOrder
