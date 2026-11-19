import Hironaka.Resolution.HironakaActualTrueMarkCommonContact
import Hironaka.Resolution.HironakaActualTrueMarkCoefficientHistorySandwich
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualInheritedAnalyticBlockJacobian
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! Genuine whole weighted Taylor levels on an actual proper contact.
Blueprint FIRST: hironaka-actual-contact-weighted-coefficient-threshold.tex.
Extended-natural orders retain the zero lower ideal and infinity. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualContactWeightedCoefficientThreshold
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality
  HironakaActualInheritedAnalyticBlockJacobian HironakaRelativeNormalTaylorCoefficients
  HironakaActualFormalCoordinatePowerDivision
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  RelativePrincipalizationSpan BlowupTowers BlowupFlatCoordinates BlowupSNCTransform GiraudAlong TangentDirectionAlong
  DerivativeIdealAlong DerivativeIdealAlongCoherent RegularPointDimension RegularPatchPullback HadamardBridgeAlong
  RestrictedIdealWeight
  IdealWeightPowers GermIdealPullbackCalculus HomogenizedGlueing HomogenizedEquivalence
  HomogenizedIdealAlong CoefficientIdeal MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualOriginalFormalTaylor HironakaHolomorphicPointJets OrderTaylor HolomorphicTaylorTail GermIdealOrder
  HironakaActualCanonicalBlockJacobian
  HironakaActualTrueMarkCoefficientHistorySandwich HironakaActualOriginalCoefficientHistoryAlong
  HironakaActualTrueMarkCommonContact HironakaActualOriginalTrueMarkMaskCompanions
  StepOneValue StepOneValueMasked CompanionRebase CompanionReductionAlong CompanionOpen
  ResolutionInvariantSpec InvDomainTowerAlong BlowupTowerTransforms NonmonomialOrderLocal
  NonmonomialOrderTail MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaEmbeddedAnalytic
  ContactStageKept CoefficientIdealRestriction HomogenizedGlueingTower

/-- The whole coefficient-defined weighted ideal, in the genuine series ring. -/
def weightedLevel {n : ℕ} (w : Fin n→ℕ) (r : ℕ) : Ideal (MvPowerSeries (Fin n) ℂ) where
  carrier:={F | (r : ℕ∞)≤F.weightedOrder w}
  zero_mem':=by simp
  add_mem' hF hG:=(le_min hF hG).trans (MvPowerSeries.min_weightedOrder_le_add w)
  smul_mem' c F hF:=hF.trans ((show F.weightedOrder w≤c.weightedOrder w+F.weightedOrder w from le_add_self).trans
    (MvPowerSeries.le_weightedOrder_mul w))

private theorem mem_weightedLevel_iff {n : ℕ} (w : Fin n→ℕ) (r : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) :
    F∈weightedLevel w r ↔ ∀α : Fin n→₀ℕ,Finsupp.weight w α<r→MvPowerSeries.coeff α F=0 := by
  constructor
  · intro h α hα
    exact MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder w
      ((show (Finsupp.weight w α : ℕ∞)<r by exact_mod_cast hα).trans_le h)
  · exact MvPowerSeries.nat_le_weightedOrder w

private theorem weightedOrder_pow {n : ℕ} (w : Fin n→ℕ)
    (F : MvPowerSeries (Fin n) ℂ) : ∀p : ℕ,(F^p).weightedOrder w=(p : ℕ∞)*F.weightedOrder w
  | 0=>by simp
  | p+1=>by
    rw [pow_succ,MvPowerSeries.weightedOrder_mul,weightedOrder_pow w F p]
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

private theorem weighted_power_reflection {n : ℕ} (w : Fin n→ℕ)
    (F : MvPowerSeries (Fin n) ℂ) {p : ℕ} (hp : 0<p) (r : ℕ) :
    F^p∈weightedLevel w (p*r) ↔ F∈weightedLevel w r := by
  change ((p*r : ℕ) : ℕ∞)≤(F^p).weightedOrder w ↔ (r : ℕ∞)≤F.weightedOrder w
  rw [weightedOrder_pow]
  by_cases hTop : F.weightedOrder w=⊤
  · have hp0 : (p : ℕ∞)≠0:=by exact_mod_cast (Nat.ne_of_gt hp)
    simp only [hTop,ENat.mul_top hp0,le_top]
  · obtain ⟨s,hs⟩:=ENat.ne_top_iff_exists.mp hTop
    rw [←hs,←Nat.cast_mul]
    exact_mod_cast (show p*r≤p*s ↔ r≤s from
      ⟨fun h=>Nat.le_of_mul_le_mul_left h hp,fun h=>Nat.mul_le_mul_left p h⟩)

private theorem weighted_pderiv {n : ℕ} (w : Fin n→ℕ) (a r : ℕ)
    (hw : ∀i,w i≤a) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈weightedLevel w (r+a)) (i : Fin n) :
    MvPowerSeries.pderiv ℂ i F∈weightedLevel w r := by
  apply (mem_weightedLevel_iff w r _).mpr
  intro α hα
  rw [MvPowerSeries.coeff_pderiv]
  have hWeight : Finsupp.weight w (α+Finsupp.single i 1)<r+a := by
    rw [map_add,Finsupp.weight_single]
    simpa only [one_smul] using Nat.add_lt_add_of_lt_of_le hα (hw i)
  rw [(mem_weightedLevel_iff w (r+a) F).mp hF _ hWeight,zero_mul]

/-- The contact normal has weight a and every actual tangent variable weight b. -/
def normalWeight (d a b : ℕ) : Fin (d+1)→ℕ:=Fin.addCases (fun _=>b) (fun _=>a)

private theorem joined_weight (d a b : ℕ) (β : Fin d→₀ℕ) (γ : Fin 1→₀ℕ) :
    Finsupp.weight (normalWeight d a b) (actualJoinedExponent β γ)=
      b*normalExponentDegree β+a*normalExponentDegree γ := by
  rw [Finsupp.weight_eq_sum,Fin.sum_univ_add]
  simp [normalWeight,actualJoinedExponent,smul_eq_mul,normalExponentDegree,Finset.mul_sum,Nat.mul_comm]

private theorem const_weight (d b : ℕ) (β : Fin d→₀ℕ) :
    Finsupp.weight (fun _ : Fin d=>b) β=b*normalExponentDegree β := by
  rw [Finsupp.weight_eq_sum]
  simp only [smul_eq_mul,normalExponentDegree,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _=>Nat.mul_comm _ _

private theorem const_weightedOrder (d b : ℕ) (hb : 0<b) (F : MvPowerSeries (Fin d) ℂ) :
    F.weightedOrder (fun _=>b)=(b : ℕ∞)*F.order := by
  by_cases hF : F=0
  · subst F
    have hb0 : (b : ℕ∞)≠0:=by exact_mod_cast (Nat.ne_of_gt hb)
    simp [ENat.mul_top hb0]
  · have hFinite : F.order≠⊤:=fun h=>hF (MvPowerSeries.order_eq_top_iff.mp h)
    obtain ⟨s,hs⟩:=ENat.ne_top_iff_exists.mp hFinite
    have hLeast : F.weightedOrder (fun _=>b)≤((b*s : ℕ) : ℕ∞) := by
      have hNat : (F.order.toNat : ℕ∞)=F.order:=by rw [←hs];simp
      obtain ⟨β,hβ,hDegree⟩:=MvPowerSeries.exists_coeff_ne_zero_and_order hNat
      have he : normalExponentDegree β=s:=by
        simpa only [←hs,Nat.cast_inj,Finsupp.degree_eq_sum,normalExponentDegree] using hDegree
      have hLe:=MvPowerSeries.weightedOrder_le (fun _ : Fin d=>b) hβ
      simpa only [const_weight,he] using hLe
    have hGreat : ((b*s : ℕ) : ℕ∞)≤F.weightedOrder (fun _=>b) := by
      apply MvPowerSeries.nat_le_weightedOrder
      intro β hβ
      rw [const_weight] at hβ
      have hDeg : normalExponentDegree β<s:=Nat.lt_of_mul_lt_mul_left hβ
      apply MvPowerSeries.coeff_of_lt_order
      rw [←hs]
      simpa only [Finsupp.degree_eq_sum,normalExponentDegree,Nat.cast_lt] using hDeg
    rw [←hs,←Nat.cast_mul]
    exact hLeast.antisymm hGreat

private theorem formal_normal_weighted_iff (d a b m : ℕ) (hb : 0<b)
    (F : MvPowerSeries (Fin (d+1)) ℂ) :
    F∈weightedLevel (normalWeight d a b) (m*a) ↔
      ∀γ : Fin 1→₀ℕ,normalExponentDegree γ<m→
        (((m-normalExponentDegree γ)*a : ℕ) : ℕ∞)≤
          (b : ℕ∞)*(actualFormalNormalCoefficient F γ).order := by
  constructor
  · intro h γ hγ
    rw [←const_weightedOrder d b hb]
    apply MvPowerSeries.nat_le_weightedOrder
    intro β hβ
    change MvPowerSeries.coeff (actualJoinedExponent β γ) F=0
    apply (mem_weightedLevel_iff _ _ F).mp h
    rw [joined_weight]
    rw [const_weight] at hβ
    have hAdd : (m-normalExponentDegree γ)*a+normalExponentDegree γ*a=m*a:=by
      rw [←Nat.add_mul,Nat.sub_add_cancel (by omega)]
    nlinarith
  · intro h
    apply (mem_weightedLevel_iff _ _ F).mpr
    intro α hα
    let β:=actualTangentExponent α
    let γ:=actualNormalExponent α
    have hSplit : actualJoinedExponent β γ=α:=actualJoinedExponent_split α
    have hWeight : b*normalExponentDegree β+a*normalExponentDegree γ<m*a:=by
      rw [←joined_weight,hSplit]
      exact hα
    have hγ : normalExponentDegree γ<m:=by
      by_contra hle
      have hGe:=Nat.mul_le_mul_left a (Nat.le_of_not_gt hle)
      nlinarith
    have hc:=h γ hγ
    rw [←const_weightedOrder d b hb] at hc
    have hβ : Finsupp.weight (fun _ : Fin d=>b) β<(m-normalExponentDegree γ)*a:=by
      rw [const_weight]
      have hAdd : (m-normalExponentDegree γ)*a+normalExponentDegree γ*a=m*a:=by
        rw [←Nat.add_mul,Nat.sub_add_cancel (by omega)]
      nlinarith
    have hz:=MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder (fun _ : Fin d=>b)
      ((show (Finsupp.weight (fun _ : Fin d=>b) β : ℕ∞)<((m-normalExponentDegree γ)*a : ℕ) by exact_mod_cast hβ).trans_le hc)
    change MvPowerSeries.coeff (actualJoinedExponent β γ) F=0 at hz
    rwa [hSplit] at hz

/-- Actual analytic normal coefficient germs, extracted from the WHOLE
original germ, detect its genuine weighted Taylor ideal membership. -/
theorem weighted_normal_coefficient_iff (d a b m : ℕ) (hb : 0<b)
    (g : HolGerm (ComplexModel (d+1))) :
    actualUnshiftedTaylorAlgHom (d+1) g∈weightedLevel (normalWeight d a b) (m*a) ↔
      ∀γ : Fin 1→₀ℕ,normalExponentDegree γ<m→
        (((m-normalExponentDegree γ)*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
          (actualUnshiftedTaylorAlgHom d (actualNormalAnalyticCoefficientGerm d 1 g γ)).order := by
  rw [formal_normal_weighted_iff d a b m hb]
  apply forall_congr'
  intro γ
  rw [actualFormalNormalCoefficient_actualTaylor]

variable {n : ℕ} {X : CMfd.{u} n}

private theorem contact_coordinates {N V : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) {m : ℕ} {w : X→ℂ}
    (hw : IsTangentDirectionAlong N A m V w) (z : X)
    (hz : z∈N ∧ z∈V ∧ w z=0) :
    ∃k : ℕ,0<k ∧ k≤n ∧ ∃l : Fin n,l.val+1=k ∧
      ∃Θ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z),
        Θ.source⊆(chartAt (ComplexModel n) z).target ∧
        Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧
        ∀y∈flatDomain Θ,y∈V ∧
          (y∈N ↔ flatMap Θ y∈complexCoordinatePlane n k) ∧
          flatCoord Θ l y=w y ∧
          (y∈N ∧ w y=0 ↔ flatMap Θ y∈complexCoordinatePlane n (k-1)) := by
  obtain ⟨k,hk⟩:=hN.2 z hz.1
  obtain ⟨hkn,_hzN,Φ,hSrc,h0,hFlat⟩:=hk
  change LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z) at Φ
  have hHol : ∀y∈V,HolomorphicAt n w y:=fun y hy=>
    holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hA hf) (m-1) y w (hw.mem y hy)
  obtain ⟨e,ξ,hξ,hNonzero⟩:=hw.multiplicity_one z hz.2.1 hz.2.2
  obtain ⟨j,hjk,hjNonzero⟩:=exists_flatPartial_ne_zero hSrc hFlat
    (mem_flatDomain_self Φ) hz.1 (hHol z hz.2.1) hξ hNonzero
  have hkPos : 0<k:=by omega
  let l : Fin n:=⟨k-1,by omega⟩
  have hl : l.val+1=k:=by dsimp [l];omega
  let O:=V∩flatDomain Φ
  have hO : IsOpen O:=hw.isOpen.inter (isOpen_flatDomain Φ)
  have hzO : z∈O:=⟨hz.2.1,mem_flatDomain_self Φ⟩
  have hW : ∀y∈O,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (contactCoords Φ j l w) y:=by
    intro y hy
    exact contMDiffAt_of_eventually_mdifferentiableAt
      (eventually_of_mem (hO.mem_nhds hy) fun p hp=>mdifferentiableAt_contactCoords
        j l hp.2 (hHol p hp.1))
  have hW0 : contactCoords Φ j l w z=0:=by
    ext i
    change contactCoords Φ j l w z i=(0 : ℂ)
    rw [contactCoords_apply]
    split_ifs
    · exact hz.2.2
    · change flatMap Φ z (Equiv.swap j l i)=0
      rw [show flatMap Φ z=0 from h0]
      rfl
  obtain ⟨Θ,hΘSrc,hΘ0,hΘ⟩:=exists_recentred_coords hO hW hzO
    (injective_fderiv_contactCoords hSrc (hHol z hz.2.1) hjNonzero)
  refine ⟨k,hkPos,hkn,l,hl,Θ,hΘSrc,hΘ0,?_⟩
  intro y hy
  obtain ⟨hyO,hEq⟩:=hΘ hy.1 hy.2
  change flatMap Θ y=contactCoords Φ j l w y-contactCoords Φ j l w z at hEq
  rw [hW0,sub_zero] at hEq
  have hNormal : ∀i : Fin n,k ≤ i.val → contactCoords Φ j l w y i=flatMap Φ y i:=by
    intro i hi
    rw [contactCoords_apply,if_neg (by intro he;subst i;omega),
      Equiv.swap_apply_of_ne_of_ne (by intro he;subst i;omega) (by intro he;subst i;omega)]
  have hPlane : contactCoords Φ j l w y∈complexCoordinatePlane n k ↔
      flatMap Φ y∈complexCoordinatePlane n k:=by
    constructor
    · intro h i hi
      simpa only [hNormal i hi] using h i hi
    · intro h i hi
      rw [hNormal i hi]
      exact h i hi
  refine ⟨hyO.1,?_,?_,?_⟩
  · rw [hEq,hPlane]
    exact (hFlat hyO.2.1 hyO.2.2)
  · change flatMap Θ y l=w y
    rw [hEq,contactCoords_apply,if_pos rfl]
  · rw [hEq]
    exact (contactCoords_mem_plane_iff hFlat hjk hl w hyO.2).symm

/-- Genuine Taylor series of the actual native function restricted to a
proper carrier by its actual holomorphic coordinate retraction. -/
def flattenedTaylor {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (f : X→ℂ) (hf : HolomorphicAt n f z) : MvPowerSeries (Fin n) ℂ:=
  actualUnshiftedTaylorAlgHom n (HolGerm.mk (flatten Φ k f)
    (eventually_differentiableAt_flatten hSrc h0 k hf))

/-- Whole native ideal weighted membership, using EVERY actual germ member.
No comparison law or desired weighted relation is part of this definition. -/
def WeightedAlongAt {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (A : GermIdeal n X) (r : ℕ) : Prop:=
  ∀f (hf : HolomorphicAt n f z),A.mem z f→flattenedTaylor Φ hSrc h0 k f hf∈weightedLevel w r

private theorem flattenedTaylor_congr {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    {f g : X→ℂ} (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z)
    (h : f=ᶠ[𝓝 z]g) : flattenedTaylor Φ hSrc h0 k f hf=flattenedTaylor Φ hSrc h0 k g hg := by
  apply congrArg (actualUnshiftedTaylorAlgHom n)
  apply HolGerm.mk_eq_mk_iff.mpr
  exact (tendsto_flatInv_planeRetract hSrc h0 k).eventually h

private theorem flattenedTaylor_mul {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (f g : X→ℂ) (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z) :
    flattenedTaylor Φ hSrc h0 k (f*g) (hf.mul hg)=
      flattenedTaylor Φ hSrc h0 k f hf*flattenedTaylor Φ hSrc h0 k g hg := by
  unfold flattenedTaylor
  change actualUnshiftedTaylorAlgHom n (HolGerm.mk
    (fun y=>flatten Φ k f y*flatten Φ k g y) _)=_
  rw [HolGerm.mk_mul _ _
    (eventually_differentiableAt_flatten hSrc h0 k hf)
    (eventually_differentiableAt_flatten hSrc h0 k hg),map_mul]

private theorem flattenedTaylor_sum {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k q : ℕ)
    (f : Fin q→X→ℂ) (hf : ∀i,HolomorphicAt n (f i) z) :
    flattenedTaylor Φ hSrc h0 k (fun y=>∑i,f i y) (HolomorphicAt.sum _ fun i _=>hf i)=
      ∑i,flattenedTaylor Φ hSrc h0 k (f i) (hf i) := by
  unfold flattenedTaylor
  change actualUnshiftedTaylorAlgHom n (HolGerm.mk (fun y=>∑i,flatten Φ k (f i) y) _)=_
  rw [HolGerm.mk_sum Finset.univ (fun i=>flatten Φ k (f i))
    (fun i=>eventually_differentiableAt_flatten hSrc h0 k (hf i)),map_sum]

private theorem weighted_span {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r : ℕ) {S : (X→ℂ)→Prop}
    (hS : ∀s,S s→∃hs : HolomorphicAt n s z,flattenedTaylor Φ hSrc h0 k s hs∈weightedLevel w r)
    {f : X→ℂ} (hf : HolomorphicAt n f z) (hSpan : IsInSpanAt (n:=n) S z f) :
    flattenedTaylor Φ hSrc h0 k f hf∈weightedLevel w r := by
  obtain ⟨_hf,q,s,c,hs,hc,hEq⟩:=hSpan
  choose hsh hsw using fun i=>hS (s i) (hs i)
  have hTerms : ∀i,HolomorphicAt n (c i*s i) z:=fun i=>(hc i).mul (hsh i)
  have hSum : HolomorphicAt n (fun y=>∑i,c i y*s i y) z:=HolomorphicAt.sum _ fun i _=>hTerms i
  rw [flattenedTaylor_congr Φ hSrc h0 k hf hSum hEq]
  change flattenedTaylor Φ hSrc h0 k (fun y=>∑i,(c i*s i) y) _∈weightedLevel w r
  rw [flattenedTaylor_sum Φ hSrc h0 k q (fun i=>c i*s i) hTerms]
  apply Ideal.sum_mem
  intro i _
  rw [flattenedTaylor_mul Φ hSrc h0 k (c i) (s i) (hc i) (hsh i)]
  exact Ideal.mul_mem_left _ _ (hsw i)

private theorem flattenedTaylor_zero_of_flatten_zero {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (f : X→ℂ) (hf : HolomorphicAt n f z)
    (h : flatten Φ k f=ᶠ[𝓝 (0 : ComplexModel n)]0) :
    flattenedTaylor Φ hSrc h0 k f hf=0 := by
  unfold flattenedTaylor
  have he : HolGerm.mk (flatten Φ k f) (eventually_differentiableAt_flatten hSrc h0 k hf)=0:=by
    rw [←HolGerm.mk_zero]
    exact HolGerm.mk_eq_mk_iff.mpr h
  rw [he,map_zero]

private theorem flattenedTaylor_zero {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ) :
    flattenedTaylor Φ hSrc h0 k 0 (holomorphicAt_const 0)=0 :=
  flattenedTaylor_zero_of_flatten_zero Φ hSrc h0 k 0 (holomorphicAt_const 0)
    (Eventually.of_forall fun _=>rfl)

private theorem flattenedTaylor_normal_coord_zero {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (j : Fin n) (hj : k≤j.val) :
    flattenedTaylor Φ hSrc h0 k (flatCoord Φ j)
      (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ))=0 := by
  apply flattenedTaylor_zero_of_flatten_zero
  filter_upwards [eventually_planeRetract_mem_target hSrc h0 k] with y hy
  change flatMap Φ (flatInv Φ (planeRetract k y)) j=0
  rw [flatMap_flatInv hy hSrc]
  exact planeRetract_mem k y j hj

private theorem flattenedTaylor_flatPartial {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (f : X→ℂ) (hf : HolomorphicAt n f z) (j : Fin n) (hj : j.val<k) :
    flattenedTaylor Φ hSrc h0 k (flatPartial Φ j f)
      (holomorphicAt_flatPartial j (mem_flatDomain_self Φ) hf)=
        MvPowerSeries.pderiv ℂ j (flattenedTaylor Φ hSrc h0 k f hf) := by
  have hPlane : planeRetract k (EuclideanSpace.single j (1 : ℂ))=EuclideanSpace.single j 1:=
    planeRetract_of_mem (single_mem_complexCoordinatePlane hj)
  have hEq:=dirDeriv_flatten_eventuallyEq hSrc h0 (k:=k) hf (EuclideanSpace.single j 1)
  rw [hPlane] at hEq
  have hGerm : actualAnalyticCoordinateDerivative j
      (HolGerm.mk (flatten Φ k f) (eventually_differentiableAt_flatten hSrc h0 k hf))=
      HolGerm.mk (flatten Φ k (flatPartial Φ j f))
        (eventually_differentiableAt_flatten hSrc h0 k
          (holomorphicAt_flatPartial j (mem_flatDomain_self Φ) hf)) := by
    rw [actualAnalyticCoordinateDerivative,iteratedDerivativeGerm_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact hEq
  have h:=actualTaylor_actualAnalyticCoordinateDerivative j
    (HolGerm.mk (flatten Φ k f) (eventually_differentiableAt_flatten hSrc h0 k hf))
  rw [hGerm] at h
  exact h

private theorem weighted_along_deriv {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (w : Fin n→ℕ) (a r : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent)
    (hBound : WeightedAlongAt Φ hSrc h0 k w A (r+a)) :
    WeightedAlongAt Φ hSrc h0 k w (derivIdealAlong N A) r := by
  obtain ⟨U,hU,hzU,q,s,hs,hGen⟩:=hA z
  have hsh : ∀i,HolomorphicAt n (s i) z:=fun i=>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hzU
  have hsm : ∀i,A.mem z (s i):=fun i=>(hGen z hzU _).mpr
    (InvertibleIdealQuotient.isInSpanAt_self ⟨i,rfl⟩ (hsh i))
  let O:=U∩flatDomain Φ
  have hO : IsOpen O:=hU.inter (isOpen_flatDomain Φ)
  have hzO : z∈O:=⟨hzU,mem_flatDomain_self Φ⟩
  have hDeriv (g : X→ℂ) : (derivIdealAlong N A).mem z g ↔
      IsInSpanAt (n:=n) (·∈range (derivFamilyAlong Φ k s)) z g :=
    derivIdealAlong_mem_iff_of_generators hSrc hFlat hO inter_subset_right
      (fun i=> (hs i).mono inter_subset_left) (fun y hy=>hGen y hy.1) hzO g
  intro f hf hD
  apply weighted_span Φ hSrc h0 k w r (hf:=hf) (hSpan:=(hDeriv f).mp hD)
  let P : (X→ℂ)→Prop:=fun g=>∃hg : HolomorphicAt n g z,
    flattenedTaylor Φ hSrc h0 k g hg∈weightedLevel w r
  change ∀g,g∈range (derivFamilyAlong Φ k s)→P g
  rintro g ⟨c,rfl⟩
  rcases c with i | j | ij
  · refine ⟨hsh i,?_⟩
    have h:=hBound (s i) (hsh i) (hsm i)
    exact (show (r : ℕ∞)≤r+a by exact_mod_cast (Nat.le_add_right r a)).trans h
  · change P (if k≤j.val then flatCoord Φ j else fun _=>0)
    by_cases hj : k≤j.val
    · rw [if_pos hj]
      exact ⟨holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ),by
        rw [flattenedTaylor_normal_coord_zero Φ hSrc h0 k j hj]
        exact Ideal.zero_mem _⟩
    · rw [if_neg hj]
      exact ⟨holomorphicAt_const 0,by
        rw [flattenedTaylor_zero_of_flatten_zero Φ hSrc h0 k (fun _=>0)
          (holomorphicAt_const 0) (Eventually.of_forall fun _=>rfl)]
        exact Ideal.zero_mem _⟩
  · change P (if ij.2.val<k then flatPartial Φ ij.2 (s ij.1) else fun _=>0)
    by_cases hj : ij.2.val<k
    · rw [if_pos hj]
      exact ⟨holomorphicAt_flatPartial ij.2 (mem_flatDomain_self Φ) (hsh ij.1),by
        rw [flattenedTaylor_flatPartial Φ hSrc h0 k (s ij.1) (hsh ij.1) ij.2 hj]
        exact weighted_pderiv w a r hWeights _ (hBound _ (hsh ij.1) (hsm ij.1)) ij.2⟩
    · rw [if_neg hj]
      exact ⟨holomorphicAt_const 0,by
        rw [flattenedTaylor_zero_of_flatten_zero Φ hSrc h0 k (fun _=>0)
          (holomorphicAt_const 0) (Eventually.of_forall fun _=>rfl)]
        exact Ideal.zero_mem _⟩

/-- Literal chosen contact weight, on the SAME actual carrier coordinates. -/
def contactWeight (l : Fin n) (a b : ℕ) : Fin n→ℕ:=fun j=>if j=l then a else b

/-- A genuine actual contact supplies its own proper-carrier coordinates,
and ALL native along derivatives satisfy the whole weighted loss bound. -/
theorem actual_contact_weighted_derivatives {N V : Set X} {A : GermIdeal n X}
    (hA : A.IsCoherent) (hN : IsClosedSubmanifold n N) {m : ℕ} {w : X→ℂ}
    (hw : IsTangentDirectionAlong N A m V w) (z : X)
    (hz : z∈N ∧ z∈V ∧ w z=0) :
    ∃k : ℕ,0<k ∧ k≤n ∧ ∃l : Fin n,l.val+1=k ∧
      ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
        (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
        (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
        (∀y∈flatDomain Φ,y∈V ∧
          (y∈N ↔ flatMap Φ y∈complexCoordinatePlane n k) ∧
          flatCoord Φ l y=w y ∧
          (y∈N ∧ w y=0 ↔ flatMap Φ y∈complexCoordinatePlane n (k-1))) ∧
        ∀a b : ℕ,0<b→b≤a→∀r : ℕ,
          WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) A (r+a)→
          WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) (derivIdealAlong N A) r := by
  obtain ⟨k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords⟩:=contact_coordinates hA hN hw z hz
  refine ⟨k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords,?_⟩
  intro a b _hb hba r hBound
  apply weighted_along_deriv Φ hSrc h0 k (fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1)
    (contactWeight l a b) a r _ hA hBound
  intro i
  dsimp only [contactWeight]
  split_ifs
  · exact le_rfl
  · exact hba

private def planeEmbedding (k : ℕ) : {i : Fin n // i.val<k} ↪ Fin n:=
  ⟨Subtype.val,Subtype.val_injective⟩

private def formalPlaneProject (k : ℕ) :
    MvPowerSeries (Fin n) ℂ→ₐ[ℂ]MvPowerSeries (Fin n) ℂ:=
  (MvPowerSeries.rename (planeEmbedding k)).comp (MvPowerSeries.killCompl (planeEmbedding k))

private theorem formalPlaneProject_X (k : ℕ) (j : Fin n) :
    formalPlaneProject k (MvPowerSeries.X j)=if j.val<k then MvPowerSeries.X j else 0 := by
  change MvPowerSeries.rename (planeEmbedding k)
    (MvPowerSeries.killCompl (planeEmbedding k) (MvPowerSeries.X j))=_
  by_cases hj : j.val<k
  · rw [if_pos hj]
    let i : {i : Fin n // i.val<k}:=⟨j,hj⟩
    change MvPowerSeries.rename (planeEmbedding k)
      (MvPowerSeries.killCompl (planeEmbedding k) (MvPowerSeries.X (planeEmbedding k i)))=_
    rw [MvPowerSeries.killCompl_X,MvPowerSeries.rename_X]
    rfl
  · rw [if_neg hj,MvPowerSeries.killCompl_X_eq_zero (by
      rintro ⟨i,hi⟩
      exact hj (hi ▸ i.property)),map_zero]

private theorem coeff_formalPlaneProject (k : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (α : Fin n→₀ℕ) :
    MvPowerSeries.coeff α (formalPlaneProject k F)=
      if (↑α.support : Set (Fin n))⊆range (planeEmbedding k)
      then MvPowerSeries.coeff α F else 0 := by
  change MvPowerSeries.coeff α (MvPowerSeries.rename (planeEmbedding k)
    (MvPowerSeries.killCompl (planeEmbedding k) F))=_
  by_cases hSub : (↑α.support : Set (Fin n))⊆range (planeEmbedding k)
  · rw [if_pos hSub]
    obtain ⟨β,hβ⟩:=(Finsupp.mem_range_embDomain_iff _ _).mpr hSub
    rw [←hβ,MvPowerSeries.coeff_embDomain_rename,MvPowerSeries.coeff_killCompl]
  · rw [if_neg hSub]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨β,hβ⟩
    apply hSub
    apply (Finsupp.mem_range_embDomain_iff _ _).mp
    exact ⟨β,by simpa only [Finsupp.embDomain_eq_mapDomain] using hβ⟩

private def germPlaneProject (k : ℕ) :
    HolGerm (ComplexModel n)→ₐ[ℂ]HolGerm (ComplexModel n):=
  compAlgHom (planeRetract k)
    (Eventually.of_forall fun _=>(planeRetract k).differentiableAt) (map_zero _)

private theorem germPlaneProject_coordinate (k : ℕ) (j : Fin n) :
    germPlaneProject k (coordinateGerm j)=if j.val<k then coordinateGerm j else 0 := by
  unfold germPlaneProject coordinateGerm
  rw [compAlgHom_mk]
  by_cases hj : j.val<k
  · rw [if_pos hj]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun y=>by
      change planeRetract k y j=y j
      rw [planeRetract_apply,if_pos hj]
  · rw [if_neg hj,←HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun y=>by
      change planeRetract k y j=(0 : ℂ)
      rw [planeRetract_apply,if_neg hj]

/-- Actual coordinate identities and genuine Taylor separation derive this
whole functional-calculus identity, rather than assuming it. -/
private theorem actualTaylor_planeProject (k : ℕ) :
    (actualUnshiftedTaylorAlgHom n).comp (germPlaneProject k)=
      (formalPlaneProject k).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro j
    change actualUnshiftedTaylorAlgHom n (germPlaneProject k (coordinateGerm j))=
      formalPlaneProject k (actualUnshiftedTaylorAlgHom n (coordinateGerm j))
    rw [germPlaneProject_coordinate,actualUnshiftedTaylor_coordinate,formalPlaneProject_X]
    split_ifs <;> simp only [actualUnshiftedTaylor_coordinate,map_zero]
  · intro j
    change actualUnshiftedTaylorAlgHom n (germPlaneProject k (coordinateGerm j))∈
      actualFormalCoordinateIdeal n univ
    rw [germPlaneProject_coordinate]
    split_ifs with hj
    · rw [actualUnshiftedTaylor_coordinate]
      exact Ideal.subset_span ⟨j,mem_univ _,rfl⟩
    · rw [map_zero]
      exact Ideal.zero_mem _

private theorem flattenedTaylor_congr_on {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    {f g : X→ℂ} (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z)
    (h : ∀ᶠy in 𝓝 z,y∈N→f y=g y) :
    flattenedTaylor Φ hSrc h0 k f hf=flattenedTaylor Φ hSrc h0 k g hg := by
  apply congrArg (actualUnshiftedTaylorAlgHom n)
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [eventually_planeRetract_mem_target hSrc h0 k,
    (tendsto_flatInv_planeRetract hSrc h0 k).eventually h] with y hy he
  exact he (flatInv_mem hSrc hFlat hy (planeRetract_mem k y))

private theorem weighted_span_on {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (w : Fin n→ℕ) (r : ℕ) {S : (X→ℂ)→Prop}
    (hS : ∀s,S s→∃hs : HolomorphicAt n s z,flattenedTaylor Φ hSrc h0 k s hs∈weightedLevel w r)
    {f : X→ℂ} (hf : HolomorphicAt n f z) (hSpan : IsInSpanOnAt (n:=n) N S z f) :
    flattenedTaylor Φ hSrc h0 k f hf∈weightedLevel w r := by
  obtain ⟨q,s,c,hs,hc,hEq⟩:=hSpan
  choose hsh hsw using fun i=>hS (s i) (hs i)
  have hTerms : ∀i,HolomorphicAt n (c i*s i) z:=fun i=>(hc i).mul (hsh i)
  have hSum : HolomorphicAt n (fun y=>∑i,c i y*s i y) z:=HolomorphicAt.sum _ fun i _=>hTerms i
  rw [flattenedTaylor_congr_on Φ hSrc h0 k hFlat hf hSum hEq]
  change flattenedTaylor Φ hSrc h0 k (fun y=>∑i,(c i*s i) y) _∈weightedLevel w r
  rw [flattenedTaylor_sum Φ hSrc h0 k q (fun i=>c i*s i) hTerms]
  apply Ideal.sum_mem
  intro i _
  rw [flattenedTaylor_mul Φ hSrc h0 k (c i) (s i) (hc i) (hsh i)]
  exact Ideal.mul_mem_left _ _ (hsw i)

private theorem weighted_restrictLe {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (w : Fin n→ℕ) (r : ℕ) {A B : GermIdeal n X} (hB : B.IsCoherent)
    (hLe : RestrictLe N A B) (hBound : WeightedAlongAt Φ hSrc h0 k w B r) :
    WeightedAlongAt Φ hSrc h0 k w A r := by
  intro f hf hAf
  apply weighted_span_on Φ hSrc h0 k hFlat w r (hf:=hf)
    (hSpan:=hLe z (mem_of_flat hSrc h0 hFlat) f hAf)
  intro g hg
  have hh:=GermIdeal.IsCoherent.holomorphicAt_mem hB hg
  exact ⟨hh,hBound g hh hg⟩

private theorem weighted_product {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r s : ℕ) {A B : GermIdeal n X} (hA : A.IsCoherent) (hB : B.IsCoherent)
    (hABound : WeightedAlongAt Φ hSrc h0 k w A r) (hBBound : WeightedAlongAt Φ hSrc h0 k w B s) :
    WeightedAlongAt Φ hSrc h0 k w (A.mul B) (r+s) := by
  intro f hf hAB
  apply weighted_span Φ hSrc h0 k w (r+s) (hf:=hf)
    (hSpan:=InvertibleIdealQuotient.mem_mul_iff.mp hAB)
  rintro g ⟨g₁,g₂,hg₁,hg₂,rfl⟩
  have hh₁:=GermIdeal.IsCoherent.holomorphicAt_mem hA hg₁
  have hh₂:=GermIdeal.IsCoherent.holomorphicAt_mem hB hg₂
  refine ⟨hh₁.mul hh₂,?_⟩
  rw [flattenedTaylor_mul Φ hSrc h0 k g₁ g₂ hh₁ hh₂]
  exact (show ((r+s : ℕ) : ℕ∞)≤
    (flattenedTaylor Φ hSrc h0 k g₁ hh₁).weightedOrder w+
      (flattenedTaylor Φ hSrc h0 k g₂ hh₂).weightedOrder w by
      rw [Nat.cast_add]
      exact add_le_add (hABound g₁ hh₁ hg₁) (hBBound g₂ hh₂ hg₂)).trans
        (MvPowerSeries.le_weightedOrder_mul w)

private theorem flattenedTaylor_pow {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (f : X→ℂ) (hf : HolomorphicAt n f z) (p : ℕ)
    (hfPow : HolomorphicAt n (fun y=>f y^p) z) :
    flattenedTaylor Φ hSrc h0 k (fun y=>f y^p) hfPow=
      (flattenedTaylor Φ hSrc h0 k f hf)^p := by
  unfold flattenedTaylor
  change actualUnshiftedTaylorAlgHom n (HolGerm.mk (fun y=>(flatten Φ k f y)^p) _)=_
  rw [HolGerm.mk_pow _ (eventually_differentiableAt_flatten hSrc h0 k hf) p,map_pow]

private theorem weighted_idealPow {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r : ℕ) {A : GermIdeal n X} (hA : A.IsCoherent)
    (hBound : WeightedAlongAt Φ hSrc h0 k w A r) :
    ∀p : ℕ,WeightedAlongAt Φ hSrc h0 k w (idealPow A p) (p*r)
  | 0=>by
    intro f hf _h
    change ((0*r : ℕ) : ℕ∞)≤_
    rw [Nat.zero_mul,Nat.cast_zero]
    exact bot_le
  | p+1=>by
    have h:=weighted_product Φ hSrc h0 k w (p*r) r (isCoherent_idealPow hA p) hA
      (weighted_idealPow Φ hSrc h0 k w r hA hBound p) hBound
    simpa only [idealPow_succ,Nat.succ_mul] using h

private theorem weighted_idealPow_reflect {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r : ℕ) {A : GermIdeal n X} (hA : A.IsCoherent)
    {p : ℕ} (hp : 0<p) (hBound : WeightedAlongAt Φ hSrc h0 k w (idealPow A p) (p*r)) :
    WeightedAlongAt Φ hSrc h0 k w A r := by
  intro f hf hAf
  have hPower:=OrderMultiplicativity.pow_mem_idealPow hAf hf p
  have hHol:=GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hA p) hPower
  have h:=hBound (fun y=>f y^p) hHol hPower
  rw [flattenedTaylor_pow Φ hSrc h0 k f hf p hHol] at h
  exact (weighted_power_reflection w _ hp r).mp h

private theorem weighted_finSum {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r q : ℕ) (A : ℕ→GermIdeal n X)
    (hA : ∀i<q,(A i).IsCoherent)
    (hBound : ∀i<q,WeightedAlongAt Φ hSrc h0 k w (A i) r) :
    WeightedAlongAt Φ hSrc h0 k w (finSumIdeal A q) r := by
  intro f hf hSum
  apply weighted_span Φ hSrc h0 k w r (hf:=hf)
    (hSpan:=show IsInSpanAt (n:=n) (fun g=>∃i,i<q ∧ (A i).mem z g) z f from hSum)
  rintro g ⟨i,hi,hg⟩
  have hh:=GermIdeal.IsCoherent.holomorphicAt_mem (hA i hi) hg
  exact ⟨hh,hBound i hi g hh hg⟩

private theorem weighted_mono {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) (r : ℕ) {A B : GermIdeal n X} (hLe : A.Le B)
    (hBound : WeightedAlongAt Φ hSrc h0 k w B r) :
    WeightedAlongAt Φ hSrc h0 k w A r := fun f hf hAf=>hBound f hf (hLe z f hAf)

private theorem weighted_level_mono {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (w : Fin n→ℕ) {r s : ℕ} (hrs : r≤s) {A : GermIdeal n X}
    (hBound : WeightedAlongAt Φ hSrc h0 k w A s) :
    WeightedAlongAt Φ hSrc h0 k w A r := by
  intro f hf hAf
  exact (show (r : ℕ∞)≤s by exact_mod_cast hrs).trans (hBound f hf hAf)

private theorem weighted_iter_deriv {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent) :
    ∀i r : ℕ,WeightedAlongAt Φ hSrc h0 k w A ((r+i)*a)→
      WeightedAlongAt Φ hSrc h0 k w (iterDerivIdealAlong N A i) (r*a)
  | 0,r,hBound=>by simpa only [Nat.add_zero,iterDerivIdealAlong] using hBound
  | i+1,r,hBound=>by
    have hPrev : WeightedAlongAt Φ hSrc h0 k w (iterDerivIdealAlong N A i) ((r+1)*a):=
      weighted_iter_deriv Φ hSrc h0 k hFlat hN w a hWeights hA i (r+1)
        (by rw [show (r+1)+i=r+(i+1) by omega];exact hBound)
    exact weighted_along_deriv Φ hSrc h0 k hFlat w a (r*a) hWeights
      (isCoherent_iterDerivIdealAlong hA hN i)
      (by simpa only [Nat.add_mul,Nat.one_mul] using hPrev)

private theorem native_exponent_bound {d μ e p i : ℕ} (hd : 0<d) (hμ : d≤μ)
    (hi : i<d) (hBalance : (d-i)*p=d*e) : e*μ≤p*(μ-i) := by
  have hep : e≤p := by
    have hde : d*e≤d*p:=by rw [←hBalance];exact Nat.mul_le_mul_right p (Nat.sub_le d i)
    exact Nat.le_of_mul_le_mul_left hde hd
  calc
    e*μ=d*e+(μ-d)*e:=by rw [←Nat.add_mul,Nat.add_sub_of_le hμ,Nat.mul_comm]
    _=(d-i)*p+(μ-d)*e:=by rw [hBalance]
    _≤(d-i)*p+(μ-d)*p:=Nat.add_le_add_left (Nat.mul_le_mul_left (μ-d) hep) _
    _=(μ-i)*p:=by rw [←Nat.add_mul];congr 1;omega
    _=p*(μ-i):=Nat.mul_comm _ _

private def nativeCoefficientIdeal (N : Set X) (A : GermIdeal n X) (d : ℕ) : GermIdeal n X:=
  finSumIdeal (fun i=>idealPow (iterDerivIdealAlong N A i) (sumExp (fun j=>d-j) d i)) d

private theorem weighted_coefficient_high_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent) (d μ : ℕ) (hd : 1≤d) (hμ : d≤μ) :
    WeightedAlongAt Φ hSrc h0 k w (nativeCoefficientIdeal N A d)
      (sumExp (fun j=>d-j) d 0*μ*a) ↔ WeightedAlongAt Φ hSrc h0 k w A (μ*a) := by
  let e:=sumExp (fun j=>d-j) d 0
  let p:=fun i=>sumExp (fun j=>d-j) d i
  have he : 0<e:=one_le_sumExp (fun j hj=>by omega) 0
  have hBalance : ∀i<d,(d-i)*p i=d*e:=by
    intro i hi
    exact (mul_sumExp (fun j=>d-j) hi).trans
      (by simpa only [Nat.sub_zero] using (mul_sumExp (fun j=>d-j) (show 0<d from hd) (i:=0)).symm)
  constructor
  · intro hBound
    apply weighted_idealPow_reflect Φ hSrc h0 k w (μ*a) hA he
    have hLe : (idealPow A e).Le (nativeCoefficientIdeal N A d):=by
      intro x f hf
      change IsInSpanAt (n:=n) (fun g=>∃i,i<d ∧
        (idealPow (iterDerivIdealAlong N A i) (p i)).mem x g) x f
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨0,hd,hf⟩
        (GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_idealPow hA e) hf)
    have h:=weighted_mono Φ hSrc h0 k w (e*μ*a) hLe hBound
    simpa only [Nat.mul_assoc] using h
  · intro hBound
    apply weighted_finSum Φ hSrc h0 k w (e*μ*a) d _
      (fun i _=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN i) _)
    intro i hi
    have hDi : WeightedAlongAt Φ hSrc h0 k w (iterDerivIdealAlong N A i) ((μ-i)*a):=
      weighted_iter_deriv Φ hSrc h0 k hFlat hN w a hWeights hA i (μ-i)
        (by simpa only [Nat.sub_add_cancel (show i≤μ by omega)] using hBound)
    have hPower:=weighted_idealPow Φ hSrc h0 k w ((μ-i)*a)
      (isCoherent_iterDerivIdealAlong hA hN i) hDi (p i)
    apply weighted_level_mono Φ hSrc h0 k w _ hPower
    simpa only [←Nat.mul_assoc] using
      Nat.mul_le_mul_right a (native_exponent_bound (show 0<d from hd) hμ hi (hBalance i hi))

private theorem weighted_homogenized_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent) (m : ℕ) (hm : 1≤m) :
    WeightedAlongAt Φ hSrc h0 k w (homogenizedIdealAlong N A m) (m*a) ↔
      WeightedAlongAt Φ hSrc h0 k w A (m*a) := by
  constructor
  · exact weighted_mono Φ hSrc h0 k w (m*a)
      (le_homogenizedIdealAlong (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hA h) hm)
  · intro hBound
    change WeightedAlongAt Φ hSrc h0 k w
      (finSumIdeal (fun i=>(iterDerivIdealAlong N A i).mul
        (idealPow (iterDerivIdealAlong N A (m-1)) i)) m) (m*a)
    apply weighted_finSum Φ hSrc h0 k w (m*a) m _ (fun i _=>isCoherent_mul
      (isCoherent_iterDerivIdealAlong hA hN i)
      (isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN (m-1)) i))
    intro i hi
    have hDi : WeightedAlongAt Φ hSrc h0 k w (iterDerivIdealAlong N A i) ((m-i)*a):=
      weighted_iter_deriv Φ hSrc h0 k hFlat hN w a hWeights hA i (m-i)
        (by simpa only [Nat.sub_add_cancel hi.le] using hBound)
    have hT : WeightedAlongAt Φ hSrc h0 k w (iterDerivIdealAlong N A (m-1)) a := by
      have h:=weighted_iter_deriv Φ hSrc h0 k hFlat hN w a hWeights hA (m-1) 1
        (by rw [show 1+(m-1)=m by omega];exact hBound)
      simpa only [Nat.one_mul] using h
    have hPower:=weighted_idealPow Φ hSrc h0 k w a
      (isCoherent_iterDerivIdealAlong hA hN (m-1)) hT i
    have hProduct:=weighted_product Φ hSrc h0 k w ((m-i)*a) (i*a)
      (isCoherent_iterDerivIdealAlong hA hN i)
      (isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN (m-1)) i) hDi hPower
    have hIndex : (m-i)*a+i*a=m*a:=by rw [←Nat.add_mul,Nat.sub_add_cancel hi.le]
    simpa only [hIndex] using hProduct

private theorem weighted_coefficient_own_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent) (m : ℕ) (hm : 1≤m) :
    WeightedAlongAt Φ hSrc h0 k w (nativeCoefficientIdeal N A m)
      ((Finset.range m).prod (fun j=>m-j)*a) ↔ WeightedAlongAt Φ hSrc h0 k w A (m*a) := by
  have hMark : sumExp (fun j=>m-j) m 0*m=(Finset.range m).prod (fun j=>m-j):=by
    rw [Nat.mul_comm]
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>m-j) (show 0<m from hm) (i:=0)
  simpa only [hMark] using weighted_coefficient_high_iff Φ hSrc h0 k hFlat hN w a hWeights hA m m hm le_rfl

private def nativeBarIdeal (N : Set X) (A : GermIdeal n X) (m : ℕ) : GermIdeal n X:=
  nativeCoefficientIdeal N (homogenizedIdealAlong N A m) m

private theorem weighted_bar_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a)
    {A : GermIdeal n X} (hA : A.IsCoherent) (m : ℕ) (hm : 1≤m) :
    WeightedAlongAt Φ hSrc h0 k w (nativeBarIdeal N A m)
      ((Finset.range m).prod (fun j=>m-j)*a) ↔ WeightedAlongAt Φ hSrc h0 k w A (m*a) :=
  (weighted_coefficient_own_iff Φ hSrc h0 k hFlat hN w a hWeights
    (isCoherent_homogenizedIdealAlong hA hN m) m hm).trans
      (weighted_homogenized_iff Φ hSrc h0 k hFlat hN w a hWeights hA m hm)

private theorem flattenedTaylor_smaller_plane {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k s : ℕ) (hsk : s≤k)
    (f : X→ℂ) (hf : HolomorphicAt n f z) :
    flattenedTaylor Φ hSrc h0 s f hf=formalPlaneProject s (flattenedTaylor Φ hSrc h0 k f hf) := by
  have hComp : ∀y : ComplexModel n,planeRetract k (planeRetract s y)=planeRetract s y:=by
    intro y
    apply planeRetract_of_mem
    intro j hj
    exact planeRetract_mem s y j (hsk.trans hj)
  let g:=HolGerm.mk (flatten Φ k f) (eventually_differentiableAt_flatten hSrc h0 k hf)
  have hGerm : germPlaneProject s g=HolGerm.mk (flatten Φ s f)
      (eventually_differentiableAt_flatten hSrc h0 s hf) := by
    rw [germPlaneProject,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun y=>by
      change f (flatInv Φ (planeRetract k (planeRetract s y)))=f (flatInv Φ (planeRetract s y))
      rw [hComp]
  have h:=congrArg (fun h : HolGerm (ComplexModel n)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ=>h g)
    (actualTaylor_planeProject s)
  change actualUnshiftedTaylorAlgHom n (germPlaneProject s g)=formalPlaneProject s (actualUnshiftedTaylorAlgHom n g) at h
  rw [hGerm] at h
  exact h

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

private theorem actualTaylor_order_iff (q : ℕ) (g : HolGerm (ComplexModel n)) :
    (q : ℕ∞)≤(actualUnshiftedTaylorAlgHom n g).order ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  rw [actual_maximal_pow_iff]
  constructor
  · intro h α hα
    apply MvPowerSeries.coeff_of_lt_order
    have hd : (α.degree : ℕ∞)<q:=by
      simpa only [Finsupp.degree_eq_sum,normalExponentDegree,Nat.cast_lt] using hα
    exact hd.trans_le h
  · intro h
    apply MvPowerSeries.nat_le_order
    intro α hα
    apply h α
    simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using hα

private theorem native_vanishes_iff_flatten_order {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (f : X→ℂ) (hf : HolomorphicAt n f z) (q : ℕ) :
    VanishesToOrderOn n N z q f ↔ (q : ℕ∞)≤(flattenedTaylor Φ hSrc h0 k f hf).order := by
  let hF:=eventually_differentiableAt_flatten hSrc h0 k hf
  rw [vanishesToOrderOn_iff_iterDeriv_flatten hSrc h0 hFlat hf q]
  change _ ↔ (q : ℕ∞)≤(actualUnshiftedTaylorAlgHom n (HolGerm.mk (flatten Φ k f) hF)).order
  rw [actualTaylor_order_iff,mem_maximalIdeal_pow_iff_point_power hF q]
  let e:=complexChartAt (n:=n) (0 : ComplexModel n)
  rw [mem_idealPow_pointIdeal_iff (e:=e) (mem_complexChartAt_source (0 : ComplexModel n))
    (hF.mono fun _ h=>h.mdifferentiableAt) q]
  apply forall_congr'
  intro L
  apply imp_congr_right
  intro _hL
  rw [iterChartDeriv_eq_iterDeriv e _ L (mem_complexChartAt_source (0 : ComplexModel n))]
  simp only [e,complexChartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_symm,
    Function.comp_def,OpenPartialHomeomorph.refl_apply,id_eq]

private theorem multiplied_threshold_index (b t : ℕ) (hb : 0<b) :
    ∃q : ℕ,∀o : ℕ∞,(t : ℕ∞)≤(b : ℕ∞)*o ↔ (q : ℕ∞)≤o := by
  have hEx : ∃q : ℕ,t≤b*q:=⟨t,by
    have h:=Nat.mul_le_mul_right t hb
    simpa only [Nat.one_mul] using h⟩
  let q:=Nat.find hEx
  have hq : ∀r : ℕ,q≤r ↔ t≤b*r:=by
    intro r
    exact ⟨fun h=>(Nat.find_spec hEx).trans (Nat.mul_le_mul_left b h),fun h=>Nat.find_min' hEx h⟩
  refine ⟨q,?_⟩
  intro o
  by_cases ho : o=⊤
  · have hb0 : (b : ℕ∞)≠0:=by exact_mod_cast (Nat.ne_of_gt hb)
    simp only [ho,ENat.mul_top hb0,le_top]
  · obtain ⟨r,hr⟩:=ENat.ne_top_iff_exists.mp ho
    rw [←hr,←Nat.cast_mul]
    exact_mod_cast (hq r).symm

private theorem native_order_weighted_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    {A : GermIdeal n X} (hA : A.IsCoherent) (b t : ℕ) (hb : 0<b) :
    (t : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A z ↔
      WeightedAlongAt Φ hSrc h0 k (fun _=>b) A t := by
  obtain ⟨q,hq⟩:=multiplied_threshold_index b t hb
  rw [hq,GermIdealOrder.le_order_iff (fun f hf=>GermIdeal.IsCoherent.holomorphicAt_mem hA hf)]
  constructor
  · intro h f hf hAf
    change (t : ℕ∞)≤(flattenedTaylor Φ hSrc h0 k f hf).weightedOrder (fun _=>b)
    rw [const_weightedOrder n b hb,hq]
    exact (native_vanishes_iff_flatten_order Φ hSrc h0 k hFlat f hf q).mp (h f hAf)
  · intro h f hAf
    have hf:=GermIdeal.IsCoherent.holomorphicAt_mem hA hAf
    apply (native_vanishes_iff_flatten_order Φ hSrc h0 k hFlat f hf q).mpr
    apply (hq _).mp
    have hMember:=h f hf hAf
    change (t : ℕ∞)≤(flattenedTaylor Φ hSrc h0 k f hf).weightedOrder (fun _=>b) at hMember
    rwa [const_weightedOrder n b hb] at hMember

private theorem support_plane_iff (k : ℕ) (α : Fin n→₀ℕ) :
    (↑α.support : Set (Fin n))⊆range (planeEmbedding k) ↔
      ∀j : Fin n,k ≤ j.val→α j=0 := by
  constructor
  · intro h j hj
    by_contra hα
    obtain ⟨i,hi⟩:=h (Finsupp.mem_support_iff.mpr hα)
    have hi' : j.val<k:=by simpa only [planeEmbedding] using hi ▸ i.property
    omega
  · intro h j hj
    refine ⟨⟨j,?_⟩,rfl⟩
    by_contra hk
    exact (Finsupp.mem_support_iff.mp hj) (h j (by omega))

private theorem contact_weight_zero (l : Fin n) (a b : ℕ) (α : Fin n→₀ℕ)
    (hα : α l=0) :
    Finsupp.weight (contactWeight l a b) α=b*normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum,normalExponentDegree,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=l
  · subst j
    simp only [hα,zero_smul,mul_zero]
  · simp only [contactWeight,if_neg hj,smul_eq_mul,Nat.mul_comm]

private theorem weighted_contact_trace (k : ℕ) (l : Fin n) (hl : l.val+1=k)
    (a b r : ℕ) {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈weightedLevel (contactWeight l a b) r) :
    formalPlaneProject (k-1) F∈weightedLevel (fun _=>b) r := by
  apply (mem_weightedLevel_iff _ _ _).mpr
  intro α hα
  rw [coeff_formalPlaneProject]
  split_ifs with hSub
  · apply (mem_weightedLevel_iff _ _ _).mp hF
    rw [contact_weight_zero l a b α ((support_plane_iff _ _).mp hSub l (by omega))]
    rwa [const_weight] at hα
  · rfl

/-- Recovery uses ALL genuine coefficients and nonzero derivative factorials. -/
private theorem weighted_contact_recover (k : ℕ) (l : Fin n) (hl : l.val+1=k)
    (a b m : ℕ) {F : MvPowerSeries (Fin n) ℂ}
    (hFixed : formalPlaneProject k F=F)
    (hDeriv : ∀i,i<m→formalPlaneProject (k-1)
      (actualFormalMultiDerivative (Finsupp.single l i) F)∈
        weightedLevel (fun _=>b) ((m-i)*a)) :
    F∈weightedLevel (contactWeight l a b) (m*a) := by
  apply (mem_weightedLevel_iff _ _ _).mpr
  intro α hα
  by_cases hSub : (↑α.support : Set (Fin n))⊆range (planeEmbedding k)
  · let β:=α.erase l
    have hβl : β l=0:=Finsupp.erase_same
    have hSplit : β+Finsupp.single l (α l)=α:=by
      ext j
      by_cases hj : j=l
      · subst j
        simp only [Finsupp.add_apply,hβl,Finsupp.single_eq_same,zero_add]
      · simp only [Finsupp.add_apply,Finsupp.single_eq_of_ne hj,add_zero]
        exact Finsupp.erase_ne hj
    have hWeight : Finsupp.weight (contactWeight l a b) α=
        b*normalExponentDegree β+a*(α l) := by
      conv_lhs=>rw [←hSplit]
      rw [map_add,contact_weight_zero l a b β hβl,Finsupp.weight_single]
      simp [contactWeight,smul_eq_mul,Nat.mul_comm]
    have hi : α l<m:=by
      by_contra hi
      have h:=Nat.mul_le_mul_left a (show m≤α l by omega)
      rw [hWeight] at hα
      nlinarith
    have hβSub : (↑β.support : Set (Fin n))⊆range (planeEmbedding (k-1)):=by
      apply (support_plane_iff _ _).mpr
      intro j hj
      by_cases hjl : j=l
      · simpa only [hjl] using hβl
      · have hjk : k ≤ j.val:=by
          have hne : j.val≠l.val:=fun h=>hjl (Fin.ext h)
          omega
        rw [Finsupp.erase_ne hjl]
        exact (support_plane_iff _ _).mp hSub j hjk
    have hβWeight : Finsupp.weight (fun _ : Fin n=>b) β<(m-α l)*a:=by
      rw [const_weight]
      have hm : (m-α l)*a+(α l)*a=m*a:=by
        rw [←Nat.add_mul,Nat.sub_add_cancel hi.le]
      rw [hWeight,Nat.mul_comm a (α l)] at hα
      omega
    have hZero:=(mem_weightedLevel_iff _ _ _).mp (hDeriv (α l) hi) β hβWeight
    rw [coeff_formalPlaneProject,if_pos hβSub,coeff_actualFormalMultiDerivative,hSplit] at hZero
    exact (mul_eq_zero.mp hZero).resolve_right
      (div_ne_zero (actualExponentFactorial_ne_zero α) (actualExponentFactorial_ne_zero β))
  · have h:=congrArg (MvPowerSeries.coeff α) hFixed
    rw [coeff_formalPlaneProject,if_neg hSub] at h
    exact h.symm

private def flatIter {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (l : Fin n) : ℕ→(X→ℂ)→X→ℂ
  | 0,f=>f
  | i+1,f=>flatPartial Φ l (flatIter Φ l i f)

private theorem flatIter_hol {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (l : Fin n) (i : ℕ) {f : X→ℂ} (hf : HolomorphicAt n f z) :
    HolomorphicAt n (flatIter Φ l i f) z := by
  induction i with
  | zero=>exact hf
  | succ i ih=>exact holomorphicAt_flatPartial l (mem_flatDomain_self Φ) ih

private theorem flatIter_mem {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (l : Fin n) (hl : l.val<k) {A : GermIdeal n X}
    {f : X→ℂ} (hf : HolomorphicAt n f z) (hAf : A.mem z f) (i : ℕ) :
    (iterDerivIdealAlong N A i).mem z (flatIter Φ l i f) := by
  induction i with
  | zero=>exact hAf
  | succ i ih=>
    apply InvertibleIdealQuotient.isInSpanAt_self
    · exact Or.inr (Or.inr ⟨_,_,flatIter Φ l i f,
        isTangentField_flatField hSrc hFlat (single_mem_complexCoordinatePlane hl)
          (mem_flatDomain_self Φ),ih,rfl⟩)
    · exact flatIter_hol Φ l (i+1) hf

private theorem flattenedTaylor_flatIter {z : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (l : Fin n) (hl : l.val<k) (f : X→ℂ) (hf : HolomorphicAt n f z) (i : ℕ) :
    flattenedTaylor Φ hSrc h0 k (flatIter Φ l i f) (flatIter_hol Φ l i hf)=
      actualFormalMultiDerivative (Finsupp.single l i) (flattenedTaylor Φ hSrc h0 k f hf) := by
  induction i with
  | zero=>simp only [Finsupp.single_zero,actualFormalMultiDerivative_zero,flatIter]
  | succ i ih=>
    change flattenedTaylor Φ hSrc h0 k (flatPartial Φ l (flatIter Φ l i f)) _=_
    rw [flattenedTaylor_flatPartial Φ hSrc h0 k _ (flatIter_hol Φ l i hf) l hl,ih]
    rw [show Finsupp.single l (i+1)=Finsupp.single l i+Finsupp.single l 1 from Finsupp.single_add l i 1,
      actualFormalMultiDerivative_add_single]

private theorem weighted_derivative_trace_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) (l : Fin n) (hl : l.val+1=k)
    {A : GermIdeal n X} (hA : A.IsCoherent) (a b m : ℕ) (_hb : 0<b) (hba : b≤a) :
    (∀i,i<m→WeightedAlongAt Φ hSrc h0 (k-1) (fun _=>b)
      (iterDerivIdealAlong N A i) ((m-i)*a)) ↔
        WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) A (m*a) := by
  constructor
  · intro hTrace f hf hAf
    apply weighted_contact_recover k l hl a b m
    · exact (flattenedTaylor_smaller_plane Φ hSrc h0 k k le_rfl f hf).symm
    · intro i hi
      have hHol:=flatIter_hol Φ l i hf
      have hMem:=flatIter_mem Φ hSrc k hFlat l (by omega) hf hAf i
      have hBound:=hTrace i hi (flatIter Φ l i f) hHol hMem
      rw [flattenedTaylor_smaller_plane Φ hSrc h0 k (k-1) (Nat.sub_le _ _) _ hHol,
        flattenedTaylor_flatIter Φ hSrc h0 k l (by omega) f hf i] at hBound
      exact hBound
  · intro hBound i hi f hf hDf
    have hWeights : ∀j,contactWeight l a b j≤a:=by
      intro j
      dsimp only [contactWeight]
      split_ifs
      · exact le_rfl
      · exact hba
    have hD:=weighted_iter_deriv Φ hSrc h0 k hFlat hN (contactWeight l a b) a hWeights
      hA i (m-i) (by simpa only [Nat.sub_add_cancel hi.le] using hBound)
    have hF:=hD f hf hDf
    rw [flattenedTaylor_smaller_plane Φ hSrc h0 k (k-1) (Nat.sub_le _ _) f hf]
    exact weighted_contact_trace k l hl a b ((m-i)*a) hF

private theorem weighted_coefficient_trace_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (s : ℕ)
    (hN : IsClosedSubmanifold n N) {A : GermIdeal n X} (hA : A.IsCoherent)
    (m a b : ℕ) (_hm : 1≤m) :
    WeightedAlongAt Φ hSrc h0 s (fun _=>b) (nativeCoefficientIdeal N A m)
      ((Finset.range m).prod (fun j=>m-j)*a) ↔
      ∀i,i<m→WeightedAlongAt Φ hSrc h0 s (fun _=>b)
        (iterDerivIdealAlong N A i) ((m-i)*a) := by
  let p:=fun i=>sumExp (fun j=>m-j) m i
  have hBalance : ∀i<m,p i*((m-i)*a)=(Finset.range m).prod (fun j=>m-j)*a:=by
    intro i hi
    rw [←Nat.mul_assoc,Nat.mul_comm (p i) (m-i),mul_sumExp (fun j=>m-j) hi]
  constructor
  · intro hBound i hi
    have hLe : (idealPow (iterDerivIdealAlong N A i) (p i)).Le (nativeCoefficientIdeal N A m):=by
      intro y f hf
      change IsInSpanAt (n:=n) (fun g=>∃j,j<m ∧
        (idealPow (iterDerivIdealAlong N A j) (p j)).mem y g) y f
      exact InvertibleIdealQuotient.isInSpanAt_self ⟨i,hi,hf⟩
        (GermIdeal.IsCoherent.holomorphicAt_mem
          (isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN i) _) hf)
    apply weighted_idealPow_reflect Φ hSrc h0 s (fun _=>b) ((m-i)*a)
      (isCoherent_iterDerivIdealAlong hA hN i)
      (show 0<p i from one_le_sumExp (fun j hj=>by omega) i)
    rw [hBalance i hi]
    exact weighted_mono Φ hSrc h0 s (fun _=>b) _ hLe hBound
  · intro hAll
    apply weighted_finSum Φ hSrc h0 s (fun _=>b) _ m _
      (fun i _=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN i) _)
    intro i hi
    have h:=weighted_idealPow Φ hSrc h0 s (fun _=>b) ((m-i)*a)
      (isCoherent_iterDerivIdealAlong hA hN i) (hAll i hi) (p i)
    rwa [hBalance i hi] at h

private theorem coefficient_contact_in_coordinates {z : X} {N S : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hSFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈S ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n (k-1)))
    (hN : IsClosedSubmanifold n N) (l : Fin n) (hl : l.val+1=k)
    {A : GermIdeal n X} (hA : A.IsCoherent) (m a b : ℕ)
    (hm : 1≤m) (hb : 0<b) (hba : b≤a) :
    (((Finset.range m).prod (fun j=>m-j)*a : ℕ) : ℕ∞)≤
      (b : ℕ∞)*GermIdealOrder.order n S (nativeCoefficientIdeal N A m) z ↔
        WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) A (m*a) := by
  have hC : (nativeCoefficientIdeal N A m).IsCoherent:=
    isCoherent_finSumIdeal (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN i) _) m
  exact (native_order_weighted_iff Φ hSrc h0 (k-1) hSFlat hC b _ hb).trans
    ((weighted_coefficient_trace_iff Φ hSrc h0 (k-1) hN hA m a b hm).trans
      (weighted_derivative_trace_iff Φ hSrc h0 k hFlat hN l hl hA a b m hb hba))

/-- Native coefficient-record order, with all infinite/zero restrictions retained. -/
theorem contact_coefficient_weighted_threshold (M : MarkedIdeal n X)
    (hA : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) (hm : 1≤M.d)
    {V : Set X} {w : X→ℂ} (hw : IsTangentDirectionAlong M.N M.ideal M.d V w)
    (z : X) (hz : z∈M.N ∧ z∈V ∧ w z=0) :
    ∃k : ℕ,0<k ∧ k≤n ∧ ∃l : Fin n,l.val+1=k ∧
      ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
        (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
        (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
        (∀y∈flatDomain Φ,y∈V ∧
          (y∈M.N ↔ flatMap Φ y∈complexCoordinatePlane n k) ∧
          flatCoord Φ l y=w y ∧
          (y∈M.N ∧ w y=0 ↔ flatMap Φ y∈complexCoordinatePlane n (k-1))) ∧
        ∀a b : ℕ,0<b→b≤a→
          ((((coeffMarkedAlong M).d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
            GermIdealOrder.order n (M.N∩{y | w y=0}) (coeffMarkedAlong M).ideal z ↔
              WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) M.ideal (M.d*a)) := by
  obtain ⟨k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords⟩:=contact_coordinates hA hN hw z hz
  refine ⟨k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords,?_⟩
  intro a b hb hba
  exact coefficient_contact_in_coordinates Φ hSrc h0 k
    (fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1)
    (fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.2.2)
    hN l hl hA M.d a b hm hb hba

private theorem double_contact_in_coordinates {z : X} {N S : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hSFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈S ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n (k-1)))
    (hN : IsClosedSubmanifold n N) (l : Fin n) (hl : l.val+1=k)
    {A : GermIdeal n X} (hA : A.IsCoherent) (m a b : ℕ)
    (hm : 1≤m) (hb : 0<b) (hba : b≤a) :
    let D:=(Finset.range m).prod (fun j=>m-j)
    ((((Finset.range D).prod (fun j=>D-j))*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
      GermIdealOrder.order n S (nativeCoefficientIdeal N (nativeBarIdeal N A m) D) z ↔
        WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) A (m*a) := by
  let D:=(Finset.range m).prod (fun j=>m-j)
  have hD : 1≤D:=by
    have hPos : 0<D:=by
      apply Finset.prod_pos
      intro i hi
      have hi':=Finset.mem_range.mp hi
      omega
    omega
  have hBar : (nativeBarIdeal N A m).IsCoherent:=
    isCoherent_finSumIdeal (fun i=>isCoherent_idealPow
      (isCoherent_iterDerivIdealAlong (isCoherent_homogenizedIdealAlong hA hN m) hN i) _) m
  have hWeights : ∀j,contactWeight l a b j≤a:=by
    intro j
    dsimp only [contactWeight]
    split_ifs
    · exact le_rfl
    · exact hba
  exact (coefficient_contact_in_coordinates Φ hSrc h0 k hFlat hSFlat hN l hl hBar D a b hD hb hba).trans
    (weighted_bar_iff Φ hSrc h0 k hFlat hN (contactWeight l a b) a hWeights hA m hm)

/-- Exact native DOUBLE-coefficient record, with literal full boundary and product marks. -/
theorem actual_double_coefficient_contact_threshold (M : MarkedIdeal n X)
    (hA : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) (hm : 1≤M.d)
    {V : Set X} {w : X→ℂ} (hw : IsTangentDirectionAlong M.N M.ideal M.d V w)
    (z : X) (hz : z∈M.N ∧ z∈V ∧ w z=0) :
    let C:=coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))
    C.N=M.N ∧ C.E=M.E ∧
      C.d=(Finset.range ((Finset.range M.d).prod (fun j=>M.d-j))).prod
        (fun j=>(Finset.range M.d).prod (fun j=>M.d-j)-j) ∧
    ∃k : ℕ,0<k ∧ k≤n ∧ ∃l : Fin n,l.val+1=k ∧
      ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
        (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
        (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
        (∀y∈flatDomain Φ,y∈V ∧
          (y∈M.N ↔ flatMap Φ y∈complexCoordinatePlane n k) ∧
          flatCoord Φ l y=w y ∧
          (y∈M.N ∧ w y=0 ↔ flatMap Φ y∈complexCoordinatePlane n (k-1))) ∧
        ∀a b : ℕ,0<b→b≤a→
          ((((C.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
            GermIdealOrder.order n (M.N∩{y | w y=0}) C.ideal z) ↔
              WeightedAlongAt Φ hSrc h0 k (contactWeight l a b) M.ideal (M.d*a)) := by
  obtain ⟨k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords⟩:=contact_coordinates hA hN hw z hz
  refine ⟨rfl,rfl,rfl,k,hk,hkn,l,hl,Φ,hSrc,h0,hCoords,?_⟩
  intro a b hb hba
  exact double_contact_in_coordinates Φ hSrc h0 k
    (fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1)
    (fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.2.2)
    hN l hl hA M.d a b hm hb hba

private theorem weighted_sandwich_iff {z : X} {N : Set X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
    (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0) (k : ℕ)
    (hFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n k))
    (hN : IsClosedSubmanifold n N) {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) (d μ : ℕ) (hd : 1≤d) (hμ : d≤μ)
    (hLow : RestrictLe N (idealPow A (sumExp (fun j=>d-j) d 0)) B)
    (hHigh : RestrictLe N B (nativeCoefficientIdeal N A d))
    (w : Fin n→ℕ) (a : ℕ) (hWeights : ∀i,w i≤a) :
    WeightedAlongAt Φ hSrc h0 k w B (sumExp (fun j=>d-j) d 0*μ*a) ↔
      WeightedAlongAt Φ hSrc h0 k w A (μ*a) := by
  let e:=sumExp (fun j=>d-j) d 0
  constructor
  · intro h
    apply weighted_idealPow_reflect Φ hSrc h0 k w (μ*a) hA
      (show 0<e from one_le_sumExp (fun j hj=>by omega) 0)
    simpa only [Nat.mul_assoc] using
      weighted_restrictLe Φ hSrc h0 k hFlat w (e*μ*a) hB hLow h
  · intro h
    have hC : (nativeCoefficientIdeal N A d).IsCoherent:=
      isCoherent_finSumIdeal (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hA hN i) _) d
    exact weighted_restrictLe Φ hSrc h0 k hFlat w (e*μ*a) hC hHigh
      ((weighted_coefficient_high_iff Φ hSrc h0 k hFlat hN w a hWeights hA d μ hd hμ).mpr h)

/-- Ordinary ORIGINAL inputs produce the weighted dictionary at EVERY actual original prefix. -/
theorem original_lower_weighted_histories {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set A) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      x∈U ∧ B=coeffMarkedAlong P ∧ J.d=μ ∧ K.d=e*μ ∧
      ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T→
        IsGeoTestTower K T ∧ (geoTransformAlong J T).N=(geoTransformAlong K T).N ∧
        (geoTransformAlong J T).E=(geoTransformAlong K T).E ∧
        (geoTransformAlong J T).E.length=T.length ∧ (geoTransformAlong K T).E.length=T.length ∧
        ∀(z : Y)(s : ℕ)(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
          (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
          (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
          (∀{y : Y},y∈(chartAt (ComplexModel n) z).source→
            chartAt (ComplexModel n) z y∈Φ.source→
              (y∈(geoTransformAlong J T).N ↔
                Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s))→
          ∀(w : Fin n→ℕ)(a : ℕ),(∀i,w i≤a)→
            (WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong J T).ideal (μ*a) ↔
              WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong K T).ideal (e*μ*a)) := by
  obtain ⟨hm,hxU,hNatural,hJ,hK,hJd,hKd,hHist⟩:=
    original_lower_companion_history_sandwich hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hm0,hL,_hEmpty,_hMark,_hx,hμ,_hOrd,_hCoeff,_hHist0⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,hNatural,hJd,hKd,?_⟩
  intro Y T hT
  obtain ⟨hTK,hNT,hET,hLenJ,hLenK,hLow,hHigh⟩:=hHist T hT
  refine ⟨hTK,hNT,hET,hLenJ,hLenK,?_⟩
  intro z s Φ hSrc h0 hFlat w a hWeights
  have hJT:=isInvDomain_geoTransformAlong hJ T hT
  have hKT:=isInvDomain_geoTransformAlong hK T hTK
  exact (weighted_sandwich_iff Φ hSrc h0 s hFlat hJT.isWellFormed.isClosedSubmanifold_N
    hJT.isWellFormed.isCoherent hKT.isWellFormed.isCoherent _ _ hL.one_le_d hμ
    hLow hHigh w a hWeights).symm

private theorem native_order_pullback_open {N : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) (V : TopologicalSpace.Opens X) (x : V) (hx : x.val∈N) :
    GermIdealOrder.order n ((Subtype.val : V→X) ⁻¹' N)
      (GermIdeal.pullback (m:=n) (Subtype.val : V→X) I) x=GermIdealOrder.order n N I x.val := by
  have hPull:=isCoherent_pullback (f:=(Subtype.val : V→X)) contMDiff_subtype_val hI
  apply ENat.eq_of_forall_natCast_le_iff
  intro q
  rw [GermIdealOrder.le_order_iff (fun f hf=>GermIdeal.IsCoherent.holomorphicAt_mem hPull hf),
    GermIdealOrder.le_order_iff (fun f hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf)]
  let M : MarkedIdeal n X:={N:=N,E:=[],ideal:=I,d:=q}
  have hCos : x∈(MarkedIdeal.pullback (Subtype.val : V→X) M).cosupp ↔ x.val∈M.cosupp:=by
    rw [cosupp_pullback_val M (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf) V]
    rfl
  exact ⟨fun h=>(hCos.mp ⟨hx,h⟩).2,fun h=>(hCos.mpr ⟨hx,h⟩).2⟩

private theorem common_contact_cuts_in_window (J K : MarkedIdeal n X)
    (hJI : J.ideal.IsCoherent) (hKI : K.ideal.IsCoherent)
    (hJN : IsClosedSubmanifold n J.N) (hKN : IsClosedSubmanifold n K.N)
    (hJm : 1≤J.d) (hKm : 1≤K.d) (hNK : J.N=K.N)
    (d : ℕ) (hd : 1≤d) (hdm : d≤J.d)
    (hMark : K.d=sumExp (fun j=>d-j) d 0*J.d)
    (hLow : RestrictLe J.N (idealPow J.ideal (sumExp (fun j=>d-j) d 0)) K.ideal)
    (hHigh : RestrictLe J.N K.ideal (nativeCoefficientIdeal J.N J.ideal d))
    {V : Set X} {w : X→ℂ} (hwK : IsTangentDirectionAlong K.N K.ideal K.d V w)
    (z : X) (hz : z∈K.N ∧ z∈V ∧ w z=0) :
    let Vz : TopologicalSpace.Opens X:=⟨V,hwK.isOpen⟩
    let RJ:=contactMarkedKept J w (.refl : BlowupTower X X) Vz
    let RK:=contactMarkedKept K w (.refl : BlowupTower X X) Vz
    ∀a b : ℕ,0<b→b≤a→
      ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RJ.ideal (⟨z,hz.2.1⟩ : Vz)) ↔
       (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RK.N RK.ideal (⟨z,hz.2.1⟩ : Vz))) := by
  dsimp only
  let Vz : TopologicalSpace.Opens X:=⟨V,hwK.isOpen⟩
  have hzS : z∈K.N∩{y | w y=0}:=⟨hz.1,hz.2.2⟩
  obtain ⟨s,_hs,_hsn,l,hl,Φ,hSrc,h0,hCoords⟩:=contact_coordinates hKI hKN hwK z hz
  have hKFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈K.N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s):=
    fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1
  have hJFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈J.N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s):=by
    rw [hNK]
    exact hKFlat
  have hKSFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈K.N∩{y | w y=0} ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n (s-1)):=
    fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.2.2
  have hJSFlat : ∀{y : X},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈J.N∩{y | w y=0} ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n (s-1)):=by
    rw [hNK]
    exact hKSFlat
  let CJ:=coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong J))
  let CK:=coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong K))
  have hCJ : CJ.ideal.IsCoherent:=isCoherent_coeffMarkedAlong
    (isCoherent_coeffMarkedAlong (isCoherent_homogenizedIdealAlong hJI hJN _) hJN) hJN
  have hCK : CK.ideal.IsCoherent:=isCoherent_coeffMarkedAlong
    (isCoherent_coeffMarkedAlong (isCoherent_homogenizedIdealAlong hKI hKN _) hKN) hKN
  have hOrdJ:=native_order_pullback_open hCJ Vz (⟨z,hz.2.1⟩ : Vz)
    (show z∈J.N∩{y | w y=0} by rw [hNK];exact hzS)
  have hOrdK:=native_order_pullback_open hCK Vz (⟨z,hz.2.1⟩ : Vz) hzS
  intro a b hb hba
  change (((CJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
    ((Subtype.val : Vz→X) ⁻¹' (J.N∩{y | w y=0}))
    (GermIdeal.pullback (m:=n) (Subtype.val : Vz→X) CJ.ideal) (⟨z,hz.2.1⟩ : Vz) ↔
      ((CK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
    ((Subtype.val : Vz→X) ⁻¹' (K.N∩{y | w y=0}))
    (GermIdeal.pullback (m:=n) (Subtype.val : Vz→X) CK.ideal) (⟨z,hz.2.1⟩ : Vz))
  rw [hOrdJ,hOrdK]
  have hDJ:=double_contact_in_coordinates Φ hSrc h0 s hJFlat hJSFlat hJN l hl hJI J.d a b hJm hb hba
  have hDK:=double_contact_in_coordinates Φ hSrc h0 s hKFlat hKSFlat hKN l hl hKI K.d a b hKm hb hba
  have hWeights : ∀j,contactWeight l a b j≤a:=by
    intro j
    dsimp only [contactWeight]
    split_ifs
    · exact le_rfl
    · exact hba
  have hCuts:=(weighted_sandwich_iff Φ hSrc h0 s hJFlat hJN hJI hKI d J.d hd hdm
    hLow hHigh (contactWeight l a b) a hWeights).symm
  change (((CJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n (J.N∩{y | w y=0}) CJ.ideal z) ↔
    WeightedAlongAt Φ hSrc h0 s (contactWeight l a b) J.ideal (J.d*a) at hDJ
  change (((CK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n (K.N∩{y | w y=0}) CK.ideal z) ↔
    WeightedAlongAt Φ hSrc h0 s (contactWeight l a b) K.ideal (K.d*a) at hDK
  rw [hDJ,hDK,hMark]
  exact hCuts

private theorem initial_contact_E (M : MarkedIdeal n X) (w : X→ℂ) (V : TopologicalSpace.Opens X) :
    (contactMarkedKept M w (.refl : BlowupTower X X) V).E=
      M.E.map ((Subtype.val : V→X) ⁻¹' ·) := rfl

private theorem initial_contact_d (M : MarkedIdeal n X) (w : X→ℂ) (V : TopologicalSpace.Opens X) :
    (contactMarkedKept M w (.refl : BlowupTower X X) V).d=
      (Finset.range ((Finset.range M.d).prod (fun j=>M.d-j))).prod
        (fun j=>(Finset.range M.d).prod (fun j=>M.d-j)-j) := rfl

/-- SAME actual selected contact, literal double marks and whole extended-order cuts. -/
theorem original_lower_common_contact_thresholds {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set A) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.d=μ ∧ K.d=e*μ ∧
      ∀z∈K.cosupp,∃hOpen : IsOpen (tangentChoice K z).1,
        let Vz : TopologicalSpace.Opens (CMfd.of (n:=n) U):=⟨(tangentChoice K z).1,hOpen⟩
        ∃hzV : z∈Vz,
          let RJ:=contactMarkedKept J (tangentChoice K z).2 (.refl : BlowupTower _ _) Vz
          let RK:=contactMarkedKept K (tangentChoice K z).2 (.refl : BlowupTower _ _) Vz
          RJ.E=J.E.map ((Subtype.val : Vz→U) ⁻¹' ·) ∧
          RK.E=K.E.map ((Subtype.val : Vz→U) ⁻¹' ·) ∧
          RJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
            (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
          RK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
            (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
          ∀a b : ℕ,0<b→b≤a→
            ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
              GermIdealOrder.order n RJ.N RJ.ideal (⟨z,hzV⟩ : Vz)) ↔
            (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
              GermIdealOrder.order n RK.N RK.ideal (⟨z,hzV⟩ : Vz))) := by
  obtain ⟨hm,_hxU,hJ,hK,hNK,hJd,hKd,_hzJ,_hzK,_hIncl,hContact⟩:=
    original_lower_selected_common_contact hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=companionOf n P μ
  let K:=companionOf n B (e*μ)
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  change J.N=K.N at hNK
  change J.d=μ at hJd
  change K.d=e*μ at hKd
  obtain ⟨_hmW,_hxUW,_hNatural,_hJ0,_hK0,_hJdW,_hKdW,hHist⟩:=
    original_lower_companion_history_sandwich hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hm0,hL,_hEmpty,_hMark,_hx,hμ,_hOrd,_hCoeff,_hHist0⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax W hW hSing a ha
  change IsInvDomain (k-1) L at hL
  change L.d≤μ at hμ
  refine ⟨hm,hJ,hK,hJd,hKd,?_⟩
  intro z hz
  obtain ⟨hzV,hwK,_hwJ,_hZeroJ,hZeroK⟩:=hContact z hz
  obtain ⟨_hTK,_hNT,_hET,_hLenJ,_hLenK,hLow,hHigh⟩:=hHist .refl trivial
  have hLow' : RestrictLe J.N (idealPow J.ideal e) K.ideal:=hLow
  have hHigh' : RestrictLe J.N K.ideal (nativeCoefficientIdeal J.N J.ideal L.d):=hHigh
  let Vz : TopologicalSpace.Opens (CMfd.of (n:=n) U):=⟨(tangentChoice K z).1,hwK.isOpen⟩
  refine ⟨hwK.isOpen,hzV,?_,?_,?_,?_,?_⟩
  · exact initial_contact_E J _ Vz
  · exact initial_contact_E K _ Vz
  · simpa only [hJd] using initial_contact_d J (tangentChoice K z).2 Vz
  · simpa only [hKd] using initial_contact_d K (tangentChoice K z).2 Vz
  · exact common_contact_cuts_in_window J K hJ.isWellFormed.isCoherent hK.isWellFormed.isCoherent
      hJ.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isClosedSubmanifold_N
      hJ.one_le_d hK.one_le_d hNK L.d hL.one_le_d (by rw [hJd];exact hμ)
      (by rw [hJd,hKd]) hLow' hHigh' hwK z ⟨hz.1,hzV,hZeroK ⟨hz,hzV⟩⟩

end
end Hironaka.HironakaActualContactWeightedCoefficientThreshold
