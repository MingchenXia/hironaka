import Hironaka.Resolution.HironakaActualOriginalHistoricalBarWeightedThreshold
import Hironaka.Invariant.ContactEquivalenceStage

/-! Actual ORIGINAL strict-contact/openPreimage lower-record order cuts.
Blueprint FIRST: hironaka-actual-original-strict-contact-weighted-order.tex.
Local generic nested-coordinate coefficient helper proofs repeat frozen1551
PRIVATE arguments and earn ZERO new mathematical-engine credit. New credit is
actual historical strict geometry/ORIGINAL lower transport and native clocks. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalStrictContactWeightedOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality HironakaActualInheritedAnalyticBlockJacobian
  HironakaRelativeNormalTaylorCoefficients HironakaActualFormalCoordinatePowerDivision
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  RelativePrincipalizationSpan BlowupTowers BlowupFlatCoordinates BlowupSNCTransform GiraudAlong TangentDirectionAlong
  DerivativeIdealAlong DerivativeIdealAlongCoherent RegularPointDimension RegularPatchPullback HadamardBridgeAlong
  RestrictedIdealWeight IdealWeightPowers GermIdealPullbackCalculus HomogenizedGlueing HomogenizedEquivalence
  HomogenizedIdealAlong CoefficientIdeal MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualOriginalFormalTaylor HironakaHolomorphicPointJets OrderTaylor HolomorphicTaylorTail GermIdealOrder
  HironakaActualCanonicalBlockJacobian HironakaActualContactWeightedCoefficientThreshold
  HironakaActualOriginalHistoricalBarWeightedThreshold HironakaActualTrueMarkCoefficientHistorySandwich
  HironakaActualOriginalCoefficientHistoryAlong HironakaActualTrueMarkCommonContact
  HironakaActualOriginalTrueMarkMaskCompanions StepOneValue StepOneValueMasked CompanionRebase CompanionReductionAlong
  CompanionOpen ResolutionInvariantSpec InvDomainTowerAlong BlowupTowerTransforms NonmonomialOrderLocal
  NonmonomialOrderTail MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaEmbeddedAnalytic
  ContactStageKept CoefficientIdealRestriction HomogenizedGlueingTower ContactEquivalenceStage
variable {n : ℕ} {X : CMfd.{u} n}

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

private def nativeCoefficientIdeal (N : Set X) (A : GermIdeal n X) (d : ℕ) : GermIdeal n X:=
  finSumIdeal (fun i=>idealPow (iterDerivIdealAlong N A i) (sumExp (fun j=>d-j) d i)) d

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


/-- ONE actual strict-contact chart supports ALL ordinary target records on the same carrier. -/
theorem original_open_contact_weighted_dictionary {k : ℕ} (C : MarkedIdeal n X)
    (hC : IsInvDomain k C) (U : TopologicalSpace.Opens X) {u : X→ℂ}
    (hu : IsTangentDirectionAlong C.N C.ideal C.d U u)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower C T)
    (z : openPreimage T U) (hzS : z.val∈strictAlong T (C.N∩{x | u x=0})) :
    ∃Ω : TopologicalSpace.Opens Y,z.val∈Ω ∧ (Ω : Set Y)⊆openPreimage T U ∧
      ∃uT : Y→ℂ,
        IsTangentDirectionAlong (geoTransformAlong C T).N (geoTransformAlong C T).ideal
          (geoTransformAlong C T).d Ω uT ∧
      ∃s : ℕ,0<s ∧ s≤n ∧ ∃l : Fin n,l.val+1=s ∧
      ∃(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z.val z.val))
        (hSrc : Φ.source⊆(chartAt (ComplexModel n) z.val).target)
        (h0 : Φ.toFun (chartAt (ComplexModel n) z.val z.val)=0),
        (∀y∈flatDomain Φ,y∈Ω ∧
          (y∈(geoTransformAlong C T).N ↔ flatMap Φ y∈complexCoordinatePlane n s) ∧
          flatCoord Φ l y=uT y ∧
          (y∈strictAlong T (C.N∩{x | u x=0}) ↔ flatMap Φ y∈complexCoordinatePlane n (s-1))) ∧
        ∀(M : MarkedIdeal n X){q : ℕ}(_hM : IsInvDomain q M),M.N=C.N→IsGeoTestTower M T→
          let R:=contactMarkedKept M u T (openPreimage T U)
          R.N=(Subtype.val : openPreimage T U→Y) ⁻¹' strictAlong T (C.N∩{x | u x=0}) ∧
          R.E=(geoTransformAlong M T).E.map ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
          R.d=(Finset.range ((Finset.range M.d).prod (fun j=>M.d-j))).prod
            (fun j=>(Finset.range M.d).prod (fun j=>M.d-j)-j) ∧
          R.E.length=M.E.length+T.length ∧
          ∀a b : ℕ,0<b→b≤a→
            ((((R.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n R.N R.ideal z) ↔
              WeightedAlongAt Φ hSrc h0 s (contactWeight l a b) (geoTransformAlong M T).ideal (M.d*a)) := by
  have hCurrent:=isInvDomain_geoTransformAlong hC T hT
  have hzN : z.val∈(geoTransformAlong C T).N:=
    MaximalContactAlongTower.strictAlong_subset_N C (fun _ hx=>hx.1) T hzS
  obtain ⟨Ω,hzΩ,hΩU,uT,huT,hStrict⟩:=exists_isTangentDirectionAlong_stage C
    hC.isWellFormed.isClosedSubmanifold_N hC.isWellFormed.isCoherent hC.one_le_d U hu T hT hzN z.property
  have hzZero : uT z.val=0:=((Set.ext_iff.mp hStrict z.val).mpr ⟨hzS,hzΩ⟩).1.2
  obtain ⟨s,hs,hsn,l,hl,Φ,hSrc,h0,hCoords,_hLoss⟩:=actual_contact_weighted_derivatives
    hCurrent.isWellFormed.isCoherent hCurrent.isWellFormed.isClosedSubmanifold_N huT z.val ⟨hzN,hzΩ,hzZero⟩
  have hStrictFlat : ∀{y : Y},y∈(chartAt (ComplexModel n) z.val).source→
      chartAt (ComplexModel n) z.val y∈Φ.source→
        (y∈strictAlong T (C.N∩{x | u x=0}) ↔
          Φ.toFun (chartAt (ComplexModel n) z.val y)∈complexCoordinatePlane n (s-1)):=by
    intro y hy hyΦ
    have hyΩ:=(hCoords y ⟨hy,hyΦ⟩).1
    have hEq : y∈strictAlong T (C.N∩{x | u x=0}) ↔ y∈(geoTransformAlong C T).N∩{y | uT y=0}:=
      ⟨fun h=>((Set.ext_iff.mp hStrict y).mpr ⟨h,hyΩ⟩).1,
        fun h=>((Set.ext_iff.mp hStrict y).mp ⟨h,hyΩ⟩).1⟩
    exact hEq.trans (hCoords y ⟨hy,hyΦ⟩).2.2.2
  refine ⟨Ω,hzΩ,hΩU,uT,huT,s,hs,hsn,l,hl,Φ,hSrc,h0,?_,?_⟩
  · intro y hy
    exact ⟨(hCoords y hy).1,(hCoords y hy).2.1,(hCoords y hy).2.2.1,
      hStrictFlat hy.1 hy.2⟩
  · intro M q hM hMN hTM
    let Z:=openPreimage T U
    let B:=coeffMarkedAlong (homMarkedAlong M)
    let A:=geoTransformAlong B T
    let R:=contactMarkedKept M u T Z
    obtain ⟨_hB,hA,_hBT,hAN,hAE,hAd,hALen,hWeighted⟩:=original_bar_weighted_history M hM T hTM
    have hNMC : (geoTransformAlong M T).N=(geoTransformAlong C T).N:=by
      rw [N_geoTransformAlong,N_geoTransformAlong,hMN]
    have hFlatM : ∀{y : Y},y∈(chartAt (ComplexModel n) z.val).source→
        chartAt (ComplexModel n) z.val y∈Φ.source→
          (y∈(geoTransformAlong M T).N ↔
            Φ.toFun (chartAt (ComplexModel n) z.val y)∈complexCoordinatePlane n s):=by
      rw [hNMC]
      exact fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1
    have hFlatA : ∀{y : Y},y∈(chartAt (ComplexModel n) z.val).source→
        chartAt (ComplexModel n) z.val y∈Φ.source→
          (y∈A.N ↔ Φ.toFun (chartAt (ComplexModel n) z.val y)∈complexCoordinatePlane n s):=by
      rw [hAN]
      exact hFlatM
    have hSM : strictAlong T (M.N∩{x | u x=0})=strictAlong T (C.N∩{x | u x=0}):=by rw [hMN]
    have hCoeff : (coeffMarkedAlong A).ideal.IsCoherent:=
      isCoherent_coeffMarkedAlong hA.isWellFormed.isCoherent hA.isWellFormed.isClosedSubmanifold_N
    have hOrd:=native_order_pullback_open hCoeff Z z
      (show z.val∈strictAlong T (M.N∩{x | u x=0}) by rw [hSM];exact hzS)
    refine ⟨?_,?_,?_,?_,?_⟩
    · change (Subtype.val : Z→Y) ⁻¹' strictAlong T (M.N∩{x | u x=0})=_
      rw [hSM]
    · change A.E.map ((Subtype.val : Z→Y) ⁻¹' ·)=(geoTransformAlong M T).E.map _
      rw [hAE]
    · change (Finset.range A.d).prod (fun j=>A.d-j)=_
      rw [hAd]
    · change (A.E.map ((Subtype.val : Z→Y) ⁻¹' ·)).length=_
      rw [List.length_map]
      exact hALen
    · intro a b hb hba
      change (((R.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        ((Subtype.val : Z→Y) ⁻¹' strictAlong T (M.N∩{x | u x=0}))
        (GermIdeal.pullback (m:=n) (Subtype.val : Z→Y) (coeffMarkedAlong A).ideal) z ↔_)
      rw [hOrd,hSM]
      have hDictionary:=coefficient_contact_in_coordinates Φ hSrc h0 s hFlatA hStrictFlat
        hA.isWellFormed.isClosedSubmanifold_N l hl hA.isWellFormed.isCoherent A.d a b hA.one_le_d hb hba
      change (((R.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        (strictAlong T (C.N∩{x | u x=0})) (coeffMarkedAlong A).ideal z.val) ↔
          WeightedAlongAt Φ hSrc h0 s (contactWeight l a b) A.ideal (A.d*a) at hDictionary
      rw [hDictionary,hAd]
      have hWeights : ∀j,contactWeight l a b j≤a:=by
        intro j
        dsimp only [contactWeight]
        split_ifs
        · exact le_rfl
        · exact hba
      exact hWeighted z.val s Φ hSrc h0 hFlatM (contactWeight l a b) a hWeights

private theorem contact_stage_fields {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (w : X→ℂ) (V : TopologicalSpace.Opens Y) :
    let R:=contactMarkedKept M w T V
    R.E=(geoTransformAlong M T).E.map ((Subtype.val : V→Y) ⁻¹' ·) ∧
    R.d=(Finset.range ((Finset.range M.d).prod (fun j=>M.d-j))).prod
      (fun j=>(Finset.range M.d).prod (fun j=>M.d-j)-j) ∧
    R.E.length=M.E.length+T.length := by
  obtain ⟨_hB,_hBT,_hTest,_hN,hE,hd,hLen,_hW⟩:=original_bar_weighted_history M hM T hT
  refine ⟨?_,?_,?_⟩
  · change (geoTransformAlong (coeffMarkedAlong (homMarkedAlong M)) T).E.map _=_
    rw [hE]
  · change (Finset.range (geoTransformAlong (coeffMarkedAlong (homMarkedAlong M)) T).d).prod
      (fun j=>(geoTransformAlong (coeffMarkedAlong (homMarkedAlong M)) T).d-j)=_
    rw [hd]
  · change ((geoTransformAlong (coeffMarkedAlong (homMarkedAlong M)) T).E.map _).length=_
    rw [List.length_map]
    exact hLen

/- The actual public endpoint derives every one of these already-held upper
history data from ordinary406/1551 inputs; no lower/future packet is public. -/
private theorem paired_contact_stage {kJ kK : ℕ} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K) (hNK : J.N=K.N)
    (U₀ : TopologicalSpace.Opens X) {w : X→ℂ}
    (hwK : IsTangentDirectionAlong K.N K.ideal K.d U₀ w)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (hTK : IsGeoTestTower K T)
    (hNT : (geoTransformAlong J T).N=(geoTransformAlong K T).N)
    (hET : (geoTransformAlong J T).E=(geoTransformAlong K T).E)
    (hLenJ : (geoTransformAlong J T).E.length=T.length)
    (hLenK : (geoTransformAlong K T).E.length=T.length)
    (hUpper : ∀(z : Y)(s : ℕ)(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
      (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
      (∀{y : Y},y∈(chartAt (ComplexModel n) z).source→chartAt (ComplexModel n) z y∈Φ.source→
        (y∈(geoTransformAlong J T).N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s))→
      ∀(v : Fin n→ℕ)(a : ℕ),(∀i,v i≤a)→
        (WeightedAlongAt Φ hSrc h0 s v (geoTransformAlong J T).ideal (J.d*a) ↔
         WeightedAlongAt Φ hSrc h0 s v (geoTransformAlong K T).ideal (K.d*a))) :
    let Z:=openPreimage T U₀
    let RJ:=contactMarkedKept J w T Z
    let RK:=contactMarkedKept K w T Z
    RJ.N=RK.N ∧ RJ.E=RK.E ∧
    RJ.d=(Finset.range ((Finset.range J.d).prod (fun j=>J.d-j))).prod
      (fun j=>(Finset.range J.d).prod (fun j=>J.d-j)-j) ∧
    RK.d=(Finset.range ((Finset.range K.d).prod (fun j=>K.d-j))).prod
      (fun j=>(Finset.range K.d).prod (fun j=>K.d-j)-j) ∧
    RJ.E.length=T.length ∧ RK.E.length=T.length ∧
    ∀z : Z,z.val∈strictAlong T (K.N∩{y | w y=0})→∀a b : ℕ,0<b→b≤a→
      ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RJ.ideal z) ↔
        (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RK.N RK.ideal z)) := by
  let Z:=openPreimage T U₀
  let RJ:=contactMarkedKept J w T Z
  let RK:=contactMarkedKept K w T Z
  obtain ⟨hEJ,hdJ,_hRLJ⟩:=contact_stage_fields J hJ T hTJ w Z
  obtain ⟨hEK,hdK,_hRLK⟩:=contact_stage_fields K hK T hTK w Z
  refine ⟨?_,?_,hdJ,hdK,?_,?_,?_⟩
  · change (Subtype.val : Z→Y) ⁻¹' strictAlong T (J.N∩{y | w y=0})=
      (Subtype.val : Z→Y) ⁻¹' strictAlong T (K.N∩{y | w y=0})
    rw [hNK]
  · rw [hEJ,hEK,hET]
  · rw [hEJ,List.length_map,hLenJ]
  · rw [hEK,List.length_map,hLenK]
  · intro z hzS
    obtain ⟨_Ω,_hzΩ,_hΩU,_uT,_huT,s,_hs,_hsn,l,_hl,Φ,hSrc,h0,hCoords,hDictionary⟩:=
      original_open_contact_weighted_dictionary K hK U₀ hwK T hTK z hzS
    obtain ⟨_hNJR,_hEJR,_hDJA,_hLenJR,hDJ⟩:=hDictionary J hJ hNK hTJ
    obtain ⟨_hNKR,_hEKR,_hDKA,_hLenKR,hDK⟩:=hDictionary K hK rfl hTK
    have hFlatJ : ∀{y : Y},y∈(chartAt (ComplexModel n) z.val).source→
        chartAt (ComplexModel n) z.val y∈Φ.source→
          (y∈(geoTransformAlong J T).N ↔
            Φ.toFun (chartAt (ComplexModel n) z.val y)∈complexCoordinatePlane n s):=by
      rw [hNT]
      exact fun {y} hy hyΦ=>(hCoords y ⟨hy,hyΦ⟩).2.1
    intro a b hb hba
    have hWeights : ∀j,contactWeight l a b j≤a:=by
      intro j
      dsimp only [contactWeight]
      split_ifs
      · exact le_rfl
      · exact hba
    have hCuts:=hUpper z.val s Φ hSrc h0 hFlatJ (contactWeight l a b) a hWeights
    exact (hDJ a b hb hba).trans (hCuts.trans (hDK a b hb hba).symm)

/-- Actual original J/K lower records at EVERY original UPPER history, on the SAME openPreimage. -/
theorem original_lower_common_contact_history_thresholds {A : CMfd.{0} n}
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
      ∃hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.d=μ ∧ K.d=e*μ ∧
        (⟨x,hxU⟩ : U)∈J.cosupp ∧ (⟨x,hxU⟩ : U)∈K.cosupp ∧
        ∀z₀∈K.cosupp,∃hOpen : IsOpen (tangentChoice K z₀).1,
          let U₀ : TopologicalSpace.Opens (CMfd.of (n:=n) U):=⟨(tangentChoice K z₀).1,hOpen⟩
          ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T→
            IsGeoTestTower K T ∧
            let Z:=openPreimage T U₀
            let RJ:=contactMarkedKept J (tangentChoice K z₀).2 T Z
            let RK:=contactMarkedKept K (tangentChoice K z₀).2 T Z
            RJ.N=RK.N ∧ RJ.E=RK.E ∧
            RJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
              (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
            RK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
              (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
            RJ.E.length=T.length ∧ RK.E.length=T.length ∧
            ∀z : Z,z.val∈strictAlong T (K.N∩{y | (tangentChoice K z₀).2 y=0})→
              ∀a b : ℕ,0<b→b≤a→
                ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RJ.ideal z) ↔
                  (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RK.N RK.ideal z)) := by
  obtain ⟨hm,hxU,hJ,hK,hNK,hJd,hKd,hzJ,hzK,_hIncl,hContact⟩:=
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
  obtain ⟨_hmW,_hxUW,_hNatural,_hJdW,_hKdW,hHist⟩:=
    original_lower_weighted_histories hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJd,hKd,hzJ,hzK,?_⟩
  intro z₀ hz₀
  obtain ⟨_hzU₀,huK,_huJ,_hZeroJ,_hZeroK⟩:=hContact z₀ hz₀
  let U₀ : TopologicalSpace.Opens (CMfd.of (n:=n) U):=⟨(tangentChoice K z₀).1,huK.isOpen⟩
  refine ⟨huK.isOpen,?_⟩
  dsimp only
  intro Y T hTJ
  obtain ⟨hTK,hNT,hET,hLenJ,hLenK,hUpper⟩:=hHist T hTJ
  have hUpperNative : ∀(z : Y)(s : ℕ)(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
      (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
      (∀{y : Y},y∈(chartAt (ComplexModel n) z).source→chartAt (ComplexModel n) z y∈Φ.source→
        (y∈(geoTransformAlong J T).N ↔ Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s))→
      ∀(v : Fin n→ℕ)(a : ℕ),(∀i,v i≤a)→
        (WeightedAlongAt Φ hSrc h0 s v (geoTransformAlong J T).ideal (J.d*a) ↔
         WeightedAlongAt Φ hSrc h0 s v (geoTransformAlong K T).ideal (K.d*a)):=by
    intro z s Φ hSrc h0 hFlat v a hv
    simpa only [hJd,hKd] using hUpper z s Φ hSrc h0 hFlat v a hv
  refine ⟨hTK,?_⟩
  simpa only [hJd,hKd] using paired_contact_stage J K hJ hK hNK U₀ huK T hTJ hTK
    hNT hET hLenJ hLenK hUpperNative

end
end Hironaka.HironakaActualOriginalStrictContactWeightedOrder
