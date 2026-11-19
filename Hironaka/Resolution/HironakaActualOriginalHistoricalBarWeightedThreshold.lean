import Hironaka.Resolution.HironakaActualContactWeightedCoefficientThreshold
import Hironaka.Resolution.HironakaActualTrueMarkCoefficientHistorySandwich

/-! ORIGINAL historical homogenization/bar transport on actual proper carriers.
Blueprint FIRST: hironaka-actual-original-historical-bar-weighted-threshold.tex.
The local finite-span weighted helper arguments repeat the frozen1551 calculus
because those helpers are private; they receive ZERO new mathematical-engine credit.
The new conclusions concern actual ORIGINAL hom/bar transforms and clocks. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalHistoricalBarWeightedThreshold
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualContactWeightedCoefficientThreshold HironakaActualTrueMarkCoefficientHistorySandwich
  RelativePrincipalizationSpan BlowupTowers BlowupFlatCoordinates BlowupSNCTransform GiraudAlong
  DerivativeIdealAlong DerivativeIdealAlongCoherent RegularPointDimension RegularPatchPullback HadamardBridgeAlong
  RestrictedIdealWeight IdealWeightPowers GermIdealPullbackCalculus HomogenizedGlueing HomogenizedEquivalence
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualRelativeCoefficientGerms HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalTaylorCoefficients
  HironakaActualOriginalFormalTaylor HironakaHolomorphicPointJets
  ResolutionInvariantSpec InvDomainTowerAlong BlowupTowerTransforms MarkedIdealBiholomorphism
  HironakaActualInitialNonmonomialCoefficientBoundary
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


private theorem hol {Y : CMfd.{u} n} {I : GermIdeal n Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem hom_domain {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    IsInvDomain k (homMarkedAlong M) where
  isWellFormed:=⟨hM.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hM.isWellFormed.isCoherent hM.isWellFormed.isClosedSubmanifold_N,
    hM.isWellFormed.isSNCDivisor,hM.isWellFormed.isTransverse⟩
  dimLE:=hM.dimLE
  one_le_d:=hM.one_le_d
  isNonzeroAlongAt:=by
    intro z hz
    obtain ⟨f,hf,hFreq⟩:=hM.isNonzeroAlongAt z hz
    exact ⟨f,le_homogenizedIdealAlong (hol hM.isWellFormed.isCoherent) hM.one_le_d z f hf,hFreq⟩

/-- Whole ORIGINAL hom transforms, with all proper carriers and original clocks. -/
theorem original_homogenization_history_sandwich {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let H:=homMarkedAlong M
    IsGeoTestTower H T ∧ (geoTransformAlong H T).N=(geoTransformAlong M T).N ∧
    (geoTransformAlong H T).E=(geoTransformAlong M T).E ∧ (geoTransformAlong H T).d=M.d ∧
    (geoTransformAlong H T).E.length=M.E.length+T.length ∧
    (geoTransformAlong M T).E.length=M.E.length+T.length ∧
    (geoTransformAlong M T).ideal.Le (geoTransformAlong H T).ideal ∧
    RestrictLe (geoTransformAlong M T).N (geoTransformAlong H T).ideal
      (homogenizedIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal M.d) := by
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hI:=hM.isWellFormed.isCoherent
  have hCurrent:=isInvDomain_geoTransformAlong hM T hT
  have hNC:=hCurrent.isWellFormed.isClosedSubmanifold_N
  have hIC:=hCurrent.isWellFormed.isCoherent
  obtain ⟨hHT,hHC,hEq⟩:=hom_tower_along M hN hI hM.one_le_d T hT
  have hLower:=lower_mark_transform (A:=M) (B:=homMarkedAlong M) rfl rfl
    (le_homogenizedIdealAlong (hol hI) hM.one_le_d) le_rfl T
  have hDi : ∀i,i≤M.d→RestrictLe (geoTransformAlong M T).N
      (geoTransformAlong (derivMarkedAlong M i) T).ideal
      (iterDerivIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal i):=
    fun i hi=>(inclusions_tower_along M hN hI hi T hT).2.2.2.2.2.2
  have hUpper : RestrictLe (geoTransformAlong M T).N (homTower M T).ideal
      (homogenizedIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal M.d):=
    restrictLe_homSum (fun i _=>hol (isCoherent_iterDerivIdealAlong hIC hNC i))
      (hol (isCoherent_iterDerivIdealAlong hIC hNC (M.d-1)))
      (fun i hi=>hDi i hi.le) (hDi (M.d-1) (Nat.sub_le _ _))
  have hHistLe:=hEq.le
  rw [←hLower.1] at hHistLe
  exact ⟨hHT,hLower.1.symm,hLower.2.1.symm,d_geoTransformAlong _ T,
    length_E_geoTransformAlong _ T,length_E_geoTransformAlong _ T,
    hLower.2.2.1,RestrictLeCalculus.RestrictLe.trans hHistLe hUpper⟩

/-- The ORIGINAL historical hom has the normalized weighted cut of the ORIGINAL current ideal. -/
theorem original_homogenization_weighted_history {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let H:=homMarkedAlong M
    IsInvDomain k H ∧ IsInvDomain k (geoTransformAlong H T) ∧
    ∀(z : Y)(s : ℕ)(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
      (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
      (∀{y : Y},y∈(chartAt (ComplexModel n) z).source→
        chartAt (ComplexModel n) z y∈Φ.source→
          (y∈(geoTransformAlong M T).N ↔
            Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s))→
      ∀(w : Fin n→ℕ)(a : ℕ),(∀i,w i≤a)→
        (WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong H T).ideal (M.d*a) ↔
          WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong M T).ideal (M.d*a)) := by
  obtain ⟨hHT,_hNT,_hET,_hMark,_hLenH,_hLenM,hLow,hHigh⟩:=
    original_homogenization_history_sandwich M hM T hT
  have hH:=hom_domain M hM
  have hHC:=isInvDomain_geoTransformAlong hH T hHT
  have hMC:=isInvDomain_geoTransformAlong hM T hT
  refine ⟨hH,hHC,?_⟩
  intro z s Φ hSrc h0 hFlat w a hWeights
  constructor
  · exact weighted_mono Φ hSrc h0 s w (M.d*a) hLow
  · intro h
    apply weighted_restrictLe Φ hSrc h0 s hFlat w (M.d*a)
      (isCoherent_homogenizedIdealAlong hMC.isWellFormed.isCoherent
        hMC.isWellFormed.isClosedSubmanifold_N M.d) hHigh
    exact (weighted_homogenized_iff Φ hSrc h0 s hFlat hMC.isWellFormed.isClosedSubmanifold_N
      w a hWeights hMC.isWellFormed.isCoherent M.d hM.one_le_d).mpr h

private theorem recoded_own_eq (M : MarkedIdeal n X) (hm : 1≤M.d) :
    recodedCoefficient M M.d=coeffMarkedAlong M := by
  have hMark : sumExp (fun j=>M.d-j) M.d 0*M.d=(coeffMarkedAlong M).d:=by
    change sumExp (fun j=>M.d-j) M.d 0*M.d=(Finset.range M.d).prod (fun j=>M.d-j)
    rw [Nat.mul_comm]
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>M.d-j) (show 0<M.d from hm) (i:=0)
  change {coeffMarkedAlong M with d:=sumExp (fun j=>M.d-j) M.d 0*M.d}=coeffMarkedAlong M
  rw [hMark]

/-- ORIGINAL bar transport, exact native product mark and ALL full original clocks. -/
theorem original_bar_weighted_history {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let B:=coeffMarkedAlong (homMarkedAlong M)
    let D:=(Finset.range M.d).prod (fun j=>M.d-j)
    IsInvDomain k B ∧ IsInvDomain k (geoTransformAlong B T) ∧ IsGeoTestTower B T ∧
    (geoTransformAlong B T).N=(geoTransformAlong M T).N ∧
    (geoTransformAlong B T).E=(geoTransformAlong M T).E ∧ (geoTransformAlong B T).d=D ∧
    (geoTransformAlong B T).E.length=M.E.length+T.length ∧
    ∀(z : Y)(s : ℕ)(Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) z z))
      (hSrc : Φ.source⊆(chartAt (ComplexModel n) z).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) z z)=0),
      (∀{y : Y},y∈(chartAt (ComplexModel n) z).source→
        chartAt (ComplexModel n) z y∈Φ.source→
          (y∈(geoTransformAlong M T).N ↔
            Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s))→
      ∀(w : Fin n→ℕ)(a : ℕ),(∀i,w i≤a)→
        (WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong B T).ideal (D*a) ↔
          WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong M T).ideal (M.d*a)) := by
  let H:=homMarkedAlong M
  let B:=coeffMarkedAlong H
  let e:=sumExp (fun j=>M.d-j) M.d 0
  let D:=(Finset.range M.d).prod (fun j=>M.d-j)
  obtain ⟨hHT,hHN,hHE,_hHm,_hHLen,_hMLen,_hLowH,_hHighH⟩:=
    original_homogenization_history_sandwich M hM T hT
  have hH:=hom_domain M hM
  have hB:=coefficient_isInvDomain H hH
  obtain ⟨hBT,hBN,hBE,_hBd,hLow,hHigh,hLen⟩:=
    recoded_coefficient_history_sandwich H hH H.d hH.one_le_d le_rfl T hHT
  have hSource : recodedCoefficient H H.d=B:=recoded_own_eq H hH.one_le_d
  rw [hSource] at hBT hBN hBE hLow hHigh hLen
  have hBC:=isInvDomain_geoTransformAlong hB T hBT
  have hHC:=isInvDomain_geoTransformAlong hH T hHT
  have hMark : e*M.d=D:=by
    rw [Nat.mul_comm]
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>M.d-j) (show 0<M.d from hM.one_le_d) (i:=0)
  refine ⟨hB,hBC,hBT,hBN.trans hHN,hBE.trans hHE,d_geoTransformAlong B T,hLen,?_⟩
  intro z s Φ hSrc h0 hFlat w a hWeights
  have hFlatH : ∀{y : Y},y∈(chartAt (ComplexModel n) z).source→
      chartAt (ComplexModel n) z y∈Φ.source→
        (y∈(geoTransformAlong H T).N ↔
          Φ.toFun (chartAt (ComplexModel n) z y)∈complexCoordinatePlane n s):=by
    rw [hHN]
    exact hFlat
  have hWeighted:=(weighted_sandwich_iff Φ hSrc h0 s hFlatH hHC.isWellFormed.isClosedSubmanifold_N
    hHC.isWellFormed.isCoherent hBC.isWellFormed.isCoherent M.d M.d hM.one_le_d le_rfl
    hLow hHigh w a hWeights)
  change WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong B T).ideal (e*M.d*a) ↔
    WeightedAlongAt Φ hSrc h0 s w (geoTransformAlong H T).ideal (M.d*a) at hWeighted
  rw [hMark] at hWeighted
  exact hWeighted.trans ((original_homogenization_weighted_history M hM T hT).2.2
    z s Φ hSrc h0 hFlat w a hWeights)

end
end Hironaka.HironakaActualOriginalHistoricalBarWeightedThreshold
