import Hironaka.Resolution.HironakaActualHistoricalWholeJetFrames

/-! Homogeneous frames for every old historical prefix, on one actual
nearby constant-HS window. The member functions are the same historical
functions; no translated monic heads or prefix-rank certificate is supplied. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalPrefixJetFrames
noncomputable section
open HolGerm HironakaHolomorphicPointJets
 HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
 HironakaActualHistoricalWholeJetFrames HironakaActualCauchyCoordinateDivision
 HironakaActualCauchyNeumannDivision HironakaActualCauchyMonomialDivision
 HironakaActualCauchyEnumeratedPartition HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

/-- The actual homogeneous degree, including the degree-zero case. -/
abbrev homogeneousExponentIndex (n d : ℕ) :=
  {α : Fin n →₀ ℕ // normalExponentDegree α=d}

@[instance_reducible] def homogeneousExponentFintype (n d : ℕ) : Fintype (homogeneousExponentIndex n d) := by
  letI:=normalExponentFintype n (d+1)
  exact Fintype.ofInjective
    (fun α : homogeneousExponentIndex n d=>(⟨α.val,by rw [α.property]; omega⟩ : normalExponentIndex n (d+1)))
    (fun a b h=>Subtype.ext (congrArg (fun z : normalExponentIndex n (d+1)=>z.val) h))

def homogeneousCoefficients (d : ℕ) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] (homogeneousExponentIndex n d → ℂ) :=
  LinearMap.pi fun α=>MvPowerSeries.coeff α.val

/-- Literal homogeneous polynomial lift, with no quotient or rank data. -/
def homogeneousSeries (d : ℕ) :
    (homogeneousExponentIndex n d → ℂ) →ₗ[ℂ] MvPowerSeries (Fin n) ℂ := by
  classical
  exact {
    toFun:=fun c α=>if hα : normalExponentDegree α=d then c ⟨α,hα⟩ else 0
    map_add':=by
      intro c e
      ext α
      change (if hα : normalExponentDegree α=d then (c+e) ⟨α,hα⟩ else 0)=
        (if hα : normalExponentDegree α=d then c ⟨α,hα⟩ else 0)+
        (if hα : normalExponentDegree α=d then e ⟨α,hα⟩ else 0)
      split_ifs <;> simp
    map_smul':=by
      intro r c
      ext α
      change (if hα : normalExponentDegree α=d then r*c ⟨α,hα⟩ else 0)=
        r*(if hα : normalExponentDegree α=d then c ⟨α,hα⟩ else 0)
      split_ifs <;> simp }

def historicalHomogeneousOperator (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (d : ℕ) :
    (homogeneousExponentIndex n d → ℂ) →ₗ[ℂ] (homogeneousExponentIndex n d → ℂ) :=
  (homogeneousCoefficients d).comp ((historicalReassemble w g).comp (homogeneousSeries d))

/-- The genuinely marked historical operator commutes with every actual
truncation. This is the filtered square used for the homogeneous blocks. -/
theorem historicalWholeJetMap_truncation (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    historicalWholeJetMap w g q (boundedCoefficients q F)=
      boundedCoefficients q (historicalReassemble w g F) := by
  rw [historicalWholeJetMap_eq_operator]
  have hm:=historicalReassemble_mem_power w g hmarked (sub_boundedSeries_mem_power q F)
  rw [map_sub] at hm
  exact ((boundedCoefficients_eq_iff q _ _).mpr hm).symm

/-- Whole-jet bijections at the adjacent actual truncations induce a
homogeneous block bijection, with no determinant or graded rank premise. -/
theorem historicalHomogeneousOperator_bijective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) (d : ℕ) :
    Function.Bijective (historicalHomogeneousOperator w g d) := by
  classical
  let :=homogeneousExponentFintype n d
  have hsurj : Function.Surjective (historicalHomogeneousOperator w g d) := by
    intro v
    obtain ⟨x,hx⟩:=(hwhole (d+1)).2 (boundedCoefficients (d+1) (homogeneousSeries d v))
    let F:=boundedSeries (d+1) x
    have hOutput : boundedCoefficients (d+1) (historicalReassemble w g F)=
        boundedCoefficients (d+1) (homogeneousSeries d v) := by
      rw [historicalWholeJetMap_eq_operator] at hx
      exact hx
    have hlow : boundedCoefficients d F=0 := by
      apply (hwhole d).1
      rw [historicalWholeJetMap_truncation w g hmarked,map_zero]
      funext α
      have hα : normalExponentDegree α.val<d+1:=by omega
      have he:=congrFun hOutput (⟨α.val,hα⟩ : normalExponentIndex n (d+1))
      change MvPowerSeries.coeff α.val (historicalReassemble w g F)=0
      change MvPowerSeries.coeff α.val (historicalReassemble w g F)=
        (if h : normalExponentDegree α.val=d then v ⟨α.val,h⟩ else 0) at he
      exact he.trans (dif_neg (by omega))
    have hF : F=homogeneousSeries d (homogeneousCoefficients d F) := by
      ext α
      change MvPowerSeries.coeff α F=
        (if h : normalExponentDegree α=d then MvPowerSeries.coeff α F else 0)
      by_cases hd : normalExponentDegree α=d
      · rw [dif_pos hd]
      rw [dif_neg hd]
      by_cases hl : normalExponentDegree α<d
      · exact congrFun hlow (⟨α,hl⟩ : normalExponentIndex n d)
      · change (if h : normalExponentDegree α<d+1 then x ⟨α,h⟩ else 0)=0
        exact dif_neg (by omega)
    refine ⟨homogeneousCoefficients d F,?_⟩
    funext α
    have hα : normalExponentDegree α.val<d+1:=by rw [α.property]; omega
    have he:=congrFun hOutput (⟨α.val,hα⟩ : normalExponentIndex n (d+1))
    rw [hF] at he
    change MvPowerSeries.coeff α.val
      (historicalReassemble w g (homogeneousSeries d (homogeneousCoefficients d F)))=
        (if h : normalExponentDegree α.val=d then v ⟨α.val,h⟩ else 0) at he
    exact he.trans (dif_pos α.property)
  exact ⟨(LinearMap.injective_iff_surjective).mpr hsurj,hsurj⟩

def historicalHomogeneousColumnMap (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (d : ℕ) :
    (homogeneousExponentIndex n d → ℂ) →ₗ[ℂ] (homogeneousExponentIndex n d → ℂ) := by
  classical
  letI:=homogeneousExponentFintype n d
  exact {
    toFun:=fun c α=>∑β,c β*MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val)
    map_add':=by
      intro c e
      funext α
      simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
    map_smul':=by
      intro r c
      funext α
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,Finset.mul_sum] }

theorem homogeneousSeries_eq_sum (d : ℕ) (v : homogeneousExponentIndex n d → ℂ) :
    homogeneousSeries d v=by
      classical
      let :=homogeneousExponentFintype n d
      exact ∑α,MvPowerSeries.monomial α.val (v α) := by
  classical
  let :=homogeneousExponentFintype n d
  ext α
  change (if hα : normalExponentDegree α=d then v ⟨α,hα⟩ else 0)=_
  rw [map_sum]
  by_cases hα : normalExponentDegree α=d
  · rw [dif_pos hα]
    let a : homogeneousExponentIndex n d:=⟨α,hα⟩
    symm
    rw [Finset.sum_eq_single a]
    · exact MvPowerSeries.coeff_monomial_same α (v a)
    · intro β _ hβ
      have hne : β.val≠α:=fun h=>hβ (Subtype.ext h)
      rw [MvPowerSeries.coeff_monomial,if_neg (Ne.symm hne)]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  · rw [dif_neg hα]
    symm
    apply Finset.sum_eq_zero
    intro β _
    have hne : β.val≠α:=fun h=>hα (h ▸ β.property)
    rw [MvPowerSeries.coeff_monomial,if_neg (Ne.symm hne)]

private theorem monomial_scalar (α : Fin n →₀ ℕ) (c : ℂ) :
    (MvPowerSeries.monomial α c : MvPowerSeries (Fin n) ℂ)=c • MvPowerSeries.monomial α 1 := by
  ext β
  rw [map_smul]
  simp only [MvPowerSeries.coeff_monomial,smul_eq_mul]
  split_ifs <;> simp

/-- The graded map is exactly the displayed homogeneous supported-column
matrix, rather than an abstract isomorphism of unnamed jet spaces. -/
theorem historicalHomogeneousColumnMap_eq_operator (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (d : ℕ) :
    historicalHomogeneousColumnMap w g d=historicalHomogeneousOperator w g d := by
  classical
  let :=homogeneousExponentFintype n d
  apply LinearMap.ext
  intro c
  funext α
  change (∑β,c β*MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val))=
    MvPowerSeries.coeff α.val (historicalReassemble w g (homogeneousSeries d c))
  rw [homogeneousSeries_eq_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [monomial_scalar β.val (c β),map_smul,historicalReassemble_monomial,map_smul]
  rfl

theorem historicalHomogeneousColumnMap_bijective_of_neumann {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,actualUnshiftedTaylorAlgHom n (HironakaActualCauchyTaylorSupport.modelGerm hr
      ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w j))) (d : ℕ) :
    Function.Bijective (historicalHomogeneousColumnMap w
      (fun j=>actualUnshiftedTaylorAlgHom n (HironakaActualCauchyTaylorSupport.modelGerm hr
        ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))) d) := by
  rw [historicalHomogeneousColumnMap_eq_operator]
  exact historicalHomogeneousOperator_bijective w _ hmarked
    (historicalWholeJetMap_bijective_of_neumann hr w D H hH hHb hmarked) d

/-- A genuinely owned old head cannot acquire a higher order: its actual
column would vanish in a whole jet where the old basis vector is nonzero. -/
theorem historicalWholeJetMap_member_not_mem_succ (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (j : Fin k)
    (howner : historicalOwner w (wordExponent (w j))=some j)
    (hinj : Function.Injective (historicalWholeJetMap w g
      (normalExponentDegree (wordExponent (w j))+1))) :
    g j∉genuineFormalVariables n^(normalExponentDegree (wordExponent (w j))+1) := by
  classical
  let q:=normalExponentDegree (wordExponent (w j))+1
  let :=normalExponentFintype n q
  let a : normalExponentIndex n q:=⟨wordExponent (w j),by dsimp only [q]; omega⟩
  let v : normalExponentIndex n q → ℂ:=fun β=>if β=a then 1 else 0
  intro hhigh
  have hc : historicalWholeColumn w g a.val=g j:=by
    change historicalWholeColumn w g (wordExponent (w j))=g j
    simp only [historicalWholeColumn,howner,tsub_self,MvPowerSeries.monomial_zero_one,one_mul]
  have hz : historicalWholeJetMap w g q v=0:=by
    funext α
    change (∑β,v β*MvPowerSeries.coeff α.val (historicalWholeColumn w g β.val))=0
    rw [Finset.sum_eq_single a]
    · simp only [v,if_pos rfl,one_mul,hc]
      exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hhigh α.val α.property
    · intro β _ hβ
      simp only [v,if_neg hβ,zero_mul]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  have hv : v=0:=hinj (hz.trans (map_zero _).symm)
  have he : (1 : ℂ)=0:=by simpa only [v,if_pos rfl,Pi.zero_apply] using congrFun hv a
  exact one_ne_zero he

/-- A fixed degree-first order with the original label as tie breaker.
This keeps literal degree prefixes, independently of the old enumeration. -/
def historicalDegreeKey (w : Fin k → CoordinateWord n) (j : Fin k) : Lex (ℕ × Fin k) :=
  toLex (normalExponentDegree (wordExponent (w j)),j)

def historicalDegreePrefixKeys (w : Fin k → CoordinateWord n) (m : ℕ) : Finset (Lex (ℕ × Fin k)) :=
  (Finset.univ.filter (fun j=>normalExponentDegree (wordExponent (w j))≤m)).image (historicalDegreeKey w)

def historicalDegreePrefixCount (w : Fin k → CoordinateWord n) (m : ℕ) : ℕ :=
  (historicalDegreePrefixKeys w m).card

def historicalDegreePrefixLabel (w : Fin k → CoordinateWord n) (m : ℕ)
    (j : Fin (historicalDegreePrefixCount w m)) : Fin k :=
  (ofLex ((historicalDegreePrefixKeys w m).orderIsoOfFin rfl j).val).2

theorem historicalDegreePrefixLabel_mem (w : Fin k → CoordinateWord n) (m : ℕ)
    (j : Fin (historicalDegreePrefixCount w m)) :
    normalExponentDegree (wordExponent (w (historicalDegreePrefixLabel w m j)))≤m := by
  have he:=((historicalDegreePrefixKeys w m).orderIsoOfFin rfl j).property
  obtain ⟨a,ha,heq⟩:=Finset.mem_image.mp he
  have hl : a=historicalDegreePrefixLabel w m j:=
    congrArg (fun v : Lex (ℕ × Fin k)=>(ofLex v).2) heq
  rw [←hl]
  exact (Finset.mem_filter.mp ha).2

theorem historicalDegreePrefixLabel_key (w : Fin k → CoordinateWord n) (m : ℕ)
    (j : Fin (historicalDegreePrefixCount w m)) :
    historicalDegreeKey w (historicalDegreePrefixLabel w m j)=
      ((historicalDegreePrefixKeys w m).orderIsoOfFin rfl j).val := by
  have he:=((historicalDegreePrefixKeys w m).orderIsoOfFin rfl j).property
  obtain ⟨a,_ha,heq⟩:=Finset.mem_image.mp he
  have hl : a=historicalDegreePrefixLabel w m j:=
    congrArg (fun v : Lex (ℕ × Fin k)=>(ofLex v).2) heq
  rw [←hl]
  exact heq

def historicalDegreePrefixLabelEquiv (w : Fin k → CoordinateWord n) (m : ℕ) :
    Fin (historicalDegreePrefixCount w m) ≃
      {j : Fin k // normalExponentDegree (wordExponent (w j))≤m} where
  toFun:=fun j=>⟨historicalDegreePrefixLabel w m j,historicalDegreePrefixLabel_mem w m j⟩
  invFun:=fun j=>(historicalDegreePrefixKeys w m).orderIsoOfFin rfl |>.symm
    ⟨historicalDegreeKey w j.val,Finset.mem_image.mpr ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.property⟩,rfl⟩⟩
  left_inv:=by
    intro j
    apply ((historicalDegreePrefixKeys w m).orderIsoOfFin rfl).injective
    apply Subtype.ext
    rw [OrderIso.apply_symm_apply]
    exact historicalDegreePrefixLabel_key w m j
  right_inv:=by
    intro j
    apply Subtype.ext
    change (ofLex (((historicalDegreePrefixKeys w m).orderIsoOfFin rfl)
      (((historicalDegreePrefixKeys w m).orderIsoOfFin rfl).symm _)).val).2=j.val
    rw [OrderIso.apply_symm_apply]
    rfl

def historicalDegreePrefixWords (w : Fin k → CoordinateWord n) (m : ℕ) :
    Fin (historicalDegreePrefixCount w m) → CoordinateWord n :=
  fun j=>w (historicalDegreePrefixLabel w m j)

theorem historicalDegreePrefixLabel_strictMono (w : Fin k → CoordinateWord n) (m : ℕ) :
    StrictMono (fun j=>historicalDegreeKey w (historicalDegreePrefixLabel w m j)) := by
  intro a b hab
  change historicalDegreeKey w (historicalDegreePrefixLabel w m a)<
    historicalDegreeKey w (historicalDegreePrefixLabel w m b)
  rw [historicalDegreePrefixLabel_key,historicalDegreePrefixLabel_key]
  exact ((historicalDegreePrefixKeys w m).orderIsoOfFin rfl).strictMono hab

/-- Every natural degree cutoff is literally one of the finitely many
bounded cutoffs. No natural prefix is discarded. -/
theorem historicalDegreePrefixKeys_clamp (w : Fin k → CoordinateWord n) {M : ℕ}
    (hBound : ∀j,normalExponentDegree (wordExponent (w j))≤M) (m : ℕ) :
    historicalDegreePrefixKeys w (min m M)=historicalDegreePrefixKeys w m := by
  unfold historicalDegreePrefixKeys
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,le_min_iff]
  exact and_iff_left (hBound j)

def HistoricalDegreePrefixFrames (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (m : ℕ) : Prop :=
  (∀q,Function.Bijective (historicalWholeJetMap (historicalDegreePrefixWords w m)
    (fun j=>g (historicalDegreePrefixLabel w m j)) q)) ∧
  ∀d,Function.Bijective (historicalHomogeneousColumnMap (historicalDegreePrefixWords w m)
    (fun j=>g (historicalDegreePrefixLabel w m j)) d)

/-- The finite quantitative choice covers every natural literal prefix,
with its unchanged original label dictionary. -/
theorem historicalDegreePrefixFrames_all_cutoffs (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) {M : ℕ}
    (hBound : ∀j,normalExponentDegree (wordExponent (w j))≤M)
    (hFrames : ∀m : Fin (M+1),HistoricalDegreePrefixFrames w g m.val) :
    ∀m : ℕ,HistoricalDegreePrefixFrames w g m := by
  intro m
  let b : Fin (M+1):=⟨min m M,by omega⟩
  have hFrame:=hFrames b
  have hClamp:=historicalDegreePrefixKeys_clamp w hBound m
  let FrameAt (K : Finset (Lex (ℕ × Fin k))) : Prop:=
    (∀q,Function.Bijective (historicalWholeJetMap
      (fun j : Fin K.card=>w (ofLex ((K.orderIsoOfFin rfl) j).val).2)
      (fun j : Fin K.card=>g (ofLex ((K.orderIsoOfFin rfl) j).val).2) q)) ∧
    ∀d,Function.Bijective (historicalHomogeneousColumnMap
      (fun j : Fin K.card=>w (ofLex ((K.orderIsoOfFin rfl) j).val).2)
      (fun j : Fin K.card=>g (ofLex ((K.orderIsoOfFin rfl) j).val).2) d)
  have hLow : FrameAt (historicalDegreePrefixKeys w (min m M)):=hFrame
  exact Eq.mp (congrArg FrameAt hClamp) hLow

open HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
 HironakaActualInheritedSourceCauchyRemainder HironakaActualInheritedUniformTranslatedTails
 HironakaActualFiniteDegLexWeights HironakaActualWeightedVertexSmallTails
 HironakaActualTranslatedCauchyOwnerSupport HironakaActualCauchyTaylorSupport
 HironakaActualRelativeNormalJetDivision HironakaActualGeometricCurrentNeighborhoodHS
 HironakaActualInheritedTranslatedAnalyticDivision HironakaActualDiagonalTaylor
 HironakaActualInheritedNeighborhoodStandardJets
 HironakaActualWeightedScaling
 HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance

private theorem eventually_translate_halfBall {R : ℝ} (hR : 0<R) :
    ∀ᶠp : CoordinateSpace n in 𝓝 0,
      MapsTo (fun z=>p+z) (Metric.ball 0 (R/2)) (Metric.ball 0 R) := by
  have hquarter : 0<R/4:=div_pos hR (by norm_num)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hquarter)] with p hp
  intro z hz
  have hpN:=mem_ball_zero_iff.mp hp
  have hzN:=mem_ball_zero_iff.mp hz
  apply mem_ball_zero_iff.mpr
  exact (norm_add_le p z).trans_lt (by linarith)

private theorem eventually_head_translate_small {R ε : ℝ}
    (hR : 0<R) (hε : 0<ε) (w : CoordinateWord n) :
    ∀ᶠp : CoordinateSpace n in 𝓝 0,
      ∀z∈Metric.ball (0 : CoordinateSpace n) (R/2),
        ‖wordMonomial w (p+z)-wordMonomial w z‖<ε := by
  have hu : UniformContinuousOn (wordMonomial w) (Metric.closedBall (0 : CoordinateSpace n) R):=
    (isCompact_closedBall (0 : CoordinateSpace n) R).uniformContinuousOn_of_continuous
      (wordMonomial_differentiable w).continuous.continuousOn
  obtain ⟨η,hη,hmod⟩:=(Metric.uniformContinuousOn_iff.mp hu) ε hε
  have hsmall : 0<min η (R/4):=lt_min hη (div_pos hR (by norm_num))
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hsmall)] with p hp
  intro z hz
  have hpN:=mem_ball_zero_iff.mp hp
  have hpη : ‖p‖<η:=hpN.trans_le (min_le_left _ _)
  have hpR : ‖p‖<R/4:=hpN.trans_le (min_le_right _ _)
  have hzN:=mem_ball_zero_iff.mp hz
  have hpzR : ‖p+z‖<R:=(norm_add_le p z).trans_lt (by linarith)
  have hzR : ‖z‖≤R:=by linarith
  have hdist : dist (p+z) z<η:=by simpa only [dist_eq_norm,add_sub_cancel_right] using hpη
  have hdiff:=hmod (p+z) (mem_closedBall_zero_iff.mpr hpzR.le)
    z (mem_closedBall_zero_iff.mpr hzR) hdist
  simpa only [dist_eq_norm] using hdiff

section GeometricSource
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

/-- Actual minimal original vertices retain their own literal historical
columns in every degree prefix in which they occur. -/
theorem actualDegreePrefixHead_owner (m : ℕ)
    (j : Fin (historicalDegreePrefixCount (actualVertexWords n I) m)) :
    historicalOwner (historicalDegreePrefixWords (actualVertexWords n I) m)
      (wordExponent (historicalDegreePrefixWords (actualVertexWords n I) m j))=some j := by
  apply (historicalOwner_eq_some_iff _ _ _).mpr
  refine ⟨le_rfl,?_⟩
  apply (avoidsCones_take_iff _ _ _).mpr
  intro i hij hdiv
  let a:=actualVertexEnumeration n I (historicalDegreePrefixLabel (actualVertexWords n I) m j)
  let b:=actualVertexEnumeration n I (historicalDegreePrefixLabel (actualVertexWords n I) m i)
  have ha : Minimal (·∈actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) a.val:=by
    simpa [actualInitialVertices,analyticZeroTaylorIdeal] using a.property
  have hb : Minimal (·∈actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) b.val:=by
    simpa [actualInitialVertices,analyticZeroTaylorIdeal] using b.property
  have hba : b.val≤a.val:=by
    simpa only [historicalDegreePrefixWords,actualVertexWords,wordExponent_wordOfExponent] using hdiv
  have hEq : b.val=a.val:=le_antisymm hba (ha.le_of_le hb.prop hba)
  have hLabel : historicalDegreePrefixLabel (actualVertexWords n I) m i=
      historicalDegreePrefixLabel (actualVertexWords n I) m j:=
    (actualVertexEnumeration n I).injective (Subtype.ext hEq)
  have he : i=j:=(historicalDegreePrefixLabelEquiv (actualVertexWords n I) m).injective (Subtype.ext hLabel)
  exact (ne_of_lt hij) he

/-- The internally produced degree-prefix frames force every SAME member
to retain a nonzero original homogeneous leading part. -/
theorem actual_member_not_mem_succ_of_prefix_frames
    (g : Fin (actualVertexCount n I) → MvPowerSeries (Fin n) ℂ)
    (hFrames : ∀m,HistoricalDegreePrefixFrames (actualVertexWords n I) g m) :
    ∀j,g j∉genuineFormalVariables n^(normalExponentDegree (wordExponent (actualVertexWords n I j))+1) := by
  intro j
  let m:=normalExponentDegree (wordExponent (actualVertexWords n I j))
  let e:=historicalDegreePrefixLabelEquiv (actualVertexWords n I) m
  let a:=e.symm ⟨j,le_rfl⟩
  have hLabel : historicalDegreePrefixLabel (actualVertexWords n I) m a=j:=
    congrArg (fun z : {i : Fin (actualVertexCount n I) //
      normalExponentDegree (wordExponent (actualVertexWords n I i))≤m}=>z.val)
      (e.apply_symm_apply ⟨j,le_rfl⟩)
  have hNot:=historicalWholeJetMap_member_not_mem_succ
    (historicalDegreePrefixWords (actualVertexWords n I) m)
    (fun i=>g (historicalDegreePrefixLabel (actualVertexWords n I) m i)) a
    (actualDegreePrefixHead_owner m a) (((hFrames m).1 _).1)
  simpa only [historicalDegreePrefixWords,hLabel] using hNot

/-- ONE genuine scale and translation window serve ALL literal historical
degree prefixes before any translated point or homogeneous degree. -/
theorem exists_actual_inherited_uniform_degree_prefix_tails :
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ),s≠0 ∧ s∈Metric.ball 0 P.radius ∧
      ∃D : ∀m : Fin (P.germs.degreeBound+1),ConcreteNeumannData (P.radius/2)
          (historicalDegreePrefixWords (actualVertexWords n I) m.val),
      ∃δ : ℝ,0<δ ∧
        ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
          MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius) ∧
          (∀j,DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j) (Metric.ball 0 (P.radius/2))) ∧
          ∀(m : Fin (P.germs.degreeBound+1))(j : Fin (historicalDegreePrefixCount (actualVertexWords n I) m.val)),
            ∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
              ‖actualInheritedTranslatedTail P s p (historicalDegreePrefixLabel (actualVertexWords n I) m.val j) z‖≤
                (D m).epsilon := by
  classical
  obtain ⟨P⟩:=nonempty_actualInheritedWeightedTailData G
  let D (m : Fin (P.germs.degreeBound+1)) : ConcreteNeumannData (P.radius/2)
      (historicalDegreePrefixWords (actualVertexWords n I) m.val):=
    Classical.choice (nonempty_concreteNeumannData (P.radius/2) (half_pos P.radius_pos)
      (historicalDegreePrefixWords (actualVertexWords n I) m.val))
  let ε:=Finset.univ.inf' Finset.univ_nonempty (fun m : Fin (P.germs.degreeBound+1)=>(D m).epsilon)
  have hε : 0<ε:=(Finset.lt_inf'_iff _).mpr fun m _=>(D m).epsilon_pos
  have hεle (m : Fin (P.germs.degreeBound+1)) : ε≤(D m).epsilon:=
    Finset.inf'_le _ (Finset.mem_univ m)
  obtain ⟨s,hs0,hs,_hhol,hsmall⟩:=exists_inherited_smallParameter P (ε/2) (half_pos hε)
  have hhead : ∀ᶠp : CoordinateSpace n in 𝓝 0,
      ∀j : Fin (actualVertexCount n I),∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
        ‖wordMonomial (actualVertexWords n I j) (p+z)-wordMonomial (actualVertexWords n I j) z‖<ε/2:=
    eventually_all.mpr fun j=>eventually_head_translate_small P.radius_pos (half_pos hε) (actualVertexWords n I j)
  obtain ⟨δ,hδ,hnear⟩:=Metric.eventually_nhds_iff_ball.mp
    ((eventually_translate_halfBall P.radius_pos).and hhead)
  refine ⟨P,s,hs0,hs,D,δ,hδ,?_⟩
  intro p hp
  have hdom:=(hnear p hp).1
  have hheads:=(hnear p hp).2
  refine ⟨hdom,?_,?_⟩
  · intro j
    exact (actual_coordinate_translation_differentiableOn
      (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom).sub
        (wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn
  intro m j z hz
  let a:=historicalDegreePrefixLabel (actualVertexWords n I) m.val j
  have htail : ‖actualInheritedSourceScaledTail P s a (p+z)‖≤ε/2:=
    (hsmall (actualVertexEnumeration n I a) (p+z) (hdom hz)).2.le
  calc
    ‖actualInheritedTranslatedTail P s p a z‖=
        ‖actualInheritedSourceScaledTail P s a (p+z)+
          (wordMonomial (actualVertexWords n I a) (p+z)-wordMonomial (actualVertexWords n I a) z)‖:=by
      congr 1
      unfold actualInheritedTranslatedTail
      rw [actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs a (hdom hz)]
      ring
    _≤‖actualInheritedSourceScaledTail P s a (p+z)‖+
        ‖wordMonomial (actualVertexWords n I a) (p+z)-wordMonomial (actualVertexWords n I a) z‖:=norm_add_le _ _
    _≤ε/2+ε/2:=add_le_add htail (hheads a z hz).le
    _=ε:=by ring
    _≤(D m).epsilon:=hεle m

/-- Exact original member orders at the actual native point, stated in
its original holomorphic local ring rather than only a rescaled jet space. -/
def ActualHistoricalNativeExactOrderAt
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (u : ComplexModel n) (hu : u∈PHS.neighborhood) : Prop :=
  ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
    translatedGerm u (PHS.representatives a) (PHS.holomorphicAt _ hu a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val ∧
    translatedGerm u (PHS.representatives a) (PHS.holomorphicAt _ hu a)∉
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(normalExponentDegree a.val+1)

/-- The actual degree-prefix conclusion, produced jointly on one genuine
native window. Every natural cutoff and every jet degree is quantified
AFTER the common scale, open and literal member-function dictionaries. -/
def ActualHistoricalDegreePrefixJetNeighborhood
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) : Prop :=
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (hs : s∈Metric.ball 0 P.radius)(δ : ℝ),0<δ ∧
    IsOpen (historicalNativeJetWindow P s hs0 δ) ∧
    (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ ∧
    historicalNativeJetWindow P s hs0 δ⊆PHS.neighborhood ∧
    ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
      ∃hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius),
      ∃hu : scaledOriginalPoint P s p∈PHS.neighborhood,
        (∀j : Fin (actualVertexCount n I),
          let a:=actualVertexEnumeration n I j
          let W:=degLexWeight n P.germs.degreeBound
          actualInheritedTranslatedGerm P hs p hdom j=
            HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
              actualDiagonalPullback (fun i=>s^W i)
                (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a)
                  (PHS.holomorphicAt _ hu a))) ∧
        ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ActualHistoricalNativeExactOrderAt PHS (scaledOriginalPoint P s p) hu ∧
          ∀m : ℕ,
            (∀q,Function.Bijective (historicalWholeJetMap
              (historicalDegreePrefixWords (actualVertexWords n I) m)
              (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
                (historicalDegreePrefixLabel (actualVertexWords n I) m j))) q)) ∧
            ∀d,Function.Bijective (historicalHomogeneousColumnMap
              (historicalDegreePrefixWords (actualVertexWords n I) m)
              (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
                (historicalDegreePrefixLabel (actualVertexWords n I) m j))) d))

/-- Genuine geometric HS derives all original member marks; all literal
degree-prefix whole and homogeneous supported-column bases are constructed
on ONE native open. No prefix-rank/diagram/translated-head input occurs. -/
theorem exists_actual_geometric_historical_degree_prefix_jet_neighbourhood
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) :
    ActualHistoricalDegreePrefixJetNeighborhood PHS := by
  classical
  obtain ⟨P,s,hs0,hs,D,δ,hδ,hnear⟩:=exists_actual_inherited_uniform_degree_prefix_tails (G:=G)
  have hEq (a) : P.representative a=ᶠ[𝓝 (0 : ComplexModel n)] PHS.representatives a:=
    HolGerm.mk_eq_mk_iff.mp ((P.representative_eq a).trans (PHS.sameGerms a).symm)
  have hPmem : ∀ᶠx in 𝓝 (0 : ComplexModel n),x∈PHS.neighborhood:=
    PHS.isOpen_neighborhood.mem_nhds PHS.zero_mem
  have hAll : ∀ᶠx in 𝓝 (0 : ComplexModel n),x∈PHS.neighborhood ∧
      ∀a,P.representative a x=PHS.representatives a x:=hPmem.and (eventually_all.mpr hEq)
  obtain ⟨O,hOsub,hO,h0O⟩:=mem_nhds_iff.mp hAll
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have hc : Continuous (scaledOriginalPoint P s):=
    (actualDiagonalMap (fun i=>s^(degLexWeight n P.germs.degreeBound i))).continuous.comp e.symm.continuous
  have hc0 : scaledOriginalPoint P s (0 : CoordinateSpace n)=0:=by
    change actualDiagonalMap _ (e.symm 0)=0
    rw [map_zero,map_zero]
  have ht : Tendsto (scaledOriginalPoint P s) (𝓝 0) (𝓝 0):=by simpa only [hc0] using hc.tendsto 0
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp (ht.eventually (hO.mem_nhds h0O))
  refine ⟨P,s,hs0,hs,min δ η,lt_min hδ hη,
    historicalNativeJetWindow_isOpen P s hs0 _,historicalNativeJetWindow_zero P s hs0 (lt_min hδ hη),?_,?_⟩
  · intro u hu
    obtain ⟨p,hp,hpu⟩:=historicalNativeJetWindow_coverage P s hs0 (min δ η) u hu
    have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
      (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
    exact hpu ▸ (hOsub (hηsub hpη)).1
  intro p hp
  have hpδ : p∈Metric.ball (0 : CoordinateSpace n) δ:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_left δ η))
  have hpη : p∈Metric.ball (0 : CoordinateSpace n) η:=mem_ball_zero_iff.mpr
    (lt_of_lt_of_le (mem_ball_zero_iff.mp hp) (min_le_right δ η))
  have huO : scaledOriginalPoint P s p∈O:=hηsub hpη
  have hu : scaledOriginalPoint P s p∈PHS.neighborhood:=(hOsub huO).1
  obtain ⟨hdom,hHd,hHb⟩:=hnear p hpδ
  have hCov:=scaled_translated_historical_germ PHS P hs p hdom O hO
    (fun x hx=>(hOsub hx).2) huO hu
  refine ⟨hdom,hu,hCov,?_⟩
  intro hHS
  have hMarked : ∀j : Fin (actualVertexCount n I),
      actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) := by
    intro j
    let a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=actualVertexEnumeration n I j
    have hOld:=(PHS.wholeHS _ hu).mpr hHS a
    have hDiag:=diagonal_pullback_mem_maximal_power
      (fun i=>s^(degLexWeight n P.germs.degreeBound i)) hOld
    have hScaled:=Ideal.mul_mem_left
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
      (HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)) hDiag
    have hCurrent : actualInheritedTranslatedGerm P hs p hdom j∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val:=
      Eq.mpr (congrArg (fun F : HolGerm (ComplexModel n)=>F∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val) (hCov j)) hScaled
    have hTaylor:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hCurrent
    rw [map_actualUnshifted_maximal_pow] at hTaylor
    have hTaylor' : actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
        genuineFormalVariables n^normalExponentDegree (actualVertexEnumeration n I j).val:=hTaylor
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using hTaylor'
  have hIdentity:=translated_neumann_family_taylor P hs p hdom hHd
  have hFrames (m : Fin (P.germs.degreeBound+1)) :
      (∀q,Function.Bijective (historicalWholeJetMap
        (historicalDegreePrefixWords (actualVertexWords n I) m.val)
        (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
          (historicalDegreePrefixLabel (actualVertexWords n I) m.val j))) q)) ∧
      ∀d,Function.Bijective (historicalHomogeneousColumnMap
        (historicalDegreePrefixWords (actualVertexWords n I) m.val)
        (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
          (historicalDegreePrefixLabel (actualVertexWords n I) m.val j))) d) := by
    let w:=historicalDegreePrefixWords (actualVertexWords n I) m.val
    let H:=fun j=>actualInheritedTranslatedTail P s p (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)
    have hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 (P.radius/2)):=
      fun j=>hHd (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)
    have hM : ∀j,actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
        ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))∈
          genuineFormalVariables n^normalExponentDegree (wordExponent (w j)):=by
      intro j
      change actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
        ((wordMonomial_differentiable (actualVertexWords n I
          (historicalDegreePrefixLabel (actualVertexWords n I) m.val j))).differentiableOn.add
          (hHd (historicalDegreePrefixLabel (actualVertexWords n I) m.val j))))∈_
      rw [hIdentity (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)]
      exact hMarked (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)
    have hW:=historicalWholeJetMap_bijective_of_neumann (half_pos P.radius_pos)
      w (D m) H hH (hHb m) hM
    have hFamily : (fun j=>actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
      ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j))))=
        (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
          (historicalDegreePrefixLabel (actualVertexWords n I) m.val j))):=
      funext fun j=>hIdentity (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)
    rw [hFamily] at hW
    refine ⟨hW,?_⟩
    intro d
    rw [historicalHomogeneousColumnMap_eq_operator]
    exact historicalHomogeneousOperator_bijective w _
      (fun j=>hMarked (historicalDegreePrefixLabel (actualVertexWords n I) m.val j)) hW d
  have hBound : ∀j : Fin (actualVertexCount n I),
      normalExponentDegree (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound:=by
    intro j
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using P.germs.degree_le (actualVertexEnumeration n I j)
  have hAllFrames:=historicalDegreePrefixFrames_all_cutoffs (actualVertexWords n I)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hBound hFrames
  refine ⟨?_,hAllFrames⟩
  have hNotFormal:=actual_member_not_mem_succ_of_prefix_frames
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hAllFrames
  intro a
  refine ⟨(PHS.wholeHS _ hu).mpr hHS a,?_⟩
  intro hHigher
  let j:=(actualVertexEnumeration n I).symm a
  have hj : actualVertexEnumeration n I j=a:=(actualVertexEnumeration n I).apply_symm_apply a
  have hDiag:=diagonal_pullback_mem_maximal_power
    (fun i=>s^(degLexWeight n P.germs.degreeBound i)) hHigher
  have hScaled:=Ideal.mul_mem_left
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(normalExponentDegree a.val+1))
    (HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)) hDiag
  have hCovj : actualInheritedTranslatedGerm P hs p hdom j=
      HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)*
        actualDiagonalPullback (fun i=>s^(degLexWeight n P.germs.degreeBound i))
          (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a)):=by
    simpa only [hj] using hCov j
  have hCurrent : actualInheritedTranslatedGerm P hs p hdom j∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(normalExponentDegree a.val+1):=
    Eq.mpr (congrArg (fun F : HolGerm (ComplexModel n)=>F∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(normalExponentDegree a.val+1)) hCovj) hScaled
  have hTaylor:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hCurrent
  rw [map_actualUnshifted_maximal_pow] at hTaylor
  have hTaylor' : actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
      genuineFormalVariables n^(normalExponentDegree a.val+1):=hTaylor
  apply hNotFormal j
  simpa only [actualVertexWords,wordExponent_wordOfExponent,hj] using hTaylor'

end GeometricSource

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
 HironakaActualHistoricalPrescribedIteration HironakaActualPrescribedHSRecursion
 HironakaActualPrescribedCentreRebasing HironakaActualPrescribedWeightedSuccessor
 HironakaActualCurrentMarkedFunctionSquares HironakaActualWholeHSContactWindow
 HironakaSmoothCentreCoherentDomain HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualInheritedCurrentSourceRelabel
 HironakaActualNormalMarkedDirection HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualRelativeNormalJetDivision HironakaActualAnalyticBlowupTaylor
 HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
 HironakaActualFiniteCoefficientIdeals HironakaRelativeNormalDeformationInitialRelations
 HironakaActualFixedFlatteningHSComparison
 HironakaRelativeNormalCoherentTranslatedJets HironakaActualNormalAllDirectionAnalyticSaturation
 MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder InvertibleIdealQuotient

/-- ORIGINAL source geometry produces the SAME actual historical stage and
global continuation, with exact original native member orders and ALL literal
degree-prefix whole and homogeneous frames on a jointly chosen actual window. -/
theorem exists_actual_geometric_stage_with_degree_prefix_jets
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+2))) Z] [IsComplexManifold (d+(t+2)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+2)))) (h0U : (0 : ComplexModel (d+(t+2)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
      ComplexModel (d+(t+2)) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+(t+2))))∩complexCoordinatePlane (d+(t+2)) d⊆
      cosupport (d+(t+2)) univ (actualPrincipalCoefficientIdeal (d+(t+2)) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+2)) ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+2)))=0)
    (W : Set U) (hWa : IsComplexAnalyticSubset (n:=d+(t+2)) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+(t+2)))))
    (hOrigin : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    y∈Q.cosupp ∧
    ∃(e : Fin (d+(t+2)))(b : Fin (d+(t+2)) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
        chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
        (π z : ComplexModel (d+(t+2)))=actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      ∃u : HolGerm (ComplexModel (d+(t+2))),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (d+(t+2))))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2))
            (strictTransform (d+(t+2)) π W)) y Θ) 0)
        let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
        let A₀:=vanishingIdeal (n:=d+(t+2))
          (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
        let A:=GermIdeal.pullback (m:=d+(t+2)) P.chart.toFun A₀
        J=Ideal.map C.toRingEquiv.toRingHom K ∧ J=originalCoherentOriginIdeal A ∧
        ∃PHS : ActualGeometricInheritedNeighborhoodHS A J D.targetFamily (hilbertSamuelValue I),
          PHS.representatives=P.currentFunctions ∧ PHS.neighborhood⊆P.currentDomain ∧
          MapsTo P.chart.toFun PHS.neighborhood Θ.target ∧
          (∀k,∀z∈PHS.neighborhood,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) (sameAnalyticZeroNormalizedIdeal (d+(t+2)) _
                D.sourceFamily q D.sourcePower))) k,z j=0) ∧
          (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) ∧
          ActualSelectedContactWindowLaws S
            (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
            (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
            A (hilbertSamuelValue I) P.chart.toFun PHS.neighborhood ∧
          ActualPrescribedStageRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedWeightedRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedRepeatedHSRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧ ActualHistoricalWholeJetNeighborhood PHS ∧ ActualHistoricalDegreePrefixJetNeighborhood PHS := by
  dsimp only
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets⟩:=
    exists_actual_geometric_stage_with_moving_whole_jets I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,?_⟩
  exact exists_actual_geometric_historical_degree_prefix_jet_neighbourhood PHS


end
end Hironaka.HironakaActualHistoricalPrefixJetFrames
