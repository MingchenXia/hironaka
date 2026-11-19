import Hironaka.Resolution.HironakaActualHistoricalPrefixJetFrames

/-! Whole formal supported division for the SAME nonmonic moving historical
family. The inverse is assembled from its genuinely produced compatible
whole jets; target monic heads and target division certificates are absent. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalFormalSupportedDivision
noncomputable section
open HolGerm HironakaHolomorphicPointJets
 HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
 HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
 HironakaActualCauchyCoordinateDivision HironakaActualCauchyMonomialDivision
 HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
 HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

def historicalInverseJet (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) (q : ℕ)
    (v : normalExponentIndex n q → ℂ) : normalExponentIndex n q → ℂ :=
  (Equiv.ofBijective (historicalWholeJetMap w g q) (hwhole q)).symm v

theorem historicalWholeJetMap_inverseJet (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) (q : ℕ)
    (v : normalExponentIndex n q → ℂ) :
    historicalWholeJetMap w g q (historicalInverseJet w g hwhole q v)=v :=
  (Equiv.ofBijective (historicalWholeJetMap w g q) (hwhole q)).apply_symm_apply v

/-- The unique finite inverses are genuinely compatible under every actual
coefficient truncation; compatibility is derived from injectivity. -/
theorem historicalInverseJet_truncation (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    {q r : ℕ} (hqr : q≤r) (F : MvPowerSeries (Fin n) ℂ) :
    boundedCoefficients q (boundedSeries r
      (historicalInverseJet w g hwhole r (boundedCoefficients r F)))=
      historicalInverseJet w g hwhole q (boundedCoefficients q F) := by
  have hRight:=historicalWholeJetMap_inverseJet w g hwhole r (boundedCoefficients r F)
  rw [historicalWholeJetMap_eq_operator] at hRight
  apply (hwhole q).1
  rw [historicalWholeJetMap_truncation w g hmarked,historicalWholeJetMap_inverseJet]
  funext α
  have hαr : normalExponentDegree α.val<r:=lt_of_lt_of_le α.property hqr
  exact congrFun hRight (⟨α.val,hαr⟩ : normalExponentIndex n r)

/-- The whole inverse series is assembled coefficientwise from the unique
actual inverse jet at that coefficient's degree plus one. -/
def historicalFormalInverse (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun α=>historicalInverseJet w g hwhole (normalExponentDegree α+1)
    (boundedCoefficients (normalExponentDegree α+1) F) ⟨α,Nat.lt_succ_self _⟩

theorem historicalFormalInverse_truncation (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    boundedCoefficients q (historicalFormalInverse w g hwhole F)=
      historicalInverseJet w g hwhole q (boundedCoefficients q F) := by
  classical
  funext α
  let r:=normalExponentDegree α.val+1
  let a : normalExponentIndex n r:=⟨α.val,Nat.lt_succ_self _⟩
  have hrq : r≤q:=by dsimp only [r]; omega
  have he:=congrFun (historicalInverseJet_truncation w g hmarked hwhole hrq F) a
  change (if h : normalExponentDegree α.val<q then
    historicalInverseJet w g hwhole q (boundedCoefficients q F) ⟨α.val,h⟩ else 0)=
      historicalInverseJet w g hwhole r (boundedCoefficients r F) a at he
  rw [dif_pos α.property] at he
  exact he.symm

theorem historicalReassemble_formalInverse (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ) :
    historicalReassemble w g (historicalFormalInverse w g hwhole F)=F := by
  ext α
  let q:=normalExponentDegree α+1
  have he:=historicalWholeJetMap_truncation w g hmarked q (historicalFormalInverse w g hwhole F)
  rw [historicalFormalInverse_truncation w g hmarked hwhole,historicalWholeJetMap_inverseJet] at he
  exact (congrFun he (⟨α,Nat.lt_succ_self _⟩ : normalExponentIndex n q)).symm

theorem historicalReassemble_injective (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) :
    Function.Injective (historicalReassemble w g) := by
  intro F H hEq
  ext α
  let q:=normalExponentDegree α+1
  have he : boundedCoefficients q F=boundedCoefficients q H:=by
    apply (hwhole q).1
    rw [historicalWholeJetMap_truncation w g hmarked,
      historicalWholeJetMap_truncation w g hmarked,hEq]
  exact congrFun he (⟨α,Nat.lt_succ_self _⟩ : normalExponentIndex n q)

/-- The actual filtered whole operator is a genuine full formal linear
equivalence, derived from the compatible whole jets. -/
def historicalFormalEquiv (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) :
    MvPowerSeries (Fin n) ℂ ≃ₗ[ℂ] MvPowerSeries (Fin n) ℂ :=
  LinearEquiv.ofBijective (historicalReassemble w g)
    ⟨historicalReassemble_injective w g hmarked hwhole,
      fun F=>⟨historicalFormalInverse w g hwhole F,historicalReassemble_formalInverse w g hmarked hwhole F⟩⟩

/-- The inverse preserves every maximal-ideal power, including order zero.
This is the continuity needed for arbitrary FORMAL multiplier coefficients. -/
theorem historicalFormalEquiv_symm_mem_power (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    {q : ℕ} {F : MvPowerSeries (Fin n) ℂ} (hF : F∈genuineFormalVariables n^q) :
    (historicalFormalEquiv w g hmarked hwhole).symm F∈genuineFormalVariables n^q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  have he : boundedCoefficients q ((historicalFormalEquiv w g hmarked hwhole).symm F)=0:=by
    apply (hwhole q).1
    rw [historicalWholeJetMap_truncation w g hmarked,map_zero]
    change boundedCoefficients q ((historicalFormalEquiv w g hmarked hwhole)
      ((historicalFormalEquiv w g hmarked hwhole).symm F))=0
    rw [LinearEquiv.apply_symm_apply]
    funext α
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hF α.val α.property
  intro α hα
  exact congrFun he (⟨α,hα⟩ : normalExponentIndex n q)

def historicalFormalQuotient (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) (j : Fin k) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ :=
  (historicalMonomialQuotient w j).comp (historicalFormalEquiv w g hmarked hwhole).symm.toLinearMap

def historicalFormalRemainder (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ :=
  (historicalMonomialRemainder w).comp (historicalFormalEquiv w g hmarked hwhole).symm.toLinearMap

/-- Actual WHOLE formal division, for every series, in the literal old
supported regions. No formal division certificate is supplied. -/
theorem historicalFormal_division (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ) :
    F=(∑j,historicalFormalQuotient w g hmarked hwhole j F*g j)+
      historicalFormalRemainder w g hmarked hwhole F :=
  ((historicalFormalEquiv w g hmarked hwhole).apply_symm_apply F).symm

theorem historicalFormalQuotient_support (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ) (j : Fin k) (β : Fin n →₀ ℕ)
    (ho : historicalOwner w (β+wordExponent (w j))≠some j) :
    MvPowerSeries.coeff β (historicalFormalQuotient w g hmarked hwhole j F)=0 := by
  classical
  change (if historicalOwner w (β+wordExponent (w j))=some j then _ else 0)=0
  exact if_neg ho

theorem historicalFormalRemainder_support (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ) (β : Fin n →₀ ℕ) (ho : historicalOwner w β≠none) :
    MvPowerSeries.coeff β (historicalFormalRemainder w g hmarked hwhole F)=0 := by
  classical
  change (if historicalOwner w β=none then _ else 0)=0
  exact if_neg ho

theorem historicalFormalQuotient_mem_power (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    {q : ℕ} {F : MvPowerSeries (Fin n) ℂ} (hF : F∈genuineFormalVariables n^q) (j : Fin k) :
    historicalFormalQuotient w g hmarked hwhole j F∈
      genuineFormalVariables n^(q-normalExponentDegree (wordExponent (w j))) :=
  historicalMonomialQuotient_mem_power w j (historicalFormalEquiv_symm_mem_power w g hmarked hwhole hF)

theorem historicalFormalRemainder_mem_power (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    {q : ℕ} {F : MvPowerSeries (Fin n) ℂ} (hF : F∈genuineFormalVariables n^q) :
    historicalFormalRemainder w g hmarked hwhole F∈genuineFormalVariables n^q :=
  historicalMonomialRemainder_mem_power w (historicalFormalEquiv_symm_mem_power w g hmarked hwhole hF)

/-- The whole remainder is uniquely identified by any actual supported
division. This will identify it with the genuine analytic Neumann output. -/
theorem historicalFormalRemainder_eq_of_supported (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (F : MvPowerSeries (Fin n) ℂ)
    (Q : Fin k → MvPowerSeries (Fin n) ℂ) (R : MvPowerSeries (Fin n) ℂ)
    (hDiv : F=(∑j,Q j*g j)+R)
    (hQ : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0)
    (hR : ∀β,historicalOwner w β≠none → MvPowerSeries.coeff β R=0) :
    historicalFormalRemainder w g hmarked hwhole F=R := by
  let A:=(∑j,MvPowerSeries.monomial (wordExponent (w j)) 1*Q j)+R
  have hRA : historicalReassemble w g A=(∑j,Q j*g j)+R:=
    historicalReassemble_of_supported_division w g Q R hQ hR
  have he : (historicalFormalEquiv w g hmarked hwhole).symm F=A:=
    (historicalFormalEquiv w g hmarked hwhole).injective
      (((historicalFormalEquiv w g hmarked hwhole).apply_symm_apply F).trans (hDiv.trans hRA.symm))
  change historicalMonomialRemainder w ((historicalFormalEquiv w g hmarked hwhole).symm F)=R
  rw [he]
  exact historical_supported_remainder_recovery w Q R hQ hR

theorem sub_truncTotal_mem_power (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F-(MvPowerSeries.truncTotal q F : MvPowerSeries (Fin n) ℂ)∈genuineFormalVariables n^q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  have hdeg : α.degree<q:=by simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using hα
  rw [map_sub,MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal F hdeg,sub_self]

/-- Polynomial multiplier zero remainders extend to ARBITRARY formal
multiplier coefficients by the derived maximal-power filtration. -/
theorem historicalFormalRemainder_formal_multiple_zero (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hPolynomial : ∀(j : Fin k)(P : MvPolynomial (Fin n) ℂ),
      historicalFormalRemainder w g hmarked hwhole ((P : MvPowerSeries (Fin n) ℂ)*g j)=0)
    (j : Fin k) (Q : MvPowerSeries (Fin n) ℂ) :
    historicalFormalRemainder w g hmarked hwhole (Q*g j)=0 := by
  ext α
  rw [map_zero]
  let q:=normalExponentDegree α+1
  let r:=q-normalExponentDegree (wordExponent (w j))
  have hMul:=(Ideal.mul_mem_mul (sub_truncTotal_mem_power r Q) (hmarked j))
  rw [←pow_add] at hMul
  have hm : Q*g j-(MvPowerSeries.truncTotal r Q : MvPowerSeries (Fin n) ℂ)*g j∈genuineFormalVariables n^q:=by
    rw [←sub_mul]
    exact (Ideal.pow_le_pow_right (by dsimp only [r]; omega)) hMul
  have hRem:=historicalFormalRemainder_mem_power w g hmarked hwhole hm
  rw [map_sub,hPolynomial j (MvPowerSeries.truncTotal r Q),sub_zero] at hRem
  exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hRem α (Nat.lt_succ_self _)

/-- Zero remainder holds on the ENTIRE actual ideal span, with arbitrary
formal multiplier coefficients, once the actual polynomial law is produced. -/
theorem historicalFormalRemainder_whole_ideal_zero (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hPolynomial : ∀(j : Fin k)(P : MvPolynomial (Fin n) ℂ),
      historicalFormalRemainder w g hmarked hwhole ((P : MvPowerSeries (Fin n) ℂ)*g j)=0)
    {F : MvPowerSeries (Fin n) ℂ} (hF : F∈Ideal.span (range g)) :
    historicalFormalRemainder w g hmarked hwhole F=0 := by
  classical
  obtain ⟨Q,hQ⟩:=Ideal.mem_span_range_iff_exists_fun.mp hF
  rw [←hQ,map_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact historicalFormalRemainder_formal_multiple_zero w g hmarked hwhole hPolynomial j (Q j)

open HironakaActualCauchyTaylorSupport HironakaActualCauchyDiagramPartition
 HironakaActualCauchyNeumannDivision

private theorem modelTaylor_sum {ι : Type} [Fintype ι] {r : ℝ} (hr : 0<r)
    (f : ι → CoordinateSpace n → ℂ) (hf : ∀i,DifferentiableOn ℂ (f i) (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n
      (modelGerm hr (DifferentiableOn.fun_sum fun i (_hi : i∈Finset.univ)=>hf i))=
      ∑i,actualUnshiftedTaylorAlgHom n (modelGerm hr (hf i)) := by
  change actualUnshiftedTaylorAlgHom n (HolGerm.mk (fun z : ComplexModel n=>∑i,modelFunction (f i) z) _)=_
  rw [HolGerm.mk_sum Finset.univ _ (fun i=>modelFunction_holAt hr (hf i)),map_sum]
  rfl

private theorem modelTaylor_mul {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr (hf.mul hg))=
      actualUnshiftedTaylorAlgHom n (modelGerm hr hf)*actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  change actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : ComplexModel n=>modelFunction f z*modelFunction g z) _)=_
  rw [HolGerm.mk_mul _ _ (modelFunction_holAt hr hf) (modelFunction_holAt hr hg),map_mul]
  rfl

private theorem modelTaylor_add {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr (hf.add hg))=
      actualUnshiftedTaylorAlgHom n (modelGerm hr hf)+actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  change actualUnshiftedTaylorAlgHom n
    (HolGerm.mk (fun z : ComplexModel n=>modelFunction f z+modelFunction g z) _)=_
  rw [HolGerm.mk_add _ _ (modelFunction_holAt hr hf) (modelFunction_holAt hr hg),map_add]
  rfl

private theorem modelTaylor_scaled_word {r : ℝ} (hr : 0<r) (c : ℂ) (w : CoordinateWord n) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr ((wordMonomial_differentiable w).differentiableOn.const_mul c))=
      MvPowerSeries.monomial (wordExponent w) c := by
  have hG : modelGerm hr ((wordMonomial_differentiable w).differentiableOn.const_mul c)=
      HolGerm.constHom c*modelGerm hr (wordMonomial_differentiable w).differentiableOn := by
    change HolGerm.mk (fun z : ComplexModel n=>c*modelFunction (wordMonomial w) z) _=_
    have hc : ∀ᶠz : ComplexModel n in 𝓝 0,DifferentiableAt ℂ (fun _ : ComplexModel n=>c) z:=
      Eventually.of_forall fun _=>differentiableAt_const c
    have hm:=HolGerm.mk_mul (fun _ : ComplexModel n=>c) (modelFunction (wordMonomial w)) hc
      (modelFunction_holAt hr (wordMonomial_differentiable w).differentiableOn)
    simpa only [modelGerm,HolGerm.mk_const] using hm
  have hc : actualUnshiftedTaylorAlgHom n (HolGerm.constHom c)=MvPowerSeries.C c := by
    change (actualUnshiftedTaylorAlgHom n) (algebraMap ℂ (HolGerm (ComplexModel n)) c)=algebraMap ℂ _ c
    exact AlgHom.commutes _ c
  rw [hG,map_mul,hc,actualTaylor_wordMonomial]
  ext α
  rw [MvPowerSeries.coeff_C_mul]
  simp only [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

private theorem modelTaylor_eqOn {r : ℝ} (hr : 0<r)
    {f g : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r))
    (he : EqOn f g (Metric.ball 0 r)) :
    actualUnshiftedTaylorAlgHom n (modelGerm hr hf)=actualUnshiftedTaylorAlgHom n (modelGerm hr hg) := by
  apply congrArg (actualUnshiftedTaylorAlgHom n)
  apply HolGerm.mk_eq_mk_iff.mpr
  let e:=EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)
  have ht : Tendsto e (𝓝 (0 : ComplexModel n)) (𝓝 (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with z hz
  exact he hz


def historicalNeumannFamily {r : ℝ} (hr : 0<r) (w : Fin k → CoordinateWord n)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r)) : Fin k → MvPowerSeries (Fin n) ℂ :=
  fun j=>actualUnshiftedTaylorAlgHom n (modelGerm hr
    ((wordMonomial_differentiable (w j)).differentiableOn.add (hH j)))

/-- The constructed WHOLE formal remainder is the literal Taylor series
of the actual analytic Neumann remainder for the SAME family and numerator. -/
theorem historicalFormalRemainder_eq_neumann {r M : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,historicalNeumannFamily hr w H hH j∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (historicalNeumannFamily hr w H hH) q))
    {f : CoordinateSpace n → ℂ} (hM : 0≤M)
    (hfd : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hfb : ∀z∈Metric.ball (0 : CoordinateSpace n) r,‖f z‖≤M) :
    historicalFormalRemainder w (historicalNeumannFamily hr w H hH) hmarked hwhole
      (actualUnshiftedTaylorAlgHom n (modelGerm hr hfd))=
        actualUnshiftedTaylorAlgHom n
          (modelGerm hr (neumannSums_differentiableOn hr D hH hHb hM hfd hfb).2) := by
  classical
  have hd:=neumannSums_differentiableOn hr D hH hHb hM hfd hfb
  have hs:=neumannSums_whole_support hr D hH hHb hM hfd hfb
  let Q:=fun j=>actualUnshiftedTaylorAlgHom n (modelGerm hr (hd.1 j))
  let R:=actualUnshiftedTaylorAlgHom n (modelGerm hr hd.2)
  apply historicalFormalRemainder_eq_of_supported w _ hmarked hwhole _ Q R
  · let G:=fun j z=>wordMonomial (w j) z+H j z
    have hg (j) : DifferentiableOn ℂ (G j) (Metric.ball 0 r):=
      (wordMonomial_differentiable (w j)).differentiableOn.add (hH j)
    have hsum : DifferentiableOn ℂ (fun z=>∑j,neumannQuotientSum r w H f j z*G j z) (Metric.ball 0 r):=
      DifferentiableOn.fun_sum fun j _=>(hd.1 j).mul (hg j)
    have hEq:=modelTaylor_eqOn hr hfd (hsum.add hd.2)
      (fun z hz=>neumannSums_division hr D hH hHb hM hfd hfb hz)
    rw [modelTaylor_add hr hsum hd.2,
      modelTaylor_sum hr _ (fun j=>(hd.1 j).mul (hg j))] at hEq
    have hProducts (j : Fin k) : actualUnshiftedTaylorAlgHom n
        (modelGerm hr ((hd.1 j).mul (hg j)))=Q j*historicalNeumannFamily hr w H hH j:=
      modelTaylor_mul hr (hd.1 j) (hg j)
    exact hEq.trans (congrArg (fun A=>A+R) (Finset.sum_congr rfl (fun j _=>hProducts j)))
  · intro j β ho
    apply hs.1 j β
    intro hprev
    apply ho
    exact (historicalOwner_eq_some_iff w _ j).mpr ⟨le_add_self,hprev⟩
  · intro β ho
    apply hs.2 β
    intro hav
    exact ho ((historicalOwner_eq_none_iff w β).mpr hav)

theorem historicalFormalRemainder_monomial_neumann_zero {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,historicalNeumannFamily hr w H hH j∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (historicalNeumannFamily hr w H hH) q))
    (j : Fin k) (α : Fin n →₀ ℕ) (c : ℂ)
    (hzero : ∀z∈Metric.ball (0 : CoordinateSpace n) r,
      neumannRemainderSum r w H
        (fun x=>c*wordMonomial (wordOfExponent α) x*(wordMonomial (w j) x+H j x)) z=0) :
    historicalFormalRemainder w (historicalNeumannFamily hr w H hH) hmarked hwhole
      (MvPowerSeries.monomial α c*historicalNeumannFamily hr w H hH j)=0 := by
  let f : CoordinateSpace n → ℂ:=fun x=>c*wordMonomial (wordOfExponent α) x*(wordMonomial (w j) x+H j x)
  have hA : DifferentiableOn ℂ (fun x=>c*wordMonomial (wordOfExponent α) x) (Metric.ball 0 r):=
    (wordMonomial_differentiable (wordOfExponent α)).differentiableOn.const_mul c
  have hG : DifferentiableOn ℂ (fun x=>wordMonomial (w j) x+H j x) (Metric.ball 0 r):=
    (wordMonomial_differentiable (w j)).differentiableOn.add (hH j)
  have hf : DifferentiableOn ℂ f (Metric.ball 0 r):=hA.mul hG
  let M:=‖c‖*r^wordDegree (wordOfExponent α)*(r^wordDegree (w j)+D.epsilon)
  have hM : 0≤M:=mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _))
    (add_nonneg (pow_nonneg hr.le _) D.epsilon_pos.le)
  have hfb : ∀z∈Metric.ball (0 : CoordinateSpace n) r,‖f z‖≤M:=by
    intro z hz
    change ‖c*wordMonomial (wordOfExponent α) z*(wordMonomial (w j) z+H j z)‖≤_
    rw [norm_mul,norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (wordMonomial_norm_le _ hr hz) (norm_nonneg _))
      ((norm_add_le _ _).trans (add_le_add (wordMonomial_norm_le _ hr hz) (hHb j z hz)))
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _))
  have hTaylor : actualUnshiftedTaylorAlgHom n (modelGerm hr hf)=
      MvPowerSeries.monomial α c*historicalNeumannFamily hr w H hH j:=by
    rw [modelTaylor_mul hr hA hG,modelTaylor_scaled_word,wordExponent_wordOfExponent]
    rfl
  rw [←hTaylor,historicalFormalRemainder_eq_neumann hr w D H hH hHb hmarked hwhole hM hf hfb]
  have hd:=neumannSums_differentiableOn hr D hH hHb hM hf hfb
  have hEq:=modelTaylor_eqOn hr hd.2 (differentiableOn_const (c:=(0 : ℂ))) hzero
  change _=actualUnshiftedTaylorAlgHom n (HolGerm.mk (fun _ : ComplexModel n=>(0 : ℂ)) _) at hEq
  rw [HolGerm.mk_const,map_zero] at hEq
  simpa only [map_zero] using hEq

/-- The genuine analytic monomial zero law gives every polynomial zero
law by literal finite linearity, without an ideal/remainder certificate. -/
theorem historicalFormalRemainder_polynomial_zero_of_monomials
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hMono : ∀j α c,historicalFormalRemainder w g hmarked hwhole (MvPowerSeries.monomial α c*g j)=0) :
    ∀(j : Fin k)(P : MvPolynomial (Fin n) ℂ),
      historicalFormalRemainder w g hmarked hwhole ((P : MvPowerSeries (Fin n) ℂ)*g j)=0 := by
  intro j P
  induction P using MvPolynomial.induction_on' with
  | monomial α c=>simpa only [MvPolynomial.coe_monomial] using hMono j α c
  | add P Q hP hQ=>rw [MvPolynomial.coe_add,add_mul,map_add,hP,hQ,add_zero]

/-- The full old-supported formal ideal law, with arbitrary formal
multiplier coefficients. This is an OUTPUT of the actual moving producer. -/
def HistoricalWholeSupportedDivision (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) : Prop :=
  ∀F∈Ideal.span (range g),∃Q : Fin k → MvPowerSeries (Fin n) ℂ,
    F=∑j,Q j*g j ∧
    ∀j β,¬AvoidsCones ((List.ofFn w).take j.val) (β+wordExponent (w j)) →
      MvPowerSeries.coeff β (Q j)=0

theorem historicalWholeSupportedDivision_of_neumann_zero {r : ℝ} (hr : 0<r)
    (w : Fin k → CoordinateWord n) (D : ConcreteNeumannData r w)
    (H : Fin k → CoordinateSpace n → ℂ)
    (hH : ∀j,DifferentiableOn ℂ (H j) (Metric.ball 0 r))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) r,‖H j z‖≤D.epsilon)
    (hmarked : ∀j,historicalNeumannFamily hr w H hH j∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hzero : ∀j α c,∀z∈Metric.ball (0 : CoordinateSpace n) r,
      neumannRemainderSum r w H
        (fun x=>c*wordMonomial (wordOfExponent α) x*(wordMonomial (w j) x+H j x)) z=0) :
    HistoricalWholeSupportedDivision w (historicalNeumannFamily hr w H hH) := by
  classical
  have hwhole:=historicalWholeJetMap_bijective_of_neumann hr w D H hH hHb hmarked
  have hMono:=historicalFormalRemainder_monomial_neumann_zero hr w D H hH hHb hmarked hwhole
  have hPoly:=historicalFormalRemainder_polynomial_zero_of_monomials w _ hmarked hwhole
    (fun j α c=>hMono j α c (hzero j α c))
  intro F hF
  have hz:=historicalFormalRemainder_whole_ideal_zero w _ hmarked hwhole hPoly hF
  refine ⟨fun j=>historicalFormalQuotient w _ hmarked hwhole j F,?_,?_⟩
  · have hd:=historicalFormal_division w _ hmarked hwhole F
    rwa [hz,add_zero] at hd
  · intro j β hprev
    apply historicalFormalQuotient_support w _ hmarked hwhole F j β
    intro ho
    exact hprev ((historicalOwner_eq_some_iff w _ j).mp ho).2

def HistoricalComplementSeparatesIdeal (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) : Prop :=
  ∀F∈Ideal.span (range g),
    (∀β,historicalOwner w β≠none → MvPowerSeries.coeff β F=0) → F=0

theorem historicalComplement_separates_of_division (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hDivision : HistoricalWholeSupportedDivision w g) :
    HistoricalComplementSeparatesIdeal w g := by
  classical
  intro F hF hComp
  obtain ⟨Q,hDiv,hQ⟩:=hDivision F hF
  have hQowner : ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0:=by
    intro j β ho
    apply hQ j β
    intro hprev
    exact ho ((historicalOwner_eq_some_iff w _ j).mpr ⟨le_add_self,hprev⟩)
  have hZero : historicalFormalRemainder w g hmarked hwhole F=0:=by
    apply historicalFormalRemainder_eq_of_supported w g hmarked hwhole F Q 0
    · simpa only [add_zero] using hDiv
    · exact hQowner
    · intro β _
      exact map_zero _
  have hFix : historicalFormalRemainder w g hmarked hwhole F=F:=by
    apply historicalFormalRemainder_eq_of_supported w g hmarked hwhole F (fun _=>0) F
    · simp only [zero_mul,Finset.sum_const_zero,zero_add]
    · intro j β _
      exact map_zero _
    · exact hComp
  exact hFix.symm.trans hZero

/-- Reordering can change the individual owned regions, but SAME ideal
and SAME complement suffice for its full supported division law. -/
theorem historicalWholeSupportedDivision_of_complement_separation
    {l : ℕ} (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (v : Fin l → CoordinateWord n) (h : Fin l → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,h j∈genuineFormalVariables n^normalExponentDegree (wordExponent (v j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap v h q))
    (hSpan : Ideal.span (range h)=Ideal.span (range g))
    (hComplement : ∀β,historicalOwner v β=none ↔ historicalOwner w β=none)
    (hSeparate : HistoricalComplementSeparatesIdeal w g) :
    HistoricalWholeSupportedDivision v h := by
  classical
  intro F hF
  let Q:=fun j=>historicalFormalQuotient v h hmarked hwhole j F
  let R:=historicalFormalRemainder v h hmarked hwhole F
  have hDiv : F=(∑j,Q j*h j)+R:=historicalFormal_division v h hmarked hwhole F
  have hCombination : (∑j,Q j*h j)∈Ideal.span (range h):=by
    apply Ideal.sum_mem
    intro j _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  have hRas : R=F-∑j,Q j*h j:=eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hDiv.symm)
  have hRmem : R∈Ideal.span (range h):=by
    rw [hRas]
    exact Ideal.sub_mem _ hF hCombination
  have hRzero : R=0:=by
    apply hSeparate R (hSpan ▸ hRmem)
    intro β ho
    apply historicalFormalRemainder_support v h hmarked hwhole F β
    intro hnone
    exact ho ((hComplement β).mp hnone)
  refine ⟨Q,?_,?_⟩
  · simpa only [hRzero,add_zero] using hDiv
  · intro j β hprev
    apply historicalFormalQuotient_support v h hmarked hwhole F j β
    intro ho
    exact hprev ((historicalOwner_eq_some_iff v _ j).mp ho).2

theorem historicalDegreePrefixFull_range (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) {M : ℕ}
    (hBound : ∀j,normalExponentDegree (wordExponent (w j))≤M) :
    range (fun j=>g (historicalDegreePrefixLabel w M j))=range g := by
  ext F
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨historicalDegreePrefixLabel w M j,rfl⟩
  · rintro ⟨j,rfl⟩
    let e:=historicalDegreePrefixLabelEquiv w M
    let a:=e.symm ⟨j,hBound j⟩
    have he : historicalDegreePrefixLabel w M a=j:=
      congrArg (fun z : {i : Fin k // normalExponentDegree (wordExponent (w i))≤M}=>z.val)
        (e.apply_symm_apply ⟨j,hBound j⟩)
    exact ⟨a,congrArg g he⟩

theorem historicalDegreePrefixFull_complement (w : Fin k → CoordinateWord n) {M : ℕ}
    (hBound : ∀j,normalExponentDegree (wordExponent (w j))≤M) (β : Fin n →₀ ℕ) :
    historicalOwner (historicalDegreePrefixWords w M) β=none ↔ historicalOwner w β=none := by
  rw [historicalOwner_eq_none_iff,historicalOwner_eq_none_iff]
  constructor
  · intro h a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    let e:=historicalDegreePrefixLabelEquiv w M
    let b:=e.symm ⟨j,hBound j⟩
    have he : historicalDegreePrefixLabel w M b=j:=
      congrArg (fun z : {i : Fin k // normalExponentDegree (wordExponent (w i))≤M}=>z.val)
        (e.apply_symm_apply ⟨j,hBound j⟩)
    apply h (w j)
    exact List.mem_ofFn.mpr ⟨b,by dsimp only [historicalDegreePrefixWords]; rw [he]⟩
  · intro h a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    exact h _ (List.mem_ofFn.mpr ⟨historicalDegreePrefixLabel w M j,rfl⟩)

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

open OkaRelationSheaf OkaIdealOperations Hironaka.HolomorphicIdealSheaves

/-- The literal ENTIRE actual native stalk ideal, formed from all actual
membership germs of the current geometric strict sheaf. -/
def actualHistoricalWholeNativeIdeal (A : GermIdeal n (ComplexModel n)) (u : ComplexModel n) :
    Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span {g | ∃(f : ComplexModel n → ℂ)(hf : HolAt f u),A.mem u f ∧ g=translatedGerm u f hf}

theorem actualHistoricalWholeNativeIdeal_eq_span
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (u : ComplexModel n) (hu : u∈PHS.neighborhood) :
    actualHistoricalWholeNativeIdeal A u=Ideal.span (range fun j : Fin (actualVertexCount n I)=>
      translatedGerm u (PHS.representatives (actualVertexEnumeration n I j))
        (PHS.holomorphicAt _ hu _)) := by
  classical
  let S:=fun j : Fin (actualVertexCount n I)=>PHS.representatives (actualVertexEnumeration n I j)
  have hS : ∀j,HolAt (S j) u:=fun j=>PHS.holomorphicAt _ hu _
  have hGen (f : ComplexModel n → ℂ) : A.mem u f ↔ InSpanAt S u f:=
    (PHS.wholeGeneration u hu f).trans
      (CoherentIdealColon.inSpanAt_comp_equiv (actualVertexEnumeration n I) PHS.representatives u f).symm
  have hStalk (f : ComplexModel n → ℂ) (hf : HolAt f u) :
      A.mem u f ↔ translatedGerm u f hf∈translatedIdeal S u hS := by
    rw [←isInSpanAt_iff_translatedGerm_mem S u hS hf,CoherentIdealColon.isInSpanAt_range_iff]
    constructor
    · intro hA
      obtain ⟨hh,c,hc,he⟩:=(hGen f).mp hA
      exact ⟨hh.mono (fun _ hz=>hz.mdifferentiableAt),c,
        fun j=>(hc j).mono (fun _ hz=>hz.mdifferentiableAt),he⟩
    · rintro ⟨hh,c,hc,he⟩
      exact (hGen f).mpr ⟨hh.mono (fun _ hz=>hz.differentiableAt),c,
        fun j=>(hc j).mono (fun _ hz=>hz.differentiableAt),he⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hAf,rfl⟩
    exact (hStalk f hf).mp hAf
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply Ideal.subset_span
    refine ⟨S j,hS j,?_,rfl⟩
    exact (hStalk (S j) (hS j)).mpr (Ideal.subset_span ⟨j,rfl⟩)

/-- The full formal extension of the literal actual native stalk, pulled
back by the actual produced diagonal coordinate map. -/
def actualHistoricalScaledFormalIdeal (A : GermIdeal n (ComplexModel n))
    (u : ComplexModel n) (c : Fin n → ℂ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
    (Ideal.map (actualDiagonalPullback c).toRingHom (actualHistoricalWholeNativeIdeal A u))

theorem actualHistoricalScaledFormalIdeal_eq_span
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s≠0) (hs : s∈Metric.ball 0 P.radius)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (hu : scaledOriginalPoint P s p∈PHS.neighborhood)
    (hCov : ∀j : Fin (actualVertexCount n I),
      let a:=actualVertexEnumeration n I j
      let W:=degLexWeight n P.germs.degreeBound
      actualInheritedTranslatedGerm P hs p hdom j=
        HolGerm.constHom ((s^weightedDegree W a.val)⁻¹)*
          actualDiagonalPullback (fun i=>s^W i)
            (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives a) (PHS.holomorphicAt _ hu a))) :
    actualHistoricalScaledFormalIdeal A (scaledOriginalPoint P s p)
        (fun i=>s^(degLexWeight n P.germs.degreeBound i))=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) := by
  classical
  let N:=actualHistoricalWholeNativeIdeal A (scaledOriginalPoint P s p)
  let B:=Ideal.span (range fun j=>actualInheritedTranslatedGerm P hs p hdom j)
  let T:=actualDiagonalPullback (fun i=>s^(degLexWeight n P.germs.degreeBound i))
  have hSpan:=actualHistoricalWholeNativeIdeal_eq_span PHS (scaledOriginalPoint P s p) hu
  have hBack (j : Fin (actualVertexCount n I)) :
      T (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives (actualVertexEnumeration n I j))
        (PHS.holomorphicAt _ hu _))=
      HolGerm.constHom (s^weightedDegree (degLexWeight n P.germs.degreeBound) (actualVertexEnumeration n I j).val)*
        actualInheritedTranslatedGerm P hs p hdom j := by
    rw [hCov j,←mul_assoc,←map_mul,mul_inv_cancel₀ (pow_ne_zero _ hs0),map_one,one_mul]
  have hDiag : Ideal.map T.toRingHom N=B:=by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      change actualHistoricalWholeNativeIdeal A (scaledOriginalPoint P s p)≤_
      rw [hSpan]
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change T _∈B
      rw [hBack j]
      exact Ideal.mul_mem_left B _ (Ideal.subset_span ⟨j,rfl⟩)
    · apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change actualInheritedTranslatedGerm P hs p hdom j∈Ideal.map T.toRingHom N
      have hN : translatedGerm (scaledOriginalPoint P s p)
          (PHS.representatives (actualVertexEnumeration n I j)) (PHS.holomorphicAt _ hu _)∈N:=by
        change _∈actualHistoricalWholeNativeIdeal A (scaledOriginalPoint P s p)
        rw [hSpan]
        exact Ideal.subset_span ⟨j,rfl⟩
      exact Eq.mpr (congrArg (fun F : HolGerm (ComplexModel n)=>F∈Ideal.map T.toRingHom N) (hCov j))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem T.toRingHom hN))
  change Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.map T.toRingHom N)=_
  rw [hDiag]
  simp only [B,Ideal.map_span,←Set.range_comp']
  rfl

/-- ONE source/full/ALL-degree-prefix Neumann choice, including the actual
whole analytic zero-remainder law, before every moving point or numerator. -/
theorem exists_actual_inherited_joint_prefix_neumann_domain
    (hspan : Ideal.span (range G.germs)=I) :
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ),s≠0 ∧ s∈Metric.ball 0 P.radius ∧
      ∃(D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
        (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
        (Dp : ∀m : Fin (P.germs.degreeBound+1),ConcreteNeumannData (P.radius/2)
          (historicalDegreePrefixWords (actualVertexWords n I) m.val)) (δ : ℝ),0<δ ∧
      (∀j,∀z∈Metric.ball (0 : CoordinateSpace n) P.radius,
        ‖actualInheritedSourceScaledTail P s j z‖≤D₀.epsilon) ∧
      ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
        MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius) ∧
        (∀j,DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j) (Metric.ball 0 (P.radius/2))) ∧
        (∀j,∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
          ‖actualInheritedTranslatedTail P s p j z‖≤D₁.epsilon) ∧
        (∀(m : Fin (P.germs.degreeBound+1))(j : Fin (historicalDegreePrefixCount (actualVertexWords n I) m.val)),
          ∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
            ‖actualInheritedTranslatedTail P s p (historicalDegreePrefixLabel (actualVertexWords n I) m.val j) z‖≤
              (Dp m).epsilon) ∧
        ∀(A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ),
          (∀j,Differentiable ℂ (A j)) → ∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
            neumannRemainderSum (P.radius/2) (actualVertexWords n I)
              (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) z=0 := by
  classical
  obtain ⟨P⟩:=nonempty_actualInheritedWeightedTailData G
  obtain ⟨D₀⟩:=nonempty_concreteNeumannData P.radius P.radius_pos (actualVertexWords n I)
  obtain ⟨D₁⟩:=nonempty_concreteNeumannData (P.radius/2) (half_pos P.radius_pos) (actualVertexWords n I)
  let Dp (m : Fin (P.germs.degreeBound+1)) : ConcreteNeumannData (P.radius/2)
      (historicalDegreePrefixWords (actualVertexWords n I) m.val):=
    Classical.choice (nonempty_concreteNeumannData (P.radius/2) (half_pos P.radius_pos)
      (historicalDegreePrefixWords (actualVertexWords n I) m.val))
  let εp:=Finset.univ.inf' Finset.univ_nonempty (fun m : Fin (P.germs.degreeBound+1)=>(Dp m).epsilon)
  have hεp : 0<εp:=(Finset.lt_inf'_iff _).mpr fun m _=>(Dp m).epsilon_pos
  have hεple (m : Fin (P.germs.degreeBound+1)) : εp≤(Dp m).epsilon:=Finset.inf'_le _ (Finset.mem_univ m)
  let ε:=min D₀.epsilon (min (D₁.epsilon/2) (εp/2))
  have hε : 0<ε:=lt_min D₀.epsilon_pos (lt_min (half_pos D₁.epsilon_pos) (half_pos hεp))
  have hε0 : ε≤D₀.epsilon:=min_le_left _ _
  have hε1 : ε≤D₁.epsilon/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hεP (m : Fin (P.germs.degreeBound+1)) : ε≤(Dp m).epsilon/2:=by
    have h0 : ε≤εp/2:=(min_le_right _ _).trans (min_le_right _ _)
    have h1:=hεple m
    linarith
  obtain ⟨s,hs0,hs,_hhol,hsmall⟩:=exists_inherited_smallParameter P ε hε
  have hsource : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖≤D₀.epsilon:=by
    intro j z hz
    exact ((hsmall (actualVertexEnumeration n I j) z hz).2.le).trans hε0
  have hhead : ∀ᶠp : CoordinateSpace n in 𝓝 0,
      ∀j : Fin (actualVertexCount n I),∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
        ‖wordMonomial (actualVertexWords n I j) (p+z)-wordMonomial (actualVertexWords n I j) z‖<ε:=
    eventually_all.mpr fun j=>eventually_head_translate_small P.radius_pos hε (actualVertexWords n I j)
  obtain ⟨δ,hδ,hnear⟩:=Metric.eventually_nhds_iff_ball.mp
    ((eventually_translate_halfBall P.radius_pos).and hhead)
  refine ⟨P,s,hs0,hs,D₀,D₁,Dp,δ,hδ,hsource,?_⟩
  intro p hp
  have hdom:=(hnear p hp).1
  have hheads:=(hnear p hp).2
  have hHd (j) : DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j) (Metric.ball 0 (P.radius/2)):=
    (actual_coordinate_translation_differentiableOn
      (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom).sub
        (wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn
  have hsmallTarget (j) : ∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖≤2*ε:=by
    intro z hz
    have htail : ‖actualInheritedSourceScaledTail P s j (p+z)‖≤ε:=
      (hsmall (actualVertexEnumeration n I j) (p+z) (hdom hz)).2.le
    calc
      ‖actualInheritedTranslatedTail P s p j z‖=
          ‖actualInheritedSourceScaledTail P s j (p+z)+
            (wordMonomial (actualVertexWords n I j) (p+z)-wordMonomial (actualVertexWords n I j) z)‖:=by
        congr 1
        unfold actualInheritedTranslatedTail
        rw [actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs j (hdom hz)]
        ring
      _≤‖actualInheritedSourceScaledTail P s j (p+z)‖+
          ‖wordMonomial (actualVertexWords n I j) (p+z)-wordMonomial (actualVertexWords n I j) z‖:=norm_add_le _ _
      _≤ε+ε:=add_le_add htail (hheads j z hz).le
      _=2*ε:=by ring
  have hFull : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖≤D₁.epsilon:=by
    intro j z hz
    exact (hsmallTarget j z hz).trans (by linarith)
  refine ⟨hdom,hHd,hFull,?_,?_⟩
  · intro m j z hz
    exact (hsmallTarget (historicalDegreePrefixLabel (actualVertexWords n I) m.val j) z hz).trans
      (by have h:=hεP m; linarith)
  intro A hA z hz
  exact (actual_translated_neumann_division I G hspan P hs0 hs D₀ D₁ hsource p hdom hHd hFull A hA z hz).1

theorem actual_translated_whole_formal_supported_division
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs : s∈Metric.ball 0 P.radius)
    (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius))
    (hHd : ∀j,DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j) (Metric.ball 0 (P.radius/2)))
    (hHb : ∀j,∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖≤D₁.epsilon)
    (hAnZero : ∀(A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ),
      (∀j,Differentiable ℂ (A j)) → ∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
        neumannRemainderSum (P.radius/2) (actualVertexWords n I)
          (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) z=0)
    (hmarked : ∀j,actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j))) :
    (∀q,Function.Bijective (historicalWholeJetMap (actualVertexWords n I)
      (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) q)) ∧
    HistoricalWholeSupportedDivision (actualVertexWords n I)
      (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) := by
  classical
  have hId:=translated_neumann_family_taylor P hs p hdom hHd
  have hMarkedModel : ∀j,historicalNeumannFamily (half_pos P.radius_pos)
      (actualVertexWords n I) (actualInheritedTranslatedTail P s p) hHd j∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)):=by
    intro j
    change actualUnshiftedTaylorAlgHom n (modelGerm (half_pos P.radius_pos)
      ((wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn.add (hHd j)))∈_
    rw [hId j]
    exact hmarked j
  have hProperty:=historicalWholeSupportedDivision_of_neumann_zero (half_pos P.radius_pos)
    (actualVertexWords n I) D₁ (actualInheritedTranslatedTail P s p) hHd hHb hMarkedModel
  have hZero : ∀j α c,∀z∈Metric.ball (0 : CoordinateSpace n) (P.radius/2),
      neumannRemainderSum (P.radius/2) (actualVertexWords n I) (actualInheritedTranslatedTail P s p)
        (fun x=>c*wordMonomial (wordOfExponent α) x*
          (wordMonomial (actualVertexWords n I j) x+actualInheritedTranslatedTail P s p j x)) z=0 := by
    intro j α c
    let A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ:=
      fun i=>if i=j then fun x=>c*wordMonomial (wordOfExponent α) x else fun _=>0
    have hA : ∀i,Differentiable ℂ (A i):=by
      intro i
      by_cases hi : i=j
      · simpa only [A,if_pos hi] using (wordMonomial_differentiable (wordOfExponent α)).const_mul c
      · simpa only [A,if_neg hi] using (differentiable_const (c:=(0 : ℂ)))
    have hCombination : actualInheritedTranslatedCombination P s p A=
        (fun x=>c*wordMonomial (wordOfExponent α) x*
          (wordMonomial (actualVertexWords n I j) x+actualInheritedTranslatedTail P s p j x)):=by
      funext x
      change (∑i,A i x*actualInheritedSourceScaledFamily P s i (p+x))=_
      rw [Finset.sum_eq_single j]
      · simp only [A,if_pos rfl]
        unfold actualInheritedTranslatedTail
        ring
      · intro i _ hi
        simp only [A,if_neg hi,zero_mul]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [←hCombination]
    exact hAnZero A hA
  have hFamily : historicalNeumannFamily (half_pos P.radius_pos)
      (actualVertexWords n I) (actualInheritedTranslatedTail P s p) hHd=
        (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)):=funext hId
  refine ⟨?_,Eq.mp (congrArg (HistoricalWholeSupportedDivision (actualVertexWords n I)) hFamily) (hProperty hZero)⟩
  have hModelWhole : ∀q,Function.Bijective (historicalWholeJetMap (actualVertexWords n I)
      (historicalNeumannFamily (half_pos P.radius_pos) (actualVertexWords n I)
        (actualInheritedTranslatedTail P s p) hHd) q):=
    historicalWholeJetMap_bijective_of_neumann (half_pos P.radius_pos)
      (actualVertexWords n I) D₁ (actualInheritedTranslatedTail P s p) hHd hHb hMarkedModel
  exact Eq.mp (congrArg (fun g=>∀q,Function.Bijective (historicalWholeJetMap (actualVertexWords n I) g q)) hFamily) hModelWhole

/-- One genuine common scale and native window for the SAME historical
(1) exact orders, (2) every degree-prefix frame and (3) WHOLE formal ideal
supported division, with the literal ENTIRE actual strict-stalk ideal map. -/
def ActualHistoricalFormalPresentationNeighborhood
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
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
        actualHistoricalScaledFormalIdeal A (scaledOriginalPoint P s p)
            (fun i=>s^(degLexWeight n P.germs.degreeBound i))=
          Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
            (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))) ∧
        ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
          ActualHistoricalNativeExactOrderAt PHS (scaledOriginalPoint P s p) hu ∧
          (∀j : Fin (actualVertexCount n I),
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∈
              genuineFormalVariables n^normalExponentDegree (wordExponent (actualVertexWords n I j)) ∧
            actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)∉
              genuineFormalVariables n^(normalExponentDegree (wordExponent (actualVertexWords n I j))+1)) ∧
          (∀m,HistoricalDegreePrefixFrames (actualVertexWords n I)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) m) ∧
          HistoricalWholeSupportedDivision
            (historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound)
            (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
              (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))))

/-- Source geometric HS derives the same original orders and ALL-prefix
frames, and actual analytic covariance plus inverse limits proves whole
formal supported division for the ENTIRE same geometric strict-stalk ideal.
No order, rank, division, ideal comparison or presentation certificate is input. -/
theorem exists_actual_geometric_historical_formal_presentation_neighbourhood
    {A : Hironaka.HolomorphicIdealSheaves.GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (hspan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) :
    ActualHistoricalFormalPresentationNeighborhood PHS := by
  classical
  obtain ⟨P,s,hs0,hs,D₀,D₁,D,δ,hδ,_hsource,hnear⟩:=exists_actual_inherited_joint_prefix_neumann_domain hspan
  have hBound : ∀j : Fin (actualVertexCount n I),
      normalExponentDegree (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound:=by
    intro j
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using P.germs.degree_le (actualVertexEnumeration n I j)
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
  obtain ⟨hdom,hHd,hHbFull,hHb,hAnZero⟩:=hnear p hpδ
  have hCov:=scaled_translated_historical_germ PHS P hs p hdom O hO
    (fun x hx=>(hOsub hx).2) huO hu
  have hRawIdeal:=actualHistoricalScaledFormalIdeal_eq_span PHS P hs0 hs p hdom hu hCov
  have hFullSpan:=congrArg Ideal.span (historicalDegreePrefixFull_range (actualVertexWords n I)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hBound)
  refine ⟨hdom,hu,hCov,hRawIdeal.trans hFullSpan.symm,?_⟩
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
  have hAllFrames:=historicalDegreePrefixFrames_all_cutoffs (actualVertexWords n I)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hBound hFrames
  obtain ⟨hWholeOld,hSupportOld⟩:=actual_translated_whole_formal_supported_division
    P hs D₁ p hdom hHd hHbFull hAnZero hMarked
  have hSeparate:=historicalComplement_separates_of_division (actualVertexWords n I)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hMarked hWholeOld hSupportOld
  have hSupportSorted:=historicalWholeSupportedDivision_of_complement_separation (actualVertexWords n I)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j))
    (historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound)
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
      (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j)))
    (fun j=>hMarked (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))
    (hAllFrames P.germs.degreeBound).1 hFullSpan
    (historicalDegreePrefixFull_complement (actualVertexWords n I) hBound) hSeparate
  have hNotFormal:=actual_member_not_mem_succ_of_prefix_frames
    (fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom j)) hAllFrames
  refine ⟨?_,(fun j=>⟨hMarked j,hNotFormal j⟩),hAllFrames,hSupportSorted⟩
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

/-- ORIGINAL geometry produces the SAME stage and complete historical/global
continuation, with one actual common moving formal presentation (1)/(2)/(3)
and the literal ENTIRE actual strict-stalk ideal under its genuine coordinates. -/
theorem exists_actual_geometric_stage_with_historical_formal_presentation
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧ ActualHistoricalWholeJetNeighborhood PHS ∧ ActualHistoricalDegreePrefixJetNeighborhood PHS ∧ ActualHistoricalFormalPresentationNeighborhood PHS := by
  dsimp only
  obtain ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets⟩:=
    exists_actual_geometric_stage_with_degree_prefix_jets I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hHS
  refine ⟨hcut,e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,
    hRebaseLaws,hWeightedLaws,hHSTransition,hRepeated,hWholeJets,hDegreeJets,?_⟩
  exact exists_actual_geometric_historical_formal_presentation_neighbourhood D.targetSpan PHS



end
end Hironaka.HironakaActualHistoricalFormalSupportedDivision
