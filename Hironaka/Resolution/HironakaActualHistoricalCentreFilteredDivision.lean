import Hironaka.Resolution.HironakaActualHistoricalMovingSelectedContact
import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration

/-! Genuine coordinate-centre filtration for the ENTIRE supported division
of the SAME nonmonic historical family. Finite whole-jet subspaces force
inverse filtration; no weighted division or strict-generation certificate
is supplied. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaActualHistoricalCentreFilteredDivision
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
 HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyMonomialDivision
 HironakaActualCauchyCoordinateDivision HironakaActualFormalInitialDiagram
 HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
 HironakaActualHistoricalFormalSupportedDivision HironakaActualHistoricalMovingSelectedContact
 HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
 HironakaActualOriginalFormalHSTransfer
 HironakaActualOriginalFormalTaylor HironakaActualFreeProductGermTransport
 HironakaActualAnalyticBlockGraphTranslation HironakaActualInheritedAnalyticBlockJacobian
 HironakaActualFixedInheritedSelector HironakaHolomorphicJetChartInvariance
 HironakaActualUnshiftedInitialHSTransfer HironakaSmoothCentreRealDomainActualAmbientHS
 HironakaActualAnalyticFormalNormalPowers HironakaActualHistoricalMovingPrefixSupport
 HironakaActualCanonicalBlockJacobian HironakaActualInheritedNestedContactFlag

variable {n k : ℕ}

/-- Old supported quotient extraction lowers the TRUE coordinate-centre
weight by exactly the weight of its historical monomial head. -/
theorem historicalMonomialQuotient_mem_centre_power
    (w : Fin k → CoordinateWord n) (A : Set (Fin n)) (j : Fin k)
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    historicalMonomialQuotient w j F∈actualFormalCoordinateIdeal n A^
      (d-Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) := by
  classical
  apply (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mpr
  intro β hβ
  change (if historicalOwner w (β+wordExponent (w j))=some j then
    MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)=0
  split_ifs
  · apply (mem_actualFormalCoordinateIdeal_pow_iff A d F).mp hF
    rw [map_add]
    omega
  · rfl

theorem historicalMonomialRemainder_mem_centre_power
    (w : Fin k → CoordinateWord n) (A : Set (Fin n))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    historicalMonomialRemainder w F∈actualFormalCoordinateIdeal n A^d := by
  classical
  apply (mem_actualFormalCoordinateIdeal_pow_iff A d _).mpr
  intro β hβ
  change (if historicalOwner w β=none then MvPowerSeries.coeff β F else 0)=0
  split_ifs
  · exact (mem_actualFormalCoordinateIdeal_pow_iff A d F).mp hF β hβ
  · rfl

/-- Actual centre powers of the SAME members make the whole historical
operator preserve every actual coordinate-centre power. -/
theorem historicalReassemble_mem_centre_power
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (A : Set (Fin n))
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    historicalReassemble w g F∈actualFormalCoordinateIdeal n A^d := by
  change (∑j,historicalMonomialQuotient w j F*g j)+historicalMonomialRemainder w F∈_
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro j _
    have hm:=Ideal.mul_mem_mul (historicalMonomialQuotient_mem_centre_power w A j hF) (hcentre j)
    rw [←pow_add] at hm
    exact (Ideal.pow_le_pow_right (by omega)) hm
  · exact historicalMonomialRemainder_mem_centre_power w A hF

/-- The literal finite whole-jet subspace cut out by actual centre weight,
with no assertion of its dimension or determinant as an input. -/
def historicalCentreJetSubspace (A : Set (Fin n)) (d q : ℕ) :
    Submodule ℂ (normalExponentIndex n q → ℂ) where
  carrier:={v | ∀α,Finsupp.weight (actualCoordinateWeight A) α.val<d → v α=0}
  zero_mem':=by intro α _;rfl
  add_mem':=by
    intro v t hv ht α hα
    change v α+t α=0
    rw [hv α hα,ht α hα,add_zero]
  smul_mem':=by intro c v hv α hα;change c*v α=0;rw [hv α hα,mul_zero]

theorem boundedSeries_mem_centre_power
    (A : Set (Fin n)) (d q : ℕ) (v : normalExponentIndex n q → ℂ)
    (hv : v∈historicalCentreJetSubspace A d q) :
    boundedSeries q v∈actualFormalCoordinateIdeal n A^d := by
  classical
  apply (mem_actualFormalCoordinateIdeal_pow_iff A d _).mpr
  intro α hα
  change (if h : normalExponentDegree α<q then v ⟨α,h⟩ else 0)=0
  split_ifs with h
  · exact hv ⟨α,h⟩ hα
  · rfl

theorem boundedCoefficients_mem_centre_subspace
    (A : Set (Fin n)) (d q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    boundedCoefficients q F∈historicalCentreJetSubspace A d q := by
  intro α hα
  exact (mem_actualFormalCoordinateIdeal_pow_iff A d F).mp hF α.val hα

theorem historicalWholeJetOperator_preserves_centre_subspace
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (A : Set (Fin n))
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    (d q : ℕ) (v : normalExponentIndex n q → ℂ)
    (hv : v∈historicalCentreJetSubspace A d q) :
    historicalWholeJetOperator w g q v∈historicalCentreJetSubspace A d q :=
  boundedCoefficients_mem_centre_subspace A d q _
    (historicalReassemble_mem_centre_power w g A hcentre (boundedSeries_mem_centre_power A d q v hv))

/-- A genuine finite-dimensional subspace, not an assumed weighted division
certificate, forces the unique whole inverse to preserve every centre
power. This is the nonmonic whole-division form of BM97 Lemma 7.22. -/
theorem historicalFormalEquiv_symm_mem_centre_power
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (A : Set (Fin n))
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    (historicalFormalEquiv w g hmarked hwhole).symm F∈actualFormalCoordinateIdeal n A^d := by
  classical
  apply (mem_actualFormalCoordinateIdeal_pow_iff A d _).mpr
  intro α hα
  let q:=normalExponentDegree α+1
  let :=normalExponentFintype n q
  let S:=historicalCentreJetSubspace A d q
  let T : S →ₗ[ℂ] S:={
    toFun:=fun v=>⟨historicalWholeJetOperator w g q v.val,
      historicalWholeJetOperator_preserves_centre_subspace w g A hcentre d q v.val v.property⟩
    map_add':=by intro v t;apply Subtype.ext;exact map_add _ v.val t.val
    map_smul':=by intro c v;apply Subtype.ext;exact map_smul _ c v.val }
  have hInj : Function.Injective (historicalWholeJetOperator w g q):=by
    rw [←historicalWholeJetMap_eq_operator]
    exact (hwhole q).1
  have hTinj : Function.Injective T:=by
    intro v t h
    exact Subtype.ext (hInj (congrArg Subtype.val h))
  have hTsurj : Function.Surjective T:=(LinearMap.injective_iff_surjective).mp hTinj
  let vF : S:=⟨boundedCoefficients q F,boundedCoefficients_mem_centre_subspace A d q F hF⟩
  obtain ⟨v,hv⟩:=hTsurj vF
  have hForward : historicalWholeJetOperator w g q
      (boundedCoefficients q ((historicalFormalEquiv w g hmarked hwhole).symm F))=boundedCoefficients q F := by
    rw [←historicalWholeJetMap_eq_operator,historicalWholeJetMap_truncation w g hmarked]
    change boundedCoefficients q ((historicalFormalEquiv w g hmarked hwhole)
      ((historicalFormalEquiv w g hmarked hwhole).symm F))=boundedCoefficients q F
    rw [LinearEquiv.apply_symm_apply]
  have hInverse : boundedCoefficients q ((historicalFormalEquiv w g hmarked hwhole).symm F)=v.val:=
    hInj (hForward.trans (congrArg Subtype.val hv).symm)
  have hCoeff:=congrFun hInverse (⟨α,Nat.lt_succ_self _⟩ : normalExponentIndex n q)
  exact hCoeff.trans (v.property ⟨α,Nat.lt_succ_self _⟩ hα)

theorem historicalFormalQuotient_mem_centre_power
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (A : Set (Fin n))
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalCoordinateIdeal n A^d) (j : Fin k) :
    historicalFormalQuotient w g hmarked hwhole j F∈actualFormalCoordinateIdeal n A^
      (d-Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) :=
  historicalMonomialQuotient_mem_centre_power w A j
    (historicalFormalEquiv_symm_mem_centre_power w g hmarked hwhole A hcentre hF)

theorem historicalFormalRemainder_ideal_zero_of_supported_division
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (F : MvPowerSeries (Fin n) ℂ) (hI : F∈Ideal.span (range g)) :
    historicalFormalRemainder w g hmarked hwhole F=0 := by
  obtain ⟨Q,hDiv,hQ⟩:=hSupported F hI
  apply historicalFormalRemainder_eq_of_supported w g hmarked hwhole F Q 0
  · simpa only [add_zero] using hDiv
  · intro j β ho
    apply hQ j β
    intro hAvoid
    exact ho ((historicalOwner_eq_some_iff w (β+wordExponent (w j)) j).mpr
      ⟨le_add_self,hAvoid⟩)
  · intro β _
    exact map_zero _

/-- WHOLE division of every member of the SAME ideal, with actual
coordinate-centre powers on each original supported quotient. -/
theorem historical_formal_centre_power_whole_division
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A : Set (Fin n))
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hI : F∈Ideal.span (range g)) (hF : F∈actualFormalCoordinateIdeal n A^d) :
    F=∑j,historicalFormalQuotient w g hmarked hwhole j F*g j ∧
      ∀j,historicalFormalQuotient w g hmarked hwhole j F∈actualFormalCoordinateIdeal n A^
        (d-Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) := by
  refine ⟨?_,fun j=>historicalFormalQuotient_mem_centre_power w g hmarked hwhole A hcentre hF j⟩
  have hDiv:=historicalFormal_division w g hmarked hwhole F
  rw [historicalFormalRemainder_ideal_zero_of_supported_division w g hmarked hwhole hSupported F hI,
    add_zero] at hDiv
  exact hDiv

/-- Every normalized actual original member belongs to the finite ideal
of normalized SAME historical members. No current monic basis is selected. -/
theorem actualNormalizedFormalMember_mem_historical_span
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)))
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hI : F∈Ideal.span (range g)) (hF : F∈actualFormalCoordinateIdeal n A^d) :
    actualNormalizedFormalMember A e he b d F hF∈Ideal.span
      (range fun j=>actualNormalizedFormalMember A e he b
        (Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) (g j) (hcentre j)) := by
  let μ:=fun j=>Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))
  have hDiv:=historical_formal_centre_power_whole_division w g hmarked hwhole hSupported A hcentre d F hI hF
  let Q:=fun j=>historicalFormalQuotient w g hmarked hwhole j F
  let Qb:=fun j=>actualNormalizedFormalMember A e he b (d-μ j) (Q j) (hDiv.2 j)
  let gb:=fun j=>actualNormalizedFormalMember A e he b (μ j) (g j) (hcentre j)
  have hTerm (j : Fin k) : actualFormalBlowup A e b (Q j*g j)=
      (MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(μ j-d)*Qb j*gb j) := by
    rw [map_mul,←actualNormalizedFormalMember_spec A e he b (d-μ j) (Q j) (hDiv.2 j),
      ←actualNormalizedFormalMember_spec A e he b (μ j) (g j) (hcentre j)]
    change ((MvPowerSeries.X e)^(d-μ j)*Qb j)*((MvPowerSeries.X e)^(μ j)*gb j)=_
    calc
      _=(MvPowerSeries.X e)^((d-μ j)+μ j)*(Qb j*gb j) := by rw [pow_add];ring
      _=(MvPowerSeries.X e)^d*((MvPowerSeries.X e)^(μ j-d)*Qb j*gb j) := by
        rw [show (d-μ j)+μ j=d+(μ j-d) by omega,pow_add]
        ring
  have hNormalized : actualNormalizedFormalMember A e he b d F hF=
      ∑j,(MvPowerSeries.X e)^(μ j-d)*Qb j*gb j := by
    apply mul_left_cancel₀ (pow_ne_zero d (actualFormalExceptional_ne_zero e))
    calc
      _=actualFormalBlowup A e b F:=actualNormalizedFormalMember_spec A e he b d F hF
      _=actualFormalBlowup A e b (∑j,Q j*g j):=congrArg (actualFormalBlowup A e b) hDiv.1
      _=∑j,actualFormalBlowup A e b (Q j*g j):=map_sum _ _ _
      _=_:=by simp_rw [hTerm];exact (Finset.mul_sum _ _ _).symm
  rw [hNormalized]
  exact Ideal.sum_mem _ fun j _=>Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

/-- The ideal generated by normalized images of EVERY original formal
centre-power member is exactly the ideal of the transformed SAME family.
This is the nonmonic historical form of BM97 Corollary 7.24. -/
theorem actualNormalizedOriginalMemberIdeal_eq_historical_span
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) :
    actualNormalizedOriginalMemberIdeal (Ideal.span (range g)) A e he b=Ideal.span
      (range fun j=>actualNormalizedFormalMember A e he b
        (Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))) (g j) (hcentre j)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨d,F,hI,hF,rfl⟩
    exact actualNormalizedFormalMember_mem_historical_span w g hmarked hwhole hSupported A e he b hcentre d F hI hF
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.subset_span ⟨_,g j,Ideal.subset_span ⟨j,rfl⟩,hcentre j,rfl⟩

/-- The same inverse-filtration argument works for EVERY genuine
nonnegative coefficient weight; no weighted rank is an input. -/
def historicalWeightJetSubspace (W : Fin n → ℕ) (d q : ℕ) :
    Submodule ℂ (normalExponentIndex n q → ℂ) where
  carrier:={v | ∀α,Finsupp.weight W α.val<d → v α=0}
  zero_mem':=by intro α _;rfl
  add_mem':=by
    intro v t hv ht α hα
    change v α+t α=0
    rw [hv α hα,ht α hα,add_zero]
  smul_mem':=by intro c v hv α hα;change c*v α=0;rw [hv α hα,mul_zero]

theorem historicalMonomialQuotient_mem_weight
    (w : Fin k → CoordinateWord n) (W : Fin n → ℕ) (j : Fin k)
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalWeightVanishing W d) :
    historicalMonomialQuotient w j F∈actualFormalWeightVanishing W
      (d-Finsupp.weight W (wordExponent (w j))) := by
  classical
  intro β hβ
  change (if historicalOwner w (β+wordExponent (w j))=some j then
    MvPowerSeries.coeff (β+wordExponent (w j)) F else 0)=0
  split_ifs
  · apply hF
    rw [map_add]
    omega
  · rfl

theorem historicalMonomialRemainder_mem_weight
    (w : Fin k → CoordinateWord n) (W : Fin n → ℕ)
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F∈actualFormalWeightVanishing W d) :
    historicalMonomialRemainder w F∈actualFormalWeightVanishing W d := by
  classical
  intro β hβ
  change (if historicalOwner w β=none then MvPowerSeries.coeff β F else 0)=0
  split_ifs
  · exact hF β hβ
  · rfl

theorem historicalReassemble_mem_weight
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (W : Fin n → ℕ)
    (hg : ∀j,g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ} (hF : F∈actualFormalWeightVanishing W d) :
    historicalReassemble w g F∈actualFormalWeightVanishing W d := by
  change (∑j,historicalMonomialQuotient w j F*g j)+historicalMonomialRemainder w F∈_
  apply Ideal.add_mem
  · apply Ideal.sum_mem
    intro j _
    have hm:=actualFormalWeightVanishing_mul_mem W _ _ _ _
      (historicalMonomialQuotient_mem_weight w W j hF) (hg j)
    intro α hα
    exact hm α (by omega)
  · exact historicalMonomialRemainder_mem_weight w W hF

theorem boundedSeries_mem_weight
    (W : Fin n → ℕ) (d q : ℕ) (v : normalExponentIndex n q → ℂ)
    (hv : v∈historicalWeightJetSubspace W d q) :
    boundedSeries q v∈actualFormalWeightVanishing W d := by
  classical
  intro α hα
  change (if h : normalExponentDegree α<q then v ⟨α,h⟩ else 0)=0
  split_ifs with h
  · exact hv ⟨α,h⟩ hα
  · rfl

theorem boundedCoefficients_mem_weight_subspace
    (W : Fin n → ℕ) (d q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalWeightVanishing W d) :
    boundedCoefficients q F∈historicalWeightJetSubspace W d q :=
  fun α hα=>hF α.val hα

theorem historicalWholeJetOperator_preserves_weight_subspace
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (W : Fin n → ℕ)
    (hg : ∀j,g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))))
    (d q : ℕ) (v : normalExponentIndex n q → ℂ)
    (hv : v∈historicalWeightJetSubspace W d q) :
    historicalWholeJetOperator w g q v∈historicalWeightJetSubspace W d q :=
  boundedCoefficients_mem_weight_subspace W d q _
    (historicalReassemble_mem_weight w g W hg (boundedSeries_mem_weight W d q v hv))

theorem historicalWholeJetOperator_weight_subspace_iff
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (W : Fin n → ℕ)
    (hg : ∀j,g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))))
    (d q : ℕ) (hwhole : Function.Bijective (historicalWholeJetMap w g q))
    (v : normalExponentIndex n q → ℂ) :
    historicalWholeJetOperator w g q v∈historicalWeightJetSubspace W d q ↔
      v∈historicalWeightJetSubspace W d q := by
  classical
  let :=normalExponentFintype n q
  let S:=historicalWeightJetSubspace W d q
  let T : S →ₗ[ℂ] S:={
    toFun:=fun x=>⟨historicalWholeJetOperator w g q x.val,
      historicalWholeJetOperator_preserves_weight_subspace w g W hg d q x.val x.property⟩
    map_add':=by intro x y;apply Subtype.ext;exact map_add _ x.val y.val
    map_smul':=by intro c x;apply Subtype.ext;exact map_smul _ c x.val }
  have hInj : Function.Injective (historicalWholeJetOperator w g q):=by
    rw [←historicalWholeJetMap_eq_operator]
    exact hwhole.1
  constructor
  · intro hv
    have hTinj : Function.Injective T:=fun x y h=>Subtype.ext (hInj (congrArg Subtype.val h))
    have hTsurj : Function.Surjective T:=(LinearMap.injective_iff_surjective).mp hTinj
    obtain ⟨x,hx⟩:=hTsurj ⟨historicalWholeJetOperator w g q v,hv⟩
    have he : x.val=v:=hInj (congrArg Subtype.val hx)
    exact he ▸ x.property
  · exact historicalWholeJetOperator_preserves_weight_subspace w g W hg d q v

theorem historicalReassemble_sub_mem_weight_succ
    (w : Fin k → CoordinateWord n) (g h : Fin k → MvPowerSeries (Fin n) ℂ)
    (W : Fin n → ℕ)
    (hDiff : ∀j,h j-g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))+1))
    {d : ℕ} {F : MvPowerSeries (Fin n) ℂ} (hF : F∈actualFormalWeightVanishing W d) :
    historicalReassemble w h F-historicalReassemble w g F∈actualFormalWeightVanishing W (d+1) := by
  have he : historicalReassemble w h F-historicalReassemble w g F=
      ∑j,historicalMonomialQuotient w j F*(h j-g j) := by
    change ((∑j,historicalMonomialQuotient w j F*h j)+historicalMonomialRemainder w F)-
      ((∑j,historicalMonomialQuotient w j F*g j)+historicalMonomialRemainder w F)=_
    simp only [mul_sub,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply Ideal.sum_mem
  intro j _
  have hm:=actualFormalWeightVanishing_mul_mem W _ _ _ _
    (historicalMonomialQuotient_mem_weight w W j hF) (hDiff j)
  intro α hα
  exact hm α (by omega)

/-- A perturbation strictly raising any genuine finite coefficient weight
retains the whole historical jet basis. The proof derives nilpotence by
finite filtration, rather than assuming a target determinant. -/
theorem historicalWholeJetMap_bijective_of_weighted_perturbation
    (w : Fin k → CoordinateWord n) (g h : Fin k → MvPowerSeries (Fin n) ℂ)
    (W : Fin n → ℕ)
    (hg : ∀j,g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))))
    (hDiff : ∀j,h j-g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))+1))
    (q : ℕ) (hwhole : Function.Bijective (historicalWholeJetMap w g q)) :
    Function.Bijective (historicalWholeJetMap w h q) := by
  classical
  let :=normalExponentFintype n q
  let D:=Finset.univ.sup (fun α : normalExponentIndex n q=>Finsupp.weight W α.val)+1
  have hDiffOp (d : ℕ) (v : normalExponentIndex n q → ℂ)
      (hv : v∈historicalWeightJetSubspace W d q) :
      historicalWholeJetOperator w h q v-historicalWholeJetOperator w g q v∈
        historicalWeightJetSubspace W (d+1) q := by
    have hm:=historicalReassemble_sub_mem_weight_succ w g h W hDiff (boundedSeries_mem_weight W d q v hv)
    have hb:=boundedCoefficients_mem_weight_subspace W (d+1) q _ hm
    rw [map_sub] at hb
    exact hb
  have hInj : Function.Injective (historicalWholeJetOperator w h q):=by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro v hv
      have hz : historicalWholeJetOperator w h q v=0:=LinearMap.mem_ker.mp hv
      have hAll (d : ℕ) : v∈historicalWeightJetSubspace W d q:=by
        induction d with
        | zero => intro α hα;omega
        | succ d ih =>
            apply (historicalWholeJetOperator_weight_subspace_iff w g W hg (d+1) q hwhole v).mp
            have hDiffV:=hDiffOp d v ih
            rw [hz,zero_sub] at hDiffV
            simpa only [neg_neg] using (historicalWeightJetSubspace W (d+1) q).neg_mem hDiffV
      have hv0 : v=0:=by
        funext α
        have hα : Finsupp.weight W α.val<D:=Nat.lt_succ_of_le
          (Finset.le_sup (f:=fun β : normalExponentIndex n q=>Finsupp.weight W β.val) (Finset.mem_univ α))
        exact hAll D α hα
      exact hv0 ▸ (Submodule.zero_mem ⊥)
    · exact bot_le
  have hBij : Function.Bijective (historicalWholeJetOperator w h q):=
    ⟨hInj,(LinearMap.injective_iff_surjective).mp hInj⟩
  rw [historicalWholeJetMap_eq_operator]
  exact hBij

/-- Total degree, with a second positive weight on the fixed free variables.
This one weight detects a strict increase either in degree or in free
degree; its choice is independent of every future jet order. -/
def historicalFreeTieWeight (B : Set (Fin n)) (i : Fin n) : ℕ :=
  1+actualCoordinateWeight Bᶜ i

theorem historicalFreeTieWeight_degree (B : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (historicalFreeTieWeight B) α=
      normalExponentDegree α+Finsupp.weight (actualCoordinateWeight Bᶜ) α := by
  simp only [Finsupp.weight_eq_sum,historicalFreeTieWeight,smul_eq_mul,mul_add,mul_one,
    Finset.sum_add_distrib,normalExponentDegree]

theorem historical_free_weight_zero_iff (B : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Bᶜ) α=0 ↔ ∀i,i∉B → α i=0 := by
  classical
  rw [Finsupp.weight_eq_sum]
  constructor
  · intro h i hi
    have hLe : α i≤∑j,α j • actualCoordinateWeight Bᶜ j := by
      have hTerm : α i • actualCoordinateWeight Bᶜ i=α i:=by
        simp only [actualCoordinateWeight,mem_compl_iff,if_pos hi,smul_eq_mul,mul_one]
      rw [←hTerm]
      exact Finset.single_le_sum (f:=fun j=>α j • actualCoordinateWeight Bᶜ j)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hLe
    omega
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i∈B
    · simp only [actualCoordinateWeight,mem_compl_iff,if_neg (not_not.mpr hi),smul_eq_mul,mul_zero]
    · rw [h i hi,zero_smul]

theorem historicalFreeTieWeight_head
    (B : Set (Fin n)) (α : Fin n →₀ ℕ) (hα : ∀i,i∉B → α i=0) :
    Finsupp.weight (historicalFreeTieWeight B) α=normalExponentDegree α := by
  rw [historicalFreeTieWeight_degree,(historical_free_weight_zero_iff B α).mpr hα,add_zero]

/-- Equality of the actual pure-essential LEADING coefficients suffices to
retain the entire old historical jet basis. Higher terms and mixed free
terms may change; no moving monicity or target diagram is required. -/
theorem historicalWholeJetMap_bijective_of_pure_leading_agreement
    (w : Fin k → CoordinateWord n) (g h : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hh : ∀j,h j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (B : Set (Fin n)) (hHeads : ∀j i,i∉B → wordExponent (w j) i=0)
    (hLeading : ∀j α,normalExponentDegree α=normalExponentDegree (wordExponent (w j)) →
      (∀i,i∉B → α i=0) → MvPowerSeries.coeff α (h j)=MvPowerSeries.coeff α (g j))
    (q : ℕ) (hwhole : Function.Bijective (historicalWholeJetMap w g q)) :
    Function.Bijective (historicalWholeJetMap w h q) := by
  let W:=historicalFreeTieWeight B
  have hDegree (α : Fin n →₀ ℕ) : normalExponentDegree α≤Finsupp.weight W α:=by
    rw [historicalFreeTieWeight_degree]
    omega
  have hHead (j : Fin k) : Finsupp.weight W (wordExponent (w j))=
      normalExponentDegree (wordExponent (w j)):=historicalFreeTieWeight_head B _ (hHeads j)
  have hgW (j : Fin k) : g j∈actualFormalWeightVanishing W (Finsupp.weight W (wordExponent (w j))) := by
    intro α hα
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mp (hg j) α
    rw [hHead] at hα
    exact lt_of_le_of_lt (hDegree α) hα
  have hDiff (j : Fin k) : h j-g j∈actualFormalWeightVanishing W
      (Finsupp.weight W (wordExponent (w j))+1) := by
    intro α hα
    rw [map_sub]
    rw [hHead] at hα
    have hDegreeLe : normalExponentDegree α≤normalExponentDegree (wordExponent (w j)):=by
      have h:=hDegree α
      omega
    by_cases hLow : normalExponentDegree α<normalExponentDegree (wordExponent (w j))
    · rw [(mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mp (hh j) α hLow,
        (mem_genuineFormalVariables_pow_iff_coefficients_zero n _ _).mp (hg j) α hLow,sub_self]
    · have hEqual : normalExponentDegree α=normalExponentDegree (wordExponent (w j)):=by omega
      have hFree : Finsupp.weight (actualCoordinateWeight Bᶜ) α=0:=by
        rw [historicalFreeTieWeight_degree,hEqual] at hα
        omega
      exact sub_eq_zero.mpr (hLeading j α hEqual ((historical_free_weight_zero_iff B α).mp hFree))
  exact historicalWholeJetMap_bijective_of_weighted_perturbation w g h W hgW hDiff q hwhole

/-- The genuine zero-dimensional reassociation in the whole Taylor map
retains the original maximal-power kernel at EVERY order. -/
theorem actual_maximal_power_iff_formal_coefficients_zero (r d : ℕ)
    (F : HolGerm (ComplexModel r)) :
    F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel r))^d ↔
      ∀α : Fin r →₀ ℕ,normalExponentDegree α<d →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom r F)=0 := by
  let P (s : ℕ) (f : HolGerm (ComplexModel s) →ₐ[ℂ] MvPowerSeries (Fin r) ℂ) : Prop:=
    ∀g,g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel s))^d ↔
      ∀α : Fin r →₀ ℕ,normalExponentDegree α<d → MvPowerSeries.coeff α (f g)=0
  have hOriginal : P (0+r) (originalTaylorAlgHom r):=
    mem_original_maximal_pow_iff_formal_coefficients_zero r d
  have transport {s : ℕ} (h : s=r)
      (f : HolGerm (ComplexModel s) →ₐ[ℂ] MvPowerSeries (Fin r) ℂ) (hf : P s f) :
      P r (cast (congrArg (fun j=>HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin r) ℂ) h) f) := by
    subst s
    exact hf
  exact transport (Nat.zero_add r) (originalTaylorAlgHom r) hOriginal F

theorem actualTaylor_mem_power_of_maximal_power (r d : ℕ) (F : HolGerm (ComplexModel r))
    (hF : F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel r))^d) :
    actualUnshiftedTaylorAlgHom r F∈genuineFormalVariables r^d :=
  (mem_genuineFormalVariables_pow_iff_coefficients_zero r d _).mpr
    ((actual_maximal_power_iff_formal_coefficients_zero r d F).mp hF)

/-- An actual inverse product chart fixes EVERY pure-essential coefficient
of the SAME member, without any monic/lower hypothesis on that member. -/
theorem actualFreeProduct_pure_coefficient (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (F : HolGerm (ComplexModel (m+e))) (α : Fin (m+e) →₀ ℕ)
    (hα : ∀i : Fin (m+e),¬ m ≤ i.val → α i=0) :
    MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (m+e)
      (actualFreeProductGermEquiv m e χ hχ0 F))=
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (m+e) F) := by
  have hSection:=(actualFreeProductGermEquiv_section_coordinates m e χ hχ0).2 F
  have hTaylor:=congrArg (actualUnshiftedTaylorAlgHom (m+e)) hSection
  have hProjection (H : HolGerm (ComplexModel (m+e))) :
      actualUnshiftedTaylorAlgHom (m+e) (actualBlockProjectionGermHom {i : Fin (m+e) | m ≤ i.val} H)=
        actualFormalBlockCoordinateProjection {i : Fin (m+e) | m ≤ i.val} (actualUnshiftedTaylorAlgHom (m+e) H):=
    DFunLike.congr_fun (actualTaylor_blockProjection _) H
  rw [hProjection,hProjection] at hTaylor
  have hCoeff:=congrArg (MvPowerSeries.coeff α) hTaylor
  rw [coeff_actualFormalBlockCoordinateProjection,coeff_actualFormalBlockCoordinateProjection] at hCoeff
  simpa only [mem_ofPred_eq,if_pos hα] using hCoeff

/-- A genuine free-coordinate flattening preserves the SAME entire
historical whole-jet basis of a NONMONIC moving family. It is the real
whole-germ inverse pullback of that chart, not a supplied target frame. -/
theorem actualFreeProduct_historical_whole_jets (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (w : Fin k → CoordinateWord (m+e)) (Γ : Fin k → HolGerm (ComplexModel (m+e)))
    (hmarked : ∀j,Γ j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (w j)))
    (hHeads : ∀(j : Fin k)(i : Fin (m+e)),¬ m ≤ i.val → wordExponent (w j) i=0)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j)) q)) :
    ∀q,Function.Bijective (historicalWholeJetMap w
      (fun j=>actualUnshiftedTaylorAlgHom (m+e) (actualFreeProductGermEquiv m e χ hχ0 (Γ j))) q) := by
  let E:=actualFreeProductGermEquiv m e χ hχ0
  have hTarget (j : Fin k) : E (Γ j)∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (w j)) := by
    have hm:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom (hmarked j)
    have hMap : Ideal.map E.toRingEquiv.toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
          normalExponentDegree (wordExponent (w j)))=
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
          normalExponentDegree (wordExponent (w j)) := by
      rw [Ideal.map_pow]
      exact congrArg (fun J : Ideal (HolGerm (ComplexModel (m+e)))=>J^
        normalExponentDegree (wordExponent (w j)))
        (IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv)
    rwa [hMap] at hm
  intro q
  exact historicalWholeJetMap_bijective_of_pure_leading_agreement w
    (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j))
    (fun j=>actualUnshiftedTaylorAlgHom (m+e) (E (Γ j)))
    (fun j=>actualTaylor_mem_power_of_maximal_power _ _ _ (hmarked j))
    (fun j=>actualTaylor_mem_power_of_maximal_power _ _ _ (hTarget j))
    {i : Fin (m+e) | m ≤ i.val} hHeads
    (fun j α _ hα=>actualFreeProduct_pure_coefficient m e χ hχ0 (Γ j) α hα) q (hwhole q)

/-- The literal original DEGREE prefixes and their homogeneous columns
survive the genuine free flattening, with the exact old label inclusions.
No prefix rank or homogeneous determinant is supplied. -/
theorem actualFreeProduct_historical_degree_prefix_frames (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (w : Fin k → CoordinateWord (m+e)) (Γ : Fin k → HolGerm (ComplexModel (m+e)))
    (hmarked : ∀j,Γ j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (w j)))
    (hHeads : ∀(j : Fin k)(i : Fin (m+e)),¬ m ≤ i.val → wordExponent (w j) i=0)
    (hFrames : ∀r,HistoricalDegreePrefixFrames w (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j)) r) :
    ∀r,HistoricalDegreePrefixFrames w
      (fun j=>actualUnshiftedTaylorAlgHom (m+e) (actualFreeProductGermEquiv m e χ hχ0 (Γ j))) r := by
  intro r
  let wp:=historicalDegreePrefixWords w r
  let Γp:=fun j=>Γ (historicalDegreePrefixLabel w r j)
  have hMarkp : ∀j,Γp j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (wp j)):=fun j=>hmarked _
  have hHeadp : ∀(j : Fin (historicalDegreePrefixCount w r))(i : Fin (m+e)),
      ¬ m ≤ i.val → wordExponent (wp j) i=0:=fun j=>hHeads _
  have hWhole:=actualFreeProduct_historical_whole_jets m e χ hχ0 wp Γp hMarkp hHeadp (hFrames r).1
  refine ⟨hWhole,?_⟩
  intro d
  rw [historicalHomogeneousColumnMap_eq_operator]
  apply historicalHomogeneousOperator_bijective _ _ _ hWhole d
  intro j
  apply actualTaylor_mem_power_of_maximal_power
  let E:=actualFreeProductGermEquiv m e χ hχ0
  have hm:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom (hMarkp j)
  have hMap : Ideal.map E.toRingEquiv.toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
        normalExponentDegree (wordExponent (wp j)))=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
        normalExponentDegree (wordExponent (wp j)) := by
    rw [Ideal.map_pow]
    exact congrArg (fun J : Ideal (HolGerm (ComplexModel (m+e)))=>J^
      normalExponentDegree (wordExponent (wp j)))
      (IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv)
  rwa [hMap] at hm

/-- The actual bounded OLD complement, as a subspace of the same whole
coefficient jet. It is not the newly chosen diagram of a moving ideal. -/
def historicalComplementJetSpace (w : Fin k → CoordinateWord n) (q : ℕ) :
    Submodule ℂ (normalExponentIndex n q → ℂ) where
  carrier:={v | ∀α,historicalOwner w α.val≠none → v α=0}
  zero_mem':=by intro α _;rfl
  add_mem':=by
    intro v t hv ht α hα
    change v α+t α=0
    rw [hv α hα,ht α hα,add_zero]
  smul_mem':=by intro c v hv α hα;change c*v α=0;rw [hv α hα,mul_zero]

def historicalComplementQuotientMap (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    historicalComplementJetSpace w q →ₗ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (Ideal.span (range g)⊔genuineFormalVariables n^q)) :=
  ((Ideal.Quotient.mkₐ ℂ (Ideal.span (range g)⊔genuineFormalVariables n^q)).toLinearMap.comp
    (boundedSeries q)).comp (historicalComplementJetSpace w q).subtype

theorem historicalComplement_boundedSeries_support (w : Fin k → CoordinateWord n)
    (q : ℕ) (v : historicalComplementJetSpace w q) (α : Fin n →₀ ℕ)
    (hα : historicalOwner w α≠none) : MvPowerSeries.coeff α (boundedSeries q v.val)=0 := by
  classical
  change (if h : normalExponentDegree α<q then v.val ⟨α,h⟩ else 0)=0
  split_ifs with h
  · exact v.property ⟨α,h⟩ hα
  · rfl

theorem historicalFormalRemainder_complement_lift
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (q : ℕ) (v : historicalComplementJetSpace w q) :
    historicalFormalRemainder w g hmarked hwhole (boundedSeries q v.val)=boundedSeries q v.val := by
  apply historicalFormalRemainder_eq_of_supported w g hmarked hwhole _ (fun _=>0) _
  · simp only [zero_mul,Finset.sum_const_zero,zero_add]
  · intro _ _ _
    exact map_zero _
  · exact historicalComplement_boundedSeries_support w q v

/-- Whole historical jets make the OLD complement reach every genuine
whole ideal quotient, even before zero remainder on that ideal is known. -/
theorem historicalComplementQuotientMap_surjective
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q)) (q : ℕ) :
    Function.Surjective (historicalComplementQuotientMap w g q) := by
  intro z
  obtain ⟨F,rfl⟩:=Ideal.Quotient.mk_surjective z
  let R:=historicalFormalRemainder w g hmarked hwhole F
  let v : historicalComplementJetSpace w q:=⟨boundedCoefficients q R,
    fun α ho=>historicalFormalRemainder_support w g hmarked hwhole F α.val ho⟩
  refine ⟨v,?_⟩
  change Ideal.Quotient.mk (Ideal.span (range g)⊔genuineFormalVariables n^q)
    (boundedSeries q v.val)=Ideal.Quotient.mk _ F
  apply Ideal.Quotient.eq.mpr
  have hSource : F-R∈Ideal.span (range g) := by
    have hDiv:=historicalFormal_division w g hmarked hwhole F
    have hEq : F-R=∑j,historicalFormalQuotient w g hmarked hwhole j F*g j:=by
      exact sub_eq_iff_eq_add.mpr hDiv
    rw [hEq]
    exact Ideal.sum_mem _ fun j _=>Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  have hR : R-boundedSeries q v.val∈genuineFormalVariables n^q:=sub_boundedSeries_mem_power q R
  have hTotal : F-boundedSeries q v.val∈Ideal.span (range g)⊔genuineFormalVariables n^q := by
    have he : F-boundedSeries q v.val=(F-R)+(R-boundedSeries q v.val):=by abel
    rw [he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hSource) (Ideal.mem_sup_right hR)
  simpa only [neg_sub] using (Ideal.span (range g)⊔genuineFormalVariables n^q).neg_mem hTotal

/-- Actual whole supported division separates the old complement in every
whole ideal quotient. This does not identify a moving initial diagram. -/
theorem historicalComplementQuotientMap_injective
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g) (q : ℕ) :
    Function.Injective (historicalComplementQuotientMap w g q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro v hv
    have hz:=LinearMap.mem_ker.mp hv
    change Ideal.Quotient.mk (Ideal.span (range g)⊔genuineFormalVariables n^q) (boundedSeries q v.val)=0 at hz
    obtain ⟨F,hF,Z,hZ,hSum⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hRem:=congrArg (historicalFormalRemainder w g hmarked hwhole) hSum
    rw [map_add,historicalFormalRemainder_ideal_zero_of_supported_division w g hmarked hwhole hSupported F hF,
      zero_add,historicalFormalRemainder_complement_lift] at hRem
    have hPower : boundedSeries q v.val∈genuineFormalVariables n^q:=
      hRem ▸ historicalFormalRemainder_mem_power w g hmarked hwhole hZ
    have hv0 : v=0:=by
      apply Subtype.ext
      funext α
      have hzα:=(mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hPower α.val α.property
      have hRecover:=congrFun (boundedCoefficients_boundedSeries q v.val) α
      exact hRecover.symm.trans hzα
    exact hv0 ▸ (Submodule.zero_mem ⊥)
  · exact bot_le

/-- Equal ACTUAL whole ideal quotient dimensions, together with derived
whole jets, force supported division of the entire target ideal. The
dimension equality will be discharged by the genuine free-chart ring
equivalence; it is not used for a blowup equality conclusion. -/
theorem historicalWholeSupportedDivision_of_equal_quotient_dimensions
    (w : Fin k → CoordinateWord n) (g h : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hh : ∀j,h j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hWholeG : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hWholeH : ∀q,Function.Bijective (historicalWholeJetMap w h q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (hDimensions : ∀q,Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸
      (Ideal.span (range g)⊔genuineFormalVariables n^q))=
      Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸ (Ideal.span (range h)⊔genuineFormalVariables n^q))) :
    HistoricalWholeSupportedDivision w h := by
  classical
  have hTargetInj (q : ℕ) : Function.Injective (historicalComplementQuotientMap w h q) := by
    let :=normalExponentFintype n q
    let SG:=historicalComplementQuotientMap w g q
    let SH:=historicalComplementQuotientMap w h q
    have hSG : Function.Bijective SG:=
      ⟨historicalComplementQuotientMap_injective w g hg hWholeG hSupported q,
        historicalComplementQuotientMap_surjective w g hg hWholeG q⟩
    have hSH : Function.Surjective SH:=historicalComplementQuotientMap_surjective w h hh hWholeH q
    let : FiniteDimensional ℂ (MvPowerSeries (Fin n) ℂ ⧸
        (Ideal.span (range h)⊔genuineFormalVariables n^q)):=FiniteDimensional.of_surjective SH hSH
    have hDim : Module.finrank ℂ (historicalComplementJetSpace w q)=
        Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸ (Ideal.span (range h)⊔genuineFormalVariables n^q)):=
      (LinearEquiv.ofBijective SG hSG).finrank_eq.trans (hDimensions q)
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hDim).mpr hSH
  intro F hF
  have hZero : historicalFormalRemainder w h hh hWholeH F=0 := by
    let R:=historicalFormalRemainder w h hh hWholeH F
    have hRIdeal : R∈Ideal.span (range h) := by
      have hDiv:=historicalFormal_division w h hh hWholeH F
      have hEq : R=F-∑j,historicalFormalQuotient w h hh hWholeH j F*h j:=by
        exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hDiv.symm))
      rw [hEq]
      exact Ideal.sub_mem _ hF (Ideal.sum_mem _ fun j _=>Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩))
    ext α
    let q:=normalExponentDegree α+1
    let v : historicalComplementJetSpace w q:=⟨boundedCoefficients q R,
      fun β ho=>historicalFormalRemainder_support w h hh hWholeH F β.val ho⟩
    have hv : historicalComplementQuotientMap w h q v=0 := by
      change Ideal.Quotient.mk (Ideal.span (range h)⊔genuineFormalVariables n^q) (boundedSeries q v.val)=0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hDiff : R-boundedSeries q v.val∈genuineFormalVariables n^q:=sub_boundedSeries_mem_power q R
      have hEq : boundedSeries q v.val=R-(R-boundedSeries q v.val):=by abel
      rw [hEq]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hRIdeal) (Ideal.mem_sup_right hDiff)
    have hv0 : v=0:=(hTargetInj q) (hv.trans (map_zero _).symm)
    exact congrFun (congrArg Subtype.val hv0) (⟨α,Nat.lt_succ_self _⟩ : normalExponentIndex n q)
  refine ⟨fun j=>historicalFormalQuotient w h hh hWholeH j F,?_,?_⟩
  · have hDiv:=historicalFormal_division w h hh hWholeH F
    simpa only [hZero,add_zero] using hDiv
  · intro j β hAvoid
    apply historicalFormalQuotient_support w h hh hWholeH F j β
    intro ho
    exact hAvoid ((historicalOwner_eq_some_iff w (β+wordExponent (w j)) j).mp ho).2

/-- The genuine analytic local ring equivalence preserves the HS of the
ENTIRE Taylor-extended family ideal, not only its finite member jets. -/
theorem actual_family_formal_hs_map_algEquiv
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
    (Γ : Fin k → HolGerm (ComplexModel n)) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n
      (Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j)))) ℓ=
    genuineFormalHilbertSamuelValue n
      (Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (Γ j))) ℓ := by
  let I:=Ideal.span (range Γ)
  have hSource : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) := by
    dsimp only [I]
    rw [Ideal.map_span,←Set.range_comp]
    rfl
  have hTarget : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map E.toRingEquiv.toRingHom I)=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j))) := by
    dsimp only [I]
    rw [Ideal.map_span,Ideal.map_span,←Set.range_comp,←Set.range_comp]
    rfl
  calc
    _=HironakaHolomorphicPointJets.hilbertSamuelValue (Ideal.map E.toRingEquiv.toRingHom I) ℓ:=by
      rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,hTarget]
    _=HironakaHolomorphicPointJets.hilbertSamuelValue I ℓ:=actualAmbientHS_eq_of_genuineAlgEquiv E I ℓ
    _=_:=by rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,hSource]

/-- Whole supported formal division is transported through a genuine free
flattening of the SAME nonmonic analytic family. The target quotient
dimensions are derived from the actual ring equivalence, not assumed. -/
theorem actualFreeProduct_historical_whole_supported_division (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (w : Fin k → CoordinateWord (m+e)) (Γ : Fin k → HolGerm (ComplexModel (m+e)))
    (hmarked : ∀j,Γ j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (w j)))
    (hHeads : ∀(j : Fin k)(i : Fin (m+e)),¬ m ≤ i.val → wordExponent (w j) i=0)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j))) :
    HistoricalWholeSupportedDivision w
      (fun j=>actualUnshiftedTaylorAlgHom (m+e) (actualFreeProductGermEquiv m e χ hχ0 (Γ j))) := by
  let E:=actualFreeProductGermEquiv m e χ hχ0
  have hTarget (j : Fin k) : E (Γ j)∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
      normalExponentDegree (wordExponent (w j)) := by
    have hm:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom (hmarked j)
    have hMap : Ideal.map E.toRingEquiv.toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
          normalExponentDegree (wordExponent (w j)))=
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+e)))^
          normalExponentDegree (wordExponent (w j)) := by
      rw [Ideal.map_pow]
      exact congrArg (fun J : Ideal (HolGerm (ComplexModel (m+e)))=>J^
        normalExponentDegree (wordExponent (w j)))
        (IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv)
    rwa [hMap] at hm
  apply historicalWholeSupportedDivision_of_equal_quotient_dimensions w
    (fun j=>actualUnshiftedTaylorAlgHom (m+e) (Γ j))
    (fun j=>actualUnshiftedTaylorAlgHom (m+e) (E (Γ j)))
    (fun j=>actualTaylor_mem_power_of_maximal_power _ _ _ (hmarked j))
    (fun j=>actualTaylor_mem_power_of_maximal_power _ _ _ (hTarget j))
    hwhole (actualFreeProduct_historical_whole_jets m e χ hχ0 w Γ hmarked hHeads hwhole) hSupported
  intro q
  cases q with
  | zero =>
      have hZero (J : Ideal (MvPowerSeries (Fin (m+e)) ℂ)) :
          J⊔genuineFormalVariables (m+e)^0=⊤ := by
        rw [pow_zero,Ideal.one_eq_top,sup_top_eq]
      exact congrArg (fun J : Ideal (MvPowerSeries (Fin (m+e)) ℂ)=>
        Module.finrank ℂ (MvPowerSeries (Fin (m+e)) ℂ ⧸ J))
        ((hZero _).trans (hZero _).symm)
  | succ ℓ => exact (actual_family_formal_hs_map_algEquiv E Γ ℓ).symm

theorem actualFreeProduct_historical_eval (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (F : HolGerm (ComplexModel (m+e))) :
    HolGerm.eval (actualFreeProductGermEquiv m e χ hχ0 F)=HolGerm.eval F := by
  rw [←HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    ←HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero]
  exact actualFreeProduct_pure_coefficient m e χ hχ0 F 0 (fun _ _=>rfl)

theorem actualFreeProduct_historical_coordinate_derivative (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    (i : Fin (m+e)) (hi : m ≤ i.val) (F : HolGerm (ComplexModel (m+e))) :
    actualAnalyticCoordinateDerivative i (actualFreeProductGermEquiv m e χ hχ0 F)=
      actualFreeProductGermEquiv m e χ hχ0 (actualAnalyticCoordinateDerivative i F) := by
  have hSingle (H : HolGerm (ComplexModel (m+e))) :
      actualAnalyticMultiDerivative (Finsupp.single i 1) H=actualAnalyticCoordinateDerivative i H := by
    apply actualUnshiftedTaylorAlgHom_injective
    rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_actualAnalyticCoordinateDerivative]
    simpa only [zero_add,actualFormalMultiDerivative_zero] using
      actualFormalMultiDerivative_add_single 0 i (actualUnshiftedTaylorAlgHom (m+e) H)
  have hPure (j : Fin (m+e)) (hj : ¬ m ≤ j.val) : (Finsupp.single i 1 : Fin (m+e) →₀ ℕ) j=0:=
    Finsupp.single_eq_of_ne (show j≠i from fun h=>hj (h.symm ▸ hi))
  have h:=actualFreeProductGermEquiv_multiDerivative m e χ hχ0 (Finsupp.single i 1) hPure F
  simpa only [hSingle] using h

theorem actualFreeProduct_historical_selected_derivative (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hHeads : ∀(a : V)(i : Fin (m+e)),¬ m ≤ i.val → a.val i=0)
    (S : ActualFixedInheritedSelector V) (Γ : V → HolGerm (ComplexModel (m+e)))
    (j : fixedSelectorEssential V) :
    actualFixedSelectorDerivative S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a)) j=
      actualFreeProductGermEquiv m e χ hχ0 (actualFixedSelectorDerivative S Γ j) := by
  apply actualFreeProductGermEquiv_multiDerivative
  intro i hi
  simp only [fixedSelectorBeta,Finsupp.tsub_apply,hHeads (S.selected j) i hi,zero_tsub]

/-- WHOLE selected contact and the literal block Jacobian commute with the
actual free flattening of a nonmonic historical family. The selector is
unchanged, and target rank is an output. -/
theorem actualFreeProduct_historical_selected_contact (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hHeads : ∀(a : V)(i : Fin (m+e)),¬ m ≤ i.val → a.val i=0)
    (S : ActualFixedInheritedSelector V) (Γ : V → HolGerm (ComplexModel (m+e)))
    (hContact : ∀r,actualFixedSelectorContactAt S Γ r)
    (hdet : ∀r,(actualFixedSelectorJacobian S Γ r).det≠0) :
    ∀r,actualFixedSelectorContactAt S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a)) r ∧
      actualFixedSelectorJacobian S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a)) r=
        actualFixedSelectorJacobian S Γ r ∧
      (actualFixedSelectorJacobian S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a)) r).det≠0 := by
  intro r
  have hBlock (i : Fin (m+e)) (hi : i∈fixedSelectorBlock V r) : m ≤ i.val := by
    obtain ⟨a,_ha,hai⟩:=hi
    by_contra h
    exact hai (hHeads a i h)
  have hJac : actualFixedSelectorJacobian S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a)) r=
      actualFixedSelectorJacobian S Γ r := by
    ext j i
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S (fun a=>actualFreeProductGermEquiv m e χ hχ0 (Γ a))
        (fixedSelectorBlockEssential r j)))=_
    rw [actualFreeProduct_historical_selected_derivative m e χ hχ0 hHeads S Γ,
      actualFreeProduct_historical_coordinate_derivative m e χ hχ0 i.val (hBlock i.val i.property),
      actualFreeProduct_historical_eval]
    rfl
  refine ⟨?_,hJac,?_⟩
  · intro j
    rw [actualFreeProduct_historical_selected_derivative m e χ hχ0 hHeads S Γ]
    have hm:=Ideal.mem_map_of_mem (actualFreeProductGermEquiv m e χ hχ0).toRingEquiv.toRingHom (hContact r j)
    rw [actualFreeProductGermEquiv_map_coordinateIdeal m e χ hχ0 (fixedSelectorBlock V r) hBlock] at hm
    exact hm
  · rw [hJac]
    exact hdet r

/-- WHOLE old prefix-cone support is preserved by the same actual free
chart, at every exponent and every literal natural degree cutoff. -/
theorem actualFreeProduct_historical_whole_prefix_support (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n:=m) (0 : ComplexModel m)) (hχ0 : χ.toFun 0=0)
    {V : Finset (Fin (m+e) →₀ ℕ)}
    (hHeads : ∀(a : V)(i : Fin (m+e)),¬ m ≤ i.val → a.val i=0)
    (Γ : V → HolGerm (ComplexModel (m+e)))
    (hPrefix : HistoricalWholePrefixSupport V (fun a=>actualUnshiftedTaylorAlgHom (m+e) (Γ a))) :
    HistoricalWholePrefixSupport V
      (fun a=>actualUnshiftedTaylorAlgHom (m+e) (actualFreeProductGermEquiv m e χ hχ0 (Γ a))) := by
  intro r a hra b hbr
  have hZero : actualAnalyticMultiDerivative b.val (Γ a)=0:=
    (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val (Γ a)).mpr (hPrefix r a hra b hbr)
  apply (actualAnalyticMultiDerivative_eq_zero_iff_cone b.val _).mp
  rw [actualFreeProductGermEquiv_multiDerivative m e χ hχ0 b.val (hHeads b),hZero,map_zero]

/-- Every genuine analytic germ equivalence preserves EACH actual maximal
power in both directions. This does not select or change any family. -/
theorem actual_maximal_power_map_algEquiv_iff
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (d : ℕ)
    (F : HolGerm (ComplexModel n)) :
    E F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d ↔
      F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d := by
  have hForward (A : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n))
      (G : HolGerm (ComplexModel n)) (hG : G∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d) :
      A G∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d := by
    have hm:=Ideal.mem_map_of_mem A.toRingEquiv.toRingHom hG
    have hMap : Ideal.map A.toRingEquiv.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d)=
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^d := by
      rw [Ideal.map_pow]
      exact congrArg (fun J : Ideal (HolGerm (ComplexModel n))=>J^d)
        (IsLocalRing.map_ringEquiv_maximalIdeal A.toRingEquiv)
    rwa [hMap] at hm
  exact ⟨fun h=>by simpa only [AlgEquiv.symm_apply_apply] using hForward E.symm (E F) h,hForward E F⟩

/-- A whole fixed essential section, obtained from an actual product chart,
preserves every coefficient supported in that section in ORIGINAL indices. -/
theorem actual_pure_coefficient_of_fixed_section
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (B : Set (Fin n))
    (hSection : ∀F,actualBlockProjectionGermHom B (E F)=actualBlockProjectionGermHom B F)
    (F : HolGerm (ComplexModel n)) (α : Fin n →₀ ℕ) (hα : ∀i,i∉B → α i=0) :
    MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (E F))=
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n F) := by
  have hTaylor:=congrArg (actualUnshiftedTaylorAlgHom n) (hSection F)
  have hProjection (H : HolGerm (ComplexModel n)) :
      actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom B H)=
        actualFormalBlockCoordinateProjection B (actualUnshiftedTaylorAlgHom n H):=
    DFunLike.congr_fun (actualTaylor_blockProjection B) H
  rw [hProjection,hProjection] at hTaylor
  have hCoeff:=congrArg (MvPowerSeries.coeff α) hTaylor
  rw [coeff_actualFormalBlockCoordinateProjection,coeff_actualFormalBlockCoordinateProjection] at hCoeff
  simpa only [if_pos hα] using hCoeff

/-- Whole historical jets through any ACTUAL fixed-section chart. In
particular a free chart conjugated back to the original coordinate indices
keeps every old word and label literally, with no new canonical basis. -/
theorem actual_historical_whole_jets_of_fixed_section
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (B : Set (Fin n))
    (hSection : ∀F,actualBlockProjectionGermHom B (E F)=actualBlockProjectionGermHom B F)
    (w : Fin k → CoordinateWord n) (Γ : Fin k → HolGerm (ComplexModel n))
    (hmarked : ∀j,Γ j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^
      normalExponentDegree (wordExponent (w j)))
    (hHeads : ∀j i,i∉B → wordExponent (w j) i=0)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) q)) :
    ∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j))) q) := by
  intro q
  exact historicalWholeJetMap_bijective_of_pure_leading_agreement w
    (fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) (fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j)))
    (fun j=>actualTaylor_mem_power_of_maximal_power n _ _ (hmarked j))
    (fun j=>actualTaylor_mem_power_of_maximal_power n _ _ ((actual_maximal_power_map_algEquiv_iff E _ _).mpr (hmarked j)))
    B hHeads (fun j α _ hα=>actual_pure_coefficient_of_fixed_section E B hSection (Γ j) α hα) q (hwhole q)

theorem actual_historical_whole_supported_division_of_fixed_section
    (E : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)) (B : Set (Fin n))
    (hSection : ∀F,actualBlockProjectionGermHom B (E F)=actualBlockProjectionGermHom B F)
    (w : Fin k → CoordinateWord n) (Γ : Fin k → HolGerm (ComplexModel n))
    (hmarked : ∀j,Γ j∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^
      normalExponentDegree (wordExponent (w j)))
    (hHeads : ∀j i,i∉B → wordExponent (w j) i=0)
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun j=>actualUnshiftedTaylorAlgHom n (Γ j))) :
    HistoricalWholeSupportedDivision w (fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j))) := by
  apply historicalWholeSupportedDivision_of_equal_quotient_dimensions w
    (fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) (fun j=>actualUnshiftedTaylorAlgHom n (E (Γ j)))
    (fun j=>actualTaylor_mem_power_of_maximal_power n _ _ (hmarked j))
    (fun j=>actualTaylor_mem_power_of_maximal_power n _ _ ((actual_maximal_power_map_algEquiv_iff E _ _).mpr (hmarked j)))
    hwhole (actual_historical_whole_jets_of_fixed_section E B hSection w Γ hmarked hHeads hwhole) hSupported
  intro q
  cases q with
  | zero =>
      have hZero (J : Ideal (MvPowerSeries (Fin n) ℂ)) : J⊔genuineFormalVariables n^0=⊤:=by
        rw [pow_zero,Ideal.one_eq_top,sup_top_eq]
      exact congrArg (fun J : Ideal (MvPowerSeries (Fin n) ℂ)=>Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸ J))
        ((hZero _).trans (hZero _).symm)
  | succ ℓ => exact (actual_family_formal_hs_map_algEquiv E Γ ℓ).symm

end
end Hironaka.HironakaActualHistoricalCentreFilteredDivision
