import Hironaka.Resolution.Algebraic.ActualDimensionGroupBlowup
import Hironaka.Scheme.BlowUp.AffineAlgebra
import Hironaka.Algebra.FunctionFieldDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced

/-! Component dimensions of the SAME actual separated Proj-Rees chart rings.
No equidimensionality, fraction-field comparison or future-history certificate
is supplied. Source-first proof:
`actual-dimension-group-chart-dimension-20261101.tex`. -/
set_option autoImplicit false
open Set AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualDimensionGroupChartDimension
noncomputable section
open ActualDimensionGroupBlowup

variable (R : Type u) [CommRing R]

/-- Contraction along the SAME native chart's actual coefficient map. -/
def chartContraction (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) : Ideal R :=
  q.val.comap (algebraMap R (affineBlowUpAlgebra I a))

instance chartContraction_isPrime (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    (chartContraction R I a q).IsPrime := by
  have : q.val.IsPrime := q.property.isPrime
  exact Ideal.IsPrime.comap (algebraMap R (affineBlowUpAlgebra I a))

/-- Actual chart minimal primes come from original minimal primes, avoiding the denominator. -/
theorem chartContraction_mem_minimalPrimes (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    chartContraction R I a q ∈ minimalPrimes R ∧ a ∉ chartContraction R I a q := by
  let B := affineBlowUpAlgebra I a
  let C := Localization.Away a
  have : q.val.IsPrime := q.property.isPrime
  have ha : algebraMap R B a ∉ q.val := by
    intro h
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h q.property
      (affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors (I := I) (a := a))
  have : IsLocalization.Away (algebraMap R B a) C :=
    affineBlowUpAlgebra.isLocalization_away (I := I) (a := a)
  let Q : Ideal C := q.val.map (algebraMap B C)
  have hd : Disjoint (Submonoid.powers (algebraMap R B a) : Set B) (q.val : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr ha
  have hUnder : Q.under B = q.val :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (algebraMap R B a)) C
      q.property.isPrime hd
  have hQ : Q ∈ minimalPrimes C := by
    have h := IsLocalization.minimalPrimes_map (Submonoid.powers (algebraMap R B a)) C (⊥ : Ideal B)
    have hm : Q ∈ ((⊥ : Ideal B).map (algebraMap B C)).minimalPrimes := by
      rw [h]
      change Q.under B ∈ minimalPrimes B
      rw [hUnder]
      exact q.property
    simpa only [Ideal.map_bot] using hm
  have hp : Q.under R ∈ minimalPrimes R := by
    change Q ∈ Ideal.under R ⁻¹' (⊥ : Ideal R).minimalPrimes
    rw [← IsLocalization.minimalPrimes_map (Submonoid.powers a) C (⊥ : Ideal R)]
    simpa only [Ideal.map_bot] using hQ
  have hCon : Q.under R = chartContraction R I a q := by
    rw [← Ideal.under_under (A := R) (B := B),hUnder]
    rfl
  exact ⟨hCon ▸ hp,ha⟩

/-- The actual denominator forces the original minimal component's intrinsic label. -/
theorem dimension_chart_component_label (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d)
    (q : minimalPrimes (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val)) :
    let p : minimalPrimes R :=
      ⟨chartContraction R (dimensionSeparationIdeal R) a.val q,
        (chartContraction_mem_minimalPrimes R _ _ q).1⟩
    componentDimension R p = d.val := by
  let p : minimalPrimes R :=
    ⟨chartContraction R (dimensionSeparationIdeal R) a.val q,
      (chartContraction_mem_minimalPrimes R _ _ q).1⟩
  let e : dimensionIndex R := ⟨componentDimension R p,⟨p,rfl⟩⟩
  by_contra h
  have hed : e ≠ d := fun he => h (congrArg Subtype.val he)
  have hae : a.val ∈ dimensionGroupIdeal R e :=
    (Ideal.mem_iInf.mp ((Ideal.mem_iInf.mp a.property) e)) hed
  have hap : a.val ∈ p.val :=
    (Ideal.mem_iInf.mp ((Ideal.mem_iInf.mp hae) p)) rfl
  exact (chartContraction_mem_minimalPrimes R _ _ q).2 hap

private theorem fg_adjoin_linear_image {C : Type u} [CommRing C] [Algebra R C]
    (M : Submodule R R) (hM : M.FG) (f : R →ₗ[R] C) :
    (Algebra.adjoin R (f '' (M : Set R))).FG := by
  obtain ⟨t,ht⟩ := Submodule.FG.map f hM
  refine ⟨t,?_⟩
  calc
    _ = Algebra.adjoin R (Submodule.span R (t : Set C) : Set C) := by rw [Algebra.adjoin_span]
    _ = Algebra.adjoin R (M.map f : Set C) := congrArg (fun T : Submodule R C =>
      Algebra.adjoin R (T : Set C)) ht
    _ = _ := rfl

/-- Finite ideal generation derives finite type for the SAME native fraction chart. -/
theorem affineBlowUpAlgebra_finiteType (I : Ideal R) (hI : I.FG) (a : R) :
    Algebra.FiniteType R (affineBlowUpAlgebra I a) := by
  let C := Localization.Away a
  let f : R →ₗ[R] C :=
    { toFun := fun x => algebraMap R C x * IsLocalization.Away.invSelf a
      map_add' := fun x y => by simp only [map_add,add_mul]
      map_smul' := fun r x => by simp only [smul_eq_mul,map_mul,Algebra.smul_def,mul_assoc,RingHom.id_apply] }
  have hFG := fg_adjoin_linear_image R (I : Submodule R R) hI f
  apply (Subalgebra.fg_iff_finiteType (affineBlowUpAlgebra I a)).mp
  rw [affineBlowUpAlgebra_eq_adjoin]
  exact hFG

private abbrev ComponentField (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :=
  FractionRing (R ⧸ chartContraction R I a q)

private def originalFieldMap (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) : R →+* ComponentField R I a q :=
  (algebraMap (R ⧸ chartContraction R I a q) (ComponentField R I a q)).comp
    (Ideal.Quotient.mk (chartContraction R I a q))

private theorem originalFieldMap_eq_zero_iff (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) (x : R) :
    originalFieldMap R I a q x = 0 ↔ x ∈ chartContraction R I a q := by
  change algebraMap (R ⧸ chartContraction R I a q) (ComponentField R I a q)
    (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _),Ideal.Quotient.eq_zero_iff_mem]

private theorem originalFieldMap_denominator_ne_zero (I : Ideal R) (a : R)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) : originalFieldMap R I a q a ≠ 0 :=
  fun h => (chartContraction_mem_minimalPrimes R I a q).2
    ((originalFieldMap_eq_zero_iff R I a q a).mp h)

private theorem field_center_eq (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    I.map (originalFieldMap R I a q) = Ideal.span {originalFieldMap R I a q a} := by
  have hu : IsUnit (originalFieldMap R I a q a) :=
    isUnit_iff_ne_zero.mpr (originalFieldMap_denominator_ne_zero R I a q)
  exact (Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (originalFieldMap R I a q) ha) hu).trans
    (Ideal.span_singleton_eq_top.mpr hu).symm

private def chartFieldLift (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    affineBlowUpAlgebra I a →+* ComponentField R I a q :=
  affineBlowUpAlgebra.lift (originalFieldMap R I a q) ha
    (mem_nonZeroDivisors_iff_ne_zero.mpr (originalFieldMap_denominator_ne_zero R I a q))
    (field_center_eq R I a ha q)

private theorem chartFieldLift_coeff (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) (x : R) :
    chartFieldLift R I a ha q (algebraMap R (affineBlowUpAlgebra I a) x) =
      originalFieldMap R I a q x := by
  exact congrArg (fun f : R →+* ComponentField R I a q => f x)
    (affineBlowUpAlgebra.lift_comp_algebraMap (originalFieldMap R I a q) ha
      (mem_nonZeroDivisors_iff_ne_zero.mpr (originalFieldMap_denominator_ne_zero R I a q))
      (field_center_eq R I a ha q))

private theorem chartFieldLift_ker (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    RingHom.ker (chartFieldLift R I a ha q) = q.val := by
  have hq : q.val.IsPrime := q.property.isPrime
  have hnot : algebraMap R (affineBlowUpAlgebra I a) a ∉ q.val :=
    (chartContraction_mem_minimalPrimes R I a q).2
  ext b
  obtain ⟨m,x,_hx,hb⟩ := (affineBlowUpAlgebra.mem_iff ha b.val).mp b.property
  have hb' : b * (algebraMap R (affineBlowUpAlgebra I a) a) ^ m =
      algebraMap R (affineBlowUpAlgebra I a) x := Subtype.ext hb
  have hδ : chartFieldLift R I a ha q b * (originalFieldMap R I a q a) ^ m =
      originalFieldMap R I a q x := by
    have h := congrArg (chartFieldLift R I a ha q) hb'
    simpa only [map_mul,map_pow,chartFieldLift_coeff] using h
  have hpow : (algebraMap R (affineBlowUpAlgebra I a) a) ^ m ∉ q.val :=
    fun h => hnot (hq.mem_of_pow_mem m h)
  change chartFieldLift R I a ha q b = 0 ↔ b ∈ q.val
  constructor
  · intro hzero
    have hxzero : originalFieldMap R I a q x = 0 := by rw [← hδ,hzero,zero_mul]
    have hxq : algebraMap R (affineBlowUpAlgebra I a) x ∈ q.val :=
      (originalFieldMap_eq_zero_iff R I a q x).mp hxzero
    have hbq : b * (algebraMap R (affineBlowUpAlgebra I a) a) ^ m ∈ q.val := hb' ▸ hxq
    exact (hq.mem_or_mem hbq).resolve_right hpow
  · intro hbq
    have hxq : algebraMap R (affineBlowUpAlgebra I a) x ∈ q.val :=
      hb' ▸ q.val.mul_mem_right _ hbq
    have hxzero : originalFieldMap R I a q x = 0 :=
      (originalFieldMap_eq_zero_iff R I a q x).mpr hxq
    exact (mul_eq_zero.mp (hδ.trans hxzero)).resolve_right
      (pow_ne_zero m (originalFieldMap_denominator_ne_zero R I a q))

/-- An actual component chart embeds into the ORIGINAL contracted component's fraction field. -/
def chartComponentFieldMap (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    (affineBlowUpAlgebra I a ⧸ q.val) →+*
      FractionRing (R ⧸ chartContraction R I a q) :=
  Ideal.Quotient.lift q.val (chartFieldLift R I a ha q) (fun b hb => by
    change b ∈ RingHom.ker (chartFieldLift R I a ha q)
    rw [chartFieldLift_ker]
    exact hb)

private theorem chartComponentFieldMap_injective (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    Function.Injective (chartComponentFieldMap R I a ha q) :=
  RingHom.lift_injective_of_ker_le_ideal q.val _ (chartFieldLift_ker R I a ha q).le

/-- The map retains the literal original quotient and coefficient triangle. -/
theorem chartComponentFieldMap_commutes (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) (x : R) :
    chartComponentFieldMap R I a ha q
        (Ideal.Quotient.mk q.val (algebraMap R (affineBlowUpAlgebra I a) x)) =
      algebraMap (R ⧸ chartContraction R I a q) (FractionRing (R ⧸ chartContraction R I a q))
        (Ideal.Quotient.mk (chartContraction R I a q) x) :=
  chartFieldLift_coeff R I a ha q x

/-- The SAME original function field is a fraction field of the actual chart component. -/
theorem chartComponentFieldMap_isFractionRing (I : Ideal R) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    letI : Algebra (affineBlowUpAlgebra I a ⧸ q.val)
        (FractionRing (R ⧸ chartContraction R I a q)) :=
      (chartComponentFieldMap R I a ha q).toAlgebra
    IsFractionRing (affineBlowUpAlgebra I a ⧸ q.val)
      (FractionRing (R ⧸ chartContraction R I a q)) := by
  let K := FractionRing (R ⧸ chartContraction R I a q)
  let : Algebra (affineBlowUpAlgebra I a ⧸ q.val) K :=
    (chartComponentFieldMap R I a ha q).toAlgebra
  have : FaithfulSMul (affineBlowUpAlgebra I a ⧸ q.val) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (chartComponentFieldMap_injective R I a ha q)
  apply IsFractionRing.of_field (R := affineBlowUpAlgebra I a ⧸ q.val) (K := K)
  intro z
  obtain ⟨r,s,_hs,hz⟩ := IsFractionRing.div_surjective (R ⧸ chartContraction R I a q) z
  obtain ⟨r₀,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s₀,rfl⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨Ideal.Quotient.mk q.val (algebraMap R (affineBlowUpAlgebra I a) r₀),
    Ideal.Quotient.mk q.val (algebraMap R (affineBlowUpAlgebra I a) s₀),?_⟩
  change z = chartComponentFieldMap R I a ha q _ / chartComponentFieldMap R I a ha q _
  rw [chartComponentFieldMap_commutes,chartComponentFieldMap_commutes]
  exact hz.symm

private theorem chart_component_dimension (k : Type u) [Field k] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I.FG) (a : R) (ha : a ∈ I)
    (q : minimalPrimes (affineBlowUpAlgebra I a)) :
    ringKrullDim (affineBlowUpAlgebra I a ⧸ q.val) =
      ringKrullDim (R ⧸ chartContraction R I a q) := by
  let B := affineBlowUpAlgebra I a
  let P := R ⧸ chartContraction R I a q
  let Q := B ⧸ q.val
  let K := FractionRing P
  have : q.val.IsPrime := q.property.isPrime
  have : IsScalarTower k R B := inferInstance
  have : Algebra.FiniteType R B := affineBlowUpAlgebra_finiteType R I hI a
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have : IsScalarTower k P K := inferInstance
  let : Algebra Q K := (chartComponentFieldMap R I a ha q).toAlgebra
  have : IsFractionRing Q K := chartComponentFieldMap_isFractionRing R I a ha q
  have : IsScalarTower k Q K := by
    apply IsScalarTower.of_algebraMap_eq (R := k) (S := Q) (A := K)
    intro c
    change algebraMap P K (algebraMap k P c) =
      chartComponentFieldMap R I a ha q
        (Ideal.Quotient.mk q.val (algebraMap R B (algebraMap k R c)))
    exact (chartComponentFieldMap_commutes R I a ha q (algebraMap k R c)).symm
  obtain ⟨n,hn,htrn⟩ :=
    Hironaka.Algebra.FunctionFieldDimension.exists_dimension_and_trdeg k P K
  obtain ⟨m,hm,htrm⟩ :=
    Hironaka.Algebra.FunctionFieldDimension.exists_dimension_and_trdeg k Q K
  have hnm : n = m := by exact_mod_cast htrn.symm.trans htrm
  rw [hm,hn,hnm]

/-- Each SAME actual separated chart is reduced and has all its component dimensions d. -/
theorem dimension_group_chart_equidimensional (k : Type u) [Field k] [Algebra k R]
    [Algebra.FiniteType k R] [IsReduced R] (d : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) d) :
    IsReduced (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val) ∧
      ∀ q : minimalPrimes (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val),
        ringKrullDim (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val ⧸ q.val) = d.val := by
  constructor
  · exact isReduced_of_injective (affineBlowUpAlgebra (dimensionSeparationIdeal R) a.val).val.toRingHom
      Subtype.val_injective
  · intro q
    have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
    have hI : (dimensionSeparationIdeal R).FG := IsNoetherian.noetherian _
    have ha : a.val ∈ dimensionSeparationIdeal R :=
      (le_iSup (fun e => complementIdeal R (dimensionGroupIdeal R) e) d) a.property
    have hdim := chart_component_dimension R k (dimensionSeparationIdeal R) hI a.val ha q
    exact hdim.trans (dimension_chart_component_label R d a q)

end
end Hironaka.Resolution.Algebraic.ActualDimensionGroupChartDimension
