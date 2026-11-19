import Hironaka.Resolution.HironakaActualInheritedAnalyticBlockJacobian
import Hironaka.Resolution.HironakaActualCanonicalTriangularShear
import Hironaka.MarkedIdeal.NormalDerivativeMonomial
import Hironaka.Manifold.LocalHolomorphicInverse

/-! Genuine pure analytic graph translations. The maps read their graph
functions only on the complement of the ENTIRE current block. Actual
local holomorphic inverses, whole Taylor substitutions, both formal head
identities and actual block multi-derivative commutation are constructed.
This structural graph dictionary does not itself solve the graph equations
or construct an initial contact flag; those are separate producers. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualAnalyticBlockGraphTranslation

noncomputable section

open HolGerm HironakaHolomorphicJetChartInvariance
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualTaylorCoordinateNaturality HironakaActualInheritedAnalyticBlockJacobian
  HironakaRelativeNormalTaylorCoefficients HolomorphicTaylorTail NormalTaylorOrder
  HironakaActualCauchyCoefficientLimits HironakaActualFormalCoordinatePowerDivision
  OkaRelationSheaf HironakaHolomorphicJetMonomialSpan

variable {n : ℕ}

private def MonicAt (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) : Prop :=
  MvPowerSeries.coeff a F = 1 ∧ ∀ β, m.toSyn β < m.toSyn a → MvPowerSeries.coeff β F = 0

private theorem monicAt_ne_zero (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) (h : MonicAt m F a) : F ≠ 0 := by
  intro hz
  have hc := h.1
  rw [hz, map_zero] at hc
  exact zero_ne_one hc

private theorem monicAt_initial (m : MonomialOrder (Fin n)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ) (h : MonicAt m F a) :
    actualInitialExponent m F (monicAt_ne_zero m F a h) = a :=
  actualInitialExponent_eq_of_coefficients m F _ a (by rw [h.1]; exact one_ne_zero) h.2

private theorem monicAt_mul (m : MonomialOrder (Fin n))
    (F G : MvPowerSeries (Fin n) ℂ) (a c : Fin n →₀ ℕ)
    (hF : MonicAt m F a) (hG : MonicAt m G c) : MonicAt m (F*G) (a+c) := by
  have hFn := monicAt_ne_zero m F a hF
  have hGn := monicAt_ne_zero m G c hG
  have hFa := monicAt_initial m F a hF
  have hGc := monicAt_initial m G c hG
  have hprod := actualInitialExponent_mul m F G hFn hGn
  rw [hFa, hGc] at hprod
  constructor
  · have hc := coeff_mul_actualInitialExponent m F G hFn hGn
    simpa only [hFa, hGc, hF.1, hG.1, one_mul] using hc
  · intro β hβ
    apply coeff_eq_zero_of_lt_actualInitialExponent m (F*G) (mul_ne_zero hFn hGn) β
    rwa [hprod]

private theorem monicAt_one (m : MonomialOrder (Fin n)) :
    MonicAt m (1 : MvPowerSeries (Fin n) ℂ) 0 := by
  constructor
  · simp
  · intro β hβ
    rw [map_zero] at hβ
    exact False.elim ((not_lt_of_ge (m.zero_le (m.toSyn β))) hβ)

private theorem monicAt_power (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (i : Fin n)
    (hF : MonicAt m F (Finsupp.single i 1)) (k : ℕ) :
    MonicAt m (F^k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa only [pow_zero, Finsupp.single_zero] using monicAt_one m
  | succ k ih =>
      simpa only [pow_succ, Finsupp.single_add] using
        monicAt_mul m _ _ (Finsupp.single i k) (Finsupp.single i 1) ih hF

private theorem monicAt_finset_prod {ι : Type*} [DecidableEq ι]
    (m : MonomialOrder (Fin n)) (s : Finset ι) (F : ι → MvPowerSeries (Fin n) ℂ)
    (a : ι → (Fin n →₀ ℕ)) (h : ∀ i ∈ s, MonicAt m (F i) (a i)) :
    MonicAt m (∏ i ∈ s, F i) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using monicAt_one m
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact monicAt_mul m _ _ _ _ (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem coordinate_product_monic (m : MonomialOrder (Fin n))
    (C : Fin n → MvPowerSeries (Fin n) ℂ)
    (hC : ∀ i, MonicAt m (C i) (Finsupp.single i 1)) (α : Fin n →₀ ℕ) :
    MonicAt m (α.prod (fun i k => C i ^ k)) α := by
  have h := monicAt_finset_prod m α.support (fun i => C i ^ (α i))
    (fun i => Finsupp.single i (α i)) (fun i _ => monicAt_power m (C i) i (hC i) (α i))
  have hexp : (∑ i ∈ α.support, Finsupp.single i (α i)) = α := by
    simpa only [Finsupp.sum] using α.sum_single
  simpa only [Finsupp.prod, hexp] using h

/-- Genuine zero-constant formal substitution, with no continuity certificate input. -/
def actualMonicCoordinateSubstitution (C : Fin n → MvPowerSeries (Fin n) ℂ)
    (hC0 : ∀ i, MvPowerSeries.constantCoeff (C i) = 0) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hC0)

/-- Genuine entire nonlinear substitutions with original monic coordinate heads
preserve each SAME nonzero series' actual head and its coefficient. -/
theorem actualMonicCoordinateSubstitution_initial_data (m : MonomialOrder (Fin n))
    (C : Fin n → MvPowerSeries (Fin n) ℂ)
    (hC0 : ∀ i, MvPowerSeries.constantCoeff (C i) = 0)
    (hC : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) (C i) = 1 ∧
      ∀ β, m.toSyn β < m.toSyn (Finsupp.single i 1) → MvPowerSeries.coeff β (C i) = 0)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    ∃ hSF : actualMonicCoordinateSubstitution C hC0 F ≠ 0,
      actualInitialExponent m (actualMonicCoordinateSubstitution C hC0 F) hSF =
        actualInitialExponent m F hF ∧
      MvPowerSeries.coeff (actualInitialExponent m F hF)
        (actualMonicCoordinateSubstitution C hC0 F) =
        MvPowerSeries.coeff (actualInitialExponent m F hF) F := by
  let a := actualInitialExponent m F hF
  have hcoeff : MvPowerSeries.coeff a (actualMonicCoordinateSubstitution C hC0 F) =
      MvPowerSeries.coeff a F := by
    rw [actualMonicCoordinateSubstitution, MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hC0) F a]
    rw [finsum_eq_single _ a]
    · rw [(coordinate_product_monic m C hC a).1, smul_eq_mul, mul_one]
    · intro β hβ
      by_cases hc : MvPowerSeries.coeff β F = 0
      · rw [hc, zero_smul]
      · have hlt : m.toSyn a < m.toSyn β := by
          apply lt_of_le_of_ne ((actualInitialExponent_spec m F hF).2 β hc)
          intro he
          exact hβ (m.toSyn.injective he).symm
        rw [(coordinate_product_monic m C hC β).2 a hlt, smul_zero]
  have hSF : actualMonicCoordinateSubstitution C hC0 F ≠ 0 := by
    intro hz
    have hn := (actualInitialExponent_spec m F hF).1
    rw [← hcoeff, hz, map_zero] at hn
    exact hn rfl
  refine ⟨hSF, ?_, hcoeff⟩
  apply actualInitialExponent_eq_of_coefficients m _ hSF a
  · rw [hcoeff]
    exact (actualInitialExponent_spec m F hF).1
  · intro γ hγ
    rw [actualMonicCoordinateSubstitution, MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hC0) F γ]
    apply finsum_eq_zero_of_forall_eq_zero
    intro β
    by_cases hc : MvPowerSeries.coeff β F = 0
    · rw [hc, zero_smul]
    · have hlt := hγ.trans_le ((actualInitialExponent_spec m F hF).2 β hc)
      rw [(coordinate_product_monic m C hC β).2 γ hlt, smul_zero]

/-- Actual continuous-linear projection onto an arbitrary original coordinate block. -/
def actualBlockCoordinateProjection (B : Set (Fin n)) : ComplexModel n →L[ℂ] ComplexModel n :=
  ∑ i : Fin n, if i ∈ B then
    (EuclideanSpace.proj i).smulRight (EuclideanSpace.single i (1 : ℂ)) else 0

theorem actualBlockCoordinateProjection_apply (B : Set (Fin n))
    (z : ComplexModel n) (i : Fin n) :
    actualBlockCoordinateProjection B z i = if i ∈ B then z i else 0 := by
  classical
  rw [actualBlockCoordinateProjection, sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  by_cases hi : i ∈ B
  · rw [if_pos hi]
    rw [Finset.sum_eq_single i]
    · rw [if_pos hi, ContinuousLinearMap.smulRight_apply]
      simp
    · intro j _ hji
      by_cases hj : j ∈ B
      · rw [if_pos hj, ContinuousLinearMap.smulRight_apply]
        simp [show i ≠ j from fun hij => hji hij.symm]
      · rw [if_neg hj]
        rfl
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ B
    · rw [if_pos hj, ContinuousLinearMap.smulRight_apply]
      have hij : i ≠ j := fun he => hi (he.symm ▸ hj)
      simp [hij]
    · rw [if_neg hj]
      rfl

/-- The genuine graph map translates only C and reads its entire graph function
only on the complement of B. Thus it is independent of ALL B coordinates. -/
def actualBlockGraphMap (B C : Set (Fin n))
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ComplexModel n :=
  z + actualBlockCoordinateProjection C (h (actualBlockCoordinateProjection Bᶜ z))

theorem actualBlockGraphMap_apply (B C : Set (Fin n))
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) (i : Fin n) :
    actualBlockGraphMap B C h z i =
      z i + if i ∈ C then h (actualBlockCoordinateProjection Bᶜ z) i else 0 := by
  simp [actualBlockGraphMap, actualBlockCoordinateProjection_apply]

theorem actualBlockCoordinateProjection_complement_graph
    (B C : Set (Fin n)) (hCB : C ⊆ B)
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    actualBlockCoordinateProjection Bᶜ (actualBlockGraphMap B C h z) =
      actualBlockCoordinateProjection Bᶜ z := by
  ext i
  by_cases hi : i ∈ B
  · simp [actualBlockCoordinateProjection_apply, hi]
  · have hCi : i ∉ C := fun hc => hi (hCB hc)
    simp [actualBlockCoordinateProjection_apply, actualBlockGraphMap_apply, hi, hCi]

theorem actualBlockGraphMap_inverse (B C : Set (Fin n)) (hCB : C ⊆ B)
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    actualBlockGraphMap B C (fun x => -h x) (actualBlockGraphMap B C h z) = z := by
  rw [actualBlockGraphMap, actualBlockCoordinateProjection_complement_graph B C hCB]
  change (z + actualBlockCoordinateProjection C (h (actualBlockCoordinateProjection Bᶜ z))) +
    actualBlockCoordinateProjection C (-h (actualBlockCoordinateProjection Bᶜ z)) = z
  rw [map_neg, add_neg_cancel_right]

theorem actualBlockGraphMap_zero (B C : Set (Fin n))
    (h : ComplexModel n → ComplexModel n) (h0 : h 0 = 0) :
    actualBlockGraphMap B C h 0 = 0 := by
  simp [actualBlockGraphMap, h0]

/-- A literal global identity, before any differentiability assumption. -/
theorem actualBlockGraphMap_add_block_direction (B C : Set (Fin n))
    (h : ComplexModel n → ComplexModel n) (i : Fin n) (hi : i ∈ B)
    (z : ComplexModel n) (t : ℂ) :
    actualBlockGraphMap B C h (z + t • EuclideanSpace.single i 1) =
      actualBlockGraphMap B C h z + t • EuclideanSpace.single i 1 := by
  have hp : actualBlockCoordinateProjection Bᶜ (EuclideanSpace.single i (1 : ℂ)) = 0 := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [actualBlockCoordinateProjection_apply, hi]
    · simp [actualBlockCoordinateProjection_apply, hj]
  simp only [actualBlockGraphMap, map_add, map_smul, hp, smul_zero, add_zero]
  abel

/-- Actual analytic graph representatives on one honest base neighbourhood.
Dependence only on B-complement coordinates is enforced by the displayed
projection in the graph map, not assumed as a transformation certificate. -/
structure ActualBlockGraphData (B C : Set (Fin n)) where
  subset : C ⊆ B
  baseDomain : Set (ComplexModel n)
  isOpen_baseDomain : IsOpen baseDomain
  zero_mem_baseDomain : (0 : ComplexModel n) ∈ baseDomain
  value : ComplexModel n → ComplexModel n
  holomorphic : DifferentiableOn ℂ value baseDomain
  zero : value 0 = 0

def actualBlockGraphDomain {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    Set (ComplexModel n) := actualBlockCoordinateProjection Bᶜ ⁻¹' D.baseDomain

theorem actualBlockGraphDomain_isOpen {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    IsOpen (actualBlockGraphDomain D) :=
  D.isOpen_baseDomain.preimage (actualBlockCoordinateProjection Bᶜ).continuous

theorem actualBlockGraphDomain_zero {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    (0 : ComplexModel n) ∈ actualBlockGraphDomain D := by
  change actualBlockCoordinateProjection Bᶜ 0 ∈ D.baseDomain
  simpa only [map_zero] using D.zero_mem_baseDomain

theorem actualBlockGraphMap_differentiableOn {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) :
    DifferentiableOn ℂ (actualBlockGraphMap B C D.value) (actualBlockGraphDomain D) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_id.add
  apply (actualBlockCoordinateProjection C).differentiableAt.comp z
  exact (D.holomorphic.differentiableAt (D.isOpen_baseDomain.mem_nhds hz)).comp z
    (actualBlockCoordinateProjection Bᶜ).differentiableAt

theorem actualBlockGraphInverse_differentiableOn {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) :
    DifferentiableOn ℂ (actualBlockGraphMap B C (fun x => -D.value x))
      (actualBlockGraphDomain D) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_id.add
  apply (actualBlockCoordinateProjection C).differentiableAt.comp z
  exact ((D.holomorphic.differentiableAt (D.isOpen_baseDomain.mem_nhds hz)).neg).comp z
    (actualBlockCoordinateProjection Bᶜ).differentiableAt

/-- A genuine local holomorphic equivalence with both actual representatives
and both inverse identities on the SAME open set. -/
def actualBlockGraphLocalEquiv {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) where
  source := actualBlockGraphDomain D
  target := actualBlockGraphDomain D
  isOpen_source := actualBlockGraphDomain_isOpen D
  isOpen_target := actualBlockGraphDomain_isOpen D
  center_mem_source := actualBlockGraphDomain_zero D
  toFun := actualBlockGraphMap B C D.value
  invFun := actualBlockGraphMap B C (fun x => -D.value x)
  toFun_holomorphic := actualBlockGraphMap_differentiableOn D
  invFun_holomorphic := actualBlockGraphInverse_differentiableOn D
  mapsTo_toFun z hz := by
    change actualBlockCoordinateProjection Bᶜ (actualBlockGraphMap B C D.value z) ∈ D.baseDomain
    rwa [actualBlockCoordinateProjection_complement_graph B C D.subset]
  mapsTo_invFun z hz := by
    change actualBlockCoordinateProjection Bᶜ
      (actualBlockGraphMap B C (fun x => -D.value x) z) ∈ D.baseDomain
    rwa [actualBlockCoordinateProjection_complement_graph B C D.subset]
  left_inv z _ := actualBlockGraphMap_inverse B C D.subset D.value z
  right_inv z _ := by
    simpa only [neg_neg] using
      actualBlockGraphMap_inverse B C D.subset (fun x => -D.value x) z

theorem actualBlockGraphLocalEquiv_zero {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    (actualBlockGraphLocalEquiv D).toFun 0 = 0 :=
  actualBlockGraphMap_zero B C D.value D.zero

/-- The entire analytic germ algebra equivalence is supplied by the actual
local holomorphic inverse, rather than by arbitrary coordinate formulas. -/
def actualBlockGraphGermEquiv {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (actualBlockGraphLocalEquiv D) (actualBlockGraphLocalEquiv_zero D)

theorem actualBlockGraphGermEquiv_mk {B C : Set (Fin n)} (D : ActualBlockGraphData B C)
    (F : ComplexModel n → ℂ) (hF : HolAt F 0) :
    actualBlockGraphGermEquiv D (HolGerm.mk F hF) =
      HolGerm.mk (F ∘ actualBlockGraphMap B C D.value)
        (holomorphic_comp (actualBlockGraphMap B C D.value)
          (local_toFun_holomorphic (actualBlockGraphLocalEquiv D))
          (actualBlockGraphLocalEquiv_zero D) hF) := rfl

theorem actualBlockGraphGermEquiv_coordinate_fixed {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) (hi : i ∉ C) :
    actualBlockGraphGermEquiv D (coordinateGerm i) = coordinateGerm i := by
  unfold coordinateGerm
  rw [actualBlockGraphGermEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall (fun z => by simp [actualBlockGraphMap_apply, hi])

/-- The WHOLE actual analytic coordinate ideal for an arbitrary block. -/
def actualAnalyticCoordinateBlockIdeal (A : Set (Fin n)) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (coordinateGerm '' A)

theorem map_actualAnalyticCoordinateBlockIdeal_graph {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (A : Set (Fin n)) (hA : ∀ i ∈ A, i ∉ C) :
    Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal A) = actualAnalyticCoordinateBlockIdeal A := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    change actualBlockGraphGermEquiv D (coordinateGerm i) ∈ actualAnalyticCoordinateBlockIdeal A
    rw [actualBlockGraphGermEquiv_coordinate_fixed D i (hA i hi)]
    exact Ideal.subset_span ⟨i, hi, rfl⟩
  · apply Ideal.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    have h := Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
      (show coordinateGerm i ∈ actualAnalyticCoordinateBlockIdeal A from
        Ideal.subset_span ⟨i, hi, rfl⟩)
    change actualBlockGraphGermEquiv D (coordinateGerm i) ∈ _ at h
    rwa [actualBlockGraphGermEquiv_coordinate_fixed D i (hA i hi)] at h

/-- Every genuine coordinate word supported in ALL of B commutes with the
actual graph pullback. In particular this includes the entire old block. -/
theorem actualBlockGraphGermEquiv_word_derivative {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (L : List (Fin n)) (hL : ∀ i ∈ L, i ∈ B)
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticWordDerivative L (actualBlockGraphGermEquiv D F) =
      actualBlockGraphGermEquiv D (actualAnalyticWordDerivative L F) := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    change iteratedDerivativeGerm (L.map (fun i => EuclideanSpace.single i 1))
      (actualBlockGraphGermEquiv D (HolGerm.mk f hf)) =
      actualBlockGraphGermEquiv D
        (iteratedDerivativeGerm (L.map (fun i => EuclideanSpace.single i 1)) (HolGerm.mk f hf))
    rw [actualBlockGraphGermEquiv_mk, iteratedDerivativeGerm_mk,
      iteratedDerivativeGerm_mk, actualBlockGraphGermEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    obtain ⟨V, hVf, hVo, h0V⟩ := eventually_nhds_iff.mp hf
    let Ψ := actualBlockGraphMap B C D.value
    let U := actualBlockGraphDomain D ∩ Ψ ⁻¹' V
    have hU : IsOpen U :=
      (actualBlockGraphMap_differentiableOn D).continuousOn.isOpen_inter_preimage
        (actualBlockGraphDomain_isOpen D) hVo
    have h0U : (0 : ComplexModel n) ∈ U := by
      refine ⟨actualBlockGraphDomain_zero D, ?_⟩
      change actualBlockGraphMap B C D.value 0 ∈ V
      rwa [actualBlockGraphMap_zero B C D.value D.zero]
    have hΨ : DifferentiableOn ℂ Ψ U := (actualBlockGraphMap_differentiableOn D).mono inter_subset_left
    have hUV : MapsTo Ψ U V := fun _ hz => hz.2
    have hfV : DifferentiableOn ℂ f V := fun z hz => (hVf z hz).differentiableWithinAt
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact NormalDerivativeMonomial.iterDeriv_comp_translate hU hVo hΨ hUV hfV L
      (fun i hi z t => actualBlockGraphMap_add_block_direction B C D.value i (hL i hi) z t) z hz

theorem actualBlockGraphGermEquiv_multi_derivative {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (β : Fin n →₀ ℕ)
    (hβ : ∀ i ∉ B, β i = 0) (F : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative β (actualBlockGraphGermEquiv D F) =
      actualBlockGraphGermEquiv D (actualAnalyticMultiDerivative β F) := by
  apply actualBlockGraphGermEquiv_word_derivative D (actualCoordinateDerivativeWord β)
  intro i hi
  by_contra hiB
  have him : i ∈ β.toMultiset := by simpa [actualCoordinateDerivativeWord] using hi
  have hne := Finsupp.mem_support_iff.mp ((Finsupp.mem_toMultiset β i).mp him)
  exact hne (hβ i hiB)

/-- The true formal retention of an arbitrary original coordinate block. -/
def actualFormalBlockCoordinateProjection (B : Set (Fin n)) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  (MvPowerSeries.rename (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ Fin n)).comp
    (MvPowerSeries.killCompl (⟨Subtype.val, Subtype.val_injective⟩ : B ↪ Fin n))

theorem coeff_actualFormalBlockCoordinateProjection (B : Set (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (actualFormalBlockCoordinateProjection B F) =
      if ∀ i ∉ B, α i = 0 then MvPowerSeries.coeff α F else 0 := by
  let e : B ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  by_cases hα : ∀ i ∉ B, α i = 0
  · rw [if_pos hα]
    let β := α.subtypeDomain (fun i => i ∈ B)
    have hβ : Finsupp.embDomain e β = α := by
      ext i
      by_cases hi : i ∈ B
      · change Finsupp.embDomain e β (e ⟨i, hi⟩) = α i
        rw [Finsupp.embDomain_apply_self]
        rfl
      · have hn : i ∉ Set.range e := by
          rintro ⟨j, hj⟩
          exact hi (hj ▸ j.property)
        rw [Finsupp.embDomain_of_notMem_range _ _ _ hn]
        exact (hα i hi).symm
    change MvPowerSeries.coeff α (MvPowerSeries.rename e (MvPowerSeries.killCompl e F)) = _
    rw [← hβ, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_killCompl]
  · rw [if_neg hα]
    change MvPowerSeries.coeff α (MvPowerSeries.rename e (MvPowerSeries.killCompl e F)) = 0
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨β, hβ⟩
    apply hα
    intro i hi
    have hn : i ∉ Set.range e := by
      rintro ⟨j, hj⟩
      exact hi (hj ▸ j.property)
    have hz : (Finsupp.mapDomain e β) i = 0 := by
      rw [← Finsupp.embDomain_eq_mapDomain]
      exact Finsupp.embDomain_of_notMem_range _ _ _ hn
    exact (congrArg (fun γ : Fin n →₀ ℕ => γ i) hβ).symm.trans hz

theorem actualFormalBlockCoordinateProjection_X (B : Set (Fin n)) (i : Fin n) :
    actualFormalBlockCoordinateProjection B (MvPowerSeries.X i) =
      if i ∈ B then MvPowerSeries.X i else 0 := by
  let e : B ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  by_cases hi : i ∈ B
  · rw [if_pos hi]
    change MvPowerSeries.rename e (MvPowerSeries.killCompl e (MvPowerSeries.X (e ⟨i, hi⟩))) = _
    rw [MvPowerSeries.killCompl_X, MvPowerSeries.rename_X]
    rfl
  · rw [if_neg hi]
    have hn : i ∉ Set.range e := by
      rintro ⟨j, hj⟩
      exact hi (hj ▸ j.property)
    change MvPowerSeries.rename e (MvPowerSeries.killCompl e (MvPowerSeries.X i)) = 0
    rw [MvPowerSeries.killCompl_X_eq_zero hn, map_zero]

/-- Actual nonlinear germ composition by the honest continuous-linear block projection. -/
def actualBlockProjectionGermHom (B : Set (Fin n)) :
    HolGerm (ComplexModel n) →ₐ[ℂ] HolGerm (ComplexModel n) :=
  compAlgHom (actualBlockCoordinateProjection B)
    (Eventually.of_forall (fun _ => (actualBlockCoordinateProjection B).differentiableAt)) (map_zero _)

theorem actualBlockProjectionGermHom_coordinate (B : Set (Fin n)) (i : Fin n) :
    actualBlockProjectionGermHom B (coordinateGerm i) = if i ∈ B then coordinateGerm i else 0 := by
  by_cases hi : i ∈ B
  · rw [if_pos hi]
    unfold actualBlockProjectionGermHom coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z => by simp [actualBlockCoordinateProjection_apply, hi])
  · rw [if_neg hi]
    unfold actualBlockProjectionGermHom coordinateGerm
    rw [compAlgHom_mk, ← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z => by simp [actualBlockCoordinateProjection_apply, hi])

/-- The entire analytic projection and the entire formal retention are the SAME
Taylor algebra map, established from real original coordinate identities. -/
theorem actualTaylor_blockProjection (B : Set (Fin n)) :
    (actualUnshiftedTaylorAlgHom n).comp (actualBlockProjectionGermHom B) =
      (actualFormalBlockCoordinateProjection B).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom B (coordinateGerm i)) =
      actualFormalBlockCoordinateProjection B (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [actualBlockProjectionGermHom_coordinate, actualUnshiftedTaylor_coordinate,
      actualFormalBlockCoordinateProjection_X]
    split_ifs <;> simp [actualUnshiftedTaylor_coordinate]
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom B (coordinateGerm i)) ∈ _
    rw [actualBlockProjectionGermHom_coordinate]
    by_cases hi : i ∈ B
    · rw [if_pos hi, actualUnshiftedTaylor_coordinate]
      exact Ideal.subset_span ⟨i, mem_univ _, rfl⟩
    · rw [if_neg hi, map_zero]
      exact Ideal.zero_mem _

/-- The actual component of the given vector-valued analytic graph representative. -/
def actualBlockGraphValueGerm {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (i : Fin n) :
    HolGerm (ComplexModel n) :=
  HolGerm.mk (fun z => D.value z i)
    ((show ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ D.baseDomain from
      D.isOpen_baseDomain.mem_nhds D.zero_mem_baseDomain).mono fun z hz =>
      (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp z
        (D.holomorphic.differentiableAt (D.isOpen_baseDomain.mem_nhds hz)))

/-- Its actual graph correction reads only B-complement coordinates. -/
def actualBlockGraphShiftGerm {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (i : Fin n) :
    HolGerm (ComplexModel n) :=
  if i ∈ C then actualBlockProjectionGermHom Bᶜ (actualBlockGraphValueGerm D i) else 0

theorem actualBlockGraphGermEquiv_coordinate {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) :
    actualBlockGraphGermEquiv D (coordinateGerm i) = coordinateGerm i + actualBlockGraphShiftGerm D i := by
  by_cases hi : i ∈ C
  · rw [actualBlockGraphShiftGerm, if_pos hi]
    unfold coordinateGerm actualBlockGraphValueGerm actualBlockProjectionGermHom
    rw [actualBlockGraphGermEquiv_mk, compAlgHom_mk, ← HolGerm.mk_add]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z => by simp [actualBlockGraphMap_apply, hi])
  · rw [actualBlockGraphGermEquiv_coordinate_fixed D i hi,
      actualBlockGraphShiftGerm, if_neg hi, add_zero]

theorem actualTaylor_blockGraphShift {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (i : Fin n) :
    actualUnshiftedTaylorAlgHom n (actualBlockGraphShiftGerm D i) =
      if i ∈ C then actualFormalBlockCoordinateProjection Bᶜ
        (actualUnshiftedTaylorAlgHom n (actualBlockGraphValueGerm D i)) else 0 := by
  by_cases hi : i ∈ C
  · rw [actualBlockGraphShiftGerm, if_pos hi, if_pos hi]
    exact congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ =>
      f (actualBlockGraphValueGerm D i)) (actualTaylor_blockProjection Bᶜ)
  · rw [actualBlockGraphShiftGerm, if_neg hi, if_neg hi, map_zero]

theorem actualBlockGraphShift_coeff_zero {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (i : Fin n) :
    MvPowerSeries.coeff 0 (actualUnshiftedTaylorAlgHom n (actualBlockGraphShiftGerm D i)) = 0 := by
  rw [actualTaylor_blockGraphShift]
  by_cases hi : i ∈ C
  · rw [if_pos hi, coeff_actualFormalBlockCoordinateProjection]
    simp only [Finsupp.zero_apply, implies_true, if_true]
    rw [actualTaylor_coeff_zero, actualBlockGraphValueGerm, HolGerm.eval_mk, D.zero]
    rfl
  · rw [if_neg hi, map_zero]

theorem actualBlockGraphShift_coeff_block_single {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i j : Fin n) (hj : j ∈ B) :
    MvPowerSeries.coeff (Finsupp.single j 1)
      (actualUnshiftedTaylorAlgHom n (actualBlockGraphShiftGerm D i)) = 0 := by
  rw [actualTaylor_blockGraphShift]
  by_cases hi : i ∈ C
  · rw [if_pos hi, coeff_actualFormalBlockCoordinateProjection]
    have hn : ¬∀ l ∉ Bᶜ, (Finsupp.single j 1 : Fin n →₀ ℕ) l = 0 := by
      intro h
      have h0 := h j (by simpa using hj)
      exact Nat.one_ne_zero (by simpa only [Finsupp.single_eq_same] using h0)
    rw [if_neg hn]
  · rw [if_neg hi, map_zero]

/-- Only the genuine free first coefficients enter this structural hypothesis.
The internally solved next graph will produce it from its actual triangular Jacobian. -/
def ActualBlockGraphLinearPriority {B C : Set (Fin n)} (D : ActualBlockGraphData B C) : Prop :=
  ∀ j ∈ C, ∀ i ∉ B,
    MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single j 1) →
    MvPowerSeries.coeff (Finsupp.single i 1)
      (actualUnshiftedTaylorAlgHom n (actualBlockGraphValueGerm D j)) = 0

private theorem exponent_below_coordinate (i : Fin n) (α : Fin n →₀ ℕ)
    (hα : MonomialOrder.degLex.toSyn α < MonomialOrder.degLex.toSyn (Finsupp.single i 1)) :
    α = 0 ∨ ∃ j : Fin n, α = Finsupp.single j 1 := by
  have hd : α.degree ≤ 1 := by
    rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp hα) with h | ⟨h, _⟩
    · simp only [ofDegLex_toDegLex, Finsupp.degree_single] at h
      omega
    · simpa only [ofDegLex_toDegLex, Finsupp.degree_single] using h.le
  by_cases hz : α.degree = 0
  · exact Or.inl ((Finsupp.degree_eq_zero_iff α).mp hz)
  · have h1 : α.degree = 1 := by omega
    right
    have hr : α ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
      rw [Finsupp.range_single_one]
      exact h1
    obtain ⟨j, hj⟩ := hr
    exact ⟨j, hj.symm⟩

/-- Internally derived full coordinate head data from the actual graph's first jet. -/
theorem actualBlockGraphGermEquiv_coordinate_initial_data {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D) (j : Fin n) :
    MvPowerSeries.coeff (Finsupp.single j 1)
      (actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm j))) = 1 ∧
    ∀ α, MonomialOrder.degLex.toSyn α < MonomialOrder.degLex.toSyn (Finsupp.single j 1) →
      MvPowerSeries.coeff α
        (actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm j))) = 0 := by
  rw [actualBlockGraphGermEquiv_coordinate, map_add, actualUnshiftedTaylor_coordinate]
  constructor
  · rw [map_add]
    by_cases hj : j ∈ C
    · rw [actualBlockGraphShift_coeff_block_single D j j (D.subset hj)]
      simp
    · rw [actualBlockGraphShiftGerm, if_neg hj, map_zero, map_zero]
      simp
  · intro α hα
    have hne : α ≠ Finsupp.single j 1 := by
      intro he
      exact (ne_of_lt hα) (congrArg MonomialOrder.degLex.toSyn he)
    rw [map_add, MvPowerSeries.coeff_X, if_neg hne, zero_add]
    rcases exponent_below_coordinate j α hα with rfl | ⟨i, rfl⟩
    · exact actualBlockGraphShift_coeff_zero D j
    · by_cases hi : i ∈ B
      · exact actualBlockGraphShift_coeff_block_single D j i hi
      · rw [actualTaylor_blockGraphShift]
        by_cases hj : j ∈ C
        · rw [if_pos hj, coeff_actualFormalBlockCoordinateProjection]
          have hc := hpriority j hj i hi hα
          rw [hc]
          split_ifs <;> rfl
        · rw [if_neg hj, map_zero]

/-- The actual opposite graph, on exactly the same honest open base domain. -/
def ActualBlockGraphData.neg {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    ActualBlockGraphData B C where
  subset := D.subset
  baseDomain := D.baseDomain
  isOpen_baseDomain := D.isOpen_baseDomain
  zero_mem_baseDomain := D.zero_mem_baseDomain
  value := fun z => -D.value z
  holomorphic := D.holomorphic.neg
  zero := by simp only [D.zero, neg_zero]

theorem actualBlockGraphValueGerm_neg {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) :
    actualBlockGraphValueGerm D.neg i = -actualBlockGraphValueGerm D i := by
  unfold actualBlockGraphValueGerm
  rw [← HolGerm.mk_neg]
  rfl

theorem actualBlockGraphLinearPriority_neg {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (hpriority : ActualBlockGraphLinearPriority D) :
    ActualBlockGraphLinearPriority D.neg := by
  intro j hj i hi hij
  rw [actualBlockGraphValueGerm_neg, map_neg, map_neg, hpriority j hj i hi hij, neg_zero]

theorem actualBlockGraphGermEquiv_comp_neg {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (F : HolGerm (ComplexModel n)) :
    actualBlockGraphGermEquiv D (actualBlockGraphGermEquiv D.neg F) = F := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    rw [actualBlockGraphGermEquiv_mk, actualBlockGraphGermEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z => congrArg f
      (actualBlockGraphMap_inverse B C D.subset D.value z))

theorem actualBlockGraphGermEquiv_neg_comp {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (F : HolGerm (ComplexModel n)) :
    actualBlockGraphGermEquiv D.neg (actualBlockGraphGermEquiv D F) = F := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    rw [actualBlockGraphGermEquiv_mk, actualBlockGraphGermEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z => congrArg f (by
      simpa only [ActualBlockGraphData.neg, neg_neg] using
        actualBlockGraphMap_inverse B C D.subset (fun x => -D.value x) z))

/-- Genuine entire Taylor coordinates of the actual analytic graph pullback. -/
def actualBlockGraphFormalCoordinates {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) : MvPowerSeries (Fin n) ℂ :=
  actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm i))

theorem actualBlockGraphFormalCoordinates_constant_zero {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) :
    MvPowerSeries.constantCoeff (actualBlockGraphFormalCoordinates D i) = 0 := by
  change MvPowerSeries.coeff 0
    (actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm i))) = 0
  rw [actualBlockGraphGermEquiv_coordinate, map_add, map_add,
    actualUnshiftedTaylor_coordinate, actualBlockGraphShift_coeff_zero, add_zero]
  simp

/-- The whole formal graph substitution is constructed from actual zero-constant
Taylor coordinates; no formal inverse or convergence certificate is supplied. -/
def actualBlockGraphFormalHom {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  actualMonicCoordinateSubstitution (actualBlockGraphFormalCoordinates D)
    (actualBlockGraphFormalCoordinates_constant_zero D)

theorem actualBlockGraphFormalHom_X {B C : Set (Fin n)}
    (D : ActualBlockGraphData B C) (i : Fin n) :
    actualBlockGraphFormalHom D (MvPowerSeries.X i) = actualBlockGraphFormalCoordinates D i :=
  MvPowerSeries.substAlgHom_X
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (actualBlockGraphFormalCoordinates_constant_zero D)) i

/-- True whole-ring Taylor naturality is derived from original coordinate
identities and original localness, without a formal pullback premise. -/
theorem actualTaylor_blockGraph {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    (actualUnshiftedTaylorAlgHom n).comp (actualBlockGraphGermEquiv D).toAlgHom =
      (actualBlockGraphFormalHom D).comp (actualUnshiftedTaylorAlgHom n) := by
  apply actualGermAlgHom_eq_of_coordinate_images
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm i)) =
      actualBlockGraphFormalHom D (actualUnshiftedTaylorAlgHom n (coordinateGerm i))
    rw [actualUnshiftedTaylor_coordinate, actualBlockGraphFormalHom_X]
    rfl
  · intro i
    change actualUnshiftedTaylorAlgHom n (actualBlockGraphGermEquiv D (coordinateGerm i)) ∈ _
    have hmap := map_actualGerm_maximalIdeal_le_formal_coordinates (actualUnshiftedTaylorAlgHom n)
      (fun j => by
        rw [actualUnshiftedTaylor_coordinate]
        exact Ideal.subset_span ⟨j, mem_univ _, rfl⟩)
    apply hmap
    apply Ideal.mem_map_of_mem
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rw [← actualTaylor_coeff_zero]
    exact actualBlockGraphFormalCoordinates_constant_zero D i

private theorem formal_graph_comp_inverse {B C : Set (Fin n)}
    (D E : ActualBlockGraphData B C)
    (hDE : ∀ F : HolGerm (ComplexModel n),
      actualBlockGraphGermEquiv D (actualBlockGraphGermEquiv E F) = F)
    (F : MvPowerSeries (Fin n) ℂ) :
    actualBlockGraphFormalHom D (actualBlockGraphFormalHom E F) = F := by
  have hcoord (i : Fin n) : actualBlockGraphFormalHom D
      (actualBlockGraphFormalCoordinates E i) = MvPowerSeries.X i := by
    have h := congrArg (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ =>
      f (actualBlockGraphGermEquiv E (coordinateGerm i))) (actualTaylor_blockGraph D)
    change actualUnshiftedTaylorAlgHom n
      (actualBlockGraphGermEquiv D (actualBlockGraphGermEquiv E (coordinateGerm i))) =
      actualBlockGraphFormalHom D (actualBlockGraphFormalCoordinates E i) at h
    rw [hDE, actualUnshiftedTaylor_coordinate] at h
    exact h.symm
  dsimp only [actualBlockGraphFormalHom, actualMonicCoordinateSubstitution]
  rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
  have hc : (fun i => MvPowerSeries.substAlgHom
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (actualBlockGraphFormalCoordinates_constant_zero D))
        (actualBlockGraphFormalCoordinates E i)) = MvPowerSeries.X := funext hcoord
  rw [hc, MvPowerSeries.subst_self]
  rfl

/-- Both entire formal inverse substitutions come from the two genuine analytic graphs. -/
def actualBlockGraphFormalEquiv {B C : Set (Fin n)} (D : ActualBlockGraphData B C) :
    MvPowerSeries (Fin n) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := actualBlockGraphFormalHom D
  invFun := actualBlockGraphFormalHom D.neg
  left_inv F := formal_graph_comp_inverse D.neg D (actualBlockGraphGermEquiv_neg_comp D) F
  right_inv F := formal_graph_comp_inverse D D.neg (actualBlockGraphGermEquiv_comp_neg D) F
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := (actualBlockGraphFormalHom D).commutes

/-- The actual graph node: whole formal heads in BOTH directions, true analytic
multi-derivative commutation, and the WHOLE fixed old coordinate ideals. -/
theorem actualAnalyticBlockGraphTranslation_initial_and_derivatives
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C)
    (hpriority : ActualBlockGraphLinearPriority D) :
    (∀ F : MvPowerSeries (Fin n) ℂ, ∀ hF : F ≠ 0,
      ∃ hSF : actualBlockGraphFormalEquiv D F ≠ 0,
        actualInitialExponent MonomialOrder.degLex (actualBlockGraphFormalEquiv D F) hSF =
          actualInitialExponent MonomialOrder.degLex F hF ∧
        MvPowerSeries.coeff (actualInitialExponent MonomialOrder.degLex F hF)
          (actualBlockGraphFormalEquiv D F) =
            MvPowerSeries.coeff (actualInitialExponent MonomialOrder.degLex F hF) F) ∧
    (∀ F : MvPowerSeries (Fin n) ℂ, ∀ hF : F ≠ 0,
      ∃ hSF : (actualBlockGraphFormalEquiv D).symm F ≠ 0,
        actualInitialExponent MonomialOrder.degLex ((actualBlockGraphFormalEquiv D).symm F) hSF =
          actualInitialExponent MonomialOrder.degLex F hF ∧
        MvPowerSeries.coeff (actualInitialExponent MonomialOrder.degLex F hF)
          ((actualBlockGraphFormalEquiv D).symm F) =
            MvPowerSeries.coeff (actualInitialExponent MonomialOrder.degLex F hF) F) ∧
    (∀ β : Fin n →₀ ℕ, (∀ i ∉ B, β i = 0) → ∀ F : HolGerm (ComplexModel n),
      actualAnalyticMultiDerivative β (actualBlockGraphGermEquiv D F) =
        actualBlockGraphGermEquiv D (actualAnalyticMultiDerivative β F)) ∧
    ∀ A : Set (Fin n), A ⊆ B \ C →
      Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
        (actualAnalyticCoordinateBlockIdeal A) = actualAnalyticCoordinateBlockIdeal A := by
  refine ⟨?_, ?_, actualBlockGraphGermEquiv_multi_derivative D, ?_⟩
  · intro F hF
    exact actualMonicCoordinateSubstitution_initial_data MonomialOrder.degLex
      (actualBlockGraphFormalCoordinates D) (actualBlockGraphFormalCoordinates_constant_zero D)
      (actualBlockGraphGermEquiv_coordinate_initial_data D hpriority) F hF
  · intro F hF
    exact actualMonicCoordinateSubstitution_initial_data MonomialOrder.degLex
      (actualBlockGraphFormalCoordinates D.neg) (actualBlockGraphFormalCoordinates_constant_zero D.neg)
      (actualBlockGraphGermEquiv_coordinate_initial_data D.neg
        (actualBlockGraphLinearPriority_neg D hpriority)) F hF
  · intro A hA
    exact map_actualAnalyticCoordinateBlockIdeal_graph D A (fun i hi => (hA hi).2)

end

end Hironaka.HironakaActualAnalyticBlockGraphTranslation
