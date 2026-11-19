import Hironaka.Resolution.HironakaActualInheritedSmallTails
import Hironaka.Resolution.HironakaActualCauchyNeumannDivision
import Hironaka.Resolution.HironakaActualDiagonalTaylor

/-! Whole analytic division by a selected part of the SAME inherited family.
The actual Cauchy operators retain the entire disjoint quotient partition.
No standardness of the selected subideal or canonicality is an input. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaActualInheritedSelectedAnalyticDivision
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFiniteDegLexWeights HironakaActualWeightedScaling HironakaActualWeightedVertexSmallTails
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualDiagonalTaylor HironakaActualRelativeNormalJetDivision
  HironakaActualSelectedVertexHomogeneousBasis HironakaActualInheritedSmallTails
variable {n : ℕ}

/-- The actual finite selected subtype, retaining the original vertex labels. -/
def inheritedSelectedCount (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (S : Set (actualInitialVertices MonomialOrder.degLex K)) : ℕ :=
  Fintype.card {a : actualInitialVertices MonomialOrder.degLex K // a ∈ S}

def inheritedSelectedEnumeration (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (S : Set (actualInitialVertices MonomialOrder.degLex K)) :
    Fin (inheritedSelectedCount K S) ≃ {a : actualInitialVertices MonomialOrder.degLex K // a ∈ S} :=
  (Fintype.equivFin {a : actualInitialVertices MonomialOrder.degLex K // a ∈ S}).symm

def inheritedSelectedWords (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (j : Fin (inheritedSelectedCount K S)) : CoordinateWord n :=
  wordOfExponent (inheritedSelectedEnumeration K S j).val.val

/-- The selected cones are literal cones of the original selected exponents;
no diagram identity for their generated ideal is involved. -/
theorem inheritedSelectedWords_avoids_iff (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (S : Set (actualInitialVertices MonomialOrder.degLex K)) (β : Fin n →₀ ℕ) :
    AvoidsCones (List.ofFn (inheritedSelectedWords K S)) β ↔
      β ∉ actualSelectedVertexDiagram K S := by
  constructor
  · intro havoid hβ
    obtain ⟨a, ha, hab⟩ := hβ
    let v : {a : actualInitialVertices MonomialOrder.degLex K // a ∈ S} := ⟨a, ha⟩
    let j := (inheritedSelectedEnumeration K S).symm v
    have hmem : inheritedSelectedWords K S j ∈ List.ofFn (inheritedSelectedWords K S) :=
      List.mem_ofFn.mpr ⟨j, rfl⟩
    apply havoid _ hmem
    simpa only [inheritedSelectedWords, j, Equiv.apply_symm_apply, wordExponent_wordOfExponent] using hab
  · intro hβ w hw hle
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    apply hβ
    refine ⟨(inheritedSelectedEnumeration K S j).val,
      (inheritedSelectedEnumeration K S j).property, ?_⟩
    simpa only [inheritedSelectedWords, wordExponent_wordOfExponent] using hle

private theorem weighted_joint_eq_diagonal (W : Fin n → ℕ) (s : ℂ) (z : ComplexModel n) :
    actualWeightedScalingMap W
        (jointPoint n (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)) =
      actualDiagonalMap (fun i => s ^ W i) z := by
  ext i
  let p : CoordinateSpace n × ℂ := (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)
  have hp : jointPoint n p (parameterIndex n) = s := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) ((0 : Fin 1).natAdd n)) p = s
    rw [Fin.addCases_right]
    rfl
  have hb : jointPoint n p (i.castAdd 1) = z i := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) (i.castAdd 1)) p = z i
    rw [Fin.addCases_left]
    rfl
  change jointPoint n p (parameterIndex n) ^ W i * jointPoint n p (i.castAdd 1) = s ^ W i * z i
  rw [hp,hb]

private theorem modelGerm_eq_sum_mul_add
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    {h r : CoordinateSpace n → ℂ} {q G : ι → CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R))
    (hq : ∀ j, DifferentiableOn ℂ (q j) (ball 0 R))
    (hG : ∀ j, DifferentiableOn ℂ (G j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R))
    (he : ∀ z ∈ ball (0 : CoordinateSpace n) R, h z = ∑ j, q j z * G j z + r z) :
    modelGerm hR hh = ∑ j, modelGerm hR (hq j) * modelGerm hR (hG j) + modelGerm hR hr := by
  have hp (j : ι) := eventually_differentiableAt_mul
    (modelFunction_holAt hR (hq j)) (modelFunction_holAt hR (hG j))
  have hsum := eventually_differentiableAt_sum Finset.univ hp
  have hall := eventually_differentiableAt_add hsum (modelFunction_holAt hR hr)
  change HolGerm.mk (modelFunction h) (modelFunction_holAt hR hh) = _
  calc
    _ = HolGerm.mk (fun z : ComplexModel n =>
        ∑ j, modelFunction (q j) z * modelFunction (G j) z + modelFunction r z) hall := by
      apply HolGerm.mk_eq_mk_iff.mpr
      let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
      have ht : Tendsto e (nhds (0 : ComplexModel n)) (nhds (0 : CoordinateSpace n)) := by
        simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
      filter_upwards [ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hR))] with z hz
      exact he (e z) hz
    _ = _ := by
      rw [HolGerm.mk_add _ _ hsum (modelFunction_holAt hR hr),
        HolGerm.mk_sum Finset.univ _ hp]
      congr 1


variable {d t : ℕ} {K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)}

private theorem inheritedNormalizedScaledRepresentative_hol
    {G : ActualAnalyticInheritedFamily d t K} (P : ActualInheritedWeightedTailData G)
    (a : actualInitialVertices MonomialOrder.degLex K) {s : ℂ} (hs : s ∈ ball 0 P.radius) :
    DifferentiableOn ℂ (inheritedNormalizedScaledRepresentative P a s) (ball 0 P.radius) := by
  have hgraph : Differentiable ℂ (fun z : CoordinateSpace (d+t) => (z,s)) :=
    differentiable_id.prodMk (differentiable_const s)
  have hd := (P.scaled_hol a).comp hgraph.differentiableOn (fun z hz => ⟨hz,hs⟩)
  unfold inheritedNormalizedScaledRepresentative
  simp only [div_eq_mul_inv]
  exact hd.mul_const ((s ^ weightedDegree (degLexWeight (d+t) P.germs.degreeBound) a.val)⁻¹)

private theorem modelGerm_inheritedNormalizedScaledRepresentative
    {G : ActualAnalyticInheritedFamily d t K} (P : ActualInheritedWeightedTailData G)
    (a : actualInitialVertices MonomialOrder.degLex K) {s : ℂ} (hs : s ∈ ball 0 P.radius) :
    modelGerm P.radius_pos (inheritedNormalizedScaledRepresentative_hol P a hs) =
      HolGerm.constHom ((s ^ weightedDegree (degLexWeight (d+t) P.germs.degreeBound) a.val)⁻¹) *
        actualDiagonalPullback (fun i => s ^ degLexWeight (d+t) P.germs.degreeBound i) (G.germs a) := by
  rw [← P.representative_eq a]
  unfold actualDiagonalPullback
  rw [compAlgHom_mk, ← HolGerm.mk_const, ← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    simp only [modelFunction, Function.comp_apply, inheritedNormalizedScaledRepresentative,
      weighted_joint_eq_diagonal, div_eq_mul_inv, mul_comm]

/-- The SAME selected germs and SAME numerator internally supply genuine
whole analytic quotients and remainder. The entire quotient owner partition
is retained, even when the selected subideal is not a standard basis. -/
theorem exists_actual_inherited_selected_analytic_division
    (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∃ (Q : Fin (inheritedSelectedCount K S) → HolGerm (ComplexModel (d+t)))
      (R : HolGerm (ComplexModel (d+t))),
      G.germs a = (∑ j, Q j * G.germs (inheritedSelectedEnumeration K S j).val) + R ∧
      (∀ j β, ¬ AvoidsCones ((List.ofFn (inheritedSelectedWords K S)).take j.val)
        (β + (inheritedSelectedEnumeration K S j).val.val) →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (Q j)) = 0) ∧
      ∀ β ∈ actualSelectedVertexDiagram K S,
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) R) = 0 := by
  obtain ⟨P⟩ := nonempty_actualInheritedWeightedTailData G
  let w := inheritedSelectedWords K S
  obtain ⟨D⟩ := nonempty_concreteNeumannData P.radius P.radius_pos w
  obtain ⟨s, hs0, hs, hGhol, hGtail⟩ := exists_inherited_smallParameter P D.epsilon D.epsilon_pos
  let W := degLexWeight (d+t) P.germs.degreeBound
  let c : Fin (d+t) → ℂ := fun i => s ^ W i
  have hc (i : Fin (d+t)) : c i ≠ 0 := pow_ne_zero _ hs0
  let H (j : Fin (inheritedSelectedCount K S)) (z : CoordinateSpace (d+t)) :=
    s * P.tailFactor (inheritedSelectedEnumeration K S j).val (z,s)
  have hHd (j : Fin (inheritedSelectedCount K S)) : DifferentiableOn ℂ (H j) (ball 0 P.radius) := by
    have hgraph : Differentiable ℂ (fun z : CoordinateSpace (d+t) => (z,s)) :=
      differentiable_id.prodMk (differentiable_const s)
    have hd := (P.factor_hol (inheritedSelectedEnumeration K S j).val).comp hgraph.differentiableOn
      (fun z hz => ⟨hz,hs⟩)
    exact (differentiable_const s).differentiableOn.fun_mul hd
  have hHb (j : Fin (inheritedSelectedCount K S)) (z : CoordinateSpace (d+t))
      (hz : z ∈ ball 0 P.radius) : ‖H j z‖ ≤ D.epsilon :=
    (hGtail (inheritedSelectedEnumeration K S j).val z hz).2.le
  let F := inheritedNormalizedScaledRepresentative P a s
  let M := P.radius ^ wordDegree (wordOfExponent a.val) + D.epsilon
  have hFd : DifferentiableOn ℂ F (ball 0 P.radius) := hGhol a
  have hM : 0 ≤ M := add_nonneg (pow_nonneg P.radius_pos.le _) D.epsilon_pos.le
  have hFb : ∀ z ∈ ball (0 : CoordinateSpace (d+t)) P.radius, ‖F z‖ ≤ M := by
    intro z hz
    have hsplit : F z = coordinateMonomial a.val z + s * P.tailFactor a (z,s) := by
      have he := (hGtail a z hz).1
      change F z - coordinateMonomial a.val z = s * P.tailFactor a (z,s) at he
      linear_combination he
    have hmono : ‖coordinateMonomial a.val z‖ ≤ P.radius ^ wordDegree (wordOfExponent a.val) := by
      rw [coordinateMonomial, ← wordMonomial_wordOfExponent]
      exact wordMonomial_norm_le (wordOfExponent a.val) P.radius_pos hz
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hmono (hGtail a z hz).2.le)
  have hd := neumannSums_differentiableOn P.radius_pos D hHd hHb hM hFd hFb
  have hsupport := neumannSums_whole_support P.radius_pos D hHd hHb hM hFd hFb
  let q (j : Fin (inheritedSelectedCount K S)) := neumannQuotientSum P.radius w H F j
  let r := neumannRemainderSum P.radius w H F
  let GG (j : Fin (inheritedSelectedCount K S)) :=
    inheritedNormalizedScaledRepresentative P (inheritedSelectedEnumeration K S j).val s
  have hGGhol (j : Fin (inheritedSelectedCount K S)) :
      DifferentiableOn ℂ (GG j) (ball 0 P.radius) := hGhol _
  have he : ∀ z ∈ ball (0 : CoordinateSpace (d+t)) P.radius,
      F z = (∑ j, q j z * GG j z) + r z := by
    intro z hz
    have hn := neumannSums_division P.radius_pos D hHd hHb hM hFd hFb hz
    change F z = (∑ j, q j z * (wordMonomial (w j) z + H j z)) + r z at hn
    rw [hn]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hg := (hGtail (inheritedSelectedEnumeration K S j).val z hz).1
    dsimp only [w, inheritedSelectedWords]
    rw [wordMonomial_wordOfExponent]
    change coordinateMonomial _ z + H j z = GG j z
    change GG j z - coordinateMonomial _ z = H j z at hg
    linear_combination -hg
  let qG (j : Fin (inheritedSelectedCount K S)) := modelGerm P.radius_pos (hd.1 j)
  let rG := modelGerm P.radius_pos hd.2
  have hScaled := modelGerm_eq_sum_mul_add P.radius_pos hFd hd.1 hGGhol hd.2 he
  have hScaledF : modelGerm P.radius_pos hFd =
      HolGerm.constHom ((s ^ weightedDegree W a.val)⁻¹) * actualDiagonalPullback c (G.germs a) :=
    modelGerm_inheritedNormalizedScaledRepresentative P a hs
  have hScaledG (j : Fin (inheritedSelectedCount K S)) : modelGerm P.radius_pos (hGGhol j) =
      HolGerm.constHom ((s ^ weightedDegree W (inheritedSelectedEnumeration K S j).val.val)⁻¹) *
        actualDiagonalPullback c (G.germs (inheritedSelectedEnumeration K S j).val) :=
    modelGerm_inheritedNormalizedScaledRepresentative P _ hs
  rw [hScaledF] at hScaled
  simp_rw [hScaledG] at hScaled
  let E := actualDiagonalPullback (fun i => (c i)⁻¹)
  let u : HolGerm (ComplexModel (d+t)) := HolGerm.constHom (s ^ weightedDegree W a.val)
  let Q (j : Fin (inheritedSelectedCount K S)) :=
    u * E (qG j) * HolGerm.constHom ((s ^ weightedDegree W (inheritedSelectedEnumeration K S j).val.val)⁻¹)
  let R := u * E rG
  have hUn := congrArg E hScaled
  dsimp only [E] at hUn
  simp only [map_add, map_sum, map_mul, actualDiagonalPullback_const,
    actualDiagonalPullback_inverse c hc] at hUn
  have hunit : u * HolGerm.constHom ((s ^ weightedDegree W a.val)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hs0), map_one]
  refine ⟨Q, R, ?_, ?_, ?_⟩
  · calc
      G.germs a = u * (HolGerm.constHom ((s ^ weightedDegree W a.val)⁻¹) * G.germs a) := by
        rw [← mul_assoc, hunit, one_mul]
      _ = u * ((∑ j, E (qG j) *
          (HolGerm.constHom ((s ^ weightedDegree W (inheritedSelectedEnumeration K S j).val.val)⁻¹) *
            G.germs (inheritedSelectedEnumeration K S j).val)) + E rG) := congrArg (fun x => u * x) hUn
      _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [Q]
        ring
  · intro j β hbad
    have hz : MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (qG j)) = 0 := by
      apply hsupport.1 j β
      simpa only [w, inheritedSelectedWords, wordExponent_wordOfExponent] using hbad
    have hconst (z : ℂ) : actualUnshiftedTaylorAlgHom (d+t) (HolGerm.constHom z) = MvPowerSeries.C z :=
      (actualUnshiftedTaylorAlgHom (d+t)).commutes z
    dsimp only [Q, u, E]
    simp only [map_mul, hconst]
    rw [MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_C_mul,
      coeff_actualDiagonalPullback, hz, mul_zero, mul_zero, zero_mul]
  · intro β hβ
    have hz : MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) rG) = 0 := by
      apply hsupport.2 β
      intro havoid
      exact (inheritedSelectedWords_avoids_iff K S β).mp havoid hβ
    have hconst (z : ℂ) : actualUnshiftedTaylorAlgHom (d+t) (HolGerm.constHom z) = MvPowerSeries.C z :=
      (actualUnshiftedTaylorAlgHom (d+t)).commutes z
    dsimp only [R, u, E]
    rw [map_mul, hconst, MvPowerSeries.coeff_C_mul, coeff_actualDiagonalPullback, hz, mul_zero, mul_zero]

end
end Hironaka.HironakaActualInheritedSelectedAnalyticDivision
