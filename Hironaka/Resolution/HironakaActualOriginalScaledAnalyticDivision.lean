import Hironaka.Resolution.HironakaActualCauchyNeumannDivision
import Hironaka.Resolution.HironakaActualWeightedVertexSmallTails

/-! Original-ideal-only coupling of actual small tails with actual Cauchy-Neumann analytic division. -/
set_option autoImplicit false
open Set Metric Classical

namespace Hironaka.HironakaActualOriginalScaledAnalyticDivision

noncomputable section
attribute [local instance] Classical.propDecidable

open HolGerm HironakaActualFormalInitialDiagram HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualWeightedVertexSmallTails

def actualVertexCount (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) : ℕ :=
  Fintype.card (ActualVertexIndex n I)

def actualVertexEnumeration (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    Fin (actualVertexCount n I) ≃ ActualVertexIndex n I :=
  (Fintype.equivFin (ActualVertexIndex n I)).symm

def actualVertexWords (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (j : Fin (actualVertexCount n I)) : CoordinateWord n :=
  wordOfExponent (actualVertexEnumeration n I j).val

/-- The internally enumerated true cones have EXACTLY the true whole original diagram. -/
theorem actualVertexWords_avoids_iff (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (b : Fin n →₀ ℕ) :
    AvoidsCones (List.ofFn (actualVertexWords n I)) b ↔
      b ∉ actualInitialDiagram MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  constructor
  · intro havoid hb
    obtain ⟨a,ha,hab⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex _ b).mp hb
    let v : ActualVertexIndex n I := ⟨a,ha⟩
    let j := (actualVertexEnumeration n I).symm v
    have hmem : actualVertexWords n I j ∈ List.ofFn (actualVertexWords n I) := List.mem_ofFn.mpr ⟨j,rfl⟩
    apply havoid _ hmem
    simpa only [actualVertexWords,j,Equiv.apply_symm_apply,wordExponent_wordOfExponent] using hab
  · intro hb w hw hle
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    apply hb
    apply (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex _ b).mpr
    refine ⟨(actualVertexEnumeration n I j).val,(actualVertexEnumeration n I j).property,?_⟩
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using hle

/-- The final producer supplies all actual small tails and operators internally from I.
The additional input h is only an actual bounded holomorphic function on the produced domain. -/
theorem exists_actualOriginal_scaled_analytic_division (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ P : ActualWeightedVertexSmallTailData n I, ∃ s : ℂ, s ≠ 0 ∧ s ∈ ball 0 P.radius ∧
      ∀ (M : ℝ) (h : CoordinateSpace n → ℂ) (_hh : DifferentiableOn ℂ h (ball 0 P.radius)),
        (∀ z ∈ ball (0 : CoordinateSpace n) P.radius, ‖h z‖ ≤ M) →
        ∃ (q : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ) (r : CoordinateSpace n → ℂ)
          (hq : ∀ j, DifferentiableOn ℂ (q j) (ball 0 P.radius))
          (hr : DifferentiableOn ℂ r (ball 0 P.radius)),
          (∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
            h z = ∑ j, q j z * normalizedScaledRepresentative P (actualVertexEnumeration n I j) s z + r z) ∧
          (∀ j b, ¬ AvoidsCones ((List.ofFn (actualVertexWords n I)).take j.val)
              (b + (actualVertexEnumeration n I j).val) →
            MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n (modelGerm P.radius_pos (hq j))) = 0) ∧
          ∀ b ∈ actualInitialDiagram MonomialOrder.degLex (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
            MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n (modelGerm P.radius_pos hr)) = 0 := by
  obtain ⟨P⟩ := nonempty_actualWeightedVertexSmallTailData n I
  let w := actualVertexWords n I
  obtain ⟨D⟩ := nonempty_concreteNeumannData P.radius P.radius_pos w
  obtain ⟨s,hs0,hs,_hGhol,hGtail⟩ := exists_smallParameter P D.epsilon D.epsilon_pos
  let H (j : Fin (actualVertexCount n I)) (z : CoordinateSpace n) :=
    s * P.tailFactor (actualVertexEnumeration n I j) (z,s)
  have hHd (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ (H j) (ball 0 P.radius) := by
    have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,s)) :=
      differentiable_id.prodMk (differentiable_const _)
    have hd := (P.factor_hol (actualVertexEnumeration n I j)).comp hgraph.differentiableOn
      (fun z hz => ⟨hz,hs⟩)
    exact (differentiable_const s).differentiableOn.fun_mul hd
  have hHb (j : Fin (actualVertexCount n I)) (z : CoordinateSpace n) (hz : z ∈ ball 0 P.radius) :
      ‖H j z‖ ≤ D.epsilon := (hGtail (actualVertexEnumeration n I j) z hz).2.le
  refine ⟨P,s,hs0,hs,?_⟩
  intro M h hh hbound
  have hM : 0 ≤ M := (norm_nonneg (h 0)).trans (hbound 0 (mem_ball_self P.radius_pos))
  have hd := neumannSums_differentiableOn P.radius_pos D hHd hHb hM hh hbound
  have hsupport := neumannSums_whole_support P.radius_pos D hHd hHb hM hh hbound
  refine ⟨neumannQuotientSum P.radius w H h,neumannRemainderSum P.radius w H h,hd.1,hd.2,?_,?_,?_⟩
  · intro z hz
    have he := neumannSums_division P.radius_pos D hHd hHb hM hh hbound hz
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hgen := (hGtail (actualVertexEnumeration n I j) z hz).1
    change wordMonomial (actualVertexWords n I j) z + H j z =
      normalizedScaledRepresentative P (actualVertexEnumeration n I j) s z
    rw [actualVertexWords,wordMonomial_wordOfExponent]
    change coordinateMonomial (actualVertexEnumeration n I j).val z + H j z =
      normalizedScaledRepresentative P (actualVertexEnumeration n I j) s z
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp hgen).symm
  · intro j b hbad
    apply hsupport.1 j b
    simpa only [w,actualVertexWords,wordExponent_wordOfExponent] using hbad
  · intro b hb
    apply hsupport.2 b
    intro havoid
    exact (actualVertexWords_avoids_iff n I b).mp havoid hb

end

end Hironaka.HironakaActualOriginalScaledAnalyticDivision
