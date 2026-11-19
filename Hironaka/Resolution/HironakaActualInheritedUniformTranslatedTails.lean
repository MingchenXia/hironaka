import Hironaka.Resolution.HironakaActualInheritedSourceCauchyRemainder
import Hironaka.Resolution.HironakaActualTranslatedCauchyOwnerSupport
import Mathlib.Topology.UniformSpace.HeineCantor

/-! One actual source/target Cauchy domain for every real translation of the
SAME inherited analytic full family. The weighted scale is chosen once using
both genuine Cauchy thresholds. Uniform continuity is applied only to the
finite polynomial heads on an actual compact ball. No target monic head,
target diagram, marked order or HS equality is assumed. Source-only draft;
this is a lower BP3 producer with no independent blueprint-node credit. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedUniformTranslatedTails
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualWeightedVertexSmallTails
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyMonomialDivision
  HironakaActualCauchyDiagramPartition HironakaActualCauchyEnumeratedPartition
  HironakaActualCauchyNeumannDivision HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
  HironakaActualInheritedSourceCauchyRemainder HironakaActualTranslatedCauchyOwnerSupport

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
variable {G : ActualAnalyticInheritedFamily n 0
  (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

/-- The ACTUAL translated tail relative to the same original monomial heads.
Its small norm is proved below; its target head is not presumed monic. -/
def actualInheritedTranslatedTail (P : ActualInheritedWeightedTailData G) (s : ℂ)
    (p : CoordinateSpace n) (j : Fin (actualVertexCount n I)) (z : CoordinateSpace n) : ℂ :=
  actualInheritedSourceScaledFamily P s j (p+z) - wordMonomial (actualVertexWords n I j) z

private theorem eventually_translate_halfBall_maps {R : ℝ} (hR : 0 < R) :
    ∀ᶠ p : CoordinateSpace n in 𝓝 0,
      MapsTo (fun z => p+z) (ball 0 (R/2)) (ball 0 R) := by
  have hquarter : 0 < R/4 := div_pos hR (by norm_num)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hquarter)] with p hp
  intro z hz
  have hpN : ‖p‖ < R/4 := mem_ball_zero_iff.mp hp
  have hzN : ‖z‖ < R/2 := mem_ball_zero_iff.mp hz
  apply mem_ball_zero_iff.mpr
  exact (norm_add_le p z).trans_lt (by linarith)

private theorem eventually_wordMonomial_translate_small {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (w : CoordinateWord n) :
    ∀ᶠ p : CoordinateSpace n in 𝓝 0,
      ∀ z ∈ ball (0 : CoordinateSpace n) (R/2),
        ‖wordMonomial w (p+z) - wordMonomial w z‖ < ε := by
  have hu : UniformContinuousOn (wordMonomial w) (closedBall (0 : CoordinateSpace n) R) :=
    (isCompact_closedBall (0 : CoordinateSpace n) R).uniformContinuousOn_of_continuous
      (wordMonomial_differentiable w).continuous.continuousOn
  obtain ⟨η,hη,hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
  have hsmall : 0 < min η (R/4) := lt_min hη (div_pos hR (by norm_num))
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hsmall)] with p hp
  intro z hz
  have hpN : ‖p‖ < min η (R/4) := mem_ball_zero_iff.mp hp
  have hpη : ‖p‖ < η := hpN.trans_le (min_le_left _ _)
  have hpR : ‖p‖ < R/4 := hpN.trans_le (min_le_right _ _)
  have hzN : ‖z‖ < R/2 := mem_ball_zero_iff.mp hz
  have hpzR : ‖p+z‖ < R := (norm_add_le p z).trans_lt (by linarith)
  have hzR : ‖z‖ ≤ R := by linarith
  have hdist : dist (p+z) z < η := by
    simpa only [dist_eq_norm, add_sub_cancel_right] using hpη
  have hdiff := hmod (p+z) (mem_closedBall_zero_iff.mpr hpzR.le)
    z (mem_closedBall_zero_iff.mpr hzR) hdist
  simpa only [dist_eq_norm] using hdiff

/-- The SAME original family internally produces one nonzero weighted scale,
both actual Cauchy data, and ONE parameter ball, all before any polynomial
numerator or jet order is chosen. Every legal target tail is genuinely small
on the SAME fixed inner ball. No nearby initial-diagram certificate occurs. -/
theorem exists_actual_inherited_uniform_translated_tail_domain
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) :
    ∃ (P : ActualInheritedWeightedTailData G) (s : ℂ), s ≠ 0 ∧ s ∈ ball 0 P.radius ∧
      ∃ (D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
        (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I)) (δ : ℝ),
        0 < δ ∧
        (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
          ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon) ∧
        ∀ p ∈ ball (0 : CoordinateSpace n) δ,
          MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius) ∧
          (∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
            (ball 0 (P.radius/2))) ∧
          ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
            ‖actualInheritedTranslatedTail P s p j z‖ ≤ D₁.epsilon := by
  obtain ⟨P⟩ := nonempty_actualInheritedWeightedTailData G
  obtain ⟨D₀⟩ := nonempty_concreteNeumannData P.radius P.radius_pos (actualVertexWords n I)
  obtain ⟨D₁⟩ := nonempty_concreteNeumannData (P.radius/2) (half_pos P.radius_pos)
    (actualVertexWords n I)
  let ε := min D₀.epsilon (D₁.epsilon/2)
  have hε : 0 < ε := lt_min D₀.epsilon_pos (half_pos D₁.epsilon_pos)
  obtain ⟨s,hs0,hs,_hGhol,hGtail⟩ := exists_inherited_smallParameter P ε hε
  have hsource : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon := by
    intro j z hz
    exact ((hGtail (actualVertexEnumeration n I j) z hz).2.le).trans (min_le_left _ _)
  have hhead : ∀ᶠ p : CoordinateSpace n in 𝓝 0,
      ∀ j : Fin (actualVertexCount n I), ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
        ‖wordMonomial (actualVertexWords n I j) (p+z) -
          wordMonomial (actualVertexWords n I j) z‖ < D₁.epsilon/2 :=
    eventually_all.mpr fun j => eventually_wordMonomial_translate_small P.radius_pos
      (half_pos D₁.epsilon_pos) (actualVertexWords n I j)
  have hdomain := eventually_translate_halfBall_maps (n := n) P.radius_pos
  obtain ⟨δ,hδ,hδall⟩ := Metric.eventually_nhds_iff_ball.mp (hdomain.and hhead)
  refine ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,hsource,?_⟩
  intro p hp
  have hdom := (hδall p hp).1
  have hheads := (hδall p hp).2
  refine ⟨hdom,?_,?_⟩
  · intro j
    exact (actual_coordinate_translation_differentiableOn
      (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom).sub
      (wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn
  · intro j z hz
    have hpz := hdom hz
    have htail : ‖actualInheritedSourceScaledTail P s j (p+z)‖ ≤ D₁.epsilon/2 :=
      ((hGtail (actualVertexEnumeration n I j) (p+z) hpz).2.le).trans (min_le_right _ _)
    calc
      ‖actualInheritedTranslatedTail P s p j z‖ =
          ‖actualInheritedSourceScaledTail P s j (p+z) +
            (wordMonomial (actualVertexWords n I j) (p+z) -
              wordMonomial (actualVertexWords n I j) z)‖ := by
        congr 1
        unfold actualInheritedTranslatedTail
        rw [actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs j hpz]
        ring
      _ ≤ ‖actualInheritedSourceScaledTail P s j (p+z)‖ +
          ‖wordMonomial (actualVertexWords n I j) (p+z) -
            wordMonomial (actualVertexWords n I j) z‖ := norm_add_le _ _
      _ ≤ D₁.epsilon/2 + D₁.epsilon/2 := add_le_add htail (hheads j z hz).le
      _ = D₁.epsilon := by ring

end
end Hironaka.HironakaActualInheritedUniformTranslatedTails
