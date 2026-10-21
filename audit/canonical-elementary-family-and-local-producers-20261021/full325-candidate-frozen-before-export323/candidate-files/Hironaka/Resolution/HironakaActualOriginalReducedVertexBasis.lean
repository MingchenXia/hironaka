/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalVertexConvergence
import Hironaka.Resolution.HironakaActualConvergentTaylorRealization
/-!
# Actual canonical reduced holomorphic generators and whole original analytic division

Every original ideal internally produces genuine holomorphic germs with the
EXACT canonical reduced formal Taylor images, and those germs generate the
whole original ideal. Actual small-radius Neumann division and inverse Taylor
realization give holomorphic owner quotients and the canonical analytic normal
remainder for EVERY original germ. The resulting genuine complex-linear
idempotent projection has precisely the original ideal as kernel and induces
the whole original quotient's literal analytic normal-representative equivalence.
No chosen prepared family, convergence, or desired division certificate is input.

Blueprint: `hironaka-actual-original-reduced-vertex-basis-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualOriginalReducedVertexBasis
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualFormalInitialDiagram
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis
  HironakaActualOriginalVertexConvergence HironakaActualConvergentTaylorRealization
  HironakaActualReducedBasisDivision HironakaActualMonomialDivisionBounds
  HironakaActualVertexSmallRadius HironakaActualAnalyticVertexPerturbation
  HironakaActualVertexNeumannDivision
variable {n : ℕ}

/-- Actual holomorphic germs whose unchanged original Taylor images are the WHOLE canonical reduced series. -/
def originalReducedVertexBasis (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) : HolGerm (ComplexModel (0+n)) :=
  let hex := exists_original_reduced_vertices_finite_mass J
  evaluationGerm (Classical.choose hex) (Classical.choose_spec hex).1
    (actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J) a)
    ((Classical.choose_spec hex).2 a).1

theorem originalReducedVertexBasis_taylor (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
    originalTaylorAlgHom n (originalReducedVertexBasis J a)=
      actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J) a := by
  unfold originalReducedVertexBasis
  exact originalTaylor_evaluationGerm _ _ _ _

theorem originalReducedVertexBasis_mem (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) : originalReducedVertexBasis J a∈J := by
  apply (mem_original_ideal_iff_formal_extension n J _).mpr
  rw [originalReducedVertexBasis_taylor]
  exact actualReducedVertexSeries_mem _ _ a

theorem originalReducedVertexBasis_span (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal.span (range (originalReducedVertexBasis J))=J := by
  apply original_formal_ideal_extension_injective n
  rw [Ideal.map_span,← Set.range_comp]
  have he : (originalTaylorAlgHom n).toRingHom ∘ originalReducedVertexBasis J=
      actualReducedVertexSeries MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J) :=
    funext fun a => originalReducedVertexBasis_taylor J a
  rw [he]
  exact (actual_formal_ideal_eq_span_reduced_vertex_series _ _).symm

private theorem monomial_finite_mass (ρ : Fin n → ℝ) (a : Fin n →₀ ℕ) (c : ℂ) :
    HasFiniteCoefficientMass ρ (MvPowerSeries.monomial a c) := by
  apply summable_of_ne_finset_zero (s := {a})
  intro b hb
  have hba : b≠a := by simpa only [Finset.mem_singleton] using hb
  simp [MvPowerSeries.coeff_monomial,hba]

/-- Actual analytic whole-germ division by the SAME fixed canonical reduced family, with owner-supported quotients. -/
theorem exists_original_reduced_vertex_division (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    ∃ (H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)))
      (s : HolGerm (ComplexModel (0+n))),
      g=(∑ a,originalReducedVertexBasis J a*H a)+s ∧
      originalTaylorAlgHom n s=actualFormalRemainder MonomialOrder.degLex
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) (originalTaylorAlgHom n g) ∧
      ∀ a β,actualDivisionOwner MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J)
        (β+a.val)≠some a → MvPowerSeries.coeff β (originalTaylorAlgHom n (H a))=0 := by
  let I := Ideal.map (originalTaylorAlgHom n).toRingHom J
  let B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n)) I :=
    { series := actualReducedVertexSeries MonomialOrder.degLex I
      mem := actualReducedVertexSeries_mem _ _
      monic := actualReducedVertexSeries_coefficient _ _
      lower := actualReducedVertexSeries_coefficient_lower _ _ }
  let A : Option (actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) →
      HolGerm (ComplexModel (0+n)) := fun i => i.elim g (originalReducedVertexBasis J)
  obtain ⟨r,hr,hM⟩ := exists_finite_originalTaylor_common_mass A
  have hTail (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) :
      HasFiniteCoefficientMass (fun _ : Fin n => r) (B.series a-MvPowerSeries.monomial a.val 1) := by
    have hmon : HasFiniteCoefficientMass (fun _ : Fin n => r) (-MvPowerSeries.monomial a.val (1 : ℂ)) := by
      simpa only [HasFiniteCoefficientMass,map_neg,norm_neg] using
        monomial_finite_mass (fun _ : Fin n => r) a.val (1 : ℂ)
    have hG : B.series a=originalTaylorAlgHom n (originalReducedVertexBasis J a) :=
      (originalReducedVertexBasis_taylor J a).symm
    rw [hG,sub_eq_add_neg]
    exact finiteCoefficientMass_add _ (fun _ => hr) _ _ (hM (some a)) hmon
  obtain ⟨ρ,hρ,hle,hB,hsmall⟩ := exists_actual_vertex_small_radius I B (fun _ => r) (fun _ => hr) hTail
  have hg : HasFiniteCoefficientMass ρ (originalTaylorAlgHom n g) :=
    finiteCoefficientMass_mono _ _ hρ hle _ (hM none)
  obtain ⟨Q,S,hQ,hS,hdivision,hcanonical,howner,_hnormal,_hbound,_hqb⟩ :=
    exists_absolute_vertex_division MonomialOrder.degLex I B ρ hρ hB hsmall (originalTaylorAlgHom n g) hg
  let H := fun a => evaluationGerm ρ hρ (Q a) (hQ a)
  let s := evaluationGerm ρ hρ S hS
  have hH (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) :
      originalTaylorAlgHom n (H a)=Q a := originalTaylor_evaluationGerm _ _ _ _
  have hs : originalTaylorAlgHom n s=S := originalTaylor_evaluationGerm _ _ _ _
  refine ⟨H,s,?_,hs.trans hcanonical,?_⟩
  · apply originalTaylorAlgHom_injective n
    rw [map_add,map_sum]
    simp_rw [map_mul,originalReducedVertexBasis_taylor,hH,hs]
    exact hdivision
  · intro a β ha
    rw [hH]
    exact howner a β ha

private theorem exists_original_normal_representative (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    ∃ s : HolGerm (ComplexModel (0+n)),originalTaylorAlgHom n s=
      actualFormalRemainder MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J)
        (originalTaylorAlgHom n g) := by
  obtain ⟨_H,s,_hdiv,hs,_howner⟩ := exists_original_reduced_vertex_division J g
  exact ⟨s,hs⟩

private def originalNormalRepresentative (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) : HolGerm (ComplexModel (0+n)) :=
  Classical.choose (exists_original_normal_representative J g)

private theorem originalNormalRepresentative_taylor (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom n (originalNormalRepresentative J g)=actualFormalRemainder MonomialOrder.degLex
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) (originalTaylorAlgHom n g) :=
  Classical.choose_spec (exists_original_normal_representative J g)

/-- Genuine analytic complex-linear canonical reduction, obtained by actual convergent whole division. -/
def originalNormalProjection (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    HolGerm (ComplexModel (0+n)) →ₗ[ℂ] HolGerm (ComplexModel (0+n)) where
  toFun := originalNormalRepresentative J
  map_add' g h := by
    apply originalTaylorAlgHom_injective n
    rw [originalNormalRepresentative_taylor,map_add,map_add,
      originalNormalRepresentative_taylor,originalNormalRepresentative_taylor,
      actualFormalRemainder_add]
  map_smul' c g := by
    apply originalTaylorAlgHom_injective n
    rw [originalNormalRepresentative_taylor,map_smul,map_smul,
      originalNormalRepresentative_taylor,actualFormalRemainder_smul]
    rfl

theorem originalNormalProjection_taylor (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom n (originalNormalProjection J g)=actualFormalRemainder MonomialOrder.degLex
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) (originalTaylorAlgHom n g) :=
  originalNormalRepresentative_taylor J g

theorem originalNormalProjection_idempotent (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    originalNormalProjection J (originalNormalProjection J g)=originalNormalProjection J g := by
  apply originalTaylorAlgHom_injective n
  rw [originalNormalProjection_taylor,originalNormalProjection_taylor,
    actualFormalRemainder_idempotent]

theorem originalNormalProjection_diagram (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) (c : Fin n →₀ ℕ)
    (hc : c∈actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
    MvPowerSeries.coeff c (originalTaylorAlgHom n (originalNormalProjection J g))=0 := by
  rw [originalNormalProjection_taylor]
  exact actualFormalRemainder_coefficient_diagram _ _ _ c hc

theorem originalNormalProjection_unique (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g s : HolGerm (ComplexModel (0+n))) (hmem : g-s∈J)
    (hnormal : ∀ c∈actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J),
      MvPowerSeries.coeff c (originalTaylorAlgHom n s)=0) : s=originalNormalProjection J g := by
  apply originalTaylorAlgHom_injective n
  rw [originalNormalProjection_taylor]
  apply actualFormalRemainder_unique _ _ _ _ _ hnormal
  simpa only [map_sub] using (mem_original_ideal_iff_formal_extension n J (g-s)).mp hmem

theorem originalNormalProjection_ker (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    LinearMap.ker (originalNormalProjection J)=J.restrictScalars ℂ := by
  ext g
  rw [LinearMap.mem_ker]
  constructor
  · intro hg
    apply (mem_original_ideal_iff_formal_extension n J g).mpr
    apply (actualFormalRemainder_eq_zero_iff _ _ _).mp
    rw [← originalNormalProjection_taylor,hg,map_zero]
  · intro hg
    apply originalTaylorAlgHom_injective n
    rw [originalNormalProjection_taylor,map_zero]
    exact (actualFormalRemainder_eq_zero_iff _ _ _).mpr
      ((mem_original_ideal_iff_formal_extension n J g).mp hg)

theorem sub_originalNormalProjection_mem (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) : g-originalNormalProjection J g∈J := by
  apply (mem_original_ideal_iff_formal_extension n J _).mpr
  rw [map_sub,originalNormalProjection_taylor]
  exact sub_actualFormalRemainder_mem _ _ _

/-- The WHOLE actual original ideal quotient, with its canonical analytic normal representative. -/
def originalNormalQuotientEquiv (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    (HolGerm (ComplexModel (0+n)) ⧸ J) ≃ₗ[ℂ] LinearMap.range (originalNormalProjection J) :=
  ((Submodule.Quotient.restrictScalarsEquiv ℂ J).symm.trans
    (Submodule.quotEquivOfEq _ _ (originalNormalProjection_ker J).symm)).trans
      (originalNormalProjection J).quotKerEquivRange

theorem originalNormalQuotientEquiv_mk (J : Ideal (HolGerm (ComplexModel (0+n))))
    (g : HolGerm (ComplexModel (0+n))) :
    (originalNormalQuotientEquiv J (Ideal.Quotient.mk J g) : HolGerm (ComplexModel (0+n)))=
      originalNormalProjection J g := by
  rfl

end
end Hironaka.HironakaActualOriginalReducedVertexBasis
