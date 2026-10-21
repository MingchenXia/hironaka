/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualMultilinearTaylorCoordinates
import Hironaka.Resolution.HironakaActualPolydiscEvaluationAlgebra

/-!
# Original whole ideals internally produce convergent canonical reduced vertices

Actual polynomial finite jets lift original ideal members. Degree-first ordering
then produces genuine original monic vertex witnesses, whose original Taylor
convergence internally supplies all radii for actual reduced-vertex convergence.
Blueprint: `hironaka-actual-original-vertex-convergence-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualOriginalVertexConvergence
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalIdealContraction
  HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualReducedBasisDivision HironakaActualMultilinearTaylorCoordinates
  HironakaActualMonomialDivisionBounds HironakaActualVertexSmallRadius
  HironakaActualAnalyticVertexPerturbation HironakaActualReducedFormalStandardBasis
  HironakaActualPolydiscHolomorphicEvaluation
variable {n : ℕ}

/-- Actual ideal members lift every finite jet of their unchanged whole formal extension. -/
theorem exists_original_ideal_finite_jet_lift
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.map (originalTaylorAlgHom n).toRingHom J) (q : ℕ) :
    ∃ g ∈ J,∀ a : Fin n →₀ ℕ,a.degree < q →
      MvPowerSeries.coeff a (originalTaylorAlgHom n g)=MvPowerSeries.coeff a F := by
  let Q := genuineFormalVariables n ^ q
  let ψ := (Ideal.Quotient.mk Q).comp (originalTaylorAlgHom n).toRingHom
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨G,rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨originalPolynomialEval n (MvPowerSeries.truncTotal q G),?_⟩
    change Ideal.Quotient.mk Q (originalTaylorAlgHom n
      (originalPolynomialEval n (MvPowerSeries.truncTotal q G)))=Ideal.Quotient.mk Q G
    apply Ideal.Quotient.eq.mpr
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
    intro a ha
    rw [map_sub]
    change MvPowerSeries.coeff a (originalTaylorAlgHom n
      (originalPolynomialEval n (MvPowerSeries.truncTotal q G)))-MvPowerSeries.coeff a G=0
    rw [originalTaylorAlgHom_polynomialEval,MvPolynomial.coeff_coe,
      MvPowerSeries.coeff_truncTotal G (by rwa [Finsupp.degree_eq_sum]),sub_self]
  have hmem : Ideal.Quotient.mk Q F ∈ Ideal.map ψ J := by
    rw [show Ideal.map ψ J=Ideal.map (Ideal.Quotient.mk Q)
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) from (Ideal.map_map _ _).symm]
    exact Ideal.mem_map_of_mem _ hF
  obtain ⟨g,hg,he⟩ := (Ideal.mem_map_iff_of_surjective ψ hψ).mp hmem
  have hdiff : originalTaylorAlgHom n g-F ∈ genuineFormalVariables n ^ q :=
    Ideal.Quotient.eq.mp he
  refine ⟨g,hg,?_⟩
  intro a ha
  have hzero := (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hdiff a
    (by simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using ha)
  simpa only [map_sub,sub_eq_zero] using hzero

/-- The actual whole formal extension internally supplies monic ORIGINAL germ witnesses at all its vertices. -/
theorem exists_original_monic_vertex_family (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    ∃ B : ActualMonicVertexFamily (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J),
      ∀ a,∃ g ∈ J,originalTaylorAlgHom n g=B.series a := by
  let I := Ideal.map (originalTaylorAlgHom n).toRingHom J
  have hw (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) :
      ∃ g ∈ J,MvPowerSeries.coeff a.val (originalTaylorAlgHom n g)=1 ∧
        ∀ b : Fin n →₀ ℕ,(MonomialOrder.degLex (σ := Fin n)).toSyn b <
          (MonomialOrder.degLex (σ := Fin n)).toSyn a.val →
          MvPowerSeries.coeff b (originalTaylorAlgHom n g)=0 := by
    obtain ⟨F,hF,hne,he,hmonic⟩ := exists_actual_monic_vertex_series
      (MonomialOrder.degLex (σ := Fin n)) I a.val a.property
    obtain ⟨g,hg,hjet⟩ := exists_original_ideal_finite_jet_lift J F hF (a.val.degree+1)
    refine ⟨g,hg,(hjet a.val (Nat.lt_succ_self _)).trans hmonic,?_⟩
    intro b hb
    have hdeg : b.degree≤a.val.degree := by
      have h := (Finsupp.DegLex.lt_iff).mp ((MonomialOrder.degLex_lt_iff).mp hb)
      rcases h with h | h
      · exact h.le
      · exact h.1.le
    rw [hjet b (Nat.lt_succ_of_le hdeg)]
    exact coeff_eq_zero_of_lt_actualInitialExponent _ F hne b (he.symm ▸ hb)
  choose G hG hmonic hlower using hw
  refine ⟨{ series := fun a => originalTaylorAlgHom n (G a)
            mem := fun a => Ideal.mem_map_of_mem _ (hG a)
            monic := hmonic
            lower := hlower },?_⟩
  intro a
  exact ⟨G a,hG a,rfl⟩

/-- All original Taylor series in any finite original germ family converge at ONE internally produced positive radius. -/
theorem exists_finite_originalTaylor_common_mass {ι : Type} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (0+n))) :
    ∃ r : ℝ,0 < r ∧ ∀ i,HasFiniteCoefficientMass (fun _ : Fin n => r)
      (originalTaylorAlgHom n (G i)) := by
  have hfin (s : Finset ι) : ∃ r : ℝ,0 < r ∧ ∀ i ∈ s,
      HasFiniteCoefficientMass (fun _ : Fin n => r) (originalTaylorAlgHom n (G i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,one_pos,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r,hr,hG⟩ := ih
      obtain ⟨t,ht,hT⟩ := exists_originalTaylor_finiteMass n (G i)
      refine ⟨min r t,lt_min hr ht,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact finiteCoefficientMass_mono _ _ (fun _ => lt_min hr ht)
          (fun _ => min_le_right r t) _ hT
      · exact finiteCoefficientMass_mono _ _ (fun _ => lt_min hr ht)
          (fun _ => min_le_left r t) _ (hG j hj)
  obtain ⟨r,hr,hG⟩ := hfin Finset.univ
  exact ⟨r,hr,fun i => hG i (Finset.mem_univ i)⟩

private theorem monomial_finite_mass (ρ : Fin n → ℝ) (a : Fin n →₀ ℕ) (c : ℂ) :
    HasFiniteCoefficientMass ρ (MvPowerSeries.monomial a c) := by
  apply summable_of_ne_finset_zero (s := {a})
  intro b hb
  have hba : b≠a := by simpa only [Finset.mem_singleton] using hb
  simp [MvPowerSeries.coeff_monomial,hba]

/-- Original ideal data ALONE produce actual convergence and holomorphy of every canonical reduced vertex. -/
theorem exists_original_reduced_vertices_finite_mass
    (J : Ideal (HolGerm (ComplexModel (0+n)))) :
    ∃ ρ : Fin n → ℝ,(∀ i,0 < ρ i) ∧
      ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J),
        HasFiniteCoefficientMass ρ (actualReducedVertexSeries (MonomialOrder.degLex (σ := Fin n))
          (Ideal.map (originalTaylorAlgHom n).toRingHom J) a) ∧
        DifferentiableOn ℂ (actualSeriesEvaluation (actualReducedVertexSeries
          (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J) a))
          (HironakaActualPolydiscHolomorphicEvaluation.openPolydisc ρ) := by
  obtain ⟨B,hw⟩ := exists_original_monic_vertex_family J
  choose G hGI hG using hw
  obtain ⟨r,hr,hM⟩ := exists_finite_originalTaylor_common_mass G
  have hTail (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      HasFiniteCoefficientMass (fun _ : Fin n => r) (B.series a-MvPowerSeries.monomial a.val 1) := by
    have hm : HasFiniteCoefficientMass (fun _ : Fin n => r) (-MvPowerSeries.monomial a.val (1 : ℂ)) := by
      simpa only [HasFiniteCoefficientMass,map_neg,norm_neg] using
        monomial_finite_mass (fun _ : Fin n => r) a.val (1 : ℂ)
    rw [←hG a,sub_eq_add_neg]
    exact finiteCoefficientMass_add _ (fun _ => hr) _ _ (hM a) hm
  obtain ⟨ρ,hρ,_hle,hMass⟩ := exists_actual_reduced_vertices_finite_mass
    (Ideal.map (originalTaylorAlgHom n).toRingHom J) B (fun _ => r) (fun _ => hr) hTail
  exact ⟨ρ,hρ,fun a => ⟨hMass a,evaluation_differentiableOn ρ _ (hMass a)⟩⟩

end
end Hironaka.HironakaActualOriginalVertexConvergence
