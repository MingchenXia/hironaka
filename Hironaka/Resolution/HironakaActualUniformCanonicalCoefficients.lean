/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCanonicalNormalCoefficientData
import Hironaka.Resolution.HironakaActualRelativeCoefficientMassSlicing

/-!
# All canonical coefficient functions on one actual original base polydisc

Actual finite original canonical generators supply one common full mass radius.
Every relative slice evaluates holomorphically on its SAME base polydisc; genuine
inverse Taylor realization gives the exact original coefficient germs. On all
whole-diagram labels formal reducedness gives constant FUNCTIONS simultaneously.
Blueprint: `hironaka-actual-uniform-canonical-coefficients-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualUniformCanonicalCoefficients
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaActualOriginalFormalTaylor HironakaActualCoefficientPresentationCentrePower
  HironakaActualMultilinearTaylorCoordinates HironakaActualOriginalVertexConvergence
  HironakaActualConvergentTaylorRealization HironakaActualCanonicalNormalCoefficientData
  HironakaActualRelativeCoefficientMassSlicing HironakaActualAnalyticVertexCoefficientData
  HironakaActualFiniteCoefficientIdeals HironakaActualFormalInitialDiagram
  HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualPureNormalVertices
  HironakaActualMonomialDivisionBounds HironakaActualPolydiscHolomorphicEvaluation
  HironakaActualAnalyticFormalNormalPowers HironakaActualCoupledNormalFreeness
  HironakaActualStandardNormalIndependence HironakaActualHomogeneousInitialHS
  HironakaRelativeNormalIdeal HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
variable {d t : ℕ}

private theorem unshifted_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem common_unshifted_mass (n : ℕ) {ι : Type} [Fintype ι]
    (G : ι → HolGerm (ComplexModel n)) :
    ∃ r : ℝ,0<r ∧ ∀ i,HasFiniteCoefficientMass (fun _ : Fin n => r)
      (actualUnshiftedTaylorAlgHom n (G i)) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) :=
    ∀ G : ι → HolGerm (ComplexModel m),∃ r : ℝ,0<r ∧
      ∀ i,HasFiniteCoefficientMass (fun _ : Fin n => r) (f (G i))
  have h : P (0+n) (originalTaylorAlgHom n) := fun G => exists_finite_originalTaylor_common_mass G
  exact unshifted_property n P h G

private theorem unshifted_evaluation_taylor (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ i,0<ρ i)
    (F : MvPowerSeries (Fin n) ℂ) (hF : HasFiniteCoefficientMass ρ F) :
    ∃ hf : HolAt (fun z : ComplexModel n => actualSeriesEvaluation F (fun i : Fin n => z i)) 0,
      actualUnshiftedTaylorAlgHom n (HolGerm.mk
        (fun z : ComplexModel n => actualSeriesEvaluation F (fun i : Fin n => z i)) hf)=F := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) :=
    ∀ e : m=n,∃ hf : HolAt (fun z : ComplexModel m =>
      actualSeriesEvaluation F (fun i : Fin n => z (Fin.cast e.symm i))) 0,
      f (HolGerm.mk (fun z : ComplexModel m =>
        actualSeriesEvaluation F (fun i : Fin n => z (Fin.cast e.symm i))) hf)=F
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro e
    have he : (fun z : ComplexModel (0+n) =>
        actualSeriesEvaluation F (fun i : Fin n => z (Fin.cast e.symm i)))=evaluationFunction F := by
      funext z
      change actualSeriesEvaluation F (fun i : Fin n => z (Fin.cast e.symm i))=
        actualSeriesEvaluation F (fun i : Fin n => z (i.natAdd 0))
      congr 1
      funext i
      have hi : Fin.cast e.symm i=i.natAdd 0 := by
        apply Fin.ext
        simp
      rw [hi]
    have hf : HolAt (fun z : ComplexModel (0+n) =>
        actualSeriesEvaluation F (fun i : Fin n => z (Fin.cast e.symm i))) 0 := by
      rw [he]
      exact evaluationFunction_holomorphic ρ hρ F hF
    refine ⟨hf,?_⟩
    simpa only [he,evaluationGerm] using originalTaylor_evaluationGerm ρ hρ F hF
  simpa only [Fin.cast_refl,id_eq] using unshifted_property n P h rfl

private theorem evaluation_constant (n : ℕ) (c : ℂ) (z : Fin n → ℂ) :
    actualSeriesEvaluation (MvPowerSeries.C c) z=c := by
  unfold actualSeriesEvaluation
  simp [MvPowerSeries.coeff_C]

/-- All coefficient functions of ONE exact canonical original datum are holomorphic on ONE actual domain. -/
theorem exists_uniform_canonical_coefficient_data (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I,
      (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a) ∧
      (∀ a γ,MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (P.coefficient a γ) P.domain) ∧
      ∀ a γ (u : ComplexModel d),P.coefficient a γ u=
        actualNormalCoefficientEvaluation (actualUnshiftedTaylorAlgHom (d+t) (P.generator a)) γ u := by
  obtain ⟨P₀,hP₀⟩ := exists_canonical_reduced_coefficient_data d 0 t I
  obtain ⟨r,hr,hMass⟩ := common_unshifted_mass (d+t) P₀.generator
  let ρ : Fin (d+t) → ℝ := fun _ => r
  let U := actualBaseOpenPolydisc (d := d) (t := t) ρ
  let c := fun a γ => actualNormalCoefficientEvaluation
    (actualUnshiftedTaylorAlgHom (d+t) (P₀.generator a)) γ
  have hDomain (a) := normalCoefficient_evaluations_common_domain ρ (fun _ => hr)
    (actualUnshiftedTaylorAlgHom (d+t) (P₀.generator a)) (hMass a)
  have hU : IsOpen U := by
    change IsOpen (actualBaseOpenPolydisc ρ)
    have hzero : HasFiniteCoefficientMass ρ (0 : MvPowerSeries (Fin (d+t)) ℂ) := by
      simp [HasFiniteCoefficientMass]
    exact (normalCoefficient_evaluations_common_domain ρ (fun _ => hr) 0 hzero).1
  have h0 : (0 : ComplexModel d)∈U := by
    change (0 : ComplexModel d)∈actualBaseOpenPolydisc ρ
    change ∀ i : Fin d,‖((EuclideanSpace.equiv (Fin d) ℂ) (0 : ComplexModel d)) i‖<ρ (i.castAdd t)
    simpa only [map_zero,Pi.zero_apply,norm_zero] using fun _ : Fin d => hr
  have hc (a) (γ : Fin t →₀ ℕ) : HolAt (c a γ) 0 :=
    normalCoefficient_evaluation_holomorphicAt_zero ρ (fun _ => hr) _ (hMass a) γ
  have hreg (a) (γ : Fin t →₀ ℕ) : MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (c a γ) U :=
    ((hDomain a).2.2 γ).2.1
  have hTaylor (a) (γ : Fin t →₀ ℕ) :
      actualFormalNormalCoefficient (actualUnshiftedTaylorAlgHom (d+t) (P₀.generator a)) γ=
        actualUnshiftedTaylorAlgHom d (HolGerm.mk (c a γ) (hc a γ)) := by
    obtain ⟨hfun,he⟩ := unshifted_evaluation_taylor d (baseRadius ρ)
      (fun i => hr) _ (normalCoefficient_hasFiniteCoefficientMass ρ (fun _ => hr) _ (hMass a) γ)
    exact he.symm
  let P : ActualAnalyticVertexCoefficientData d 0 t I := {
    P₀ with
    domain := U
    isOpen_domain := hU
    zero_mem_domain := h0
    coefficient := c
    holomorphic := hc
    regular := fun a γ _ => hreg a γ
    coherent := fun a γ _ => coherentOn_actualPrincipalCoefficientIdeal d (c a γ) U hU (hreg a γ)
    coefficient_member := fun a γ _ => mem_actualPrincipalCoefficientIdeal d (c a γ) U hU (hreg a γ) 0 h0
    coefficient_eq := hTaylor }
  exact ⟨P,hP₀,hreg,fun _ _ _ => rfl⟩

/-- Whole-diagram zero/one identities hold as actual FUNCTIONS simultaneously on the SAME produced domain. -/
theorem exists_uniform_canonical_diagram_data (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F∈actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F∈actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)) :
    ∃ P : ActualAnalyticVertexCoefficientData d 0 t I,
      (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a) ∧
      (∀ a γ,MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (P.coefficient a γ) P.domain) ∧
      ∀ a γ,actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        ∀ u∈P.domain,P.coefficient a γ u=if γ=actualNormalExponent a.val then (1 : ℂ) else 0 := by
  obtain ⟨P,hP,hhol,hEval⟩ := exists_uniform_canonical_coefficient_data I
  refine ⟨P,hP,hhol,?_⟩
  intro a γ hγ u _hu
  rw [hEval]
  unfold actualNormalCoefficientEvaluation
  rw [hP a,normalCoefficient_reduced_vertex_of_pure_normal MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a
    (tangentExponent_vertex_zero_of_initial_tangent_pderiv d t _ hD a) γ hγ]
  exact evaluation_constant d _ _

section OriginalCentre
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original HSconstant geometry produces ONE canonical datum with all true coefficient FUNCTION identities and whole powers. -/
theorem exists_original_hs_centre_uniform_canonical_data
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M},y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex K0 a) ∧
        (∀ a γ,MDifferentiableOn 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ℂ) (P.coefficient a γ) P.domain) ∧
        (∀ a γ,actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex K0 →
          ∀ u∈P.domain,P.coefficient a γ u=if γ=actualNormalExponent a.val then (1 : ℂ) else 0) ∧
        ∀ a,P.generator a∈normalIdeal d t ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  obtain ⟨Φ,hsrc,h0,hflat,hfree,hD,_hDP,_hExt⟩ :=
    exists_original_hs_constant_centre_coupled_normal_data C x hreg A hA hhs
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) 0)
  obtain ⟨P,hP,hhol,hcoeff⟩ := exists_uniform_canonical_diagram_data I0 hD
  have hV := actual_reduced_vertices_mem_normal_powers_of_normal_free_and_initial_stable d t I0
    (fun q => (hfree q).2) hD
  refine ⟨Φ,hsrc,h0,hflat,P,hP,hhol,hcoeff,?_⟩
  intro a
  apply (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t _ (P.generator a)).mpr
  rw [hP]
  exact hV a

end OriginalCentre
end
end Hironaka.HironakaActualUniformCanonicalCoefficients
