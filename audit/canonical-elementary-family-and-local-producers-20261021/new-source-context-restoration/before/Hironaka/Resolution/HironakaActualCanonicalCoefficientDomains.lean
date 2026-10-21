/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCanonicalNormalCoefficientData
/-!
# The SAME canonical coefficient functions on genuine finite support domains

True original coefficient-germ identities give a finite family of actual
neighbourhood conditions. Their genuine finite intersection and a real open
shrink produce literal coefficient FUNCTION identities at every basepoint,
while preserving all original generators and coefficient functions exactly.
The original HS-constant centre endpoint fixes ONE actual flattening and
ONE exact canonical datum before EVERY finite cutoff and its open shrink.
No common domain for infinitely many cutoffs or transformed HS persistence
criterion is asserted.

Blueprint: `hironaka-actual-canonical-coefficient-domains-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCanonicalCoefficientDomains
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualOriginalFormalTaylor HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualAnalyticVertexCoefficientData
  HironakaActualCoefficientPresentationCentrePower HironakaActualFiniteCoefficientIdeals
  HironakaActualFormalCoordinatePowerDivision HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualCanonicalNormalCoefficientData
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
variable {d t : ℕ}
local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

/-- A genuine common open for EVERY bounded-degree diagram label of the SAME actual coefficient functions. -/
theorem exists_finite_diagram_support_shrink
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : ActualAnalyticVertexCoefficientData d 0 t I)
    (hs : ∀ a γ,actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        HolGerm.mk (P.coefficient a γ) (P.holomorphic a γ)=
          HolGerm.constHom (if γ=actualNormalExponent a.val then (1 : ℂ) else 0)) (q : ℕ) :
    ∃ Q : ActualAnalyticVertexCoefficientData d 0 t I,
      Q.generator=P.generator ∧ Q.coefficient=P.coefficient ∧ Q.domain⊆P.domain ∧
      ∀ a γ,normalExponentDegree γ<q →
        actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        ∀ z∈Q.domain,Q.coefficient a γ z=if γ=actualNormalExponent a.val then (1 : ℂ) else 0 := by
  let V := actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
  have he (i : V × normalExponentIndex t q) :
      ∀ᶠ z in 𝓝 (0 : ComplexModel (d+0)),
        actualJoinedExponent (0 : Fin d →₀ ℕ) i.2.val∈actualInitialDiagram MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
        P.coefficient i.1 i.2.val z=if i.2.val=actualNormalExponent i.1.val then (1 : ℂ) else 0 := by
    by_cases hΓ : actualJoinedExponent (0 : Fin d →₀ ℕ) i.2.val∈actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
    · have hg := hs i.1 i.2.val hΓ
      rw [HolGerm.constHom_apply] at hg
      exact (HolGerm.mk_eq_mk_iff.mp hg).mono fun z hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hΓ h)
  obtain ⟨U,hUf,hU,h0⟩ := eventually_nhds_iff.mp (eventually_all.mpr he)
  let W := U∩P.domain
  have hW : IsOpen W := hU.inter P.isOpen_domain
  have h0W : (0 : ComplexModel (d+0))∈W := ⟨h0,P.zero_mem_domain⟩
  have hWP : W⊆P.domain := inter_subset_right
  let Q : ActualAnalyticVertexCoefficientData d 0 t I := { P with
    domain := W
    isOpen_domain := hW
    zero_mem_domain := h0W
    regular := fun a γ hγ => (P.regular a γ hγ).mono hWP
    coherent := fun a γ hγ => coherentOn_actualPrincipalCoefficientIdeal (d+0) (P.coefficient a γ)
      W hW ((P.regular a γ hγ).mono hWP) }
  refine ⟨Q,rfl,rfl,hWP,?_⟩
  intro a γ hγ hΓ z hz
  change z∈U∩P.domain at hz
  exact hUf z hz.1 (a,⟨γ,hγ⟩) hΓ

section OriginalCentre
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original geometry fixes ONE exact canonical family before EVERY finite actual common-support domain. -/
theorem exists_original_hs_constant_centre_finite_support_domains
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex K0 a) ∧
        (∀ a,P.generator a∈normalIdeal d t ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
        ∀ q : ℕ,∃ Q : ActualAnalyticVertexCoefficientData d 0 t I0,
          Q.generator=P.generator ∧ Q.coefficient=P.coefficient ∧ Q.domain⊆P.domain ∧
          ∀ a γ,normalExponentDegree γ<q →
            actualJoinedExponent (0 : Fin d →₀ ℕ) γ∈actualInitialDiagram MonomialOrder.degLex K0 →
            ∀ z∈Q.domain,Q.coefficient a γ z=if γ=actualNormalExponent a.val then (1 : ℂ) else 0 := by
  obtain ⟨Φ,hsrc,h0,hflat,P,hP,hcoeff,hpow⟩ :=
    exists_original_hs_constant_centre_canonical_coefficient_data C x hreg A hA hhs
  exact ⟨Φ,hsrc,h0,hflat,P,hP,hpow,fun q => exists_finite_diagram_support_shrink _ P hcoeff q⟩

end OriginalCentre
end
end Hironaka.HironakaActualCanonicalCoefficientDomains
