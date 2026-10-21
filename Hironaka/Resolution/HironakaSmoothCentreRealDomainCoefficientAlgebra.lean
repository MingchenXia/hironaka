/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainNearbyInitialKernel
import Hironaka.Resolution.HironakaRelativeNormalCoefficientFunctionAlgebra

/-! # Actual common coefficient domains from original real-centre input
Complete three-node mathematics precedes code. Nearby maps are actual function
translations on real coefficient domains. No global flattened-model coherence,
arbitrary origin-germ map or caller family/kernel/domain certificate is used.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainCoefficientAlgebra
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainNearbyInitialKernel
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalDeformationFiniteRelationsSpread
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalCoefficientFunctionAlgebra
attribute [local instance] coefficientSubalgebraRing
attribute [local instance] MvPolynomial.gradedAlgebra
private theorem real_map_span_range {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Q : ι → R) :
    Ideal.map f (Ideal.span (range Q)) = Ideal.span (range (fun i => f (Q i))) := by
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Q i, ⟨i, rfl⟩, rfl⟩


section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original-only inputs supply actual coefficient functions presenting every WHOLE original nearby initial ideal. -/
theorem exists_original_regular_real_coefficient_algebra_initial_family
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
        (∀ a ∈ B, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        ∃ Q : ↥(actualOriginalRelationFamily d t F) →
          MvPolynomial (Fin t) (coefficientFunctionAlgebra d B),
          (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
          (∀ P, MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (Q P) = P.val) ∧
          Ideal.map (MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal F) ∧
          ∀ a (ha : a ∈ B),
            Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom)
              (Ideal.span (range Q)) = originalNormalInitialIdeal d t
                (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0,hflat,_N,_U,V,_hU,_h0U,_hUV,_hcol,_hchain,_hsat,_hV,_h0V,_hVsub,
    _hcent,_hcoeff,_hpoly,_hdegree,_hfg,_hcentral,hB,h0B,hpoint,hc,hmodels⟩ :=
    exists_original_regular_real_all_nearby_initial_polynomial_kernels C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let B := (tangentInclusion d t) ⁻¹' V
  let Q := fun P : ↥(actualOriginalRelationFamily d t F) =>
    coefficientPolynomialLift d t B P.val (fun α a ha => hc a ha P α)
  have hQ0 (P : ↥(actualOriginalRelationFamily d t F)) :
      MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom (Q P) = P.val :=
    coefficientPolynomialLift_origin d t B P.val (fun α a ha => hc a ha P α) h0B
  refine ⟨Φ,hsrc,h0,hflat,B,hB,h0B,hpoint,Q,?_,hQ0,?_,?_⟩
  · intro P
    obtain ⟨q,hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t
      (originalCoherentOriginIdeal F) P.val P.property
    exact ⟨q,coefficientPolynomialLift_homogeneous d t B P.val _ hq⟩
  · rw [real_map_span_range (MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t F) => P.val := funext hQ0
    rw [he]
    have hr : range (fun P : ↥(actualOriginalRelationFamily d t F) => P.val) =
        (actualOriginalRelationFamily d t F : Set _) := by
      ext P
      exact ⟨fun ⟨Q,hQ⟩ => hQ ▸ Q.property,fun hP => ⟨⟨P,hP⟩,rfl⟩⟩
    rw [hr]
    exact (actualOriginalHomogeneousRelations_spec d t (originalCoherentOriginIdeal F)).2.symm
  · intro a ha
    rw [real_map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t F) =>
          actualNearbyCoefficientPolynomial d t P.val a (hc a ha P) := by
      funext P
      exact coefficientPolynomialLift_nearby d t B P.val _ a ha
    rw [he]
    obtain ⟨_,_,_,_,_,hinit,_,_,_,_⟩ := hmodels a ha
    exact hinit.symm

/-- Original-only geometry/coherence supplies a finite type ACTUAL coefficient subalgebra for all whole nearby ideals. -/
theorem exists_original_regular_real_finiteType_coefficient_initial_family
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
        (∀ a ∈ B, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        ∃ C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B), Algebra.FiniteType ℂ C0 ∧
        ∃ Q : ↥(actualOriginalRelationFamily d t F) → MvPolynomial (Fin t) C0,
          (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
          Ideal.map (MvPolynomial.map ((coefficientGermHom d B 0 h0).comp C0.val).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal F) ∧
          ∀ a (ha : a ∈ B),
            Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom)
              (Ideal.span (range Q)) = originalNormalInitialIdeal d t
                (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) := by
  classical
  obtain ⟨Φ,hsrc,h0,hflat,B,hB,h0B,hpoint,Q,hhom,_hQ0,horigin,hnearby⟩ :=
    exists_original_regular_real_coefficient_algebra_initial_family C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let Ps : Finset (MvPolynomial (Fin t) (coefficientFunctionAlgebra d B)) := Finset.univ.image Q
  have hPs (P : ↥(actualOriginalRelationFamily d t F)) : Q P ∈ Ps :=
    Finset.mem_image.mpr ⟨P,Finset.mem_univ _,rfl⟩
  let C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B) := finitePolynomialCoefficientAlgebra Ps
  let L : ↥(actualOriginalRelationFamily d t F) → MvPolynomial (Fin t) C0 :=
    fun P => finiteCoefficientPolynomialLift Ps (Q P) (hPs P)
  have hL (a : ComplexModel d) (ha : a ∈ B) (P : ↥(actualOriginalRelationFamily d t F)) :
      MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom (L P) =
        MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P) := by
    rw [← finiteCoefficientPolynomialLift_map Ps (Q P) (hPs P)]
    rw [MvPolynomial.map_map]
    rfl
  have himage (a : ComplexModel d) (ha : a ∈ B) :
      Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom)
        (Ideal.span (range L)) =
      Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) (Ideal.span (range Q)) := by
    let : CommRing C0 := C0.toCommRing
    rw [real_map_span_range (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom) L,
      real_map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    exact congrArg (fun F => Ideal.span (range F)) (funext (hL a ha))
  refine ⟨Φ,hsrc,h0,hflat,B,hB,h0B,hpoint,C0,finitePolynomialCoefficientAlgebra_finiteType Ps,L,?_,?_,?_⟩
  · intro P
    obtain ⟨q,hq⟩ := hhom P
    exact ⟨q,finiteCoefficientPolynomialLift_homogeneous Ps (Q P) (hPs P) hq⟩
  · exact (himage 0 h0B).trans horigin
  · exact fun a ha => (himage a ha).trans (hnearby a ha)

/-- A common genuine quotient DOMAIN, with real function factorisations, presents every ENTIRE original nearby initial ideal. -/
theorem exists_original_regular_real_common_domain_initial_family
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
        (∀ a ∈ B, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        ∃ C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B), Algebra.FiniteType ℂ C0 ∧
          IsDomain (coefficientOriginAlgebra d B h0 C0) ∧
          Algebra.FiniteType ℂ (coefficientOriginAlgebra d B h0 C0) ∧
        ∃ W : Set (ComplexModel d), IsOpen W ∧ (0 : ComplexModel d) ∈ W ∧
        ∃ hWB : W ⊆ B,
        ∃ ρ : ∀ a : ComplexModel d, a ∈ W →
          coefficientOriginAlgebra d B h0 C0 →ₐ[ℂ] HolGerm (ComplexModel d),
        ∃ Q : ↥(actualOriginalRelationFamily d t F) →
          MvPolynomial (Fin t) (coefficientOriginAlgebra d B h0 C0),
          (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
          (∀ a (ha : a ∈ W),
            (ρ a ha).comp (Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C0)) =
              (coefficientGermHom d B a (hWB ha)).comp C0.val) ∧
          ∀ a (ha : a ∈ W), Ideal.map (MvPolynomial.map (ρ a ha).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t
              (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) := by
  classical
  obtain ⟨Φ,hsrc,h0,hflat,B,hB,h0B,hpoint,C0,hC,L,hhom,_horigin,hnearby⟩ :=
    exists_original_regular_real_finiteType_coefficient_initial_family C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  let : Algebra.FiniteType ℂ C0 := hC
  let : IsNoetherianRing C0 := Algebra.FiniteType.isNoetherianRing ℂ C0
  obtain ⟨W,hW,h0W,hWB,ρ,hρ⟩ := exists_common_coefficient_origin_quotient_homs d B hB h0B C0
  let q := Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0B C0)
  let Q := fun P => MvPolynomial.map q.toRingHom (L P)
  refine ⟨Φ,hsrc,h0,hflat,B,hB,h0B,hpoint,C0,hC,coefficientOriginAlgebra_isDomain d B h0B C0,
    coefficientOriginAlgebra_finiteType d B h0B C0,W,hW,h0W,hWB,ρ,Q,?_,hρ,?_⟩
  · intro P
    obtain ⟨k,hk⟩ := hhom P
    exact ⟨k,hk.map q.toRingHom⟩
  · intro a ha
    have hmap (P : ↥(actualOriginalRelationFamily d t F)) :
        MvPolynomial.map (ρ a ha).toRingHom (Q P) =
          MvPolynomial.map ((coefficientGermHom d B a (hWB ha)).comp C0.val).toRingHom (L P) := by
      change MvPolynomial.map (ρ a ha).toRingHom (MvPolynomial.map q.toRingHom (L P)) = _
      rw [MvPolynomial.map_map]
      change MvPolynomial.map ((ρ a ha).comp q).toRingHom (L P) = _
      exact congrArg (fun f : C0 →ₐ[ℂ] HolGerm (ComplexModel d) =>
        MvPolynomial.map f.toRingHom (L P)) (hρ a ha)
    rw [real_map_span_range (MvPolynomial.map (ρ a ha).toRingHom) Q]
    apply Eq.trans (congrArg
      (fun F : ↥(actualOriginalRelationFamily d t F) → MvPolynomial (Fin t) (HolGerm (ComplexModel d)) =>
        Ideal.span (range F)) (funext hmap))
    exact (real_map_span_range
      (MvPolynomial.map ((coefficientGermHom d B a (hWB ha)).comp C0.val).toRingHom) L).symm.trans
      (hnearby a (hWB ha))

end Original

end
end Hironaka.HironakaSmoothCentreRealDomainCoefficientAlgebra
