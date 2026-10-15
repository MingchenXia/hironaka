/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalDeformationInitialRelations
import Hironaka.Resolution.HironakaRelativeNormalAnalyticCoefficients

/-!
# Actual finite original initial relations in nearby entire central stalks

Only the original coherent ideal sheaf and d,t are original consumer inputs.
The selected original finite homogeneous relation family is internal; the
whole image of its entire initial ideal is exactly the span of its genuine
analytic evaluations. Actual whole ambient holomorphic representatives share
ONE open; their true finite functional span has an entire origin dictionary.
Actual coherent inclusion spreading places this WHOLE finite source model in
EVERY actual central stalk on ONE genuine neighborhood. Intersecting with the
actual central map preimage retains the SAME original equation saturation index
and the literal all-power/whole-union dictionaries at every actual central image.

No source family/index/open/generator/kernel/flatness/result certificate is an
original input. The finite origin model is NOT identified with WHOLE nearby
ORIGINAL initial ideals. Reverse central/Rees/graded dictionaries, nearby all-
degree freeness, analytic normal-flatness, higher HS and G8 remain OPEN.
Mathematics.tex preceded the first substantive Lean. This own offlib checkpoint
awaits formal write-set registration and native target build.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HironakaRelativeNormalDeformationFiniteRelationsSpread
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticCoefficients

def actualOriginalRelationFamily (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    Finset (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :=
  actualOriginalHomogeneousRelations d t (originalCoherentOriginIdeal I)

def actualInitialAnalyticIdeal (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  let := tangentAlgebra d t
  Ideal.map (normalPolynomialEval d t).toRingHom
    (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))

def actualOriginalRelationEvaluations (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    Finset (HolGerm (ComplexModel (d+t))) := by
  classical
  exact (actualOriginalRelationFamily d t I).image (normalPolynomialEval d t)

theorem actualInitialAnalyticIdeal_eq_span_evaluations (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    actualInitialAnalyticIdeal d t I = Ideal.span (actualOriginalRelationEvaluations d t I : Set _) := by
  classical
  let := tangentAlgebra d t
  unfold actualInitialAnalyticIdeal actualOriginalRelationEvaluations actualOriginalRelationFamily
  rw [(actualOriginalHomogeneousRelations_spec d t (originalCoherentOriginIdeal I)).2,Ideal.map_span]
  rw [Finset.coe_image]
  rfl

def actualRelationFunction (d t : ℕ) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    ComplexModel (d+t) → ℂ :=
  actualCoefficientRepresentative (normalPolynomialEval d t P)

theorem actualRelationFunction_holomorphic (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    HolAt (actualRelationFunction d t P) 0 :=
  actualCoefficientRepresentative_holomorphic (normalPolynomialEval d t P)

theorem actualRelationFunction_whole_germ (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    HolGerm.mk (actualRelationFunction d t P) (actualRelationFunction_holomorphic d t P) =
      normalPolynomialEval d t P := by
  apply Subtype.ext
  exact actualCoefficientRepresentative_germ (normalPolynomialEval d t P)

def actualFiniteRelationSpan (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (y : ComplexModel (d+t)) (g : ComplexModel (d+t) → ℂ) : Prop :=
  InSpanAt (fun P : ↥(actualOriginalRelationFamily d t I) => actualRelationFunction d t P.val) y g

theorem actualFiniteRelationSpan_origin_dictionary (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) {g : ComplexModel (d+t) → ℂ} (hg : HolAt g 0) :
    actualFiniteRelationSpan d t I 0 g ↔ HolGerm.mk g hg ∈ actualInitialAnalyticIdeal d t I := by
  classical
  unfold actualFiniteRelationSpan
  rw [inSpanAt_zero_iff_mem_origin_span
    (fun P : ↥(actualOriginalRelationFamily d t I) => actualRelationFunction d t P.val)
    (fun P : ↥(actualOriginalRelationFamily d t I) => actualRelationFunction_holomorphic d t P.val) hg,
    actualInitialAnalyticIdeal_eq_span_evaluations]
  simp only [actualRelationFunction_whole_germ]
  have he : range (fun P : ↥(actualOriginalRelationFamily d t I) => normalPolynomialEval d t P.val) =
      (actualOriginalRelationEvaluations d t I : Set _) := by
    ext h
    constructor
    · rintro ⟨P,rfl⟩
      exact Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩
    · intro hh
      obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hh
      exact ⟨⟨P,hP⟩,rfl⟩
  rw [he]

theorem exists_actual_finite_relation_holomorphic_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    ∃ A : Set (ComplexModel (d+t)), IsOpen A ∧ 0 ∈ A ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ A, HolAt (actualRelationFunction d t P) y) ∧
      ∀ y ∈ A, IdealFGAt (actualFiniteRelationSpan d t I) y := by
  classical
  obtain ⟨A,hA,h0A,hhol⟩ := exists_common_coefficient_open (actualOriginalRelationEvaluations d t I)
  have hdiff : ∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ A,
      DifferentiableAt ℂ (actualRelationFunction d t P) y := by
    intro P hP y hy
    exact hhol (normalPolynomialEval d t P) (Finset.mem_image.mpr ⟨P,hP,rfl⟩) y hy
  refine ⟨A,hA,h0A,?_,?_⟩
  · intro P hP y hy
    have he : ∀ᶠ z in 𝓝 y, z ∈ A := hA.mem_nhds hy
    exact he.mono (fun z hz => hdiff P hP z hz)
  · intro y hy
    exact ⟨A,hA,hy,↥(actualOriginalRelationFamily d t I),inferInstance,
      fun P => actualRelationFunction d t P.val,
      fun P z hz => (hdiff P.val P.property z hz).differentiableWithinAt,
      fun _ _ _ => Iff.rfl⟩

private theorem finite_model_spread (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (N : ℕ)
    (hcent : (originalDeformationCentralIdeal d t I N).IsCoherent)
    (hmap : actualInitialAnalyticIdeal d t I ≤
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N)) :
    ∃ A : Set (ComplexModel (d+t)), IsOpen A ∧ 0 ∈ A ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ A, HolAt (actualRelationFunction d t P) y) ∧
      (∀ y ∈ A, IdealFGAt (actualFiniteRelationSpan d t I) y) ∧
      ∀ y ∈ A, ∀ g, actualFiniteRelationSpan d t I y g →
        (originalDeformationCentralIdeal d t I N).mem y g := by
  obtain ⟨V,hV,h0V,hhol,hfg⟩ := exists_actual_finite_relation_holomorphic_model d t I
  have h0 : ∀ g, actualFiniteRelationSpan d t I 0 g →
      (originalDeformationCentralIdeal d t I N).mem 0 g := by
    intro g hg
    exact (mk_mem_originalCoherentOriginIdeal_iff (originalDeformationCentralIdeal d t I N)
      hcent hg.1).mp (hmap ((actualFiniteRelationSpan_origin_dictionary d t I hg.1).mp hg))
  obtain ⟨W,hW,h0W,hsub⟩ := exists_open_coherent_inclusion (hfg 0 h0V)
    (germIdeal_actual_finitely_generated (originalDeformationCentralIdeal d t I N) hcent) h0
  refine ⟨V ∩ W,hV.inter hW,⟨h0V,h0W⟩,?_,?_,?_⟩
  · exact fun P hP y hy => hhol P hP y hy.1
  · exact fun y hy => hfg y hy.1
  · exact fun y hy g hg => hsub y hy.2 g hg

theorem exists_original_finite_relation_model_and_saturation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
      ∃ A : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧ IsOpen A ∧ 0 ∈ A ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ A, HolAt (actualRelationFunction d t P) y) ∧
      (∀ y ∈ A, IdealFGAt (actualFiniteRelationSpan d t I) y) ∧
      (∀ y ∈ A, ∀ g, actualFiniteRelationSpan d t I y g →
        (originalDeformationCentralIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
        (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0U,_,hcent,hchain,hpow,hsat,hmap⟩ :=
    exists_original_deformation_initial_ideal_inclusion d t I hI
  obtain ⟨A,hA,h0A,hhol,hfg,hsub⟩ := finite_model_spread d t I N hcent hmap
  exact ⟨N,U,A,hU,h0U,hA,h0A,hcent,hhol,hfg,hsub,hchain,hpow,hsat⟩

/-- ONLY the original coherent ideal supplies actual finite-model inclusion and SAME all-power central dictionaries. -/
theorem exists_original_finite_relation_spread (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ V : Set (ComplexModel (d+t)), IsOpen V ∧ 0 ∈ V ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ V, HolAt (actualRelationFunction d t P) y) ∧
      (∀ y ∈ V, IdealFGAt (actualFiniteRelationSpan d t I) y) ∧
      (∀ y ∈ V, ∀ g, actualFiniteRelationSpan d t I y g →
        (originalDeformationCentralIdeal d t I N).mem y g) ∧
      (∀ y ∈ V, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem (deformationCentralInclusion d t y) g ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t y) g) ∧
      (∀ y ∈ V, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g (deformationCentralInclusion d t y) →
        ((originalDeformationIdeal d t I).mem (deformationCentralInclusion d t y)
          (fun z => g z*deformationParameter d t z^q) ↔
        (originalDeformationIdeal d t I).mem (deformationCentralInclusion d t y)
          (fun z => g z*deformationParameter d t z^N))) ∧
      ∀ y ∈ V, ∀ g,
        (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem (deformationCentralInclusion d t y) g) ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t y) g := by
  obtain ⟨N,U,A,hU,h0U,hA,h0A,hcent,hhol,hfg,hsub,hchain,hpow,hsat⟩ :=
    exists_original_finite_relation_model_and_saturation d t I hI
  let V := A ∩ deformationCentralInclusion d t ⁻¹' U
  have hV : IsOpen V := hA.inter (hU.preimage (deformationCentralInclusion d t).continuous)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨h0A,by change deformationCentralInclusion d t 0 ∈ U; simpa only [map_zero] using h0U⟩
  exact ⟨N,V,hV,h0V,hcent,
    (fun P hP y hy => hhol P hP y hy.1),
    (fun y hy => hfg y hy.1),(fun y hy g hg => hsub y hy.1 g hg),
    (fun y hy => hchain _ hy.2),(fun y hy => hpow _ hy.2),(fun y hy => hsat _ hy.2)⟩

end
end Hironaka.HironakaRelativeNormalDeformationFiniteRelationsSpread
