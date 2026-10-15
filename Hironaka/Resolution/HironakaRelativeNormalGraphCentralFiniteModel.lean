/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralIdealEquality
import Hironaka.Resolution.HironakaRelativeNormalDeformationFiniteRelationsSpread

/-! Actual finite coherent presentations spread whole origin equality.
The finite whole representatives are not declared literal normal polynomials. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphCentralFiniteModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalGraphCentralIdealEquality

theorem exists_original_whole_central_finite_model_and_saturation (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
      ∃ A : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧ IsOpen A ∧ 0 ∈ A ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ A, HolAt (actualRelationFunction d t P) y) ∧
      (∀ y ∈ A, IdealFGAt (actualFiniteRelationSpan d t I) y) ∧
      (∀ y ∈ A, ∀ g, actualFiniteRelationSpan d t I y g ↔
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
  obtain ⟨N,U,hU,h0U,_hcol,hcent,hchain,hpow,hsat,heq⟩ :=
    exists_original_coherent_whole_graph_central_ideal_equality d t I hI
  obtain ⟨V,hV,h0V,hhol,hfg⟩ := exists_actual_finite_relation_holomorphic_model d t I
  have hcentFG := germIdeal_actual_finitely_generated (originalDeformationCentralIdeal d t I N) hcent
  have hiff : ∀ g, actualFiniteRelationSpan d t I 0 g ↔
      (originalDeformationCentralIdeal d t I N).mem 0 g := by
    intro g
    constructor
    · intro hg
      have hmem := (actualFiniteRelationSpan_origin_dictionary d t I hg.1).mp hg
      change HolGerm.mk g hg.1 ∈ Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) at hmem
      rw [← heq] at hmem
      exact (mk_mem_originalCoherentOriginIdeal_iff (originalDeformationCentralIdeal d t I N)
        hcent hg.1).mp hmem
    · intro hg
      obtain ⟨B,_hB,h0B,μ,_hμ,s,_hs,hsc⟩ := hcentFG
      have hgHol : HolAt g 0 := ((hsc 0 h0B g).mp hg).1
      apply (actualFiniteRelationSpan_origin_dictionary d t I hgHol).mpr
      change HolGerm.mk g hgHol ∈ Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))
      rw [← heq]
      exact (mk_mem_originalCoherentOriginIdeal_iff (originalDeformationCentralIdeal d t I N)
        hcent hgHol).mpr hg
  obtain ⟨W,hW,h0W,hwhole⟩ := exists_open_coherent_equality (hfg 0 h0V) hcentFG hiff
  exact ⟨N,U,V ∩ W,hU,h0U,hV.inter hW,⟨h0V,h0W⟩,hcent,
    (fun P hP y hy => hhol P hP y hy.1),
    (fun y hy => hfg y hy.1),(fun y hy => hwhole y hy.2),hchain,hpow,hsat⟩

theorem exists_original_whole_central_finite_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ V : Set (ComplexModel (d+t)), IsOpen V ∧ 0 ∈ V ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ P ∈ actualOriginalRelationFamily d t I, ∀ y ∈ V, HolAt (actualRelationFunction d t P) y) ∧
      (∀ y ∈ V, IdealFGAt (actualFiniteRelationSpan d t I) y) ∧
      (∀ y ∈ V, ∀ g, actualFiniteRelationSpan d t I y g ↔
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
  obtain ⟨N,U,A,hU,h0U,hA,h0A,hcent,hhol,hfg,hwhole,hchain,hpow,hsat⟩ :=
    exists_original_whole_central_finite_model_and_saturation d t I hI
  let V := A ∩ deformationCentralInclusion d t ⁻¹' U
  have hV : IsOpen V := hA.inter (hU.preimage (deformationCentralInclusion d t).continuous)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨h0A,by change deformationCentralInclusion d t 0 ∈ U; simpa only [map_zero] using h0U⟩
  exact ⟨N,V,hV,h0V,hcent,
    (fun P hP y hy => hhol P hP y hy.1),
    (fun y hy => hfg y hy.1),(fun y hy => hwhole y hy.1),
    (fun y hy => hchain _ hy.2),(fun y hy => hpow _ hy.2),(fun y hy => hsat _ hy.2)⟩

end
end Hironaka.HironakaRelativeNormalGraphCentralFiniteModel
