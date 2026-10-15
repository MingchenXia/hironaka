/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralAnalyticClosure

/-! Complete actual mathematics precedes this OWN OFFLIB whole origin equality.
No nearby original normal-cone or same-neighbourhood all-q free claim. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphCentralIdealEquality
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalAnalyticGraphQuotient HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalGraphCentralAnalyticClosure

theorem original_coherent_all_selected_graph_central_reverse_inclusions (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∀ M : ℕ, originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I M) ≤
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
  let := tangentAlgebra d t
  obtain ⟨_N,_U,_hU,_h0,_hgraph,_hchain,hwhole,_hselected⟩ :=
    exists_original_coherent_whole_graph_central_reverse_inclusion d t I hI
  dsimp only
  intro M
  rw [originalCentralOriginIdeal_eq_graphColon_image d t I hI M]
  apply Ideal.map_le_iff_le_comap.mpr
  intro h hh
  exact hwhole h ⟨M,hh⟩

theorem exists_original_coherent_whole_graph_central_ideal_equality (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (originalDeformationColonIdeal d t I N).IsCoherent ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        ((originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^q) ↔
          (originalDeformationIdeal d t I).mem y (fun z => g z*deformationParameter d t z^N))) ∧
      (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g) ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0,hcol,hcent,hchain,hpow,hsat,hforward⟩ :=
    exists_original_deformation_initial_ideal_inclusion d t I hI
  exact ⟨N,U,hU,h0,hcol,hcent,hchain,hpow,hsat,
    (original_coherent_all_selected_graph_central_reverse_inclusions d t I hI N).antisymm hforward⟩

theorem exists_original_coherent_whole_graph_central_quotient_equiv (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) ∧
      ∃ e : (HolGerm (ComplexModel (d+t)) ⧸
          Ideal.map (normalPolynomialEval d t).toRingHom
            (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))) ≃+*
          (HolGerm (ComplexModel (d+t)) ⧸
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N)),
        ∀ g : HolGerm (ComplexModel (d+t)),
          e (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ g := by
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0,_hcol,hcent,_hchain,_hpow,_hsat,heq⟩ :=
    exists_original_coherent_whole_graph_central_ideal_equality d t I hI
  exact ⟨N,U,hU,h0,hcent,heq,Ideal.quotEquivOfEq heq.symm,
    fun g => Ideal.quotEquivOfEq_mk heq.symm g⟩

end
end Hironaka.HironakaRelativeNormalGraphCentralIdealEquality
