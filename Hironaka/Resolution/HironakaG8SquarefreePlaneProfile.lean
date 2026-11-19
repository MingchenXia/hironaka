import Hironaka.Resolution.HironakaActualPointGeometricBennett
import Hironaka.Resolution.HironakaActualPrincipalHSFormula
import Hironaka.Analytic.ActualHolomorphicGermFactoriality
import Hironaka.Analytic.RueckertNullstellensatz
import Mathlib.Algebra.Squarefree.Basic

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG8SquarefreePlaneProfile
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm OkaRelationSheaf HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance HironakaActualPointGeometricBennett
  ActualHolomorphicGermFactoriality HironakaActualPrincipalHSFormula HironakaActualPrincipalJetMultiplication

variable (f : ComplexModel 2 → ℂ) (hf : HolAt f 0)

theorem origin_ideal_of_squarefree_plane_equation
    (h : Squarefree (HolGerm.mk f hf)) :
    originalCoherentOriginIdeal (vanishingIdeal (n := 2) {z | f z = 0}) =
      Ideal.span {HolGerm.mk f hf} := by
  have hGeo : originalCoherentOriginIdeal (vanishingIdeal (n := 2) {z | f z = 0}) =
      AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} := by
    ext g
    obtain ⟨a,ha,rfl⟩ := HolGerm.exists_eq_mk g
    rw [mk_mem_original_vanishing_origin_ideal_iff,AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  rw [hGeo]
  let := uniqueFactorizationMonoid_holGerm_euclidean 2
  have hRa : (Ideal.span ({HolGerm.mk f hf} : Set (HolGerm (ComplexModel 2)))).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl h))
  apply le_antisymm
  · have hBound := RueckertNullstellensatz.vanishingIdeal_le_radical (Ideal.span {HolGerm.mk f hf})
      (fun _ : Fin 1 => f) (fun _ => ⟨hf,Ideal.subset_span rfl⟩)
    apply (show AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} ≤ _ from ?_).trans
      (hRa.radical_le_iff.mpr le_rfl)
    simpa only [Fin.forall_fin_one] using hBound
  · apply Ideal.span_le.mpr
    rintro g rfl
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun _ hz => hz)

theorem origin_profile_of_squarefree_plane_equation
    (h : Squarefree (HolGerm.mk f hf)) (hne : HolGerm.mk f hf ≠ 0) (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 2) {z | f z = 0}) 0 l =
      Nat.choose (2+l) 2 - (if actualGermOrder (HolGerm.mk f hf) hne ≤ l then
        Nat.choose (2+(l-actualGermOrder (HolGerm.mk f hf) hne)) 2 else 0) := by
  rw [hilbertSamuelAt_model_zero,origin_ideal_of_squarefree_plane_equation f hf h]
  exact hilbertSamuelValue_actual_principal_order (HolGerm.mk f hf) hne l

end
end Hironaka.HironakaG8SquarefreePlaneProfile
