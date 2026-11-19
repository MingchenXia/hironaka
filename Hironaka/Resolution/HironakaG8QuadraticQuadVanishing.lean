import Hironaka.Resolution.HironakaG8QuadraticAxesInitialHS
import Hironaka.Analytic.HolomorphicCoordinatePrime
import Hironaka.Analytic.RueckertNullstellensatz
import Mathlib.Algebra.Squarefree.Basic

/-! The full-rank quadric's coherent origin ideal is its literal reduced
geometric vanishing stalk. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG8QuadraticQuadVanishing
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HolomorphicCoordinatePrime
  HironakaG8QuadraticAxesRecoding HironakaG8QuadraticAxesInitialHS
  HironakaActualPointGeometricBennett HironakaRelativeNormalDeformationInitialRelations
  ActualHolomorphicGermFactoriality

private theorem trace_coordinate (d : ℕ) (i : Fin d) :
    planeTrace d 1 (coordinateGerm (i.castAdd 1)) = coordinateGerm i := by
  unfold planeTrace coordinateGerm
  rw [compAlgHom_mk]
  exact HolGerm.mk_eq_mk_iff.mpr
    (Eventually.of_forall fun z => tangentInclusion_tangent d 1 z i)

private theorem trace_eval (d : ℕ) (g : HolGerm (ComplexModel (d+1))) :
    HolGerm.eval (planeTrace d 1 g) = HolGerm.eval g := by
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
  rw [planeTrace,compAlgHom_mk,HolGerm.eval_mk,HolGerm.eval_mk]
  simp

private theorem plane_product_squarefree :
    Squarefree (coordinateGerm (0 : Fin 2) * coordinateGerm 1) := by
  let := uniqueFactorizationMonoid_holGerm_euclidean 2
  have hp (j : Fin 2) : Prime (coordinateGerm j) := prime_coordinate_germ j
  have hNot : ¬ coordinateGerm (1 : Fin 2) ∣ coordinateGerm (0 : Fin 2) := by
    intro h
    obtain ⟨k,hk⟩ := h
    have he := congrArg (planeTrace 1 1) hk
    have h1 : (1 : Fin 2) = (0 : Fin 1).natAdd 1 := rfl
    have h0 : (0 : Fin 2) = (0 : Fin 1).castAdd 1 := rfl
    rw [map_mul,h0,trace_coordinate,h1] at he
    change coordinateGerm (0 : Fin 1) =
      planeTrace 1 1 (normalCoordinate 1 1 0) * planeTrace 1 1 k at he
    rw [planeTrace_normalCoordinate,zero_mul] at he
    exact (prime_coordinate_germ (0 : Fin 1)).ne_zero he
  apply squarefree_mul_iff.mpr
  refine ⟨?_,(hp 0).squarefree,(hp 1).squarefree⟩
  intro a ha hb
  obtain ⟨w,hw⟩ := hb
  rcases (hp 1).irreducible.isUnit_or_isUnit hw with h | h
  · exact h
  · obtain ⟨u,rfl⟩ := h
    have hd : a * (u : HolGerm (ComplexModel 2)) ∣ a := ⟨↑u⁻¹,by simp [mul_assoc]⟩
    rw [← hw] at hd
    exact (hNot (dvd_trans hd ha)).elim

/-- Genuine analytic reduction follows by restricting any purported square
factor to the coordinate plane where the quadric is the squarefree product. -/
theorem quad_germ_squarefree : Squarefree quadGerm := by
  intro g hg
  have hTrace : planeTrace 2 1 quadGerm = coordinateGerm (0 : Fin 2) * coordinateGerm 1 := by
    unfold quadGerm
    rw [map_add,map_mul,map_mul]
    have hz : (coordinateGerm (2 : Fin 3)) = normalCoordinate 2 1 0 := rfl
    rw [hz,planeTrace_normalCoordinate,zero_mul,add_zero]
    exact congrArg₂ (· * ·) (trace_coordinate 2 0) (trace_coordinate 2 1)
  have hd : planeTrace 2 1 g * planeTrace 2 1 g ∣ planeTrace 2 1 quadGerm := by
    rw [← map_mul]
    exact map_dvd (planeTrace 2 1) hg
  rw [hTrace] at hd
  have hUnit := plane_product_squarefree _ hd
  apply (HolGerm.isUnit_iff_eval_ne_zero g).mpr
  have h := (HolGerm.isUnit_iff_eval_ne_zero (planeTrace 2 1 g)).mp hUnit
  rwa [trace_eval] at h

def quadSet : Set (ComplexModel 3) := {z | quadFunction z = 0}

/-- The actual geometric zero set has the same entire original origin
stalk as the literal polynomial ideal. -/
theorem quad_geometric_origin :
    originalCoherentOriginIdeal (vanishingIdeal (n := 3) quadSet) =
      originalCoherentOriginIdeal quadIdeal := by
  have hGeo : originalCoherentOriginIdeal (vanishingIdeal (n := 3) quadSet) =
      AnalyticGermDecomposition.vanishingIdeal quadSet := by
    ext g
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    rw [mk_mem_original_vanishing_origin_ideal_iff,AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  rw [hGeo,quad_origin]
  have hD : Differentiable ℂ quadFunction :=
    (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.mul
      (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable)).add
      (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable.mul
        (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable))
  let hf : HolAt quadFunction 0 := Eventually.of_forall hD
  have he : HolGerm.mk quadFunction hf = quadGerm := by
    unfold quadGerm coordinateGerm
    rw [← HolGerm.mk_mul,← HolGerm.mk_mul,← HolGerm.mk_add]
    rfl
  let := uniqueFactorizationMonoid_holGerm_euclidean 3
  have hRa : (Ideal.span ({quadGerm} : Set R)).IsRadical :=
    isRadical_iff_span_singleton.mp (isRadical_iff_squarefree_or_zero.mpr (Or.inl quad_germ_squarefree))
  apply le_antisymm
  · have h := RueckertNullstellensatz.vanishingIdeal_le_radical (Ideal.span {quadGerm})
      (fun _ : Fin 1 => quadFunction) (fun _ => ⟨hf,he ▸ Ideal.subset_span rfl⟩)
    apply (show AnalyticGermDecomposition.vanishingIdeal quadSet ≤ _ from ?_).trans
      (hRa.radical_le_iff.mpr le_rfl)
    have hSet : {y | ∀ _ : Fin 1, quadFunction y = 0} = quadSet := by
      ext y
      constructor
      · intro hy
        exact hy 0
      · intro hy _
        exact hy
    rwa [hSet] at h
  · apply Ideal.span_le.mpr
    rintro g rfl
    rw [← he]
    exact AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      (Eventually.of_forall fun _ hz => hz)

end
end Hironaka.HironakaG8QuadraticQuadVanishing
