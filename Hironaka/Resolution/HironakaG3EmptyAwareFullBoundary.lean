import Hironaka.Resolution.HironakaG3EmptyAwareBornSlots
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG3EmptyAwareFullBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareOldSlots HironakaG3EmptyAwareBornSlots

theorem boundary_decomp {d : ℕ} {X Y : CMfd.{u} d} (M : MarkedIdeal d X)
    (T : BlowupTower X Y) :
    (geoTransformAlong M T).E = M.E.map (strictAlong T) ++ bornAlong T := by
  induction T with
  | refl => simp [bornAlong, strictAlong, geoTransformAlong_refl]
  | @step Y Z T C π hπ ih =>
    rw [geoTransformAlong_step, geoTransform_E, ih]
    simp only [bornAlong,List.map_append,List.map_map,List.append_assoc]
    rfl

theorem full_boundary_transport {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (M₁ : MarkedIdeal d P₁) (M₂ : MarkedIdeal d P₂)
    (hE : M₁.E = M₂.E.map (Φ ⁻¹' ·)) (hclosed : ∀ H ∈ M₂.E, IsClosed H) :
    (geoTransformAlong M₁ T₁).E.filter (fun H => decide H.Nonempty) =
      ((geoTransformAlong M₂ T₂).E.filter (fun H => decide H.Nonempty)).map (ψ ⁻¹' ·) := by
  rw [boundary_decomp,boundary_decomp,hE,List.filter_append,List.filter_append,List.map_append]
  rw [emptyAware_old_boundary_eq h M₂.E hclosed, filter_map_bijection ψ ψ.surjective,
    emptyAware_born_boundary h]

end
end Hironaka.HironakaG3EmptyAwareFullBoundary
