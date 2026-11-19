import Hironaka.Resolution.HironakaG8ActualCentreFibre
import Hironaka.Resolution.HironakaG8TangentOpen
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
/-! # Source-open tangency implies actual birth-trace containment -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8BirthTraceContainment
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold BlowupSpaceTangent BlowupRestrictOpen
  MarkedIdealRestrictOpen HironakaG8ActualCentreFibre HironakaG8TangentOpen

/-- At an actual blowup, uniform source tangency along the centre implies
containment of the complete birth trace over a source open. Carrier and old
member need be smooth and contain the centre only on that open. -/
theorem exceptional_trace_subset_of_tangent_on_open
    {n : ℕ} {X Y : CMfd.{0} n} {C P H : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (U : Opens X)
    (hP : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' P))
    (hH : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' H))
    (hCP : ((Subtype.val : U → X) ⁻¹' C) ⊆ ((Subtype.val : U → X) ⁻¹' P))
    (hCH : ((Subtype.val : U → X) ⁻¹' C) ⊆ ((Subtype.val : U → X) ⁻¹' H))
    (htan : ∀ x ∈ C, x ∈ U → tangentSpace n P x ≤ tangentSpace n H x) :
    ∀ z : Y, π z ∈ U → π z ∈ C → z ∈ geoStrictTransform π C P →
      z ∈ geoStrictTransform π C H := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun p => ⟨π p.val,p.2⟩
  let C' : Set U := (Subtype.val : U → X) ⁻¹' C
  let P' : Set U := (Subtype.val : U → X) ⁻¹' P
  let H' : Set U := (Subtype.val : U → X) ⁻¹' H
  have hρ : IsBlowupAlong n C' ρ := isBlowupAlong_restrict hπ U V.isOpen
  intro z hzU hzC hzP
  let z' : V := ⟨z,hzU⟩
  have hxC : ρ z' ∈ C' := hzC
  obtain ⟨k,hk⟩ := hP.2 (ρ z') (hCP hxC)
  have hk0 : RegularAtDim (n := n) P (π z) k :=
    (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U) (x := ρ z')).mp hk
  have hxH : π z ∈ H := hCH hxC
  have htan' : tangentSpace n P' (ρ z') ≤ tangentSpace n H' (ρ z') :=
    (tangent_le_preimage_val_iff U (ρ z') hk0 hxH).mpr (htan (π z) hzC hzU)
  have hzP' : z' ∈ geoStrictTransform ρ C' P' := by
    rw [geoStrictTransform_restrict U V.isOpen P]
    exact hzP
  have hzH' := (strict_fibre_subset_iff_tangentSpace_le hρ.1 hρ.2.1 hρ hP hH hCP hCH hxC).mpr
    htan' z' rfl hzP'
  rw [geoStrictTransform_restrict U V.isOpen H] at hzH'
  exact hzH'

end
end Hironaka.HironakaG8BirthTraceContainment
