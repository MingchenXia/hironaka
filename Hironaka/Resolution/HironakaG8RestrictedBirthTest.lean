import Hironaka.Resolution.HironakaG8PairDomainOpen
/-! # Restricting an actual birth and its test suffix -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8RestrictedBirthTest
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal

/-- Restriction to a source open preserves the literal birth and its test
suffix; the restricted birth transform is exactly the restriction of the
original birth transform. -/
theorem restrict_birth_and_suffix
    {n : ℕ} {X Y Z : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    {C : Set X} (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (T : BlowupTower Y Z) (hT : IsGeoTestTower (M.geoTransform C π) T) (G : Opens X) :
    let V : Opens Y := ⟨π ⁻¹' (G : Set X), G.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → G := fun p => ⟨π p.val,p.2⟩
    let M' := MarkedIdeal.pullback (Subtype.val : G → X) M
    let C' := (Subtype.val : G → X) ⁻¹' C
    M'.IsAdmissibleCentre C' ∧
      M'.geoTransform C' ρ = MarkedIdeal.pullback (Subtype.val : V → Y) (M.geoTransform C π) ∧
      IsGeoTestTower (M'.geoTransform C' ρ) (restrict V T) := by
  let V : Opens Y := ⟨π ⁻¹' (G : Set X), G.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → G := fun p => ⟨π p.val,p.2⟩
  let M' := MarkedIdeal.pullback (Subtype.val : G → X) M
  let C' := (Subtype.val : G → X) ⁻¹' C
  let One : BlowupTower X Y := .step .refl C π hπ
  have hOne : IsGeoTestTower M One := ⟨trivial,hC⟩
  have hCG : M'.IsAdmissibleCentre C' :=
    MarkedIdealRestrictOpen.IsAdmissibleCentre.pullback_val (hol_of_isCoherent hM.isCoherent) hC G
  have hPost : (M.geoTransform C π).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM One hOne
  have heq : M'.geoTransform C' ρ = MarkedIdeal.pullback (Subtype.val : V → Y) (M.geoTransform C π) :=
    geoTransform_pullback_val hM.isCoherent hπ hPost.isCoherent G V.isOpen
  have hTG := isGeoTestTower_restrict V hPost.isClosedSubmanifold_N hPost.isCoherent T hT
  rw [← heq] at hTG
  exact ⟨hCG,heq,hTG⟩

end
end Hironaka.HironakaG8RestrictedBirthTest
