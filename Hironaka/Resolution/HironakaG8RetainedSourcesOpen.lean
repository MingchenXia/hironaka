import Hironaka.Resolution.HironakaG11RetainedBirthContainment
import Hironaka.Blowup.BlowupRestrictOpen

/-! # Retained birth sources after restricting to a source open -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8RetainedSourcesOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupRestrictOpen
  MarkedIdealRestrictOpen HomogenizedGlueingTower

/-- Smooth retained sources, their strict images and centre-germ inclusion
are preserved by restriction to a source open and its literal test suffix. -/
theorem retained_sources_restrict
    {n : ℕ} {X Y Z : CMfd.{0} n} {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (U : Opens X) (T : BlowupTower Y Z)
    {z : Z} (hzU : π (T.proj z) ∈ U) {S : List (Set Z)}
    (hsource : ∀ K ∈ S, ∃ H : Set X, IsClosedSubmanifold n H ∧
      IsClosedSubmanifold n (geoStrictTransform π C H) ∧
      K = strictAlong T (geoStrictTransform π C H) ∧
      ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ H) :
    let V : Opens Y := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → U := fun p => ⟨π p.val,p.2⟩
    let C' : Set U := (Subtype.val : U → X) ⁻¹' C
    let W := openPreimage T V
    let z' : W := ⟨z,hzU⟩
    let T' := restrict V T
    ∀ K ∈ S.map ((Subtype.val : W → Z) ⁻¹' ·), ∃ H : Set U,
      IsClosedSubmanifold n H ∧ IsClosedSubmanifold n (geoStrictTransform ρ C' H) ∧
      K = strictAlong T' (geoStrictTransform ρ C' H) ∧
      ∀ᶠ x in 𝓝 (ρ (T'.proj z')), x ∈ C' → x ∈ H := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun p => ⟨π p.val,p.2⟩
  let C' : Set U := (Subtype.val : U → X) ⁻¹' C
  let W := openPreimage T V
  let z' : W := ⟨z,hzU⟩
  let T' := restrict V T
  have hproj : ((T'.proj z' : V) : Y) = T.proj z := proj_restrict V T z'
  have hpoint : ρ (T'.proj z') = (⟨π (T.proj z), hzU⟩ : U) := by
    apply Subtype.ext
    change π ((T'.proj z' : V) : Y) = π (T.proj z)
    rw [hproj]
  change ∀ K ∈ S.map ((Subtype.val : W → Z) ⁻¹' ·), ∃ H : Set U,
      IsClosedSubmanifold n H ∧ IsClosedSubmanifold n (geoStrictTransform ρ C' H) ∧
      K = strictAlong T' (geoStrictTransform ρ C' H) ∧
      ∀ᶠ x in 𝓝 (ρ (T'.proj z')), x ∈ C' → x ∈ H
  intro K hK
  obtain ⟨K₀,hK₀,rfl⟩ := List.mem_map.mp hK
  obtain ⟨H,hH,hHs,hEq,hCH⟩ := hsource K₀ hK₀
  refine ⟨(Subtype.val : U → X) ⁻¹' H, isClosedSubmanifold_preimage_val hH U, ?_, ?_, ?_⟩
  · rw [geoStrictTransform_restrict U V.isOpen H]
    exact isClosedSubmanifold_preimage_val hHs V
  · rw [geoStrictTransform_restrict U V.isOpen H, strictAlong_restrict V T (geoStrictTransform π C H), hEq]
  · rw [hpoint]
    exact (continuous_subtype_val.tendsto (⟨π (T.proj z),hzU⟩ : U)).eventually hCH

end
end Hironaka.HironakaG8RetainedSourcesOpen
