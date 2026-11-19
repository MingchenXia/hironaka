import Hironaka.Invariant.StepOneSeq
import Hironaka.Invariant.ContactStageKept
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3ContactChoiceAtBase
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain ResolutionInvariantSpec
  ContactStageKept TangentDirectionAlong
noncomputable section

/-- Two valid contact choices agree at an actual common point when their actual lower tails are canonical. -/
theorem contact_choice_values_at_actual_base {n k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) {X Y Z : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : 1 ≤ M.d)
    (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z) (hT : IsGeoTestTower (barMarked M) (T₀.append T₁))
    (z : Z) (hz : z ∈ (geoTransformAlong (barMarked M) (T₀.append T₁)).cosupp)
    (a b : X → ℂ) (U V : Set X)
    (ha : IsTangentDirectionAlong M.N M.ideal M.d U a) (hxU : T₀.proj (T₁.proj z) ∈ U)
    (hb : IsTangentDirectionAlong M.N M.ideal M.d V b) (hxV : T₀.proj (T₁.proj z) ∈ V)
    (Wₐ Wᵦ : Opens Y)
    (hWₐ : (Wₐ : Set Y) ⊆ T₀.proj ⁻¹' U) (hWᵦ : (Wᵦ : Set Y) ⊆ T₀.proj ⁻¹' V)
    (hEₐ : ∀ H ∈ origMembers M T₀, Disjoint (Wₐ : Set Y) H)
    (hEᵦ : ∀ H ∈ origMembers M T₀, Disjoint (Wᵦ : Set Y) H)
    (hDₐ : IsInvDomain k (contactMarkedKept M a T₀ Wₐ))
    (hCₐ : IsCanonical (contactMarkedKept M a T₀ Wₐ) (R.inv (contactMarkedKept M a T₀ Wₐ)) (restrict Wₐ T₁))
    (hDᵦ : IsInvDomain k (contactMarkedKept M b T₀ Wᵦ))
    (hCᵦ : IsCanonical (contactMarkedKept M b T₀ Wᵦ) (R.inv (contactMarkedKept M b T₀ Wᵦ)) (restrict Wᵦ T₁))
    (hzₐ : T₁.proj z ∈ Wₐ) (hzᵦ : T₁.proj z ∈ Wᵦ) :
    R.inv (contactMarkedKept M a T₀ Wₐ) (restrict Wₐ T₁) ⟨z,hzₐ⟩ =
      R.inv (contactMarkedKept M b T₀ Wᵦ) (restrict Wᵦ T₁) ⟨z,hzᵦ⟩ := by
  have hJ := isWellFormed_barMarked M hM
  have hx := proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent (T₀.append T₁) hT hz
  rw [cosupp_barMarked M hM hd, BlowupTower.proj_append] at hx
  obtain ⟨O,hxO,hO⟩ := Seq.StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint
    R M hM.isCoherent hM.isClosedSubmanifold_N hd hx ha hxU hb hxV
  exact hO T₀ T₁ hT Wₐ Wᵦ hWₐ hWᵦ hEₐ hEᵦ hDₐ hCₐ hDᵦ hCᵦ ⟨z,hzₐ⟩ ⟨z,hzᵦ⟩ rfl hxO hz
end
end Hironaka.G3ContactChoiceAtBase
