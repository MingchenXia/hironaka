import Hironaka.Resolution.HironakaG8IndexedVisibleSwapGeometry
import Hironaka.Resolution.HironakaG8LiteralCompressedSwapComparison
import Hironaka.Resolution.HironakaG8OrderedFootprintTraces

set_option autoImplicit false
open Classical
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NestedMoveReadback
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaStageCenters HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder
  HironakaG8DisjointSwapFullHistory G3UniverseEmptyAwareCore HironakaG8LiteralCompressedSwapComparison

open HironakaG8IndexedVisibleSwapGeometry HironakaG8EmptyAwareTestTransport

variable {n : ℕ} {A B F G H : CMfd.{0} n}

theorem visible_nested_move_readback
    (N : MarkedIdeal n B) (hN : N.IsWellFormed)
    {T : BlowupTower B F} {R : BlowupTower B G}
    {e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G} {i : ℕ}
    (w : AdjacentSwapGeometry T R e i)
    (hBefore : IsGeoTestTower N T) (hAfter : IsGeoTestTower N R)
    (U : Opens B) (hVis₀ : (slotFootprint T i ∩ (U : Set B)).Nonempty)
    (hVis₁ : (slotFootprint T (i+1) ∩ (U : Set B)).Nonempty)
    (S : BlowupTower A H)
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ψ : H ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U))
    (hNested : EmptyAwareTowerIso φ S (restrict U T) ψ) :

    let M := MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : U → B) N)
    ∃ (K : CMfd.{0} n) (S' : BlowupTower A K)
      (η : H ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ K)
      (θ : K ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage R U)),
      StageCentres (fun _ K => K.Nonempty) S' ∧ IsGeoTestTower M S' ∧ S'.proj ∘ η = S.proj ∧
      EmptyAwareTowerIso φ S' (restrict U R) θ ∧
      (∀ z, (θ (η z)).val = e (ψ z).val) ∧
      occupiedFootprints S = (occupiedFootprints (restrict U T)).map (φ ⁻¹' ·) ∧
      occupiedFootprints S' = (occupiedFootprints (restrict U R)).map (φ ⁻¹' ·) := by
  obtain ⟨F₁,G₁,Q,R₁,ψ₁,f₁,χ,_,hQCmp,hProj,_,hRT,hCmp,hEnd,_,_⟩ :=
    compatible_visible_small_swap_of_geometry N hN w hBefore hAfter U hVis₀ hVis₁ S φ ψ hNested
  let M := MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : U → B) N)
  have hM : M.IsWellFormed := MarkedIdealTowerTransport.IsWellFormed.pullback
    (Φ := φ) (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U)
  obtain ⟨K,S',k,hOcc,_,hK,hTest⟩ := test_empty_free_compression M hM R₁
  have hh := G3UniverseEmptyAwareCore.trans hK hCmp
  rw [Diffeomorph.refl_trans] at hh
  let η := (ψ₁.symm.trans f₁).trans k.symm
  refine ⟨K,S',η,k.trans χ,hOcc,hTest.mpr hRT,?_,hh,?_,
    occupiedFootprints_emptyAware hNested,occupiedFootprints_emptyAware hh⟩
  · funext z
    have hk := emptyAware_proj_comm hK (k.symm (f₁ (ψ₁.symm z)))
    have hq := emptyAware_proj_comm hQCmp (ψ₁.symm z)
    change R₁.proj (k (k.symm (f₁ (ψ₁.symm z)))) = S'.proj (η z) at hk
    change S.proj (ψ₁ (ψ₁.symm z)) = Q.proj (ψ₁.symm z) at hq
    rw [k.apply_symm_apply] at hk
    rw [ψ₁.apply_symm_apply] at hq
    exact hk.symm.trans ((congrFun hProj (ψ₁.symm z)).trans hq.symm)
  · intro z
    change (χ (k (k.symm (f₁ (ψ₁.symm z))))).val = _
    rw [k.apply_symm_apply,hEnd,ψ₁.apply_symm_apply]

/-- An exact ordered trace list for any literal nested comparison. -/
theorem occupied_footprints_of_nested_chart
    (U : Opens B) (T : BlowupTower B F) (S : BlowupTower A H)
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {ψ : H ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U)}
    (hNested : EmptyAwareTowerIso φ S (restrict U T) ψ) :
    occupiedFootprints S = ((occupiedFootprints T).filterMap
      (fun footprint => if (footprint ∩ (U : Set B)).Nonempty then
        some ((Subtype.val : U → B) ⁻¹' footprint) else none)).map (φ ⁻¹' ·) := by
  rw [occupiedFootprints_emptyAware hNested,
    HironakaG8OrderedFootprintTraces.occupiedFootprints_restrict_eq_filterMap]

end Hironaka.HironakaG8NestedMoveReadback
