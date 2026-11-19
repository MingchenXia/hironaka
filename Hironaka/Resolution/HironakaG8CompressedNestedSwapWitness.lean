import Hironaka.Resolution.HironakaG8CompressedVisibleAdjacency
import Hironaka.Resolution.HironakaG8IndexedDisjointSwap
import Hironaka.Resolution.HironakaG8SingularTestCompression
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareNonempty

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompressedNestedSwapWitness

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8EmptyAwareTestTransport HironakaG8OccupiedSlotComparison
  HironakaG8RankedTestCompression HironakaG8CompressedVisibleAdjacency
  HironakaG8IndexedDisjointSwap HironakaG8SingularTestCompression HironakaG8FirstFootprintOrder
  G3UniverseEmptyAwareCore G3UniverseEmptyAwareNonempty
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal

variable {n : ℕ} {A B Y Z : CMfd.{0} n}

/-- A larger adjacent disjoint pair visible on the overlap gives an
actual adjacent swap in an empty-free compression of the smaller TEST.
The two selected compressed footprints are exactly the original traces. -/
theorem exists_compressed_nested_adjacent_swap
    (U : Opens B) (S : BlowupTower A Y) (T : BlowupTower B Z)
    {φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hNested : EmptyAwareTowerIso φ S (restrict U T) ψ)
    (i : ℕ) (hDisj : Disjoint (slotFootprint T i) (slotFootprint T (i+1)))
    (hVis₀ : (slotFootprint T i ∩ (U : Set B)).Nonempty)
    (hVis₁ : (slotFootprint T (i+1) ∩ (U : Set B)).Nonempty)
    (M : MarkedIdeal n A) (hM : M.IsWellFormed) (hN : M.N = univ)
    (W : Set A) (hW : IsClosed W) (hTest : IsGeoTestTower M S)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) S)
    :
    ∃ (Y₀ Y₁ : CMfd.{0} n) (Q : BlowupTower A Y₀) (R : BlowupTower A Y₁)
      (e₀ : Y₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (e₁ : Y₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₁) (j : ℕ),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) Q S e₀ ∧
      StageCentres (fun _ C => C.Nonempty) Q ∧ IsGeoTestTower M Q ∧
      j + 1 < Q.length ∧
      slotFootprint Q j = ((Subtype.val : U → B) ∘ φ) ⁻¹' slotFootprint T i ∧
      slotFootprint Q (j+1) = ((Subtype.val : U → B) ∘ φ) ⁻¹' slotFootprint T (i+1) ∧
      IsGeoTestTower M R ∧ R.proj ∘ e₁ = Q.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      ∀ k, slotFootprint R k = slotFootprint Q (Equiv.swap j (j+1) k) := by
  obtain ⟨Y₀,Q,e₀,hQCmp,hQTest,hQOcc,hQStage,_,_,_,_⟩ :=
    exists_empty_free_singular_test_compression M hM W hW S hTest hStage
  obtain ⟨Z₀,P,u,hPOcc,_,hPCmp,_⟩ := test_empty_free_compression (MarkedIdeal.pullback φ.symm M)
    (MarkedIdealTowerTransport.IsWellFormed.pullback (Φ := φ.symm) hM) (restrict U T)
  have hCmp := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans hQCmp hNested) (G3UniverseEmptyAwareCore.symm hPCmp)
  have hφ : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞).trans φ).trans
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).symm = φ := by ext x; rfl
  rw [hφ] at hCmp
  have hQP := isTowerIso_of_emptyAware_nonempty hCmp hQOcc hPOcc
  let a := (compressedRawOccupiedIso hPOcc hPCmp).symm
    ⟨i,(occupied_restrict_iff_slotFootprint_meets T U i).mpr hVis₀⟩
  let b := (compressedRawOccupiedIso hPOcc hPCmp).symm
    ⟨i+1,(occupied_restrict_iff_slotFootprint_meets T U (i+1)).mpr hVis₁⟩
  have hab := visibleEndpoints_compressed_adjacent_iff T U hPOcc hPCmp (Nat.lt_succ_self i) hVis₀ hVis₁
  change (compressedVisibleSlots T U hPOcc hPCmp a).val = i ∧
    (compressedVisibleSlots T U hPOcc hPCmp b).val = i+1 ∧ _ at hab
  obtain ⟨ha,hb,hadj⟩ := hab
  have hNext : b.val = a.val+1 := hadj.mpr (fun k h₀ h₁ => by omega)
  have hBound : a.val+1 < Q.length := by rw [hQP.length_eq,← hNext]; exact b.isLt
  have hFoot₀ : slotFootprint Q a.val = ((Subtype.val : U → B) ∘ φ) ⁻¹' slotFootprint T i := by
    rw [slotFootprint_of_isTowerIso hQP,
      compressedVisibleSlots_footprint T U hPOcc hPCmp a,ha,preimage_comp]
  have hFoot₁ : slotFootprint Q (a.val+1) =
      ((Subtype.val : U → B) ∘ φ) ⁻¹' slotFootprint T (i+1) := by
    rw [← hNext,slotFootprint_of_isTowerIso hQP,
      compressedVisibleSlots_footprint T U hPOcc hPCmp b,hb,preimage_comp]
  have hD : Disjoint (slotFootprint Q a.val) (slotFootprint Q (a.val+1)) := by
    rw [hFoot₀,hFoot₁]
    exact hDisj.preimage _
  obtain ⟨Y₁,R,e₁,hR,hProj,hStages,hFoot⟩ :=
    swap_adjacent_at_index Q a.val hBound hD W M hM hN hQTest hQStage
  exact ⟨Y₀,Y₁,Q,R,e₀,e₁,a.val,hQCmp,hQOcc,hQTest,hBound,hFoot₀,hFoot₁,hR,hProj,hStages,hFoot⟩

end Hironaka.HironakaG8CompressedNestedSwapWitness

#print axioms Hironaka.HironakaG8CompressedNestedSwapWitness.exists_compressed_nested_adjacent_swap
