import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! Exact empty-step compression of original singular-centred TEST. -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SingularTestCompression
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8EmptyAwareTestTransport HironakaG8SingularFootprintExtension
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Compress an actual singular-centred original TEST by deleting its empty
steps. The original projection and every projected occupied centre agree
exactly, and the occupied stage matching is an order isomorphism. -/
theorem exists_empty_free_singular_test_compression
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (W : Set X) (hW : IsClosed W)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower M T)
    (hSing : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower X Z)
      (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y),
      ∃ hCmp : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) Q T e,
        IsGeoTestTower M Q ∧
        StageCentres (fun _ C => C.Nonempty) Q ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
        Q.length ≤ T.length ∧
        (∀ z, T.proj (e z) = Q.proj z) ∧
        occupiedFootprints Q = occupiedFootprints T ∧
        (∀ i : {k // Occupied Q k},
          slotFootprint Q i.val = slotFootprint T (occupiedComparison hCmp i).val) := by
  obtain ⟨Z,Q,e,hOcc,hLength,hCmp,hTests⟩ := test_empty_free_compression M hM T
  have hRev := G3UniverseEmptyAwareCore.symm hCmp
  have hStep := singular_stages_of_emptyAware W hW
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).symm hRev
  have hSingQ : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q := by
    apply hStep
    simpa only [Diffeomorph.symm_refl,Diffeomorph.coe_refl,preimage_id] using hSing
  refine ⟨Z,Q,e,hCmp,hTests.mpr hTest,hOcc,hSingQ,hLength,?_,?_,?_⟩
  · exact emptyAware_proj_comm hCmp
  · simpa only [Diffeomorph.coe_refl,preimage_id,List.map_id'] using occupiedFootprints_emptyAware hCmp
  · intro i
    simpa only [Diffeomorph.coe_refl,preimage_id] using slotFootprint_occupiedComparison hCmp i

end Hironaka.HironakaG8SingularTestCompression
