import Hironaka.Resolution.HironakaG8FiniteParallelLocalReadback
import Hironaka.Resolution.HironakaG8DisjointPhaseMerge
import Hironaka.Resolution.HironakaOriginalOldBranchTestLocality

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ParallelBlocksJoin

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MaxLocusLocal
  G3UniverseEmptyAwareCore HironakaG8DisjointPhaseMerge
  HironakaG8EmptyAwareTestTransport HironakaOriginalOldBranchOpenHistory

/-- Local block comparisons concatenate, and their terminal point dictionary
is unchanged by either of the actual append restriction identifications. -/
theorem append_local_parallel_comparisons {n : ℕ} {X A B Y : CMfd.{0} n}
    (U : Opens X) (P : BlowupTower X A) (P' : BlowupTower X B)
    (S : BlowupTower A Y) (S' : BlowupTower B Y)
    {β : CMfd.of (n := n) (openPreimage P U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage P' U)}
    (hP : EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict U P) (restrict U P') β)
    {χ : CMfd.of (n := n) (openPreimage S (openPreimage P U))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S' (openPreimage P' U))}
    (hS : EmptyAwareTowerIso β (restrict (openPreimage P U) S) (restrict (openPreimage P' U) S') χ)
    (hVal : ∀ y, (χ y).val = y.val) :
    ∃ φ : CMfd.of (n := n) (openPreimage (P.append S) U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (P'.append S') U),
      (∀ y, (φ y).val = y.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl _ _ _)
        (restrict U (P.append S)) (restrict U (P'.append S')) φ := by
  have hA := emptyAware_of_isTowerIso (isTowerIso_restrict_append U P S)
  have hB := emptyAware_of_isTowerIso (isTowerIso_restrict_append U P' S').symm
  let a := opensCongr (n := n) (openPreimage_append P S U).symm
  let b := opensCongr (n := n) (openPreimage_append P' S' U).symm
  refine ⟨(a.trans χ).trans b.symm,fun y => hVal (a y),?_⟩
  simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans] using
    G3UniverseEmptyAwareCore.trans
      (G3UniverseEmptyAwareCore.trans hA (emptyAware_append hP hS)) hB

/-- Any finite regrouping compared on a source cover retains the original
well-formed TEST, including its original ordered boundary. -/
theorem grouped_test_of_local_comparisons {n : ℕ} {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (T : BlowupTower X Y) (G : BlowupTower X Z) (hT : IsGeoTestTower M T)
    {ι : Type*} (U : ι → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hCompare : ∀ i, ∃ e : CMfd.of (n := n) (openPreimage T (U i))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage G (U i)),
      EmptyAwareTowerIso (Diffeomorph.refl _ _ _) (restrict (U i) T) (restrict (U i) G) e) :
    IsGeoTestTower M G := by
  apply isGeoTestTower_of_open_cover M hM.isClosedSubmanifold_N hM.isCoherent G
  intro x
  obtain ⟨i,hx⟩ := hCover x
  refine ⟨U i,hx,?_⟩
  obtain ⟨e,h⟩ := hCompare i
  let M₀ := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U i → X) M
  have hM₀ : M₀.IsWellFormed := IsWellFormed.pullback_val hM (U i)
  have hT₀ := isGeoTestTower_restrict (U i) hM.isClosedSubmanifold_N hM.isCoherent T hT
  have hTransport := isGeoTestTower_iff_of_emptyAware M₀ hM₀ _ h
  simp only [Diffeomorph.coe_refl,ContactCanonicalAlong.pullback_id _ hM₀.isCoherent] at hTransport
  exact hTransport.mp hT₀

end Hironaka.HironakaG8ParallelBlocksJoin
