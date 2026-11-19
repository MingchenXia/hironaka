import Hironaka.Resolution.HironakaG8DisjointPatchDiffeomorphism
import Hironaka.Resolution.HironakaG8EmptyAwareCoverBaseChange

/-! Literal history comparison over disjoint patches of two cutoffs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointCutoffDescent

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG8OccupiedSlotComparison
  HironakaSharpActualCurveComparisonRestriction HironakaG8DisjointPatchDiffeomorphism
  HironakaG8EmptyAwareCoverBaseChange

variable {n : ℕ} {X X' Y Z : CMfd.{0} n} {ι : Type*}
local notation "𝓘c" => 𝓘(ℂ,ComplexModel n)

/-- Disjoint literal local tower comparisons over the given base map
glue to a whole comparison if the ordered occupied footprints agree. -/
theorem exists_emptyAware_of_disjoint_cover_footprints
    (U : ι → Opens X') (hCover : ∀ x : X', ∃ i, x ∈ U i)
    (hDisj : Pairwise fun i j => Disjoint (U i : Set X') (U j : Set X'))
    (f : X ≃ₘ⟮𝓘c,𝓘c⟯ X') (S : BlowupTower X Y) (T : BlowupTower X' Z)
    (M : MarkedIdeals.MarkedIdeal n X) (hM : M.IsWellFormed)
    (hFoot : occupiedFootprints S = (occupiedFootprints T).map (f ⁻¹' ·))
    (hLocal : ∀ i, ∃ e : CMfd.of (n := n) (openPreimage S (preimageOpen f (U i))) ≃ₘ⟮𝓘c,𝓘c⟯
        CMfd.of (n := n) (openPreimage T (U i)),
      EmptyAwareTowerIso (openRestriction f (preimageOpen f (U i)) (U i) rfl)
        (restrict (preimageOpen f (U i)) S) (restrict (U i) T) e) :
    ∃ e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z, EmptyAwareTowerIso f S T e := by
  choose a ha using hLocal
  let L (i : ι) := openPreimage S (preimageOpen f (U i))
  let R (i : ι) := openPreimage T (U i)
  have hL (y : Y) : ∃ i, y ∈ L i := hCover (f (S.proj y))
  have hR (z : Z) : ∃ i, z ∈ R i := hCover (T.proj z)
  have hdL : Pairwise fun i j => Disjoint (L i : Set Y) (L j : Set Y) := by
    intro i j h
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => Set.disjoint_left.mp (hDisj h) h₁ h₂)
  have hdR : Pairwise fun i j => Disjoint (R i : Set Z) (R j : Set Z) := by
    intro i j h
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => Set.disjoint_left.mp (hDisj h) h₁ h₂)
  obtain ⟨e,he,_⟩ := exists_diffeomorph_of_disjoint_open_covers L R hL hR hdL hdR a
  refine ⟨e,emptyAware_over_of_local_of_occupiedFootprints_eq U hCover f S T e ?_
    M hM hFoot (fun i => ⟨a i,fun y => (he i y).symm,ha i⟩)⟩
  intro y
  obtain ⟨i,hy⟩ := hL y
  let p : L i := ⟨y,hy⟩
  let P := preimageOpen f (U i)
  let fU := openRestriction f P (U i) rfl
  change T.proj (e p.val) = f (S.proj p.val)
  calc
    T.proj (e p.val) = T.proj (a i p).val := congrArg T.proj (he i p)
    _ = ((restrict (U i) T).proj (a i p)).val := (proj_restrict (U i) T (a i p)).symm
    _ = (fU ((restrict P S).proj p)).val :=
      congrArg (fun z : U i => z.val) (emptyAware_proj_comm (ha i) p)
    _ = f (((restrict P S).proj p).val) := openRestriction_val f P (U i) rfl _
    _ = f (S.proj p.val) := congrArg f (proj_restrict P S p)

end Hironaka.HironakaG8DisjointCutoffDescent
