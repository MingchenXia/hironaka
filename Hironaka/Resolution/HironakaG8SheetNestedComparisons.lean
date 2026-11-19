import Hironaka.Resolution.HironakaG8DisjointCutoffDescent
import Hironaka.Resolution.HironakaG8ConsecutiveNestedReorderings

/-! Comparisons of two cofinal cutoff towers from their common sheets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SheetNestedComparisons

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals HironakaG3EmptyAwareHistory HironakaG8OccupiedSlotComparison
  HironakaSharpActualCurveComparisonRestriction HironakaG8DisjointCutoffDescent
  HironakaG8ConsecutiveNestedReorderings MaxLocusLocal

variable {n : ℕ} {X A B : CMfd.{0} n} {ι : Type*} {U V : Opens X}
local notation "𝓘c" => 𝓘(ℂ,ComplexModel n)
local notation "BU" => CMfd.of (n := n) U
local notation "BV" => CMfd.of (n := n) V

/-- Build an actual nested comparison from literal matching on each disjoint
sheet of the smaller chart and equality of the ordered occupied footprints. -/
theorem nested_geometry_of_disjoint_sheet_comparisons
    (hUV : U ≤ V) (O : ι → Opens X) (hOU : ∀ i, O i ≤ U)
    (hCover : ∀ (x : U), ∃ i, x.val ∈ O i)
    (hDisj : Pairwise fun i j => Disjoint (O i : Set X) (O j : Set X))
    (S : BlowupTower BU A) (T : BlowupTower BV B)
    (M : MarkedIdeal n BU) (hM : M.IsWellFormed)
    (hFoot : occupiedFootprints S = (occupiedFootprints (restrict (nestedOpens V U) T)).map
      ((nestedOpensDiffeo (n := n) hUV).symm ⁻¹' ·))
    (hLocal : ∀ i,
      ∃ f : CMfd.of (n := n) (nestedOpens U (O i)) ≃ₘ⟮𝓘c,𝓘c⟯
          CMfd.of (n := n) (nestedOpens V (O i)),
        (∀ x, (f x).val.val = x.val.val) ∧
        ∃ e : CMfd.of (n := n) (openPreimage S (nestedOpens U (O i))) ≃ₘ⟮𝓘c,𝓘c⟯
          CMfd.of (n := n) (openPreimage T (nestedOpens V (O i))),
          EmptyAwareTowerIso f (restrict (nestedOpens U (O i)) S)
            (restrict (nestedOpens V (O i)) T) e) :
    NestedGeometry S T := by
  let V₀ := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hUV).symm
  let Q (i : ι) := nestedOpens V (O i)
  let H (i : ι) := nestedOpens V₀ (Q i)
  have hCoverH (y : V₀) : ∃ i, y ∈ H i := hCover ⟨y.val.val,y.property⟩
  have hDisjH : Pairwise fun i j => Disjoint (H i : Set V₀) (H j : Set V₀) := by
    intro i j h
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => Set.disjoint_left.mp (hDisj h) h₁ h₂)
  have hH (i : ι) :
      ∃ f : CMfd.of (n := n) (openPreimage S (preimageOpen e (H i))) ≃ₘ⟮𝓘c,𝓘c⟯
        CMfd.of (n := n) (openPreimage (restrict V₀ T) (H i)),
      EmptyAwareTowerIso (openRestriction e (preimageOpen e (H i)) (H i) rfl)
        (restrict (preimageOpen e (H i)) S) (restrict (H i) (restrict V₀ T)) f := by
    obtain ⟨g,hg,f,hf⟩ := hLocal i
    have hQV : Q i ≤ V₀ := fun _ h => hOU i h
    let d := nestedOpensDiffeo (n := n) hQV
    have hFlatten := emptyAware_of_isTowerIso (isTowerIso_restrict_nestedOpens hQV T)
    let LocalAt (P : Opens BU) : Prop :=
      ∃ a : CMfd.of (n := n) P ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (H i),
        (∀ x, (a x).val = e x.val) ∧
        ∃ b : CMfd.of (n := n) (openPreimage S P) ≃ₘ⟮𝓘c,𝓘c⟯
            CMfd.of (n := n) (openPreimage (restrict V₀ T) (H i)),
          EmptyAwareTowerIso a (restrict P S) (restrict (H i) (restrict V₀ T)) b
    have hSmall : LocalAt (nestedOpens U (O i)) := by
      refine ⟨g.trans d.symm,fun x => ?_,_,G3UniverseEmptyAwareCore.trans hf
        (G3UniverseEmptyAwareCore.symm hFlatten)⟩
      exact Subtype.ext (Subtype.ext (hg x))
    have hPre : preimageOpen e (H i) = nestedOpens U (O i) := by
      ext x
      rfl
    obtain ⟨a,ha,b,hb⟩ := hPre.symm ▸ hSmall
    have hA : a = openRestriction e (preimageOpen e (H i)) (H i) rfl := by
      apply Diffeomorph.ext
      intro x
      exact Subtype.ext (ha x)
    exact ⟨b,hA ▸ hb⟩
  obtain ⟨f,hf⟩ := exists_emptyAware_of_disjoint_cover_footprints
    H hCoverH hDisjH e S (restrict V₀ T) M hM hFoot hH
  exact ⟨e,fun _ => rfl,f,hf⟩

end Hironaka.HironakaG8SheetNestedComparisons
