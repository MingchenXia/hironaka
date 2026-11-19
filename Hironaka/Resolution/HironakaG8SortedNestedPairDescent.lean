import Hironaka.Resolution.HironakaG8SortedNestedEndpoint
import Hironaka.Resolution.HironakaG8EmptyAwareCoverBaseChange

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SortedNestedPairDescent

open BlowupTowers BlowupTowerTransforms MaxLocusLocal MarkedIdeals MarkedIdeals.MarkedIdeal
  G3UniverseEmptyAwareCore HironakaSharpActualCurveComparisonRestriction
  HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord HironakaG8SortedNestedEndpoint
  HironakaG8OccupiedSlotComparison HironakaG8EmptyAwareCoverBaseChange

variable {n : ℕ} {X A B Y Z : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- A literal point dictionary identifies the local base map with the
canonical open restriction of the prescribed ambient base map. -/
theorem canonical_local_comparison
    (e : A ≃ₘ⟮𝓘c,𝓘c⟯ B) (g : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (S : BlowupTower A Y) (T : BlowupTower B Z)
    (Q : Opens A) (H : Opens B) (hQ : preimageOpen e H = Q)
    (p : CMfd.of (n := n) Q ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) H)
    (q : CMfd.of (n := n) (openPreimage S Q) ≃ₘ⟮𝓘c,𝓘c⟯
      CMfd.of (n := n) (openPreimage T H))
    (hp : ∀ z, (p z).val = e z.val) (hq : ∀ z, (q z).val = g z.val)
    (h : EmptyAwareTowerIso p (restrict Q S) (restrict H T) q) :
    LocalEmptyComparisonOver e S T g H := by
  subst Q
  have hP : p = openRestriction e (preimageOpen e H) H rfl := by
    ext z
    exact hp z
  exact ⟨q,hq,hP ▸ h⟩

variable {U V : Opens X}
local notation "BU" => CMfd.of (n := n) U
local notation "BV" => CMfd.of (n := n) V

/-- Equal ordered occupied footprints and the exact local comparisons of
the fixed words descend over the original base diffeomorphism. -/
theorem sorted_nested_pair_of_occupiedFootprints_eq
    {L L' : TowerAt BU} {R R' : TowerAt BV}
    (WL : Set BU) (WR : Set BV) (ML : MarkedIdeal n BU) (MR : MarkedIdeal n BV)
    (hML : ML.IsWellFormed) {w v : List ℕ}
    (hL : RealizedWord (GeometricIndexedMove WL ML) w L L')
    (hR : RealizedWord (GeometricIndexedMove WR MR) v R R')
    (e : BU ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : L.1 ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage R.2 (nestedOpens V U)))
    (h : EmptyAwareTowerIso e L.2 (restrict (nestedOpens V U) R.2) f)
    (hFoot : occupiedFootprints L'.2 =
      (occupiedFootprints (restrict (nestedOpens V U) R'.2)).map (e ⁻¹' ·)) :
    ∃ (a : L.1 ≃ₘ⟮𝓘c,𝓘c⟯ L'.1) (b : R.1 ≃ₘ⟮𝓘c,𝓘c⟯ R'.1)
      (_ha : L'.2.proj ∘ a = L.2.proj) (hb : R'.2.proj ∘ b = R.2.proj),
      EmptyAwareTowerIso e L'.2 (restrict (nestedOpens V U) R'.2)
        (sortedEndpoint R.2 R'.2 a b hb f) := by
  classical
  obtain ⟨a,b,ha,hb,hProj,hLocal⟩ :=
    nested_words_have_fixed_endpoint_cover WL WR ML MR hL hR e he f h
  choose O hPoint hOU hOV hRead using hLocal
  let H (x : U) := nestedOpens (nestedOpens V U) (nestedOpens V (O x))
  refine ⟨a,b,ha,hb,emptyAware_over_of_local_of_occupiedFootprints_eq H ?_
    e L'.2 _ _ hProj ML hML hFoot ?_⟩
  · intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    exact ⟨x,by change (e x).val.val ∈ O x; rw [he]; exact hPoint x⟩
  · intro x
    obtain ⟨p,hp,q,hq,hIso⟩ := hRead x
    have hEq : preimageOpen e (H x) = nestedOpens U (O x) := by
      ext y
      change (e y).val.val ∈ O x ↔ y.val ∈ O x
      rw [he]
    exact canonical_local_comparison e _ L'.2 _ _ _ hEq p q hp hq hIso

end Hironaka.HironakaG8SortedNestedPairDescent
