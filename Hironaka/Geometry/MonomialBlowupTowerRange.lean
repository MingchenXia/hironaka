import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Abstract range identities for actual tower chart maps

These elementary lemmas keep chart coverage at the level of exact open
ranges. Their consumers need not evaluate inverse scheme isomorphisms on
points of an increasingly dependent global tower.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.MonomialBlowupTowerRange

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Composing an actual two-chart open cover gives exactly the outer open range. -/
theorem opensRange_comp_sup_eq {T U V Y : Scheme.{u}}
    (u : U ⟶ T) (v : V ⟶ T) (k : T ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsOpenImmersion k]
    (h : u.opensRange ⊔ v.opensRange = ⊤) :
    (u ≫ k).opensRange ⊔ (v ≫ k).opensRange = k.opensRange := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_comp]
  apply SetLike.coe_injective
  change k '' (u.opensRange : Set T) ∪ k '' (v.opensRange : Set T) = Set.range k
  rw [← Set.image_union]
  have hs : (u.opensRange : Set T) ∪ (v.opensRange : Set T) = Set.univ :=
    congrArg (fun W : T.Opens => (W : Set T)) h
  rw [hs, Set.image_univ]

/-- Exact inverse-image ranges replace an actual old cover by actual new chart maps. -/
theorem covers_of_preimage_ranges {X Y : Scheme.{u}} {ι : Type v}
    {F : ι → Scheme.{u}} {C U V : Scheme.{u}}
    (p : Y ⟶ X) (f : ∀ i, F i ⟶ X) (g : C ⟶ X)
    (f' : ∀ i, F i ⟶ Y) (u : U ⟶ Y) (v : V ⟶ Y)
    [∀ i, IsOpenImmersion (f i)] [IsOpenImmersion g]
    [∀ i, IsOpenImmersion (f' i)] [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, (∃ i, x ∈ (f i).opensRange) ∨ x ∈ g.opensRange)
    (hf : ∀ i, (f' i).opensRange = p ⁻¹ᵁ (f i).opensRange)
    (hg : u.opensRange ⊔ v.opensRange = p ⁻¹ᵁ g.opensRange) :
    ∀ y : Y, (∃ i, y ∈ (f' i).opensRange) ∨ y ∈ u.opensRange ∨ y ∈ v.opensRange := by
  intro y
  rcases hc (p y) with ⟨i, hi⟩ | hc
  · left
    refine ⟨i, ?_⟩
    rw [hf]
    exact hi
  · right
    have hy : y ∈ u.opensRange ⊔ v.opensRange := by
      rw [hg]
      exact hc
    exact hy

end Hironaka.Geometry.MonomialBlowupTowerRange
