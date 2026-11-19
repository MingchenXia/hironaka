import Hironaka.Geometry.ChowLemmaAffineCover

/-!
# An actual finite affine cover subordinate to actual base affine opens

Every source point chooses an actual base affine neighbourhood and an actual
source affine neighbourhood contained in its preimage. Compactness extracts
the actual finite cover while preserving all original containments.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- Actual nonempty affine source patches, actual affine base patches,
actual containments, and an actual finite source cover are produced internally. -/
theorem exists_finite_subordinate_affine_cover
    (p : X ⟶ S) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens) (V : Fin n → S.affineOpens),
      (∀ i, ((U i).1 : Set X).Nonempty) ∧
      (∀ i, (U i).1 ≤ p ⁻¹ᵁ (V i).1) ∧ (⨆ i, (U i).1) = ⊤ := by
  classical
  have hpatch (x : X) :
      ∃ (U : X.affineOpens) (V : S.affineOpens),
        x ∈ U.1 ∧ U.1 ≤ p ⁻¹ᵁ V.1 := by
    let V : S.affineOpens :=
      ⟨(S.affineCover.f (S.affineCover.idx (p x))).opensRange, isAffineOpen_opensRange _⟩
    have hx : x ∈ p ⁻¹ᵁ V.1 := S.affineCover.covers (p x)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨⟨U, hU⟩, V, hxU, hUV⟩
  choose U V hxU hUV using hpatch
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => ((U x).1 : Set X)) (fun x => (U x).1.isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let L := t.toList
  refine ⟨L.length, fun i => U (L.get i), fun i => V (L.get i),
    fun i => ⟨L.get i, hxU (L.get i)⟩, fun i => hUV (L.get i), top_le_iff.mp ?_⟩
  intro x _
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr ha : a ∈ L)
  refine Opens.mem_iSup.mpr ⟨i, ?_⟩
  change x ∈ (U (t.toList.get i)).1
  rw [hi]
  exact hxa

end Hironaka.Geometry.RelativeChow
