import Hironaka.Resolution.HironakaOriginalOldBranchHistoryLocality

set_option autoImplicit false

/-!
# Actual test towers are local on their base

The original-branch induction needs testness for an arbitrary original
presentation, reconstructed from its through-point and empty parts. The
local test histories here produce actual ambient testness; an ambient test
history is not a hypothesis.

Blueprint: `hir:original-old-branch-test-open-locality` in
`hironaka-original-old-branch-open-history-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings
  GermIdealPullbackCalculus

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hasNormalCrossings_of_locally_pullback {A : CMfd.{u} n}
    {C : Set A} {E : List (Set A)}
    (h : ∀ x ∈ C, ∃ U : Opens A, x ∈ U ∧
      HasNormalCrossings n ((Subtype.val : U → A) ⁻¹' C)
        (E.map ((Subtype.val : U → A) ⁻¹' ·))) :
    HasNormalCrossings n C E := by
  intro x hx
  obtain ⟨U, hxU, hU⟩ := h x hx
  obtain ⟨S₀, S, hcoord, hcard⟩ := hU ⟨x, hxU⟩ hx
  let k : Fin E.length → Fin (E.map ((Subtype.val : U → A) ⁻¹' ·)).length :=
    Fin.cast (List.length_map _).symm
  refine ⟨S₀, fun i => S (k i), ?_, ?_⟩
  · apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff
      (x := (⟨x, hxU⟩ : U))).mp
    refine NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hcoord (Option.map k) ?_ ?_
    · rintro (_ | i)
      · rfl
      · simp [k]
    · rintro (_ | i) <;> rfl
  · intro i hi
    apply hcard (k i)
    simpa [NormalCrossingsInvariance.get_map_preimage, k] using hi

/-- Actual test histories on an open cover of the original base produce testness of the
same ambient geometric tower. No ambient test-history certificate is supplied. -/
theorem isGeoTestTower_of_open_cover (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (∀ x : X, ∃ U : Opens X, x ∈ U ∧
        IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)) →
      IsGeoTestTower M T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hCover => by
    have hPrev : IsGeoTestTower M T := isGeoTestTower_of_open_cover M hN hI T (by
      intro x
      obtain ⟨U, hxU, hTU⟩ := hCover x
      exact ⟨U, hxU, hTU.1⟩)
    obtain ⟨_hNT, hIT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hPrev
    refine ⟨hPrev, hπ.1, ?_, ?_⟩
    · intro y hy
      obtain ⟨U, hyU, hTU⟩ := hCover (T.proj y)
      have hCU := hTU.2
      rw [geoTransformAlong_restrict U hN hI T hPrev] at hCU
      have hp := hCU.2.1 (show (⟨y, hyU⟩ : openPreimage T U) ∈
        (Subtype.val : openPreimage T U → _) ⁻¹' C from hy)
      rw [cosupp_pullback_val (geoTransformAlong M T)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIT hg)
        (openPreimage T U)] at hp
      exact hp
    · apply hasNormalCrossings_of_locally_pullback
      intro y hy
      obtain ⟨U, hyU, hTU⟩ := hCover (T.proj y)
      have hCU := hTU.2
      rw [geoTransformAlong_restrict U hN hI T hPrev] at hCU
      exact ⟨openPreimage T U, hyU, hCU.2.2⟩

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
