import Hironaka.Resolution.HironakaOriginalOldBranchTestLocality
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false

/-!
# Adding the original through-point and empty branch blocks

For any given original SNC list, the actual highest-count centre condition
internally makes every local original branch either empty or containing the
local centre carrier. Whole-history boundary comparison and open locality
then produce the augmented test history. No augmented history is an input.

These are the source-geometric helpers for
`hir:original-old-branch-highest-phase-universal-history`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalOldBranchOpenHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings DropMembers
  HomogenizedGlueingTower MemberInterTowerAlong BoundaryCount RestrictEmptyTower
  CoefficientIdealRestriction

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Restriction preserves the entire added original branch block and the entire retained list. -/
theorem pullback_add_old_boundary (M : MarkedIdeal n X) (B : List (Set X)) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : U → X)
        ({ M with E := B ++ M.E } : MarkedIdeal n X) =
      ({ MarkedIdeal.pullback (Subtype.val : U → X) M with
        E := B.map ((Subtype.val : U → X) ⁻¹' ·) ++
          (MarkedIdeal.pullback (Subtype.val : U → X) M).E } : MarkedIdeal n U) := by
  simp only [MarkedIdeal.pullback, List.map_append]

/-- An old branch which is empty or contains the source of every centre can be added
to the actual original test tower, with its literal position retained. -/
theorem isGeoTestTower_add_branches_of_containing_or_empty (M : MarkedIdeal n X)
    (B : List (Set X))
    (hWF : ({ M with E := B ++ M.E } : MarkedIdeal n X).IsWellFormed)
    {S : Set X} (hB : ∀ A ∈ B, A = ∅ ∨ S ⊆ A)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (hTS : CentresIn S T) :
    IsGeoTestTower ({ M with E := B ++ M.E } : MarkedIdeal n X) T := by
  classical
  let D := B.filter (fun A => A = ∅) ++ M.E
  let L : MarkedIdeal n X := { M with E := D }
  have hsub : ∀ A ∈ M.E, A ∈ L.E := fun A hA => List.mem_append_right _ hA
  have hdis : ∀ A ∈ L.E, A ∉ M.E → IsClosed A ∧ Disjoint L.cosupp A := by
    intro A hA hnot
    rcases List.mem_append.mp hA with hA | hA
    · have hEmpty : A = ∅ := by simpa using (List.mem_filter.mp hA).2
      rw [hEmpty]
      exact ⟨isClosed_empty, disjoint_empty _⟩
    · exact False.elim (hnot hA)
  have hTL : IsGeoTestTower L T :=
    ((isGeoTestTower_withE_iff_of_disjoint L hWF.isClosedSubmanifold_N hWF.isCoherent
      (E' := M.E) hsub hdis T).1).mp hT
  have hDsub : ∀ A ∈ D, A ∈ B ++ M.E := by
    intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact List.mem_append_left _ (List.mem_filter.mp hA).1
    · exact List.mem_append_right _ hA
  have hContaining : ∀ A ∈ B ++ M.E, A ∉ D → S ⊆ A := by
    intro A hA hnot
    rcases List.mem_append.mp hA with hA | hA
    · rcases hB A hA with hEmpty | hContaining
      · exact False.elim (hnot (List.mem_append_left _
          (List.mem_filter.mpr ⟨hA, by simpa using hEmpty⟩)))
      · exact hContaining
    · exact False.elim (hnot (List.mem_append_right _ hA))
  exact ((isGeoTestTower_withE_iff_of_centresIn
    ({ M with E := B ++ M.E } : MarkedIdeal n X) hWF
    (E' := D) (S := S) hDsub hContaining T hTS).1).mp hTL

/-- The actual centre-carrier condition restricts, retaining every step, including empty steps. -/
theorem centresIn_restrict_original (U : Opens X) {S : Set X} :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresIn S T →
      CentresIn ((Subtype.val : U → X) ⁻¹' S) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨centresIn_restrict_original U T hT.1, ?_⟩
    intro p hp
    rw [strictAlong_restrict U T S]
    exact hT.2 hp

private theorem centresOver_of_centresIn_original {S : Set X} (hS : IsClosed S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresIn S T → CentresOver S T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, hT =>
    ⟨centresOver_of_centresIn_original hS T hT.1,
      fun _ hp => strictAlong_subset_preimage T hS (hT.2 hp)⟩

/-- The genuine highest-count geometry of a fixed original SNC branch list produces
its whole augmented test history. There is no incoming augmented-history hypothesis. -/
theorem isGeoTestTower_add_snc_branches_of_centresIn_maxcount (M : MarkedIdeal n X)
    (B : List (Set X))
    (hWF : ({ M with E := B ++ M.E } : MarkedIdeal n X).IsWellFormed)
    (r : ℕ) (hbound : ∀ x : X, boundaryCount B x ≤ r)
    {S : Set X} (hS : IsClosed S) (hScount : ∀ x ∈ S, r ≤ boundaryCount B x)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (hTS : CentresIn S T) :
    IsGeoTestTower ({ M with E := B ++ M.E } : MarkedIdeal n X) T := by
  classical
  let A : MarkedIdeal n X := { M with E := B ++ M.E }
  have hClosed : ∀ C ∈ B, IsClosed C :=
    fun C hC => hWF.isSNCDivisor.1 C (List.mem_append_left _ hC)
  have hOver := centresOver_of_centresIn_original hS T hTS
  apply isGeoTestTower_of_open_cover A hWF.isClosedSubmanifold_N hWF.isCoherent T
  intro x
  by_cases hxS : x ∈ S
  · let Wset : Set X := ⋂ i : Fin B.length,
      if x ∈ B.get i then univ else (B.get i)ᶜ
    have hWset : IsOpen Wset := isOpen_iInter_of_finite fun i => by
      by_cases hi : x ∈ B.get i
      · rw [if_pos hi]
        exact isOpen_univ
      · rw [if_neg hi]
        exact (hClosed _ (List.get_mem B i)).isOpen_compl
    let W : Opens X := ⟨Wset, hWset⟩
    have hxW : x ∈ W := mem_iInter.mpr fun i => by
      by_cases hi : x ∈ B.get i
      · rw [if_pos hi]
        exact mem_univ _
      · rw [if_neg hi]
        exact hi
    let MU := MarkedIdeal.pullback (Subtype.val : W → X) M
    let BW := B.map ((Subtype.val : W → X) ⁻¹' ·)
    let SW := (Subtype.val : W → X) ⁻¹' S
    let through : X → Finset (Fin B.length) :=
      fun z => Finset.univ.filter (fun i => z ∈ B.get i)
    have hSubset (y : W) : through y.val ⊆ through x := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      by_contra hxi
      have hyW := mem_iInter.mp y.property i
      rw [if_neg hxi] at hyW
      exact hyW (Finset.mem_filter.mp hi).2
    have hEqual (y : W) (hyS : y ∈ SW) : through y.val = through x := by
      apply Finset.eq_of_subset_of_card_le (hSubset y)
      exact (hbound x).trans (hScount y.val hyS)
    have hBW : ∀ C ∈ BW, C = ∅ ∨ SW ⊆ C := by
      intro C hC
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hD
      by_cases hxi : x ∈ B.get i
      · right
        intro y hyS
        have hi : i ∈ through y.val := by
          rw [hEqual y hyS]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩
        exact (Finset.mem_filter.mp hi).2
      · left
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hyW := mem_iInter.mp y.property i
        rw [if_neg hxi] at hyW
        exact hyW hy
    have hPB := pullback_add_old_boundary M B W
    have hWFU := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hWF W
    rw [hPB] at hWFU
    have hTU : IsGeoTestTower MU (restrict W T) :=
      isGeoTestTower_restrict (𝔪 := M) W hWF.isClosedSubmanifold_N hWF.isCoherent T hT
    have hTSU := centresIn_restrict_original W T hTS
    refine ⟨W, hxW, ?_⟩
    rw [hPB]
    exact isGeoTestTower_add_branches_of_containing_or_empty MU BW hWFU hBW
      (restrict W T) hTU hTSU
  · let W : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩
    have hDisjoint : Disjoint (W : Set X) S := disjoint_compl_left
    have hEmpty := isEmptyTower_restrict_of_centresOver W hDisjoint T hOver
    exact ⟨W, hxS, ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower
      (MarkedIdeal.pullback (Subtype.val : W → X) A) (restrict W T) hEmpty⟩

end

end Hironaka.HironakaOriginalOldBranchOpenHistory
