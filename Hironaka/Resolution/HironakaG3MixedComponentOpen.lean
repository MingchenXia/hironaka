import Hironaka.Resolution.HironakaG3CompactStratum
import Hironaka.Analytic.ClosureDifferenceAnalytic

/-! A dense regular open of an irreducible analytic component avoiding a finite
family of other analytic components and boundary members. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedComponentOpen
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3CompactStratum ClosureDifferenceAnalytic

variable {n : ℕ} {X : CMfd.{0} n}

/-- A finite union of the given analytic subsets is analytic. -/
theorem analytic_list_union (E : List (Set X))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H) :
    IsComplexAnalyticSubset (n := n) (⋃ H ∈ E, H) := by
  induction E with
  | nil => simp
  | cons H E ih =>
    have hUnion : (⋃ K ∈ H :: E, K) = H ∪ ⋃ K ∈ E, K := by ext x; simp
    rw [hUnion]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hE H (List.mem_cons_self ..)) (ih (fun K hK => hE K (List.mem_cons_of_mem _ hK)))

/-- An irreducible analytic subset covered by finitely many analytic subsets
is contained in one of them. -/
theorem irreducible_subset_list_union {C : Set X}
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (E : List (Set X))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H)
    (hCover : C ⊆ ⋃ H ∈ E, H) : ∃ H ∈ E, C ⊆ H := by
  induction E with
  | nil =>
    obtain ⟨x, hx⟩ := hC.nonempty
    have := hCover hx
    simp at this
  | cons H E ih =>
    have hH := hE H (List.mem_cons_self ..)
    have hRest : ∀ K ∈ E, IsComplexAnalyticSubset (n := n) K :=
      fun K hK => hE K (List.mem_cons_of_mem _ hK)
    have hRestA := analytic_list_union E hRest
    have hSplit : C = (C ∩ H) ∪ (C ∩ ⋃ K ∈ E, K) := by
      ext x
      constructor
      · intro hx
        have hu := hCover hx
        simp only [List.mem_cons, mem_iUnion, exists_prop] at hu
        obtain ⟨K, (rfl | hK), hxK⟩ := hu
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr ⟨hx, mem_iUnion.mpr ⟨K, mem_iUnion.mpr ⟨hK, hxK⟩⟩⟩
      · rintro (h | h) <;> exact h.1
    rcases hC.eq_left_or_eq_right (hC.analytic.inter hH) (hC.analytic.inter hRestA)
      inter_subset_left inter_subset_left hSplit with h | h
    · exact ⟨H, List.mem_cons_self .., fun x hx => (h ▸ hx : x ∈ C ∩ H).2⟩
    · obtain ⟨K, hK, hCK⟩ := ih hRest (fun x hx => (h ▸ hx : x ∈ C ∩ ⋃ K ∈ E, K).2)
      exact ⟨K, List.mem_cons_of_mem _ hK, hCK⟩

/-- An irreducible component is dense outside finitely many analytic sets,
provided none contains it. -/
theorem irreducible_dense_off_list {C : Set X}
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (E : List (Set X))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H)
    (hNot : ∀ H ∈ E, ¬ C ⊆ H) : C ⊆ closure (C \ ⋃ H ∈ E, H) := by
  let Z : Set X := ⋃ H ∈ E, H
  have hZ : IsComplexAnalyticSubset (n := n) Z := analytic_list_union E hE
  have hNotZ : ¬ C ⊆ Z := by
    intro hCover
    obtain ⟨H,hHE,hCH⟩ := irreducible_subset_list_union hC E hE hCover
    exact hNot H hHE hCH
  have hCl := isComplexAnalyticSubset_closure_diff hC.analytic hZ
  have hSub : closure (C \ Z) ⊆ C := closure_minimal sdiff_subset hC.analytic.isClosed
  have hSplit : C = (C ∩ Z) ∪ closure (C \ Z) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hz : x ∈ Z
      · exact Or.inl ⟨hx,hz⟩
      · exact Or.inr (subset_closure ⟨hx,hz⟩)
    · exact union_subset inter_subset_left hSub
  rcases hC.eq_left_or_eq_right (hC.analytic.inter hZ) hCl inter_subset_left hSub hSplit with h | h
  · exact False.elim (hNotZ (fun x hx => (h ▸ hx : x ∈ C ∩ Z).2))
  · exact h.subset

/-- A fixed-dimension regular open can avoid finitely many other analytic
components or boundary members without losing any point of C in closure. -/
theorem exists_dense_regular_open_off_list {C : Set X}
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) {d : ℕ}
    (hPure : C ⊆ closure (regularLocus (n := n) C d)) (E : List (Set X))
    (hE : ∀ H ∈ E, IsComplexAnalyticSubset (n := n) H)
    (hNot : ∀ H ∈ E, ¬ C ⊆ H) :
    ∃ O : Opens X, (∀ H ∈ E, Disjoint H (O : Set X)) ∧
      (∀ x ∈ C, x ∈ O → RegularAtDim (n := n) C x d) ∧
      C ⊆ closure (C ∩ (O : Set X)) := by
  let Z : Set X := ⋃ H ∈ E, H
  have hZ : IsClosed Z := (analytic_list_union E hE).isClosed
  have hBad : IsClosed (C \ regularLocus (n := n) C d ∪ Z) :=
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hC.analytic.isClosed d).union hZ
  let O : Opens X := ⟨(C \ regularLocus (n := n) C d ∪ Z)ᶜ, hBad.isOpen_compl⟩
  refine ⟨O,?_,?_,?_⟩
  · intro H hHE
    apply disjoint_left.mpr
    intro x hxH hxO
    exact hxO (Or.inr (mem_iUnion.mpr ⟨H, mem_iUnion.mpr ⟨hHE,hxH⟩⟩))
  · intro x hxC hxO
    by_contra h
    exact hxO (Or.inl ⟨hxC,h⟩)
  · exact HironakaEmbeddedBoundary.subset_closure_inter_compl hPure hZ
      (irreducible_dense_off_list hC E hE hNot)


/-- A compact irreducible target in one selected proper stratum admits a
non-erasing full-boundary ambient history while its lower open avoids a
finite family of other analytic components and boundary members. -/
theorem exists_compact_irreducible_stratum_resolution
    {d t : ℕ} {X : CMfd.{0} (d+t)} {N : Set X} (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) (ht : 0 < t)
    {E B : List (Set X)} (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (hTrans : IsTransverse (d+t) N B)
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    let V : Set N := (Subtype.val : N → X) ⁻¹' W
    let B₀ := B.map fun H => (Subtype.val : N → X) ⁻¹' H
    IsComplexAnalyticallyIrreducible (n := d) V → IsCompact V → interior V = ∅ →
    IsSNCDivisor d B₀ →
    ∀ (m : ℕ), V ⊆ closure (regularLocus (n := d) V m) →
    ∀ (F : List (Set N)), (∀ H ∈ F, IsComplexAnalyticSubset (n := d) H) →
      (∀ H ∈ F, ¬ V ⊆ H) → (∀ H ∈ B₀, H ∈ F) →
      ∃ (O : Opens (CMfd.of (n := d) N)) (Q : CMfd.{0} d)
        (T : BlowupTower (CMfd.of (n := d) N) Q)
        (Y : CMfd.{0} (d+t)) (U : BlowupTower X Y) (η : Q → Y),
        (∀ H ∈ F, Disjoint H (O : Set N)) ∧
        RestrictEmptyTower.CentresAvoid O T ∧
        CoupledHistory N B (vanishingIdeal (n := d+t) W) (Subtype.val : N → X)
          (fullMarked B₀ (vanishingIdeal (n := d) V)) T U η ∧
        IsGeoTestTower (fullMarked E (vanishingIdeal (n := d+t) W)) U ∧
        HasNormalCrossings (d+t) (strictAlong U W)
          (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E ∧
        U.proj '' strictAlong U W = W := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  dsimp only
  intro hV hK hint hB m hPure F hF hNot hSub
  obtain ⟨O,hAvoid,hreg,hdense⟩ := exists_dense_regular_open_off_list
    (X := CMfd.of (n := d) N) hV hPure F hF hNot
  obtain ⟨Q,T,hT,hTAvoid,hSmooth,hDim,hNC,hImage⟩ :=
    exists_compact_lower_tower_with_nonerasure (X := CMfd.of (n := d) N)
      (W := (Subtype.val : N → X) ⁻¹' W) (d := m) hV.analytic hK hint hB O
      (fun H hH => hAvoid H (hSub H hH)) hreg hdense
  obtain ⟨Y,U,η,hU,hLength,hHist,hUNC,hProj⟩ :=
    HironakaG3StratumTerminalNC.exists_full_boundary_history_with_terminal_nc
      hNc hN ht hE hBsub hOmitted hTrans hWa hWN T hT hNC
  have hW : (Subtype.val : N → X) '' ((Subtype.val : N → X) ⁻¹' W) = W := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x,hWN hx⟩, hx, rfl⟩
  refine ⟨O,Q,T,Y,U,η,hAvoid,hTAvoid,hHist,hU,hUNC,?_⟩
  rw [hProj, hImage, hW]

end
end Hironaka.HironakaG3MixedComponentOpen
