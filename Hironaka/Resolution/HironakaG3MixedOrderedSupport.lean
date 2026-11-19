import Hironaka.Resolution.HironakaG3MixedOrderedComparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedOrderedSupport
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaAdmissibleCalculus HironakaAdmissibleSequence HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaOriginalCanonicalSumSeparation HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalOrderedResolution HironakaG3MixedOrderedSeparation HironakaG3MixedComponentOpen

private theorem centresOver_mono {n : ℕ} {X : CMfd.{0} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centresOver_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

/-- Every actual centre in a canonical head chain lies over the original
head/tail intersections. -/
theorem head_chain_centresOver {n : ℕ} {X Y : CMfd.{0} n}
    {E : List (Set X)} {A F : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X Y} {Ef : List (Set Y)}
    (h : CanonicalSeparationChain E A L T Ef)
    (hClosed : ∀ p ∈ L, IsClosed p.1)
    (hCover : ∀ p ∈ L, A ∩ p.1 ⊆ F) : CentresOver F T := by
  induction h with
  | nil => trivial
  | @cons X E A B e L Y Z T S hAa hBa hM hc hr Ef hs ih =>
    let M := sumMarkedIdeal A B E
    have hcos : M.cosupp = A ∩ B := by
      calc
        _ = M.ideal.zeroLocus := cosupp_univ_one hM.isWellFormed.isCoherent
        _ = A ∩ B := HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
    have hOverSmall : CentresOver (A ∩ B) T := by
      have hOver := centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hr.1
      rwa [hcos] at hOver
    have hOver : CentresOver F T := centresOver_mono (hCover (B,e) (List.mem_cons_self ..)) T hOverSmall
    have hCoverTail : ∀ p ∈ L.map (fun p => (strictTransform n T.proj p.1,p.2)),
        strictTransform n T.proj A ∩ p.1 ⊆ T.proj ⁻¹' F := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      intro z hz
      apply hCover q (List.mem_cons_of_mem _ hq)
      exact ⟨strictTransform_subset_preimage T.contMDiff_proj.continuous hAa.isClosed hz.1,
        strictTransform_subset_preimage T.contMDiff_proj.continuous
          (hClosed q (List.mem_cons_of_mem _ hq)) hz.2⟩
    have hClosedTail : ∀ p ∈ L.map (fun p => (strictTransform n T.proj p.1,p.2)), IsClosed p.1 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact isClosed_closure
    exact (centresOver_append_iff F T S).mpr ⟨hOver,ih hClosedTail hCoverTail⟩

/-- Every centre of an actual ordered separator tree lies over the union of
the original pairwise component intersections. -/
theorem mixed_tree_centresOver {n : ℕ} {X Y : CMfd.{0} n}
    {E : List (Set X)} {L : List (Set X × ℕ)} {F : Set X}
    {T : BlowupTower X Y} {Ef : List (Set Y)}
    (h : CanonicalMixedSeparation E L T Ef)
    (hClosed : ∀ p ∈ L, IsClosed p.1)
    (hPair : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ F)) : CentresOver F T := by
  induction h with
  | nil => trivial
  | @cons X Y Z E A d L E₁ E₂ T S hHead hTail ih =>
    have hClosedL : ∀ p ∈ L, IsClosed p.1 := fun p hp => hClosed p (List.mem_cons_of_mem _ hp)
    have hHeadOver : CentresOver F T :=
      head_chain_centresOver hHead hClosedL (List.pairwise_cons.mp hPair).1
    have hPairL : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ F) := (List.pairwise_cons.mp hPair).2
    have hPairTail : (strictParts T L).Pairwise (fun p q => p.1 ∩ q.1 ⊆ T.proj ⁻¹' F) := by
      simp only [strictParts,List.pairwise_map]
      apply hPairL.imp_of_mem
      intro p q hp hq hpq z hz
      exact hpq ⟨strictTransform_subset_preimage T.contMDiff_proj.continuous (hClosedL p hp) hz.1,
        strictTransform_subset_preimage T.contMDiff_proj.continuous (hClosedL q hq) hz.2⟩
    have hClosedTail : ∀ p ∈ strictParts T L, IsClosed p.1 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact isClosed_closure
    exact (centresOver_append_iff F T S).mpr ⟨hHeadOver,ih hClosedTail hPairTail⟩


/-- The finite list of original labelled pair intersections. -/
def intersectionObstacles {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X) : List (Set X) := by
  classical
  exact ((Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).toList).map
    (fun p => (V p.1).carrier ∩ (V p.2).carrier)

/-- The original support of all pairwise mixed-component intersections. -/
def intersectionSupport {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X) : Set X :=
  ⋃ H ∈ intersectionObstacles V, H

/-- This support is analytic; every incomparable irreducible component is
dense away from it. -/
theorem intersectionSupport_analytic_and_dense {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier) :
    IsComplexAnalyticSubset (n := n) (intersectionSupport V) ∧
      ∀ a, (V a).carrier ⊆ closure ((V a).carrier \ intersectionSupport V) := by
  classical
  have hObs : ∀ H ∈ intersectionObstacles V, IsComplexAnalyticSubset (n := n) H := by
    intro H hH
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
    exact (V p.1).irreducible_carrier.analytic.inter (V p.2).irreducible_carrier.analytic
  refine ⟨analytic_list_union (intersectionObstacles V) hObs,?_⟩
  intro a
  apply irreducible_dense_off_list (V a).irreducible_carrier (intersectionObstacles V) hObs
  intro H hH
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
  intro hSub
  by_cases ha : a = p.1
  · subst a
    exact hDistinct p.1 p.2 (ne_of_lt hp') (hSub.trans inter_subset_right)
  · exact hDistinct a p.1 ha (hSub.trans inter_subset_left)

/-- A full actual ordered tree is supported over the original pairwise
intersection locus, independently of its chosen canonical stages. -/
theorem full_mixed_tree_centresOver_intersections {n k : ℕ} {X Y : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    {E : List (Set X)} {T : BlowupTower X Y} {Ef : List (Set Y)}
    (h : CanonicalMixedSeparation E ((List.finRange k).map fun a => ((V a).carrier,(V a).dim)) T Ef) :
    CentresOver (intersectionSupport V) T := by
  classical
  apply mixed_tree_centresOver h
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact (V a).isClosed_carrier
  · simp only [List.pairwise_map]
    apply (List.pairwise_lt_finRange k).imp
    intro a b hab z hz
    apply mem_iUnion₂.mpr
    refine ⟨(V a).carrier ∩ (V b).carrier,?_,hz⟩
    apply List.mem_map.mpr
    refine ⟨(a,b),?_,rfl⟩
    simp [hab]

end
end Hironaka.HironakaG3MixedOrderedSupport
