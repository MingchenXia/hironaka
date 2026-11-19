import Hironaka.Resolution.HironakaG3MixedOrderedSupport
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Resolution.HironakaG3LocalMixedHeadChain
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FiniteMixedBadLocus
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaG3MixedOrderedSupport HironakaG3MixedComponentOpen HironakaEmbeddedAnalyticLocal
  HironakaG3LocalMixedHeadChain HironakaOriginalCanonicalPartListResolution HironakaAdmissibleSequence
  RestrictEmptyTower HironakaBaseChange

/-- The singular points of all labelled irreducible components. -/
def singularObstacles {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X) : List (Set X) :=
  (List.finRange k).map (fun a => (V a).carrier \ regularLocus (n := n) (V a).carrier (V a).dim)

/-- A closed bad support using singular loci and pair intersections only. -/
def mixedBadLocus {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X) : Set X :=
  (⋃ H ∈ singularObstacles V, H) ∪ intersectionSupport V

/-- The actual closed bad set is thin on each original component, even if
the component lies inside the prescribed boundary. -/
theorem mixedBadLocus_closed_and_good {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier) :
    IsClosed (mixedBadLocus V) ∧
      ∀ a, IsLocGoodPart n [] (mixedBadLocus V) (V a).carrier (V a).dim := by
  classical
  have hSingClosed : ∀ H ∈ singularObstacles V, IsClosed H := by
    intro H hH
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hH
    exact HironakaEmbeddedReducible.isClosed_diff_regularLocus (V b).isClosed_carrier (V b).dim
  have hF := intersectionSupport_analytic_and_dense V hDistinct
  have hG : IsClosed (mixedBadLocus V) :=
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hSingClosed).union hF.1.isClosed
  refine ⟨hG,?_⟩
  intro a
  let others : List (Set X) := ((List.finRange k).filter fun b => decide (b ≠ a)).map
    (fun b => (V b).carrier)
  have hOthers : ∀ H ∈ others, IsComplexAnalyticSubset (n := n) H := by
    intro H hH
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hH
    exact (V b).irreducible_carrier.analytic
  have hNot : ∀ H ∈ others, ¬ (V a).carrier ⊆ H := by
    intro H hH
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hH
    have hba : b ≠ a := by simpa using (List.mem_filter.mp hb).2
    exact hDistinct a b hba.symm
  obtain ⟨O,hAvoid,hRegular,hDense⟩ := exists_dense_regular_open_off_list
    (V a).irreducible_carrier (HironakaEmbeddedReducible.subset_closure_regularLocus (V a))
      others hOthers hNot
  have hOtherMem : ∀ b, b ≠ a → (V b).carrier ∈ others := by
    intro b hba
    exact List.mem_map.mpr ⟨b,List.mem_filter.mpr ⟨List.mem_finRange b,by simpa using hba⟩,rfl⟩
  have hAvoidOther : ∀ b, b ≠ a → Disjoint (V b).carrier (O : Set X) :=
    fun b hb => hAvoid _ (hOtherMem b hb)
  have hInside : (V a).carrier ∩ (O : Set X) ⊆ (V a).carrier \ mixedBadLocus V := by
    intro z hz
    refine ⟨hz.1,?_⟩
    rintro (hsing | hinter)
    · obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hsing
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hH
      by_cases hba : b = a
      · subst b
        exact hzH.2 (hRegular z hz.1 hz.2)
      · exact Set.disjoint_left.mp (hAvoidOther b hba) hzH.1 hz.2
    · obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hinter
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hH
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
      by_cases hpa : p.1 = a
      · have hne : p.2 ≠ a := by rw [← hpa]; exact ne_of_gt hp'
        exact Set.disjoint_left.mp (hAvoidOther p.2 hne) hzH.2 hz.2
      · exact Set.disjoint_left.mp (hAvoidOther p.1 hpa) hzH.1 hz.2
  refine ⟨(V a).irreducible_carrier.analytic,hDim a,?_,?_,hDense.trans (closure_mono hInside)⟩
  · intro z hz
    left
    apply mem_iUnion₂.mpr
    exact ⟨(V a).carrier \ regularLocus (n := n) (V a).carrier (V a).dim,
      List.mem_map.mpr ⟨a,List.mem_finRange a,rfl⟩,hz⟩
  · simp

/-- Every distinct pair is contained in the derived bad locus. -/
theorem pair_intersection_subset_mixedBadLocus {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X) {a b : Fin k} (hab : a ≠ b) :
    (V a).carrier ∩ (V b).carrier ⊆ mixedBadLocus V := by
  classical
  intro z hz
  right
  apply mem_iUnion₂.mpr
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨(V a).carrier ∩ (V b).carrier,?_,hz⟩
    apply List.mem_map.mpr
    refine ⟨(a,b),?_,rfl⟩
    simp [hlt]
  · refine ⟨(V b).carrier ∩ (V a).carrier,?_,⟨hz.2,hz.1⟩⟩
    apply List.mem_map.mpr
    refine ⟨(b,a),?_,rfl⟩
    simp [hgt]


/-- Original finite irreducible components directly construct a noncompact
local canonical head separator and its genuine compact-enclosed host. -/
theorem exists_local_irreducible_mixed_head
    {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (i : Fin k) (L : List (Fin k)) (hOrder : ∀ b ∈ L, i < b)
    {B₀ : CMfd.{0} n} (ι : B₀ → X) (hι : IsOpenHoloEmbedding n ι)
    (hKι : ∃ K : Set X, IsCompact K ∧ range ι ⊆ K) :
    ∃ (C : CMfd.{0} n) (T : BlowupTower B₀ C) (Ef : List (Set C))
      (H : CMfd.{0} n) (EH : List (Set H)) (GH : Set H)
      (P : Set X → Set H) (j : C → H),
      CanonicalSeparationChain (E.map (ι ⁻¹' ·)) (ι ⁻¹' (V i).carrier)
        (L.map (fun b => (ι ⁻¹' (V b).carrier,(V b).dim))) T Ef ∧
      CentresOver (ι ⁻¹' mixedBadLocus V) T ∧
      IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' mixedBadLocus V) C T.proj Ef ∧
      IsSNCDivisor n Ef ∧ IsSNCDivisor n EH ∧ IsClosed GH ∧
      IsOpenHoloEmbedding n j ∧ (∃ K : Set H, IsCompact K ∧ range j ⊆ K) ∧
      Ef = EH.map (j ⁻¹' ·) ∧ j ⁻¹' GH = T.proj ⁻¹' (ι ⁻¹' mixedBadLocus V) ∧
      (∀ a, IsLocGoodPart n [] GH (P (V a).carrier) (V a).dim) ∧
      (∀ a b, a ≠ b → P (V a).carrier ∩ P (V b).carrier ⊆ GH) ∧
      (∀ a, strictTransform n T.proj (ι ⁻¹' (V a).carrier) = j ⁻¹' P (V a).carrier) ∧
      (∀ b ∈ L, Disjoint (P (V i).carrier) (P (V b).carrier)) ∧
      ∀ b ∈ L, Disjoint (strictTransform n T.proj (ι ⁻¹' (V i).carrier))
        (strictTransform n T.proj (ι ⁻¹' (V b).carrier)) := by
  let G := mixedBadLocus V
  let L' := L.map fun b => ((V b).carrier,(V b).dim)
  have hData := mixedBadLocus_closed_and_good V hDim hDistinct
  have hGood : ∀ p ∈ L', IsLocGoodPart n [] G p.1 p.2 := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact hData.2 b
  have hSep : ∀ p ∈ L', (V i).carrier ∩ p.1 ⊆ G := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact pair_intersection_subset_mixedBadLocus V (ne_of_lt (hOrder b hb))
  obtain ⟨C,T,Ef,H,EH,GH,P,j,hChain,hOver,hAdm,hEf,hEH,hGH,hj,hKj,hEqE,hEqG,
      hGoodH,_hDisH,hInterH,hStrictH,hSepH,hSepSource⟩ :=
    exists_local_mixed_canonical_ordered_separator L.length E hE G hData.1 (V i).carrier (V i).dim
      (hData.2 i) L' (by simp [L']) hGood hSep ι hι hKι
  refine ⟨C,T,Ef,H,EH,GH,P,j,?_,hOver,hAdm,hEf,hEH,hGH,hj,hKj,hEqE,hEqG,?_,?_,?_,?_,?_⟩
  · simpa only [L',List.map_map,Function.comp_def] using hChain
  · intro a
    exact hGoodH _ _ (hData.2 a)
  · intro a b hab
    exact hInterH _ _ (V a).isClosed_carrier (V b).isClosed_carrier
      (pair_intersection_subset_mixedBadLocus V hab)
  · intro a
    exact hStrictH _ (V a).isClosed_carrier (hData.2 a).2.2.2.2
  · intro b hb
    exact hSepH _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
  · intro b hb
    exact hSepSource _ (List.mem_map.mpr ⟨b,hb,rfl⟩)

end
end Hironaka.HironakaG3FiniteMixedBadLocus
