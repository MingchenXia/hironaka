import Hironaka.Resolution.HironakaG3MixedOrderedHead
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedOrderedSeparation
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaAdmissibleCalculus HironakaOriginalNCOldStratumStrictEquality
  HironakaMixedDimensionalBoundaryFiniteSeparation HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalOrderedResolution HironakaG3MixedOrderedHead

/-- Ordered separator provenance, with each head's literal canonical chain
and its full boundary retained before the next head. -/
inductive CanonicalMixedSeparation {n : ℕ} :
    {X : CMfd.{0} n} → (E : List (Set X)) → (L : List (Set X × ℕ)) →
      {Y : CMfd.{0} n} → BlowupTower X Y → List (Set Y) → Prop
  | nil {X : CMfd.{0} n} {E : List (Set X)} :
      CanonicalMixedSeparation E [] .refl E
  | cons {X Y Z : CMfd.{0} n} {E : List (Set X)} {A : Set X} {d : ℕ}
      {L : List (Set X × ℕ)} {E₁ : List (Set Y)} {E₂ : List (Set Z)}
      (T : BlowupTower X Y) (S : BlowupTower Y Z)
      (hHead : CanonicalSeparationChain E A L T E₁)
      (hTail : CanonicalMixedSeparation E₁ (strictParts T L) S E₂) :
      CanonicalMixedSeparation E ((A,d)::L) (T.append S) E₂

/-- Every ordered finite subfamily has an actual canonical separator tree;
the terminal labelled strict transforms are pairwise disjoint. -/
theorem exists_compact_ordered_mixed_separation {n k : ℕ} :
    ∀ (L : List (Fin k)), L.Pairwise (· < ·) →
      ∀ {X : CMfd.{0} n} (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
        (_hCompact : ∀ a, IsCompact (V a).carrier) (_hDim : ∀ a, (V a).dim < n)
        (_hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
        (E : List (Set X)) (_hE : IsSNCDivisor n E),
        ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
          (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y) (E' : List (Set Y)),
          CanonicalMixedSeparation E (L.map fun a => ((V a).carrier,(V a).dim)) T E' ∧
          IsGeoTestTower (boundaryGeometry E) T ∧ E' = (geoTransformAlong (boundaryGeometry E) T).E ∧
          IsSNCDivisor n E' ∧
          (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
          (∀ a, (V' a).dim = (V a).dim) ∧ (∀ a, IsCompact (V' a).carrier) ∧
          (∀ a b, a ≠ b → ¬ (V' a).carrier ⊆ (V' b).carrier) ∧
          (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
          ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (V' a).carrier (V' b).carrier := by
  intro L
  induction L with
  | nil =>
    intro hOrder X V hCompact hDim hDistinct E hE
    refine ⟨X,.refl,V,E,.nil,trivial,rfl,hE,?_,?_,hCompact,hDistinct,?_,?_⟩
    · intro a
      simp [strictTransform,exceptionalLocus_id,(V a).isClosed_carrier.closure_eq]
    · intro a
      rfl
    · intro a
      simp [BlowupTower.proj]
    · intro a ha
      exact False.elim (List.not_mem_nil ha)
  | cons i L ih =>
    intro hOrder X V hCompact hDim hDistinct E hE
    have hLater : ∀ b ∈ L, i < b := (List.pairwise_cons.mp hOrder).1
    have hTailOrder : L.Pairwise (· < ·) := (List.pairwise_cons.mp hOrder).2
    obtain ⟨Y,T,V₁,E₁,hHead,hDT,hE₁,hSNC₁,hV₁,hDim₁,hCompact₁,hDistinct₁,hProj₁,hHeadDis⟩ :=
      exists_compact_ordered_head_chain i L V hCompact hDim hDistinct E hE hLater
    have hDim₁' : ∀ a, (V₁ a).dim < n := fun a => (hDim₁ a) ▸ hDim a
    obtain ⟨Z,S,V₂,E₂,hTail,hDS,hE₂,hSNC₂,hV₂,hDim₂,hCompact₂,hDistinct₂,hProj₂,hDis₂⟩ :=
      ih hTailOrder V₁ hCompact₁ hDim₁' hDistinct₁ E₁ hSNC₁
    have hMap : (L.map fun b => ((V₁ b).carrier,(V₁ b).dim)) =
        strictParts T (L.map fun b => ((V b).carrier,(V b).dim)) := by
      simp only [strictParts,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro b _hb
      rw [hV₁ b,hDim₁ b]
    rw [hMap] at hTail
    have hTree : CanonicalMixedSeparation E ((i :: L).map fun a => ((V a).carrier,(V a).dim))
        (T.append S) E₂ := .cons T S hHead hTail
    have hCurrent : IsGeoTestTower (geoTransformAlong (boundaryGeometry E) T) S := by
      rw [boundaryGeometry_geoTransformAlong E T,← hE₁]
      exact hDS
    have hAppend : IsGeoTestTower (boundaryGeometry E) (T.append S) :=
      (isGeoTestTower_append_iff (boundaryGeometry E) T S).mpr ⟨hDT,hCurrent⟩
    have hEnd : E₂ = (geoTransformAlong (boundaryGeometry E) (T.append S)).E := by
      rw [hE₂,geoTransformAlong_append,boundaryGeometry_geoTransformAlong E T,← hE₁]
    refine ⟨Z,T.append S,V₂,E₂,hTree,hAppend,hEnd,hSNC₂,?_,?_,hCompact₂,hDistinct₂,?_,?_⟩
    · intro a
      rw [hV₂ a,hV₁ a,BlowupTower.proj_append,
        StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj]
    · intro a
      exact (hDim₂ a).trans (hDim₁ a)
    · intro a
      rw [BlowupTower.proj_append,Set.image_comp,hProj₂ a,hProj₁ a]
    · intro a ha b hb hab
      rcases List.mem_cons.mp ha with hEqA | hTailA
      · subst a
        rcases List.mem_cons.mp hb with hEqB | hTailB
        · subst b
          exact False.elim (hab rfl)
        · rw [hV₂ i,hV₂ b]
          exact Disjoint.mono
            (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ i).isClosed_carrier)
            (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ b).isClosed_carrier)
            ((hHeadDis b hTailB).preimage S.proj)
      · rcases List.mem_cons.mp hb with hEqB | hTailB
        · subst b
          rw [hV₂ a,hV₂ i]
          exact Disjoint.mono
            (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ a).isClosed_carrier)
            (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ i).isClosed_carrier)
            ((hHeadDis a hTailA).symm.preimage S.proj)
        · exact hDis₂ a hTailA b hTailB hab

/-- An internally ordered complete separator tree for a finite compact
family, retaining every actual canonical head chain and boundary. -/
theorem exists_compact_full_ordered_mixed_separation {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hCompact : ∀ a, IsCompact (V a).carrier) (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
      (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y) (E' : List (Set Y)),
      CanonicalMixedSeparation E ((List.finRange k).map fun a => ((V a).carrier,(V a).dim)) T E' ∧
      IsGeoTestTower (boundaryGeometry E) T ∧ E' = (geoTransformAlong (boundaryGeometry E) T).E ∧
      IsSNCDivisor n E' ∧
      (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
      (∀ a, (V' a).dim = (V a).dim) ∧ (∀ a, IsCompact (V' a).carrier) ∧
      (∀ a b, a ≠ b → ¬ (V' a).carrier ⊆ (V' b).carrier) ∧
      (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
      ∀ a b, a ≠ b → Disjoint (V' a).carrier (V' b).carrier := by
  obtain ⟨Y,T,V',E',hTree,hTest,hE',hSNC,hCarrier,hDim',hCompact',hDistinct',hProj,hDis⟩ :=
    exists_compact_ordered_mixed_separation (List.finRange k) (List.pairwise_lt_finRange k)
      V hCompact hDim hDistinct E hE
  refine ⟨Y,T,V',E',hTree,hTest,hE',hSNC,hCarrier,hDim',hCompact',hDistinct',hProj,?_⟩
  intro a b hab
  exact hDis a (List.mem_finRange a) b (List.mem_finRange b) hab

end
end Hironaka.HironakaG3MixedOrderedSeparation
