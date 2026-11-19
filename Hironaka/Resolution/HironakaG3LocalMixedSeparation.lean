import Hironaka.Resolution.HironakaG3FiniteMixedBadLocus
import Hironaka.Resolution.HironakaG3MixedOrderedSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocalMixedSeparation
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaBaseChange
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaEmbeddedAnalyticLocal HironakaOriginalCanonicalPartListResolution
  HironakaOriginalCanonicalOrderedResolution HironakaG3LocalMixedHeadChain
  HironakaG3MixedOrderedSeparation HironakaG3FiniteMixedBadLocus

/-- Locally good parts, without boundary avoidance, produce an actual local
ordered mixed-separation tree on any compact-enclosed open source. -/
theorem exists_local_mixed_separation_tree {n : ℕ} (ℓ : ℕ) :
    ∀ {X : CMfd.{0} n} (E : List (Set X)) (_hE : IsSNCDivisor n E)
      (G : Set X) (_hG : IsClosed G) (L : List (Set X × ℕ)), L.length = ℓ →
      (∀ p ∈ L, IsLocGoodPart n [] G p.1 p.2) →
      L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
      ∀ {B₀ : CMfd.{0} n} (ι : B₀ → X), IsOpenHoloEmbedding n ι →
      (∃ K : Set X, IsCompact K ∧ range ι ⊆ K) →
      ∃ (D : CMfd.{0} n) (T : BlowupTower B₀ D) (Ef : List (Set D)),
        CanonicalMixedSeparation (E.map (ι ⁻¹' ·)) (L.map fun p => (ι ⁻¹' p.1,p.2)) T Ef ∧
        CentresOver (ι ⁻¹' G) T ∧
        IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) D T.proj Ef ∧
        IsSNCDivisor n Ef ∧
        L.Pairwise (fun p q => Disjoint (strictTransform n T.proj (ι ⁻¹' p.1))
          (strictTransform n T.proj (ι ⁻¹' q.1))) := by
  induction ℓ with
  | zero =>
    intro X E hE G hG L hL hGood hPair B₀ ι hι hK
    rw [List.length_eq_zero_iff.mp hL]
    exact ⟨B₀,.refl,E.map (ι ⁻¹' ·),.nil,trivial,IsAdmissibleBlowupSequence.refl,
      hι.isSNCDivisor_map_preimage hE,List.Pairwise.nil⟩
  | succ ℓ ih =>
    intro X E hE G hG L hL hGood hPair B₀ ι hι hK
    obtain ⟨⟨A,d⟩,L',rfl⟩ := List.exists_cons_of_length_eq_add_one hL
    have hL' : L'.length = ℓ := by simpa using hL
    obtain ⟨hAsep,hPair'⟩ := List.pairwise_cons.mp hPair
    have hA := hGood (A,d) (List.mem_cons_self ..)
    have hGood' : ∀ p ∈ L', IsLocGoodPart n [] G p.1 p.2 :=
      fun p hp => hGood p (List.mem_cons_of_mem _ hp)
    obtain ⟨C₀,T₀,E₁,H₀,EH₀,GH₀,P₀,j₀,hHead,hOver₀,hAdm₀,hE₁,hEH₀,hGH₀,hj₀,hKj₀,
      hEdict,hGdict,hGood₀,hDis₀,hInter₀,hStrict₀,hHostSep₀,hSrcSep₀⟩ :=
      exists_local_mixed_canonical_ordered_separator ℓ E hE G hG A d hA L' hL' hGood' hAsep ι hι hK
    let LH := L'.map (fun p => (P₀ p.1,p.2))
    have hGoodH : ∀ p ∈ LH, IsLocGoodPart n [] GH₀ p.1 p.2 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact hGood₀ q.1 q.2 (hGood' q hq)
    have hPairH : LH.Pairwise (fun p q => p.1 ∩ q.1 ⊆ GH₀) := by
      simp only [LH,List.pairwise_map]
      apply hPair'.imp_of_mem
      intro p q hp hq hpq
      exact hInter₀ _ _ (hGood' p hp).isClosed (hGood' q hq).isClosed hpq
    obtain ⟨D,S,Ef,hTail,hOverS,hAdmS,hEf,hDisS⟩ :=
      ih EH₀ hEH₀ GH₀ hGH₀ LH (by simp [LH,hL']) hGoodH hPairH j₀ hj₀ hKj₀
    have hMap : L'.map (fun p => (j₀ ⁻¹' P₀ p.1,p.2)) =
        strictParts T₀ (L'.map fun p => (ι ⁻¹' p.1,p.2)) := by
      simp only [strictParts,List.map_map]
      apply List.map_congr_left
      intro p hp
      exact Prod.ext (hStrict₀ p.1 (hGood' p hp).isClosed (hGood' p hp).2.2.2.2).symm rfl
    have hTail' : CanonicalMixedSeparation E₁
        (strictParts T₀ (L'.map fun p => (ι ⁻¹' p.1,p.2))) S Ef := by
      rw [hEdict,← hMap]
      simpa only [LH,List.map_map,Function.comp_def] using hTail
    have hTree : CanonicalMixedSeparation (E.map (ι ⁻¹' ·))
        (((A,d)::L').map fun p => (ι ⁻¹' p.1,p.2)) (T₀.append S) Ef :=
      .cons T₀ S hHead hTail'
    have hOver : CentresOver (ι ⁻¹' G) (T₀.append S) :=
      (centresOver_append_iff _ T₀ S).mpr ⟨hOver₀,by rw [← hGdict]; exact hOverS⟩
    have hAdmS' : IsAdmissibleBlowupSequence n C₀ E₁ (T₀.proj ⁻¹' (ι ⁻¹' G)) D S.proj Ef := by
      rw [hEdict,← hGdict]
      exact hAdmS
    have hAdm : IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' G)
        D (T₀.append S).proj Ef := by
      simpa only [BlowupTower.proj_append] using IsAdmissibleBlowupSequence.comp hAdm₀ hAdmS'
    refine ⟨D,T₀.append S,Ef,hTree,hOver,hAdm,hEf,?_⟩
    apply List.Pairwise.cons
    · intro p hp
      have hFirst : Disjoint (strictTransform n T₀.proj (ι ⁻¹' A))
          (strictTransform n T₀.proj (ι ⁻¹' p.1)) := hSrcSep₀ p hp
      rw [BlowupTower.proj_append,
        StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj S.contMDiff_proj,
        StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj S.contMDiff_proj]
      exact Disjoint.mono
        (strictTransform_subset_preimage S.contMDiff_proj.continuous isClosed_closure)
        (strictTransform_subset_preimage S.contMDiff_proj.continuous isClosed_closure)
        (hFirst.preimage S.proj)
    · simp only [LH,List.pairwise_map] at hDisS
      apply hDisS.imp_of_mem
      intro p q hp hq hpq
      rw [← hStrict₀ p.1 (hGood' p hp).isClosed (hGood' p hp).2.2.2.2,
        ← hStrict₀ q.1 (hGood' q hq).isClosed (hGood' q hq).2.2.2.2] at hpq
      simpa only [BlowupTower.proj_append,
        StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj S.contMDiff_proj] using hpq

/-- Original finite irreducible components directly produce an actual
ordered local separator, without compactness or boundary avoidance. -/
theorem exists_local_irreducible_mixed_separation {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    {B₀ : CMfd.{0} n} (ι : B₀ → X) (hι : IsOpenHoloEmbedding n ι)
    (hK : ∃ K : Set X, IsCompact K ∧ range ι ⊆ K) :
    ∃ (D : CMfd.{0} n) (T : BlowupTower B₀ D) (Ef : List (Set D)),
      CanonicalMixedSeparation (E.map (ι ⁻¹' ·))
        ((List.finRange k).map fun a => (ι ⁻¹' (V a).carrier,(V a).dim)) T Ef ∧
      CentresOver (ι ⁻¹' mixedBadLocus V) T ∧
      IsAdmissibleBlowupSequence n B₀ (E.map (ι ⁻¹' ·)) (ι ⁻¹' mixedBadLocus V) D T.proj Ef ∧
      IsSNCDivisor n Ef ∧
      (List.finRange k).Pairwise (fun a b =>
        Disjoint (strictTransform n T.proj (ι ⁻¹' (V a).carrier))
          (strictTransform n T.proj (ι ⁻¹' (V b).carrier))) := by
  let L := (List.finRange k).map fun a => ((V a).carrier,(V a).dim)
  have hData := mixedBadLocus_closed_and_good V hDim hDistinct
  have hGood : ∀ p ∈ L, IsLocGoodPart n [] (mixedBadLocus V) p.1 p.2 := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact hData.2 a
  have hPair : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ mixedBadLocus V) := by
    simp only [L,List.pairwise_map]
    apply (List.pairwise_lt_finRange k).imp
    intro a b hab
    exact pair_intersection_subset_mixedBadLocus V (ne_of_lt hab)
  obtain ⟨D,T,Ef,hTree,hOver,hAdm,hEf,hDis⟩ :=
    exists_local_mixed_separation_tree L.length E hE (mixedBadLocus V) hData.1 L rfl hGood hPair ι hι hK
  refine ⟨D,T,Ef,?_,hOver,hAdm,hEf,?_⟩
  · simpa only [L,List.map_map,Function.comp_def] using hTree
  · simpa only [L,List.pairwise_map] using hDis

end
end Hironaka.HironakaG3LocalMixedSeparation
