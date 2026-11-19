import Hironaka.Resolution.HironakaG3FiniteMixedSeparation
import Hironaka.Resolution.HironakaOriginalCanonicalSeparationChainChoice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3MixedOrderedHead
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  CanonicalCentres HironakaG3PairSeparationMeasure HironakaOriginalCanonicalSumSeparation
  RestrictEmptyTower HironakaAdmissibleCalculus HironakaOriginalNCOldStratumStrictEquality
  HironakaMixedDimensionalBoundaryFiniteSeparation
  HironakaOriginalEmptySumStage HironakaOriginalCanonicalPartListResolution
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- One prescribed ordered pair has an actual canonical terminal stage,
including the empty stage when the parts are already disjoint. -/
theorem exists_compact_pair_stage {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hCompact : ∀ a, IsCompact (V a).carrier) (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    {i j : Fin k} (hij : i < j) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let M := sumMarkedIdeal (V i).carrier (V j).carrier E
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
      (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
      (∀ a, (V' a).dim = (V a).dim) ∧
      (∀ a, IsCompact (V' a).carrier) ∧
      (∀ a b, a ≠ b → ¬ (V' a).carrier ⊆ (V' b).carrier) ∧
      (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
      Disjoint (V' i).carrier (V' j).carrier := by
  classical
  by_cases hdis : Disjoint (V i).carrier (V j).carrier
  · let M := sumMarkedIdeal (V i).carrier (V j).carrier E
    have hi : interior (V i).carrier = ∅ := EmbeddedFromResolution.interior_eq_empty_of_dim_lt (V i) (hDim i)
    have hdom := isInvDomain_sumMarkedIdeal (V i).irreducible_carrier.analytic (V j).irreducible_carrier.analytic hi hE
    have hcan : IsCanonical M ((canonicalInvariant n).inv M) (BlowupTower.refl : BlowupTower X X) := trivial
    have hres := (canonical_sum_stage_empty_of_disjoint (V i).irreducible_carrier.analytic
      (V j).irreducible_carrier.analytic hi E hE hdis .refl hcan).2.2
    refine ⟨X,.refl,V,hdom,hcan,hres,hE,?_,?_,hCompact,hDistinct,?_,hdis⟩
    · intro a
      simp [strictTransform,exceptionalLocus_id,(V a).isClosed_carrier.closure_eq]
    · intro a
      rfl
    · intro a
      simp [BlowupTower.proj]
  · let F : Fin k → Set X := fun a => (V a).carrier
    have hI : ∀ a, IsComplexAnalyticallyIrreducible (n := n) (F a) := fun a => (V a).irreducible_carrier
    have hK : IsCompact (F i ∩ F j) := (hCompact i).inter_right (V j).isClosed_carrier
    have hint : interior (F i) = ∅ := EmbeddedFromResolution.interior_eq_empty_of_dim_lt (V i) (hDim i)
    obtain ⟨Y,T,hdom,hcan,hres,hcent,hSNC,hsep,_hdec,hProj,hDistinctT⟩ :=
      exists_irreducible_canonical_pair_decrease F hI hDistinct hij hdis hint hK E hE
    let O : Opens X := ⟨(F i ∩ F j)ᶜ, ((V i).isClosed_carrier.inter (V j).isClosed_carrier).isOpen_compl⟩
    have hAvoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hcent
    have hExc : T.proj '' exceptionalLocus n T.proj ⊆ F i ∩ F j := by
      have h := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O T hAvoid
      change T.proj '' exceptionalLocus n T.proj ⊆ ((F i ∩ F j)ᶜ)ᶜ at h
      simpa only [compl_compl] using h
    have hNot : ∀ a, ¬ F a ⊆ F i ∩ F j := by
      intro a h
      by_cases hai : a = i
      · subst a
        exact hDistinct i j (ne_of_lt hij) (h.trans inter_subset_right)
      · exact hDistinct a i hai (h.trans inter_subset_left)
    have hExist : ∀ a, ∃ W : ClosedIrreducibleAnalyticSubvariety n Y,
        W.carrier = strictTransform n T.proj (V a).carrier ∧ W.dim = (V a).dim := by
      intro a
      exact HironakaEmbeddedResolutionLocal.exists_strictTransform_subvariety_of_isBlowupSequence
        T.isBlowupSequence (V a) (fun hs => hNot a (hs.trans hExc))
    choose V' hCarrier hDim' using hExist
    refine ⟨Y,T,V',hdom,hcan,hres,hSNC,hCarrier,hDim',?_,?_,?_,?_⟩
    · intro a
      rw [hCarrier a]
      exact HironakaAdmissibleCalculus.isCompact_strictTransform T.isBlowupSequence (hCompact a)
    · intro a b hab
      rw [hCarrier a,hCarrier b]
      exact hDistinctT a b hab
    · intro a
      rw [hCarrier a]
      exact hProj a
    · rw [hCarrier i,hCarrier j]
      exact hsep

/-- A prescribed ordered head list produces the actual canonical
separation chain, including empty sum stages, without assuming boundary
density of any component. -/
theorem exists_compact_ordered_head_chain {n k : ℕ} (i : Fin k) :
    ∀ (L : List (Fin k)) {X : CMfd.{0} n} (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
      (_hCompact : ∀ a, IsCompact (V a).carrier) (_hDim : ∀ a, (V a).dim < n)
      (_hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
      (E : List (Set X)) (_hE : IsSNCDivisor n E) (_hOrder : ∀ b ∈ L, i < b),
      ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
        (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y) (E' : List (Set Y)),
        CanonicalSeparationChain E (V i).carrier (L.map fun b => ((V b).carrier,(V b).dim)) T E' ∧
        IsGeoTestTower (boundaryGeometry E) T ∧ E' = (geoTransformAlong (boundaryGeometry E) T).E ∧
        IsSNCDivisor n E' ∧
        (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
        (∀ a, (V' a).dim = (V a).dim) ∧ (∀ a, IsCompact (V' a).carrier) ∧
        (∀ a b, a ≠ b → ¬ (V' a).carrier ⊆ (V' b).carrier) ∧
        (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
        ∀ b ∈ L, Disjoint (V' i).carrier (V' b).carrier := by
  intro L
  induction L with
  | nil =>
    intro X V hCompact hDim hDistinct E hE hOrder
    refine ⟨X,.refl,V,E,.nil,trivial,rfl,hE,?_,?_,hCompact,hDistinct,?_,?_⟩
    · intro a
      simp [strictTransform,exceptionalLocus_id,(V a).isClosed_carrier.closure_eq]
    · intro a
      rfl
    · intro a
      simp [BlowupTower.proj]
    · intro b hb
      exact False.elim (List.not_mem_nil hb)
  | cons j L ih =>
    intro X V hCompact hDim hDistinct E hE hOrder
    have hij : i < j := hOrder j (List.mem_cons_self ..)
    have hOrderTail : ∀ b ∈ L, i < b := fun b hb => hOrder b (List.mem_cons_of_mem _ hb)
    obtain ⟨Y,T,V₁,hdom,hcan,hres,hSNC₁,hV₁,hDim₁,hCompact₁,hDistinct₁,hProj₁,hSep₁⟩ :=
      exists_compact_pair_stage V hCompact hDim hDistinct hij E hE
    let M := sumMarkedIdeal (V i).carrier (V j).carrier E
    let D := boundaryGeometry E
    let E₁ := (geoTransformAlong M T).E
    have hDim₁' : ∀ a, (V₁ a).dim < n := fun a => (hDim₁ a) ▸ hDim a
    obtain ⟨Z,S,V₂,E₂,hChain₂,hDS,hE₂,hSNC₂,hV₂,hDim₂,hCompact₂,hDistinct₂,hProj₂,hDis₂⟩ :=
      ih V₁ hCompact₁ hDim₁' hDistinct₁ E₁ hSNC₁ hOrderTail
    have hMap : (L.map fun b => ((V₁ b).carrier,(V₁ b).dim)) =
        (L.map fun b => ((V b).carrier,(V b).dim)).map
          (fun p => (strictTransform n T.proj p.1,p.2)) := by
      simp only [List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro b _hb
      rw [hV₁ b,hDim₁ b]
    rw [hMap,hV₁ i] at hChain₂
    have hChain : CanonicalSeparationChain E (V i).carrier
        ((j :: L).map fun b => ((V b).carrier,(V b).dim)) (T.append S) E₂ := by
      exact .cons T S (V i).irreducible_carrier.analytic (V j).irreducible_carrier.analytic
        hdom hcan hres hChain₂
    have hDT : IsGeoTestTower D T := boundaryGeometry_test M hE T hres.1
    have hEeq : E₁ = (geoTransformAlong D T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := M) (𝔫 := D) rfl T
    have hCurrent : IsGeoTestTower (geoTransformAlong D T) S := by
      rw [boundaryGeometry_geoTransformAlong E T,← hEeq]
      exact hDS
    have hAppend : IsGeoTestTower D (T.append S) :=
      (isGeoTestTower_append_iff D T S).mpr ⟨hDT,hCurrent⟩
    have hEnd : E₂ = (geoTransformAlong D (T.append S)).E := by
      rw [hE₂,geoTransformAlong_append,boundaryGeometry_geoTransformAlong E T,← hEeq]
    refine ⟨Z,T.append S,V₂,E₂,hChain,hAppend,hEnd,hSNC₂,?_,?_,hCompact₂,hDistinct₂,?_,?_⟩
    · intro a
      rw [hV₂ a,hV₁ a,BlowupTower.proj_append,
        StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj]
    · intro a
      exact (hDim₂ a).trans (hDim₁ a)
    · intro a
      rw [BlowupTower.proj_append,Set.image_comp,hProj₂ a,hProj₁ a]
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [hV₂ i,hV₂ b]
        exact Disjoint.mono
          (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ i).isClosed_carrier)
          (strictTransform_subset_preimage S.contMDiff_proj.continuous (V₁ b).isClosed_carrier)
          (hSep₁.preimage S.proj)
      · exact hDis₂ b hb

end
end Hironaka.HironakaG3MixedOrderedHead
