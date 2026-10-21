/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalOrderedResolution

/-!
# Original mixed-dimensional elementary projection from actual canonical stages

The original analytic dimension parts internally supply the finite ordered
resolution tree. The same actual projection retains the entire elementary
dictionary and its genuine smooth source, with intrinsic source dimension parts.
Blueprint: `hironaka-original-nonpure-canonical-resolution-extension.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalNonpureCanonicalResolution

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts HironakaOriginalCanonicalDimensionList
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaOriginalStoppedPrefixSmoothComparison HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings RestrictEmptyTower

variable {n : ℕ} {X D : CMfd.{u} n}

private theorem whole_geometry_of_dimension_parts
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅)
    (T : BlowupTower X D) (E₀ : List (Set D))
    (hres : ∀ k < n, (∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n T.proj (dimensionPart (n := n) W k)) z k) ∧
      HasNormalCrossings n (strictTransform n T.proj (dimensionPart (n := n) W k)) E₀)
    (hdisj : ∀ k j : ℕ, k ≠ j → Disjoint (strictTransform n T.proj (dimensionPart (n := n) W k))
      (strictTransform n T.proj (dimensionPart (n := n) W j))) :
    IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      strictTransform n T.proj W = ⋃ k : Fin n, strictTransform n T.proj (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n T.proj W) z k) ∧
      HasNormalCrossings n (strictTransform n T.proj W) E₀ := by
  have hempty : ∀ k : ℕ, ¬ k < n → strictTransform n T.proj (dimensionPart (n := n) W k) = ∅ := by
    intro k hk
    rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk),strictTransform_empty]
  have hUnion : strictTransform n T.proj W =
      ⋃ k : Fin n, strictTransform n T.proj (dimensionPart (n := n) W k) := by
    conv_lhs => rw [eq_iUnion_dimensionPart_fin hWa hint]
    rw [strictTransform,preimage_iUnion,iUnion_sdiff,closure_iUnion_of_finite]
    rfl
  have hloc : ∀ k : ℕ, ∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
      ∃ U : Set D, IsOpen U ∧ z ∈ U ∧ strictTransform n T.proj W ∩ U =
        strictTransform n T.proj (dimensionPart (n := n) W k) ∩ U := by
    intro k z hz
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hz
      exact hz
    let S : Set (Fin n) := {j | (j : ℕ) ≠ k}
    refine ⟨(⋃ j ∈ S,strictTransform n T.proj (dimensionPart (n := n) W j))ᶜ,
      (S.toFinite.isClosed_biUnion fun j _ => isClosed_closure).isOpen_compl,?_,?_⟩
    · simp only [mem_compl_iff,mem_iUnion,not_exists]
      intro j hj hzj
      exact disjoint_left.mp (hdisj k j (Ne.symm hj)) hz hzj
    · ext y
      simp only [mem_inter_iff,mem_compl_iff,mem_iUnion,not_exists]
      refine ⟨fun ⟨hyW,hyU⟩ => ⟨?_,hyU⟩,fun ⟨hyk,hyU⟩ => ⟨?_,hyU⟩⟩
      · rw [hUnion] at hyW
        obtain ⟨j,hj⟩ := mem_iUnion.mp hyW
        by_cases hjk : (j : ℕ) = k
        · rw [← hjk]
          exact hj
        · exact absurd hj (hyU j hjk)
      · rw [hUnion]
        exact mem_iUnion.mpr ⟨⟨k,hk⟩,hyk⟩
  have hreg : ∀ k : ℕ, ∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n T.proj W) z k := by
    intro k z hz
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hz
      exact hz
    obtain ⟨U,hU,hzU,hUeq⟩ := hloc k z hz
    exact RegularPointDimension.regularAtDim_of_inter_eq hU hzU hUeq.symm ((hres k hk).1 z hz)
  have hsub : IsClosedSubmanifold n (strictTransform n T.proj W) := by
    refine ⟨isClosed_closure,fun z hz => ?_⟩
    rw [hUnion] at hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    exact ⟨k,hreg k z hk⟩
  refine ⟨hsub,hUnion,hreg,?_⟩
  apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
  intro z hz
  rw [hUnion] at hz
  obtain ⟨k,hk⟩ := mem_iUnion.mp hz
  obtain ⟨U,hU,hzU,hUeq⟩ := hloc k z hk
  refine ⟨strictTransform n T.proj (dimensionPart (n := n) W k),hk,?_,(hres k k.2).2⟩
  filter_upwards [hU.mem_nhds hzU] with y hyU
  constructor
  · intro hy
    exact ((Set.ext_iff.mp hUeq y).mp ⟨hy,hyU⟩).1
  · intro hy
    exact ((Set.ext_iff.mp hUeq y).mpr ⟨hy,hyU⟩).1

/-- The original compact analytic carrier internally constructs its actual
ordered canonical-stage projection and every compatible intrinsic smooth source. -/
theorem exists_original_nonpure_canonical_resolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W = ∅)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    let G := singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H
    let L := (List.range n).map (fun k => (dimensionPart (n := n) W k,k))
    ∃ (D : CMfd.{u} n) (T : BlowupTower X D) (E₁ : List (Set D)),
      CanonicalOrderedResolution E₀ G L T E₁ ∧ CentresOver G T ∧
      IsAdmissibleBlowupSequence n X E₀ G D T.proj E₁ ∧ IsSNCDivisor n E₁ ∧
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ E₁.drop E₀.length, H ∧
      (⋃ H ∈ E₁.drop E₀.length, H) ⊆ T.proj ⁻¹' G ∧
      T.proj ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n T.proj ∧
      IsIsomorphismOver n T.proj Gᶜ ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      strictTransform n T.proj W = ⋃ k : Fin n, strictTransform n T.proj (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n T.proj W) z k) ∧
      (∀ k j : ℕ, k ≠ j → Disjoint (strictTransform n T.proj (dimensionPart (n := n) W k))
        (strictTransform n T.proj (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n T.proj W) E₁ ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
        Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
        let W' := b ⁻¹' W
        let E' := E₀.map (b ⁻¹' ·)
        let G' := singularSet (n := m) W' ∪ W' ∩ ⋃ H ∈ E', H
        let L' := L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))
        ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
          IsActualTowerPullback b Q T g ∧
          CanonicalOrderedResolution E' G' L' Q (E₁.map (g ⁻¹' ·)) ∧
          ((List.range m).map (fun j => (dimensionPart (n := m) W' j,j))).filter (fun p => decide p.1.Nonempty) =
            L'.filter (fun p => decide p.1.Nonempty) ∧
          IsAdmissibleBlowupSequence m Y E' G' C Q.proj (E₁.map (g ⁻¹' ·)) ∧
          IsSNCDivisor m (E₁.map (g ⁻¹' ·)) ∧
          exceptionalLocus m Q.proj ⊆ ⋃ H ∈ (E₁.map (g ⁻¹' ·)).drop E₀.length, H ∧
          (⋃ H ∈ (E₁.map (g ⁻¹' ·)).drop E₀.length, H) ⊆ Q.proj ⁻¹' G' ∧
          Q.proj ⁻¹' singularSet (n := m) W' ⊆ exceptionalLocus m Q.proj ∧
          IsIsomorphismOver m Q.proj G'ᶜ ∧
          strictTransform m Q.proj W' = g ⁻¹' strictTransform n T.proj W ∧
          (∀ k : ℕ, strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n))) =
            g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k)) ∧
          IsClosedSubmanifold m (strictTransform m Q.proj W') ∧
          strictTransform m Q.proj W' = ⋃ j : Fin m, strictTransform m Q.proj (dimensionPart (n := m) W' j) ∧
          (∀ j : ℕ, ∀ z ∈ strictTransform m Q.proj (dimensionPart (n := m) W' j),
            RegularAtDim (n := m) (strictTransform m Q.proj W') z j) ∧
          (∀ i j : ℕ, i ≠ j → Disjoint (strictTransform m Q.proj (dimensionPart (n := m) W' i))
            (strictTransform m Q.proj (dimensionPart (n := m) W' j))) ∧
          HasNormalCrossings m (strictTransform m Q.proj W') (E₁.map (g ⁻¹' ·)) ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
          Q.length = T.length ∧ (∀ z, T.proj (g z) = b (Q.proj z)) ∧
          HolomorphicSquarePullback b g Q.proj T.proj := by
  dsimp only
  let G := singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H
  let L := (List.range n).map (fun k => (dimensionPart (n := n) W k,k))
  have hG : IsClosed G := (isClosed_singularSet hWa.isClosed).union
    (hWa.isClosed.inter (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1))
  have hgood : ∀ p ∈ L, IsGoodPart n E₀ G p.1 p.2 := by
    intro p hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact ⟨isComplexAnalyticSubset_dimensionPart hWa k,
      hK.of_isClosed_subset isClosed_closure (dimensionPart_subset hWa.isClosed k),List.mem_range.mp hk,
      (diff_regularLocus_dimensionPart_subset_singularSet hWa.isClosed k).trans subset_union_left,
      fun x hx => Or.inr ⟨dimensionPart_subset hWa.isClosed k hx.1,hx.2⟩,
      dimensionPart_subset_closure_diff hE₀W k⟩
  have hpair : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) := by
    simp only [L,List.pairwise_map]
    exact List.nodup_range.imp fun {k j} hkj =>
      (inter_dimensionPart_subset_singularSet hWa.isClosed hkj).trans subset_union_left
  obtain ⟨D,T,E₁,hTree,hover,hadm,hE₁,hRes,hDisj,hSource⟩ :=
    exists_canonical_ordered_resolution L.length E₀ hE₀ G hG L rfl hgood hpair
  have hempty (k : ℕ) (hk : ¬ k < n) : strictTransform n T.proj (dimensionPart (n := n) W k) = ∅ := by
    rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk),strictTransform_empty]
  have hresk : ∀ k < n, (∀ z ∈ strictTransform n T.proj (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n T.proj (dimensionPart (n := n) W k)) z k) ∧
      HasNormalCrossings n (strictTransform n T.proj (dimensionPart (n := n) W k)) E₁ :=
    fun k hk => hRes _ (List.mem_map_of_mem (List.mem_range.mpr hk))
  have hdisjk : ∀ k j : ℕ, k ≠ j → Disjoint (strictTransform n T.proj (dimensionPart (n := n) W k))
      (strictTransform n T.proj (dimensionPart (n := n) W j)) := by
    intro k j hkj
    by_cases hk : k < n
    · by_cases hj : j < n
      · have hh : (List.range n).Pairwise (fun k j => Disjoint
            (strictTransform n T.proj (dimensionPart (n := n) W k))
            (strictTransform n T.proj (dimensionPart (n := n) W j))) := by
          simpa only [L,List.pairwise_map] using hDisj
        have : Std.Symm (fun k j : ℕ => Disjoint (strictTransform n T.proj (dimensionPart (n := n) W k))
            (strictTransform n T.proj (dimensionPart (n := n) W j))) := ⟨fun _ _ h => h.symm⟩
        exact hh.forall (List.mem_range.mpr hk) (List.mem_range.mpr hj) hkj
      · rw [hempty j hj]
        exact disjoint_empty _
    · rw [hempty k hk]
      exact empty_disjoint _
  obtain ⟨hSM,hUnion,hreg,hNC⟩ := whole_geometry_of_dimension_parts W hWa hint T E₁ hresk hdisjk
  obtain ⟨hExc,hNew⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadm
  have hSing := preimage_singularSet_subset_exceptionalLocus T.contMDiff_proj hWa.isClosed hSM
  refine ⟨D,T,E₁,hTree,hover,hadm,hE₁,hExc,hNew,hSing,
    IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadm,hSM,hUnion,hreg,hdisjk,hNC,
    T.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence,?_⟩
  intro m Y b hb
  let W' := b ⁻¹' W
  let E' := E₀.map (b ⁻¹' ·)
  let G' := singularSet (n := m) W' ∪ W' ∩ ⋃ H ∈ E', H
  let L' := L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))
  have hBad : b ⁻¹' G = G' := by
    simp only [G,G',W',E',preimage_union,preimage_inter,
      ← singularSet_preimage_eq hb W,HironakaEmbeddedBoundary.preimage_biUnion_list]
  obtain ⟨C,Q,g,hactual,hTreeQ,hadmQ,hEQ,_hStrictParts,_hResQ,_hDisjQ,hg,hlen,hcomm,hcart⟩ :=
    hSource Y b hb
  have hTreeQ' : CanonicalOrderedResolution E' G' L' Q (E₁.map (g ⁻¹' ·)) := by
    rw [← hBad]
    exact hTreeQ
  have hadmQ' : IsAdmissibleBlowupSequence m Y E' G' C Q.proj (E₁.map (g ⁻¹' ·)) := by
    rw [← hBad]
    exact hadmQ
  have hList : ((List.range m).map (fun j => (dimensionPart (n := m) W' j,j))).filter
      (fun p => decide p.1.Nonempty) = L'.filter (fun p => decide p.1.Nonempty) := by
    simpa only [L',L,W',List.map_map,Function.comp_def] using nonempty_dimension_list_preimage hb W
  let O : Opens X := ⟨Gᶜ,hG.isOpen_compl⟩
  have hav : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hover
  have hDensePart : ∀ k : ℕ, dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ G) := by
    intro k
    by_cases hk : k < n
    · exact (hgood _ (List.mem_map_of_mem (List.mem_range.mpr hk))).2.2.2.2.2
    · rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk)]
      exact empty_subset _
  have hDenseW : W ⊆ closure (W \ G) := by
    intro x hx
    rw [eq_iUnion_dimensionPart_fin hWa hint] at hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact closure_mono (sdiff_subset_sdiff_left (dimensionPart_subset hWa.isClosed k)) (hDensePart k hk)
  have hStrictW : strictTransform m Q.proj W' = g ⁻¹' strictTransform n T.proj W :=
    IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O hav W
      (by change W ⊆ closure (W \ G); exact hDenseW)
  have hPart : ∀ k : ℕ, strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n))) =
      g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k) := by
    intro k
    rw [dimensionPart_preimage_eq_shift hb W k]
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual O hav _
      (by change dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ G); exact hDensePart k)
  have hLow (j : ℕ) (hj : j < m-n) : strictTransform m Q.proj (dimensionPart (n := m) W' j) = ∅ := by
    rw [dimensionPart_preimage_eq_empty_of_lt_fibre hb W hj,strictTransform_empty]
  have hRegQ : ∀ j : ℕ, ∀ z ∈ strictTransform m Q.proj (dimensionPart (n := m) W' j),
      RegularAtDim (n := m) (strictTransform m Q.proj W') z j := by
    intro j z hz
    by_cases hj : j < m-n
    · rw [hLow j hj] at hz
      exact hz.elim
    · have heq : j = (j-(m-n))+(m-n) := by omega
      have hz' := hz
      rw [heq,hPart] at hz'
      have hr := regularAtDim_preimage_submersion (hg.isSubmersionAt z) (hreg (j-(m-n)) (g z) hz')
      rw [← hStrictW,← heq] at hr
      exact hr
  have hDisjQ : ∀ i j : ℕ, i ≠ j →
      Disjoint (strictTransform m Q.proj (dimensionPart (n := m) W' i))
        (strictTransform m Q.proj (dimensionPart (n := m) W' j)) := by
    intro i j hij
    by_cases hi : i < m-n
    · rw [hLow i hi]
      exact empty_disjoint _
    · by_cases hj : j < m-n
      · rw [hLow j hj]
        exact disjoint_empty _
      · have hei : i = (i-(m-n))+(m-n) := by omega
        have hej : j = (j-(m-n))+(m-n) := by omega
        have hne : i-(m-n) ≠ j-(m-n) := by omega
        rw [hei,hej,hPart,hPart]
        exact (hdisjk _ _ hne).preimage g
  have hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  have hintY : interior W' = ∅ := by
    rw [← hbo.preimage_interior_eq_interior_preimage hb.contMDiff.continuous,hint,preimage_empty]
  have hUnionQ : strictTransform m Q.proj W' =
      ⋃ j : Fin m,strictTransform m Q.proj (dimensionPart (n := m) W' j) := by
    change strictTransform m Q.proj (b ⁻¹' W) = _
    conv_lhs => rw [eq_iUnion_dimensionPart_fin hWaY hintY]
    rw [strictTransform,preimage_iUnion,iUnion_sdiff,closure_iUnion_of_finite]
    rfl
  have hSMQ : IsClosedSubmanifold m (strictTransform m Q.proj W') := by
    rw [hStrictW]
    exact isClosedSubmanifold_preimage_submersion hg hSM
  have hNCQ : HasNormalCrossings m (strictTransform m Q.proj W') (E₁.map (g ⁻¹' ·)) := by
    rw [hStrictW]
    exact hasNormalCrossings_preimage_submersion hg hNC
  obtain ⟨hExcQ,hNewQ⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadmQ'
  have hElen : E'.length = E₀.length := List.length_map _
  rw [hElen] at hExcQ hNewQ
  exact ⟨C,Q,g,hactual,hTreeQ',hList,hadmQ',hEQ,hExcQ,hNewQ,
    preimage_singularSet_subset_exceptionalLocus Q.contMDiff_proj hWaY.isClosed hSMQ,
    IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadmQ',hStrictW,hPart,hSMQ,hUnionQ,hRegQ,hDisjQ,hNCQ,
    Q.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj Q,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence,hg,hlen,hcomm,hcart⟩

end

end Hironaka.HironakaOriginalNonpureCanonicalResolution
