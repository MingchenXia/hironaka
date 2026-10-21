/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalNonpureCanonicalResolution
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Resolution.HironakaOriginalLocalCanonicalOrderedResolution
import Hironaka.Resolution.HironakaOriginalIntrinsicNonpureRecipe
import Hironaka.Resolution.HironakaOriginalOrderedTreeSmoothPullback

/-!
# Original local mixed-dimensional canonical elementary data

The original analytic carrier internally supplies all local part conditions.
Whole strict geometry is assembled from genuinely resolved intrinsic parts.
Blueprint: `hironaka-original-local-nonpure-canonical-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalLocalNonpureCanonicalResolution
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts HironakaOriginalCanonicalDimensionList
  HironakaOriginalCanonicalOrderedResolution HironakaOriginalSmoothIntrinsicRegularLoci
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaOriginalStoppedPrefixSmoothComparison HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionNormalCrossings RestrictEmptyTower HironakaEmbeddedAnalyticLocal
open HironakaOriginalIntrinsicNonpureRecipe HironakaOriginalOrderedTreeSmoothPullback
  HironakaOriginalStoppedBoundaryTransport HironakaOriginalCanonicalSeparationChainChoice
variable {n : ℕ} {X D : CMfd.{u} n}

/-- All original intrinsic local-algorithm fields, without carrier compactness. -/
theorem intrinsic_local_input
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H)) :
    let G := singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H
    let L := (List.range n).map (fun k => (dimensionPart (n := n) W k,k))
    IsClosed G ∧ (∀ p∈L,IsLocGoodPart n E₀ G p.1 p.2) ∧
      L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) := by
  dsimp only
  let G := singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H
  refine ⟨(isClosed_singularSet hWa.isClosed).union
    (hWa.isClosed.inter (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1)),?_,?_⟩
  · intro p hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact ⟨isComplexAnalyticSubset_dimensionPart hWa k,List.mem_range.mp hk,
      (diff_regularLocus_dimensionPart_subset_singularSet hWa.isClosed k).trans subset_union_left,
      fun x hx => Or.inr ⟨dimensionPart_subset hWa.isClosed k hx.1,hx.2⟩,
      dimensionPart_subset_closure_diff hE₀W k⟩
  · rw [List.pairwise_map]
    exact List.nodup_range.imp fun {k j} hkj =>
      (inter_dimensionPart_subset_singularSet hWa.isClosed hkj).trans subset_union_left

theorem whole_geometry_of_dimension_parts
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


/-- The original prescribed open internally has its intrinsic canonical target
and complete elementary geometry, without any compactness of the carrier. -/
theorem exists_original_local_nonpure_target
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let XU := CMfd.of (n := n) U
    let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
    let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
    let FU := singularSet (n := n) WU ∪ WU ∩ ⋃ H∈EU,H
    let LU := (List.range n).map (fun k => (dimensionPart (n := n) WU k,k))
    ∃ (D : CMfd.{u} n) (T : BlowupTower XU D) (Ef : List (Set D)),
      CanonicalOrderedResolution EU FU LU T Ef ∧ CentresOver FU T ∧
      HironakaOriginalIntrinsicNonpureRecipe.HasElementaryGeometry WU EU T Ef := by
  dsimp only
  let G := singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H
  let L := (List.range n).map (fun k => (dimensionPart (n := n) W k,k))
  obtain ⟨hG,hgood,hpair⟩ := intrinsic_local_input W hWa E₀ hE₀ hE₀W
  have hval := HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U
  have hbval := HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val U
  obtain ⟨D,T,Ef,hTree,hover,hadm,hEf,hRes,hDisj⟩ :=
    HironakaOriginalLocalCanonicalOrderedResolution.exists_local_canonical_ordered_resolution
      L.length E₀ hE₀ G hG L rfl hgood hpair (B₀ := CMfd.of (n := n) U) (Subtype.val : U → X) hval
      ⟨K,hK,by rintro x ⟨u,rfl⟩;exact hUK u.property⟩
  let WU : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  let FU := singularSet (n := n) WU ∪ WU ∩ ⋃ H∈EU,H
  let LU := (List.range n).map (fun k => (dimensionPart (n := n) WU k,k))
  have hWaU := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hbval.contMDiff hWa
  have hOpenVal : IsOpenMap (Subtype.val : U → X) :=
    HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion
      (A := X) (B := CMfd.of (n := n) U) hbval
  have hIntU : interior WU=∅ := by
    change interior ((Subtype.val : U → X) ⁻¹' W)=∅
    rw [← hOpenVal.preimage_interior_eq_interior_preimage hbval.contMDiff.continuous W,hint,preimage_empty]
  have hBad : (Subtype.val : U → X) ⁻¹' G=FU := by
    simp only [G,FU,WU,EU,preimage_union,preimage_inter,
      ← HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq (X := X) (Y := CMfd.of (n := n) U) hbval W,
      HironakaEmbeddedBoundary.preimage_biUnion_list]
  have hDim (k : ℕ) : dimensionPart (n := n) WU k=(Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k := by
    simpa only [WU,Nat.sub_self,Nat.add_zero] using dimensionPart_preimage_eq_shift (X := X) (Y := CMfd.of (n := n) U) hbval W k
  have hList : LU=L.map (fun p => ((Subtype.val : U → X) ⁻¹' p.1,p.2)) := by
    simp only [LU,L,List.map_map]
    apply List.map_congr_left
    intro k _hk
    exact Prod.ext (hDim k) rfl
  have hTreeU : CanonicalOrderedResolution EU FU LU T Ef := by
    rw [hList,← hBad]
    exact hTree
  have hoverU : CentresOver FU T := by rw [← hBad];exact hover
  have hadmU : IsAdmissibleBlowupSequence n U EU FU D T.proj Ef := by rw [← hBad];exact hadm
  have hempty (k : ℕ) (hk : ¬ k<n) : strictTransform n T.proj (dimensionPart (n := n) WU k)=∅ := by
    rw [hDim k,dimensionPart_eq_empty_of_le hint (not_lt.mp hk),preimage_empty,strictTransform_empty]
  have hResU : ∀ k<n,(∀ z∈strictTransform n T.proj (dimensionPart (n := n) WU k),
      RegularAtDim (n := n) (strictTransform n T.proj (dimensionPart (n := n) WU k)) z k) ∧
      HasNormalCrossings n (strictTransform n T.proj (dimensionPart (n := n) WU k)) Ef := by
    intro k hk
    rw [hDim k]
    exact hRes _ (List.mem_map_of_mem (List.mem_range.mpr hk))
  have hDisjU : ∀ k j : ℕ,k≠j → Disjoint (strictTransform n T.proj (dimensionPart (n := n) WU k))
      (strictTransform n T.proj (dimensionPart (n := n) WU j)) := by
    intro k j hkj
    by_cases hk : k<n
    · by_cases hj : j<n
      · have hp : (List.range n).Pairwise (fun k j => Disjoint
            (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
            (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) := by
          simpa only [L,List.pairwise_map] using hDisj
        have : Std.Symm (fun k j : ℕ => Disjoint
            (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
            (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) :=
          ⟨fun _ _ h => h.symm⟩
        rw [hDim k,hDim j]
        exact hp.forall (List.mem_range.mpr hk) (List.mem_range.mpr hj) hkj
      · rw [hempty j hj]
        exact disjoint_empty _
    · rw [hempty k hk]
      exact empty_disjoint _
  obtain ⟨hSM,hUnion,hReg,hNC⟩ := whole_geometry_of_dimension_parts WU hWaU hIntU T Ef hResU hDisjU
  obtain ⟨hExc,hNew⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadmU
  have hSing := preimage_singularSet_subset_exceptionalLocus T.contMDiff_proj hWaU.isClosed hSM
  refine ⟨D,T,Ef,hTreeU,hoverU,?_⟩
  exact ⟨hadmU,hEf,hExc,hNew,hSing,IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadmU,
    hSM,hUnion,hReg,hDisjU,hNC,T.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence⟩

/-- Transparent output contract for actual intrinsic smooth sources and independently chosen recipes. -/
def HasIntrinsicSmoothSources (W : Set X) (E : List (Set X))
    (T : BlowupTower X D) (Ef : List (Set D)) : Prop :=
∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X),
  Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b →
  let W' := b ⁻¹' W
  let E' := E.map (b ⁻¹' ·)
  ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
    IntrinsicOrderedRecipe W' E' Q (Ef.map (g ⁻¹' ·)) ∧
    HasElementaryGeometry W' E' Q (Ef.map (g ⁻¹' ·)) ∧
    IsActualTowerPullback b Q T g ∧
    strictTransform m Q.proj W'=g ⁻¹' strictTransform n T.proj W ∧
    (∀ k : ℕ,strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n)))=
      g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k)) ∧
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
    Q.length=T.length ∧ (∀ z,T.proj (g z)=b (Q.proj z)) ∧
    HolomorphicSquarePullback b g Q.proj T.proj ∧
    ∀ (C' : CMfd.{u} m) (S : BlowupTower Y C') (Es : List (Set C')),
      IntrinsicOrderedRecipe W' E' S Es →
      IsSNCDivisor m Es ∧ IsClosedSubmanifold m (strictTransform m S.proj W') ∧
        HasNormalCrossings m (strictTransform m S.proj W') Es ∧
        ∃! η : C' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C,
          (∀ z,Q.proj (η z)=S.proj z) ∧
          Es.filter (fun H => decide H.Nonempty)=
            ((Ef.map (g ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
          (∀ P : Set Y,strictTransform m S.proj P=η ⁻¹' strictTransform m Q.proj P) ∧
          Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (g ∘ η) ∧
          HolomorphicSquarePullback b (g ∘ η) S.proj T.proj

private theorem cartesian_precompose_biholomorphism {m : ℕ} {Y C C' : CMfd.{u} m}
    {b : Y → X} {g : C → D} (q : C → Y) (s : C' → Y) (p : D → X)
    (η : C' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ C)
    (hη : ∀ z,q (η z)=s z) (hU : HolomorphicSquarePullback b g q p) :
    HolomorphicSquarePullback b (g ∘ η) s p := by
  intro k W a c ha hc hcone
  obtain ⟨w,hw,huniq⟩ := hU k W a c ha hc hcone
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro z
    exact (hη (η.symm (w z))).symm.trans (by rw [η.apply_symm_apply];exact hw.2.1 z)
  · intro z
    change g (η (η.symm (w z)))=c z
    rw [η.apply_symm_apply]
    exact hw.2.2 z
  · intro v hv
    have he : η ∘ v=w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun z => (hη (v z)).trans (hv.2.1 z),hv.2.2⟩
    funext z
    apply η.injective
    change η (v z)=η (η.symm (w z))
    rw [η.apply_symm_apply]
    exact congrFun he z


private theorem intrinsic_smooth_sources_of_actual_target
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H))
    {T : BlowupTower X D} {Ef : List (Set D)}
    (hTree : CanonicalOrderedResolution E₀ (singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H)
      ((List.range n).map (fun k => (dimensionPart (n := n) W k,k))) T Ef)
    (hover : CentresOver (singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H) T)
    (hGeom : HasElementaryGeometry W E₀ T Ef) : HasIntrinsicSmoothSources W E₀ T Ef := by
  intro m Y b hb
  let G := singularSet (n := n) W ∪ W ∩ ⋃ H∈E₀,H
  let L := (List.range n).map (fun k => (dimensionPart (n := n) W k,k))
  obtain ⟨hG,hgood,_hpair⟩ := intrinsic_local_input W hWa E₀ hE₀ hE₀W
  have hAnalytic : ∀ p∈L,IsComplexAnalyticSubset (n := n) p.1 := fun p hp => (hgood p hp).1
  have hDense : ∀ p∈L,p.1 ⊆ closure (p.1 \ G) := fun p hp => (hgood p hp).2.2.2.2
  obtain ⟨C,Q,g,hactual,hTreeQ,_hoverQ,hadmQ,hStrict⟩ :=
    ordered_tree_smooth_pullback hTree G hG hAnalytic hDense hover hb
  let W' := b ⁻¹' W
  let E' := E₀.map (b ⁻¹' ·)
  let G' := singularSet (n := m) W' ∪ W' ∩ ⋃ H∈E',H
  have hBad : b ⁻¹' G=G' := by
    simp only [G,G',W',E',preimage_union,preimage_inter,
      ← singularSet_preimage_eq hb W,HironakaEmbeddedBoundary.preimage_biUnion_list]
  have hTreeQ' : CanonicalOrderedResolution E' G'
      (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (Ef.map (g ⁻¹' ·)) := by
    rw [← hBad]
    exact hTreeQ
  have hadmQ' : IsAdmissibleBlowupSequence m Y E' G' C Q.proj (Ef.map (g ⁻¹' ·)) := by
    rw [← hBad]
    exact hadmQ
  have hList : ((List.range m).map (fun j => (dimensionPart (n := m) W' j,j))).filter
      (fun p => decide p.1.Nonempty)=(L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))).filter
        (fun p => decide p.1.Nonempty) := by
    simpa only [L,W',List.map_map,Function.comp_def] using nonempty_dimension_list_preimage hb W
  have hRecipeQ : IntrinsicOrderedRecipe W' E' Q (Ef.map (g ⁻¹' ·)) := ⟨_,hList.symm,hTreeQ'⟩
  have hDensePart : ∀ k : ℕ,dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ G) := by
    intro k
    by_cases hk : k<n
    · exact hDense _ (List.mem_map_of_mem (List.mem_range.mpr hk))
    · rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk)]
      exact empty_subset _
  have hDenseW : W ⊆ closure (W \ G) := by
    intro x hx
    rw [eq_iUnion_dimensionPart_fin hWa hint] at hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact closure_mono (sdiff_subset_sdiff_left (dimensionPart_subset hWa.isClosed k)) (hDensePart k hk)
  have hStrictW : strictTransform m Q.proj W'=g ⁻¹' strictTransform n T.proj W := hStrict W hDenseW
  have hPart (k : ℕ) : strictTransform m Q.proj (dimensionPart (n := m) W' (k+(m-n)))=
      g ⁻¹' strictTransform n T.proj (dimensionPart (n := n) W k) := by
    rw [dimensionPart_preimage_eq_shift hb W k]
    exact hStrict _ (hDensePart k)
  rcases hGeom with ⟨_hadmT,hEf,_hExcT,_hNewT,_hSingT,_hIsoT,hSM,hUnion,hReg,hDisj,hNC,
    _hHolT,_hProperT,_hSurjT⟩
  have hLow (j : ℕ) (hj : j<m-n) : strictTransform m Q.proj (dimensionPart (n := m) W' j)=∅ := by
    rw [dimensionPart_preimage_eq_empty_of_lt_fibre hb W hj,strictTransform_empty]
  have hRegQ : ∀ j : ℕ,∀ z∈strictTransform m Q.proj (dimensionPart (n := m) W' j),
      RegularAtDim (n := m) (strictTransform m Q.proj W') z j := by
    intro j z hz
    by_cases hj : j<m-n
    · rw [hLow j hj] at hz
      exact hz.elim
    · have heq : j=(j-(m-n))+(m-n) := by omega
      have hz' := hz
      rw [heq,hPart] at hz'
      have hr := regularAtDim_preimage_submersion (hactual.isSubmersion.isSubmersionAt z)
        (hReg (j-(m-n)) (g z) hz')
      rw [← hStrictW,← heq] at hr
      exact hr
  have hDisjQ : ∀ i j : ℕ,i≠j → Disjoint
      (strictTransform m Q.proj (dimensionPart (n := m) W' i))
      (strictTransform m Q.proj (dimensionPart (n := m) W' j)) := by
    intro i j hij
    by_cases hi : i<m-n
    · rw [hLow i hi]
      exact empty_disjoint _
    · by_cases hj : j<m-n
      · rw [hLow j hj]
        exact disjoint_empty _
      · have hei : i=(i-(m-n))+(m-n) := by omega
        have hej : j=(j-(m-n))+(m-n) := by omega
        have hne : i-(m-n)≠j-(m-n) := by omega
        rw [hei,hej,hPart,hPart]
        exact (hDisj _ _ hne).preimage g
  have hWaY := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hWa
  have hbo := HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion hb
  have hintY : interior W'=∅ := by
    rw [← hbo.preimage_interior_eq_interior_preimage hb.contMDiff.continuous,hint,preimage_empty]
  have hUnionQ : strictTransform m Q.proj W'=⋃ j : Fin m,
      strictTransform m Q.proj (dimensionPart (n := m) W' j) := by
    change strictTransform m Q.proj (b ⁻¹' W)=_
    conv_lhs => rw [eq_iUnion_dimensionPart_fin hWaY hintY]
    rw [strictTransform,preimage_iUnion,iUnion_sdiff,closure_iUnion_of_finite]
    rfl
  have hSMQ : IsClosedSubmanifold m (strictTransform m Q.proj W') := by
    rw [hStrictW]
    exact isClosedSubmanifold_preimage_submersion hactual.isSubmersion hSM
  have hNCQ : HasNormalCrossings m (strictTransform m Q.proj W') (Ef.map (g ⁻¹' ·)) := by
    rw [hStrictW]
    exact hasNormalCrossings_preimage_submersion hactual.isSubmersion hNC
  obtain ⟨hExcQ,hNewQ⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadmQ'
  have hGeomQ : HasElementaryGeometry W' E' Q (Ef.map (g ⁻¹' ·)) :=
    ⟨hadmQ',isSNCDivisor_preimage_submersion hactual.isSubmersion Ef hEf,hExcQ,hNewQ,
      preimage_singularSet_subset_exceptionalLocus Q.contMDiff_proj hWaY.isClosed hSMQ,
      IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadmQ',hSMQ,hUnionQ,hRegQ,hDisjQ,hNCQ,
      Q.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj Q,
      HironakaLocalPrincipalization.IsBlowupSequence.surjective Q.isBlowupSequence⟩
  refine ⟨C,Q,g,hRecipeQ,hGeomQ,hactual,hStrictW,hPart,hactual.isSubmersion,hactual.length_eq,
    hactual.proj_comm,hactual.universal,?_⟩
  intro C' S Es hRecipeS
  obtain ⟨η,hη,hu⟩ := intrinsic_recipe_choice hRecipeQ hRecipeS
  have hηsub := HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism η
  have hstrict : strictTransform m S.proj W'=η ⁻¹' strictTransform m Q.proj W' := hη.2.2 _
  have hSMS : IsClosedSubmanifold m (strictTransform m S.proj W') := by
    rw [hstrict]
    exact isClosedSubmanifold_preimage_submersion hηsub hSMQ
  have hNCS : HasNormalCrossings m (strictTransform m S.proj W') Es := by
    apply (hasNormalCrossings_filter_nonempty_iff _ _).mp
    rw [hstrict,hη.2.1]
    exact hasNormalCrossings_preimage_submersion hηsub
      ((hasNormalCrossings_filter_nonempty_iff _ _).mpr hNCQ)
  have hSNC : IsSNCDivisor m Es := by
    obtain ⟨L,_hL,hS⟩ := hRecipeS
    exact ordered_tree_final_snc hS (isSNCDivisor_preimage_submersion hb E₀ hE₀)
  refine ⟨hSNC,hSMS,hNCS,η,⟨hη.1,hη.2.1,hη.2.2,?_,?_⟩,?_⟩
  · exact HironakaSmoothSubmersionOriginalTerminalSubmersion.isSubmersion_precompose_biholomorphism hactual.isSubmersion η
  · exact cartesian_precompose_biholomorphism Q.proj S.proj T.proj η hη.1 hactual.universal
  · intro η' hh
    exact hu η' ⟨hh.1,hh.2.1,hh.2.2.1⟩

/-- The original prescribed local open has one actual mixed-dimensional target
before all genuine intrinsic independent smooth-source comparisons. -/
theorem exists_original_local_nonpure_resolution
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H))
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    let XU := CMfd.of (n := n) U
    let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
    let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
    let FU := singularSet (n := n) WU ∪ WU ∩ ⋃ H∈EU,H
    let LU := (List.range n).map (fun k => (dimensionPart (n := n) WU k,k))
    ∃ (D : CMfd.{u} n) (T : BlowupTower XU D) (Ef : List (Set D)),
      CanonicalOrderedResolution EU FU LU T Ef ∧ CentresOver FU T ∧
      HasElementaryGeometry WU EU T Ef ∧ HasIntrinsicSmoothSources WU EU T Ef := by
  dsimp only
  obtain ⟨D,T,Ef,hTree,hover,hGeom⟩ := exists_original_local_nonpure_target W hWa hint E₀ hE₀ hE₀W U hK hUK
  let XU := CMfd.of (n := n) U
  let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
  let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
  have hbval := HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val U
  have hval := HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U
  have hWaU : IsComplexAnalyticSubset (n := n) WU :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hbval.contMDiff hWa
  have hEU : IsSNCDivisor n EU := hval.isSNCDivisor_map_preimage hE₀
  have hOpenVal : IsOpenMap (Subtype.val : U → X) :=
    HironakaSmoothSubmersionOrderedImageTrace.isOpenMap_of_isSubmersion
      (A := X) (B := XU) hbval
  have hIntU : interior WU=∅ := by
    change interior ((Subtype.val : U → X) ⁻¹' W)=∅
    rw [← hOpenVal.preimage_interior_eq_interior_preimage hbval.contMDiff.continuous W,hint,preimage_empty]
  have hDenseU : WU ⊆ closure (WU \ ⋃ H∈EU,H) :=
    boundary_density_preimage (X := X) (Y := XU) hbval W E₀ hE₀W
  exact ⟨D,T,Ef,hTree,hover,hGeom,
    intrinsic_smooth_sources_of_actual_target WU hWaU hIntU EU hEU hDenseU hTree hover hGeom⟩

/-- The actual relatively compact neighbourhood, target and all intrinsic
smooth sources are internally chosen from the original data and compact K. -/
theorem exists_original_local_nonpure_resolution_near_compact
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W=∅)
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H∈E₀,H))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X,K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      let XU := CMfd.of (n := n) U
      let WU : Set XU := (Subtype.val : U → X) ⁻¹' W
      let EU := E₀.map ((Subtype.val : U → X) ⁻¹' ·)
      let FU := singularSet (n := n) WU ∪ WU ∩ ⋃ H∈EU,H
      let LU := (List.range n).map (fun k => (dimensionPart (n := n) WU k,k))
      ∃ (D : CMfd.{u} n) (T : BlowupTower XU D) (Ef : List (Set D)),
        CanonicalOrderedResolution EU FU LU T Ef ∧ CentresOver FU T ∧
        HasElementaryGeometry WU EU T Ef ∧ HasIntrinsicSmoothSources WU EU T Ef := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U,hUo,hKU,hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U,hUo⟩,hKU,hUc,
    exists_original_local_nonpure_resolution W hWa hint E₀ hE₀ hE₀W ⟨U,hUo⟩ hUc subset_closure⟩

end
end Hironaka.HironakaOriginalLocalNonpureCanonicalResolution
