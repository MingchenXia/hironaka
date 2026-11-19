import Hironaka.Resolution.HironakaG8CompactSingularEmbeddedResolution
import Hironaka.Resolution.HironakaG3DisjointAtlasCommonGood
import Hironaka.Resolution.HironakaG3RChartOfMember
import Hironaka.Resolution.HironakaG3IndexedSNCLocalSlots
import Hironaka.Resolution.HironakaG3LocallyFiniteSupportedFamilies
import Hironaka.Resolution.HironakaG3ClosedSupportedWindowExtension

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG8IsolatedCompactSingularAtlas

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaAdmissibleSequence HironakaStageCenters RestrictEmptyTower
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3DisjointLocalTowerAtlas
  HironakaG3DisjointAtlasCommonGood HironakaG3RChartOfMember
  HironakaG8CompactSingularEmbeddedResolution AnalyticSubsetOpens

variable {n : ℕ} {X : CMfd.{0} n}

private abbrev originalRecord (W : Set X) : MarkedIdeal n X :=
  ⟨univ, [], vanishingIdeal (n := n) W, 1⟩

/-- The actual singular or smooth boundary centre condition on every recorded prefix. -/
def EmbeddedPositions (W : Set X) {Y : CMfd.{0} n} (T : BlowupTower X Y) : Prop :=
  StageCentres (fun P C =>
    (C ⊆ {x | x ∈ strictTransform n P.proj W ∧
      ∀ k, ¬ RegularAtDim (n := n) (strictTransform n P.proj W) x k} ∨
    (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
      C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈ (geoTransformAlong (originalRecord W) P).E, H)) ∧
    HasNormalCrossings n C (geoTransformAlong (originalRecord W) P).E) T

/-- On empty initial boundary the literal position condition forces every
actual centre to lie over the original singular set. -/
theorem embedded_positions_centres_over {W : Set X} (hW : IsClosed W) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), EmbeddedPositions W T →
      CentresOver (singularSet (n := n) W) T ∧
      IsAdmissibleBlowupSequence n X [] (singularSet (n := n) W) Y T.proj
        (geoTransformAlong (originalRecord W) T).E
  | _, .refl, _ => ⟨trivial, .refl⟩
  | _, .step T C π hπ, hStage => by
    obtain ⟨hOver, hAdm⟩ := embedded_positions_centres_over hW T hStage.1
    have hC : C ⊆ T.proj ⁻¹' singularSet (n := n) W := by
      rcases hStage.2.1 with hSing | ⟨_, hBoundary⟩
      · let O : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW).isOpen_compl⟩
        have hAvoid := centresAvoid_of_centresOver O (F := singularSet (n := n) W)
          disjoint_compl_left T hOver
        intro y hy
        by_contra hNot
        have hyW := HironakaAdmissibleCalculus.strictTransform_subset_preimage
          T.contMDiff_proj.continuous hW (hSing hy).1
        have hReg : ∃ d, RegularAtDim (n := n) W (T.proj y) d := by
          by_contra hNone
          exact hNot (mem_singularSet_iff.mpr ⟨hyW, fun d hd => hNone ⟨d, hd⟩⟩)
        obtain ⟨d, hd⟩ := hReg
        have hNonExc := EmbeddedFromResolution.notMem_exceptionalLocus_of_centresAvoid O T hAvoid y hNot
        exact (hSing hy).2 d
          ((regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW hNonExc d).mpr hd)
      · intro y hy
        simpa using HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hAdm
          (isSNCDivisor_nil : IsSNCDivisor n ([] : List (Set X))).1 (hBoundary hy).2
    exact ⟨⟨hOver, hC⟩, .step T.proj _ C π hAdm hπ hStage.2.2 hC⟩

private theorem singular_trace (U : Opens X) (W : Set X) :
    singularSet (n := n) ((Subtype.val : U → X) ⁻¹' W) =
      (Subtype.val : U → X) ⁻¹' singularSet (n := n) W := by
  ext x
  change x ∈ singularSet (n := n) ((Subtype.val : U → X) ⁻¹' W) ↔
    x.val ∈ singularSet (n := n) W
  rw [mem_singularSet_iff, mem_singularSet_iff]
  exact and_congr Iff.rfl (forall_congr' fun k => not_congr regularAtDim_preimage_val_iff)

/-- A window class whose only member is its selected actual finite history. -/
inductive fixedWindowTower (U : Opens X) {Y : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) : LocalTowerClass X where
  | own : fixedWindowTower U T U Y T

theorem fixed_window_tower_comparisons (U : Opens X) {Y : CMfd.{0} n}
    (T : BlowupTower (CMfd.of (n := n) U) Y) : HasComparisons (fixedWindowTower U T) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
  cases h₁
  cases h₂
  exact ⟨Diffeomorph.refl _ _ ∞, fun _ => rfl⟩

/-- The finite chosen tower on the indicated entire singular window. -/
structure WindowResolution (U : Opens X) (W : Set X) where
  Y : CMfd.{0} n
  T : BlowupTower (CMfd.of (n := n) U) Y
  stage : EmbeddedPositions ((Subtype.val : U → X) ⁻¹' W) T
  smooth : IsClosedSubmanifold n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))
  snc : IsSNCDivisor n (geoTransformAlong (originalRecord ((Subtype.val : U → X) ⁻¹' W)) T).E
  nc : HasNormalCrossings n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))
    (geoTransformAlong (originalRecord ((Subtype.val : U → X) ⁻¹' W)) T).E
  exc : exceptionalLocus n T.proj =
    T.proj ⁻¹' (Subtype.val : U → X) ⁻¹' singularSet (n := n) W
  iso : IsIsomorphismOver n T.proj ((Subtype.val : U → X) ⁻¹' (singularSet (n := n) W)ᶜ)

def WindowResolution.boundary {U : Opens X} {W : Set X} (R : WindowResolution U W) : List (Set R.Y) :=
  (geoTransformAlong (originalRecord ((Subtype.val : U → X) ⁻¹' W)) R.T).E

private theorem exists_window_resolution {m : ℕ} {X : CMfd.{0} (m+1)} {W A : Set X}
    (U : Opens X) (hW : IsComplexAnalyticSubset (n := m+1) W)
    (hA : IsCompact A) (hTrace : (U : Set X) ∩ singularSet (n := m+1) W = A) :
    Nonempty (WindowResolution U W) := by
  have hLocalK : IsCompact (singularSet (n := m+1) ((Subtype.val : U → X) ⁻¹' W)) := by
    rw [singular_trace, Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_comm, hTrace]
    exact hA
  obtain ⟨Y,T,_hAdm,hStage,hSmooth,hSNC,hNC,_hTrans,_hHol,_hProp,_hSurj,_hImg,hIso,hExc⟩ :=
    exists_embedded_resolution_of_compact_singular_locus (X := CMfd.of (n := m+1) U)
      (isComplexAnalyticSubset_preimage_val hW U) hLocalK
  refine ⟨⟨Y,T,hStage,hSmooth,hSNC,hNC,?_,?_⟩⟩
  · simpa only [singular_trace] using hExc
  · simpa only [singular_trace, preimage_compl] using hIso

/-- Every chart is a chosen component history on its exact window or empty off the singular union. -/
def isolatedSingularClass {ι : Type u} (A : ι → Set X) (U : ι → Opens X) {W : Set X}
    (R : ∀ i, WindowResolution (U i) W) : LocalTowerClass X :=
  disjointWindowClass A U (fun i => fixedWindowTower (U i) (R i).T)

open HironakaG3LocallyFiniteSupportedFamilies HironakaG3ClosedSupportedWindowExtension
  HironakaG3IndexedSNCLocalSlots HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation NormalCrossingsInvariance BlowupRestrictOpen

private theorem preimage_chartIncl_image {Z : CMfd.{0} n} {D : LocalTowerClass X} {P : Z → X}
    (c : TowerChart D Z P) (H : Set c.Y) :
    (Subtype.val : c.V → Z) ⁻¹' (chartIncl c '' H) = c.φ.symm ⁻¹' H := by
  ext z
  constructor
  · rintro ⟨y,hy,h⟩
    have he : c.φ y = z := Subtype.ext h
    rw [mem_preimage, ← he, c.φ.symm_apply_apply]
    exact hy
  · intro hz
    exact ⟨c.φ.symm z, hz, chartIncl_symm c z⟩

set_option backward.isDefEq.respectTransparency false in
/-- A locally finite collection of isolated compact singular pieces admits a
proper embedded resolution by compatible literal finite window histories. -/
theorem exists_isolated_compact_singular_resolution {m : ℕ} {X : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    {ι : Type u} (A : ι → Set X) (U : ι → Opens X)
    (hCompact : ∀ i, IsCompact (A i)) (hLF : LocallyFinite A)
    (hUnion : (⋃ i, A i) = singularSet (n := m + 1) W)
    (hAU : ∀ i, A i ⊆ U i)
    (hIsolates : ∀ i j, i ≠ j → Disjoint (A j) (U i : Set X)) :
    ∃ (R : ∀ i, WindowResolution (U i) W) (Z : CMfd.{0} (m + 1)) (P : Z → X)
      (B : (Σ i, Fin (R i).boundary.length) → Set Z),
      let D := isolatedSingularClass A U R
      IsGluedFrom D Z P ∧ HasComparisons D ∧
      IsIsomorphismOver (m + 1) P (singularSet (n := m + 1) W)ᶜ ∧
      IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P W) ∧
      P '' strictTransform (m + 1) P W = W ∧
      exceptionalLocus (m + 1) P = P ⁻¹' singularSet (n := m + 1) W ∧
      IsLocallyFiniteSNCDivisor (m + 1) B ∧
      (∀ a, B a ⊆ P ⁻¹' A a.1) ∧
      (⋃ a, B a) = exceptionalLocus (m + 1) P ∧
      HasNormalCrossingsWithBoundary (strictTransform (m + 1) P W) B := by
  classical
  let n := m + 1
  let S := singularSet (n := n) W
  have hUnionS : (⋃ i, A i) = S := hUnion
  have hOnly (i : ι) (x : X) (hx : x ∈ U i) (hS : x ∈ S) : x ∈ A i := by
    rw [← hUnionS] at hS
    obtain ⟨j,hj⟩ := mem_iUnion.mp hS
    by_cases hij : i = j
    · exact hij.symm ▸ hj
    · exact (Set.disjoint_left.mp (hIsolates i j hij) hj hx).elim
  have hTrace (i : ι) : (U i : Set X) ∩ S = A i := by
    refine Subset.antisymm (fun x hx => hOnly i x hx.1 hx.2) ?_
    intro x hx
    exact ⟨hAU i hx, hUnionS ▸ mem_iUnion.mpr ⟨i,hx⟩⟩
  have hClosed (i : ι) : IsClosed (A i) := (hCompact i).isClosed
  let R (i : ι) := Classical.choice (exists_window_resolution (U i) hW (hCompact i) (hTrace i))
  let K (i : ι) : LocalTowerClass X := fixedWindowTower (U i) (R i).T
  let D := isolatedSingularClass A U R
  have hOfS (i : ι) : (Subtype.val : U i → X) ⁻¹' S = (Subtype.val : U i → X) ⁻¹' A i := by
    ext x
    exact ⟨hOnly i x x.property, fun hx => hUnionS ▸ mem_iUnion.mpr ⟨i,hx⟩⟩
  have hSupport (i : ι) := embedded_positions_centres_over
    (hW.isClosed.preimage (continuous_subtype_val : Continuous (Subtype.val : U i → X))) (R i).T (R i).stage
  have hOver : ∀ (i : ι) (V : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) V) Y),
      K i V Y T → CentresOver ((Subtype.val : V → X) ⁻¹' A i) T := by
    intro i V Y T h
    cases h
    rw [← hOfS i, ← singular_trace]
    exact (hSupport i).1
  have hKCmp : ∀ i, HasComparisons (K i) := fun i => fixed_window_tower_comparisons (U i) (R i).T
  have hCmp : HasComparisons D := disjoint_window_comparisons A U K hIsolates hKCmp hOver
  obtain ⟨Z,P,hG⟩ := exists_glued_disjoint_window_atlas A U K hClosed hLF hIsolates hKCmp hOver
    (fun i x hx => ⟨U i, hAU i hx, le_rfl, (R i).Y, (R i).T, .own⟩)
  have hIso : IsIsomorphismOver n P Sᶜ :=
    disjoint_atlas_isomorphism_over_common_good A U K Sᶜ (fun i V Y T h => by cases h; exact (R i).iso) hG
  let C := strictTransform n P W
  let chart (i : ι) : TowerChart D Z P := chartOfMember hCmp (R i).T
    (Or.inl ⟨i, le_rfl, .own⟩) hG.2.2.2 hG.1.continuous
  let O : Opens X := ⟨Sᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  let emptyChart : TowerChart D Z P := chartOfMember hCmp (.refl : BlowupTower (CMfd.of (n := n) O) _)
    (Or.inr ⟨by rw [hUnionS]; exact Subset.rfl, trivial⟩) hG.2.2.2 hG.1.continuous
  have hTraceC (i : ι) : strictTransform n (R i).T.proj ((Subtype.val : U i → X) ⁻¹' W) =
      chartIncl (chart i) ⁻¹' C := strictTransform_chart (chart i) hG.1 W
  have hSmooth : IsClosedSubmanifold n C := by
    refine ⟨isClosed_closure, fun y hy => ?_⟩
    by_cases hs : P y ∈ S
    · rw [← hUnionS] at hs
      obtain ⟨i,hi⟩ := mem_iUnion.mp hs
      have hyV : y ∈ (chart i).V := (chart i).mem_V (hAU i hi)
      let q : (R i).Y := (chart i).φ.symm ⟨y,hyV⟩
      have hq : chartIncl (chart i) q = y := chartIncl_symm _ _
      have hqC : q ∈ strictTransform n (R i).T.proj ((Subtype.val : U i → X) ⁻¹' W) := by
        rw [hTraceC i]
        change chartIncl (chart i) q ∈ C
        rwa [hq]
      obtain ⟨d,hd⟩ := (R i).smooth.2 q hqC
      exact ⟨d, hq ▸ regularAtDim_of_chart (chart i) ((hTraceC i) ▸ hd)⟩
    · have hyV : y ∈ emptyChart.V := emptyChart.mem_V hs
      let q : O := emptyChart.φ.symm ⟨y,hyV⟩
      have hq : chartIncl emptyChart q = y := chartIncl_symm _ _
      have hEq : (Subtype.val : O → X) ⁻¹' W = chartIncl emptyChart ⁻¹' C :=
        (HironakaG11PresTowerState.strictTransform_id (hW.isClosed.preimage continuous_subtype_val)).symm.trans
          (strictTransform_chart emptyChart hG.1 W)
      have hqW : q.val ∈ W := by
        change q ∈ (Subtype.val : O → X) ⁻¹' W
        rw [hEq]
        change chartIncl emptyChart q ∈ C
        rwa [hq]
      have hReg : ∃ d, RegularAtDim (n := n) W q.val d := by
        by_contra hNone
        exact q.property (mem_singularSet_iff.mpr ⟨hqW, fun k hk => hNone ⟨k,hk⟩⟩)
      obtain ⟨d,hd⟩ := hReg
      have hd' : RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) q d := regularAtDim_preimage_val_iff.mpr hd
      exact ⟨d, hq ▸ regularAtDim_of_chart emptyChart (hEq ▸ hd')⟩
  have hExc : exceptionalLocus n P = P ⁻¹' S :=
    HironakaG8SurfaceLimitEndpoint.exceptionalLocus_eq_singular_preimage W hW.isClosed P hG.1 hIso hSmooth
  let κ := Σ i, Fin (R i).boundary.length
  let B (a : κ) := chartIncl (chart a.1) '' (R a.1).boundary.get a.2
  let F (i : ι) := P ⁻¹' A i
  let br (i : ι) (j : Fin (R i).boundary.length) : Set (chart i).V :=
    (chart i).φ.symm ⁻¹' (R i).boundary.get j
  have hFClosed (i : ι) : IsClosed (F i) := (hClosed i).preimage hG.1.continuous
  have hFV (i : ι) : F i ⊆ (chart i).V := fun _ hy => (chart i).mem_V (hAU i hy)
  have hBOver : ∀ a : κ, B a ⊆ F a.1 := by
    rintro ⟨i,j⟩ _ ⟨q,hq,rfl⟩
    have hh := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset (hSupport i).2
      (isSNCDivisor_nil : IsSNCDivisor n ([] : List (Set (U i)))).1
      (mem_iUnion₂.mpr ⟨_, List.get_mem (R i).boundary j, hq⟩)
    change P (chartIncl (chart i) q) ∈ A i
    rw [proj_chartIncl (chart i) q]
    apply hOnly i _ ((R i).T.proj q).property
    simpa [singular_trace] using hh
  have hbImg (i : ι) (j : Fin (R i).boundary.length) :
      (Subtype.val : (chart i).V → Z) '' br i j = B ⟨i,j⟩ := by
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(chart i).φ.symm v, hv, chartIncl_symm _ _⟩
    · rintro ⟨q,hq,rfl⟩
      refine ⟨(chart i).φ q, ?_, rfl⟩
      change (chart i).φ.symm ((chart i).φ q) ∈ (R i).boundary.get j
      rwa [(chart i).φ.symm_apply_apply]
  have hbOver (i : ι) (j : Fin (R i).boundary.length) : br i j ⊆ (Subtype.val : (chart i).V → Z) ⁻¹' F i := by
    intro y hy
    apply hBOver ⟨i,j⟩
    rw [← hbImg]
    exact ⟨y,hy,rfl⟩
  have hBClosed : ∀ a : κ, IsClosed (B a) := by
    rintro ⟨i,j⟩
    rw [← hbImg]
    exact isClosed_image_of_closed_support _ _ (hFClosed i) (hFV i) _
      (((R i).snc.1 _ (List.get_mem (R i).boundary j)).preimage (chart i).φ.symm.continuous) (hbOver i j)
  have hBLF : LocallyFinite B := by
    have hh := locallyFinite_sigma_images_of_closed_support
      (fun i => (chart i).V) F hFClosed (hLF.preimage_continuous hG.1.continuous) hFV br
      (fun i => locallyFinite_of_finite _) hbOver
    convert hh using 1
    funext a
    exact (hbImg a.1 a.2).symm
  let L (i : ι) := (R i).boundary.map (chartIncl (chart i) '' ·)
  have hList (i : ι) : (L i).map ((Subtype.val : (chart i).V → Z) ⁻¹' ·) =
      (R i).boundary.map ((chart i).φ.symm ⁻¹' ·) := by
    simp only [L, List.map_map]
    exact List.map_congr_left fun H _ => preimage_chartIncl_image _ H
  have hNCList (i : ι) :
      IsSNCDivisor n ((L i).map ((Subtype.val : (chart i).V → Z) ⁻¹' ·)) ∧
      HasNormalCrossings n ((Subtype.val : (chart i).V → Z) ⁻¹' C)
        ((L i).map ((Subtype.val : (chart i).V → Z) ⁻¹' ·)) := by
    have hCoord : PullsBackCoordinates n (chart i).φ.symm :=
      pullsBackCoordinates_of_forall_notMem_exceptionalLocus (chart i).φ.symm.contMDiff
        (MarkedIdealTowerTransport.notMem_exceptionalLocus (chart i).φ.symm)
    rw [hList i]
    refine ⟨isSNCDivisor_map_preimage hCoord (chart i).φ.symm.continuous (R i).snc, ?_⟩
    have hEq : (Subtype.val : (chart i).V → Z) ⁻¹' C = (chart i).φ.symm ⁻¹'
        strictTransform n (R i).T.proj ((Subtype.val : U i → X) ⁻¹' W) := by
      rw [hTraceC i]
      ext v
      change (v.val ∈ C) ↔ chartIncl (chart i) ((chart i).φ.symm v) ∈ C
      rw [chartIncl_symm]
    rw [hEq]
    exact hasNormalCrossings_preimage hCoord (R i).nc
  have hLabel (i : ι) (y : Z) (hy : y ∈ (chart i).V) (a : κ) (ha : y ∈ B a) : a.1 = i := by
    by_contra hne
    have hxU : P y ∈ U i := by
      change y ∈ ((chart i).V : Set Z) at hy
      rw [(chart i).V_eq] at hy
      exact hy
    exact Set.disjoint_left.mp (hIsolates i a.1 (Ne.symm hne)) (hBOver a ha) hxU
  have hSlot (i : ι) (y : Z) (hy : y ∈ (chart i).V) (a : κ) (ha : y ∈ B a) :
      ∃ j : Fin ((L i).map ((Subtype.val : (chart i).V → Z) ⁻¹' ·)).length,
        ((L i).map ((Subtype.val : (chart i).V → Z) ⁻¹' ·)).get j =
          (Subtype.val : (chart i).V → Z) ⁻¹' B a := by
    have hi := hLabel i y hy a ha
    rcases a with ⟨k,j⟩
    change k = i at hi
    subst k
    refine ⟨⟨j, by simp [L]⟩, ?_⟩
    simp [L, B, List.get_eq_getElem]
    rfl
  have hUnique (i : ι) (y : Z) (hy : y ∈ (chart i).V) (a b : κ) (ha : y ∈ B a) (hb : y ∈ B b) :
      (Subtype.val : (chart i).V → Z) ⁻¹' B a = (Subtype.val : (chart i).V → Z) ⁻¹' B b → a = b := by
    have hai := hLabel i y hy a ha
    have hbi := hLabel i y hy b hb
    rcases a with ⟨k,j⟩
    rcases b with ⟨l,t⟩
    change k = i at hai
    change l = i at hbi
    subst k l
    intro eq
    let q : (R i).Y := (chart i).φ.symm ⟨y,hy⟩
    have hRead (s : Fin (R i).boundary.length) :
        (Subtype.val : (chart i).V → Z) ⁻¹' B ⟨i,s⟩ =
          (chart i).φ.symm ⁻¹' (R i).boundary.get s := preimage_chartIncl_image _ _
    have hQa : q ∈ (R i).boundary.get j := by
      change (⟨y,hy⟩ : (chart i).V) ∈ (chart i).φ.symm ⁻¹' (R i).boundary.get j
      rwa [← hRead j]
    have hQb : q ∈ (R i).boundary.get t := by
      change (⟨y,hy⟩ : (chart i).V) ∈ (chart i).φ.symm ⁻¹' (R i).boundary.get t
      rwa [← hRead t]
    apply congrArg (Sigma.mk i)
    apply SimultaneousNormalCrossings.eq_of_eventually_mem_iff (R i).snc hQa hQb
    apply Filter.Eventually.of_forall
    intro z
    have hh := Set.ext_iff.mp eq ((chart i).φ z)
    rw [hRead j, hRead t] at hh
    change ((chart i).φ.symm ((chart i).φ z) ∈ (R i).boundary.get j) ↔
      ((chart i).φ.symm ((chart i).φ z) ∈ (R i).boundary.get t) at hh
    rw [(chart i).φ.symm_apply_apply] at hh
    exact hh
  have hMissing (y : Z) (hy : P y ∉ S) (a : κ) : y ∉ B a := by
    intro h
    exact hy (hUnionS ▸ mem_iUnion.mpr ⟨a.1, hBOver a h⟩)
  have hSNC := indexed_snc_of_local_slots B hBLF hBClosed (fun y => by
    by_cases hy : P y ∈ S
    · rw [← hUnionS] at hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      have hyV : y ∈ (chart i).V := (chart i).mem_V (hAU i hi)
      exact ⟨_,_,hyV,(hNCList i).1,hSlot i y hyV,hUnique i y hyV⟩
    · exact ⟨⊤,[],trivial,isSNCDivisor_nil,
        fun a ha => (hMissing y hy a ha).elim, fun a _ ha _ _ => (hMissing y hy a ha).elim⟩)
  have hNC := indexed_nc_of_local_slots C B (fun y _hy => by
    by_cases hy : P y ∈ S
    · rw [← hUnionS] at hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      have hyV : y ∈ (chart i).V := (chart i).mem_V (hAU i hi)
      exact ⟨_,_,hyV,(hNCList i).2,hSlot i y hyV⟩
    · exact ⟨⊤,[],trivial, hasNormalCrossings_nil_of_isClosedSubmanifold
        (isClosedSubmanifold_preimage_val hSmooth ⊤), fun a ha => (hMissing y hy a ha).elim⟩)
  have hBUnion : (⋃ a, B a) = exceptionalLocus n P := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨a,ha⟩ := mem_iUnion.mp hy
      exact hExc.symm ▸ (hUnionS ▸ mem_iUnion.mpr ⟨a.1, hBOver a ha⟩)
    · intro y hy
      have hsy : P y ∈ S := by rw [hExc] at hy; exact hy
      rw [← hUnionS] at hsy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hsy
      have hyV : y ∈ (chart i).V := (chart i).mem_V (hAU i hi)
      let q : (R i).Y := (chart i).φ.symm ⟨y,hyV⟩
      have hq : chartIncl (chart i) q = y := chartIncl_symm _ _
      have hqExc : q ∈ exceptionalLocus n (R i).T.proj := by
        rw [show exceptionalLocus n (R i).T.proj = chartIncl (chart i) ⁻¹' exceptionalLocus n P from
          exceptionalLocus_chart (chart i) hG.1, mem_preimage, hq]
        exact hy
      have hMem := exceptionalLocus_subset_boundary (originalRecord ((Subtype.val : U i → X) ⁻¹' W))
        (R i).T hqExc
      obtain ⟨H,hH,hqH⟩ := mem_iUnion₂.mp hMem
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hH
      exact mem_iUnion.mpr ⟨⟨i,j⟩,⟨q,hqH,hq⟩⟩
  have hImage : P '' C = W := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous hW.isClosed hy
    · refine (HironakaResolutionSpace.subset_closure_diff_singularSet hW).trans
        (closure_minimal ?_ (hG.2.1.isClosedMap _ isClosed_closure))
      rintro x ⟨hxW,hxReg⟩
      obtain ⟨y,hy⟩ := hG.2.2.1 x
      refine ⟨y,subset_closure ⟨?_,?_⟩,hy⟩
      · change P y ∈ W
        rwa [hy]
      · rw [hExc]
        change P y ∉ S
        rwa [hy]
  exact ⟨R,Z,P,B,hG,hCmp,hIso,hSmooth,hImage,hExc,hSNC,hBOver,hBUnion,hNC⟩

end
end Hironaka.HironakaG8IsolatedCompactSingularAtlas
