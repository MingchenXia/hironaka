import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertBridge
import Hironaka.Analytic.Unibranch.HironakaG10RmClosedSubspace
import Hironaka.Analytic.Unibranch.HironakaG10IrreducibleBoundary
import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticPreimage
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertReduction

/-!
# Native Remmert, items 5.6 and 5.7: constant-rank images and the assembly (lane G10MW)

* `nativeDimLE_univ_of_nativePureDim`, `le_of_nativeDimLE_univ` — dimension bookkeeping;
* `rankAt_univ_opens` — the rank on `univ` is unchanged by restricting to open subsets of source and target;
* **`constantRank_image`** (5.6) — if off `g⁻¹ B` the source is regular of dimension `d` with native rank `r`,
  then `E = g(Y) ∖ B` is analytic off `B`, of local dimension `≥ r` at its points, and its regular points have
  dimension `r` (the library's `ConstantRankImage.constantRankImage` on the manifold `Reg_d(Y) ∖ g⁻¹ B`);
* the assembly (5.7) of `NativeProperImageCore` from the inputs of items 5.3–5.5, packaged as the named `Prop`
  `RankInputs` (true; lane G10R3 proves its three parts): `nativeProperImageCore_of_rankInputs`, and with 5.0
  `nativeProperImage_of_rankInputs : RankInputs → NativeProperImage`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry Module
open IsManifold ChartedSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertAssembly

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus AnalyticDimensionBasics RankDegeneracy
  SourceReducedComplexSpace HironakaG10EpNativeDim
  Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular Hironaka.Analytic.Unibranch.HironakaG10MwRemmertBridge

noncomputable section

/-! ### Dimension bookkeeping -/

section Dim

variable {Y : SourceReducedComplexSpace}

theorem le_of_nativeDimLE_univ {m : ℕ} (h : NativeDimLE Y univ m) {y : Y.obj.left} {j : ℕ}
    (hy : intrinsicRegularAtDim Y.obj y j) : j ≤ m := by
  let e := LocalEmbedding.ofPoint Y y
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hreg : RegularAtDim (n := e.dim) e.carrier c.val j := by
    have h' := (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e c j).mp
    rw [hc] at h'
    exact h' hy
  have hT := h e
  rw [trace_univ] at hT
  exact hT _ _ hreg

theorem nativeDimLE_univ_of_nativePureDim {d : ℕ} (h : NativePureDim Y d) :
    NativeDimLE Y univ d := by
  intro e z j hz
  rw [trace_univ] at hz
  have hzC : z ∈ e.carrier := hz.2.1
  have hreg := (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e
    ⟨z, hzC⟩ j).mpr hz
  exact (h _ _ hreg).le

end Dim

/-! ### Ranks on open subsets -/

section Opens

variable {N k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel N) X]
  [IsComplexManifold N X] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- The rank on `univ` does not change under restriction to open subsets of source and target. -/
theorem rankAt_univ_opens (U : Opens X) (V : Opens M) {F : X → M} {G : U → V}
    (hG : ∀ y : U, (G y : M) = F y) (x : U)
    (hFd : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel k) F x)
    (hGd : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel k) G x) :
    rankAt (n := N) (n' := k) G univ x = rankAt (n := N) (n' := k) F univ (x : X) := by
  let eU := complexChartAt (n := N) x
  let eX := complexChartAt (n := N) (x : X)
  let eV := complexChartAt (n := k) (G x)
  let eM := complexChartAt (n := k) (F x)
  have hregU := AnalyticIrreducibleComponents.regularAtDim_univ (n := N) x
  have hregX := AnalyticIrreducibleComponents.regularAtDim_univ (n := N) (x : X)
  have hU := rankIn_eq_finrank_range_of_param hregU eU (mem_complexChartAt_source x) eV
    (mem_complexChartAt_source _) hGd (P := fun u => u) (u₀ := eU.val x) rfl differentiableAt_id
    (by rw [fderiv_fun_id]; exact Function.injective_id)
    (by filter_upwards [eU.val.open_target.mem_nhds (eU.val.map_source (mem_complexChartAt_source x))]
          with u hu
        exact ⟨hu, mem_univ _⟩)
  have hX := rankIn_eq_finrank_range_of_param hregX eX (mem_complexChartAt_source _) eM
    (mem_complexChartAt_source _) hFd (P := fun u => u) (u₀ := eX.val x) rfl differentiableAt_id
    (by rw [fderiv_fun_id]; exact Function.injective_id)
    (by filter_upwards [eX.val.open_target.mem_nhds (eX.val.map_source (mem_complexChartAt_source _))]
          with u hu
        exact ⟨hu, mem_univ _⟩)
  have hpt : eU.val x = eX.val x := rfl
  have heq : (fun u => eV.val (G (eU.val.symm u))) =ᶠ[𝓝 (eU.val x)]
      (fun u => eM.val (F (eX.val.symm u))) := by
    filter_upwards [eU.val.open_target.mem_nhds (eU.val.map_source (mem_complexChartAt_source x))]
      with u hu
    have h1 : eV.val (G (eU.val.symm u)) = eM.val ((G (eU.val.symm u) : M)) := by
      have hx : ((G x : V) : M) = F x := hG x
      show (chartAt (ComplexModel k) ((G x : V) : M)) ((G (eU.val.symm u) : V) : M) =
        (chartAt (ComplexModel k) (F x)) ((G (eU.val.symm u) : V) : M)
      rw [hx]
    have h2 : ((eU.val.symm u : U) : X) = eX.val.symm u :=
      OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt (ComplexModel N) (x : X)) ⟨x⟩ hu
    rw [h1, hG, h2]
  change rankIn eU eV G univ x = rankIn eX (complexChartAt (n := k) (F x)) F univ x
  rw [hU, hX, ← hpt, heq.fderiv_eq]

end Opens

/-! ### 5.6: the image of the constant-rank part -/

section ConstantRank

variable {Y : SourceReducedComplexSpace} [SecondCountableTopology Y.obj.left]
  {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M] {C : Set M} {hC : IsComplexAnalyticSubset (n := k) C}

/-- **5.6.**  If every point of `Y` off `g⁻¹ B` is regular of dimension `d` with native rank `r`, then
`E = g(Y ∖ g⁻¹ B)` has a presentation at every point off `B`, local dimension `≥ r` at each of its points, and
all its regular points have dimension `r`. -/
theorem constantRank_image (φ : Y ⟶ ofClosedAnalytic C hC) {d r : ℕ} {B : Set M}
    (hBc : IsClosed B) (hprop : IsProperMap (pointMap φ))
    (hreg : ∀ y, pointMap φ y ∉ B → y ∈ regLocus Y d)
    (hrank : ∀ (y : regLocus Y d), pointMap φ y.val ∉ B → nativeRankAt d φ y = r) :
    (∀ w ∉ B, Nonempty (ComplexAnalyticPresentationAt (n := k)
        (pointMap φ '' (pointMap φ ⁻¹' Bᶜ)) w)) ∧
      (∀ w ∈ pointMap φ '' (pointMap φ ⁻¹' Bᶜ),
        LocDimGE (n := k) (pointMap φ '' (pointMap φ ⁻¹' Bᶜ)) w r) ∧
      (∀ w j, RegularAtDim (n := k) (pointMap φ '' (pointMap φ ⁻¹' Bᶜ)) w j → j = r) := by
  set g := pointMap φ with hg
  set E := g '' (g ⁻¹' Bᶜ) with hE
  let U : Opens (regLocus Y d) :=
    ⟨{y | g y.val ∉ B}, hBc.isOpen_compl.preimage ((continuous_pointMap φ).comp continuous_subtype_val)⟩
  let Mo : Opens M := ⟨Bᶜ, hBc.isOpen_compl⟩
  let G : U → Mo := fun y => ⟨g y.val.val, y.property⟩
  have hGval : ∀ y : U, (G y : M) = regPointMap d φ y.val := fun _ => rfl
  have hRd : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
      (fun y : U => regPointMap d φ y.val) :=
    AnalyticSubsetOpens.contMDiff_restrict (contMDiff_regPointMap φ).contMDiffOn
  have hGs : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞ G :=
    (ContMDiff.subtypeVal_comp_iff Mo G).mp hRd
  have hrankG : ∀ x ∈ (univ : Set U), rankAt (n := d) (n' := k) G univ x = r := by
    intro x _
    rw [rankAt_univ_opens U Mo hGval x
      (((contMDiff_regPointMap φ) x.val).mdifferentiableAt (by simp))
      ((hGs x).mdifferentiableAt (by simp))]
    exact hrank x.val x.property
  have hpropG : ProperOn G (univ : Set U) := by
    intro K hK
    have hKM : IsCompact ((Subtype.val : Mo → M) '' K) := hK.image continuous_subtype_val
    have hpre : IsCompact (g ⁻¹' ((Subtype.val : Mo → M) '' K)) := hprop.isCompact_preimage hKM
    let ι : U → Y.obj.left := fun y => y.val.val
    have hι : IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    have hsub : g ⁻¹' ((Subtype.val : Mo → M) '' K) ⊆ range ι := by
      rintro y ⟨m, hmK, hmy⟩
      have hyB : g y ∉ B := by
        rw [← hmy]
        exact m.property
      exact ⟨⟨⟨y, hreg y hyB⟩, hyB⟩, rfl⟩
    have h := hι.isCompact_preimage' hpre hsub
    rw [univ_inter]
    convert h using 1
    ext y
    constructor
    · intro hy
      exact ⟨G y, hy, rfl⟩
    · rintro ⟨m, hmK, hmy⟩
      have : G y = m := Subtype.ext hmy.symm
      change G y ∈ K
      rw [this]
      exact hmK
  obtain ⟨hana, hloc, hdim⟩ := ConstantRankImage.constantRankImage (P := (univ : Set U)) isClosed_univ
    (fun x _ => AnalyticIrreducibleComponents.regularAtDim_univ x) hGs hrankG hpropG
  have hpreE : (Subtype.val : Mo → M) ⁻¹' E = G '' univ := by
    ext m
    constructor
    · rintro ⟨y, hyB, hym⟩
      exact ⟨⟨⟨y, hreg y hyB⟩, hyB⟩, mem_univ _, Subtype.ext hym⟩
    · rintro ⟨y, -, rfl⟩
      exact ⟨y.val.val, y.property, rfl⟩
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w j hwj => ?_⟩
  · have P := (hana ⟨w, hw⟩).some
    rw [← hpreE] at P
    exact ⟨AnalyticSubsetOpens.presentationOfPreimageVal ⟨w, hw⟩ P⟩
  · obtain ⟨y, hyB, rfl⟩ := hw
    have h := hloc (G ⟨⟨y, hreg y hyB⟩, hyB⟩) ⟨_, mem_univ _, rfl⟩
    rw [← hpreE] at h
    exact AnalyticSubsetOpens.locDimGE_preimage_val_iff.mp h
  · have hwE : w ∈ E := hwj.2.1
    have hwB : w ∈ Mo := by
      obtain ⟨y, hyB, rfl⟩ := hwE
      exact hyB
    have h : RegularAtDim (n := k) ((Subtype.val : Mo → M) ⁻¹' E) ⟨w, hwB⟩ j :=
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hwj
    rw [hpreE] at h
    exact hdim _ _ h

end ConstantRank

/-! ### 5.7: the assembly -/

/-- **The inputs of items 5.3–5.5** (lane G10R3), in the composed form used by the assembly: for a source of pure
dimension `d`, (5.3) the rank-degeneracy sets are analytic, (5.3) an irreducible source has a maximal rank `r`
whose degeneracy set is proper, and (5.4 + 5.5) if the rank is at most `r` everywhere, the image of a saturated
analytic set of dimension `≤ a` has regular points of dimension `≤ a - (d - r)` only. -/
def RankInputs : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left] (d k : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C) (φ : Y ⟶ ofClosedAnalytic C hC),
    NativePureDim Y d →
      (∀ r, Y.IsAnalyticSubset (rankDegeneracy d φ r)) ∧
      (Y.IsIrreducibleAnalyticSubset univ →
        ∃ r, (∀ y, nativeRankAt d φ y ≤ r) ∧ ¬ (univ ⊆ rankDegeneracy d φ r)) ∧
      (∀ r, (∀ y, nativeRankAt d φ y ≤ r) → ∀ T : Set Y.obj.left, Y.IsAnalyticSubset T →
        pointMap φ ⁻¹' (pointMap φ '' T) ⊆ T → ∀ a, NativeDimLE Y T a →
        ∀ w j, RegularAtDim (n := k) (pointMap φ '' T) w j → j + (d - r) ≤ a)

section Assembly

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M] {C : Set M} {hC : IsComplexAnalyticSubset (n := k) C}

/-- Restriction of a morphism to a reduced closed subspace. -/
theorem pointMap_inclusion_comp (Y : SourceReducedComplexSpace) (S : Set Y.obj.left)
    (hS : Y.IsAnalyticSubset S) (φ : Y ⟶ ofClosedAnalytic C hC) :
    range (pointMap (OriginalAnalyticClosedSubspace.inclusion Y S hS ≫ φ)) = pointMap φ '' S := by
  have h : pointMap (OriginalAnalyticClosedSubspace.inclusion Y S hS ≫ φ) =
      pointMap φ ∘ (OriginalAnalyticClosedSubspace.inclusion Y S hS).hom.left.base := rfl
  rw [h, range_comp, OriginalAnalyticClosedSubspace.inclusion_range]

theorem isProperMap_inclusion_comp (Y : SourceReducedComplexSpace) (S : Set Y.obj.left)
    (hS : Y.IsAnalyticSubset S) (φ : Y ⟶ ofClosedAnalytic C hC) (hprop : IsProperMap (pointMap φ)) :
    IsProperMap (pointMap (OriginalAnalyticClosedSubspace.inclusion Y S hS ≫ φ)) :=
  hprop.comp (OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding Y S hS).isProperMap

/-- **Dimension `0`**: the source is discrete and the image is locally finite. -/
theorem isComplexAnalyticSubset_range_of_dim_zero {Y : SourceReducedComplexSpace}
    (φ : Y ⟶ ofClosedAnalytic C hC) (hprop : IsProperMap (pointMap φ))
    (h0 : NativeDimLE Y univ 0) : IsComplexAnalyticSubset (n := k) (range (pointMap φ)) := by
  have hdisc : DiscreteTopology Y.obj.left := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun y => ?_
    obtain ⟨U, hU, hyU, hUy⟩ := exists_isolated_of_nativeDimLE_zero isAnalyticSubset_univ h0 (mem_univ y)
    have : U = {y} := by
      apply Subset.antisymm
      · intro z hz
        exact hUy ⟨hz, mem_univ z⟩
      · rintro z rfl
        exact hyU
    rw [← this]
    exact hU
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel k) M
  intro w
  obtain ⟨K, hKc, hKw⟩ := exists_compact_mem_nhds w
  have hfin : (pointMap φ ⁻¹' K).Finite := (hprop.isCompact_preimage hKc).finite_of_discrete
  have hT : IsComplexAnalyticSubset (n := k) (pointMap φ '' (pointMap φ ⁻¹' K)) :=
    ProperMappingInduction.isComplexAnalyticSubset_of_finite (hfin.image _)
  refine RemmertStatements.nonempty_presentation_of_inter_eq isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hKw) ?_ (hT w).some
  ext z
  constructor
  · rintro ⟨⟨y, rfl⟩, hz⟩
    exact ⟨⟨y, (interior_subset hz : pointMap φ y ∈ K), rfl⟩, hz⟩
  · rintro ⟨⟨y, -, rfl⟩, hz⟩
    exact ⟨⟨y, rfl⟩, hz⟩

/-- The induction hypothesis of the assembly, for a fixed target. -/
def CoreAt (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C) (m : ℕ) : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left], NativeDimLE Y univ m →
    ∀ φ : Y ⟶ ofClosedAnalytic C hC, IsProperMap (pointMap φ) →
      IsComplexAnalyticSubset (n := k) (range (pointMap φ))

/-- **The irreducible case** (Demailly II.8.8, Step 1, natively). -/
theorem irreducible_step (hR : RankInputs) {m : ℕ} (IH : ∀ m' < m, CoreAt C hC m')
    (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left]
    (hm : NativeDimLE Y univ m) (hirr : Y.IsIrreducibleAnalyticSubset univ)
    (φ : Y ⟶ ofClosedAnalytic C hC) (hprop : IsProperMap (pointMap φ)) :
    IsComplexAnalyticSubset (n := k) (range (pointMap φ)) := by
  set g := pointMap φ with hg
  obtain ⟨d, hd⟩ := HironakaG10RmClosedSubspace.exists_nativePureDim_of_irreducible hirr
  obtain _ | d' := d
  · exact isComplexAnalyticSubset_range_of_dim_zero φ hprop (nativeDimLE_univ_of_nativePureDim hd)
  set d := d' + 1 with hdd
  obtain ⟨hSa, hmax, hfib⟩ := hR Y d k M C hC φ hd
  obtain ⟨r, hrle, hrS⟩ := hmax hirr
  set S := rankDegeneracy d φ r with hSdef
  have hS : Y.IsAnalyticSubset S := hSa r
  -- a regular point of rank `≥ r`, hence `r ≤ d ≤ m`
  obtain ⟨y₀, -, hy₀S⟩ := not_subset.mp hrS
  have hy₀reg : y₀ ∈ regLocus Y d := by
    have hy₀ : y₀ ∈ intrinsicRegularLocus Y.obj := by
      by_contra h
      exact hy₀S (Or.inl h)
    obtain ⟨j, hj⟩ := hy₀
    have := hd y₀ j hj
    rw [this] at hj
    exact hj
  have hrd : r ≤ d := by
    have hr0 : r ≤ nativeRankAt d φ ⟨y₀, hy₀reg⟩ := by
      by_contra h
      exact hy₀S (Or.inr ⟨hy₀reg, lt_of_not_ge h⟩)
    exact hr0.trans (rankAt_le_of_regularAtDim _
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := d) (⟨y₀, hy₀reg⟩ : regLocus Y d)))
  have hdm : d ≤ m := le_of_nativeDimLE_univ hm hy₀reg
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- `g(S)` is analytic by induction
  have hSdense : (univ : Set Y.obj.left) ⊆ closure (univ \ S) :=
    HironakaG10IrreducibleBoundary.subset_closure_diff_of_irreducible hirr hS hrS
  have hSdim : NativeDimLE Y S m' :=
    nativeDimLE_of_subset_of_dense isAnalyticSubset_univ (subset_univ S) hSdense hm
  let : SecondCountableTopology (OriginalAnalyticClosedSubspace.sourceObject Y S hS).obj.left :=
    HironakaG10RmClosedSubspace.secondCountableTopology_sourceObject Y S hS
  have hB : IsComplexAnalyticSubset (n := k) (g '' S) := by
    have h := IH m' (Nat.lt_succ_self m') (OriginalAnalyticClosedSubspace.sourceObject Y S hS)
      (HironakaG10RmClosedSubspace.nativeDimLE_univ_sourceObject Y S hS hSdim)
      (OriginalAnalyticClosedSubspace.inclusion Y S hS ≫ φ)
      (isProperMap_inclusion_comp Y S hS φ hprop)
    rwa [pointMap_inclusion_comp] at h
  set B := g '' S with hBdef
  have hBc : IsClosed B := hB.isClosed
  -- the saturation `Y' = g⁻¹ B`
  set Y' := g ⁻¹' B with hY'def
  by_cases hY' : (univ : Set Y.obj.left) ⊆ Y'
  · have : range g = B := by
      apply Subset.antisymm
      · rintro _ ⟨y, rfl⟩
        exact hY' (mem_univ y)
      · rintro _ ⟨y, -, rfl⟩
        exact ⟨y, rfl⟩
    rw [this]
    exact hB
  have hY'a : Y.IsAnalyticSubset Y' := by
    have h1 : (ofClosedAnalytic C hC).IsAnalyticSubset ((Subtype.val : C → M) ⁻¹' B) :=
      isAnalyticSubset_preimage_val hC hB
    exact SourceReducedComplexSpace.IsAnalyticSubset.preimage h1 φ
  have hY'dense : (univ : Set Y.obj.left) ⊆ closure (univ \ Y') :=
    HironakaG10IrreducibleBoundary.subset_closure_diff_of_irreducible hirr hY'a hY'
  have hY'dim : NativeDimLE Y Y' d' :=
    nativeDimLE_of_subset_of_dense isAnalyticSubset_univ (subset_univ Y') hY'dense
      (nativeDimLE_univ_of_nativePureDim hd)
  have hSY' : S ⊆ Y' := fun y hy => ⟨y, hy, rfl⟩
  have hgY' : g '' Y' = B := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · exact image_mono hSY'
  have hsat : g ⁻¹' (g '' Y') ⊆ Y' := by
    rw [hgY']
  have hBreg : ∀ w j, RegularAtDim (n := k) B w j → j < r := by
    intro w j hw
    rw [← hgY'] at hw
    have := hfib r hrle Y' hY'a hsat d' hY'dim w j hw
    omega
  -- off `g⁻¹ B` the source is regular of dimension `d` with rank `r`
  have hreg : ∀ y, g y ∉ B → y ∈ regLocus Y d := by
    intro y hy
    have hyS : y ∉ S := fun h => hy (hSY' h)
    have hyr : y ∈ intrinsicRegularLocus Y.obj := by
      by_contra h
      exact hyS (Or.inl h)
    obtain ⟨j, hj⟩ := hyr
    have := hd y j hj
    rw [this] at hj
    exact hj
  have hrank : ∀ y : regLocus Y d, g y.val ∉ B → nativeRankAt d φ y = r := by
    intro y hy
    have hyS : y.val ∉ S := fun h => hy (hSY' h)
    refine le_antisymm (hrle y) ?_
    by_contra h
    exact hyS (Or.inr ⟨y.property, lt_of_not_ge h⟩)
  obtain ⟨hpres, hloc, hdimE⟩ := constantRank_image φ hBc hprop hreg hrank
  set E := g '' (g ⁻¹' Bᶜ) with hEdef
  have hEB : Disjoint E B := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have hEdim : DimLE (n := k) E (m' + 1) := by
    intro w j hw
    rw [hdimE w j hw]
    omega
  have hclos : IsComplexAnalyticSubset (n := k) (closure E) :=
    ProperMappingTheorem.remmertSteinStatement (m' + 1) hB hBreg hEB hpres hEdim hloc
  have hrange : range g = closure E ∪ B := by
    apply Subset.antisymm
    · rintro _ ⟨y, rfl⟩
      by_cases hy : g y ∈ B
      · exact Or.inr hy
      · exact Or.inl (subset_closure ⟨y, hy, rfl⟩)
    · apply union_subset
      · exact closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact ⟨y, rfl⟩) hprop.isClosed_range
      · rintro _ ⟨y, -, rfl⟩
        exact ⟨y, rfl⟩
  rw [hrange]
  exact ConstantRankImage.IsComplexAnalyticSubset.union hclos hB

/-- **The general case**: finitely many global components meet the preimage of a compact set. -/
theorem core_step (hR : RankInputs) {m : ℕ} (IH : ∀ m' < m, CoreAt C hC m') : CoreAt C hC m := by
  intro Y _ hm φ hprop
  set g := pointMap φ with hg
  have hcomp : ∀ B ∈ HironakaG10RmGlobalComponents.nativeGlobalComponents Y,
      IsComplexAnalyticSubset (n := k) (g '' B) := by
    intro B hBc
    have hB := HironakaG10RmGlobalComponents.isAnalyticSubset_of_mem_nativeGlobalComponents hBc
    let : SecondCountableTopology (OriginalAnalyticClosedSubspace.sourceObject Y B hB).obj.left :=
      HironakaG10RmClosedSubspace.secondCountableTopology_sourceObject Y B hB
    have h := irreducible_step hR IH (OriginalAnalyticClosedSubspace.sourceObject Y B hB)
      (HironakaG10RmClosedSubspace.nativeDimLE_univ_sourceObject Y B hB
        (hm.anti isAnalyticSubset_univ (subset_univ B)))
      (HironakaG10RmClosedSubspace.isIrreducibleAnalyticSubset_univ_sourceObject_of_mem_nativeGlobalComponents
        Y B hB hBc)
      (OriginalAnalyticClosedSubspace.inclusion Y B hB ≫ φ)
      (isProperMap_inclusion_comp Y B hB φ hprop)
    rwa [pointMap_inclusion_comp] at h
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel k) M
  intro w
  obtain ⟨K, hKc, hKw⟩ := exists_compact_mem_nhds w
  have hfinI := (HironakaG10RmGlobalComponents.locallyFinite_nativeGlobalComponents Y).finite_nonempty_inter_compact
    (hprop.isCompact_preimage hKc)
  set t := hfinI.toFinset with ht
  have hT : IsComplexAnalyticSubset (n := k)
      (⋃ B ∈ t, g '' ((B : HironakaG10RmGlobalComponents.nativeGlobalComponents Y) : Set Y.obj.left)) :=
    ConstantRankImage.isComplexAnalyticSubset_biUnion t fun B _ => hcomp B B.2
  refine RemmertStatements.nonempty_presentation_of_inter_eq isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hKw) ?_ (hT w).some
  ext z
  simp only [mem_inter_iff, mem_iUnion, mem_image, exists_prop, mem_range]
  constructor
  · rintro ⟨⟨y, rfl⟩, hz⟩
    refine ⟨?_, hz⟩
    have hy : y ∈ ⋃₀ HironakaG10RmGlobalComponents.nativeGlobalComponents Y := by
      rw [HironakaG10RmGlobalComponents.sUnion_nativeGlobalComponents]
      exact mem_univ y
    obtain ⟨B, hB, hyB⟩ := hy
    refine ⟨⟨B, hB⟩, ?_, y, hyB, rfl⟩
    rw [ht, Set.Finite.mem_toFinset]
    exact ⟨y, hyB, (interior_subset hz : g y ∈ K)⟩
  · rintro ⟨⟨B, -, y, -, rfl⟩, hz⟩
    exact ⟨⟨y, rfl⟩, hz⟩

/-- The assembly, for a fixed target, by strong induction on the dimension. -/
theorem coreAt (hR : RankInputs) (m : ℕ) : CoreAt C hC m := by
  induction m using Nat.strong_induction_on with
  | _ m IH => exact core_step hR IH

end Assembly

/-- **5.7: the core of native Remmert from the inputs of items 5.3–5.5.** -/
theorem nativeProperImageCore_of_rankInputs (hR : RankInputs) : NativeProperImageCore := by
  intro Y _ m hm k M _ _ _ C hC φ hprop
  exact coreAt hR m Y hm φ hprop

/-- **Native Remmert from the inputs of items 5.3–5.5** (with 5.0). -/
theorem nativeProperImage_of_rankInputs (hR : RankInputs) : NativeProperImage :=
  HironakaG10MwRemmertReduction.nativeProperImage_of_core (nativeProperImageCore_of_rankInputs hR)

end

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertAssembly
