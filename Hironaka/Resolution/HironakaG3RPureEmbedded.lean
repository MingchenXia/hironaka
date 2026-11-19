import Hironaka.Resolution.HironakaG3RChartOfMember
import Hironaka.Resolution.HironakaEmbeddedReducible

/-! # G3, target (A): glued embedded resolution of a closed analytic set of pure dimension

Lane G3 (run 0080, round 5).  Blueprint: `hironaka-g3-r-pure-embedded.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (section 5 (b)).

The reducible version of `HironakaG3RGluedEmbedded`.  Let `X` be a complex manifold, not necessarily compact, and `W ⊆ X` a
closed analytic set of **pure dimension `d < n`** in the convention of `HironakaEmbeddedReducible`: the points at which `W`
is a submanifold of dimension `d` are dense in `W` (`W ⊆ closure (regularLocus W d)`); `W` may be reducible.  Its singular
set is `W_sing = W \ regularLocus W d`, and `regOpen W d = X ∖ W_sing`.  The **embedded class** of `(W, d)` is the class
of stopped prefixes (`HironakaG3RStoppedOverlap`) of `(X, X, ∅, 𝓘_W, 1)` relative to `X ∖ W_sing`.

* Generic chart API for any class of local towers: `chartIncl`, `exceptionalLocus_chart`, `strictTransform_chart`,
  `regularAtDim_of_chart`, `chartBoundary` (the transformed divisor of a marked ideal along the chart's tower, carried into
  the glued space), `chartBoundary_subset_V`.
* `stopped_geometry`: over each member the embedded resolution geometry holds (the irreducible
  `HironakaG3RGluedEmbedded.stopped_geometry` with `HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus`
  in place of the irreducible `f⁻¹(V_sing) ⊆ Exc f`).
* **`IsGluedPureResolution W d X' P`**, **`existsUnique_gluedPureResolution`**: it exists and is unique up to unique
  biholomorphism over `X`.
* Global geometry: **`exceptionalLocus_eq`** (`Exc P = P⁻¹ W_sing`), **`isIsomorphismOver`** (over `X ∖ W_sing`),
  **`strictTransform_isClosedSubmanifold`**, **`regularAtDim_strictTransform`** (dimension `d` at every point), on each
  chart **`chart_boundary`**, and **`exists_chart_of_subset_isCompact`** (one stopped prefix over every relatively compact
  open set).
* `embeddedClass_carrier`, `isGluedPureResolution_iff`: for a closed irreducible `V` the class of `(V, dim V)` is the class
  `HironakaG3RGluedEmbedded.embeddedClass V`, so the irreducible statement is the special case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RPureEmbedded

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings CanonicalCentres MaxLocusLocal
  RestrictEmptyTower HironakaG3RTowerClass HironakaG3RStoppedOverlap HironakaBaseChange
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

variable {n : ℕ}

/-! ### Generic chart API -/

section Charts

variable {X : CMfd.{u} n} {𝒞 : LocalTowerClass X} {X' : CMfd.{u} n} {P : X' → X} (c : TowerChart 𝒞 X' P)

/-- The inclusion of the last stage of a chart into the glued space. -/
def chartIncl (y : c.Y) : X' := ((c.φ y : c.V) : X')

theorem isOpenHoloEmbedding_chartIncl : IsOpenHoloEmbedding n (chartIncl c) := ⟨c.V, c.φ, fun _ => rfl⟩

theorem proj_chartIncl (y : c.Y) : P (chartIncl c y) = ((c.T.proj y : c.U) : X) := c.proj_φ y

theorem chartIncl_symm (z : c.V) : chartIncl c (c.φ.symm z) = z := by
  rw [chartIncl, Diffeomorph.apply_symm_apply]

theorem range_chartIncl : range (chartIncl c) = (c.V : Set X') := by
  ext z
  refine ⟨fun ⟨y, hy⟩ => hy ▸ (c.φ y).2, fun hz => ⟨c.φ.symm ⟨z, hz⟩, chartIncl_symm c ⟨z, hz⟩⟩⟩

/-- The exceptional locus of the local tower is the trace of the exceptional locus of `P`. -/
theorem exceptionalLocus_chart (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P) :
    exceptionalLocus n c.T.proj = chartIncl c ⁻¹' exceptionalLocus n P :=
  exceptionalLocus_eq_preimage hP c.T.contMDiff_proj (isOpenHoloEmbedding_val c.U) (isOpenHoloEmbedding_chartIncl c)
    c.proj_φ

/-- The strict transform by the local tower is the trace of the strict transform by `P`. -/
theorem strictTransform_chart (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P) (A : Set X) :
    strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' A) = chartIncl c ⁻¹' strictTransform n P A :=
  strictTransform_preimage_eq hP c.T.contMDiff_proj (isOpenHoloEmbedding_val c.U) (isOpenHoloEmbedding_chartIncl c)
    c.proj_φ A

theorem regularAtDim_of_chart {A : Set X'} {y : c.Y} {d : ℕ}
    (h : RegularAtDim (n := n) (chartIncl c ⁻¹' A) y d) : RegularAtDim (n := n) A (chartIncl c y) d := by
  have h' : RegularAtDim (n := n) (c.φ ⁻¹' ((Subtype.val : c.V → X') ⁻¹' A)) y d := h
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp
    ((CodimOnePartCanonical.regularAtDim_preimage_iff c.φ).mp h')

/-- **The boundary of a chart for a marked ideal `M` of `X`**: the transformed divisor of `M|_U` along the chart's tower,
carried into the glued space. -/
def chartBoundary (M : MarkedIdeal n X) : List (Set X') :=
  (geoTransformAlong (pullback (Subtype.val : c.U → X) M) c.T).E.map (chartIncl c '' ·)

theorem chartBoundary_map_val (M : MarkedIdeal n X) :
    (chartBoundary c M).map ((Subtype.val : c.V → X') ⁻¹' ·) =
      (geoTransformAlong (pullback (Subtype.val : c.U → X) M) c.T).E.map (c.φ.symm ⁻¹' ·) := by
  unfold chartBoundary
  rw [List.map_map]
  congr 1
  funext H
  ext v
  simp only [Function.comp_apply, mem_preimage, mem_image]
  constructor
  · rintro ⟨y, hy, hyv⟩
    have hv : c.φ y = v := Subtype.ext hyv
    rw [← hv, c.φ.symm_apply_apply]
    exact hy
  · intro hv
    exact ⟨c.φ.symm v, hv, by rw [chartIncl_symm]⟩

theorem iUnion_map_image (L : List (Set c.Y)) :
    (⋃ H ∈ L.map (chartIncl c '' ·), H) = chartIncl c '' ⋃ H ∈ L, H := by
  ext z
  simp only [mem_iUnion, List.mem_map, mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨K, hK, rfl⟩, y, hy, rfl⟩
    exact ⟨y, ⟨K, hK, hy⟩, rfl⟩
  · rintro ⟨y, ⟨K, hK, hy⟩, rfl⟩
    exact ⟨_, ⟨K, hK, rfl⟩, y, hy, rfl⟩

theorem chartBoundary_subset_V (M : MarkedIdeal n X) {H : Set X'} (hH : H ∈ chartBoundary c M) : H ⊆ c.V := by
  obtain ⟨K, -, rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y, -, rfl⟩
  exact (c.φ y).2

end Charts

/-! ### Sets of pure dimension: `X ∖ W_sing` -/

section Pure

variable {X : CMfd.{u} n}

/-- **`X ∖ W_sing`** for `W_sing = W \ regularLocus W d` (written with `interior`, which does nothing for a closed `W`, so
that no proof enters the definition). -/
def regOpen (W : Set X) (d : ℕ) : Opens X :=
  ⟨interior (W \ regularLocus (n := n) W d)ᶜ, isOpen_interior⟩

theorem coe_regOpen {W : Set X} (hW : IsClosed W) (d : ℕ) :
    (regOpen W d : Set X) = (W \ regularLocus (n := n) W d)ᶜ :=
  (HironakaEmbeddedReducible.isClosed_diff_regularLocus hW d).isOpen_compl.interior_eq

theorem mem_regOpen_iff {W : Set X} (hW : IsClosed W) {d : ℕ} {x : X} :
    x ∈ regOpen W d ↔ x ∉ W \ regularLocus (n := n) W d := by
  change x ∈ (regOpen W d : Set X) ↔ _
  rw [coe_regOpen hW d]
  rfl

theorem regularAtDim_of_mem_regOpen {W : Set X} (hW : IsClosed W) {d : ℕ} {x : X} (hxW : x ∈ W)
    (hx : x ∈ regOpen W d) : RegularAtDim (n := n) W x d := by
  by_contra h
  exact (mem_regOpen_iff hW).mp hx ⟨hxW, h⟩

theorem subset_closure_inter_regOpen {W : Set X} (hW : IsClosed W) {d : ℕ}
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) : W ⊆ closure (W ∩ regOpen W d) :=
  hpure.trans (closure_mono fun _x hx => ⟨hx.2.1, (mem_regOpen_iff hW).mpr fun h => h.2 hx⟩)

/-- For a closed irreducible `V`, `X ∖ V_sing` is `EmbeddedFromResolution.regularOpen V`. -/
theorem regOpen_carrier (V : ClosedIrreducibleAnalyticSubvariety n X) :
    regOpen V.carrier V.dim = EmbeddedFromResolution.regularOpen V :=
  Opens.ext (coe_regOpen V.isClosed_carrier V.dim)

end Pure

/-! ### Geometry over a stopped prefix -/

section Geometry

variable {X : CMfd.{u} n}

/-- **The embedded class of `(W, d)`**: the stopped prefixes of `(X, X, ∅, 𝓘_W, 1)` relative to `X ∖ W_sing`. -/
def embeddedClass (W : Set X) (d : ℕ) : LocalTowerClass X :=
  stoppedClass (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (regOpen W d)

/-- For a closed irreducible `V`, the embedded class of `(V, dim V)` is `HironakaG3RGluedEmbedded.embeddedClass V`. -/
theorem embeddedClass_carrier (V : ClosedIrreducibleAnalyticSubvariety n X) :
    embeddedClass V.carrier V.dim = HironakaG3RGluedEmbedded.embeddedClass V := by
  unfold embeddedClass HironakaG3RGluedEmbedded.embeddedClass
  rw [regOpen_carrier]

/-- **Embedded resolution over a stopped prefix** (pure dimension `d < n`): for a member `S` of the embedded class over `U`,
with `E` the transformed divisor, `E` has simple normal crossings, `Exc S = ⋃ E = S⁻¹(W_sing ∩ U)`, `S` is an isomorphism over
`U ∖ W_sing`, and the strict transform of `W ∩ U` is a closed submanifold, of dimension `d` at each of its points, with only
normal crossings with `E`. -/
theorem stopped_geometry {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) (U : Opens X)
    {Y : CMfd.{u} n} (S : BlowupTower (CMfd.of (n := n) U) Y) (hS : embeddedClass W d U Y S) :
    IsSNCDivisor n (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E ∧
      exceptionalLocus n S.proj = ⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E, H ∧
      (⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E, H) =
          S.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d)) ∧
      IsIsomorphismOver n S.proj ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W))
        (geoTransformAlong (pullback (Subtype.val : U → X)
          (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) :=
    HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure
  have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have e := SmoothCentreInvariant.pullback_val_smoothCentreMarked U W
  change IsStopped _ (nestedOpens U (regOpen W d)) S at hS
  rw [e] at hS hdom₀ ⊢
  rw [HironakaEmbeddedReducible.preimage_val_diff_regularLocus U W d]
  set W₀ : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' W with hW₀def
  let O' : Opens (CMfd.of (n := n) U) := nestedOpens U (regOpen W d)
  have hO'c : ((O' : Set (CMfd.of (n := n) U))ᶜ) = W₀ \ regularLocus (n := n) W₀ d := by
    rw [hW₀def, ← HironakaEmbeddedReducible.preimage_val_diff_regularLocus U W d]
    ext x
    change x ∉ (Subtype.val : U → X) ⁻¹' (regOpen W d : Set X) ↔ _
    rw [mem_preimage, SetLike.mem_coe, mem_regOpen_iff hWa.isClosed, not_not]
    rfl
  have hWa₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  have hreg : ∀ x ∈ W₀, x ∈ O' → RegularAtDim (n := n) W₀ x d := fun x hxW hxO =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (regularAtDim_of_mem_regOpen hWa.isClosed hxW hxO)
  have hdense : W₀ ⊆ closure (W₀ ∩ O') := by
    intro x hx
    have h1 := subset_closure_inter_regOpen hWa.isClosed hpure hx
    have h2 := (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val
      (W ∩ regOpen W d)
    exact (Set.ext_iff.mp h2 x).mp h1
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hTt := hF.isGeoTestTower_of_isCanonical hdom₀ S hS.1
  have hgeo : IsClosedSubmanifold n (strictTransform n S.proj W₀) ∧
      (∀ x ∈ strictTransform n S.proj W₀, RegularAtDim (n := n) (strictTransform n S.proj W₀) x d) ∧
      HasNormalCrossings n (strictTransform n S.proj W₀)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W₀, 1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) S).E := by
    rcases hS.2.2 with ⟨c, hc, hcO⟩ | hres
    · have hadm := hF.isAdmissibleCentre_maxLocus hdom₀ S hS.1 hTt
      have hCV := fun y (hy : S.proj y ∈ O') =>
        HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa₀.isClosed O'
          (fun H hH => absurd hH List.not_mem_nil) (d := d) (fun x hx => hreg x hx x.2) hdom₀ S hS.1 hS.2.1 hc
          hcO hy
      obtain ⟨hSC, hev, hreg'⟩ :=
        HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid hWa₀ O' hreg hdense S hS.2.1 hadm.1 hCV
      exact ⟨⟨isClosed_closure, fun x hx => ⟨d, hreg' x hx⟩⟩, hreg',
        CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
          ⟨_, hSC hx, hev x hx, hadm.2.2⟩⟩
    · have hWO : ∀ x ∈ W₀, x ∉ O' := fun x hxW hxO => by
        obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence x
        have hy := (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid hWa₀.isClosed hdom₀ O' S hTt hS.2.1
          hxO).mpr hxW
        rw [hres.2] at hy
        exact hy
      have hW0 : W₀ = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        have h := hdense hx
        rw [show W₀ ∩ (O' : Set (CMfd.of (n := n) U)) = ∅ from
          eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2, closure_empty] at h
        exact h
      have hS0 : strictTransform n S.proj W₀ = ∅ := by
        rw [hW0]
        simp [strictTransform]
      rw [hS0]
      exact ⟨⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩, fun x hx => absurd hx (notMem_empty x),
        fun x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨hsnc, hsupp, hexc, hsing⟩ :=
    HironakaEmbeddedResolutionLocal.exceptionalDivisor_facts_of_centresAvoid hdom₀ rfl O' S hTt hS.2.1
  rw [hO'c] at hsing
  have hsub := HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus S.contMDiff_proj
    hWa₀.isClosed hgeo.2.1
  have hExcS : S.proj '' exceptionalLocus n S.proj ⊆ W₀ \ regularLocus (n := n) W₀ d := by
    rintro x ⟨z, hz, rfl⟩
    exact hsing (hexc hz)
  refine ⟨hsnc, ?_, ?_, HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    S.isBlowupSequence hExcS, hgeo.1, hgeo.2.1, hgeo.2.2⟩
  · rw [← hsupp]
    exact Subset.antisymm hexc (hsing.trans hsub)
  · rw [← hsupp]
    exact Subset.antisymm hsing (hsub.trans hexc)

end Geometry

/-! ### Glued embedded resolutions of sets of pure dimension -/

section Glued

variable {X : CMfd.{u} n}

/-- **A glued embedded resolution of `(W, d)`**: `P : X' → X` glued from the embedded class of `(W, d)` (holomorphic,
proper, surjective, and over the opens of a cover of `X` biholomorphically the stopped canonical prefixes). -/
def IsGluedPureResolution (W : Set X) (d : ℕ) (X' : CMfd.{u} n) (P : X' → X) : Prop :=
  IsGluedFrom (embeddedClass W d) X' P

/-- For a closed irreducible `V`, a glued embedded resolution of `(V, dim V)` is a glued embedded resolution of `V` in the
sense of `HironakaG3RGluedEmbedded`. -/
theorem isGluedPureResolution_iff (V : ClosedIrreducibleAnalyticSubvariety n X) (X' : CMfd.{u} n) (P : X' → X) :
    IsGluedPureResolution V.carrier V.dim X' P ↔ HironakaG3RGluedEmbedded.IsGluedEmbeddedResolution V X' P := by
  unfold IsGluedPureResolution HironakaG3RGluedEmbedded.IsGluedEmbeddedResolution
  rw [embeddedClass_carrier]

theorem hasComparisons_embeddedClass {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) : HasComparisons (embeddedClass W d) :=
  hasComparisons_stoppedClass hWa.isClosed (regOpen W d) (d := d)
    (fun x hx => regularAtDim_of_mem_regOpen hWa.isClosed hx x.2) (subset_closure_inter_regOpen hWa.isClosed hpure)
    (HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure)

/-- **Existence and uniqueness of the glued embedded resolution** of a closed analytic set of pure dimension `d < n`. -/
theorem existsUnique_gluedPureResolution {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedPureResolution W d X' P ∧
      ∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedPureResolution W d X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z :=
  existsUnique_isGluedFrom
    (covers_stoppedClass (HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure) _)
    (hasComparisons_embeddedClass hWa hd hpure)

/-- **A glued embedded resolution is a single stopped canonical prefix over every open set contained in a compact set.** -/
theorem exists_chart_of_subset_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {X' : CMfd.{u} n} {P : X' → X}
    (h : IsGluedPureResolution W d X' P) (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ c : TowerChart (embeddedClass W d) X' P, c.U = U := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) :=
    HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure
  obtain ⟨Y, T, hc, hr⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hdom hK U hUK
  have hmem : ∃ (Y' : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) U) Y'), embeddedClass W d U Y' S := by
    by_cases ha : CentresAvoid (nestedOpens U (regOpen W d)) T
    · exact ⟨Y, T, hc, ha, Or.inr hr⟩
    · obtain ⟨Y', T', -, -, h1, h2, c, hc', hcU⟩ :=
        EmbeddedFromResolution.exists_first_centre _ _ (nestedOpens U (regOpen W d)) T hc ha
      exact ⟨Y', T', h1, h2, Or.inl ⟨c, hc', hcU⟩⟩
  obtain ⟨Y', S, hS⟩ := hmem
  exact ⟨HironakaG3RChartOfMember.chartOfMember (hasComparisons_embeddedClass hWa hd hpure) S hS h.2.2.2
    h.1.continuous, rfl⟩

end Glued

/-! ### Global geometry -/

section GlobalGeometry

variable {X : CMfd.{u} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
  (hpure : W ⊆ closure (regularLocus (n := n) W d)) {X' : CMfd.{u} n} {P : X' → X}
  (h : IsGluedPureResolution W d X' P)
include hWa hd hpure h

theorem exists_chart_point (z : X') :
    ∃ (c : TowerChart (embeddedClass W d) X' P) (y : c.Y), chartIncl c y = z := by
  obtain ⟨c, hc⟩ := h.2.2.2 (P z)
  exact ⟨c, c.φ.symm ⟨z, c.mem_V hc⟩, chartIncl_symm c _⟩

/-- **`Exc P = P⁻¹ W_sing`.** -/
theorem exceptionalLocus_eq : exceptionalLocus n P = P ⁻¹' (W \ regularLocus (n := n) W d) := by
  ext z
  obtain ⟨c, y, rfl⟩ := exists_chart_point hWa hd hpure h z
  have hg := stopped_geometry hWa hd hpure c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  change chartIncl c y ∈ exceptionalLocus n P ↔ P (chartIncl c y) ∈ W \ regularLocus (n := n) W d
  rw [proj_chartIncl c y]
  rw [← mem_preimage (f := chartIncl c), ← hE, hg.2.1, hg.2.2.1]
  rfl

/-- **`P` is an isomorphism over `X ∖ W_sing`.** -/
theorem isIsomorphismOver : IsIsomorphismOver n P (W \ regularLocus (n := n) W d)ᶜ := by
  refine ⟨⟨fun z hz => hz, fun z₁ hz₁ z₂ hz₂ he => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨c, y₁, rfl⟩ := exists_chart_point hWa hd hpure h z₁
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he, proj_chartIncl c y₁]; exact (c.T.proj y₁).2)
    obtain ⟨y₂, rfl⟩ : z₂ ∈ range (chartIncl c) := by rw [range_chartIncl]; exact hz₂V
    have hg := stopped_geometry hWa hd hpure c.U c.T c.mem
    have hy : y₁ = y₂ := by
      refine hg.2.2.2.1.1.2.1 ?_ ?_ (Subtype.ext ?_)
      · change ((c.T.proj y₁ : c.U) : X) ∉ W \ regularLocus (n := n) W d
        rw [← proj_chartIncl c y₁]
        exact hz₁
      · change ((c.T.proj y₂ : c.U) : X) ∉ W \ regularLocus (n := n) W d
        rw [← proj_chartIncl c y₂]
        exact hz₂
      · rw [← proj_chartIncl c y₁, ← proj_chartIncl c y₂]
        exact he
    rw [hy]
  · obtain ⟨z, rfl⟩ := h.2.2.1 x
    exact ⟨z, hx, rfl⟩
  · rw [exceptionalLocus_eq hWa hd hpure h]
    exact Set.disjoint_left.mpr fun z hz hz' => hz hz'

/-- **The strict transform of `W` is regular of dimension `d` at each of its points.** -/
theorem regularAtDim_strictTransform :
    ∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d := by
  intro z hz
  obtain ⟨c, y, rfl⟩ := exists_chart_point hWa hd hpure h z
  have hg := stopped_geometry hWa hd hpure c.U c.T c.mem
  have hst := strictTransform_chart c h.1 W
  refine regularAtDim_of_chart c ?_
  rw [← hst]
  refine hg.2.2.2.2.2.1 y ?_
  rw [hst]
  exact hz

/-- **The strict transform of `W` is a closed submanifold of `X'`.** -/
theorem strictTransform_isClosedSubmanifold : IsClosedSubmanifold n (strictTransform n P W) :=
  ⟨isClosed_closure, fun z hz => ⟨d, regularAtDim_strictTransform hWa hd hpure h z hz⟩⟩

/-- **The boundary on a chart**: the chart boundary has simple normal crossings on the chart, its union is the exceptional
locus of `P` there, and the strict transform of `W` has only normal crossings with it. -/
theorem chart_boundary (c : TowerChart (embeddedClass W d) X' P) :
    IsSNCDivisor n ((chartBoundary c (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
        ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
      (⋃ H ∈ chartBoundary c (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X), H) =
        exceptionalLocus n P ∩ c.V ∧
      HasNormalCrossings n ((Subtype.val : c.V → X') ⁻¹' strictTransform n P W)
        ((chartBoundary c (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
          ((Subtype.val : c.V → X') ⁻¹' ·)) := by
  have hg := stopped_geometry hWa hd hpure c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  have hst := strictTransform_chart c h.1 W
  refine ⟨?_, ?_, ?_⟩
  · rw [chartBoundary_map_val]
    exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hg.1
  · rw [chartBoundary, iUnion_map_image, ← hg.2.1, hE, image_preimage_eq_inter_range, range_chartIncl]
  · rw [chartBoundary_map_val]
    have hpre : (Subtype.val : c.V → X') ⁻¹' strictTransform n P W =
        c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
      rw [hst]
      ext v
      change (v : X') ∈ strictTransform n P W ↔ chartIncl c (c.φ.symm v) ∈ strictTransform n P W
      rw [chartIncl_symm]
    rw [hpre]
    exact (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff c.φ.symm).mpr hg.2.2.2.2.2.2

end GlobalGeometry

end

end Hironaka.HironakaG3RPureEmbedded
