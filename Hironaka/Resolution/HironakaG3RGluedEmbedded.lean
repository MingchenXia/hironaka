import Hironaka.Resolution.HironakaG3RStoppedOverlap
import Hironaka.Resolution.HironakaRelativelyCompact

/-! # G3, target (A): embedded resolution on a glued space (A-miss-3)

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-glued-embedded.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-3, sections 4 and 5 (b)).

Let `X` be a complex manifold, not necessarily compact, and `V ⊆ X` a closed irreducible analytic subvariety with
`dim V < n`.  The **embedded class** of `V` is the class of stopped prefixes (`HironakaG3RStoppedOverlap`) of
`(X, X, ∅, 𝓘_V, 1)` relative to `X ∖ V_sing`: over an open `U`, the canonical segments of `(U, U, ∅, 𝓘_{V ∩ U}, 1)` cut
before their first centre meeting the preimage of `U ∖ V_sing`.

* `stopped_geometry`: over each member the embedded resolution geometry holds (the conclusions of the held
  `HironakaRelativelyCompact.exists_embeddedResolution_of_subset_isCompact`, for a member instead of a constructed tower).
* **`IsGluedEmbeddedResolution V X' P`** (glued from the embedded class, `HironakaG3RTowerClass.IsGluedFrom`),
  **`existsUnique_gluedEmbeddedResolution`**: it exists and is unique up to unique biholomorphism over `X`.
* Global geometry of any glued embedded resolution `P : X' → X`: **`exceptionalLocus_eq`** (`Exc P = P⁻¹ V_sing`),
  **`isIsomorphismOver`** (`P` is an isomorphism over `X ∖ V_sing`), **`strictTransform_isClosedSubmanifold`** and
  **`regularAtDim_strictTransform`** (the strict transform of `V` is a closed submanifold of `X'` of dimension `dim V` at each
  of its points), and on each chart **`chart_boundary`**: the chart boundary (the transformed divisor of the local stopped
  prefix, carried into `X'`) has simple normal crossings, its union is `Exc P` on the chart, and the strict transform has
  only normal crossings with it.
* **`exists_glued_embeddedResolution`**: the packaged statement (A-miss-3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RGluedEmbedded

noncomputable section

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings CanonicalCentres MaxLocusLocal
  RestrictEmptyTower HironakaG3RTowerClass HironakaG3RStoppedOverlap HironakaBaseChange
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)
open EmbeddedFromResolution (regularOpen regularAtDim_of_mem_regularOpen isInvDomain_vanishingIdeal_of_dim_lt)

variable {n : ℕ} {X : CMfd.{u} n}

/-! ### Geometry over a stopped prefix -/

/-- **The embedded class of `V`**: the stopped prefixes of `(X, X, ∅, 𝓘_V, 1)` relative to `X ∖ V_sing`. -/
def embeddedClass (V : ClosedIrreducibleAnalyticSubvariety n X) : LocalTowerClass X :=
  stoppedClass (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) (regularOpen V)

/-- **Embedded resolution over a stopped prefix**: for a member `S` of the embedded class over `U`, with `E` the transformed
divisor, `E` has simple normal crossings, `Exc S = ⋃ E = S⁻¹(V_sing ∩ U)`, `S` is an isomorphism over `U ∖ V_sing`, and the
strict transform of `V ∩ U` is a closed submanifold, of dimension `dim V` at each of its points, with only normal crossings
with `E`. -/
theorem stopped_geometry (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n) (U : Opens X)
    {Y : CMfd.{u} n} (S : BlowupTower (CMfd.of (n := n) U) Y) (hS : embeddedClass V U Y S) :
    IsSNCDivisor n (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) S).E ∧
      exceptionalLocus n S.proj = ⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) S).E, H ∧
      (⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) S).E, H) =
          S.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n S.proj ((Subtype.val : U → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' V.carrier))
        (geoTransformAlong (pullback (Subtype.val : U → X)
          (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) S).E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
  have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have e := SmoothCentreInvariant.pullback_val_smoothCentreMarked U V.carrier
  change IsStopped _ (nestedOpens U (regularOpen V)) S at hS
  rw [e] at hS hdom₀ ⊢
  set W : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' V.carrier with hWdef
  let O' : Opens (CMfd.of (n := n) U) := nestedOpens U (regularOpen V)
  have hO'c : ((O' : Set (CMfd.of (n := n) U))ᶜ) = (Subtype.val : U → X) ⁻¹' singularLocus V := by
    ext x
    exact not_not
  have hWa : IsComplexAnalyticSubset (n := n) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val V.analytic
  have hreg : ∀ x ∈ W, x ∈ O' → RegularAtDim (n := n) W x V.dim := fun x hxW hxO =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (regularAtDim_of_mem_regularOpen hxW hxO)
  have hdense : W ⊆ closure (W ∩ O') := by
    intro x hx
    have h1 := HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V hx
    have h2 := (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val
      (V.carrier ∩ regularOpen V)
    exact (Set.ext_iff.mp h2 x).mp h1
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hTt := hF.isGeoTestTower_of_isCanonical hdom₀ S hS.1
  have hgeo : IsClosedSubmanifold n (strictTransform n S.proj W) ∧
      (∀ x ∈ strictTransform n S.proj W, RegularAtDim (n := n) (strictTransform n S.proj W) x V.dim) ∧
      HasNormalCrossings n (strictTransform n S.proj W)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) U)) S).E := by
    rcases hS.2.2 with ⟨c, hc, hcO⟩ | hres
    · have hadm := hF.isAdmissibleCentre_maxLocus hdom₀ S hS.1 hTt
      have hCV := fun y (hy : S.proj y ∈ O') =>
        HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O'
          (fun H hH => absurd hH List.not_mem_nil) (d := V.dim) (fun x hx => hreg x hx x.2) hdom₀ S hS.1 hS.2.1 hc
          hcO hy
      obtain ⟨hSC, hev, hreg'⟩ :=
        HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid hWa O' hreg hdense S hS.2.1 hadm.1 hCV
      exact ⟨⟨isClosed_closure, fun x hx => ⟨V.dim, hreg' x hx⟩⟩, hreg',
        CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
          ⟨_, hSC hx, hev x hx, hadm.2.2⟩⟩
    · have hWO : ∀ x ∈ W, x ∉ O' := fun x hxW hxO => by
        obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence x
        have hy := (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid hWa.isClosed hdom₀ O' S hTt hS.2.1
          hxO).mpr hxW
        rw [hres.2] at hy
        exact hy
      have hW0 : W = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        have h := hdense hx
        rw [show W ∩ (O' : Set (CMfd.of (n := n) U)) = ∅ from
          eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2, closure_empty] at h
        exact h
      have hS0 : strictTransform n S.proj W = ∅ := by
        rw [hW0]
        simp [strictTransform]
      rw [hS0]
      exact ⟨⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩, fun x hx => absurd hx (notMem_empty x),
        fun x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨hsnc, hsupp, hexc, hsing⟩ :=
    HironakaEmbeddedResolutionLocal.exceptionalDivisor_facts_of_centresAvoid hdom₀ rfl O' S hTt hS.2.1
  rw [hO'c] at hsing
  have hsub := HironakaRelativelyCompact.preimage_val_singularLocus_subset_exceptionalLocus S.contMDiff_proj V hgeo.2.1
  have hExcS : S.proj '' exceptionalLocus n S.proj ⊆ (Subtype.val : U → X) ⁻¹' singularLocus V := by
    rintro x ⟨z, hz, rfl⟩
    exact hsing (hexc hz)
  refine ⟨hsnc, ?_, ?_, HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    S.isBlowupSequence hExcS, hgeo.1, hgeo.2.1, hgeo.2.2⟩
  · rw [← hsupp]
    exact Subset.antisymm hexc (hsing.trans hsub)
  · rw [← hsupp]
    exact Subset.antisymm hsing (hsub.trans hexc)

/-! ### Glued embedded resolutions -/

/-- **A glued embedded resolution of `V`**: `P : X' → X` glued from the embedded class of `V` (holomorphic, proper,
surjective, and over the opens of a cover of `X` biholomorphically the stopped canonical prefixes). -/
def IsGluedEmbeddedResolution (V : ClosedIrreducibleAnalyticSubvariety n X) (X' : CMfd.{u} n) (P : X' → X) : Prop :=
  IsGluedFrom (embeddedClass V) X' P

/-- **Existence and uniqueness of the glued embedded resolution** (`dim V < n`). -/
theorem existsUnique_gluedEmbeddedResolution (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedEmbeddedResolution V X' P ∧
      ∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedEmbeddedResolution V X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
  exact existsUnique_isGluedFrom (covers_stoppedClass hdom (regularOpen V))
    (hasComparisons_stoppedClass V.isClosed_carrier (regularOpen V) (d := V.dim)
      (fun x hx => regularAtDim_of_mem_regularOpen hx x.2)
      (HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V) hdom)

section Charts

variable {V : ClosedIrreducibleAnalyticSubvariety n X} {X' : CMfd.{u} n} {P : X' → X}
  (c : TowerChart (embeddedClass V) X' P)

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

/-- **The boundary of a chart**: the transformed divisor of the local stopped prefix, carried into `X'`. -/
def chartBoundary : List (Set X') :=
  (geoTransformAlong (pullback (Subtype.val : c.U → X)
    (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) c.T).E.map (chartIncl c '' ·)

theorem chartBoundary_map_val :
    (chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·) =
      (geoTransformAlong (pullback (Subtype.val : c.U → X)
        (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) c.T).E.map (c.φ.symm ⁻¹' ·) := by
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

theorem iUnion_chartBoundary (L : List (Set c.Y)) :
    (⋃ H ∈ L.map (chartIncl c '' ·), H) = chartIncl c '' ⋃ H ∈ L, H := by
  ext z
  simp only [mem_iUnion, List.mem_map, mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨K, hK, rfl⟩, y, hy, rfl⟩
    exact ⟨y, ⟨K, hK, hy⟩, rfl⟩
  · rintro ⟨y, ⟨K, hK, hy⟩, rfl⟩
    exact ⟨_, ⟨K, hK, rfl⟩, y, hy, rfl⟩

end Charts

/-! ### Global geometry -/

section Geometry

variable {V : ClosedIrreducibleAnalyticSubvariety n X} (hV : V.dim < n) {X' : CMfd.{u} n} {P : X' → X}
  (h : IsGluedEmbeddedResolution V X' P)
include hV h

theorem exists_chart_point (z : X') :
    ∃ (c : TowerChart (embeddedClass V) X' P) (y : c.Y), chartIncl c y = z := by
  obtain ⟨c, hc⟩ := h.2.2.2 (P z)
  exact ⟨c, c.φ.symm ⟨z, c.mem_V hc⟩, chartIncl_symm c _⟩

/-- **`Exc P = P⁻¹ V_sing`.** -/
theorem exceptionalLocus_eq : exceptionalLocus n P = P ⁻¹' singularLocus V := by
  ext z
  obtain ⟨c, y, rfl⟩ := exists_chart_point hV h z
  have hg := stopped_geometry V hV c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  change chartIncl c y ∈ exceptionalLocus n P ↔ P (chartIncl c y) ∈ singularLocus V
  rw [proj_chartIncl c y]
  rw [← mem_preimage (f := chartIncl c), ← hE, hg.2.1, hg.2.2.1]
  rfl

/-- **`P` is an isomorphism over `X ∖ V_sing`.** -/
theorem isIsomorphismOver : IsIsomorphismOver n P (singularLocus V)ᶜ := by
  refine ⟨⟨fun z hz => hz, fun z₁ hz₁ z₂ hz₂ he => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨c, y₁, rfl⟩ := exists_chart_point hV h z₁
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he, proj_chartIncl c y₁]; exact (c.T.proj y₁).2)
    obtain ⟨y₂, rfl⟩ : z₂ ∈ range (chartIncl c) := by rw [range_chartIncl]; exact hz₂V
    have hg := stopped_geometry V hV c.U c.T c.mem
    have hy : y₁ = y₂ := by
      refine hg.2.2.2.1.1.2.1 ?_ ?_ (Subtype.ext ?_)
      · change ((c.T.proj y₁ : c.U) : X) ∉ singularLocus V
        rw [← proj_chartIncl c y₁]
        exact hz₁
      · change ((c.T.proj y₂ : c.U) : X) ∉ singularLocus V
        rw [← proj_chartIncl c y₂]
        exact hz₂
      · rw [← proj_chartIncl c y₁, ← proj_chartIncl c y₂]
        exact he
    rw [hy]
  · obtain ⟨z, rfl⟩ := h.2.2.1 x
    exact ⟨z, hx, rfl⟩
  · rw [exceptionalLocus_eq hV h]
    exact Set.disjoint_left.mpr fun z hz hz' => hz hz'

/-- **The strict transform of `V` is regular of dimension `dim V` at each of its points.** -/
theorem regularAtDim_strictTransform :
    ∀ z ∈ strictTransform n P V.carrier, RegularAtDim (n := n) (strictTransform n P V.carrier) z V.dim := by
  intro z hz
  obtain ⟨c, y, rfl⟩ := exists_chart_point hV h z
  have hg := stopped_geometry V hV c.U c.T c.mem
  have hst := strictTransform_chart c h.1 V.carrier
  refine regularAtDim_of_chart c ?_
  rw [← hst]
  refine hg.2.2.2.2.2.1 y ?_
  rw [hst]
  exact hz

/-- **The strict transform of `V` is a closed submanifold of `X'`.** -/
theorem strictTransform_isClosedSubmanifold : IsClosedSubmanifold n (strictTransform n P V.carrier) :=
  ⟨isClosed_closure, fun z hz => ⟨V.dim, regularAtDim_strictTransform hV h z hz⟩⟩

/-- **The boundary on a chart**: the chart boundary has simple normal crossings on the chart, its union is the exceptional
locus of `P` there, and the strict transform of `V` has only normal crossings with it. -/
theorem chart_boundary (c : TowerChart (embeddedClass V) X' P) :
    IsSNCDivisor n ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
      (⋃ H ∈ chartBoundary c, H) = exceptionalLocus n P ∩ c.V ∧
      HasNormalCrossings n ((Subtype.val : c.V → X') ⁻¹' strictTransform n P V.carrier)
        ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) := by
  have hg := stopped_geometry V hV c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  have hst := strictTransform_chart c h.1 V.carrier
  refine ⟨?_, ?_, ?_⟩
  · rw [chartBoundary_map_val]
    exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hg.1
  · rw [chartBoundary, iUnion_chartBoundary, ← hg.2.1, hE, image_preimage_eq_inter_range, range_chartIncl]
  · rw [chartBoundary_map_val]
    have hpre : (Subtype.val : c.V → X') ⁻¹' strictTransform n P V.carrier =
        c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' V.carrier) := by
      rw [hst]
      ext v
      change (v : X') ∈ strictTransform n P V.carrier ↔ chartIncl c (c.φ.symm v) ∈ strictTransform n P V.carrier
      rw [chartIncl_symm]
    rw [hpre]
    exact (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff c.φ.symm).mpr hg.2.2.2.2.2.2

end Geometry

/-- **A-miss-3: embedded resolution on a noncompact complex manifold, glued.**  Let `V` be a closed irreducible analytic
subvariety of a complex manifold `X` (not necessarily compact) with `dim V < n`.  There is a glued embedded resolution
`P : X' → X` (holomorphic, proper, surjective; over the opens of a cover of `X` biholomorphically the canonical stopped
prefixes), unique up to unique biholomorphism over `X`, such that `Exc P = P⁻¹ V_sing`, `P` is an isomorphism over
`X ∖ V_sing`, the strict transform of `V` is a closed submanifold of `X'` of dimension `dim V` at each of its points, and on
each chart the boundary has simple normal crossings, has union `Exc P`, and has only normal crossings with the strict
transform. -/
theorem exists_glued_embeddedResolution (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : V.dim < n) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedEmbeddedResolution V X' P ∧
      (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedEmbeddedResolution V X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
      exceptionalLocus n P = P ⁻¹' singularLocus V ∧
      IsIsomorphismOver n P (singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P V.carrier) ∧
      (∀ z ∈ strictTransform n P V.carrier, RegularAtDim (n := n) (strictTransform n P V.carrier) z V.dim) ∧
      ∀ c : TowerChart (embeddedClass V) X' P,
        IsSNCDivisor n ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
        (⋃ H ∈ chartBoundary c, H) = exceptionalLocus n P ∩ c.V ∧
        HasNormalCrossings n ((Subtype.val : c.V → X') ⁻¹' strictTransform n P V.carrier)
          ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) := by
  obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedEmbeddedResolution V hV
  exact ⟨X', P, h, huniq, exceptionalLocus_eq hV h, isIsomorphismOver hV h, strictTransform_isClosedSubmanifold hV h,
    regularAtDim_strictTransform hV h, chart_boundary hV h⟩

end

end Hironaka.HironakaG3RGluedEmbedded
