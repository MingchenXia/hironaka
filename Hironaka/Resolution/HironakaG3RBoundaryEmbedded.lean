import Hironaka.Resolution.HironakaG3RBoundaryOverlap
import Hironaka.Resolution.HironakaG3RPureEmbedded

/-! # G3, target (A): glued embedded resolution relative to a simple normal crossings boundary

Lane G3 (run 0080, round 6).  Blueprint: `hironaka-g3-r-boundary-embedded.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (G3P03′, the boundary-relative embedded resolution).

The noncompact, glued version of `HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact`.  Let `X` be a
complex manifold, not necessarily compact, `E₀` a divisor on `X` with simple normal crossings in the convention of the domain
(a finite list of closed sets, `IsSNCDivisor n E₀`; a member may have infinitely many connected components), and `W ⊆ X` a
closed analytic set of pure dimension `d < n` (held convention `W ⊆ closure (regularLocus W d)`; reducible allowed) such
that no member of `E₀` contains a nonempty relatively open subset of `W` (`W ⊆ closure (W \ |E₀|)`).  Put
`W_sing = W \ regularLocus W d` and `F = W_sing ∪ (W ∩ |E₀|)`.

* `bdryOpen W d E₀ = X ∖ (W_sing ∪ |E₀|)`; the **boundary class** `bdryClass W d E₀` of stopped canonical prefixes of
  `(X, X, E₀, 𝓘_W, 1)` relative to `bdryOpen W d E₀`; `bdryClass_nil`: with `E₀ = []` it is the embedded class of
  `HironakaG3RPureEmbedded`.
* `geometry_of_isStopped`, **`bdry_stopped_geometry`**: over each member the transformed divisor `E` has simple normal
  crossings, `Exc ⊆ ⋃ (new members) ⊆ (preimage of F)`, the preimage of `W_sing` lies in `Exc`, `⋃ E` is the total
  transform of `|E₀|` together with the new members, the tower is an isomorphism over the complement of `F`, and the strict
  transform of `W` is a closed submanifold of dimension `d` with only normal crossings with `E`.
* **`IsGluedBoundaryResolution W d E₀ X' P`** (glued from the boundary class), **`existsUnique_gluedBoundaryResolution`**
  (existence, uniqueness up to unique biholomorphism over `X`), **`exists_chart_of_subset_isCompact`** (one stopped prefix
  over every relatively compact open set).
* Global geometry: **`preimage_sing_subset_exceptionalLocus`**, **`exceptionalLocus_subset`**, **`isIsomorphismOver`**,
  **`regularAtDim_strictTransform`**, **`strictTransform_isClosedSubmanifold`**, and on each chart **`chart_boundary`** (the
  chart boundary has simple normal crossings, its union is `(P⁻¹|E₀| ∪ Exc P) ∩ P⁻¹U`, and the strict transform has only
  normal crossings with it).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RBoundaryEmbedded

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings CanonicalCentres MaxLocusLocal
  RestrictEmptyTower HironakaG3RTowerClass HironakaG3RStoppedOverlap HironakaBaseChange HironakaAdmissibleSequence
  HironakaG3RPureEmbedded HironakaG3RBoundaryOverlap
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

variable {n : ℕ}

/-! ### The open set `X ∖ (W_sing ∪ |E₀|)` -/

section Open

variable {X : CMfd.{u} n}

/-- **`X ∖ (W_sing ∪ |E₀|)`** (written with `interior`, which does nothing when `W` and the members of `E₀` are closed, so
that no proof enters the definition). -/
def bdryOpen (W : Set X) (d : ℕ) (E₀ : List (Set X)) : Opens X :=
  ⟨interior (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H)ᶜ, isOpen_interior⟩

theorem isClosed_sing_union {W : Set X} (hW : IsClosed W) (d : ℕ) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) :
    IsClosed (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H) :=
  (HironakaEmbeddedReducible.isClosed_diff_regularLocus hW d).union
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀)

theorem coe_bdryOpen {W : Set X} (hW : IsClosed W) (d : ℕ) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) :
    (bdryOpen W d E₀ : Set X) = (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H)ᶜ :=
  (isClosed_sing_union hW d hE₀).isOpen_compl.interior_eq

theorem mem_bdryOpen_iff {W : Set X} (hW : IsClosed W) {d : ℕ} {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H)
    {x : X} : x ∈ bdryOpen W d E₀ ↔ x ∉ W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H := by
  change x ∈ (bdryOpen W d E₀ : Set X) ↔ _
  rw [coe_bdryOpen hW d hE₀]
  rfl

/-- With the empty divisor, `X ∖ (W_sing ∪ |E₀|)` is `X ∖ W_sing`. -/
theorem bdryOpen_nil (W : Set X) (d : ℕ) : bdryOpen W d [] = regOpen W d := by
  have h : (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ ([] : List (Set X)), H) = W \ regularLocus (n := n) W d := by
    simp
  apply Opens.ext
  show interior (W \ regularLocus (n := n) W d ∪ ⋃ H ∈ ([] : List (Set X)), H)ᶜ =
    interior (W \ regularLocus (n := n) W d)ᶜ
  rw [h]

theorem regularAtDim_of_mem_bdryOpen {W : Set X} (hW : IsClosed W) {d : ℕ} {E₀ : List (Set X)}
    (hE₀ : ∀ H ∈ E₀, IsClosed H) {x : X} (hxW : x ∈ W) (hx : x ∈ bdryOpen W d E₀) : RegularAtDim (n := n) W x d := by
  by_contra h
  exact (mem_bdryOpen_iff hW hE₀).mp hx (Or.inl ⟨hxW, h⟩)

theorem disjoint_bdryOpen {W : Set X} (hW : IsClosed W) (d : ℕ) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H) :
    ∀ H ∈ E₀, Disjoint H (bdryOpen W d E₀ : Set X) := fun _ hH =>
  disjoint_left.mpr fun _x hxH hxO => (mem_bdryOpen_iff hW hE₀).mp hxO (Or.inr (mem_biUnion hH hxH))

theorem subset_closure_inter_bdryOpen {W : Set X} (hW : IsClosed W) {d : ℕ}
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : ∀ H ∈ E₀, IsClosed H)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) : W ⊆ closure (W ∩ bdryOpen W d E₀) := by
  rw [coe_bdryOpen hW d hE₀]
  exact HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀) hE₀W

/-- **`(X, X, E₀, 𝓘_W, 1)` lies in the domain** (`W` of pure dimension `d < n`, `E₀` with simple normal crossings). -/
theorem isInvDomain_bdry {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) :=
  HironakaEmbeddedBoundary.isInvDomain_boundary (M := X) hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀

end Open

/-! ### Geometry over a stopped prefix relative to the boundary -/

section Geometry

variable {X : CMfd.{u} n}

/-- **The boundary class of `(W, d, E₀)`**: the stopped prefixes of `(X, X, E₀, 𝓘_W, 1)` relative to
`X ∖ (W_sing ∪ |E₀|)`. -/
def bdryClass (W : Set X) (d : ℕ) (E₀ : List (Set X)) : LocalTowerClass X :=
  stoppedClass (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (bdryOpen W d E₀)

/-- With the empty divisor the boundary class is the embedded class of `HironakaG3RPureEmbedded`. -/
theorem bdryClass_nil (W : Set X) (d : ℕ) : bdryClass W d [] = embeddedClass W d := by
  unfold bdryClass embeddedClass
  rw [bdryOpen_nil]

/-- **Embedded resolution relative to `E₀` over a stopped prefix on `X` itself.** -/
theorem geometry_of_isStopped {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {Y : CMfd.{u} n} (S : BlowupTower X Y)
    (hS : IsStopped (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (bdryOpen W d E₀) S) :
    IsSNCDivisor n (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E ∧
      exceptionalLocus n S.proj ⊆
        ⋃ H ∈ (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E.drop E₀.length, H) ⊆
        S.proj ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      S.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n S.proj ∧
      (⋃ H ∈ (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) =
        S.proj ⁻¹' (⋃ H ∈ E₀, H) ∪
          ⋃ H ∈ (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E.drop E₀.length, H ∧
      IsIsomorphismOver n S.proj (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n S.proj W) ∧
      (∀ x ∈ strictTransform n S.proj W, RegularAtDim (n := n) (strictTransform n S.proj W) x d) ∧
      HasNormalCrossings n (strictTransform n S.proj W)
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ with h𝔪
  have hdom : IsInvDomain n 𝔪 := isInvDomain_bdry hWa hd hpure hE₀
  set O : Opens X := bdryOpen W d E₀ with hOdef
  have hEO := disjoint_bdryOpen hWa.isClosed d hE₀.1
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := fun x hxW hxO =>
    regularAtDim_of_mem_bdryOpen hWa.isClosed hE₀.1 hxW hxO
  have hdense : W ⊆ closure (W ∩ O) := subset_closure_inter_bdryOpen hWa.isClosed hpure hE₀.1 hE₀W
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (canonicalInvariant n)
  have hTt := hF.isGeoTestTower_of_isCanonical hdom S hS.1
  have hgeo : IsClosedSubmanifold n (strictTransform n S.proj W) ∧
      (∀ x ∈ strictTransform n S.proj W, RegularAtDim (n := n) (strictTransform n S.proj W) x d) ∧
      HasNormalCrossings n (strictTransform n S.proj W) (geoTransformAlong 𝔪 S).E := by
    rcases hS.2.2 with ⟨c, hc, hcO⟩ | hres
    · have hadm := hF.isAdmissibleCentre_maxLocus hdom S hS.1 hTt
      have hCV := fun y (hy : S.proj y ∈ O) =>
        HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O hEO (d := d)
          (fun x hx => hreg x hx x.2) hdom S hS.1 hS.2.1 hc hcO hy
      obtain ⟨hSC, hev, hreg'⟩ :=
        HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid hWa O hreg hdense S hS.2.1 hadm.1 hCV
      exact ⟨⟨isClosed_closure, fun x hx => ⟨d, hreg' x hx⟩⟩, hreg',
        CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
          ⟨_, hSC hx, hev x hx, hadm.2.2⟩⟩
    · have hWO : ∀ x ∈ W, x ∉ O := fun x hxW hxO => by
        obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective S.isBlowupSequence x
        have hy := (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid hWa.isClosed hdom O S hTt hS.2.1
          hxO).mpr hxW
        rw [hres.2] at hy
        exact hy
      have hW0 : W = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        have h := hdense hx
        rw [show W ∩ (O : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2,
          closure_empty] at h
        exact h
      have hS0 : strictTransform n S.proj W = ∅ := by
        rw [hW0]
        simp [strictTransform]
      rw [hS0]
      exact ⟨⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩, fun x hx => absurd hx (notMem_empty x),
        fun x hx => absurd hx (notMem_empty x)⟩
  set F : Set X := W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H with hFdef
  have hcos : 𝔪.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed E₀
  have hover : CentresOver F S := by
    refine HironakaEmbeddedBoundary.centresOver_of_inter_subset (F := 𝔪.cosupp) (G := ((O : Set X)ᶜ)) ?_ S
      (centresOver_cosupp 𝔪 hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent S hTt)
      (centresOver_compl_of_centresAvoid O S hS.2.1)
    rintro x ⟨hxW, hxO⟩
    rw [hcos] at hxW
    have hxO' : x ∈ W \ regularLocus (n := n) W d ∪ ⋃ H ∈ E₀, H := by
      by_contra h
      exact hxO ((mem_bdryOpen_iff hWa.isClosed hE₀.1).mpr h)
    rcases hxO' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hxW, h⟩
  have hsuppF := HironakaEmbeddedBoundary.support_exceptionalDivisor_subset_of_centresOver F S hover
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop 𝔪 hE₀.1 S
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support S
  have hsnc := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom S hTt).isWellFormed.isSNCDivisor
  have hsub := HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus S.contMDiff_proj
    hWa.isClosed hgeo.2.1
  have hExcF : S.proj '' exceptionalLocus n S.proj ⊆ F := by
    rintro x ⟨z, hz, rfl⟩
    exact hsuppF (hexc hz)
  have hunion := biUnion_E_geoTransformAlong 𝔪 hE₀.1 S
  refine ⟨hsnc, ?_, ?_, hsub, ?_,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset S.isBlowupSequence hExcF,
    hgeo.1, hgeo.2.1, hgeo.2.2⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF
  · rw [hunion, hsupp]

/-- **Embedded resolution relative to `E₀` over a member of the boundary class** (over `U`, relative to `E₀|_U`): with `E`
the transformed divisor and `F = W_sing ∪ (W ∩ |E₀|)`, `E` has simple normal crossings, `Exc ⊆ ⋃ (new members) ⊆ S⁻¹F`,
`S⁻¹ W_sing ⊆ Exc`, `⋃ E = S⁻¹|E₀| ∪ ⋃ (new members)`, `S` is an isomorphism over `U ∖ F`, and the strict transform of
`W ∩ U` is a closed submanifold, of dimension `d` at each of its points, with only normal crossings with `E`. -/
theorem bdry_stopped_geometry {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) (U : Opens X) {Y : CMfd.{u} n} (S : BlowupTower (CMfd.of (n := n) U) Y)
    (hS : bdryClass W d E₀ U Y S) :
    IsSNCDivisor n (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E ∧
      exceptionalLocus n S.proj ⊆ ⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E.drop E₀.length, H ∧
      (⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E.drop E₀.length, H) ⊆
        S.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      S.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n S.proj ∧
      (⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
        (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E, H) =
        S.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' ⋃ H ∈ E₀, H) ∪
          ⋃ H ∈ (geoTransformAlong (pullback (Subtype.val : U → X)
            (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E.drop E₀.length, H ∧
      IsIsomorphismOver n S.proj
        ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n S.proj ((Subtype.val : U → X) ⁻¹' W))
        (geoTransformAlong (pullback (Subtype.val : U → X)
          (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) S).E := by
  have hdom := isInvDomain_bdry hWa hd hpure hE₀
  have hdom₀ := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have e := HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal U E₀ W
  change IsStopped _ (nestedOpens U (bdryOpen W d E₀)) S at hS
  rw [e] at hS hdom₀ ⊢
  set W₀ : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' W with hW₀def
  set E₀' : List (Set (CMfd.of (n := n) U)) := E₀.map ((Subtype.val : U → X) ⁻¹' ·) with hE₀'def
  have hWa₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  have hopen := U.isOpen.isOpenMap_subtype_val
  have hpure₀ : W₀ ⊆ closure (regularLocus (n := n) W₀ d) := by
    intro x hx
    have h1 : (x : X) ∈ closure (regularLocus (n := n) W d) := hpure hx
    have h3 : x ∈ closure ((Subtype.val : U → X) ⁻¹' regularLocus (n := n) W d) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    refine closure_mono (fun y hy => ?_) h3
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hy
  have hE₀'snc : IsSNCDivisor n E₀' := hdom₀.isWellFormed.isSNCDivisor
  have hU : (Subtype.val : U → X) ⁻¹' (⋃ H ∈ E₀, H) = ⋃ H ∈ E₀', H :=
    HironakaEmbeddedBoundary.preimage_biUnion_list _ E₀
  have hE₀W₀ : W₀ ⊆ closure (W₀ \ ⋃ H ∈ E₀', H) := by
    intro x hx
    have h1 : (x : X) ∈ closure (W \ ⋃ H ∈ E₀, H) := hE₀W hx
    have h3 : x ∈ closure ((Subtype.val : U → X) ⁻¹' (W \ ⋃ H ∈ E₀, H)) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    rwa [preimage_sdiff, hU] at h3
  have hS' : (Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d) = W₀ \ regularLocus (n := n) W₀ d :=
    HironakaEmbeddedReducible.preimage_val_diff_regularLocus U W d
  have hF : (Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) =
      W₀ \ regularLocus (n := n) W₀ d ∪ W₀ ∩ ⋃ H ∈ E₀', H := by
    rw [preimage_union, preimage_inter, hU, hS']
  have hO : (nestedOpens U (bdryOpen W d E₀) : Set (CMfd.of (n := n) U)) = bdryOpen W₀ d E₀' := by
    rw [coe_bdryOpen hWa₀.isClosed d hE₀'snc.1]
    ext x
    show (x : X) ∈ (bdryOpen W d E₀ : Set X) ↔ x ∈ (W₀ \ regularLocus (n := n) W₀ d ∪ ⋃ H ∈ E₀', H)ᶜ
    rw [coe_bdryOpen hWa.isClosed d hE₀.1, ← hS', ← hU, ← preimage_union, ← preimage_compl]
    rfl
  have hlen : E₀'.length = E₀.length := List.length_map _
  rw [hF, hS', hU, ← hlen]
  exact geometry_of_isStopped hWa₀ hd hpure₀ hE₀'snc hE₀W₀ S (hS.congr_open hO)

end Geometry

/-! ### Glued embedded resolutions relative to a boundary -/

section Glued

variable {X : CMfd.{u} n}

/-- **A glued embedded resolution of `(W, d)` relative to `E₀`**: `P : X' → X` glued from the boundary class (holomorphic,
proper, surjective, and over the opens of a cover of `X` biholomorphically the stopped canonical prefixes of
`(U, U, E₀|_U, 𝓘_{W ∩ U}, 1)` relative to `U ∖ (W_sing ∪ |E₀|)`). -/
def IsGluedBoundaryResolution (W : Set X) (d : ℕ) (E₀ : List (Set X)) (X' : CMfd.{u} n) (P : X' → X) : Prop :=
  IsGluedFrom (bdryClass W d E₀) X' P

/-- With the empty divisor it is the glued embedded resolution of `HironakaG3RPureEmbedded`. -/
theorem isGluedBoundaryResolution_nil (W : Set X) (d : ℕ) (X' : CMfd.{u} n) (P : X' → X) :
    IsGluedBoundaryResolution W d [] X' P ↔ IsGluedPureResolution W d X' P := by
  unfold IsGluedBoundaryResolution IsGluedPureResolution
  rw [bdryClass_nil]

/-- **The overlap lemma for the boundary class.** -/
theorem hasComparisons_bdryClass {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) : HasComparisons (bdryClass W d E₀) :=
  hasComparisons_stoppedClass_bdry hWa.isClosed (bdryOpen W d E₀) (disjoint_bdryOpen hWa.isClosed d hE₀.1) (d := d)
    (fun x hx => regularAtDim_of_mem_bdryOpen hWa.isClosed hE₀.1 hx x.2)
    (subset_closure_inter_bdryOpen hWa.isClosed hpure hE₀.1 hE₀W) (isInvDomain_bdry hWa hd hpure hE₀)

/-- **Existence and uniqueness of the glued embedded resolution relative to a boundary.** -/
theorem existsUnique_gluedBoundaryResolution {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedBoundaryResolution W d E₀ X' P ∧
      ∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedBoundaryResolution W d E₀ X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z :=
  existsUnique_isGluedFrom (covers_stoppedClass (isInvDomain_bdry hWa hd hpure hE₀) _)
    (hasComparisons_bdryClass hWa hd hpure hE₀ hE₀W)

/-- **A glued embedded resolution relative to a boundary is a single stopped canonical prefix over every open set contained
in a compact set.** -/
theorem exists_chart_of_subset_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {X' : CMfd.{u} n} {P : X' → X}
    (h : IsGluedBoundaryResolution W d E₀ X' P) (U : Opens X) {K : Set X} (hK : IsCompact K)
    (hUK : (U : Set X) ⊆ K) : ∃ c : TowerChart (bdryClass W d E₀) X' P, c.U = U := by
  obtain ⟨Y, T, hc, hr⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) (isInvDomain_bdry hWa hd hpure hE₀) hK U hUK
  have hmem : ∃ (Y' : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) U) Y'), bdryClass W d E₀ U Y' S := by
    by_cases ha : CentresAvoid (nestedOpens U (bdryOpen W d E₀)) T
    · exact ⟨Y, T, hc, ha, Or.inr hr⟩
    · obtain ⟨Y', T', -, -, h1, h2, c, hc', hcU⟩ :=
        EmbeddedFromResolution.exists_first_centre _ _ (nestedOpens U (bdryOpen W d E₀)) T hc ha
      exact ⟨Y', T', h1, h2, Or.inl ⟨c, hc', hcU⟩⟩
  obtain ⟨Y', S, hS⟩ := hmem
  exact ⟨HironakaG3RChartOfMember.chartOfMember (hasComparisons_bdryClass hWa hd hpure hE₀ hE₀W) S hS h.2.2.2
    h.1.continuous, rfl⟩

end Glued

/-! ### Global geometry -/

section ChartImage

variable {X : CMfd.{u} n} {𝒞 : LocalTowerClass X} {X' : CMfd.{u} n} {P : X' → X}

/-- The image in the glued space of the preimage of `A ⊆ X` in a chart is `P⁻¹A` on the chart. -/
theorem image_chartIncl_preimage (c : TowerChart 𝒞 X' P) (A : Set X) :
    chartIncl c '' (c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' A)) = P ⁻¹' A ∩ c.V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · show P (chartIncl c y) ∈ A
      rw [proj_chartIncl c y]
      exact hy
    · rw [← range_chartIncl c]
      exact ⟨y, rfl⟩
  · rintro ⟨hzA, hzV⟩
    rw [← range_chartIncl c] at hzV
    obtain ⟨y, rfl⟩ := hzV
    refine ⟨y, ?_, rfl⟩
    show ((c.T.proj y : c.U) : X) ∈ A
    rw [← proj_chartIncl c y]
    exact hzA

end ChartImage

section GlobalGeometry

variable {X : CMfd.{u} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
  (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
  (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) {X' : CMfd.{u} n} {P : X' → X}
  (h : IsGluedBoundaryResolution W d E₀ X' P)
include hWa hd hpure hE₀ hE₀W h

theorem exists_chart_point (z : X') :
    ∃ (c : TowerChart (bdryClass W d E₀) X' P) (y : c.Y), chartIncl c y = z := by
  obtain ⟨c, hc⟩ := h.2.2.2 (P z)
  exact ⟨c, c.φ.symm ⟨z, c.mem_V hc⟩, chartIncl_symm c _⟩

/-- **`P⁻¹ W_sing ⊆ Exc P`.** -/
theorem preimage_sing_subset_exceptionalLocus :
    P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P := by
  intro z hz
  obtain ⟨c, y, rfl⟩ := exists_chart_point hWa hd hpure hE₀ hE₀W h z
  have hg := bdry_stopped_geometry hWa hd hpure hE₀ hE₀W c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  have hy : y ∈ exceptionalLocus n c.T.proj := hg.2.2.2.1 (by
    show ((c.T.proj y : c.U) : X) ∈ W \ regularLocus (n := n) W d
    rw [← proj_chartIncl c y]
    exact hz)
  rw [hE] at hy
  exact hy

/-- **`Exc P ⊆ P⁻¹ F`**, `F = W_sing ∪ (W ∩ |E₀|)`. -/
theorem exceptionalLocus_subset :
    exceptionalLocus n P ⊆ P ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) := by
  intro z hz
  obtain ⟨c, y, rfl⟩ := exists_chart_point hWa hd hpure hE₀ hE₀W h z
  have hg := bdry_stopped_geometry hWa hd hpure hE₀ hE₀W c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  have hy : y ∈ exceptionalLocus n c.T.proj := by
    rw [hE]
    exact hz
  have hyF := hg.2.2.1 (hg.2.1 hy)
  show P (chartIncl c y) ∈ W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
  rw [proj_chartIncl c y]
  exact hyF

/-- **`P` is an isomorphism over `X ∖ F`**, `F = W_sing ∪ (W ∩ |E₀|)`. -/
theorem isIsomorphismOver : IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ := by
  refine ⟨⟨fun z hz => hz, fun z₁ hz₁ z₂ hz₂ he => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨c, y₁, rfl⟩ := exists_chart_point hWa hd hpure hE₀ hE₀W h z₁
    have hz₂V : z₂ ∈ c.V := c.mem_V (by rw [← he, proj_chartIncl c y₁]; exact (c.T.proj y₁).2)
    obtain ⟨y₂, rfl⟩ : z₂ ∈ range (chartIncl c) := by rw [range_chartIncl]; exact hz₂V
    have hg := bdry_stopped_geometry hWa hd hpure hE₀ hE₀W c.U c.T c.mem
    have hy : y₁ = y₂ := by
      refine hg.2.2.2.2.2.1.1.2.1 ?_ ?_ (Subtype.ext ?_)
      · change ((c.T.proj y₁ : c.U) : X) ∉ W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
        rw [← proj_chartIncl c y₁]
        exact hz₁
      · change ((c.T.proj y₂ : c.U) : X) ∉ W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H
        rw [← proj_chartIncl c y₂]
        exact hz₂
      · rw [← proj_chartIncl c y₁, ← proj_chartIncl c y₂]
        exact he
    rw [hy]
  · obtain ⟨z, rfl⟩ := h.2.2.1 x
    exact ⟨z, hx, rfl⟩
  · exact Set.disjoint_left.mpr fun z hz hz' =>
      hz (exceptionalLocus_subset hWa hd hpure hE₀ hE₀W h hz')

/-- **The strict transform of `W` is regular of dimension `d` at each of its points.** -/
theorem regularAtDim_strictTransform :
    ∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d := by
  intro z hz
  obtain ⟨c, y, rfl⟩ := exists_chart_point hWa hd hpure hE₀ hE₀W h z
  have hg := bdry_stopped_geometry hWa hd hpure hE₀ hE₀W c.U c.T c.mem
  have hst := strictTransform_chart c h.1 W
  refine regularAtDim_of_chart c ?_
  rw [← hst]
  refine hg.2.2.2.2.2.2.2.1 y ?_
  rw [hst]
  exact hz

/-- **The strict transform of `W` is a closed submanifold of `X'`.** -/
theorem strictTransform_isClosedSubmanifold : IsClosedSubmanifold n (strictTransform n P W) :=
  ⟨isClosed_closure, fun z hz => ⟨d, regularAtDim_strictTransform hWa hd hpure hE₀ hE₀W h z hz⟩⟩

/-- **The boundary on a chart**: the chart boundary has simple normal crossings on the chart, its union is the total transform
of `|E₀|` together with the exceptional locus of `P` there, and the strict transform of `W` has only normal crossings with
it. -/
theorem chart_boundary (c : TowerChart (bdryClass W d E₀) X' P) :
    IsSNCDivisor n ((chartBoundary c (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
        ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
      (⋃ H ∈ chartBoundary c (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X), H) =
        (P ⁻¹' (⋃ H ∈ E₀, H) ∪ exceptionalLocus n P) ∩ c.V ∧
      HasNormalCrossings n ((Subtype.val : c.V → X') ⁻¹' strictTransform n P W)
        ((chartBoundary c (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)).map
          ((Subtype.val : c.V → X') ⁻¹' ·)) := by
  have hg := bdry_stopped_geometry hWa hd hpure hE₀ hE₀W c.U c.T c.mem
  have hE := exceptionalLocus_chart c h.1
  have hst := strictTransform_chart c h.1 W
  refine ⟨?_, ?_, ?_⟩
  · rw [chartBoundary_map_val]
    exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hg.1
  · rw [chartBoundary, iUnion_map_image, hg.2.2.2.2.1, image_union, image_chartIncl_preimage]
    ext z
    constructor
    · rintro (hz | ⟨y, hy, rfl⟩)
      · exact ⟨Or.inl hz.1, hz.2⟩
      · refine ⟨?_, by rw [← range_chartIncl c]; exact ⟨y, rfl⟩⟩
        have hzF : P (chartIncl c y) ∈ W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H := by
          rw [proj_chartIncl c y]
          exact hg.2.2.1 hy
        rcases hzF with hs | ⟨-, hb⟩
        · exact Or.inr (preimage_sing_subset_exceptionalLocus hWa hd hpure hE₀ hE₀W h hs)
        · exact Or.inl hb
    · rintro ⟨hz | hz, hzV⟩
      · exact Or.inl ⟨hz, hzV⟩
      · right
        rw [← range_chartIncl c] at hzV
        obtain ⟨y, rfl⟩ := hzV
        refine ⟨y, hg.2.1 ?_, rfl⟩
        rw [hE]
        exact hz
  · rw [chartBoundary_map_val]
    have hpre : (Subtype.val : c.V → X') ⁻¹' strictTransform n P W =
        c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
      rw [hst]
      ext v
      change (v : X') ∈ strictTransform n P W ↔ chartIncl c (c.φ.symm v) ∈ strictTransform n P W
      rw [chartIncl_symm]
    rw [hpre]
    exact (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff c.φ.symm).mpr hg.2.2.2.2.2.2.2.2

end GlobalGeometry

end

end Hironaka.HironakaG3RBoundaryEmbedded
