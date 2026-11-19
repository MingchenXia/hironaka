import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
import Hironaka.Resolution.HironakaG3RGluedUniqueness
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyBaseComparison
import Hironaka.Resolution.HironakaOriginalTerminalOpenComparison

/-! # G3, target (A): the boundary of the glued canonical resolution (A-miss-2, normal-crossings form)

Lane G3 (run 0080, round 3).  Blueprint: `hironaka-g3-r-glued-boundary.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-2).

For a chart `c = (U, T, φ)` of a glued canonical resolution `P : X' → X` (`HironakaG3RGluedUniqueness.GluedChart`), the
**chart boundary** `c.boundary` is the final boundary list of the local canonical resolution `T`, carried into `X'` by `φ`.

* **`boundary_overlap`**: for two charts `c₁, c₂`, the ordered lists of NONEMPTY traces of the two chart boundaries on
  `P⁻¹(U¹ ∩ U²)` are EQUAL (as lists of subsets of `X'`).  From the held transport of the filtered final boundary along the
  unique comparison of two canonical resolutions over a base biholomorphism
  (`HironakaOriginalBoundaryEmptyBaseComparison.terminal_choice_over_base_across_empty_boundaries`), the restriction of the
  boundary to open subsets (`HironakaOriginalTerminalOpenComparison.original_terminal_open_whole_record`) and rigidity
  (`HironakaG3RGluedUniqueness.eq_of_proj_eq`).
* **`gluedBoundary M X' P`**: the union of all members of all chart boundaries (intrinsic: no chart is chosen).
  `gluedBoundary_inter_V`: on every chart it is the union of that chart's boundary; `isClosed_gluedBoundary`;
  `isSNCDivisor_boundary`: on every chart the boundary members form a simple normal crossings divisor.  So the boundary of
  the glued resolution is a closed divisor with normal crossings whose ordered local members are intrinsic.

NOT claimed: a GLOBAL indexing of the boundary by smooth hypersurfaces (global simple normal crossings).  The values of the
canonical invariant are not chart independent (they shift by the order embeddings of
`HironakaOriginalFiniteEmptyCompression.original_recursive_family_empty_free_compression` when empty years are deleted), so
the value indexing proposed in round 2 does not work as stated; see `G3-TARGET-A.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RGluedBoundary

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal HironakaOriginalTerminalOverlapComparison
  HironakaG3RGluedUniqueness NormalCrossings
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ}

/-- Taking images commutes with keeping the nonempty members of a list of sets. -/
theorem filter_nonempty_map_image {α β : Type*} (g : α → β) (l : List (Set α)) :
    (l.map (g '' ·)).filter (fun H => decide H.Nonempty) =
      (l.filter (fun H => decide H.Nonempty)).map (g '' ·) := by
  induction l with
  | nil => rfl
  | cons H l ih => by_cases hne : H.Nonempty <;> simp [hne, ih, Set.image_nonempty]

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}

section Chart

variable (c : GluedChart M X' P)

/-- The last stage of the chart, mapped into the glued space. -/
def chartIncl (y : c.Y) : X' := ((c.φ y : c.V) : X')

theorem proj_chartIncl (y : c.Y) : P (chartIncl c y) = ((c.T.proj y : c.U) : X) := c.proj_φ y

theorem chartIncl_mem_V (y : c.Y) : chartIncl c y ∈ c.V := (c.φ y).2

/-- **The boundary of a chart**: the final boundary list of the local canonical resolution, carried into `X'`. -/
def chartBoundary : List (Set X') :=
  (geoTransformAlong (pullback (Subtype.val : c.U → X) M) c.T).E.map (chartIncl c '' ·)

theorem chartBoundary_subset_V {H : Set X'} (hH : H ∈ chartBoundary c) : H ⊆ c.V := by
  obtain ⟨K, -, rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y, -, rfl⟩
  exact chartIncl_mem_V c y

/-- The trace of a member on `P⁻¹W` is the image of its trace on the open preimage of `W`. -/
theorem chartIncl_image_inter_preimage (W : Opens X) (H : Set c.Y) :
    chartIncl c '' H ∩ P ⁻¹' (W : Set X) =
      (chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U W) → c.Y)) ''
        ((Subtype.val : openPreimage c.T (nestedOpens c.U W) → c.Y) ⁻¹' H) := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    have hy' : y ∈ openPreimage c.T (nestedOpens c.U W) := by
      show ((c.T.proj y : c.U) : X) ∈ (W : Set X)
      rw [← proj_chartIncl c y]
      exact hz
    exact ⟨⟨y, hy'⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y.1, hy, rfl⟩, ?_⟩
    show P (chartIncl c y.1) ∈ (W : Set X)
    rw [proj_chartIncl c y.1]
    exact y.2

end Chart

/-- **The two chart identifications agree on the overlap through the canonical comparison** (rigidity). -/
theorem incl_comparison (c₁ c₂ : GluedChart M X' P) {W : Opens X} (hW₂ : W ≤ c₂.U)
    (η : CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U W)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage c₂.T (nestedOpens c₂.U W)))
    (hη : ∀ z, ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₁.T.proj z.1 : c₁.U) : X))
    (z : openPreimage c₁.T (nestedOpens c₁.U W)) :
    chartIncl c₂ (η z).1 = chartIncl c₁ z.1 := by
  have hmem : ∀ z : openPreimage c₁.T (nestedOpens c₁.U W), chartIncl c₁ z.1 ∈ c₂.V := by
    intro z
    apply c₂.mem_V
    rw [proj_chartIncl c₁ z.1]
    exact hW₂ z.2
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : openPreimage c₁.T (nestedOpens c₁.U W) => (⟨chartIncl c₁ z.1, hmem z⟩ : c₂.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp (c₁.φ.contMDiff.comp contMDiff_subtype_val)) hmem
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val ∘ η : openPreimage c₁.T (nestedOpens c₁.U W) → c₂.Y) :=
    contMDiff_subtype_val.comp η.contMDiff
  have hexc : exceptionalLocus n (Subtype.val ∘ η : openPreimage c₁.T (nestedOpens c₁.U W) → c₂.Y) = ∅ := by
    rw [exceptionalLocus_val_comp η.contMDiff]
    exact eq_empty_of_forall_notMem fun a ha => MarkedIdealTowerTransport.notMem_exceptionalLocus η a ha
  have h := eq_of_proj_eq (Z := CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U W))) c₂.T
    (Subtype.val ∘ η) (c₂.φ.symm ∘ fun z => (⟨chartIncl c₁ z.1, hmem z⟩ : c₂.V)) hf
    (c₂.φ.symm.contMDiff.comp hk) (by rw [hexc, interior_empty]) (fun z => by
      apply Subtype.ext
      change ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₂.T.proj (c₂.φ.symm ⟨chartIncl c₁ z.1, hmem z⟩) : c₂.U) : X)
      rw [c₂.proj_symm, hη]
      exact (proj_chartIncl c₁ z.1).symm)
  have hz := congrArg (fun y => chartIncl c₂ y) (congrFun h z)
  simp only [Function.comp_apply] at hz
  rw [hz]
  simp [chartIncl]

/-- **The chart boundaries agree on overlaps** (A-miss-2, local form): for two charts `c₁, c₂` of `P : X' → X`, the ordered
lists of nonempty traces of their boundaries on `P⁻¹(U¹ ∩ U²)` are equal. -/
theorem chartBoundary_overlap (hM : IsInvDomain n M) (c₁ c₂ : GluedChart M X' P) :
    ((chartBoundary c₁).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter (fun H => decide H.Nonempty) =
      ((chartBoundary c₂).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) := by
  have hWU : c₁.U ⊓ c₂.U ≤ c₁.U := inf_le_left
  have hWV : c₁.U ⊓ c₂.U ≤ c₂.U := inf_le_right
  have hU₁ := InvDomainTowerAlong.isInvDomain_pullback_val c₁.U hM
  have hU₂ := InvDomainTowerAlong.isInvDomain_pullback_val c₂.U hM
  have hS := HironakaOriginalTerminalOpenComparison.original_terminal_open_history_data _ hU₁ c₁.T c₁.canonical
    c₁.resolution (nestedOpens c₁.U (c₁.U ⊓ c₂.U))
  have hT := HironakaOriginalTerminalOpenComparison.original_terminal_open_history_data _ hU₂ c₂.T c₂.canonical
    c₂.resolution (nestedOpens c₂.U (c₁.U ⊓ c₂.U))
  have he := original_overlap_whole_marked_dictionary M hM hWU hWV
  obtain ⟨η, ⟨hη, hE⟩, -⟩ :=
    HironakaOriginalBoundaryEmptyBaseComparison.terminal_choice_over_base_across_empty_boundaries
      (pullback (Subtype.val : nestedOpens c₂.U (c₁.U ⊓ c₂.U) → c₂.U) (pullback (Subtype.val : c₂.U → X) M))
      (pullback (Subtype.val : nestedOpens c₁.U (c₁.U ⊓ c₂.U) → c₁.U) (pullback (Subtype.val : c₁.U → X) M)) hT.1
      (overlapBaseEquiv hWU hWV) (by rw [← he]; rfl) (by rw [← he]; rfl) (by rw [← he]; rfl) (by rw [← he]; rfl)
      (restrict (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) c₁.T) (restrict (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) c₂.T)
      hS.2.1 hT.2.1 hS.2.2 hT.2.2
  rw [HironakaOriginalTerminalOpenComparison.original_terminal_open_whole_record _ hU₁ c₁.T c₁.resolution,
    HironakaOriginalTerminalOpenComparison.original_terminal_open_whole_record _ hU₂ c₂.T c₂.resolution] at hE
  have hη' : ∀ z, ((c₂.T.proj (η z).1 : c₂.U) : X) = ((c₁.T.proj z.1 : c₁.U) : X) := by
    intro y
    have hz := congrArg (fun q : nestedOpens c₂.U (c₁.U ⊓ c₂.U) => q.val.val) (hη y)
    rw [overlapBaseEquiv_point] at hz
    have htproj := congrArg (fun q : c₂.U => q.val)
      (proj_restrict (nestedOpens c₂.U (c₁.U ⊓ c₂.U)) c₂.T (η y))
    have hsproj := congrArg (fun q : c₁.U => q.val)
      (proj_restrict (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) c₁.T y)
    exact htproj.symm.trans (hz.trans hsproj)
  have hincl := incl_comparison c₁ c₂ hWV η hη'
  have hL : ∀ c : GluedChart M X' P,
      (chartBoundary c).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X)) =
        ((geoTransformAlong (pullback (Subtype.val : c.U → X) M) c.T).E.map
          ((Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y) ⁻¹' ·)).map
          ((chartIncl c ∘ (Subtype.val : openPreimage c.T (nestedOpens c.U (c₁.U ⊓ c₂.U)) → c.Y)) '' ·) := by
    intro c
    unfold chartBoundary
    rw [List.map_map, List.map_map]
    congr 1
    funext H
    exact chartIncl_image_inter_preimage c _ H
  rw [hL c₁, hL c₂, filter_nonempty_map_image, filter_nonempty_map_image]
  erw [hE]
  rw [List.map_map]
  congr 1
  funext B
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨η a, ha, hincl a⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨η.symm b, show η (η.symm b) ∈ B by rw [η.apply_symm_apply]; exact hb, ?_⟩
    have h := hincl (η.symm b)
    rw [η.apply_symm_apply] at h
    exact h.symm

/-- **The boundary of the glued resolution**: the union of the members of all chart boundaries (no chart is chosen). -/
def gluedBoundary (M : MarkedIdeal n X) (X' : CMfd.{u} n) (P : X' → X) : Set X' :=
  {z | ∃ c : GluedChart M X' P, ∃ H ∈ chartBoundary c, z ∈ H}

/-- **On every chart, the glued boundary is the union of the chart boundary.** -/
theorem gluedBoundary_inter_V (hM : IsInvDomain n M) (c : GluedChart M X' P) :
    gluedBoundary M X' P ∩ c.V = ⋃ H ∈ chartBoundary c, H := by
  ext z
  constructor
  · rintro ⟨⟨c', H', hH', hz⟩, hzV⟩
    have hz' : z ∈ (c'.V : Set X') := chartBoundary_subset_V c' hH' hz
    have hzV' : z ∈ (c.V : Set X') := hzV
    rw [c'.V_eq] at hz'
    rw [c.V_eq] at hzV'
    have hPz : P z ∈ ((c'.U ⊓ c.U : Opens X) : Set X) := ⟨hz', hzV'⟩
    have hmem : H' ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X) ∈
        ((chartBoundary c').map (· ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X))).filter
          (fun H => decide H.Nonempty) :=
      List.mem_filter.mpr ⟨List.mem_map_of_mem hH', decide_eq_true ⟨z, hz, hPz⟩⟩
    rw [chartBoundary_overlap hM c' c] at hmem
    obtain ⟨hmem1, -⟩ := List.mem_filter.mp hmem
    obtain ⟨H, hH, heq⟩ := List.mem_map.mp hmem1
    have hzH : z ∈ H ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X) := by
      rw [heq]
      exact ⟨hz, hPz⟩
    exact mem_iUnion₂.mpr ⟨H, hH, hzH.1⟩
  · intro hz
    obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hz
    exact ⟨⟨c, H, hH, hzH⟩, chartBoundary_subset_V c hH hzH⟩

/-- **On every chart, the boundary members form a simple normal crossings divisor** (of the open `P⁻¹U`). -/
theorem isSNCDivisor_chartBoundary (hM : IsInvDomain n M) (c : GluedChart M X' P) :
    IsSNCDivisor n ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) := by
  have hdom := InvDomainTowerAlong.isInvDomain_pullback_val c.U hM
  have hs := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom c.T c.resolution.1).isWellFormed.isSNCDivisor
  have hmap : (chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·) =
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
      exact ⟨c.φ.symm v, hv, by simp [chartIncl]⟩
  rw [hmap]
  exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hs

/-- **The glued boundary is closed.** -/
theorem isClosed_gluedBoundary (hM : IsInvDomain n M) (hch : ∀ x, ∃ c : GluedChart M X' P, x ∈ c.U) :
    IsClosed (gluedBoundary M X' P) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨c, hc⟩ := hch (P z)
  have hzV : z ∈ c.V := c.mem_V hc
  have hsnc := isSNCDivisor_chartBoundary hM c
  let K : Set c.V := (Subtype.val : c.V → X') ⁻¹' (⋃ H ∈ chartBoundary c, H)
  have hK : IsClosed K := by
    have hK' : K = ⋃ H ∈ {H : Set X' | H ∈ chartBoundary c}, (Subtype.val : c.V → X') ⁻¹' H := by
      simp only [K, preimage_iUnion₂]
      rfl
    rw [hK']
    exact Set.Finite.isClosed_biUnion (List.finite_toSet _)
      fun H hH => hsnc.1 _ (List.mem_map_of_mem hH)
  refine ⟨Subtype.val '' Kᶜ, ?_, (c.V.isOpen.isOpenMap_subtype_val _ hK.isOpen_compl), ⟨⟨z, hzV⟩, ?_, rfl⟩⟩
  · rintro _ ⟨v, hv, rfl⟩ hvD
    apply hv
    have h := (gluedBoundary_inter_V hM c).subset ⟨hvD, v.2⟩
    exact h
  · intro hzK
    obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hzK
    exact hz ⟨c, H, hH, hzH⟩

/-- **A-miss-2 (normal-crossings form): the boundary of a glued canonical resolution.**  The glued boundary is closed, on
every chart it is the union of the chart boundary, whose members form a simple normal crossings divisor of `P⁻¹U`, and the
chart boundaries have the same ordered nonempty traces on every overlap. -/
theorem gluedBoundary_normalCrossings (hM : IsInvDomain n M) (h : IsGluedCanonicalResolution M X' P) :
    IsClosed (gluedBoundary M X' P) ∧
      ∀ c : GluedChart M X' P,
        gluedBoundary M X' P ∩ c.V = ⋃ H ∈ chartBoundary c, H ∧
        IsSNCDivisor n ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
        ∀ c' : GluedChart M X' P,
          ((chartBoundary c).map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
              (fun H => decide H.Nonempty) =
            ((chartBoundary c').map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
              (fun H => decide H.Nonempty) :=
  ⟨isClosed_gluedBoundary hM h.exists_chart, fun c =>
    ⟨gluedBoundary_inter_V hM c, isSNCDivisor_chartBoundary hM c, fun c' => chartBoundary_overlap hM c c'⟩⟩

/-! ### The boundary is preserved by isomorphisms over `X` -/

section Transport

variable {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X} {P₂ : X₂ → X}

/-- The open `Ψ⁻¹V`. -/
def preimageOpens (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) (V : Opens X₂) : Opens X₁ :=
  G3UniverseOpenDiffeo.preimageOpens Ψ V

/-- `Ψ⁻¹` restricted to the open `V`, onto `Ψ⁻¹V`. -/
def preimageDiffeo (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) (V : Opens X₂) :
    CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (preimageOpens Ψ V) :=
  G3UniverseOpenDiffeo.preimageDiffeo Ψ V

/-- **Transport of a chart** of `P₂ : X₂ → X` along a biholomorphism `Ψ : X₁ ≃ X₂` over `X`. -/
def chartTransport (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) (hΨ : ∀ z, P₂ (Ψ z) = P₁ z)
    (c : GluedChart M X₂ P₂) : GluedChart M X₁ P₁ where
  U := c.U
  Y := c.Y
  T := c.T
  canonical := c.canonical
  resolution := c.resolution
  V := preimageOpens Ψ c.V
  V_eq := by
    ext z
    show Ψ z ∈ (c.V : Set X₂) ↔ P₁ z ∈ (c.U : Set X)
    rw [c.V_eq, mem_preimage, hΨ]
  φ := c.φ.trans (preimageDiffeo Ψ c.V)
  proj_φ := fun y => by
    change P₁ (Ψ.symm (c.φ y : X₂)) = _
    rw [← hΨ, Ψ.apply_symm_apply]
    exact c.proj_φ y

theorem chartBoundary_chartTransport (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (hΨ : ∀ z, P₂ (Ψ z) = P₁ z) (c : GluedChart M X₂ P₂) :
    chartBoundary (chartTransport Ψ hΨ c) = (chartBoundary c).map (Ψ ⁻¹' ·) := by
  unfold chartBoundary
  rw [List.map_map]
  refine List.map_congr_left fun H _ => ?_
  ext z
  change z ∈ (fun y => Ψ.symm (chartIncl c y)) '' H ↔ Ψ z ∈ chartIncl c '' H
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (Ψ.apply_symm_apply _).symm⟩
  · rintro ⟨y, hy, hyz⟩
    exact ⟨y, hy, show Ψ.symm (chartIncl c y) = z by rw [hyz, Ψ.symm_apply_apply]⟩

theorem preimage_gluedBoundary_subset (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (hΨ : ∀ z, P₂ (Ψ z) = P₁ z) : Ψ ⁻¹' gluedBoundary M X₂ P₂ ⊆ gluedBoundary M X₁ P₁ := by
  rintro z ⟨c, H, hH, hz⟩
  refine ⟨chartTransport Ψ hΨ c, Ψ ⁻¹' H, ?_, hz⟩
  rw [chartBoundary_chartTransport]
  exact List.mem_map_of_mem hH

/-- **The glued boundary is intrinsic**: a biholomorphism over `X` between two glued canonical resolutions (for instance the
unique one, `HironakaG3RGluedUniqueness.existsUnique_biholomorphism`) maps one glued boundary onto the other. -/
theorem gluedBoundary_eq_preimage (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (hΨ : ∀ z, P₂ (Ψ z) = P₁ z) : gluedBoundary M X₁ P₁ = Ψ ⁻¹' gluedBoundary M X₂ P₂ := by
  refine Subset.antisymm (fun z hz => ?_) (preimage_gluedBoundary_subset Ψ hΨ)
  have hΨ' : ∀ w, P₁ (Ψ.symm w) = P₂ w := fun w => by rw [← hΨ, Ψ.apply_symm_apply]
  have h := preimage_gluedBoundary_subset (M := M) Ψ.symm hΨ'
  exact h (show Ψ.symm (Ψ z) ∈ gluedBoundary M X₁ P₁ by rw [Ψ.symm_apply_apply]; exact hz)

end Transport

end

end Hironaka.HironakaG3RGluedBoundary
