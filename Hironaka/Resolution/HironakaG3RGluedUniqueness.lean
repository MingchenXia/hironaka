import Hironaka.Resolution.HironakaG3RGluedCanonicalResolution
import Hironaka.Resolution.HironakaOriginalTerminalOverlapComparison
import Hironaka.Resolution.HironakaOriginalTerminalProjectionUniqueness
import Hironaka.Resolution.HironakaBaseChange

/-! # G3, target (A): uniqueness of the glued canonical resolution (A-miss-1)

Lane G3 (run 0080, round 3).  Blueprint: `hironaka-g3-r-glued-uniqueness.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-1).

* **`eq_of_proj_eq`** (rigidity of a tower): two holomorphic maps `f g : Z → Y` into the last stage of a tower of blowups
  with `T.proj ∘ f = T.proj ∘ g` are equal as soon as the exceptional locus of `f` has empty interior.  Same proof as the held
  `HironakaOriginalTerminalProjectionUniqueness.biholomorphisms_eq_of_actual_proj_eq` (universal property of each blowup),
  for maps that are not biholomorphisms.
* **`IsGluedCanonicalResolution M X' P`**: the conclusion of
  `HironakaG3RGluedCanonicalResolution.exists_glued_canonical_resolution` as a predicate (target (A)), and **`GluedChart`**:
  one of its local identifications (an open `U` of the base, a canonical segment `T` of `M|_U` with empty final cosupport
  and a biholomorphism of its last stage onto `P⁻¹U` over `U`).
* **`eq_of_proj_eq_of_charts`** (rigidity of glued data): if `P : X' → X` is covered by charts, two holomorphic maps
  `f g : Z → X'` with `P ∘ f = P ∘ g` agree as soon as `f` has no exceptional points.
* **`existsUnique_biholomorphism`** (A-miss-1): two glued canonical resolutions of the same marked ideal are biholomorphic
  over `X` by a UNIQUE biholomorphism.  On `P₁⁻¹(U¹ ∩ U²)` the map is `φ² ∘ η ∘ (φ¹)⁻¹` with `η` the canonical comparison
  `HironakaOriginalTerminalOverlapComparison.commonOpenTerminalComparison` of the two local canonical resolutions on the
  common open; the local formulas agree (rigidity), the inverse is the symmetric construction (rigidity again), and any
  biholomorphism over `X` equals it (rigidity).
* **`existsUnique_gluedCanonicalResolution`**: there is a glued canonical resolution, and every other one is identified
  with it by a unique biholomorphism over `X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RGluedUniqueness

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres MaxLocusLocal HironakaOriginalTerminalOverlapComparison
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ}

/-! ### Exceptional loci of the elementary maps -/

section Exceptional

variable {A B C : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
  [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]
  [TopologicalSpace C] [ChartedSpace (ComplexModel n) C] [IsComplexManifold n C]

/-- Composing with the inclusion of an open subset does not change the exceptional locus. -/
theorem exceptionalLocus_val_comp {V : Opens B} {g : A → V}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    exceptionalLocus n (Subtype.val ∘ g) = exceptionalLocus n g := by
  rw [exceptionalLocus_comp ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)), HironakaBaseChange.exceptionalLocus_val, preimage_empty, union_empty]

/-- Co-restricting to an open subset does not change the exceptional locus. -/
theorem exceptionalLocus_opens_mk {V : Opens B} {f : A → B}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (hfV : ∀ a, f a ∈ V) :
    exceptionalLocus n (fun a => (⟨f a, hfV a⟩ : V)) = exceptionalLocus n f :=
  (exceptionalLocus_val_comp (BlowupRestrictOpen.contMDiff_opens_mk hf hfV)).symm

/-- Composing with a biholomorphism does not change the exceptional locus. -/
theorem exceptionalLocus_diffeo_comp (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ C) {g : A → B}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    exceptionalLocus n (Φ ∘ g) = exceptionalLocus n g := by
  rw [exceptionalLocus_comp (Φ.contMDiff.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
  have h : g ⁻¹' exceptionalLocus n Φ = ∅ :=
    eq_empty_of_forall_notMem fun a ha => MarkedIdealTowerTransport.notMem_exceptionalLocus Φ (g a) ha
  rw [h, union_empty]

/-- Restricting to an open subset restricts the exceptional locus. -/
theorem exceptionalLocus_comp_val {V : Opens A} {f : A → B}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    exceptionalLocus n (f ∘ (Subtype.val : V → A)) = Subtype.val ⁻¹' exceptionalLocus n f := by
  rw [exceptionalLocus_comp (hf.mdifferentiable (by simp))
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)), HironakaBaseChange.exceptionalLocus_val,
    empty_union]

end Exceptional

/-! ### Rigidity of a tower -/

section Rigidity

variable {X Y : CMfd.{u} n}

/-- **Rigidity of a tower of blowups.**  Two holomorphic maps `f g : Z → Y` into the last stage of a tower with the same
composite to the base are equal, provided the exceptional locus of `f` has empty interior (then `f` pulls back every
invertible ideal to an invertible ideal, and the universal property of each blowup applies).  The held
`biholomorphisms_eq_of_actual_proj_eq` is the case of two biholomorphisms. -/
theorem eq_of_proj_eq (T : BlowupTower X Y) {Z : CMfd.{u} n} (f g : Z → Y)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n f) = ∅)
    (hproj : ∀ z, T.proj (f z) = T.proj (g z)) : f = g := by
  generalize hlen : T.length = ℓ
  induction ℓ using Nat.strong_induction_on generalizing X with
  | h ℓ ih =>
    by_cases hpos : 0 < T.length
    · obtain ⟨A, C, π, hπ, S, heq⟩ :=
        HironakaOriginalTerminalProjectionUniqueness.exists_actual_first_step_split T hpos
      have hlt : S.length < ℓ := by
        rw [heq, BlowupTower.length_append] at hlen
        change 1 + S.length = ℓ at hlen
        omega
      have hproj' : ∀ z, π (S.proj (f z)) = π (S.proj (g z)) := by
        intro z
        have hz := hproj z
        rw [heq, BlowupTower.proj_append] at hz
        exact hz
      have hJ : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsInvertible := hπ.2.2.2.1
      have hJcoh := DivisorMetric.isCoherent_of_isInvertible hJ
      have hSI := HironakaNormalCrossingsTotalIdeal.isInvertible_original_pullback_tower S hJ
      have hFI := GermIdealTotalTransform.isInvertible_pullback hf hint hSI
      rw [← GermIdealTotalTransform.pullback_comp S.contMDiff_proj hf hJcoh] at hFI
      have hCcoh := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
      rw [← GermIdealTotalTransform.pullback_comp hπ.contMDiff (S.contMDiff_proj.comp hf) hCcoh] at hFI
      obtain ⟨w, hw, huniq⟩ := hπ.2.2.2.2 n Z (π ∘ (S.proj ∘ f))
        (hπ.contMDiff.comp (S.contMDiff_proj.comp hf)) hFI
      have hfg : S.proj ∘ f = S.proj ∘ g :=
        (huniq (S.proj ∘ f) ⟨S.contMDiff_proj.comp hf, rfl⟩).trans
          (huniq (S.proj ∘ g) ⟨S.contMDiff_proj.comp hg, funext fun z => (hproj' z).symm⟩).symm
      exact ih _ hlt S (fun z => congrFun hfg z) rfl
    · cases T with
      | refl => exact funext hproj
      | step T C π hπ => exact False.elim (hpos (Nat.succ_pos _))

end Rigidity

/-! ### Glued canonical resolutions and their charts -/

section Glued

variable {X : CMfd.{u} n}

/-- **Target (A): a glued canonical resolution of `M`** — the conclusion of
`HironakaG3RGluedCanonicalResolution.exists_glued_canonical_resolution` as a predicate on `(X', P)`: `P : X' → X` is
holomorphic, proper and surjective, and every point of `X` has an open neighbourhood `U` with a canonical segment `T` of
`M|_U` with empty final cosupport whose last stage is biholomorphic to `P⁻¹U` over `U`. -/
def IsGluedCanonicalResolution (M : MarkedIdeal n X) (X' : CMfd.{u} n) (P : X' → X) : Prop :=
  ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsCanonical (pullback (Subtype.val : U → X) M) ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) T ∧
      IsGeoResolution (pullback (Subtype.val : U → X) M) T ∧
      ∃ V : Opens X', (V : Set X') = P ⁻¹' (U : Set X) ∧
        ∃ φ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V,
          ∀ y : Y, P (φ y : X') = ((T.proj y : U) : X)

/-- Target (A) holds: every marked ideal of the domain has a glued canonical resolution. -/
theorem exists_isGluedCanonicalResolution (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P :=
  HironakaG3RGluedCanonicalResolution.exists_glued_canonical_resolution M hM

/-- **A chart of a glued canonical resolution**: an open `U` of the base, a canonical segment `T` of `M|_U` with empty
final cosupport, and a biholomorphism `φ` of its last stage onto the open `V = P⁻¹U` commuting with the projections. -/
structure GluedChart (M : MarkedIdeal n X) (X' : CMfd.{u} n) (P : X' → X) where
  /-- The open of the base. -/
  U : Opens X
  /-- The last stage of the local canonical resolution. -/
  Y : CMfd.{u} n
  /-- The local canonical resolution. -/
  T : BlowupTower (CMfd.of (n := n) U) Y
  canonical : IsCanonical (pullback (Subtype.val : U → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) T
  resolution : IsGeoResolution (pullback (Subtype.val : U → X) M) T
  /-- The saturated open of the glued space. -/
  V : Opens X'
  V_eq : (V : Set X') = P ⁻¹' (U : Set X)
  /-- The identification of the last stage with `P⁻¹U`. -/
  φ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V
  proj_φ : ∀ y : Y, P (φ y : X') = ((T.proj y : U) : X)

namespace GluedChart

variable {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X} (c : GluedChart M X' P)

theorem mem_V {z : X'} (hz : P z ∈ c.U) : z ∈ c.V := by
  have h : z ∈ (c.V : Set X') := by rw [c.V_eq]; exact hz
  exact h

theorem proj_symm (z : c.V) : ((c.T.proj (c.φ.symm z) : c.U) : X) = P z := by
  rw [← c.proj_φ, Diffeomorph.apply_symm_apply]

end GluedChart

/-- The charts of a glued canonical resolution cover the base. -/
theorem IsGluedCanonicalResolution.exists_chart {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}
    (h : IsGluedCanonicalResolution M X' P) (x : X) : ∃ c : GluedChart M X' P, x ∈ c.U := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨U, hx, Y, T, hc, hr, V, hV, φ, hφ⟩ := h x
  exact ⟨⟨U, Y, T, hc, hr, V, hV, φ, hφ⟩, hx⟩

/-- **Rigidity of glued data.**  If the base is covered by charts of `P : X' → X`, two holomorphic maps `f g : Z → X'` with
`P ∘ f = P ∘ g` are equal, provided `f` has no exceptional points. -/
theorem eq_of_proj_eq_of_charts {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}
    (hch : ∀ x, ∃ c : GluedChart M X' P, x ∈ c.U) {Z : CMfd.{u} n} (f g : Z → X')
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hexc : exceptionalLocus n f = ∅) (h : ∀ z, P (f z) = P (g z)) : f = g := by
  funext z
  obtain ⟨c, hc⟩ := hch (P (f z))
  let O : Opens Z := ⟨f ⁻¹' (c.V : Set X') ∩ g ⁻¹' (c.V : Set X'),
    (c.V.isOpen.preimage hf.continuous).inter (c.V.isOpen.preimage hg.continuous)⟩
  have hfO : ∀ o : O, f o ∈ c.V := fun o => o.2.1
  have hgO : ∀ o : O, g o ∈ c.V := fun o => o.2.2
  have hzO : z ∈ O := ⟨c.mem_V hc, c.mem_V ((h z) ▸ hc)⟩
  have hkf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨f o, hfO o⟩ : c.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (hf.comp (contMDiff_subtype_val (U := O))) hfO
  have hkg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨g o, hgO o⟩ : c.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (hg.comp (contMDiff_subtype_val (U := O))) hgO
  let f' : CMfd.of (n := n) O → c.Y := c.φ.symm ∘ fun o => ⟨f o, hfO o⟩
  let g' : CMfd.of (n := n) O → c.Y := c.φ.symm ∘ fun o => ⟨g o, hgO o⟩
  have hexc' : exceptionalLocus n f' = ∅ := by
    change exceptionalLocus n (c.φ.symm ∘ fun o : O => (⟨f o, hfO o⟩ : c.V)) = ∅
    rw [exceptionalLocus_diffeo_comp _ hkf]
    refine (exceptionalLocus_opens_mk (f := f ∘ (Subtype.val : O → Z)) (hf.comp contMDiff_subtype_val) hfO).trans ?_
    rw [exceptionalLocus_comp_val hf, hexc, preimage_empty]
  have hproj : ∀ o, c.T.proj (f' o) = c.T.proj (g' o) := by
    intro o
    apply Subtype.ext
    change ((c.T.proj (c.φ.symm ⟨f o, hfO o⟩) : c.U) : X) = ((c.T.proj (c.φ.symm ⟨g o, hgO o⟩) : c.U) : X)
    rw [c.proj_symm, c.proj_symm]
    exact h o
  have hfg := congrFun (eq_of_proj_eq c.T f' g' (c.φ.symm.contMDiff.comp hkf) (c.φ.symm.contMDiff.comp hkg)
    (by rw [hexc', interior_empty]) hproj) ⟨z, hzO⟩
  have := congrArg (fun y => ((c.φ y : c.V) : X')) hfg
  simpa [f', g'] using this

end Glued

/-! ### The local comparison maps and their gluing -/

section Comparison

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} (hM : IsInvDomain n M) {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X}
  {P₂ : X₂ → X} (hP₁ : Continuous P₁)

/-- The open of `X₁` over the common open `U¹ ∩ U²` of two charts. -/
def overlapDom (c₁ : GluedChart M X₁ P₁) (c₂ : GluedChart M X₂ P₂) : Opens X₁ :=
  ⟨P₁ ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X), (c₁.U ⊓ c₂.U).isOpen.preimage hP₁⟩

variable {hP₁} {c₁ : GluedChart M X₁ P₁} {c₂ : GluedChart M X₂ P₂}

theorem overlapDom_mem_V (z : overlapDom hP₁ c₁ c₂) : (z : X₁) ∈ c₁.V := c₁.mem_V z.2.1

/-- The point of the first local resolution over a point of the overlap. -/
def overlapPoint (z : overlapDom hP₁ c₁ c₂) : c₁.Y := c₁.φ.symm ⟨z, overlapDom_mem_V z⟩

theorem overlapPoint_mem (z : overlapDom hP₁ c₁ c₂) :
    overlapPoint z ∈ openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) := by
  show ((c₁.T.proj (overlapPoint z) : c₁.U) : X) ∈ (c₁.U ⊓ c₂.U : Opens X)
  rw [overlapPoint, c₁.proj_symm]
  exact z.2

variable (c₁ c₂ hP₁)

/-- **The local comparison map** `φ² ∘ η ∘ (φ¹)⁻¹` on `P₁⁻¹(U¹ ∩ U²)`, with `η` the canonical comparison of the two local
canonical resolutions over the common open. -/
def overlapMap (z : overlapDom hP₁ c₁ c₂) : X₂ :=
  ((c₂.φ (commonOpenTerminalComparison M hM (inf_le_left : c₁.U ⊓ c₂.U ≤ c₁.U) inf_le_right c₁.T c₂.T
    c₁.canonical c₂.canonical c₁.resolution c₂.resolution ⟨overlapPoint z, overlapPoint_mem z⟩).1 : c₂.V) : X₂)

theorem proj_overlapMap (z : overlapDom hP₁ c₁ c₂) : P₂ (overlapMap hM hP₁ c₁ c₂ z) = P₁ z := by
  rw [overlapMap, c₂.proj_φ, commonOpenTerminalComparison_proj]
  exact c₁.proj_symm _

theorem contMDiff_overlapMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (overlapMap hM hP₁ c₁ c₂) ∧
      exceptionalLocus n (overlapMap hM hP₁ c₁ c₂) = ∅ := by
  have hk₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : overlapDom hP₁ c₁ c₂ => (⟨z, overlapDom_mem_V z⟩ : c₁.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (overlapPoint : overlapDom hP₁ c₁ c₂ → c₁.Y) := c₁.φ.symm.contMDiff.comp hk₁
  have hk₂ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : overlapDom hP₁ c₁ c₂ => (⟨overlapPoint z, overlapPoint_mem z⟩ :
        openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)))) :=
    BlowupRestrictOpen.contMDiff_opens_mk hp _
  set η := commonOpenTerminalComparison M hM (inf_le_left : c₁.U ⊓ c₂.U ≤ c₁.U) inf_le_right c₁.T c₂.T
    c₁.canonical c₂.canonical c₁.resolution c₂.resolution
  have hη := η.contMDiff.comp hk₂
  have h3 := (contMDiff_subtype_val (n := ∞)).comp hη
  have h4 := c₂.φ.contMDiff.comp h3
  have h5 := (contMDiff_subtype_val (n := ∞)).comp h4
  refine ⟨h5, ?_⟩
  change exceptionalLocus n (Subtype.val ∘ (c₂.φ ∘ (Subtype.val ∘ (η ∘
    (fun z : overlapDom hP₁ c₁ c₂ => (⟨overlapPoint z, overlapPoint_mem z⟩ :
        openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)))))))) = ∅
  rw [exceptionalLocus_val_comp h4, exceptionalLocus_diffeo_comp _ h3, exceptionalLocus_val_comp hη,
    exceptionalLocus_diffeo_comp _ hk₂]
  refine (exceptionalLocus_opens_mk hp _).trans ?_
  change exceptionalLocus n (c₁.φ.symm ∘ fun z : overlapDom hP₁ c₁ c₂ => (⟨z, overlapDom_mem_V z⟩ : c₁.V)) = ∅
  rw [exceptionalLocus_diffeo_comp _ hk₁]
  refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
  exact HironakaBaseChange.exceptionalLocus_val

variable {hM hP₁ c₁ c₂}

/-- **The local comparison maps agree on overlaps** (rigidity of the glued data of `X₂`). -/
theorem overlapMap_eq_overlapMap (hch₂ : ∀ x, ∃ c : GluedChart M X₂ P₂, x ∈ c.U)
    {c₁' : GluedChart M X₁ P₁} {c₂' : GluedChart M X₂ P₂} (z : X₁) (hz : z ∈ overlapDom hP₁ c₁ c₂)
    (hz' : z ∈ overlapDom hP₁ c₁' c₂') :
    overlapMap hM hP₁ c₁ c₂ ⟨z, hz⟩ = overlapMap hM hP₁ c₁' c₂' ⟨z, hz'⟩ := by
  let O : Opens X₁ := overlapDom hP₁ c₁ c₂ ⊓ overlapDom hP₁ c₁' c₂'
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun o : O => (⟨o, o.2.1⟩ : overlapDom hP₁ c₁ c₂)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hi' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun o : O => (⟨o, o.2.2⟩ : overlapDom hP₁ c₁' c₂')) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  obtain ⟨hl, hle⟩ := contMDiff_overlapMap hM hP₁ c₁ c₂
  obtain ⟨hl', -⟩ := contMDiff_overlapMap hM hP₁ c₁' c₂'
  have hexc : exceptionalLocus n (overlapMap hM hP₁ c₁ c₂ ∘ fun o : O => (⟨o, o.2.1⟩ : overlapDom hP₁ c₁ c₂)) = ∅ := by
    rw [exceptionalLocus_comp (hl.mdifferentiable (by simp)) (hi.mdifferentiable (by simp)), hle, preimage_empty,
      union_empty]
    refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
    exact HironakaBaseChange.exceptionalLocus_val
  have h := eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) O) hch₂ _ _ (hl.comp hi) (hl'.comp hi') hexc
    (fun o => (proj_overlapMap hM hP₁ c₁ c₂ ⟨o, o.2.1⟩).trans (proj_overlapMap hM hP₁ c₁' c₂' ⟨o, o.2.2⟩).symm)
  exact congrFun h ⟨z, hz, hz'⟩

end Comparison

section Glue

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} (hM : IsInvDomain n M) {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X}
  {P₂ : X₂ → X} (hP₁ : Continuous P₁) (hch₁ : ∀ x, ∃ c : GluedChart M X₁ P₁, x ∈ c.U)
  (hch₂ : ∀ x, ∃ c : GluedChart M X₂ P₂, x ∈ c.U)

/-- **The glued comparison map** `X₁ → X₂`: at `z`, the local comparison map of the chosen charts at `P₁ z`. -/
def gluedMap (z : X₁) : X₂ :=
  overlapMap hM hP₁ (hch₁ (P₁ z)).choose (hch₂ (P₁ z)).choose
    ⟨z, (⟨(hch₁ (P₁ z)).choose_spec, (hch₂ (P₁ z)).choose_spec⟩ :
      P₁ z ∈ (((hch₁ (P₁ z)).choose.U ⊓ (hch₂ (P₁ z)).choose.U : Opens X) : Set X))⟩

/-- The glued comparison map is the local comparison map of ANY two charts on their overlap. -/
theorem gluedMap_eq (c₁ : GluedChart M X₁ P₁) (c₂ : GluedChart M X₂ P₂) (z : X₁)
    (hz : z ∈ overlapDom hP₁ c₁ c₂) : gluedMap hM hP₁ hch₁ hch₂ z = overlapMap hM hP₁ c₁ c₂ ⟨z, hz⟩ :=
  overlapMap_eq_overlapMap hch₂ z _ hz

theorem proj_gluedMap (z : X₁) : P₂ (gluedMap hM hP₁ hch₁ hch₂ z) = P₁ z :=
  proj_overlapMap hM hP₁ _ _ _

theorem contMDiff_gluedMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (gluedMap hM hP₁ hch₁ hch₂) := by
  intro z
  obtain ⟨c₁, h₁⟩ := hch₁ (P₁ z)
  obtain ⟨c₂, h₂⟩ := hch₂ (P₁ z)
  have hz : z ∈ overlapDom hP₁ c₁ c₂ :=
    (⟨h₁, h₂⟩ : P₁ z ∈ ((c₁.U ⊓ c₂.U : Opens X) : Set X))
  have hO : (fun o : overlapDom hP₁ c₁ c₂ => gluedMap hM hP₁ hch₁ hch₂ o) = overlapMap hM hP₁ c₁ c₂ :=
    funext fun o => gluedMap_eq hM hP₁ hch₁ hch₂ c₁ c₂ o o.2
  have h := (contMDiff_overlapMap hM hP₁ c₁ c₂).1 ⟨z, hz⟩
  rw [← hO] at h
  exact contMDiffAt_subtype_iff.mp h

end Glue

/-! ### Uniqueness of the glued canonical resolution -/

section Uniqueness

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X} {P₂ : X₂ → X}

/-- **Uniqueness from charts.**  If `P₁ : X₁ → X` and `P₂ : X₂ → X` are continuous and the base is covered by charts of
both (local canonical resolutions of `M` identified with the saturated opens), there is a unique biholomorphism
`Ψ : X₁ ≃ X₂` with `P₂ ∘ Ψ = P₁`. -/
theorem existsUnique_biholomorphism_of_charts (hM : IsInvDomain n M) (hP₁ : Continuous P₁) (hP₂ : Continuous P₂)
    (hch₁ : ∀ x, ∃ c : GluedChart M X₁ P₁, x ∈ c.U) (hch₂ : ∀ x, ∃ c : GluedChart M X₂ P₂, x ∈ c.U) :
    ∃! Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂, ∀ z, P₂ (Ψ z) = P₁ z := by
  have hF := contMDiff_gluedMap hM hP₁ hch₁ hch₂
  have hG := contMDiff_gluedMap hM hP₂ hch₂ hch₁
  have hpF := proj_gluedMap hM hP₁ hch₁ hch₂
  have hpG := proj_gluedMap hM hP₂ hch₂ hch₁
  have hGF : (gluedMap hM hP₂ hch₂ hch₁ ∘ gluedMap hM hP₁ hch₁ hch₂) = id :=
    (eq_of_proj_eq_of_charts hch₁ id _ contMDiff_id (hG.comp hF) exceptionalLocus_id
      fun z => ((hpG _).trans (hpF z)).symm).symm
  have hFG : (gluedMap hM hP₁ hch₁ hch₂ ∘ gluedMap hM hP₂ hch₂ hch₁) = id :=
    (eq_of_proj_eq_of_charts hch₂ id _ contMDiff_id (hF.comp hG) exceptionalLocus_id
      fun z => ((hpF _).trans (hpG z)).symm).symm
  let Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂ :=
    { toFun := gluedMap hM hP₁ hch₁ hch₂
      invFun := gluedMap hM hP₂ hch₂ hch₁
      left_inv := congrFun hGF
      right_inv := congrFun hFG
      contMDiff_toFun := hF
      contMDiff_invFun := hG }
  refine ⟨Ψ, hpF, fun Ψ' hΨ' => ?_⟩
  apply Diffeomorph.ext
  intro z
  exact congrFun (eq_of_proj_eq_of_charts hch₂ Ψ' (gluedMap hM hP₁ hch₁ hch₂) Ψ'.contMDiff hF
    (eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus Ψ'))
    fun z => (hΨ' z).trans (hpF z).symm) z

/-- **The comparison is the canonical one on each overlap**: a biholomorphism `Ψ` over `X` between two glued data is,
on `P₁⁻¹(U¹ ∩ U²)`, the local comparison map `φ² ∘ η ∘ (φ¹)⁻¹` of any two charts. -/
theorem biholomorphism_eq_overlapMap (hM : IsInvDomain n M) (hP₁ : Continuous P₁)
    (hch₂ : ∀ x, ∃ c : GluedChart M X₂ P₂, x ∈ c.U)
    (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) (hΨ : ∀ z, P₂ (Ψ z) = P₁ z)
    (c₁ : GluedChart M X₁ P₁) (c₂ : GluedChart M X₂ P₂) (z : X₁) (hz : z ∈ overlapDom hP₁ c₁ c₂) :
    Ψ z = overlapMap hM hP₁ c₁ c₂ ⟨z, hz⟩ := by
  let O := overlapDom hP₁ c₁ c₂
  obtain ⟨hl, -⟩ := contMDiff_overlapMap hM hP₁ c₁ c₂
  have hexc : exceptionalLocus n (Ψ ∘ (Subtype.val : O → X₁)) = ∅ := by
    rw [exceptionalLocus_diffeo_comp _ contMDiff_subtype_val, HironakaBaseChange.exceptionalLocus_val]
  have h := eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) O) hch₂ (Ψ ∘ Subtype.val) (overlapMap hM hP₁ c₁ c₂)
    (Ψ.contMDiff.comp contMDiff_subtype_val) hl hexc
    fun o => (hΨ o).trans (proj_overlapMap hM hP₁ c₁ c₂ o).symm
  exact congrFun h ⟨z, hz⟩

/-- **A-miss-1: uniqueness of the glued canonical resolution.**  Two glued canonical resolutions of the same marked ideal
of the domain are biholomorphic over `X` by a unique biholomorphism. -/
theorem existsUnique_biholomorphism (hM : IsInvDomain n M) (h₁ : IsGluedCanonicalResolution M X₁ P₁)
    (h₂ : IsGluedCanonicalResolution M X₂ P₂) :
    ∃! Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂, ∀ z, P₂ (Ψ z) = P₁ z :=
  existsUnique_biholomorphism_of_charts hM h₁.1.continuous h₂.1.continuous h₁.exists_chart h₂.exists_chart

/-- **Target (A) with uniqueness**: every marked ideal of the domain has a glued canonical resolution `(X', P)`, and every
glued canonical resolution `(X'', P')` of it is identified with `(X', P)` by a unique biholomorphism over `X`. -/
theorem existsUnique_gluedCanonicalResolution (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
      ∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z := by
  obtain ⟨X', P, h⟩ := exists_isGluedCanonicalResolution M hM
  exact ⟨X', P, h, fun X'' P' h' => existsUnique_biholomorphism hM h' h⟩

end Uniqueness

end

end Hironaka.HironakaG3RGluedUniqueness
