import Hironaka.Resolution.HironakaG3RTowerGluing

/-! # G3: spaces glued from a class of local towers, existence and uniqueness

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-tower-gluing.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-3, step (ii)).

A **class of local towers** on a complex manifold `X` is a predicate `𝒞 U Y T` on towers of blowups `T` over the open sets
`U` of `X`.  It **has comparisons** if any two members `T₁` over `U₁` and `T₂` over `U₂` are compared over `U₁ ∩ U₂` by
SOME biholomorphism of the parts of their last stages over `U₁ ∩ U₂` commuting with the projections, and it **covers**
`X` if every point has a neighbourhood carrying a member.

* **`IsGluedFrom 𝒞 X' P`**: `P : X' → X` is holomorphic, proper and surjective, and every point of `X` lies in the base
  `U` of a **`TowerChart`**: a member `T` of `𝒞` over `U` whose last stage is biholomorphic to `P⁻¹ U` over `U`.
* **`exists_isGluedFrom`**: a class with comparisons covering `X` glues (`HironakaG3RTowerGluing`).
* **`eq_of_proj_eq_of_charts`** (rigidity), **`existsUnique_biholomorphism`**: two spaces glued from the same class with
  comparisons are biholomorphic over `X` by a UNIQUE biholomorphism, which is on each overlap the comparison of the charts.
  The proof is the one of `HironakaG3RGluedUniqueness` with the canonical comparisons replaced by arbitrary ones (the
  rigidity of towers makes the choice irrelevant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RTowerClass

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3RGluedUniqueness HironakaG3RTowerGluing

variable {n : ℕ}

/-- **A class of local towers on `X`**: a predicate on towers of blowups over the open sets of `X`. -/
abbrev LocalTowerClass (X : CMfd.{u} n) : Type (u + 1) :=
  ∀ (U : Opens X) (Y : CMfd.{u} n), BlowupTower (CMfd.of (n := n) U) Y → Prop

variable {X : CMfd.{u} n}

/-- **The class has comparisons**: any two members are compared over the intersection of their bases by some
biholomorphism commuting with the projections. -/
def HasComparisons (𝒞 : LocalTowerClass X) : Prop :=
  ∀ (U₁ U₂ : Opens X) (Y₁ Y₂ : CMfd.{u} n) (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂), 𝒞 U₁ Y₁ T₁ → 𝒞 U₂ Y₂ T₂ →
    ∃ η : CMfd.of (n := n) (openPreimage T₁ (nestedOpens U₁ (U₁ ⊓ U₂)))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₂ (nestedOpens U₂ (U₁ ⊓ U₂))),
      ∀ y, ((T₂.proj (η y).val : U₂) : X) = ((T₁.proj y.val : U₁) : X)

/-- **The class covers `X`**: every point has an open neighbourhood carrying a member. -/
def Covers (𝒞 : LocalTowerClass X) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), 𝒞 U Y T

/-- **A chart of `P : X' → X` for the class `𝒞`**: an open `U` of the base, a member `T` of `𝒞` over `U`, and a
biholomorphism `φ` of its last stage onto the open `V = P⁻¹U` commuting with the projections. -/
structure TowerChart (𝒞 : LocalTowerClass X) (X' : CMfd.{u} n) (P : X' → X) where
  /-- The open of the base. -/
  U : Opens X
  /-- The last stage of the local tower. -/
  Y : CMfd.{u} n
  /-- The local tower. -/
  T : BlowupTower (CMfd.of (n := n) U) Y
  mem : 𝒞 U Y T
  /-- The saturated open of the glued space. -/
  V : Opens X'
  V_eq : (V : Set X') = P ⁻¹' (U : Set X)
  /-- The identification of the last stage with `P⁻¹U`. -/
  φ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V
  proj_φ : ∀ y : Y, P (φ y : X') = ((T.proj y : U) : X)

/-- **`P : X' → X` is glued from the class `𝒞`**: holomorphic, proper, surjective, and the bases of its charts cover `X`. -/
def IsGluedFrom (𝒞 : LocalTowerClass X) (X' : CMfd.{u} n) (P : X' → X) : Prop :=
  ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
    ∀ x : X, ∃ c : TowerChart 𝒞 X' P, x ∈ c.U

namespace TowerChart

variable {𝒞 : LocalTowerClass X} {X' : CMfd.{u} n} {P : X' → X} (c : TowerChart 𝒞 X' P)

theorem mem_V {z : X'} (hz : P z ∈ c.U) : z ∈ c.V := by
  have h : z ∈ (c.V : Set X') := by rw [c.V_eq]; exact hz
  exact h

theorem proj_symm (z : c.V) : ((c.T.proj (c.φ.symm z) : c.U) : X) = P z := by
  rw [← c.proj_φ, Diffeomorph.apply_symm_apply]

end TowerChart

/-! ### Existence -/

/-- **Gluing a class of local towers**: if the class has comparisons and covers `X`, some `P : X' → X` is glued from it. -/
theorem exists_isGluedFrom {𝒞 : LocalTowerClass X} (hcov : Covers 𝒞) (hcmp : HasComparisons 𝒞) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedFrom 𝒞 X' P := by
  choose U hU Y T hT using hcov
  let A : TowerAtlas X :=
    { J := X
      U := U
      cover := fun x => ⟨x, hU x⟩
      Y := Y
      T := T
      compare := fun i j => hcmp (U i) (U j) (Y i) (Y j) (T i) (T j) (hT i) (hT j) }
  refine ⟨A.manifold, A.proj, A.contMDiff_proj, A.isProperMap_proj, A.surjective_proj, fun x => ?_⟩
  exact ⟨⟨U x, Y x, T x, hT x, A.chartOpen x, rfl, A.localBiholomorphism x, A.proj_localBiholomorphism x⟩, hU x⟩

/-! ### Rigidity and uniqueness -/

/-- **Rigidity of glued data.**  If the base is covered by charts of `P : X' → X`, two holomorphic maps `f g : Z → X'` with
`P ∘ f = P ∘ g` are equal, provided `f` has no exceptional points. -/
theorem eq_of_proj_eq_of_charts {𝒞 : LocalTowerClass X} {X' : CMfd.{u} n} {P : X' → X}
    (hch : ∀ x, ∃ c : TowerChart 𝒞 X' P, x ∈ c.U) {Z : CMfd.{u} n} (f g : Z → X')
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

section Comparison

variable {𝒞 : LocalTowerClass X} (hcmp : HasComparisons 𝒞) {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X}
  {P₂ : X₂ → X} (hP₁ : Continuous P₁)

/-- The open of `X₁` over the common open `U¹ ∩ U²` of two charts. -/
def overlapDom (c₁ : TowerChart 𝒞 X₁ P₁) (c₂ : TowerChart 𝒞 X₂ P₂) : Opens X₁ :=
  ⟨P₁ ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X), (c₁.U ⊓ c₂.U).isOpen.preimage hP₁⟩

variable {hP₁} {c₁ : TowerChart 𝒞 X₁ P₁} {c₂ : TowerChart 𝒞 X₂ P₂}

theorem overlapDom_mem_V (z : overlapDom hP₁ c₁ c₂) : (z : X₁) ∈ c₁.V := c₁.mem_V z.2.1

/-- The point of the first local tower over a point of the overlap. -/
def overlapPoint (z : overlapDom hP₁ c₁ c₂) : c₁.Y := c₁.φ.symm ⟨z, overlapDom_mem_V z⟩

theorem overlapPoint_mem (z : overlapDom hP₁ c₁ c₂) :
    overlapPoint z ∈ openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)) := by
  show ((c₁.T.proj (overlapPoint z) : c₁.U) : X) ∈ (c₁.U ⊓ c₂.U : Opens X)
  rw [overlapPoint, c₁.proj_symm]
  exact z.2

variable (c₁ c₂ hP₁)

/-- The chosen comparison of the local towers of two charts. -/
def chartComparison :
    CMfd.of (n := n) (openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage c₂.T (nestedOpens c₂.U (c₁.U ⊓ c₂.U))) :=
  (hcmp c₁.U c₂.U c₁.Y c₂.Y c₁.T c₂.T c₁.mem c₂.mem).choose

theorem chartComparison_proj (y : openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U))) :
    ((c₂.T.proj (chartComparison hcmp c₁ c₂ y).val : c₂.U) : X) = ((c₁.T.proj y.val : c₁.U) : X) :=
  (hcmp c₁.U c₂.U c₁.Y c₂.Y c₁.T c₂.T c₁.mem c₂.mem).choose_spec y

/-- **The local comparison map** `φ² ∘ η ∘ (φ¹)⁻¹` on `P₁⁻¹(U¹ ∩ U²)`. -/
def overlapMap (z : overlapDom hP₁ c₁ c₂) : X₂ :=
  ((c₂.φ (chartComparison hcmp c₁ c₂ ⟨overlapPoint z, overlapPoint_mem z⟩).1 : c₂.V) : X₂)

theorem proj_overlapMap (z : overlapDom hP₁ c₁ c₂) : P₂ (overlapMap hcmp hP₁ c₁ c₂ z) = P₁ z := by
  rw [overlapMap, c₂.proj_φ, chartComparison_proj]
  exact c₁.proj_symm _

theorem contMDiff_overlapMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (overlapMap hcmp hP₁ c₁ c₂) ∧
      exceptionalLocus n (overlapMap hcmp hP₁ c₁ c₂) = ∅ := by
  have hk₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : overlapDom hP₁ c₁ c₂ => (⟨z, overlapDom_mem_V z⟩ : c₁.V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (overlapPoint : overlapDom hP₁ c₁ c₂ → c₁.Y) := c₁.φ.symm.contMDiff.comp hk₁
  have hk₂ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : overlapDom hP₁ c₁ c₂ => (⟨overlapPoint z, overlapPoint_mem z⟩ :
        openPreimage c₁.T (nestedOpens c₁.U (c₁.U ⊓ c₂.U)))) :=
    BlowupRestrictOpen.contMDiff_opens_mk hp _
  set η := chartComparison hcmp c₁ c₂
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

variable {hcmp hP₁ c₁ c₂}

/-- **The local comparison maps agree on overlaps** (rigidity of the glued data of `X₂`). -/
theorem overlapMap_eq_overlapMap (hch₂ : ∀ x, ∃ c : TowerChart 𝒞 X₂ P₂, x ∈ c.U)
    {c₁' : TowerChart 𝒞 X₁ P₁} {c₂' : TowerChart 𝒞 X₂ P₂} (z : X₁) (hz : z ∈ overlapDom hP₁ c₁ c₂)
    (hz' : z ∈ overlapDom hP₁ c₁' c₂') :
    overlapMap hcmp hP₁ c₁ c₂ ⟨z, hz⟩ = overlapMap hcmp hP₁ c₁' c₂' ⟨z, hz'⟩ := by
  let O : Opens X₁ := overlapDom hP₁ c₁ c₂ ⊓ overlapDom hP₁ c₁' c₂'
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun o : O => (⟨o, o.2.1⟩ : overlapDom hP₁ c₁ c₂)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hi' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun o : O => (⟨o, o.2.2⟩ : overlapDom hP₁ c₁' c₂')) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  obtain ⟨hl, hle⟩ := contMDiff_overlapMap hcmp hP₁ c₁ c₂
  obtain ⟨hl', -⟩ := contMDiff_overlapMap hcmp hP₁ c₁' c₂'
  have hexc : exceptionalLocus n (overlapMap hcmp hP₁ c₁ c₂ ∘ fun o : O => (⟨o, o.2.1⟩ : overlapDom hP₁ c₁ c₂)) = ∅ := by
    rw [exceptionalLocus_comp (hl.mdifferentiable (by simp)) (hi.mdifferentiable (by simp)), hle, preimage_empty,
      union_empty]
    refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
    exact HironakaBaseChange.exceptionalLocus_val
  have h := eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) O) hch₂ _ _ (hl.comp hi) (hl'.comp hi') hexc
    (fun o => (proj_overlapMap hcmp hP₁ c₁ c₂ ⟨o, o.2.1⟩).trans (proj_overlapMap hcmp hP₁ c₁' c₂' ⟨o, o.2.2⟩).symm)
  exact congrFun h ⟨z, hz, hz'⟩

end Comparison

section Glue

variable {𝒞 : LocalTowerClass X} (hcmp : HasComparisons 𝒞) {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X}
  {P₂ : X₂ → X} (hP₁ : Continuous P₁) (hch₁ : ∀ x, ∃ c : TowerChart 𝒞 X₁ P₁, x ∈ c.U)
  (hch₂ : ∀ x, ∃ c : TowerChart 𝒞 X₂ P₂, x ∈ c.U)

/-- **The glued comparison map** `X₁ → X₂`: at `z`, the local comparison map of the chosen charts at `P₁ z`. -/
def gluedMap (z : X₁) : X₂ :=
  overlapMap hcmp hP₁ (hch₁ (P₁ z)).choose (hch₂ (P₁ z)).choose
    ⟨z, (⟨(hch₁ (P₁ z)).choose_spec, (hch₂ (P₁ z)).choose_spec⟩ :
      P₁ z ∈ (((hch₁ (P₁ z)).choose.U ⊓ (hch₂ (P₁ z)).choose.U : Opens X) : Set X))⟩

/-- The glued comparison map is the local comparison map of ANY two charts on their overlap. -/
theorem gluedMap_eq (c₁ : TowerChart 𝒞 X₁ P₁) (c₂ : TowerChart 𝒞 X₂ P₂) (z : X₁)
    (hz : z ∈ overlapDom hP₁ c₁ c₂) : gluedMap hcmp hP₁ hch₁ hch₂ z = overlapMap hcmp hP₁ c₁ c₂ ⟨z, hz⟩ :=
  overlapMap_eq_overlapMap hch₂ z _ hz

theorem proj_gluedMap (z : X₁) : P₂ (gluedMap hcmp hP₁ hch₁ hch₂ z) = P₁ z :=
  proj_overlapMap hcmp hP₁ _ _ _

theorem contMDiff_gluedMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (gluedMap hcmp hP₁ hch₁ hch₂) := by
  intro z
  obtain ⟨c₁, h₁⟩ := hch₁ (P₁ z)
  obtain ⟨c₂, h₂⟩ := hch₂ (P₁ z)
  have hz : z ∈ overlapDom hP₁ c₁ c₂ :=
    (⟨h₁, h₂⟩ : P₁ z ∈ ((c₁.U ⊓ c₂.U : Opens X) : Set X))
  have hO : (fun o : overlapDom hP₁ c₁ c₂ => gluedMap hcmp hP₁ hch₁ hch₂ o) = overlapMap hcmp hP₁ c₁ c₂ :=
    funext fun o => gluedMap_eq hcmp hP₁ hch₁ hch₂ c₁ c₂ o o.2
  have h := (contMDiff_overlapMap hcmp hP₁ c₁ c₂).1 ⟨z, hz⟩
  rw [← hO] at h
  exact contMDiffAt_subtype_iff.mp h

end Glue

section Uniqueness

variable {𝒞 : LocalTowerClass X} {X₁ X₂ : CMfd.{u} n} {P₁ : X₁ → X} {P₂ : X₂ → X}

/-- **Uniqueness from charts.**  If `P₁ : X₁ → X` and `P₂ : X₂ → X` are continuous and the base is covered by charts of
both for a class with comparisons, there is a unique biholomorphism `Ψ : X₁ ≃ X₂` with `P₂ ∘ Ψ = P₁`. -/
theorem existsUnique_biholomorphism_of_charts (hcmp : HasComparisons 𝒞) (hP₁ : Continuous P₁)
    (hP₂ : Continuous P₂) (hch₁ : ∀ x, ∃ c : TowerChart 𝒞 X₁ P₁, x ∈ c.U)
    (hch₂ : ∀ x, ∃ c : TowerChart 𝒞 X₂ P₂, x ∈ c.U) :
    ∃! Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂, ∀ z, P₂ (Ψ z) = P₁ z := by
  have hF := contMDiff_gluedMap hcmp hP₁ hch₁ hch₂
  have hG := contMDiff_gluedMap hcmp hP₂ hch₂ hch₁
  have hpF := proj_gluedMap hcmp hP₁ hch₁ hch₂
  have hpG := proj_gluedMap hcmp hP₂ hch₂ hch₁
  have hGF : (gluedMap hcmp hP₂ hch₂ hch₁ ∘ gluedMap hcmp hP₁ hch₁ hch₂) = id :=
    (eq_of_proj_eq_of_charts hch₁ id _ contMDiff_id (hG.comp hF) exceptionalLocus_id
      fun z => ((hpG _).trans (hpF z)).symm).symm
  have hFG : (gluedMap hcmp hP₁ hch₁ hch₂ ∘ gluedMap hcmp hP₂ hch₂ hch₁) = id :=
    (eq_of_proj_eq_of_charts hch₂ id _ contMDiff_id (hF.comp hG) exceptionalLocus_id
      fun z => ((hpF _).trans (hpG z)).symm).symm
  let Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂ :=
    { toFun := gluedMap hcmp hP₁ hch₁ hch₂
      invFun := gluedMap hcmp hP₂ hch₂ hch₁
      left_inv := congrFun hGF
      right_inv := congrFun hFG
      contMDiff_toFun := hF
      contMDiff_invFun := hG }
  refine ⟨Ψ, hpF, fun Ψ' hΨ' => ?_⟩
  apply Diffeomorph.ext
  intro z
  exact congrFun (eq_of_proj_eq_of_charts hch₂ Ψ' (gluedMap hcmp hP₁ hch₁ hch₂) Ψ'.contMDiff hF
    (eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus Ψ'))
    fun z => (hΨ' z).trans (hpF z).symm) z

/-- **The comparison is the chosen local one on each overlap.** -/
theorem biholomorphism_eq_overlapMap (hcmp : HasComparisons 𝒞) (hP₁ : Continuous P₁)
    (hch₂ : ∀ x, ∃ c : TowerChart 𝒞 X₂ P₂, x ∈ c.U)
    (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) (hΨ : ∀ z, P₂ (Ψ z) = P₁ z)
    (c₁ : TowerChart 𝒞 X₁ P₁) (c₂ : TowerChart 𝒞 X₂ P₂) (z : X₁) (hz : z ∈ overlapDom hP₁ c₁ c₂) :
    Ψ z = overlapMap hcmp hP₁ c₁ c₂ ⟨z, hz⟩ := by
  let O := overlapDom hP₁ c₁ c₂
  obtain ⟨hl, -⟩ := contMDiff_overlapMap hcmp hP₁ c₁ c₂
  have hexc : exceptionalLocus n (Ψ ∘ (Subtype.val : O → X₁)) = ∅ := by
    rw [exceptionalLocus_diffeo_comp _ contMDiff_subtype_val, HironakaBaseChange.exceptionalLocus_val]
  have h := eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) O) hch₂ (Ψ ∘ Subtype.val) (overlapMap hcmp hP₁ c₁ c₂)
    (Ψ.contMDiff.comp contMDiff_subtype_val) hl hexc
    fun o => (hΨ o).trans (proj_overlapMap hcmp hP₁ c₁ c₂ o).symm
  exact congrFun h ⟨z, hz⟩

/-- **Uniqueness of the glued space**: two spaces glued from the same class with comparisons are biholomorphic over `X`
by a unique biholomorphism. -/
theorem existsUnique_biholomorphism (hcmp : HasComparisons 𝒞) (h₁ : IsGluedFrom 𝒞 X₁ P₁)
    (h₂ : IsGluedFrom 𝒞 X₂ P₂) :
    ∃! Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂, ∀ z, P₂ (Ψ z) = P₁ z :=
  existsUnique_biholomorphism_of_charts hcmp h₁.1.continuous h₂.1.continuous h₁.2.2.2 h₂.2.2.2

/-- **Existence and uniqueness**: a class with comparisons covering `X` glues to some `P : X' → X`, and every space glued
from the class is identified with it by a unique biholomorphism over `X`. -/
theorem existsUnique_isGluedFrom (hcov : Covers 𝒞) (hcmp : HasComparisons 𝒞) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedFrom 𝒞 X' P ∧
      ∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedFrom 𝒞 X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z := by
  obtain ⟨X', P, h⟩ := exists_isGluedFrom hcov hcmp
  exact ⟨X', P, h, fun X'' P' h' => existsUnique_biholomorphism hcmp h' h⟩

end Uniqueness

end

end Hironaka.HironakaG3RTowerClass
