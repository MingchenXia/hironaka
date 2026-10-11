/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Analytic.HolomorphicLocalInverse
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Analytic.AnalyticSubsetOpenMaps
import Hironaka.Resolution.HironakaPureRegularDensity
import Hironaka.Resolution.HironakaBlowupCompactPreimage

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Actual positions at the recorded stages of a blowup tower

The blueprint `hironaka-stage-centres-extension.tex` distinguishes the literal
Bierstone--Milman condition from the weaker containment outside the boundary.
The latter is produced for every recorded test step. A separate producer selects
an actual smooth singular centre from a freshly initialized current vanishing
ideal. It does not assert termination of that reinitialization procedure.

No project statement module is imported, and no existing statement is changed.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaStageCenters

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold
open HironakaAdmissibleSequence RestrictEmptyTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

section Boundary

variable {X Y : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {C : Set X} {π : Y → X}

/-- Every point above an old boundary member is in the new accumulated boundary:
over the centre it is in the new member, and elsewhere in the actual strict transform. -/
theorem preimage_boundary_subset_boundary_geoTransform :
    π ⁻¹' (⋃ H ∈ 𝔪.E, H) ⊆ ⋃ H ∈ (𝔪.geoTransform C π).E, H := by
  intro z hz
  rw [geoTransform_E]
  by_cases hzC : π z ∈ C
  · exact mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hzC⟩
  · obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨geoStrictTransform π C H,
      List.mem_append_left _ (List.mem_map.mpr ⟨H, hH, rfl⟩), subset_closure ⟨hzH, hzC⟩⟩

/-- Outside the new boundary the image is outside both the centre and old boundary. -/
theorem notMem_boundary_geoTransform {z : Y}
    (hz : z ∉ ⋃ H ∈ (𝔪.geoTransform C π).E, H) :
    π z ∉ C ∧ π z ∉ ⋃ H ∈ 𝔪.E, H := by
  refine ⟨?_, fun h => hz (preimage_boundary_subset_boundary_geoTransform 𝔪 h)⟩
  intro hzC
  apply hz
  rw [geoTransform_E]
  exact mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hzC⟩

/-- A point outside the accumulated boundary lies over a point outside the initial boundary. -/
theorem notMem_initial_boundary_of_notMem_boundary {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y},
      y ∉ ⋃ H ∈ (geoTransformAlong 𝔪 T).E, H → T.proj y ∉ ⋃ H ∈ 𝔪.E, H
  | _, .refl, _, h => h
  | _, .step T C π hπ, y, h => by
      have h' := notMem_boundary_geoTransform (geoTransformAlong 𝔪 T) h
      exact notMem_initial_boundary_of_notMem_boundary 𝔪 T h'.2

/-- The accumulated boundary contains the exceptional locus of every prefix projection. -/
theorem exceptionalLocus_subset_boundary {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      exceptionalLocus n T.proj ⊆ ⋃ H ∈ (geoTransformAlong 𝔪 T).E, H
  | _, .refl => by simp [BlowupTower.proj, exceptionalLocus_id]
  | _, .step T C π hπ => by
      rw [BlowupTower.proj_step, exceptionalLocus_comp
        (T.contMDiff_proj.mdifferentiable (by simp)) (hπ.contMDiff.mdifferentiable (by simp))]
      intro z hz
      rcases hz with hz | hz
      · have hzC := BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hz
        change z ∈ ⋃ H ∈ ((geoTransformAlong 𝔪 T).geoTransform C π).E, H
        rw [geoTransform_E]
        exact mem_iUnion₂.mpr ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _), hzC⟩
      · exact preimage_boundary_subset_boundary_geoTransform (geoTransformAlong 𝔪 T)
          (exceptionalLocus_subset_boundary 𝔪 T hz)

end Boundary

/-- The actual controlled cosupport transports to the initial one off the accumulated boundary. -/
theorem mem_cosupp_geoTransformAlong_iff_of_notMem_boundary {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → ∀ {y : Y},
      y ∉ ⋃ H ∈ (geoTransformAlong 𝔪 T).E, H →
      (y ∈ (geoTransformAlong 𝔪 T).cosupp ↔ T.proj y ∈ 𝔪.cosupp)
  | _, .refl, _, _, _ => Iff.rfl
  | _, .step T C π hπ, hT, y, hy => by
      have h' := notMem_boundary_geoTransform (geoTransformAlong 𝔪 T) hy
      obtain ⟨hNT, hcT⟩ :=
        MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT.1
      exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ h'.1).trans
        (mem_cosupp_geoTransformAlong_iff_of_notMem_boundary 𝔪 hN h𝔞 T hT.1 h'.2)

/-- Off the accumulated boundary the current cosupport is exactly the actual current strict transform. -/
theorem mem_cosupp_iff_mem_strictTransform_of_notMem_boundary {X Y : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosed W)
    (hcoh : (vanishingIdeal (n := n) W).IsCoherent) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    {y : Y} (hy : y ∉ ⋃ H ∈
      (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E, H) :
    y ∈ (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      y ∈ strictTransform n T.proj W := by
  let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  have h := mem_cosupp_geoTransformAlong_iff_of_notMem_boundary 𝔪
    HomogenizedGlueingTower.isClosedSubmanifold_univ hcoh T hT hy
  rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW] at h
  exact h.trans (HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem
    T.contMDiff_proj.continuous hW (fun he => hy (exceptionalLocus_subset_boundary 𝔪 T he))).symm

/-- Any extra current controlled cosupport is contained in the actual accumulated boundary. -/
theorem cosupp_subset_strictTransform_union_boundary {X Y : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosed W)
    (hcoh : (vanishingIdeal (n := n) W).IsCoherent) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T) :
    (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp ⊆
      strictTransform n T.proj W ∪ ⋃ H ∈
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E, H := by
  intro y hy
  by_cases hyE : y ∈ ⋃ H ∈
      (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E, H
  · exact Or.inr hyE
  · exact Or.inl ((mem_cosupp_iff_mem_strictTransform_of_notMem_boundary hW hcoh T hT hyE).mp hy)

/-- Regularity of the actual strict transform and its image are equivalent at any unramified point. -/
theorem regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {W : Set X} (hW : IsClosed W) {y : Y} (hy : y ∉ exceptionalLocus n f) (d : ℕ) :
    RegularAtDim (n := n) (strictTransform n f W) y d ↔ RegularAtDim (n := n) W (f y) d := by
  obtain ⟨V, s, hV, hfyV, hsy, hfs, hs, -⟩ := HolomorphicLocalInverse.exists_localInverse hf hy
  let U : Opens X := ⟨V, hV⟩
  have hsU : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun x : U => s x) :=
    AnalyticSubsetOpens.contMDiff_restrict (fun x hx => (hs x hx).contMDiffWithinAt)
  have hsec : f ∘ (fun x : U => s x) = Subtype.val := funext fun x => hfs x x.2
  have hpre := CodimOnePartCanonical.regularAtDim_preimage_iff_of_section hf U
    (fun x : U => s x) hsU hsec hfyV hsy (A := W) (k := d)
  have heq : ∀ᶠ z in 𝓝 y, z ∈ strictTransform n f W ↔ z ∈ f ⁻¹' W := by
    filter_upwards [(StrictTransformComposition.isOpen_compl_exceptionalLocus hf).mem_nhds hy] with z hz
    exact HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem hf.continuous hW hz
  exact (Iff.intro
    (CodimOneSupport.regularAtDim_of_eventually_mem_iff heq)
    (CodimOneSupport.regularAtDim_of_eventually_mem_iff (heq.mono fun _ h => h.symm))).trans hpre

/-- A property of every actual recorded centre, evaluated with its actual prefix tower. -/
def StageCentres {X : CMfd.{u} n}
    (P : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Set Y → Prop) :
    ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => StageCentres P T ∧ P T C

/-- Every actual test centre lies in the current strict transform or current boundary. -/
theorem stageCentresInStrictTransformOrBoundary_of_isGeoTestTower {X : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosed W)
    (hcoh : (vanishingIdeal (n := n) W).IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T →
      StageCentres (fun S C => C ⊆ strictTransform n S.proj W ∪ ⋃ H ∈
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hT =>
      ⟨stageCentresInStrictTransformOrBoundary_of_isGeoTestTower hW hcoh T hT.1,
        hT.2.2.1.trans (cosupp_subset_strictTransform_union_boundary hW hcoh T hT.1)⟩

/-- Every recorded test centre outside its current boundary is singular in its
current strict transform, when the centres lie over the original bad locus. -/
theorem stageCentresSingularOffBoundary_of_isGeoTestTower {X : CMfd.{u} n}
    {W : Set X} {E₀ : List (Set X)} (hW : IsClosed W)
    (hcoh : (vanishingIdeal (n := n) W).IsCoherent) (d : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T →
      CentresOver ((W \ regularLocus (n := n) W d) ∪ (W ∩ ⋃ H ∈ E₀, H)) T →
      StageCentres (fun S C => C \ (⋃ H ∈
        (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) ⊆
        strictTransform n S.proj W \ regularLocus (n := n) (strictTransform n S.proj W) d) T
  | _, .refl, _, _ => trivial
  | _, .step T _C _π _hπ, hT, hF => by
      refine ⟨stageCentresSingularOffBoundary_of_isGeoTestTower hW hcoh d T hT.1 hF.1, ?_⟩
      rintro c ⟨hc, hcE⟩
      let 𝔪 : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
      have hcs := (mem_cosupp_iff_mem_strictTransform_of_notMem_boundary hW hcoh T hT.1 hcE).mp
        (hT.2.2.1 hc)
      have horigE := notMem_initial_boundary_of_notMem_boundary 𝔪 T hcE
      have hbad := (hF.2 hc).resolve_right (fun h => horigE h.2)
      refine ⟨hcs, fun hreg => hbad.2 ?_⟩
      exact (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW
        (fun he => hcE (exceptionalLocus_subset_boundary 𝔪 T he)) d).mp hreg

/-- An actual compact pure-dimensional embedded resolution whose recorded
centres carry the proven current-stage positions outside the boundary. -/
theorem exists_tower_embeddedResolution_pure_stage_positions {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T ∧
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) Y T.proj
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      (∀ x ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) x d) ∧
      NormalCrossings.HasNormalCrossings n (strictTransform n T.proj W)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E ∧
      StageCentres (fun S C => C ⊆ strictTransform n S.proj W ∪ ⋃ H ∈
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) T ∧
      StageCentres (fun S C => C \ (⋃ H ∈
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) S).E, H) ⊆
        strictTransform n S.proj W \ regularLocus (n := n) (strictTransform n S.proj W) d) T := by
  let 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  have hdom : IsInvDomain n 𝔪 :=
    HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure
  have hcos : 𝔪.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed []
  let O : Opens X := ⟨(W \ regularLocus (n := n) W d)ᶜ,
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).isOpen_compl⟩
  have hregO : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hx hxO
    by_contra hxreg
    exact hxO ⟨hx, hxreg⟩
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := hpure.trans (closure_mono (by
    intro x hx
    exact ⟨regularLocus_subset _ _ hx, fun h => h.2 hx⟩))
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hK)
  obtain ⟨Y, T, hT, hTO, hSM, hreg, hNC⟩ := exists_tower_embedded_of_isCanonical
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
    hWa O hregO hdense hdom T₀ hcan₀ hres₀
  have hTF : CentresOver (W \ regularLocus (n := n) W d) T := by
    simpa [O] using centresOver_compl_of_centresAvoid O T hTO
  have hTF' : CentresOver ((W \ regularLocus (n := n) W d) ∪ (W ∩ ⋃ H ∈ ([] : List (Set X)), H)) T := by
    simpa using hTF
  exact ⟨Y, T, hT, isAdmissibleBlowupSequence_proj 𝔪 _ T hT hTF, hSM, hreg, hNC,
    stageCentresInStrictTransformOrBoundary_of_isGeoTestTower hWa.isClosed hdom.isWellFormed.isCoherent T hT,
    stageCentresSingularOffBoundary_of_isGeoTestTower hWa.isClosed hdom.isWellFormed.isCoherent d T hT hTF'⟩

section FreshCentre

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- If the present pure-dimensional analytic set is not smooth, the genuine
initial maximum for its own vanishing ideal contains only present singular points. -/
theorem fresh_maxLocus_subset_singular_of_not_isClosedSubmanifold
    (hF : EmbeddedFromResolution.EmbeddingFields n k inv) {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    (hns : ¬ IsClosedSubmanifold n W) :
    maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (.refl : BlowupTower X X))
      W ⊆ W \ regularLocus (n := n) W d := by
  intro c hc
  refine ⟨hc.1, ?_⟩
  intro hreg
  let 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  let T : BlowupTower X X := .refl
  let O : Opens X := ⟨(W \ regularLocus (n := n) W d)ᶜ,
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).isOpen_compl⟩
  have hcO : T.proj c ∈ O := fun h => h.2 hreg
  have hcos : (geoTransformAlong 𝔪 T).cosupp = W :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed []
  have hc' : c ∈ maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
    rwa [hcos]
  have hregO : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hx hxO
    by_contra hxreg
    exact hxO ⟨hx, hxreg⟩
  have hdense : W ⊆ closure (W ∩ (O : Set X)) := hpure.trans (closure_mono (by
    intro x hx
    exact ⟨regularLocus_subset _ _ hx, fun h => h.2 hx⟩))
  have hadm := hF.isAdmissibleCentre_maxLocus hdom T trivial trivial
  have hCV : ∀ y : X, T.proj y ∈ O →
      (y ∈ maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp ↔ T.proj y ∈ W) := fun y hy =>
    HironakaEmbeddedBoundary.mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O
      (fun H hH => by cases hH) (fun x hx => hregO x hx x.2) hdom T trivial trivial hc' hcO hy
  obtain ⟨_, _, hregs⟩ := HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid hWa O
    hregO hdense T trivial hadm.1 hCV
  have hST : strictTransform n T.proj W = W := by
    simp [T, strictTransform, exceptionalLocus_id, hWa.isClosed.closure_eq]
  rw [hST] at hregs
  exact hns ⟨hWa.isClosed, fun x hx => ⟨d, hregs x hx⟩⟩

end FreshCentre

/-- The actual canonical invariant produces a nonempty smooth centre in the
current singular locus, initialized on the actual current vanishing ideal. -/
theorem exists_fresh_admissibleCentre_subset_singular {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) (hns : ¬ IsClosedSubmanifold n W) :
    ∃ C : Set X, C.Nonempty ∧
      (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      C = maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) (.refl : BlowupTower X X)) W := by
  let 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hdom : IsInvDomain n 𝔪 :=
    HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hWa hd hpure
  have hcos : 𝔪.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed []
  have hne : W.Nonempty := by
    by_contra h
    have hzero : W = ∅ := not_nonempty_iff_eq_empty.mp h
    apply hns
    rw [hzero]
    exact ⟨isClosed_empty, fun x hx => (notMem_empty x hx).elim⟩
  have husc := R.isInvValue.usc 𝔪 hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl, hcos] at husc
  obtain ⟨c, hc, hmax⟩ := husc.exists_isMaxOn hK hne
  let C := maxLocus (R.inv 𝔪 (.refl : BlowupTower X X)) W
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  have hadm := hF.isAdmissibleCentre_maxLocus hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl, hcos] at hadm
  exact ⟨C, ⟨c, hc, hmax⟩, hadm,
    fresh_maxLocus_subset_singular_of_not_isClosedSubmanifold hF hWa hpure hdom hns, rfl⟩

/-- Construct an actual blowup in the present singular locus and the actual
compact irreducible next strict transform, with its freshly initialized domain. -/
theorem exists_fresh_singular_blowup_subvariety {X : CMfd.{u} n}
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hd : V.dim < n) (hK : IsCompact V.carrier)
    (hns : ¬ IsClosedSubmanifold n V.carrier) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X) (V' : ClosedIrreducibleAnalyticSubvariety n Y),
      C.Nonempty ∧ (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C ⊆ Hironaka.singularLocus V ∧ IsBlowupAlong n C π ∧
      V'.carrier = strictTransform n π V.carrier ∧ V'.dim = V.dim ∧ IsCompact V'.carrier ∧
      NormalCrossings.IsSNCDivisor n [π ⁻¹' C] ∧
      IsInvDomain n (⟨univ, [π ⁻¹' C], vanishingIdeal (n := n) V'.carrier, 1⟩ : MarkedIdeal n Y) := by
  obtain ⟨C, hCne, hCadm, hCsing, _⟩ := exists_fresh_admissibleCentre_subset_singular V.analytic hK hd
    (HironakaEmbeddedReducible.subset_closure_regularLocus V) hns
  have hCint : interior C = ∅ := eq_empty_of_subset_empty ((interior_mono
    (hCsing.trans sdiff_subset)).trans (EmbeddedFromResolution.interior_eq_empty_of_dim_lt V hd).subset)
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hCint
  have hExcS : π '' exceptionalLocus n π ⊆ Hironaka.singularLocus V :=
    (ExceptionalFibres.image_exceptionalLocus_subset hπ).trans hCsing
  have hVnot := StrictTransformSubvarietySequence.not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
    V hExcS
  obtain ⟨V', hV', hd'⟩ := HironakaEmbeddedResolutionLocal.exists_strictTransform_subvariety_of_isBlowupAlong hπ V hVnot
  have hK' : IsCompact V'.carrier :=
    (HironakaLocalPrincipalization.isCompact_preimage_of_isBlowupAlong hπ hK).of_isClosed_subset
      V'.isClosed_carrier (by
        rw [hV']
        exact closure_minimal sdiff_subset (V.isClosed_carrier.preimage hπ.contMDiff.continuous))
  let 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩
  let T : BlowupTower X Y := .step .refl C π hπ
  have hdom : IsInvDomain n 𝔪 := EmbeddedFromResolution.isInvDomain_vanishingIdeal_of_dim_lt
    le_rfl V hd (CartanIrreducible.cartanCoherence V.carrier V.analytic)
  have hT : IsGeoTestTower 𝔪 T := ⟨trivial, hCadm⟩
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hdom.isWellFormed T hT
  have hEsnc : NormalCrossings.IsSNCDivisor n [π ⁻¹' C] := by
    simpa [T, geoTransformAlong_step, geoTransformAlong_refl, 𝔪, geoTransform_E] using hwf.isSNCDivisor
  have hdV' : V'.dim < n := hd' ▸ hd
  have hdom' : IsInvDomain n
      (⟨univ, [π ⁻¹' C], vanishingIdeal (n := n) V'.carrier, 1⟩ : MarkedIdeal n Y) :=
    HironakaEmbeddedBoundary.isInvDomain_boundary V'.analytic
      (EmbeddedFromResolution.interior_eq_empty_of_dim_lt V' hdV') hEsnc
  exact ⟨C, Y, π, V', hCne, hCadm, hCsing, hπ, hV', hd', hK', hEsnc, hdom'⟩

end

end Hironaka.HironakaStageCenters
