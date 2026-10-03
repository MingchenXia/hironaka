/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Resolution.HironakaBoundaryRelativelyCompact
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaSeparation
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularPointDimension
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution of an arbitrary analytic set over relatively compact open sets (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6 and §13 ("finite over every
relatively compact open subset"); Włodarczyk 2005 (`wlodarczyk05-hironaka`).

**Statement.**  Let `X` be any complex manifold, `W ⊆ X` an analytic set with empty interior whose components may have
different dimensions (not necessarily compact), and `X₀ ⊆ X` an open set contained in a compact set.  With `W_sing` the points
at which `W` is not a submanifold of any dimension (`HironakaEmbeddedAnalytic.singularSet`) and `W⁽ᵏ⁾ = closure (Reg_k W)`,
there is ONE admissible blowup sequence `f : X₀' → X₀` (from the empty divisor, centres over `W_sing ∩ X₀`) with divisor `E`
such that `E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing ∩ X₀)`, `f` is an isomorphism over `X₀ \ W_sing`, the
strict transform of `W ∩ X₀` is a closed submanifold, the union of the pairwise disjoint strict transforms of the `W⁽ᵏ⁾ ∩ X₀`
(`k < n`), of dimension `k` along the strict transform of `W⁽ᵏ⁾ ∩ X₀`, with only normal crossings with `E`.  The same holds
relative to a simple normal crossings divisor `E₀` (restricted to `X₀`), and over a relatively compact neighbourhood of any
compact set.

**Route.**  The induction of `HironakaEmbeddedAnalytic` (separate one part from the others, resolve it, recurse on the others),
with every step done over a relatively compact open set and then pulled back to the given base by base change along an open
holomorphic embedding (`HironakaBaseChange`):

* the parts are *locally good* (`IsLocGoodPart`: as `IsGoodPart` without compactness);
* the induction statement (`exists_resolution_list_local`) is for an arbitrary open holomorphic embedding `ι : B → X` whose
  image lies in a compact set, the sequence living over `B`;
* in the step, a relatively compact neighbourhood `U` of the closure of `ι(B)` is chosen; the first part `A` is separated from
  the union of the others over `U` (`exists_separation_of_subset_isCompact`: principalization of `𝓘_A + 𝓘_{A'}` over `U`,
  `HironakaBoundaryRelativelyCompact`, and `HironakaSeparation.disjoint_strictTransform_of_pullback_sumIdeal`); the sequence is
  pulled back to `B` along `ι` (`exists_baseChange_of_subset`), giving an open holomorphic embedding `j₁` of the new base into
  the blown-up `U`, whose image lies in the compact preimage of the closure of `ι(B)` (blowup sequences are proper);
* then the strict transform of `A` is resolved over a relatively compact neighbourhood of the closure of `j₁(·)`
  (`HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact`) and pulled back along `j₁`;
* the remaining parts are resolved by the induction hypothesis along the new open holomorphic embedding `j₂`, with the bad set
  cut down to their strict transforms (disjoint from the resolved first part), as in the compact case.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedAnalyticLocal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence Hironaka.HironakaAdmissibleCalculus Hironaka.HironakaEmbeddedDimensionParts Hironaka.HironakaBaseChange Hironaka.HironakaEmbeddedAnalytic Hironaka.RestrictedIdealExtension Hironaka.DivisorExponentAlong

noncomputable section

variable {n : ℕ}

/-! ### Finite unions of analytic sets -/

section Union

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Products of the local equations present a union. -/
def presentationUnion {A B : Set M} {x : M} (pA : ComplexAnalyticPresentationAt (n := n) A x)
    (pB : ComplexAnalyticPresentationAt (n := n) B x) :
    ComplexAnalyticPresentationAt (n := n) (A ∪ B) x where
  generatorCount := pA.generatorCount * pB.generatorCount
  generator := fun ij z =>
    pA.generator (finProdFinEquiv.symm ij).1 z * pB.generator (finProdFinEquiv.symm ij).2 z
  coordinateNeighborhood := pA.coordinateNeighborhood ∩ pB.coordinateNeighborhood
  isOpen_coordinateNeighborhood :=
    pA.isOpen_coordinateNeighborhood.inter pB.isOpen_coordinateNeighborhood
  center_mem_coordinateNeighborhood :=
    ⟨pA.center_mem_coordinateNeighborhood, pB.center_mem_coordinateNeighborhood⟩
  coordinateNeighborhood_subset_target :=
    inter_subset_left.trans pA.coordinateNeighborhood_subset_target
  generator_holomorphic := fun _ =>
    ((pA.generator_holomorphic _).mono inter_subset_left).mul
      ((pB.generator_holomorphic _).mono inter_subset_right)
  zeroLocus := by
    intro y hy hyN
    rw [mem_union, pA.zeroLocus hy hyN.1, pB.zeroLocus hy hyN.2]
    constructor
    · rintro (h | h) ij
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    · intro h
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
      have := h (finProdFinEquiv (i, j))
      simp only [Equiv.symm_apply_apply] at this
      exact mul_ne_zero hi hj this

/-- **The union of two analytic sets is analytic.** -/
theorem isComplexAnalyticSubset_union {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) : IsComplexAnalyticSubset (n := n) (A ∪ B) :=
  fun x => ⟨presentationUnion (hA x).some (hB x).some⟩

/-- **The union of the first components of a list of analytic sets is analytic.** -/
theorem isComplexAnalyticSubset_biUnion_list {ι : Type*} :
    ∀ (L : List (Set M × ι)), (∀ p ∈ L, IsComplexAnalyticSubset (n := n) p.1) →
      IsComplexAnalyticSubset (n := n) (⋃ p ∈ L, p.1)
  | [], _ => by simp
  | q :: L, h => by
      have h1 : (⋃ p ∈ q :: L, p.1) = q.1 ∪ ⋃ p ∈ L, p.1 := by
        ext x
        simp
      rw [h1]
      exact isComplexAnalyticSubset_union (h q (List.mem_cons_self ..))
        (isComplexAnalyticSubset_biUnion_list L fun p hp => h p (List.mem_cons_of_mem _ hp))

end Union

/-! ### Locally good parts -/

section Parts

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

variable (n) in
/-- **A locally good part `(A, d)` relative to a divisor `E` and a bad set `G`**: `A` is an analytic set, `d < n`, the points of
`A` at which it is not a submanifold of dimension `d` and the points of `A` on `|E|` lie in `G`, and `A \ G` is dense in `A`
(`HironakaEmbeddedAnalytic.IsGoodPart` without compactness). -/
def IsLocGoodPart (E : List (Set X)) (G A : Set X) (d : ℕ) : Prop :=
  IsComplexAnalyticSubset (n := n) A ∧ d < n ∧ A \ regularLocus (n := n) A d ⊆ G ∧
    A ∩ (⋃ H ∈ E, H) ⊆ G ∧ A ⊆ closure (A \ G)

namespace IsLocGoodPart

variable {E : List (Set X)} {G A : Set X} {d : ℕ}

theorem isClosed (h : IsLocGoodPart n E G A d) : IsClosed A := h.1.isClosed

/-- A locally good part is of pure dimension `d`. -/
theorem pure (h : IsLocGoodPart n E G A d) : A ⊆ closure (regularLocus (n := n) A d) := by
  refine h.2.2.2.2.trans (closure_mono fun x hx => ?_)
  by_contra hreg
  exact hx.2 (h.2.2.1 ⟨hx.1, hreg⟩)

/-- A locally good part has empty interior. -/
theorem interior_eq_empty (h : IsLocGoodPart n E G A d) : interior A = ∅ :=
  HironakaEmbeddedReducible.interior_eq_empty_of_pure h.2.1 h.pure

/-- No member of `E` contains a nonempty relatively open subset of a locally good part. -/
theorem subset_closure_diff_biUnion (h : IsLocGoodPart n E G A d) : A ⊆ closure (A \ ⋃ H ∈ E, H) :=
  h.2.2.2.2.trans (closure_mono fun _ hx => ⟨hx.1, fun hxE => hx.2 (h.2.2.2.1 ⟨hx.1, hxE⟩)⟩)

/-- A locally good part off the bad set is dense in it. -/
theorem subset_closure_diff_of_inter_subset (h : IsLocGoodPart n E G A d) {B : Set X} (hB : A ∩ B ⊆ G) :
    A ⊆ closure (A \ B) :=
  h.2.2.2.2.trans (closure_mono fun _ hx => ⟨hx.1, fun hxB => hx.2 (hB ⟨hx.1, hxB⟩)⟩)

/-- **Cutting down the bad set** to its intersection with a set containing the part. -/
theorem inter (h : IsLocGoodPart n E G A d) {K : Set X} (hAK : A ⊆ K) : IsLocGoodPart n E (G ∩ K) A d := by
  refine ⟨h.1, h.2.1, fun x hx => ⟨h.2.2.1 hx, hAK hx.1⟩, fun x hx => ⟨h.2.2.2.1 hx, hAK hx.1⟩,
    h.2.2.2.2.trans (closure_mono fun x hx => ⟨hx.1, fun hxG => hx.2 hxG.1⟩)⟩

/-- **Locally good parts are carried along an admissible sequence**: if `f` is an admissible sequence of `(X, E)` with centres
over the closed set `G` (members of `E` closed), the strict transform of a locally good part is a locally good part relative to
the accumulated divisor and `f⁻¹ G`. -/
theorem strictTransform {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} {E' : List (Set Y)} (hf : IsAdmissibleBlowupSequence n X E G Y f E') (hE : ∀ H ∈ E, IsClosed H)
    (h : IsLocGoodPart n E G A d) : IsLocGoodPart n E' (f ⁻¹' G) (strictTransform n f A) d := by
  have hfc := hf.isBlowupSequence.contMDiff
  refine ⟨isComplexAnalyticSubset_strictTransform hf.isBlowupSequence h.1, h.2.1,
    diff_regularLocus_strictTransform_subset hfc (IsAdmissibleBlowupSequence.exceptionalLocus_subset hf) h.isClosed
      h.2.2.1, fun z hz => ?_, strictTransform_subset_closure_diff hfc h.isClosed h.2.2.2.2⟩
  have hzA : f z ∈ A := strictTransform_subset_preimage hfc.continuous h.isClosed hz.1
  rcases IsAdmissibleBlowupSequence.biUnion_subset hf hE hz.2 with h1 | h1
  · exact h.2.2.2.1 ⟨hzA, h1⟩
  · exact h1

/-- **Locally good parts pull back along open holomorphic embeddings.** -/
theorem preimage {B : Type u} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]
    {ι : B → X} (hι : IsOpenHoloEmbedding n ι) (h : IsLocGoodPart n E G A d) :
    IsLocGoodPart n (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) (ι ⁻¹' A) d := by
  refine ⟨AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hι.contMDiff h.1, h.2.1, fun x hx => ?_,
    fun x hx => ?_, ?_⟩
  · by_contra hxG
    exact hx.2 (hι.regularAtDim_preimage (by_contra fun hreg => hxG (h.2.2.1 ⟨hx.1, hreg⟩)))
  · obtain ⟨H', hH', hxH'⟩ := mem_iUnion₂.mp hx.2
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    exact h.2.2.2.1 ⟨hx.1, mem_iUnion₂.mpr ⟨H, hH, hxH'⟩⟩
  · calc ι ⁻¹' A ⊆ ι ⁻¹' closure (A \ G) := preimage_mono h.2.2.2.2
      _ = closure (ι ⁻¹' A \ ι ⁻¹' G) := by rw [hι.preimage_closure, preimage_sdiff]

end IsLocGoodPart

end Parts

/-! ### Separation over an open set contained in a compact set -/

section Separation

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The strict transform along `ι ∘ f`** of a closed set `S`, for an open holomorphic embedding `ι`, is the strict transform
of `ι⁻¹ S` along `f`. -/
theorem strictTransform_comp_of_isOpenHoloEmbedding {B Y : Type u} [TopologicalSpace B]
    [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {ι : B → X} (hι : IsOpenHoloEmbedding n ι) {f : Y → B}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {S : Set X} (hS : IsClosed S) :
    strictTransform n (ι ∘ f) S = strictTransform n f (ι ⁻¹' S) := by
  rw [StrictTransformComposition.strictTransform_comp hι.contMDiff hf]
  congr 1
  rw [strictTransform, hι.exceptionalLocus_eq_empty, sdiff_empty]
  exact (hS.preimage hι.continuous).closure_eq

/-- **Separation over an open set contained in a compact set, relative to a boundary**: let `A, B ⊆ X` be analytic, `A` with
empty interior, each the closure of its part off the other, `E₀` a divisor with simple normal crossings and `X₀` an open set
contained in a compact set.  There is an admissible blowup sequence of `(X₀, E₀|X₀)` with centres over `A ∩ B ∩ X₀`, with a
divisor with simple normal crossings, after which the strict transforms of `A ∩ X₀` and `B ∩ X₀` are disjoint (principalization
of `𝓘_A + 𝓘_B` over `X₀`). -/
theorem exists_separation_of_subset_isCompact {A B : Set X} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hint : interior A = ∅) (hAB : A ⊆ closure (A \ B))
    (hBA : B ⊆ closure (B \ A)) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (X₀ : Opens X) {K : Set X}
    (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (A ∩ B)) X₀' f E ∧ IsSNCDivisor n E ∧
      Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' A))
        (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' B)) := by
  set J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) B) with hJdef
  have hJ : J.IsCoherent :=
    isCoherent_sumIdeal (CartanIrreducible.cartanCoherence A hAa) (CartanIrreducible.cartanCoherence B hBa)
  have hne : ∀ x, IsNonzeroAlongAt univ J x := fun x =>
    InvDomainCompanion.isNonzeroAlongAt_sumIdeal_left (𝔟 := vanishingIdeal (n := n) A)
      (𝔠 := vanishingIdeal (n := n) B) (fun _ _ h => h.1)
      (HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hAa hint x)
  have hZ : J.zeroLocus = A ∩ B := HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hAa.isClosed hBa.isClosed
  obtain ⟨X₀', i1, i2, i3, f, D, E, hadm, hsnc, hpb, -, hsupp, -⟩ :=
    HironakaBoundaryRelativelyCompact.exists_principalization_boundary_of_subset_isCompact hJ hne hE₀ X₀ hK hX₀
  rw [hZ] at hadm hsupp
  have hf := hadm.isBlowupSequence.contMDiff
  have hval := isOpenHoloEmbedding_val (n := n) X₀
  have hpb' : GermIdeal.pullback (m := n) ((Subtype.val : X₀ → X) ∘ f) J = D.ideal := by
    rw [GermIdealTotalTransform.pullback_comp hval.contMDiff hf hJ, hpb]
  have hdisj := HironakaSeparation.disjoint_strictTransform_of_pullback_sumIdeal (hval.contMDiff.comp hf) hAB hBA D hpb'
    (by rw [hsupp]; exact subset_rfl)
  rw [strictTransform_comp_of_isOpenHoloEmbedding hval hf hAa.isClosed,
    strictTransform_comp_of_isOpenHoloEmbedding hval hf hBa.isClosed] at hdisj
  exact ⟨X₀', i1, i2, i3, f, E, hadm, hsnc, hdisj⟩

end Separation

/-! ### One step over a relatively compact neighbourhood, pulled back to the base -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {B : Type u} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B]

/-- **A relatively compact neighbourhood of the closure of the image** of a map whose image lies in a compact set. -/
theorem exists_opens_of_range_subset {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {S : Type*} {ι : S → M} (hK : ∃ K : Set M, IsCompact K ∧ range ι ⊆ K) :
    ∃ U : Opens M, closure (range ι) ⊆ U ∧ IsCompact (closure (U : Set M)) ∧ IsCompact (closure (range ι)) := by
  obtain ⟨K, hK, hιK⟩ := hK
  have hc : IsCompact (closure (range ι)) := hK.of_isClosed_subset isClosed_closure (hK.isClosed.closure_subset_iff.mpr hιK)
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel n) M
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hc
  exact ⟨⟨U, hUo⟩, hKU, hUc, hc⟩

/-- **Pulling back a step to the base**: let `ι : B → X` be an open holomorphic embedding whose image has compact closure inside
the open set `U`, and `g : Y → U` an admissible sequence of `(U, E|U)` with centres over `F ∩ U` and divisor `E₁`.  Its base
change along `ι` is an admissible sequence `g' : Y' → B` of `(B, ι⁻¹E)` with centres over `ι⁻¹F` and divisor `j⁻¹E₁`, for an
open holomorphic embedding `j : Y' → Y` whose image lies in a compact set; strict transforms correspond:
`g'`-strict transform of `ι⁻¹S` `= j⁻¹ (g`-strict transform of `S ∩ U)`. -/
theorem exists_baseChange_of_subset {ι : B → X} (hι : IsOpenHoloEmbedding n ι) {U : Opens X}
    (hιU : closure (range ι) ⊆ U) (hc : IsCompact (closure (range ι))) {E : List (Set X)} {F : Set X}
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {g : Y → U}
    {E₁ : List (Set Y)}
    (hg : IsAdmissibleBlowupSequence n U (E.map ((Subtype.val : U → X) ⁻¹' ·)) ((Subtype.val : U → X) ⁻¹' F) Y g E₁) :
    ∃ (Y' : Type u) (_ : TopologicalSpace Y') (_ : ChartedSpace (ComplexModel n) Y') (_ : IsComplexManifold n Y')
      (g' : Y' → B) (j : Y' → Y),
      IsAdmissibleBlowupSequence n B (E.map (ι ⁻¹' ·)) (ι ⁻¹' F) Y' g' (E₁.map (j ⁻¹' ·)) ∧
      IsOpenHoloEmbedding n j ∧ (∀ y, (g (j y) : X) = ι (g' y)) ∧
      (∃ K : Set Y, IsCompact K ∧ range j ⊆ K) ∧
      ∀ S : Set X, strictTransform n g' (ι ⁻¹' S) = j ⁻¹' strictTransform n g ((Subtype.val : U → X) ⁻¹' S) := by
  have hιU' : ∀ b, ι b ∈ U := fun b => hιU (subset_closure ⟨b, rfl⟩)
  set ι₁ : B → U := fun b => ⟨ι b, hιU' b⟩ with hι₁def
  have hι₁ : IsOpenHoloEmbedding n ι₁ := hι.codRestrict U hιU'
  obtain ⟨Y', i1, i2, i3, g', j, hadm, hj, hcomm, hrange⟩ :=
    IsAdmissibleBlowupSequence.exists_baseChange hg hι₁
  rw [List.map_map] at hadm
  have hgc := hg.isBlowupSequence.contMDiff
  have hg'c := hadm.isBlowupSequence.contMDiff
  refine ⟨Y', i1, i2, i3, g', j, hadm, hj, fun y => by rw [hcomm], ?_, fun S => ?_⟩
  · refine ⟨g ⁻¹' ((Subtype.val : U → X) ⁻¹' closure (range ι)), ?_, ?_⟩
    · refine (HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hg.isBlowupSequence).isCompact_preimage ?_
      rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hιU]
      exact hc
    · rw [hrange]
      rintro y ⟨b, hb⟩
      show ((g y : U) : X) ∈ closure (range ι)
      rw [← hb]
      exact subset_closure ⟨b, rfl⟩
  · exact strictTransform_preimage_eq hgc hg'c hι₁ hj hcomm ((Subtype.val : U → X) ⁻¹' S)

end Step

/-! ### Separation and resolution of a list of locally good parts over a relatively compact base -/

section Resolve

/-- **Embedded resolution of a list of locally good parts, over a base embedded in a compact set** (the induction): for a
divisor `E` with simple normal crossings, a closed bad set `G`, a list of locally good parts meeting pairwise only in `G`, and an
open holomorphic embedding `ι : B → X` whose image lies in a compact set, there is an admissible sequence of `(B, ι⁻¹E)` with
centres over `ι⁻¹G`, with a divisor with simple normal crossings, after which the strict transform of each `ι⁻¹A` (`(A, d)` a
part) is regular of dimension `d` at each of its points and has only normal crossings with the divisor, and the strict
transforms are pairwise disjoint. -/
theorem exists_resolution_list_local (m : ℕ) : ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (E : List (Set X)) (_hE : IsSNCDivisor n E) (G : Set X) (_hG : IsClosed G)
    (L : List (Set X × ℕ)), L.length = m → (∀ p ∈ L, IsLocGoodPart n E G p.1 p.2) →
    L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
    ∀ {B : Type u} [TopologicalSpace B] [ChartedSpace (ComplexModel n) B] [IsComplexManifold n B] (ι : B → X),
    IsOpenHoloEmbedding n ι → (∃ K : Set X, IsCompact K ∧ range ι ⊆ K) →
    ∃ (B' : Type u) (_ : TopologicalSpace B') (_ : ChartedSpace (ComplexModel n) B')
      (_ : IsComplexManifold n B') (f : B' → B) (E' : List (Set B')),
      IsAdmissibleBlowupSequence n B (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) B' f E' ∧ IsSNCDivisor n E' ∧
      (∀ p ∈ L, (∀ x ∈ strictTransform n f (ι ⁻¹' p.1),
          RegularAtDim (n := n) (strictTransform n f (ι ⁻¹' p.1)) x p.2) ∧
        HasNormalCrossings n (strictTransform n f (ι ⁻¹' p.1)) E') ∧
      L.Pairwise (fun p q => Disjoint (strictTransform n f (ι ⁻¹' p.1)) (strictTransform n f (ι ⁻¹' q.1))) := by
  induction m with
  | zero =>
      intro X _ _ _ E hE G _ L hL _ _ B _ _ _ ι hι _
      rw [List.length_eq_zero_iff.mp hL]
      exact ⟨B, inferInstance, inferInstance, inferInstance, id, E.map (ι ⁻¹' ·), IsAdmissibleBlowupSequence.refl,
        hι.isSNCDivisor_map_preimage hE, fun p hp => absurd hp List.not_mem_nil, List.Pairwise.nil⟩
  | succ m ih =>
      intro X _ _ _ E hE G hG L hL hgood hpair B _ _ _ ι hι hKι
      obtain ⟨⟨A, d⟩, L', rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = m := by simpa using hL
      rw [List.pairwise_cons] at hpair
      obtain ⟨hAsep, hpair'⟩ := hpair
      have hA : IsLocGoodPart n E G A d := hgood (A, d) (List.mem_cons_self ..)
      have hgood' : ∀ p ∈ L', IsLocGoodPart n E G p.1 p.2 := fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      have hEcl : ∀ H ∈ E, IsClosed H := hE.1
      -- the union of the other parts
      set Bs : Set X := ⋃ p ∈ L', p.1 with hBsdef
      have hBsa : IsComplexAnalyticSubset (n := n) Bs :=
        isComplexAnalyticSubset_biUnion_list L' fun p hp => (hgood' p hp).1
      have hABsG : A ∩ Bs ⊆ G := by
        rintro x ⟨hxA, hxB⟩
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxB
        exact hAsep p hp ⟨hxA, hxp⟩
      have hABs : A ⊆ closure (A \ Bs) := hA.subset_closure_diff_of_inter_subset hABsG
      have hBsA : Bs ⊆ closure (Bs \ A) := by
        intro x hx
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
        have h1 := (hgood' p hp).subset_closure_diff_of_inter_subset (B := A)
          (fun z hz => hAsep p hp ⟨hz.2, hz.1⟩) hxp
        refine closure_mono (fun y hy => ?_) h1
        exact ⟨mem_iUnion₂.mpr ⟨p, hp, hy.1⟩, hy.2⟩
      -- 1. separate `A` from the other parts over a relatively compact neighbourhood `U₁` of `closure (ι B)`
      obtain ⟨U₁, hιU₁, hU₁c, hcι⟩ := exists_opens_of_range_subset (n := n) hKι
      obtain ⟨Y₁, i1, i2, i3, g₁, E₁, hadm₁, hsnc₁, hdisj₁⟩ :=
        exists_separation_of_subset_isCompact hA.1 hBsa hA.interior_eq_empty hABs hBsA hE U₁ hU₁c subset_closure
      have hadm₁G : IsAdmissibleBlowupSequence n U₁ (E.map ((Subtype.val : U₁ → X) ⁻¹' ·))
          ((Subtype.val : U₁ → X) ⁻¹' G) Y₁ g₁ E₁ := hadm₁.mono (preimage_mono hABsG)
      have hg₁ := hadm₁G.isBlowupSequence.contMDiff
      obtain ⟨Y₁', j1, j2, j3, g₁', k₁, hadm₁', hk₁, hcomm₁, hKk₁, hST₁⟩ :=
        exists_baseChange_of_subset hι hιU₁ hcι hadm₁G
      have hval₁ := isOpenHoloEmbedding_val (n := n) U₁
      have hE₁cl : ∀ H ∈ E₁, IsClosed H := hsnc₁.1
      have hEU₁cl : ∀ H ∈ E.map ((Subtype.val : U₁ → X) ⁻¹' ·), IsClosed H := fun H hH => by
        obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact (hEcl H₀ hH₀).preimage continuous_subtype_val
      set G₁ : Set Y₁ := g₁ ⁻¹' ((Subtype.val : U₁ → X) ⁻¹' G) with hG₁def
      have hG₁ : IsClosed G₁ := (hG.preimage continuous_subtype_val).preimage hg₁.continuous
      -- the parts on `Y₁`
      have hgood₁ : ∀ p ∈ L', IsLocGoodPart n E₁ G₁ (strictTransform n g₁ ((Subtype.val : U₁ → X) ⁻¹' p.1)) p.2 :=
        fun p hp => ((hgood' p hp).preimage hval₁).strictTransform hadm₁G hEU₁cl
      set A₁ : Set Y₁ := strictTransform n g₁ ((Subtype.val : U₁ → X) ⁻¹' A) with hA₁def
      have hA₁ : IsLocGoodPart n E₁ G₁ A₁ d := (hA.preimage hval₁).strictTransform hadm₁G hEU₁cl
      have hdisj₁' : ∀ p ∈ L', Disjoint A₁ (strictTransform n g₁ ((Subtype.val : U₁ → X) ⁻¹' p.1)) := fun p hp =>
        hdisj₁.mono_right (strictTransform_mono g₁ (preimage_mono fun x hx => mem_iUnion₂.mpr ⟨p, hp, hx⟩))
      -- 2. resolve `A₁` over a relatively compact neighbourhood `U₂` of `closure (k₁ Y₁')`
      obtain ⟨U₂, hk₁U₂, hU₂c, hck₁⟩ := exists_opens_of_range_subset (n := n) hKk₁
      obtain ⟨Y₂, l1, l2, l3, g₂, E₂, hadm₂, hsnc₂, -, -, -, -, -, hreg₂, hnc₂⟩ :=
        HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact hA₁.1 hA₁.2.1 hA₁.pure hsnc₁
          hA₁.subset_closure_diff_biUnion U₂ hU₂c subset_closure
      have hadm₂G : IsAdmissibleBlowupSequence n U₂ (E₁.map ((Subtype.val : U₂ → Y₁) ⁻¹' ·))
          ((Subtype.val : U₂ → Y₁) ⁻¹' G₁) Y₂ g₂ E₂ :=
        hadm₂.mono (preimage_mono (union_subset hA₁.2.2.1 hA₁.2.2.2.1))
      have hg₂ := hadm₂G.isBlowupSequence.contMDiff
      obtain ⟨Y₂', m1, m2, m3, g₂', k₂, hadm₂', hk₂, hcomm₂, hKk₂, hST₂⟩ :=
        exists_baseChange_of_subset hk₁ hk₁U₂ hck₁ hadm₂G
      have hval₂ := isOpenHoloEmbedding_val (n := n) U₂
      have hE₁U₂cl : ∀ H ∈ E₁.map ((Subtype.val : U₂ → Y₁) ⁻¹' ·), IsClosed H := fun H hH => by
        obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact (hE₁cl H₀ hH₀).preimage continuous_subtype_val
      -- the parts on `Y₂`
      set T : Set X → Set Y₂ := fun S =>
        strictTransform n g₂ ((Subtype.val : U₂ → Y₁) ⁻¹' strictTransform n g₁ ((Subtype.val : U₁ → X) ⁻¹' S))
        with hTdef
      set L₂ : List (Set Y₂ × ℕ) := L'.map fun p => (T p.1, p.2) with hL₂
      set K₂ : Set Y₂ := ⋃ p ∈ L₂, p.1 with hK₂
      have hK₂cl : IsClosed K₂ := by
        have h1 := HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed (E := L₂.map Prod.fst)
          (fun H hH => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hH
            obtain ⟨p₁, -, rfl⟩ := List.mem_map.mp hp
            exact isClosed_closure)
        have h2 : (⋃ H ∈ L₂.map Prod.fst, H) = K₂ := by
          ext z
          simp [hK₂]
        rwa [h2] at h1
      have hmemK₂ : ∀ p ∈ L₂, p.1 ⊆ K₂ := fun p hp z hz => mem_iUnion₂.mpr ⟨p, hp, hz⟩
      set G₂ : Set Y₂ := g₂ ⁻¹' ((Subtype.val : U₂ → Y₁) ⁻¹' G₁) ∩ K₂ with hG₂def
      have hG₂ : IsClosed G₂ := ((hG₁.preimage continuous_subtype_val).preimage hg₂.continuous).inter hK₂cl
      have hgood₂ : ∀ p ∈ L₂, IsLocGoodPart n E₂ G₂ p.1 p.2 := by
        intro p hp
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        exact (((hgood₁ p₁ hp₁).preimage hval₂).strictTransform hadm₂G hE₁U₂cl).inter (hmemK₂ _ hp)
      have hpair₂ : L₂.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G₂) := by
        rw [hL₂, List.pairwise_map]
        refine hpair'.imp_of_mem fun {p q} hp hq hpq z hz => ⟨?_, hmemK₂ _ (List.mem_map_of_mem hp) hz.1⟩
        have h1 := strictTransform_subset_preimage hg₂.continuous
          (((hgood₁ p hp).isClosed).preimage continuous_subtype_val) hz.1
        have h2 := strictTransform_subset_preimage hg₂.continuous
          (((hgood₁ q hq).isClosed).preimage continuous_subtype_val) hz.2
        have h3 := strictTransform_subset_preimage hg₁.continuous
          (((hgood' p hp).isClosed).preimage continuous_subtype_val) h1
        have h4 := strictTransform_subset_preimage hg₁.continuous
          (((hgood' q hq).isClosed).preimage continuous_subtype_val) h2
        exact hpq ⟨h3, h4⟩
      -- 3. the other parts, by induction, along `k₂`
      obtain ⟨Y₃, n1, n2, n3, h, E₃, hadm₃, hsnc₃, hres₃, hdisj₃⟩ :=
        ih E₂ hsnc₂ G₂ hG₂ L₂ (by simp [hL₂, hL']) hgood₂ hpair₂ k₂ hk₂ hKk₂
      have hh := hadm₃.isBlowupSequence.contMDiff
      have hg₁' := hadm₁'.isBlowupSequence.contMDiff
      have hg₂' := hadm₂'.isBlowupSequence.contMDiff
      -- the resolved first part misses the bad set of the last sequence
      set A₂ : Set Y₂ := strictTransform n g₂ ((Subtype.val : U₂ → Y₁) ⁻¹' A₁) with hA₂def
      have hA₂K₂ : Disjoint A₂ K₂ := by
        rw [disjoint_left]
        intro z hzA hzK
        obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hzK
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        exact disjoint_left.mp (hdisj₁' p₁ hp₁)
          (strictTransform_subset_preimage hg₂.continuous (hA₁.isClosed.preimage continuous_subtype_val) hzA)
          (strictTransform_subset_preimage hg₂.continuous
            ((hgood₁ p₁ hp₁).isClosed.preimage continuous_subtype_val) hzp)
      have hA₂G₂ : Disjoint (k₂ ⁻¹' A₂) (k₂ ⁻¹' G₂) := (hA₂K₂.mono_right inter_subset_right).preimage k₂
      have hexc₃ := IsAdmissibleBlowupSequence.exceptionalLocus_subset hadm₃
      -- admissibility of the composite
      have hadm₂'' : IsAdmissibleBlowupSequence n Y₁' (E₁.map (k₁ ⁻¹' ·)) (g₁' ⁻¹' (ι ⁻¹' G)) Y₂' g₂'
          (E₂.map (k₂ ⁻¹' ·)) := by
        refine hadm₂'.mono fun y hy => ?_
        simp only [mem_preimage] at hy ⊢
        rw [← hcomm₁]
        exact hy
      have hadm₃' : IsAdmissibleBlowupSequence n Y₂' (E₂.map (k₂ ⁻¹' ·)) (g₂' ⁻¹' (g₁' ⁻¹' (ι ⁻¹' G))) Y₃ h E₃ := by
        refine hadm₃.mono fun z hz => ?_
        have hz1 := hz.1
        simp only [mem_preimage] at hz1 ⊢
        rw [← hcomm₁, ← hcomm₂]
        exact hz1
      have hadm : IsAdmissibleBlowupSequence n B (E.map (ι ⁻¹' ·)) (ι ⁻¹' G) Y₃ (g₁' ∘ (g₂' ∘ h)) E₃ :=
        IsAdmissibleBlowupSequence.comp hadm₁' (IsAdmissibleBlowupSequence.comp hadm₂'' hadm₃')
      -- strict transforms of the composite
      have hST : ∀ S : Set X, strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' S) = strictTransform n h (k₂ ⁻¹' T S) := by
        intro S
        rw [StrictTransformComposition.strictTransform_comp hg₁' (hg₂'.comp hh),
          StrictTransformComposition.strictTransform_comp hg₂' hh, hST₁, hST₂]
      refine ⟨Y₃, n1, n2, n3, g₁' ∘ (g₂' ∘ h), E₃, hadm, hsnc₃, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · show (∀ x ∈ strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' A),
              RegularAtDim (n := n) (strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' A)) x d) ∧
            HasNormalCrossings n (strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' A)) E₃
          have hTA : T A = A₂ := rfl
          have hA₂cl : IsClosed (k₂ ⁻¹' A₂) := isClosed_closure.preimage hk₂.continuous
          have hpre : strictTransform n h (k₂ ⁻¹' A₂) = h ⁻¹' (k₂ ⁻¹' A₂) :=
            strictTransform_eq_preimage_of_disjoint hh.continuous hexc₃ hA₂cl hA₂G₂
          rw [hST, hTA, hpre]
          refine ⟨fun z hz => regularAtDim_preimage_of_disjoint hh hexc₃ hA₂G₂
            (hk₂.regularAtDim_preimage (hreg₂ (k₂ (h z)) hz)), ?_⟩
          have hE₂cl : ∀ H ∈ E₂.map (k₂ ⁻¹' ·), IsClosed H := fun H hH => by
            obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
            exact (hsnc₂.1 H₀ hH₀).preimage hk₂.continuous
          exact IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hadm₃ hE₂cl
            (hG₂.preimage hk₂.continuous) hA₂G₂ (hk₂.hasNormalCrossings_preimage hnc₂)
        · rw [hST]
          exact hres₃ _ (List.mem_map_of_mem hp')
      · rw [List.pairwise_cons]
        refine ⟨fun q hq => ?_, ?_⟩
        · show Disjoint (strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' A))
            (strictTransform n (g₁' ∘ (g₂' ∘ h)) (ι ⁻¹' q.1))
          rw [StrictTransformComposition.strictTransform_comp hg₁' (hg₂'.comp hh),
            StrictTransformComposition.strictTransform_comp hg₁' (hg₂'.comp hh), hST₁, hST₁]
          exact ((hdisj₁' q hq).preimage k₁ |>.preimage (g₂' ∘ h)).mono
            (strictTransform_subset_preimage (hg₂'.comp hh).continuous (isClosed_closure.preimage hk₁.continuous))
            (strictTransform_subset_preimage (hg₂'.comp hh).continuous (isClosed_closure.preimage hk₁.continuous))
        · have h' := hdisj₃
          rw [hL₂, List.pairwise_map] at h'
          refine h'.imp fun {p q} hpq => ?_
          rw [hST, hST]
          exact hpq

end Resolve

/-! ### Embedded resolution of an analytic set over an open set contained in a compact set -/

section Main

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The singular set restricts to open subsets**: a singular point of `W` in the open set `U` is a singular point of
`W ∩ U`. -/
theorem preimage_val_singularSet_subset {W : Set X} (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' singularSet (n := n) W ⊆ singularSet (n := n) ((Subtype.val : U → X) ⁻¹' W) := by
  intro x hx
  refine mem_singularSet_iff.mpr ⟨(mem_singularSet_iff.mp hx).1, fun k hk => ?_⟩
  exact (mem_singularSet_iff.mp hx).2 k (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk)

/-- **Embedded resolution of an arbitrary analytic set over an open set contained in a compact set, relative to a simple
normal crossings boundary, by one admissible sequence** (Hironaka; `hir:embedded-resolution-analytic-local`): let `X` be any
complex manifold, `W ⊆ X` an analytic set with empty interior (its components may have different dimensions, `W` need not be
compact), `E₀` a divisor with simple normal crossings no member of which contains a nonempty relatively open subset of `W`, and
`X₀ ⊆ X` an open set contained in a compact set.  Put `F = W_sing ∪ (W ∩ |E₀|)`.  There are an admissible blowup sequence
`f : X₀' → X₀` of `(X₀, E₀|X₀)` with centres over `F ∩ X₀` and its divisor `E` such that `E` has simple normal crossings,
`Exc f ⊆ ⋃ (new members) ⊆ f⁻¹(F ∩ X₀)`, `f⁻¹(W_sing ∩ X₀) ⊆ Exc f`, `f` is an isomorphism over `X₀ \ F`, the strict transform
`W'` of `W ∩ X₀` is a closed submanifold of `X₀'` which is the union of the strict transforms of the `W⁽ᵏ⁾ ∩ X₀` (`k < n`),
these are pairwise disjoint, `W'` has dimension `k` at each point of the strict transform of `W⁽ᵏ⁾ ∩ X₀`, and `W'` has only
normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_boundary_of_subset_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) (X₀ : Opens X) {K : Set X} (hK : IsCompact K)
    (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' singularSet (n := n) W) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  set G : Set X := singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H with hGdef
  have hGcl : IsClosed G := (isClosed_singularSet hWa.isClosed).union
    (hWa.isClosed.inter (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1))
  set L : List (Set X × ℕ) := (List.range n).map fun k => (dimensionPart (n := n) W k, k) with hL
  have hgood : ∀ p ∈ L, IsLocGoodPart n E₀ G p.1 p.2 := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨isComplexAnalyticSubset_dimensionPart hWa k, List.mem_range.mp hk,
      (diff_regularLocus_dimensionPart_subset_singularSet hWa.isClosed k).trans subset_union_left,
      fun x hx => Or.inr ⟨dimensionPart_subset hWa.isClosed k hx.1, hx.2⟩, dimensionPart_subset_closure_diff hE₀W k⟩
  have hpair : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) := by
    rw [hL, List.pairwise_map]
    exact List.nodup_range.imp fun {k j} hkj =>
      (inter_dimensionPart_subset_singularSet hWa.isClosed hkj).trans subset_union_left
  have hval := isOpenHoloEmbedding_val (n := n) X₀
  obtain ⟨X', i1, i2, i3, f, E, hadm, hsnc, hres, hdisj⟩ :=
    exists_resolution_list_local L.length E₀ hE₀ G hGcl L rfl hgood hpair (Subtype.val : X₀ → X) hval
      ⟨K, hK, by rwa [Subtype.range_coe]⟩
  have hf := hadm.isBlowupSequence.contMDiff
  set V : Set X₀ := (Subtype.val : X₀ → X) ⁻¹' W with hVdef
  set P : ℕ → Set X₀ := fun k => (Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k with hPdef
  have hVcl : IsClosed V := hWa.isClosed.preimage continuous_subtype_val
  have hempty : ∀ k : ℕ, ¬ k < n → strictTransform n f (P k) = ∅ := fun k hk => by
    simp only [hPdef]
    rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk), preimage_empty, strictTransform_empty]
  have hresk : ∀ k < n, (∀ x ∈ strictTransform n f (P k), RegularAtDim (n := n) (strictTransform n f (P k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (P k)) E := fun k hk =>
    hres _ (List.mem_map_of_mem (List.mem_range.mpr hk))
  have hdisjk : ∀ k j : ℕ, k ≠ j → Disjoint (strictTransform n f (P k)) (strictTransform n f (P j)) := by
    intro k j hkj
    by_cases hk : k < n
    · by_cases hj : j < n
      · have h : (List.range n).Pairwise (fun k j => Disjoint (strictTransform n f (P k))
            (strictTransform n f (P j))) := by
          have h' := hdisj
          rw [hL, List.pairwise_map] at h'
          exact h'
        have : Std.Symm (fun k j : ℕ => Disjoint (strictTransform n f (P k)) (strictTransform n f (P j))) :=
          ⟨fun _ _ h' => h'.symm⟩
        exact h.forall (List.mem_range.mpr hk) (List.mem_range.mpr hj) hkj
      · rw [hempty j hj]
        exact disjoint_empty _
    · rw [hempty k hk]
      exact empty_disjoint _
  have hSTeq : strictTransform n f V = ⋃ k : Fin n, strictTransform n f (P k) := by
    have hV : V = ⋃ k : Fin n, P k := by
      simp only [hVdef, hPdef]
      conv_lhs => rw [eq_iUnion_dimensionPart_fin hWa hint]
      rw [preimage_iUnion]
    rw [hV, strictTransform, preimage_iUnion, iUnion_sdiff, closure_iUnion_of_finite]
    rfl
  -- near a point of the strict transform of `P k`, the strict transform of `V` is that of `P k`
  have hloc : ∀ k : ℕ, ∀ x ∈ strictTransform n f (P k), ∃ O : Set X', IsOpen O ∧ x ∈ O ∧
      strictTransform n f V ∩ O = strictTransform n f (P k) ∩ O := by
    intro k x hx
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hx
      exact hx
    set S : Set (Fin n) := {j | (j : ℕ) ≠ k} with hSdef
    refine ⟨(⋃ j ∈ S, strictTransform n f (P j))ᶜ,
      (S.toFinite.isClosed_biUnion fun j _ => isClosed_closure).isOpen_compl, ?_, ?_⟩
    · simp only [mem_compl_iff, mem_iUnion, not_exists]
      intro j hj hxj
      exact disjoint_left.mp (hdisjk k j (Ne.symm hj)) hx hxj
    · ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, not_exists]
      refine ⟨fun ⟨hyW, hyO⟩ => ⟨?_, hyO⟩, fun ⟨hyk, hyO⟩ => ⟨?_, hyO⟩⟩
      · rw [hSTeq] at hyW
        obtain ⟨j, hj⟩ := mem_iUnion.mp hyW
        by_cases hjk : (j : ℕ) = k
        · rw [← hjk]
          exact hj
        · exact absurd hj (hyO j hjk)
      · rw [hSTeq]
        exact mem_iUnion.mpr ⟨⟨k, hk⟩, hyk⟩
  have hreg : ∀ k : ℕ, ∀ x ∈ strictTransform n f (P k), RegularAtDim (n := n) (strictTransform n f V) x k := by
    intro k x hx
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hx
      exact hx
    obtain ⟨O, hO, hxO, hOeq⟩ := hloc k x hx
    exact RegularPointDimension.regularAtDim_of_inter_eq hO hxO hOeq.symm ((hresk k hk).1 x hx)
  have hsub : IsClosedSubmanifold n (strictTransform n f V) := by
    refine ⟨isClosed_closure, fun x hx => ?_⟩
    rw [hSTeq] at hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact ⟨j, hreg j x hj⟩
  have hnc : HasNormalCrossings n (strictTransform n f V) E := by
    refine CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx => ?_
    have hx' := hx
    rw [hSTeq] at hx'
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
    obtain ⟨O, hO, hxO, hOeq⟩ := hloc j x hj
    refine ⟨strictTransform n f (P j), hj, ?_, (hresk j j.2).2⟩
    filter_upwards [hO.mem_nhds hxO] with y hyO
    constructor
    · intro hy
      have h' : y ∈ strictTransform n f V ∩ O := ⟨hy, hyO⟩
      rw [hOeq] at h'
      exact h'.1
    · intro hy
      have h' : y ∈ strictTransform n f (P j) ∩ O := ⟨hy, hyO⟩
      rw [← hOeq] at h'
      exact h'.1
  obtain ⟨hexc, hnew⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadm
  rw [List.length_map] at hexc hnew
  have hsing : f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' singularSet (n := n) W) ⊆ exceptionalLocus n f :=
    (preimage_mono (preimage_val_singularSet_subset X₀)).trans
      (preimage_singularSet_subset_exceptionalLocus hf hVcl hsub)
  exact ⟨X', i1, i2, i3, f, E, hadm, hsnc, hexc, hnew, hsing,
    IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadm, hsub, hSTeq, hreg, hdisjk, hnc⟩

/-- **Embedded resolution of an arbitrary analytic set over an open set contained in a compact set, by one admissible
sequence** (Hironaka; `hir:embedded-resolution-analytic-local`): let `X` be any complex manifold, `W ⊆ X` an analytic set with
empty interior (components of any dimensions, `W` not necessarily compact) and `X₀ ⊆ X` an open set contained in a compact set.
There are an admissible blowup sequence `f : X₀' → X₀` (from the empty divisor, centres over `W_sing ∩ X₀`) and its divisor `E`
such that `E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing ∩ X₀)`, `f` is an isomorphism over `X₀ \ W_sing`, the
strict transform `W'` of `W ∩ X₀` is a closed submanifold of `X₀'` which is the union of the pairwise disjoint strict transforms
of the `W⁽ᵏ⁾ ∩ X₀` (`k < n`), of dimension `k` at each point of the strict transform of `W⁽ᵏ⁾ ∩ X₀`, and `W'` has only normal
crossings with `E`. -/
theorem exists_embeddedResolution_analytic_of_subset_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' singularSet (n := n) W) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' singularSet (n := n) W) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  obtain ⟨X', i1, i2, i3, f, E, hadm, hsnc, hexc, hnew, hsing, hiso, hsub, hSTeq, hreg, hdisj, hnc⟩ :=
    exists_embeddedResolution_analytic_boundary_of_subset_isCompact hWa hint (E₀ := []) isSNCDivisor_nil
      (HironakaEmbeddedBoundary.subset_closure_diff_biUnion_of_forall_disjoint (by simp)) X₀ hK hX₀
  have hG : singularSet (n := n) W ∪ W ∩ ⋃ H ∈ ([] : List (Set X)), H = singularSet (n := n) W := by simp
  rw [hG] at hadm hnew hiso
  simp only [List.length_nil, List.drop_zero, List.map_nil] at hexc hnew hadm
  exact ⟨X', i1, i2, i3, f, E, hadm, hsnc, Subset.antisymm hexc (hnew.trans hsing),
    Subset.antisymm hnew (hsing.trans hexc), hiso, hsub, hSTeq, hreg, hdisj, hnc⟩

/-- **Local embedded resolution of an arbitrary analytic set** (`hir:embedded-resolution-analytic-local`): for a compact
`K ⊆ X`, a relatively compact open neighbourhood `U` of `K` and the conclusion of
`exists_embeddedResolution_analytic_of_subset_isCompact` over `U`. -/
theorem exists_embeddedResolution_analytic_local {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U [] ((Subtype.val : U → X) ⁻¹' singularSet (n := n) W) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularSet (n := n) W) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : U → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc, exists_embeddedResolution_analytic_of_subset_isCompact hWa hint ⟨U, hUo⟩ hUc subset_closure⟩

/-- **Local embedded resolution of an arbitrary analytic set relative to a simple normal crossings boundary**
(`hir:embedded-resolution-analytic-local`): for a compact `K ⊆ X`, a relatively compact open neighbourhood `U` of `K` and the
conclusion of `exists_embeddedResolution_analytic_boundary_of_subset_isCompact` over `U`. -/
theorem exists_embeddedResolution_analytic_boundary_local {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
      IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
        ((Subtype.val : U → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)) U' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : U → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularSet (n := n) W) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
      strictTransform n f ((Subtype.val : U → X) ⁻¹' W) =
        ⋃ k : Fin n, strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W k))
          (strictTransform n f ((Subtype.val : U → X) ⁻¹' dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc,
    exists_embeddedResolution_analytic_boundary_of_subset_isCompact hWa hint hE₀ hE₀W ⟨U, hUo⟩ hUc subset_closure⟩

end Main

end

end Hironaka.HironakaEmbeddedAnalyticLocal
