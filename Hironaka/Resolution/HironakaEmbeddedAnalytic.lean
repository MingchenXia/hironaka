/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSeparation
import Hironaka.Resolution.HironakaEmbeddedDimensionParts
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaEmbeddedExceptional
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution of an arbitrary analytic set by one blowup sequence (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6 (embedded desingularization of any
closed subspace: the final strict transform is smooth and has simultaneous normal crossings with the exceptional
divisor; `E' = σ⁻¹(Sing X)` and `E'` is the critical locus of `σ`); Włodarczyk 2005 (`wlodarczyk05-hironaka`);
Kollár 2007 (`kollar07-resolution`), "Principalization III".

**Statement.**  Let `X` be a complex manifold and `W ⊆ X` a compact analytic set with empty interior; its components may have
different dimensions.  Write `W⁽ᵏ⁾ = closure (Reg_k W)` for its `k`-dimensional part
(`HironakaEmbeddedDimensionParts.dimensionPart`) and `W_sing` for the set of points at which `W` is not a submanifold of any
dimension (`singularSet`).  There is ONE admissible blowup sequence `f : X' → X` (from the empty divisor, centres over `W_sing`)
with divisor `E` such that

* `E` has simple normal crossings, and `Exc f = ⋃ E = f⁻¹(W_sing)`; `f` is an isomorphism over `X \ W_sing`;
* the strict transform `W'` of `W` is a closed submanifold of `X'`; it is the union of the strict transforms of the parts `W⁽ᵏ⁾`,
  which are pairwise disjoint, and `W'` has dimension `k` at each point of the strict transform of `W⁽ᵏ⁾`;
* `W'` has only normal crossings with `E`.

The same holds relative to a divisor `E₀` with simple normal crossings no member of which contains a nonempty relatively open
subset of `W`, with centres over `F = W_sing ∪ (W ∩ |E₀|)`, `Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F`, `f⁻¹(W_sing) ⊆ Exc f`, and `f` an
isomorphism over `X \ F`.

**Route.**  Separation first, then resolution, by induction on a list of parts `(A, d)` relative to a divisor `E` and a closed
"bad" set `G` (`IsGoodPart`: `A` compact analytic, `d < n`, the singular points of `A` (for dimension `d`) and the points of `A` on
`|E|` lie in `G`, and `A \ G` is dense in `A`; distinct parts meet only in `G`):

1. **Separation** (`exists_sepOne`): the first part `A` is separated from each later part `B` in turn by principalizing
   `𝓘_A + 𝓘_B` relative to the current divisor (`HironakaSeparation.exists_separation`), with centres over `A ∩ B ⊆ G`; strict
   transforms keep the hypotheses (`IsGoodPart.strictTransform`, from `HironakaAdmissibleCalculus`), and disjointness, once
   obtained, persists (strict transforms lie in preimages).
2. **Resolution of the first part**: embedded resolution relative to the accumulated divisor
   (`HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact`), with centres over the singular points of `A` and
   its points on the divisor, all in `A` and so disjoint from the other parts.
3. **The other parts** are resolved by induction, with the bad set cut down to the union of their strict transforms, which is
   disjoint from the resolved first part; so the later sequence is an isomorphism near it, its strict transform is its preimage,
   still smooth of dimension `d`, and normal crossings with the divisor are carried along
   (`HironakaAdmissibleCalculus.hasNormalCrossings_preimage_of_disjoint`).

The parts of `W` are `(W⁽ᵏ⁾, k)` for `k < n` (`W⁽ⁿ⁾ = ∅` as `W` has empty interior), with `G = W_sing ∪ (W ∩ |E₀|)`: two parts
meet only in `W_sing`, and the singular points of `W⁽ᵏ⁾` lie in `W_sing`.  Finally `f⁻¹(W_sing) ⊆ Exc f` because the strict
transform is a submanifold at every point (the argument of `HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus`).

**What is not claimed.**  Condition (1) of BM97 Theorem 1.6 (`C_j ⊂ Sing X_j` or `X_j` smooth and `C_j ⊂ X_j ∩ E_j`): the centres
lie over `W_sing` (resp. `F`), not inside the singular locus of the current strict transform.  With a boundary, `f` may blow up
smooth points of `W` on `|E₀|` at which `W` already has normal crossings with `E₀`.  Only compact `W` (or compact `X`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedAnalytic

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence Hironaka.HironakaAdmissibleCalculus Hironaka.HironakaEmbeddedDimensionParts

noncomputable section

variable {n : ℕ}

/-! ### Good parts -/

section Parts

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

variable (n) in
/-- **A good part `(A, d)` relative to a divisor `E` and a bad set `G`**: `A` is a compact analytic set, `d < n`, the points of
`A` at which it is not a submanifold of dimension `d` and the points of `A` on `|E|` lie in `G`, and `A \ G` is dense in `A`. -/
def IsGoodPart (E : List (Set X)) (G A : Set X) (d : ℕ) : Prop :=
  IsComplexAnalyticSubset (n := n) A ∧ IsCompact A ∧ d < n ∧ A \ regularLocus (n := n) A d ⊆ G ∧
    A ∩ (⋃ H ∈ E, H) ⊆ G ∧ A ⊆ closure (A \ G)

namespace IsGoodPart

variable {E : List (Set X)} {G A : Set X} {d : ℕ}

theorem isClosed (h : IsGoodPart n E G A d) : IsClosed A := h.1.isClosed

/-- A good part is of pure dimension `d`. -/
theorem pure (h : IsGoodPart n E G A d) : A ⊆ closure (regularLocus (n := n) A d) := by
  refine h.2.2.2.2.2.trans (closure_mono fun x hx => ?_)
  by_contra hreg
  exact hx.2 (h.2.2.2.1 ⟨hx.1, hreg⟩)

/-- A good part has empty interior. -/
theorem interior_eq_empty (h : IsGoodPart n E G A d) : interior A = ∅ :=
  HironakaEmbeddedReducible.interior_eq_empty_of_pure h.2.2.1 h.pure

/-- No member of `E` contains a nonempty relatively open subset of a good part. -/
theorem subset_closure_diff_biUnion (h : IsGoodPart n E G A d) : A ⊆ closure (A \ ⋃ H ∈ E, H) :=
  h.2.2.2.2.2.trans (closure_mono fun _ hx => ⟨hx.1, fun hxE => hx.2 (h.2.2.2.2.1 ⟨hx.1, hxE⟩)⟩)

/-- A good part off the bad set is dense in it. -/
theorem subset_closure_diff_of_inter_subset (h : IsGoodPart n E G A d) {B : Set X} (hB : A ∩ B ⊆ G) :
    A ⊆ closure (A \ B) :=
  h.2.2.2.2.2.trans (closure_mono fun _ hx => ⟨hx.1, fun hxB => hx.2 (hB ⟨hx.1, hxB⟩)⟩)

/-- **Cutting down the bad set** to its intersection with a closed set containing the part. -/
theorem inter (h : IsGoodPart n E G A d) {K : Set X} (hAK : A ⊆ K) : IsGoodPart n E (G ∩ K) A d := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx => ⟨h.2.2.2.1 hx, hAK hx.1⟩, fun x hx => ⟨h.2.2.2.2.1 hx, hAK hx.1⟩,
    h.2.2.2.2.2.trans (closure_mono fun x hx => ⟨hx.1, fun hxG => hx.2 hxG.1⟩)⟩

/-- **Good parts are carried along an admissible sequence**: if `f` is an admissible sequence of `(X, E)` with centres over the
closed set `G` (members of `E` closed), the strict transform of a good part is a good part relative to the accumulated divisor
and `f⁻¹ G`. -/
theorem strictTransform {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} {E' : List (Set Y)} (hf : IsAdmissibleBlowupSequence n X E G Y f E') (hE : ∀ H ∈ E, IsClosed H)
    (h : IsGoodPart n E G A d) : IsGoodPart n E' (f ⁻¹' G) (strictTransform n f A) d := by
  have hfc := hf.isBlowupSequence.contMDiff
  refine ⟨isComplexAnalyticSubset_strictTransform hf.isBlowupSequence h.1,
    isCompact_strictTransform hf.isBlowupSequence h.2.1, h.2.2.1,
    diff_regularLocus_strictTransform_subset hfc (IsAdmissibleBlowupSequence.exceptionalLocus_subset hf) h.isClosed
      h.2.2.2.1, fun z hz => ?_, strictTransform_subset_closure_diff hfc h.isClosed h.2.2.2.2.2⟩
  have hzA : f z ∈ A := strictTransform_subset_preimage hfc.continuous h.isClosed hz.1
  rcases IsAdmissibleBlowupSequence.biUnion_subset hf hE hz.2 with h1 | h1
  · exact h.2.2.2.2.1 ⟨hzA, h1⟩
  · exact h1

end IsGoodPart

end Parts

/-! ### Separation of one part from the others -/

section Separate

/-- **Separating one good part from finitely many others**: by successive principalizations of `𝓘_A + 𝓘_B`, an admissible
sequence of `(X, E)` with centres over `G` after which the strict transform of `A` misses the strict transform of each other
part. -/
theorem exists_sepOne (m : ℕ) : ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (E : List (Set X)) (_hE : IsSNCDivisor n E) (G : Set X) (_hG : IsClosed G)
    (A : Set X) (d : ℕ) (_hA : IsGoodPart n E G A d) (L : List (Set X × ℕ)), L.length = m →
    (∀ p ∈ L, IsGoodPart n E G p.1 p.2) → (∀ p ∈ L, A ∩ p.1 ⊆ G) →
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E' : List (Set X')),
      IsAdmissibleBlowupSequence n X E G X' f E' ∧ IsSNCDivisor n E' ∧
      ∀ p ∈ L, Disjoint (strictTransform n f A) (strictTransform n f p.1) := by
  induction m with
  | zero =>
      intro X _ _ _ E hE G _ A d _ L hL _ _
      rw [List.length_eq_zero_iff.mp hL]
      exact ⟨X, inferInstance, inferInstance, inferInstance, id, E, IsAdmissibleBlowupSequence.refl, hE,
        fun p hp => absurd hp List.not_mem_nil⟩
  | succ m ih =>
      intro X _ _ _ E hE G hG A d hA L hL hgood hsep
      obtain ⟨q, L', rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = m := by simpa using hL
      have hq := hgood q (List.mem_cons_self ..)
      have hAq : A ∩ q.1 ⊆ G := hsep q (List.mem_cons_self ..)
      obtain ⟨X₁, i1, i2, i3, f₁, E₁, hadm₁, hsnc₁, hdisj₁⟩ := HironakaSeparation.exists_separation hA.1 hq.1
        hA.interior_eq_empty (hA.2.1.inter_right hq.isClosed) (hA.subset_closure_diff_of_inter_subset hAq)
        (hq.subset_closure_diff_of_inter_subset (by rw [inter_comm]; exact hAq)) hE
      have hadm₁' : IsAdmissibleBlowupSequence n X E G X₁ f₁ E₁ := hadm₁.mono hAq
      have hEcl : ∀ H ∈ E, IsClosed H := hE.1
      have hf₁ := hadm₁'.isBlowupSequence.contMDiff
      set L₁ : List (Set X₁ × ℕ) := L'.map fun p => (strictTransform n f₁ p.1, p.2) with hL₁
      obtain ⟨X₂, j1, j2, j3, f₂, E₂, hadm₂, hsnc₂, hdisj₂⟩ := ih E₁ hsnc₁ (f₁ ⁻¹' G)
        (hG.preimage hf₁.continuous) (strictTransform n f₁ A) d (hA.strictTransform hadm₁' hEcl) L₁
        (by simp [hL₁, hL'])
        (by
          intro p hp
          obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          exact (hgood p₀ (List.mem_cons_of_mem _ hp₀)).strictTransform hadm₁' hEcl)
        (by
          intro p hp
          obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
          intro z hz
          exact hsep p₀ (List.mem_cons_of_mem _ hp₀)
            ⟨strictTransform_subset_preimage hf₁.continuous hA.isClosed hz.1,
              strictTransform_subset_preimage hf₁.continuous (hgood p₀ (List.mem_cons_of_mem _ hp₀)).isClosed hz.2⟩)
      have hf₂ := hadm₂.isBlowupSequence.contMDiff
      refine ⟨X₂, j1, j2, j3, f₁ ∘ f₂, E₂, IsAdmissibleBlowupSequence.comp hadm₁' hadm₂, hsnc₂, ?_⟩
      intro p hp
      rw [StrictTransformComposition.strictTransform_comp hf₁ hf₂, StrictTransformComposition.strictTransform_comp hf₁ hf₂]
      rcases List.mem_cons.mp hp with rfl | hp'
      · refine Disjoint.mono (strictTransform_subset_preimage hf₂.continuous isClosed_closure)
          (strictTransform_subset_preimage hf₂.continuous isClosed_closure) ?_
        exact hdisj₁.preimage f₂
      · exact hdisj₂ _ (List.mem_map_of_mem hp')

end Separate

/-! ### Separation and resolution of a list of good parts -/

section Resolve

/-- **Embedded resolution of a list of good parts** (the induction): for a divisor `E` with simple normal crossings, a closed
bad set `G` and a list of good parts meeting pairwise only in `G`, there is an admissible sequence of `(X, E)` with centres over
`G`, with a divisor with simple normal crossings, after which the strict transform of each part `(A, d)` is regular of dimension
`d` at each of its points and has only normal crossings with the divisor, and the strict transforms are pairwise disjoint. -/
theorem exists_resolution_list (m : ℕ) : ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (E : List (Set X)) (_hE : IsSNCDivisor n E) (G : Set X) (_hG : IsClosed G)
    (L : List (Set X × ℕ)), L.length = m → (∀ p ∈ L, IsGoodPart n E G p.1 p.2) →
    L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) →
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E' : List (Set X')),
      IsAdmissibleBlowupSequence n X E G X' f E' ∧ IsSNCDivisor n E' ∧
      (∀ p ∈ L, (∀ x ∈ strictTransform n f p.1, RegularAtDim (n := n) (strictTransform n f p.1) x p.2) ∧
        HasNormalCrossings n (strictTransform n f p.1) E') ∧
      L.Pairwise (fun p q => Disjoint (strictTransform n f p.1) (strictTransform n f q.1)) := by
  induction m with
  | zero =>
      intro X _ _ _ E hE G _ L hL _ _
      rw [List.length_eq_zero_iff.mp hL]
      exact ⟨X, inferInstance, inferInstance, inferInstance, id, E, IsAdmissibleBlowupSequence.refl, hE,
        fun p hp => absurd hp List.not_mem_nil, List.Pairwise.nil⟩
  | succ m ih =>
      intro X _ _ _ E hE G hG L hL hgood hpair
      obtain ⟨⟨A, d⟩, L', rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = m := by simpa using hL
      rw [List.pairwise_cons] at hpair
      obtain ⟨hAsep, hpair'⟩ := hpair
      have hA : IsGoodPart n E G A d := hgood (A, d) (List.mem_cons_self ..)
      have hgood' : ∀ p ∈ L', IsGoodPart n E G p.1 p.2 := fun p hp => hgood p (List.mem_cons_of_mem _ hp)
      have hEcl : ∀ H ∈ E, IsClosed H := hE.1
      -- 1. separate `A` from the other parts
      obtain ⟨X₁, i1, i2, i3, f₁, E₁, hadm₁, hsnc₁, hdisj₁⟩ :=
        exists_sepOne L'.length E hE G hG A d hA L' rfl hgood' hAsep
      have hf₁ := hadm₁.isBlowupSequence.contMDiff
      have hG₁ : IsClosed (f₁ ⁻¹' G) := hG.preimage hf₁.continuous
      have hE₁cl : ∀ H ∈ E₁, IsClosed H := hsnc₁.1
      set A₁ := strictTransform n f₁ A with hA₁def
      have hA₁ : IsGoodPart n E₁ (f₁ ⁻¹' G) A₁ d := hA.strictTransform hadm₁ hEcl
      set L₁ : List (Set X₁ × ℕ) := L'.map fun p => (strictTransform n f₁ p.1, p.2) with hL₁
      have hgood₁ : ∀ p ∈ L₁, IsGoodPart n E₁ (f₁ ⁻¹' G) p.1 p.2 := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        exact (hgood' p₀ hp₀).strictTransform hadm₁ hEcl
      have hdisj₁' : ∀ p ∈ L₁, Disjoint A₁ p.1 := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        exact hdisj₁ p₀ hp₀
      have hpair₁ : L₁.Pairwise (fun p q => p.1 ∩ q.1 ⊆ f₁ ⁻¹' G) := by
        rw [hL₁, List.pairwise_map]
        refine hpair'.imp_of_mem fun {p q} hp hq hpq z hz => hpq ?_
        exact ⟨strictTransform_subset_preimage hf₁.continuous (hgood' p hp).isClosed hz.1,
          strictTransform_subset_preimage hf₁.continuous (hgood' q hq).isClosed hz.2⟩
      -- 2. resolve `A₁` relative to `E₁`
      obtain ⟨X₂, j1, j2, j3, f₂, E₂, hadm₂, hsnc₂, -, -, -, -, -, hreg₂, hnc₂⟩ :=
        HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact hA₁.1 hA₁.2.1 hA₁.2.2.1 hA₁.pure
          hsnc₁ hA₁.subset_closure_diff_biUnion
      have hF₂ : A₁ \ regularLocus (n := n) A₁ d ∪ A₁ ∩ ⋃ H ∈ E₁, H ⊆ f₁ ⁻¹' G :=
        union_subset hA₁.2.2.2.1 hA₁.2.2.2.2.1
      have hadm₂' : IsAdmissibleBlowupSequence n X₁ E₁ (f₁ ⁻¹' G) X₂ f₂ E₂ := hadm₂.mono hF₂
      have hf₂ := hadm₂.isBlowupSequence.contMDiff
      -- 3. the other parts, with the bad set cut down to their strict transforms
      set L₂ : List (Set X₂ × ℕ) := L₁.map fun p => (strictTransform n f₂ p.1, p.2) with hL₂
      set K₂ : Set X₂ := ⋃ H ∈ L₂.map Prod.fst, H with hK₂
      have hK₂cl : IsClosed K₂ := by
        refine HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed fun H hH => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hH
        obtain ⟨p₁, -, rfl⟩ := List.mem_map.mp hp
        exact isClosed_closure
      have hmemK₂ : ∀ p ∈ L₂, p.1 ⊆ K₂ := fun p hp z hz =>
        mem_iUnion₂.mpr ⟨p.1, List.mem_map_of_mem hp, hz⟩
      set G₂ : Set X₂ := f₂ ⁻¹' (f₁ ⁻¹' G) ∩ K₂ with hG₂def
      have hG₂ : IsClosed G₂ := (hG₁.preimage hf₂.continuous).inter hK₂cl
      have hgood₂ : ∀ p ∈ L₂, IsGoodPart n E₂ G₂ p.1 p.2 := by
        intro p hp
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        exact ((hgood₁ p₁ hp₁).strictTransform hadm₂' hE₁cl).inter (hmemK₂ _ hp)
      have hpair₂ : L₂.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G₂) := by
        rw [hL₂, List.pairwise_map]
        refine hpair₁.imp_of_mem fun {p q} hp hq hpq z hz =>
          ⟨hpq ⟨strictTransform_subset_preimage hf₂.continuous (hgood₁ p hp).isClosed hz.1,
            strictTransform_subset_preimage hf₂.continuous (hgood₁ q hq).isClosed hz.2⟩,
            hmemK₂ _ (List.mem_map_of_mem hp) hz.1⟩
      obtain ⟨X₃, k1, k2, k3, f₃, E₃, hadm₃, hsnc₃, hres₃, hdisj₃⟩ :=
        ih E₂ hsnc₂ G₂ hG₂ L₂ (by simp [hL₂, hL₁, hL']) hgood₂ hpair₂
      have hf₃ := hadm₃.isBlowupSequence.contMDiff
      -- the resolved first part misses the bad set of the later sequence
      set A₂ := strictTransform n f₂ A₁ with hA₂def
      have hA₂K₂ : Disjoint A₂ K₂ := by
        rw [disjoint_left]
        intro z hzA hzK
        obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hzK
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hH
        obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hp
        exact disjoint_left.mp (hdisj₁' p₁ hp₁) (strictTransform_subset_preimage hf₂.continuous hA₁.isClosed hzA)
          (strictTransform_subset_preimage hf₂.continuous (hgood₁ p₁ hp₁).isClosed hzH)
      have hA₂G₂ : Disjoint A₂ G₂ := hA₂K₂.mono_right inter_subset_right
      have hexc₃ := IsAdmissibleBlowupSequence.exceptionalLocus_subset hadm₃
      have hadm₃' : IsAdmissibleBlowupSequence n X₂ E₂ (f₂ ⁻¹' (f₁ ⁻¹' G)) X₃ f₃ E₃ := hadm₃.mono inter_subset_left
      have hST : ∀ B : Set X, strictTransform n (f₁ ∘ (f₂ ∘ f₃)) B =
          strictTransform n f₃ (strictTransform n f₂ (strictTransform n f₁ B)) := fun B => by
        rw [StrictTransformComposition.strictTransform_comp hf₁ (hf₂.comp hf₃),
          StrictTransformComposition.strictTransform_comp hf₂ hf₃]
      refine ⟨X₃, k1, k2, k3, f₁ ∘ (f₂ ∘ f₃), E₃,
        IsAdmissibleBlowupSequence.comp hadm₁ (IsAdmissibleBlowupSequence.comp hadm₂' hadm₃'), hsnc₃, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · show (∀ x ∈ strictTransform n (f₁ ∘ (f₂ ∘ f₃)) A,
              RegularAtDim (n := n) (strictTransform n (f₁ ∘ (f₂ ∘ f₃)) A) x d) ∧
            HasNormalCrossings n (strictTransform n (f₁ ∘ (f₂ ∘ f₃)) A) E₃
          have hpre : strictTransform n f₃ (strictTransform n f₂ (strictTransform n f₁ A)) =
              f₃ ⁻¹' strictTransform n f₂ (strictTransform n f₁ A) :=
            strictTransform_eq_preimage_of_disjoint hf₃.continuous hexc₃ isClosed_closure hA₂G₂
          rw [hST, hpre]
          exact ⟨fun z hz => regularAtDim_preimage_of_disjoint hf₃ hexc₃ hA₂G₂ (hreg₂ (f₃ z) hz),
            IsAdmissibleBlowupSequence.hasNormalCrossings_preimage_of_disjoint hadm₃ hsnc₂.1 hG₂ hA₂G₂ hnc₂⟩
        · rw [hST]
          exact hres₃ _ (List.mem_map_of_mem (List.mem_map_of_mem hp'))
      · rw [List.pairwise_cons]
        refine ⟨fun q hq => ?_, ?_⟩
        · show Disjoint (strictTransform n (f₁ ∘ (f₂ ∘ f₃)) A) (strictTransform n (f₁ ∘ (f₂ ∘ f₃)) q.1)
          rw [StrictTransformComposition.strictTransform_comp hf₁ (hf₂.comp hf₃),
            StrictTransformComposition.strictTransform_comp hf₁ (hf₂.comp hf₃)]
          exact ((hdisj₁ q hq).preimage (f₂ ∘ f₃)).mono
            (strictTransform_subset_preimage (hf₂.comp hf₃).continuous isClosed_closure)
            (strictTransform_subset_preimage (hf₂.comp hf₃).continuous isClosed_closure)
        · have h := hdisj₃
          rw [hL₂, hL₁, List.pairwise_map, List.pairwise_map] at h
          refine h.imp fun {p q} hpq => ?_
          rw [hST, hST]
          exact hpq

end Resolve

/-! ### Analytic sets: the singular set and the dimension parts -/

section Analytic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The singular set of `W`**: the points of `W` at which `W` is not a submanifold, of any dimension. -/
def singularSet (W : Set M) : Set M :=
  W \ ⋃ k : ℕ, regularLocus (n := n) W k

theorem mem_singularSet_iff {W : Set M} {x : M} :
    x ∈ singularSet (n := n) W ↔ x ∈ W ∧ ∀ k, ¬ RegularAtDim (n := n) W x k := by
  simp [singularSet]

/-- **The singular set of a closed set is closed**: near a regular point all points of `W` are regular. -/
theorem isClosed_singularSet {W : Set M} (hW : IsClosed W) : IsClosed (singularSet (n := n) W) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxW : x ∈ W
  · obtain ⟨k, hk⟩ : ∃ k, RegularAtDim (n := n) W x k := by
      by_contra h
      push Not at h
      exact hx (mem_singularSet_iff.mpr ⟨hxW, h⟩)
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hk] with y hy hys
    exact (mem_singularSet_iff.mp hys).2 k (hy (mem_singularSet_iff.mp hys).1)
  · filter_upwards [hW.isOpen_compl.mem_nhds hxW] with y hy hys
    exact hy (mem_singularSet_iff.mp hys).1

/-- **A regular point of `W` of dimension `k` lies in no other dimension part.** -/
theorem notMem_dimensionPart_of_regularAtDim {W : Set M} {x : M} {k j : ℕ} (hx : RegularAtDim (n := n) W x k)
    (hkj : k ≠ j) : x ∉ dimensionPart (n := n) W j := by
  intro hxj
  obtain ⟨y, hy, hyj⟩ := mem_closure_iff_nhds.mp hxj _ (RegularPatchNeighborhood.eventually_regularAtDim hx)
  exact hkj (RegularPointDimension.eq_of_regularAtDim (hy hyj.2.1) hyj)

/-- **Two dimension parts meet only in the singular set.** -/
theorem inter_dimensionPart_subset_singularSet {W : Set M} (hW : IsClosed W) {k j : ℕ} (hkj : k ≠ j) :
    dimensionPart (n := n) W k ∩ dimensionPart (n := n) W j ⊆ singularSet (n := n) W := by
  rintro x ⟨hxk, hxj⟩
  refine mem_singularSet_iff.mpr ⟨dimensionPart_subset hW k hxk, fun m hm => ?_⟩
  by_cases hmk : m = k
  · subst hmk
    exact notMem_dimensionPart_of_regularAtDim hm hkj hxj
  · exact notMem_dimensionPart_of_regularAtDim hm hmk hxk

/-- **The singular points of a dimension part lie in the singular set.** -/
theorem diff_regularLocus_dimensionPart_subset_singularSet {W : Set M} (hW : IsClosed W) (k : ℕ) :
    dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ⊆ singularSet (n := n) W := by
  intro x hx
  obtain ⟨hxk, hxr⟩ := diff_regularLocus_dimensionPart_subset hW k hx
  refine mem_singularSet_iff.mpr ⟨dimensionPart_subset hW k hxk, fun m hm => ?_⟩
  by_cases hmk : m = k
  · subst hmk
    exact hxr hm
  · exact notMem_dimensionPart_of_regularAtDim hm hmk hxk

/-- **A set with empty interior has no part of dimension `≥ n`.** -/
theorem dimensionPart_eq_empty_of_le {W : Set M} (hint : interior W = ∅) {k : ℕ} (hk : n ≤ k) :
    dimensionPart (n := n) W k = ∅ := by
  rw [dimensionPart, closure_empty_iff, eq_empty_iff_forall_notMem]
  intro x hx
  have hkn : k = n := le_antisymm hx.1 hk
  rw [mem_regularLocus, hkn] at hx
  have hxi : x ∈ interior W := mem_interior_iff_mem_nhds.mpr (EmbeddedFromResolution.mem_nhds_of_regularAtDim_self hx)
  rw [hint] at hxi
  exact hxi

/-- **An analytic set with empty interior is the union of its parts of dimension `< n`.** -/
theorem eq_iUnion_dimensionPart_fin {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) :
    W = ⋃ k : Fin n, dimensionPart (n := n) W k := by
  refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun k => dimensionPart_subset hWa.isClosed k)
  rw [eq_iUnion_dimensionPart hWa] at hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have hkn : (k : ℕ) < n := by
    by_contra h
    rw [dimensionPart_eq_empty_of_le hint (not_lt.mp h)] at hk
    exact hk
  exact mem_iUnion.mpr ⟨⟨k, hkn⟩, hk⟩

/-- **The regular points of a dimension part off the singular set and off a set `Z` are dense in it**, when `W \ Z` is dense
in `W` (a regular point of `W` has a neighbourhood in which all points of `W` are regular of the same dimension). -/
theorem dimensionPart_subset_closure_diff {W Z : Set M} (hWZ : W ⊆ closure (W \ Z)) (k : ℕ) :
    dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ (singularSet (n := n) W ∪ W ∩ Z)) := by
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨y, ⟨hyt, hyreg⟩, hyW, hyZ⟩ := mem_closure_iff_nhds.mp (hWZ hx.2.1) _
    (inter_mem ht (RegularPatchNeighborhood.eventually_regularAtDim hx))
  have hyk : RegularAtDim (n := n) W y k := hyreg hyW
  refine ⟨y, hyt, subset_closure hyk, ?_⟩
  rintro (h | h)
  · exact (mem_singularSet_iff.mp h).2 k hyk
  · exact hyZ h.2

end Analytic

/-! ### Points over the singular set are exceptional -/

section Exceptional

variable {X X' : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']

/-- **A smooth strict transform forces `f⁻¹(W_sing) ⊆ Exc f`**: if the strict transform of the closed set `W` is a submanifold
(of some dimension at each point), every point over a singular point of `W` is exceptional (at a non-exceptional point `f` is a
local biholomorphism, and the strict transform is the preimage there). -/
theorem preimage_singularSet_subset_exceptionalLocus {f : X' → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {W : Set X} (hW : IsClosed W)
    (hsub : IsClosedSubmanifold n (strictTransform n f W)) :
    f ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n f := by
  intro y hy
  by_contra hyE
  have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hAO : ∀ w ∈ (exceptionalLocus n f)ᶜ, w ∈ strictTransform n f W ↔ f w ∈ W := fun w hw =>
    mem_strictTransform_iff_of_notMem hf.continuous hW hw
  obtain ⟨k, hk⟩ := hsub.2 y ((hAO y hyE).mpr (mem_singularSet_iff.mp hy).1)
  exact (mem_singularSet_iff.mp hy).2 k
    (HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage hf hyE hO hyE hAO hk)

end Exceptional

/-! ### Embedded resolution of an analytic set -/

section Main

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Embedded resolution of an arbitrary compact analytic set, relative to a simple normal crossings boundary, by one admissible
sequence** (Hironaka; `hir:embedded-resolution-analytic`): let `X` be any complex manifold, `W ⊆ X` a compact analytic set with
empty interior (its components may have different dimensions), and `E₀` a divisor with simple normal crossings no member of
which contains a nonempty relatively open subset of `W`.  Put `F = W_sing ∪ (W ∩ |E₀|)`.  There are an admissible blowup
sequence `f : X' → X` of `(X, E₀)` with centres over `F` and its divisor `E` such that `E` has simple normal crossings,
`Exc f ⊆ ⋃ (new members) ⊆ f⁻¹ F`, `f⁻¹(W_sing) ⊆ Exc f`, `f` is an isomorphism over `X \ F`, the strict transform `W'` of `W`
is a closed submanifold of `X'` which is the union of the strict transforms of the dimension parts `W⁽ᵏ⁾` (`k < n`), these are
pairwise disjoint, `W'` has dimension `k` at each point of the strict transform of `W⁽ᵏ⁾`, and `W'` has only normal crossings
with `E`. -/
theorem exists_embeddedResolution_analytic_boundary_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  set G : Set X := singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H with hGdef
  have hGcl : IsClosed G := (isClosed_singularSet hWa.isClosed).union
    (hWa.isClosed.inter (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1))
  set L : List (Set X × ℕ) := (List.range n).map fun k => (dimensionPart (n := n) W k, k) with hL
  have hgood : ∀ p ∈ L, IsGoodPart n E₀ G p.1 p.2 := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ⟨isComplexAnalyticSubset_dimensionPart hWa k,
      hK.of_isClosed_subset isClosed_closure (dimensionPart_subset hWa.isClosed k), List.mem_range.mp hk,
      (diff_regularLocus_dimensionPart_subset_singularSet hWa.isClosed k).trans subset_union_left,
      fun x hx => Or.inr ⟨dimensionPart_subset hWa.isClosed k hx.1, hx.2⟩, dimensionPart_subset_closure_diff hE₀W k⟩
  have hpair : L.Pairwise (fun p q => p.1 ∩ q.1 ⊆ G) := by
    rw [hL, List.pairwise_map]
    exact List.nodup_range.imp fun {k j} hkj =>
      (inter_dimensionPart_subset_singularSet hWa.isClosed hkj).trans subset_union_left
  obtain ⟨X', i1, i2, i3, f, E, hadm, hsnc, hres, hdisj⟩ :=
    exists_resolution_list L.length E₀ hE₀ G hGcl L rfl hgood hpair
  have hf := hadm.isBlowupSequence.contMDiff
  have hempty : ∀ k : ℕ, ¬ k < n → strictTransform n f (dimensionPart (n := n) W k) = ∅ := fun k hk => by
    rw [dimensionPart_eq_empty_of_le hint (not_lt.mp hk), strictTransform_empty]
  have hresk : ∀ k < n, (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E := fun k hk =>
    hres _ (List.mem_map_of_mem (List.mem_range.mpr hk))
  have hdisjk : ∀ k j : ℕ, k ≠ j →
      Disjoint (strictTransform n f (dimensionPart (n := n) W k))
        (strictTransform n f (dimensionPart (n := n) W j)) := by
    intro k j hkj
    by_cases hk : k < n
    · by_cases hj : j < n
      · have h : (List.range n).Pairwise (fun k j => Disjoint (strictTransform n f (dimensionPart (n := n) W k))
            (strictTransform n f (dimensionPart (n := n) W j))) := by
          have h' := hdisj
          rw [hL, List.pairwise_map] at h'
          exact h'
        have : Std.Symm (fun k j : ℕ => Disjoint (strictTransform n f (dimensionPart (n := n) W k))
            (strictTransform n f (dimensionPart (n := n) W j))) := ⟨fun _ _ h' => h'.symm⟩
        exact h.forall (List.mem_range.mpr hk) (List.mem_range.mpr hj) hkj
      · rw [hempty j hj]
        exact disjoint_empty _
    · rw [hempty k hk]
      exact empty_disjoint _
  have hSTeq : strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) := by
    conv_lhs => rw [eq_iUnion_dimensionPart_fin hWa hint]
    rw [strictTransform, preimage_iUnion, iUnion_sdiff, closure_iUnion_of_finite]
    rfl
  -- near a point of the strict transform of `W⁽ᵏ⁾`, the strict transform of `W` is that of `W⁽ᵏ⁾`
  have hloc : ∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k), ∃ O : Set X', IsOpen O ∧ x ∈ O ∧
      strictTransform n f W ∩ O = strictTransform n f (dimensionPart (n := n) W k) ∩ O := by
    intro k x hx
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hx
      exact hx
    set S : Set (Fin n) := {j | (j : ℕ) ≠ k} with hSdef
    refine ⟨(⋃ j ∈ S, strictTransform n f (dimensionPart (n := n) W j))ᶜ,
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
  have hreg : ∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
      RegularAtDim (n := n) (strictTransform n f W) x k := by
    intro k x hx
    have hk : k < n := by
      by_contra h
      rw [hempty k h] at hx
      exact hx
    obtain ⟨O, hO, hxO, hOeq⟩ := hloc k x hx
    exact RegularPointDimension.regularAtDim_of_inter_eq hO hxO hOeq.symm ((hresk k hk).1 x hx)
  have hsub : IsClosedSubmanifold n (strictTransform n f W) := by
    refine ⟨isClosed_closure, fun x hx => ?_⟩
    rw [hSTeq] at hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact ⟨j, hreg j x hj⟩
  have hnc : HasNormalCrossings n (strictTransform n f W) E := by
    refine CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx => ?_
    have hx' := hx
    rw [hSTeq] at hx'
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
    obtain ⟨O, hO, hxO, hOeq⟩ := hloc j x hj
    refine ⟨strictTransform n f (dimensionPart (n := n) W j), hj, ?_, (hresk j j.2).2⟩
    filter_upwards [hO.mem_nhds hxO] with y hyO
    constructor
    · intro hy
      have h' : y ∈ strictTransform n f W ∩ O := ⟨hy, hyO⟩
      rw [hOeq] at h'
      exact h'.1
    · intro hy
      have h' : y ∈ strictTransform n f (dimensionPart (n := n) W j) ∩ O := ⟨hy, hyO⟩
      rw [← hOeq] at h'
      exact h'.1
  obtain ⟨hexc, hnew⟩ := IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hadm
  exact ⟨X', i1, i2, i3, f, E, hadm, hsnc, hexc, hnew,
    preimage_singularSet_subset_exceptionalLocus hf hWa.isClosed hsub,
    IsAdmissibleBlowupSequence.isIsomorphismOver_compl hadm, hsub, hSTeq, hreg, hdisjk, hnc⟩

/-- **Embedded resolution of an arbitrary compact analytic set by one admissible sequence** (Hironaka;
`hir:embedded-resolution-analytic`; Bierstone--Milman 1997, Theorem 1.6 for a reduced space whose components may have different
dimensions): let `X` be any complex manifold and `W ⊆ X` a compact analytic set with empty interior.  There are an admissible
blowup sequence `f : X' → X` (from the empty divisor, centres over `W_sing`) and its divisor `E` such that `E` has simple normal
crossings, `Exc f = ⋃ E = f⁻¹(W_sing)`, `f` is an isomorphism over `X \ W_sing`, the strict transform `W'` of `W` is a closed
submanifold of `X'` which is the union of the pairwise disjoint strict transforms of the dimension parts `W⁽ᵏ⁾` (`k < n`), of
dimension `k` at each point of the strict transform of `W⁽ᵏ⁾`, and `W'` has only normal crossings with `E`. -/
theorem exists_embeddedResolution_analytic_of_isCompact {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hint : interior W = ∅) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularSet (n := n) W) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularSet (n := n) W ∧
      IsIsomorphismOver n f (singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  obtain ⟨X', i1, i2, i3, f, E, hadm, hsnc, hexc, hnew, hsing, hiso, hsub, hSTeq, hreg, hdisj, hnc⟩ :=
    exists_embeddedResolution_analytic_boundary_of_isCompact hWa hK hint (E₀ := []) isSNCDivisor_nil
      (HironakaEmbeddedBoundary.subset_closure_diff_biUnion_of_forall_disjoint (by simp))
  have hG : singularSet (n := n) W ∪ W ∩ ⋃ H ∈ ([] : List (Set X)), H = singularSet (n := n) W := by simp
  rw [hG] at hadm hnew hiso
  simp only [List.length_nil, List.drop_zero] at hexc hnew
  exact ⟨X', i1, i2, i3, f, E, hadm, hsnc, Subset.antisymm hexc (hnew.trans hsing),
    Subset.antisymm hnew (hsing.trans hexc), hiso, hsub, hSTeq, hreg, hdisj, hnc⟩

/-- **Embedded resolution of an arbitrary analytic set in a compact manifold by one admissible sequence** (`X` compact). -/
theorem exists_embeddedResolution_analytic [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularSet (n := n) W) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularSet (n := n) W ∧
      IsIsomorphismOver n f (singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  exists_embeddedResolution_analytic_of_isCompact hWa hWa.isClosed.isCompact hint

/-- **Embedded resolution of an arbitrary analytic set in a compact manifold, relative to a simple normal crossings boundary, by
one admissible sequence** (`X` compact). -/
theorem exists_embeddedResolution_analytic_boundary [CompactSpace X] {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k)) (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  exists_embeddedResolution_analytic_boundary_of_isCompact hWa hWa.isClosed.isCompact hint hE₀ hE₀W

end Main

end

end Hironaka.HironakaEmbeddedAnalytic
