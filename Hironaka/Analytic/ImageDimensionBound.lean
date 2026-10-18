/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.ThinAnalyticDimensionBound
import Hironaka.Analytic.GenericSections
import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false

/-!
# The image dimension bound

Blueprint `rem:image-dimension-bound` (Demailly, *Complex analytic and differential geometry*,
II.8.6; step M8 of the route to Remmert's proper mapping theorem, `blueprint/src/remmert.tex`).

Let `T` be analytic in a complex manifold `M` with `dim T ≤ a`, and `g : M → ℂ^d` holomorphic such
that `g(T)` contains a nonempty open subset of `ℂ^d` and every fibre `T ∩ g⁻¹(g x)` (`x ∈ T`) has
local dimension `≥ b` at `x`.  Then `d + b ≤ a` (`add_le_of_isOpen_subset_image`).

Proof by induction on `d`, slicing by the first coordinate `h = g₀`: the levels `c` for which
`T ∩ h⁻¹(c)` has interior in `T` are countably many (`countable_exceptionalLevels`: the sets are
disjoint and `M` is second countable), the first coordinates of the open set form an open set of `ℂ`
(open mapping), which is uncountable, so a non-exceptional level `c` exists; then
`T' = T ∩ h⁻¹(c)` is analytic, thin in `T` (so `dim T' ≤ a - 1`, `ThinDimensionDrop`), its image
under the remaining coordinates contains a nonempty open set, and its fibres are those of `T`.

Sorry-free.
-/

open Set Filter Topology Metric
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.ImageDimensionBound

open Hironaka.RegularLocusDense AnalyticDimensionBasics ThinDimensionDrop
  GenericSections

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Coordinates of `ℂ^(d+1)` -/

/-- Drop the first coordinate. -/
def tailCLM (d : ℕ) : ComplexModel (d + 1) →L[ℂ] ComplexModel d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => v i.succ)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp }

@[simp] theorem tailCLM_apply {d : ℕ} (v : ComplexModel (d + 1)) (i : Fin d) :
    tailCLM d v i = v i.succ := rfl

/-- Prepend a first coordinate. -/
def consPt {d : ℕ} (c : ℂ) (w : ComplexModel d) : ComplexModel (d + 1) :=
  WithLp.toLp 2 (Fin.cons c (fun i => w i))

@[simp] theorem consPt_zero {d : ℕ} (c : ℂ) (w : ComplexModel d) : consPt c w 0 = c := rfl

@[simp] theorem tailCLM_consPt {d : ℕ} (c : ℂ) (w : ComplexModel d) : tailCLM d (consPt c w) = w := by
  ext i; rfl

theorem consPt_eq {d : ℕ} (v : ComplexModel (d + 1)) : consPt (v 0) (tailCLM d v) = v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem continuous_consPt {d : ℕ} (c : ℂ) : Continuous (consPt (d := d) c) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact (PiLp.continuous_apply 2 _ j)

theorem eq_of_zero_eq_of_tail_eq {d : ℕ} {v w : ComplexModel (d + 1)} (h0 : v 0 = w 0)
    (ht : tailCLM d v = tailCLM d w) : v = w := by
  rw [← consPt_eq v, ← consPt_eq w, h0, ht]

/-! ### Exceptional levels -/

/-- **Countably many levels have interior.**  For `h : M → ℂ` the levels `c` such that
`T ∩ h⁻¹(c)` contains a nonempty relatively open subset of `T` form a countable set. -/
theorem countable_exceptionalLevels {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (T : Set X) (h : X → ℂ) :
    {c : ℂ | ∃ O : Set X, IsOpen O ∧ (O ∩ T).Nonempty ∧ O ∩ T ⊆ h ⁻¹' {c}}.Countable := by
  have hBc := TopologicalSpace.countable_countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  refine ((hBc.biUnion fun B _ => (?_ : {c : ℂ | (B ∩ T).Nonempty ∧
      B ∩ T ⊆ h ⁻¹' {c}}.Countable))).mono ?_
  · refine Set.Subsingleton.countable fun c hc c' hc' => ?_
    obtain ⟨x, hx⟩ := hc.1
    have h1 : h x = c := hc.2 hx
    have h2 : h x = c' := hc'.2 hx
    rw [← h1, ← h2]
  · rintro c ⟨O, hO, ⟨x, hxO, hxT⟩, hOT⟩
    obtain ⟨B, hB', hxB, hBO⟩ := hB.exists_subset_of_mem_open hxO hO
    exact mem_biUnion hB' ⟨⟨x, hxB, hxT⟩, fun y hy => hOT ⟨hBO hy.1, hy.2⟩⟩

/-! ### The bound -/

/-- **The image dimension bound** (`rem:image-dimension-bound`, first part; `demailly-cadg:II.8.6`).
If `T` is analytic with `dim T ≤ a`, `g : M → ℂ^d` is holomorphic, `g(T)` contains a nonempty open
set, and `dim_x (T ∩ g⁻¹(g x)) ≥ b` for every `x ∈ T`, then `d + b ≤ a`. -/
theorem add_le_of_isOpen_subset_image : ∀ (d : ℕ) {T : Set M} {a b : ℕ} {g : M → ComplexModel d},
    IsComplexAnalyticSubset (n := n) T → DimLE (n := n) T a →
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ g →
    (∃ O : Set (ComplexModel d), IsOpen O ∧ O.Nonempty ∧ O ⊆ g '' T) →
    (∀ x ∈ T, LocDimGE (n := n) (T ∩ g ⁻¹' {g x}) x b) → d + b ≤ a := by
  intro d
  induction d with
  | zero =>
    intro T a b g _ hdim _ hO hfib
    obtain ⟨O, -, ⟨o, ho⟩, hOT⟩ := hO
    obtain ⟨x, hxT, -⟩ := hOT ho
    have hset : T ∩ g ⁻¹' {g x} = T := by
      refine inter_eq_left.mpr fun y _ => ?_
      exact Subsingleton.elim (g y) (g x)
    obtain ⟨y, -, k, hbk, hy⟩ := hfib x hxT univ univ_mem
    rw [hset] at hy
    have := hdim y k hy
    omega
  | succ d ih =>
    intro T a b g hT hdim hg hO hfib
    classical
    obtain ⟨O, hOo, ⟨o, ho⟩, hOT⟩ := hO
    set h : M → ℂ := fun y => g y 0 with hh
    set Ex := {c : ℂ | ∃ O : Set M, IsOpen O ∧ (O ∩ T).Nonempty ∧ O ∩ T ⊆ h ⁻¹' {c}} with hEx
    have hExc : Ex.Countable := countable_exceptionalLevels T h
    -- the first coordinates of `O` form a nonempty open subset of `ℂ`
    set p₀ : ComplexModel (d + 1) →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin (d + 1)) with hp₀
    have hp₀s : Function.Surjective p₀ := fun c =>
      ⟨EuclideanSpace.single 0 c, by simp [hp₀]⟩
    have hΩ₀ : IsOpen (p₀ '' O) :=
      LinearMap.isOpenMap_of_finiteDimensional (p₀ : ComplexModel (d + 1) →ₗ[ℂ] ℂ) hp₀s O hOo
    have hden : Dense Exᶜ := hExc.dense_compl ℂ
    obtain ⟨c, ⟨x, hxO, hxc⟩, hcEx⟩ := hden.inter_open_nonempty _ hΩ₀ ⟨p₀ o, o, ho, rfl⟩
    -- the slice `T'`
    set T' : Set M := T ∩ {y | p₀ (g y) = c} with hT'
    have hT'a : IsComplexAnalyticSubset (n := n) T' := isComplexAnalyticSubset_section hT hg p₀ c
    have hT'T : T' ⊆ T := inter_subset_left
    have hthin : ∀ U : Set M, IsOpen U → U ∩ T ⊆ T' → U ∩ T = ∅ := by
      intro U hU hUT
      by_contra hne
      exact hcEx ⟨U, hU, nonempty_iff_ne_empty.mpr hne, fun y hy => (hUT hy).2⟩
    -- the remaining coordinates
    set g' : M → ComplexModel d := fun y => tailCLM d (g y) with hg'
    have hg'd : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel d) ∞ g' :=
      (tailCLM d).contDiff.contMDiff.comp hg
    set O' : Set (ComplexModel d) := consPt c ⁻¹' O with hO'
    have hO'o : IsOpen O' := hOo.preimage (continuous_consPt c)
    have hxO' : tailCLM d x ∈ O' := by
      show consPt c (tailCLM d x) ∈ O
      have : consPt (x 0) (tailCLM d x) = x := consPt_eq x
      have hx0 : x 0 = c := hxc
      rw [hx0] at this
      rw [this]; exact hxO
    have hO'T : O' ⊆ g' '' T' := by
      intro w hw
      obtain ⟨y, hyT, hyw⟩ := hOT hw
      refine ⟨y, ⟨hyT, ?_⟩, ?_⟩
      · show p₀ (g y) = c
        rw [hyw]; rfl
      · show tailCLM d (g y) = w
        rw [hyw, tailCLM_consPt]
    -- the fibres of `g'` on `T'` are those of `g` on `T`
    have hfib' : ∀ y ∈ T', LocDimGE (n := n) (T' ∩ g' ⁻¹' {g' y}) y b := by
      intro y hy
      have hset : T' ∩ g' ⁻¹' {g' y} = T ∩ g ⁻¹' {g y} := by
        ext z
        constructor
        · rintro ⟨⟨hzT, hz0⟩, hzt⟩
          refine ⟨hzT, eq_of_zero_eq_of_tail_eq ?_ hzt⟩
          have h1 : p₀ (g z) = c := hz0
          have h2 : p₀ (g y) = c := hy.2
          exact h1.trans h2.symm
        · rintro ⟨hzT, hzg⟩
          have hzg' : g z = g y := hzg
          refine ⟨⟨hzT, ?_⟩, ?_⟩
          · show p₀ (g z) = c
            rw [hzg']; exact hy.2
          · show tailCLM d (g z) = tailCLM d (g y)
            rw [hzg']
      rw [hset]
      exact hfib y hy.1
    -- dimension drop and induction
    have hxT' : ∃ y, y ∈ T' := by
      obtain ⟨y, hy, -⟩ := hO'T hxO'
      exact ⟨y, hy⟩
    obtain ⟨y₀, hy₀⟩ := hxT'
    obtain ⟨z, -, j, hz⟩ := exists_regularAtDim_mem_nhds hT'a hy₀ univ_mem
    have hja := lt_of_regularAtDim_of_thin hT hT'T hthin hdim hz
    have hdim' : DimLE (n := n) T' (a - 1) := dimLE_pred_of_thin hT hT'T hthin hdim
    have := ih hT'a hdim' hg'd ⟨O', hO'o, ⟨_, hxO'⟩, hO'T⟩ hfib'
    omega

end Hironaka.ImageDimensionBound

end
