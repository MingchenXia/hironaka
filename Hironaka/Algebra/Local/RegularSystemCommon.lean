/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.RegularSystem

/-!
# A common complement for two regular systems of parameters

Kollár, in the proof of the formal equivalence theorem [Kol07, 95], completes the equations
`x₁`, `x₁'` of the two hypersurfaces of maximal contact and the equations `x₂, …, x_{s+1}` of the
divisors `Eⁱ` to the local coordinate systems `x₁, x₂, …, xₙ` and `x₁', x₂, …, xₙ` by "a general
choice of `x_{s+2}, …, xₙ`".
This is the existence of a common complement of the two subspaces `⟨x̄₁, ē⟩`, `⟨x̄₁', ē⟩` of
`𝔪/𝔪²`.  No genericity or infinite-field argument is needed: a union of two proper subspaces
never exhausts a vector space, and here the construction is explicit.  The ring-level statement
is not in the sources in this form; it is used for the coordinates adapted to two hypersurfaces
of maximal contact in `Hironaka/Resolution/Algebraic/MaximalContact/Coordinates.lean`.

**Why it holds.** Let `R` be a regular local ring with residue field `κ`, `z = (z₀, …, z_d)` a
regular system of parameters (its classes `z̄ᵢ` form a basis `b` of `𝔪/𝔪²`,
`Hironaka/Algebra/Local/RegularSystem.lean`), `p₀` the index of the coordinate to be exchanged
(Kollár's `x₁ = z_{p₀}`), `T ∌ p₀` the set of indices of the protected coordinates (the equations of
the `Eⁱ` through `p`), and `x' ∈ 𝔪` (Kollár's `x₁'`) whose class does not lie in `⟨z̄ᵢ : i ∈ T⟩`
(because `x₁'` and the `Eⁱ` have simple normal crossings). Expand `x̄' = ∑ᵢ rᵢ z̄ᵢ`.

* If `r_{p₀} ≠ 0`, take `y := (zᵢ)_{i ≠ p₀}`: then `(z_{p₀}, y)` is `z` up to order, and `(x', y)`
  generates `𝔪` because `z̄_{p₀} = r_{p₀}⁻¹ (x̄' − ∑_{i ≠ p₀} rᵢ z̄ᵢ)` lies in the span of the
  classes of `x'` and `y`.
* If `r_{p₀} = 0`, some `j₀ ∉ T`, `j₀ ≠ p₀`, has `r_{j₀} ≠ 0` (otherwise `x̄' ∈ ⟨z̄_T⟩`); take `y :=
  (zᵢ)_{i ≠ p₀}` with `z_{j₀}` replaced by `z_{j₀} + z_{p₀}` (Kollár's "general choice": one
  coordinate is tilted by `x₁`). Then `(z_{p₀}, y)` still generates `𝔪` (`z_{j₀} = (z_{j₀} + z_{p₀})
  − z_{p₀}`), and for `(x', y)`: `z̄_{j₀} = r_{j₀}⁻¹ (x̄' − ∑_{i ≠ p₀, j₀} rᵢ z̄ᵢ)` and then
  `z̄_{p₀} = (z̄_{j₀} + z̄_{p₀}) − z̄_{j₀}` lie in the span, so all of `b` does.

In both cases the protected coordinates `zᵢ`, `i ∈ T`, are members of `y` unchanged, and a family of
`d + 1 = dim R` elements of `𝔪` whose classes span `𝔪/𝔪²` generates `𝔪` (Nakayama,
`span_eq_maximalIdeal_iff_span_toCotangent_eq_top` of `Hironaka/Algebra/Local/RegularSystem.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- Members of a generating family of `𝔪` lie in `𝔪`. -/
theorem mem_maximalIdeal_of_eq_span {ι : Type*} {z : ι → R}
    (hz : maximalIdeal R = Ideal.span (Set.range z)) (i : ι) : z i ∈ maximalIdeal R :=
  hz ▸ Ideal.subset_span ⟨i, rfl⟩

omit [IsRegularLocalRing R] in
/-- A regular system of parameters, one index removed and one coordinate possibly tilted by the
removed one: the family `y` of `exists_cons_regularSystem_common`. -/
noncomputable def tiltedComplement {d : ℕ} (z : Fin (d + 1) → R) (p₀ : Fin (d + 1))
    (t : Fin d → R) : Fin d → R :=
  fun j => z (p₀.succAbove j) + t j * z p₀

omit [IsRegularLocalRing R] in
theorem tiltedComplement_apply {d : ℕ} (z : Fin (d + 1) → R) (p₀ : Fin (d + 1)) (t : Fin d → R)
    (j : Fin d) : tiltedComplement z p₀ t j = z (p₀.succAbove j) + t j * z p₀ := rfl

/-- `(z_{p₀}, y)` generates `𝔪` whenever `z` does (the tilt is invertible). -/
theorem span_range_cons_tiltedComplement {d : ℕ} (z : Fin (d + 1) → R)
    (hz : maximalIdeal R = Ideal.span (Set.range z)) (p₀ : Fin (d + 1)) (t : Fin d → R) :
    maximalIdeal R = Ideal.span (Set.range (Fin.cons (z p₀) (tiltedComplement z p₀ t))) := by
  refine le_antisymm ?_ ?_
  · rw [hz]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = p₀
    · subst hi
      exact Ideal.subset_span ⟨0, by simp⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      have hy : tiltedComplement z p₀ t j ∈
          Ideal.span (Set.range (Fin.cons (z p₀) (tiltedComplement z p₀ t))) :=
        Ideal.subset_span ⟨j.succ, by simp⟩
      have hp : z p₀ ∈ Ideal.span (Set.range (Fin.cons (z p₀) (tiltedComplement z p₀ t))) :=
        Ideal.subset_span ⟨0, by simp⟩
      have : z (p₀.succAbove j) = tiltedComplement z p₀ t j - t j * z p₀ := by
        rw [tiltedComplement_apply]; ring
      rw [this]
      exact Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hp)
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using mem_maximalIdeal_of_eq_span hz p₀
    · simp only [Fin.cons_succ, tiltedComplement_apply]
      exact Ideal.add_mem _ (mem_maximalIdeal_of_eq_span hz _)
        (Ideal.mul_mem_left _ _ (mem_maximalIdeal_of_eq_span hz _))

/-- For a regular system of parameters `z` of `R`, an index `p₀`, a set `T ∌ p₀` of protected
indices and `x' ∈ 𝔪` whose class in `𝔪/𝔪²` is not in the span of the classes `z̄ᵢ`, `i ∈ T`, there
is a family `y` of `d` elements containing every `zᵢ`, `i ∈ T`, such that both `(z_{p₀}, y)` and
`(x', y)` are regular systems of parameters (Kollár's "for a general choice of `x_{s+2}, …, xₙ`",
[Kol07, 95], made explicit). -/
theorem exists_cons_regularSystem_common {d : ℕ} (z : Fin (d + 1) → R)
    (hz : maximalIdeal R = Ideal.span (Set.range z)) (p₀ : Fin (d + 1)) (T : Set (Fin (d + 1)))
    (hT : p₀ ∉ T) (x' : R) (hx' : x' ∈ maximalIdeal R)
    (b : Module.Basis (Fin (d + 1)) (ResidueField R) (CotangentSpace R))
    (hb : ∀ i, b i = (maximalIdeal R).toCotangent ⟨z i, mem_maximalIdeal_of_eq_span hz i⟩)
    (hv : (maximalIdeal R).toCotangent ⟨x', hx'⟩ ∉
      Submodule.span (ResidueField R) (b '' T)) :
    ∃ y : Fin d → R, (∀ i ∈ T, ∃ j, y j = z i) ∧
      maximalIdeal R = Ideal.span (Set.range (Fin.cons (z p₀) y)) ∧
      maximalIdeal R = Ideal.span (Set.range (Fin.cons x' y)) := by
  classical
  set v := (maximalIdeal R).toCotangent ⟨x', hx'⟩ with hvdef
  set r := b.repr v with hrdef
  have hsum : ∑ i, r i • b i = v := b.sum_repr v
  -- the tilt `t`: zero, or the indicator of `j₁` with `p₀.succAbove j₁ = j₀`
  have key : ∃ t : Fin d → R, (∀ j, t j ≠ 0 → p₀.succAbove j ∉ T) ∧
      maximalIdeal R = Ideal.span (Set.range (Fin.cons x' (tiltedComplement z p₀ t))) := by
    -- the cotangent criterion for `(x', y)`
    have hmem : ∀ t : Fin d → R, ∀ i,
        (Fin.cons x' (tiltedComplement z p₀ t) : Fin (d + 1) → R) i ∈ maximalIdeal R := by
      intro t i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx'
      · simp only [Fin.cons_succ, tiltedComplement_apply]
        exact Ideal.add_mem _ (mem_maximalIdeal_of_eq_span hz _)
          (Ideal.mul_mem_left _ _ (mem_maximalIdeal_of_eq_span hz _))
    -- the span `S t` of the classes of `(x', y)`
    set S : (Fin d → R) → Submodule (ResidueField R) (CotangentSpace R) := fun t =>
      Submodule.span (ResidueField R)
        (Set.range fun i => (maximalIdeal R).toCotangent
          ⟨(Fin.cons x' (tiltedComplement z p₀ t) : Fin (d + 1) → R) i, hmem t i⟩) with hS
    have hvS : ∀ t, v ∈ S t := fun t => Submodule.subset_span ⟨0, by simp [hvdef]⟩
    have hyS : ∀ t j, (maximalIdeal R).toCotangent
        ⟨tiltedComplement z p₀ t j, hmem t j.succ⟩ ∈ S t :=
      fun t j => Submodule.subset_span ⟨j.succ, by simp⟩
    -- the class of `y_j` is `b (p₀.succAbove j) + t̄ⱼ • b p₀`
    have hyb : ∀ t j, (maximalIdeal R).toCotangent ⟨tiltedComplement z p₀ t j, hmem t j.succ⟩ =
        b (p₀.succAbove j) + residue R (t j) • b p₀ := by
      intro t j
      rw [hb, hb]
      have : (⟨tiltedComplement z p₀ t j, hmem t j.succ⟩ : maximalIdeal R) =
          ⟨z (p₀.succAbove j), mem_maximalIdeal_of_eq_span hz _⟩ +
            t j • ⟨z p₀, mem_maximalIdeal_of_eq_span hz p₀⟩ := by
        ext; simp [tiltedComplement_apply]
      rw [this, map_add, map_smul]
      exact congrArg (_ + ·) (algebraMap_smul (ResidueField R) (t j) _).symm
    -- if all of `b` lies in `S t`, then `S t = ⊤`
    have hSt : ∀ t, (∀ i, b i ∈ S t) → S t = ⊤ := fun t h => by
      rw [eq_top_iff]
      intro w _
      rw [← b.sum_repr w]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)
    -- and then `(x', y)` generates `𝔪`
    have hgen : ∀ t, (∀ i, b i ∈ S t) →
        maximalIdeal R = Ideal.span (Set.range (Fin.cons x' (tiltedComplement z p₀ t))) :=
      fun t h => (span_eq_maximalIdeal_iff_span_toCotangent_eq_top _ (hmem t)).mpr (hSt t h)
    by_cases h0 : r p₀ = 0
    · -- case 2: some `j₀ ∉ T`, `j₀ ≠ p₀` with `r j₀ ≠ 0`
      have hns : ¬ (↑r.support ⊆ T) := fun h => hv (b.mem_span_image.mpr h)
      obtain ⟨j₀, hj₀s, hj₀T⟩ := Set.not_subset.mp hns
      have hr₀ : r j₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀s
      have hj₀ : j₀ ≠ p₀ := fun h => hr₀ (h ▸ h0)
      obtain ⟨j₁, hj₁⟩ := Fin.exists_succAbove_eq hj₀
      set t : Fin d → R := fun j => if j = j₁ then 1 else 0 with ht
      refine ⟨t, fun j hj => ?_, hgen t ?_⟩
      · have : j = j₁ := by
          by_contra hne
          exact hj (by simp [ht, hne])
        subst this
        rw [hj₁]
        exact hj₀T
      · -- classes of the untilted `y_j` are the `b i`, `i ≠ p₀, j₀`
        have hb_other : ∀ i, i ≠ p₀ → i ≠ j₀ → b i ∈ S t := by
          intro i hip hij
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hip
          have hjj : j ≠ j₁ := fun h => hij (by rw [h, hj₁])
          have := hyS t j
          rwa [hyb, show residue R (t j) = 0 by simp [ht, hjj], zero_smul, add_zero] at this
        -- `b j₀` from `v`
        have hbj₀ : b j₀ ∈ S t := by
          have hsplit : v = r j₀ • b j₀ + ∑ i ∈ Finset.univ.erase j₀, r i • b i :=
            hsum.symm.trans
              (Finset.add_sum_erase Finset.univ (fun i => r i • b i) (Finset.mem_univ j₀)).symm
          have hrest : ∑ i ∈ Finset.univ.erase j₀, r i • b i ∈ S t := by
            refine Submodule.sum_mem _ fun i hi => ?_
            by_cases hip : i = p₀
            · subst hip; rw [h0, zero_smul]; exact Submodule.zero_mem _
            · exact Submodule.smul_mem _ _ (hb_other i hip (Finset.ne_of_mem_erase hi))
          have : b j₀ = (r j₀)⁻¹ • (v - ∑ i ∈ Finset.univ.erase j₀, r i • b i) := by
            rw [hsplit, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr₀, one_smul]
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hvS t) hrest)
        -- `b p₀` from `y_{j₁}`
        have hbp₀ : b p₀ ∈ S t := by
          have := hyS t j₁
          rw [hyb, hj₁, show residue R (t j₁) = 1 by simp [ht], one_smul] at this
          have h' : b p₀ = (b j₀ + b p₀) - b j₀ := by abel
          rw [h']
          exact Submodule.sub_mem _ this hbj₀
        intro i
        by_cases hip : i = p₀
        · exact hip ▸ hbp₀
        by_cases hij : i = j₀
        · exact hij ▸ hbj₀
        exact hb_other i hip hij
    · -- case 1: `r p₀ ≠ 0`, no tilt
      refine ⟨fun _ => 0, fun j hj => (hj rfl).elim, hgen _ ?_⟩
      have hb_other : ∀ i, i ≠ p₀ → b i ∈ S fun _ => 0 := by
        intro i hip
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hip
        have := hyS (fun _ => 0) j
        rwa [hyb, map_zero, zero_smul, add_zero] at this
      have hbp₀ : b p₀ ∈ S fun _ => 0 := by
        have hsplit : v = r p₀ • b p₀ + ∑ i ∈ Finset.univ.erase p₀, r i • b i :=
          hsum.symm.trans
            (Finset.add_sum_erase Finset.univ (fun i => r i • b i) (Finset.mem_univ p₀)).symm
        have hrest : ∑ i ∈ Finset.univ.erase p₀, r i • b i ∈ S fun _ => 0 :=
          Submodule.sum_mem _ fun i hi =>
            Submodule.smul_mem _ _ (hb_other i (Finset.ne_of_mem_erase hi))
        have : b p₀ = (r p₀)⁻¹ • (v - ∑ i ∈ Finset.univ.erase p₀, r i • b i) := by
          rw [hsplit, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h0, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hvS _) hrest)
      intro i
      by_cases hip : i = p₀
      · exact hip ▸ hbp₀
      exact hb_other i hip
  obtain ⟨t, htT, hgen⟩ := key
  refine ⟨tiltedComplement z p₀ t, fun i hi => ?_, span_range_cons_tiltedComplement z hz p₀ t, hgen⟩
  have hip : i ≠ p₀ := fun h => hT (h ▸ hi)
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hip
  refine ⟨j, ?_⟩
  have htj : t j = 0 := by
    by_contra h
    exact htT j h hi
  rw [tiltedComplement_apply, htj, zero_mul, add_zero]

end IsLocalRing
