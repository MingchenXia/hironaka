import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.RelativePrincipalizationVanishingWeight
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.ExceptionalFibres

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Total transforms along a blowup sequence, and `eq:IV-H` for a two-stage modification

Source: Copy-4, the remark after `lem:relative-principalization` and Step 2 of
`prop:principalization` (`transcendental-nakamaye-copy4-20260911`).

`GermIdealTotalTransform` builds `g^* D` under the hypothesis
`interior (Exc g) = ∅`.  That hypothesis was derived in the project only inline
and only for a **single** blowup (`BlowupPushforward`, `ExceptionalMetricProof`),
whereas Step 2 composes whole sequences.  This module names it for a sequence and
then spends it:

* `interior_exceptionalLocus_eq_empty_of_isBlowupAlong` — the single-blowup fact, as
  a lemma rather than a repeated `have`.
* `interior_preimage_eq_empty` — a thin set pulls back to a thin set along a map
  whose own exceptional locus is thin.  This is the induction step, and it is the
  same openness argument as `MeteredDivisorOperations.exists_ne_zero_comp`.
* `interior_exceptionalLocus_eq_empty_of_isBlowupSequence` and the adapted version —
  by induction on the sequence, using `exceptionalLocus_comp` and the fact that a
  union of two **closed** thin sets is thin (complements are dense open).
* `pullback_vanishingIdeal_comp_eq_mul_of_isBlowupSequence` — clause (i) of
  `lem:relative-principalization` for the composition `f ∘ g` of a modification
  with a blowup sequence, with `g^* H + H'` in place of `H`; the `interior`
  hypothesis is now discharged, so this has actual instantiations.
* `exists_weights_sameSingularityTypeOn_strictTransform_comp` — `eq:IV-H` for the
  composition, in the weight form Step 5 consumes:
  `ψ_{𝓘_W} ∘ (f ∘ g) = ψ_{g^*H + H'} + ψ_{𝓘_{W''}} + O(1)`.  This is the point of
  the whole chain: `RelativePrincipalizationVanishingWeight` could only state
  `eq:IV-H` for ONE stage, and Copy-4's `H = H^fix_m + P^mov + P^F` is three.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSequenceTotalTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.GlobalAnalyticSingularities GermIdealTotalTransform

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]

/-! ## The exceptional locus of a blowup sequence is thin -/

/-- A single blowup has a thin exceptional locus: it is contained in the preimage
of the centre, whose interior is empty. -/
theorem interior_exceptionalLocus_eq_empty_of_isBlowupAlong {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) : interior (exceptionalLocus n g) = ∅ :=
  subset_empty_iff.mp
    ((interior_mono (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg)).trans
      (ExceptionalFibres.interior_preimage_eq_empty hg).subset)

/-- **A thin set pulls back to a thin set** along a holomorphic map whose own
exceptional locus is thin: off that locus the map is open, so a nonempty open
subset of the preimage would produce a nonempty open subset of the target set. -/
theorem interior_preimage_eq_empty {g : Z → Y}
    (hgm : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅)
    {A : Set Y} (hA : interior A = ∅) : interior (g ⁻¹' A) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  have hnot : ¬ interior (g ⁻¹' A) ⊆ exceptionalLocus n g := fun hsub => by
    have hmem := interior_maximal hsub isOpen_interior hz
    rw [hint] at hmem
    exact hmem
  obtain ⟨z₀, hz₀, hz₀E⟩ := not_subset.mp hnot
  have himg : g '' interior (g ⁻¹' A) ∈ 𝓝 (g z₀) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hgm hz₀E]
    exact image_mem_map (isOpen_interior.mem_nhds hz₀)
  have hsubA : g '' interior (g ⁻¹' A) ⊆ A := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_preimage.mp (interior_subset hw)
  have hmem : g z₀ ∈ interior A :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset himg hsubA)
  rw [hA] at hmem
  exact hmem

/-- **The exceptional locus of a blowup sequence has empty interior.**  Induction
on the sequence: `Exc (f ∘ g) = Exc g ∪ g⁻¹(Exc f)` is a union of two closed sets
with empty interior, and the complements are dense open. -/
theorem interior_exceptionalLocus_eq_empty_of_isBlowupSequence {f : Y → X}
    (hf : IsBlowupSequence n X Y f) : interior (exceptionalLocus n f) = ∅ := by
  induction hf with
  | refl => simp [exceptionalLocus_id]
  | step f C g hseq hblow ih =>
      have hfm := hseq.contMDiff
      have hgm := hblow.contMDiff
      have hgint := interior_exceptionalLocus_eq_empty_of_isBlowupAlong hblow
      have hpre : interior (g ⁻¹' exceptionalLocus n f) = ∅ :=
        interior_preimage_eq_empty hgm hgint ih
      rw [exceptionalLocus_comp (hfm.mdifferentiable (by simp))
        (hgm.mdifferentiable (by simp))]
      have hd : Dense ((exceptionalLocus n g)ᶜ ∩ (g ⁻¹' exceptionalLocus n f)ᶜ) :=
        (interior_eq_empty_iff_dense_compl.mp hgint).inter_of_isOpen_left
          (interior_eq_empty_iff_dense_compl.mp hpre)
          (StrictTransformComposition.isOpen_compl_exceptionalLocus hgm)
      rw [← compl_union] at hd
      exact interior_eq_empty_iff_dense_compl.mpr hd

/-- The adapted version, which is the shape `IsAdaptedBlowupSequence` users hold. -/
theorem interior_exceptionalLocus_eq_empty_of_isAdaptedBlowupSequence {W : Set X} {f : Y → X}
    (hf : IsAdaptedBlowupSequence n X W Y f) : interior (exceptionalLocus n f) = ∅ :=
  interior_exceptionalLocus_eq_empty_of_isBlowupSequence hf.isBlowupSequence

/-! ## `eq:IV-H` across two stages -/

/-- **Clause (i) of `lem:relative-principalization` for `f ∘ g`**, with `g` a
blowup sequence.  The `interior (Exc g) = ∅` hypothesis of
`GermIdealTotalTransform.pullback_vanishingIdeal_comp_eq_mul` is discharged here,
so the total transform `g^* H` exists and the composite divisor is
`g^* H + H'`. -/
theorem pullback_vanishingIdeal_comp_eq_mul_of_isBlowupSequence
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hgseq : IsBlowupSequence n Y Z g)
    {W : Set X} (hW : IsClosedSubmanifold n W)
    (hW' : IsClosedSubmanifold n (strictTransform n f W))
    (hW'' : IsClosedSubmanifold n (strictTransform n g (strictTransform n f W)))
    (H : EffectiveDivisor n Y) (H' : EffectiveDivisor n Z)
    (h1 : GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W)
      = H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)))
    (h2 : GermIdeal.pullback (m := n) g
        (vanishingIdeal (n := n) (strictTransform n f W))
      = H'.ideal.mul
          (vanishingIdeal (n := n) (strictTransform n g (strictTransform n f W)))) :
    ∃ Htot : EffectiveDivisor n Z,
      Htot.ideal = (GermIdeal.pullback (m := n) g H.ideal).mul H'.ideal ∧
      GermIdeal.pullback (m := n) (f ∘ g) (vanishingIdeal (n := n) W)
        = Htot.ideal.mul
            (vanishingIdeal (n := n) (strictTransform n (f ∘ g) W)) := by
  refine ⟨EffectiveDivisor.add
      (EffectiveDivisor.totalTransform hgseq.contMDiff
        (interior_exceptionalLocus_eq_empty_of_isBlowupSequence hgseq) H) H', rfl, ?_⟩
  exact pullback_vanishingIdeal_comp_eq_mul hf hgseq.contMDiff
    (interior_exceptionalLocus_eq_empty_of_isBlowupSequence hgseq) hW hW' hW'' H H' h1 h2

/-- **`eq:IV-H` for a two-stage modification**, in the weight form Step 5 consumes:
`ψ_{𝓘_W} ∘ (f ∘ g) = ψ_{g^*H + H'} + ψ_{𝓘_{W''}} + O(1)` on the whole of `Z`.

`RelativePrincipalizationVanishingWeight` could only state this for one stage;
Copy-4's `H = H^fix_m + P^mov + P^F` is a composition of three, and this is the
inductive step that reaches it. -/
theorem exists_weights_sameSingularityTypeOn_strictTransform_comp
    [CompactSpace X] [CompactSpace Z] {j l : ℕ}
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hgseq : IsBlowupSequence n Y Z g)
    {W : Set X} (hW : IsClosedConnectedSubmanifold n W j)
    (hW' : IsClosedSubmanifold n (strictTransform n f W))
    (hW'' : IsClosedSubmanifold n (strictTransform n g (strictTransform n f W)))
    (hWcomp : IsClosedConnectedSubmanifold n (strictTransform n (f ∘ g) W) l)
    (H : EffectiveDivisor n Y) (H' : EffectiveDivisor n Z)
    (h1 : GermIdeal.pullback (m := n) f (vanishingIdeal (n := n) W)
      = H.ideal.mul (vanishingIdeal (n := n) (strictTransform n f W)))
    (h2 : GermIdeal.pullback (m := n) g
        (vanishingIdeal (n := n) (strictTransform n f W))
      = H'.ideal.mul
          (vanishingIdeal (n := n) (strictTransform n g (strictTransform n f W)))) :
    ∃ (Htot : EffectiveDivisor n Z) (φW : X → EReal)
      (E : MeteredEffectiveQDivisor n Z) (φW' : Z → EReal),
      Htot.ideal = (GermIdeal.pullback (m := n) g H.ideal).mul H'.ideal ∧
      HasAnalyticSingularitiesOfType (n := n) φW 1 (vanishingIdeal (n := n) W) ∧
      E.support = Htot.support ∧
      HasAnalyticSingularitiesOfType (n := n) φW' 1
        (vanishingIdeal (n := n) (strictTransform n (f ∘ g) W)) ∧
      SameSingularityTypeOn (φW ∘ (f ∘ g)) (fun z => E.weight z + φW' z) univ := by
  obtain ⟨Htot, hHtot, hfact⟩ :=
    pullback_vanishingIdeal_comp_eq_mul_of_isBlowupSequence hf hgseq
      (RelativePrincipalizationVanishingWeight.isClosedSubmanifold_of_isClosedConnectedSubmanifold
        hW)
      hW' hW'' H H' h1 h2
  obtain ⟨φW, E, φW', hφW, hEsupp, hφW', hsame⟩ :=
    RelativePrincipalizationVanishingWeight.exists_weights_sameSingularityTypeOn_strictTransform
      (hf.comp hgseq.contMDiff) hW hWcomp Htot hfact
  exact ⟨Htot, φW, E, φW', hHtot, hφW, hEsupp, hφW', hsame⟩

end

end Hironaka.BlowupSequenceTotalTransform
