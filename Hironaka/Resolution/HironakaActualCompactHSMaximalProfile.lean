import Mathlib.Order.PiLex
import Hironaka.Resolution.HironakaCompactEntireHSFiniteRange
import Mathlib.Data.Set.Finite.Lemmas

/-! Original coherent ideals internally supply finite entire HS ranges on
actual compact sets, attained Lex maxima, and one actual pointwise upper
window at EVERY original order. Finite ranges are derived from analytic
descending chains and the well-quasi-order on realized profiles.
Blueprint: `hironaka-actual-compact-hs-maximal-profile-20261102.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualCompactHSMaximalProfile
noncomputable section
open Hironaka.HolomorphicIdealSheaves HironakaHolomorphicJetChartInvariance
  HironakaCompactEntireHSFiniteRange

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

set_option linter.unusedVariables false in
/-- A finite coherent family has finite entire profile range on a compact set.
The analytic-carrier hypotheses are retained for compatibility. -/
theorem actual_compact_entire_hs_family_finite_range
    {ι : Type v} [Fintype ι] (A : ι → GermIdeal n X) (hA : ∀ i, (A i).IsCoherent)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (K : Set X) (hK : IsCompact K) (hKW : K ⊆ W) :
    ((fun y i ℓ => hilbertSamuelAt (A i) y ℓ) '' K).Finite := by
  classical
  let P : ι → Set (ℕ → ℕ) := fun i => hilbertSamuelAt (A i) '' K
  have hP : ∀ i, (P i).Finite := fun i => compact_entire_hs_finite_range (A i) (hA i) K hK
  refine (Set.Finite.pi hP).subset ?_
  rintro f ⟨x, hx, rfl⟩ i hi
  exact ⟨x, hx, rfl⟩

/-- No analyticity of the compact set is needed for a genuine finite entire profile range. -/
theorem actual_compact_entire_hs_finite_range (A : GermIdeal n X) (hA : A.IsCoherent)
    (K : Set X) (hK : IsCompact K) :
    (hilbertSamuelAt A '' K).Finite := by
  exact compact_entire_hs_finite_range A hA K hK

/-- Actual compact geometry internally selects a reference attaining the entire original Lex maximum. -/
theorem exists_actual_compact_hs_lex_maximum (A : GermIdeal n X) (hA : A.IsCoherent)
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ a ∈ K, ∀ x ∈ K, toLex (hilbertSamuelAt A x) ≤ toLex (hilbertSamuelAt A a) := by
  have hf : ((fun x => toLex (hilbertSamuelAt A x)) '' K).Finite := by
    simpa only [image_image, Function.comp_def] using
      (actual_compact_entire_hs_finite_range A hA K hK).image toLex
  obtain ⟨H, hH, hm⟩ := Set.exists_max_image _ id hf (hne.image _)
  obtain ⟨a, ha, rfl⟩ := hH
  exact ⟨a, ha, fun x hx => hm _ (mem_image_of_mem _ hx)⟩

private theorem exists_entire_hs_finite_range_window (A : GermIdeal n X) (hA : A.IsCoherent)
    (a : X) : ∃ U : Opens X, a ∈ U ∧ (hilbertSamuelAt A '' (U : Set X)).Finite := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨K, hK, haK⟩ := exists_compact_mem_nhds a
  exact ⟨⟨interior K, isOpen_interior⟩, mem_interior_iff_mem_nhds.mpr haK,
    (compact_entire_hs_finite_range A hA K hK).subset (image_mono interior_subset)⟩

/-- One actual open window bounds the ENTIRE original coherent HS function at EVERY original order. -/
theorem exists_actual_entire_hs_pointwise_upper_window (A : GermIdeal n X) (hA : A.IsCoherent)
    (a : X) : ∃ U : Opens X, a ∈ U ∧
      (∀ x ∈ U, ∀ ℓ : ℕ, hilbertSamuelAt A x ℓ ≤ hilbertSamuelAt A a ℓ) ∧
      ∀ x ∈ U, toLex (hilbertSamuelAt A x) ≤ toLex (hilbertSamuelAt A a) := by
  classical
  obtain ⟨V, haV, hf⟩ := exists_entire_hs_finite_range_window A hA a
  let R := hilbertSamuelAt A '' (V : Set X)
  let B : Set (ℕ → ℕ) := {H | H ∈ R ∧ ¬ H ≤ hilbertSamuelAt A a}
  have hB : B.Finite := hf.subset (fun _ h => h.1)
  let : Fintype B := hB.fintype
  have hbad : ∀ H : B, ∃ ℓ, hilbertSamuelAt A a ℓ < H.val ℓ := by
    intro H
    have hn : ¬ ∀ ℓ, H.val ℓ ≤ hilbertSamuelAt A a ℓ := H.property.2
    obtain ⟨ℓ, hℓ⟩ := not_forall.mp hn
    exact ⟨ℓ, lt_of_not_ge hℓ⟩
  choose q hq using hbad
  let O : B → Set X := fun H => {x | ¬ H.val (q H) ≤ hilbertSamuelAt A x (q H)}
  have hO : ∀ H, IsOpen (O H) := fun H =>
    (isComplexAnalyticSubset_hilbertSamuelAt_superlevel A hA (q H) (H.val (q H))).isClosed.isOpen_compl
  let U : Opens X := ⟨(V : Set X) ∩ ⋂ H : B, O H,
    V.isOpen.inter (isOpen_iInter_of_finite hO)⟩
  have hbound : ∀ x ∈ U, ∀ ℓ : ℕ, hilbertSamuelAt A x ℓ ≤ hilbertSamuelAt A a ℓ := by
    intro x hx ℓ
    by_contra hnot
    have hxR : hilbertSamuelAt A x ∈ R := mem_image_of_mem _ hx.1
    have hxB : hilbertSamuelAt A x ∈ B := ⟨hxR, fun h => hnot (h ℓ)⟩
    let H : B := ⟨hilbertSamuelAt A x, hxB⟩
    have he := mem_iInter.mp hx.2 H
    exact he le_rfl
  refine ⟨U, ⟨haV, mem_iInter.mpr (fun H => not_le_of_gt (hq H))⟩, hbound, ?_⟩
  intro x hx
  exact Pi.toLex_monotone (hbound x hx)

end
end Hironaka.HironakaActualCompactHSMaximalProfile
