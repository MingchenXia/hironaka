import Hironaka.Analytic.Unibranch.HironakaG10FrRouteG
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.ConstantRankImage

/-!
# Frisch's Lemma (IV,7) for constructible germs in `ℂᵐ` (ASM step 1)

Ambient form of `HironakaG10FrConstructible.isAnalyticSubset_of_isClosed_of_isLocallyConstructible` for the
germs of `HironakaG10FrRouteG` (J. Frisch, Invent. Math. 4 (1967), Lemme (IV,7), p. 133):
* `isComplexAnalyticSubset_preimage_of_isHolZeroSetOn`: a holomorphic zero set on an open `N` is analytic in
  the manifold `N`;
* `exists_opens_isComplexAnalyticSubset`: a set constructible near `p₀` and relatively closed near `p₀` is
  analytic in an open neighbourhood of `p₀`;
* `isComplexAnalyticSubset_of_isClosed_of_isConstructibleNear`: a closed subset of `ℂᵐ` constructible near
  every point is analytic.
Lane G10FR, run 0081. Blueprint: `hironaka-g10fr-route-g.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.Analytic.Unibranch.HironakaG10FrAmbientIV7

open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10FrRouteG

noncomputable section

variable {m : ℕ}

theorem complexChartAt_opens_apply (U : Opens (ComplexModel m)) (x y : U) :
    (complexChartAt (n := m) x).val y = (y : ComplexModel m) := by
  change chartAt (ComplexModel m) x y = (y : ComplexModel m)
  rw [Opens.chartAt_eq, chartAt_self_eq]
  rfl

theorem mem_complexChartAt_opens_source (U : Opens (ComplexModel m)) (x y : U) :
    y ∈ (complexChartAt (n := m) x).val.source := by
  change y ∈ (chartAt (ComplexModel m) x).source
  rw [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  simp

theorem mem_of_mem_complexChartAt_opens_target (U : Opens (ComplexModel m)) (x : U)
    {v : ComplexModel m} (hv : v ∈ (complexChartAt (n := m) x).val.target) : v ∈ U := by
  change v ∈ (chartAt (ComplexModel m) x).target at hv
  rw [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_def] at hv
  simp only [mfld_simps] at hv
  exact hv

/-- A holomorphic zero set on an open `N` is analytic in the manifold `N`. -/
theorem isComplexAnalyticSubset_preimage_of_isHolZeroSetOn (N : Opens (ComplexModel m))
    {A : Set (ComplexModel m)} (hA : IsHolZeroSetOn (N : Set (ComplexModel m)) A) :
    IsComplexAnalyticSubset (n := m) ((↑) ⁻¹' A : Set N) := by
  obtain ⟨r, g, hg, hgA⟩ := hA
  intro x
  refine ⟨{
    generatorCount := r
    generator := g
    coordinateNeighborhood := (complexChartAt (n := m) x).val.target
    isOpen_coordinateNeighborhood := (complexChartAt (n := m) x).val.open_target
    center_mem_coordinateNeighborhood :=
      (complexChartAt (n := m) x).val.map_source (mem_complexChartAt_opens_source N x x)
    coordinateNeighborhood_subset_target := Subset.rfl
    generator_holomorphic := fun i => (hg i).mono fun v hv =>
      mem_of_mem_complexChartAt_opens_target N x hv
    zeroLocus := ?_ }⟩
  intro y _ _
  rw [complexChartAt_opens_apply N x y]
  have h := Set.ext_iff.mp hgA (y : ComplexModel m)
  simp only [mem_inter_iff, mem_ofPred_eq] at h
  change (y : ComplexModel m) ∈ A ↔ _
  constructor
  · intro hy
    exact (h.mp ⟨hy, y.property⟩).2
  · intro hy
    exact (h.mpr ⟨y.property, hy⟩).1

/-- **Lemma (IV,7), local form.** A set constructible near `p₀` which is relatively closed near `p₀` is
analytic in an open neighbourhood of `p₀`. -/
theorem exists_opens_isComplexAnalyticSubset {E : Set (ComplexModel m)} {p₀ : ComplexModel m}
    (hE : IsConstructibleNear E p₀) {Ω : Set (ComplexModel m)} (hΩ : IsOpen Ω) (hpΩ : p₀ ∈ Ω)
    (hcl : closure (E ∩ Ω) ∩ Ω ⊆ E) :
    ∃ U : Opens (ComplexModel m), p₀ ∈ U ∧ IsComplexAnalyticSubset (n := m) ((↑) ⁻¹' E : Set U) := by
  classical
  obtain ⟨N, hN, hpN, Q, hQ, hEQ⟩ := hE
  let U : Opens (ComplexModel m) := ⟨N ∩ Ω, hN.inter hΩ⟩
  refine ⟨U, ⟨hpN, hpΩ⟩, ?_⟩
  have hQU : ∀ q ∈ Q, IsHolZeroSetOn (U : Set (ComplexModel m)) q.1 ∧
      IsHolZeroSetOn (U : Set (ComplexModel m)) q.2 := fun q hq =>
    ⟨(hQ q hq).1.mono inter_subset_left, (hQ q hq).2.mono inter_subset_left⟩
  have htrace : ((↑) ⁻¹' E : Set U) = ⋃ q ∈ Q, ((↑) ⁻¹' q.1 \ (↑) ⁻¹' q.2 : Set U) := by
    ext z
    have h := Set.ext_iff.mp hEQ (z : ComplexModel m)
    simp only [mem_inter_iff, mem_iUnion, Set.mem_sdiff, exists_prop] at h
    simp only [mem_preimage, mem_iUnion, Set.mem_sdiff, exists_prop]
    have hzN : (z : ComplexModel m) ∈ N := z.property.1
    constructor
    · intro hz
      exact (h.mp ⟨hz, hzN⟩).1
    · intro hz
      exact (h.mpr ⟨hz, hzN⟩).1
  have hclosed : closure ((↑) ⁻¹' E : Set U) ⊆ (↑) ⁻¹' E := by
    intro z hz
    have hz' : (z : ComplexModel m) ∈ closure (E ∩ Ω) := by
      have h1 := (continuous_subtype_val.closure_preimage_subset (f := ((↑) : U → ComplexModel m)) E) hz
      have hzU : (z : ComplexModel m) ∈ (U : Set (ComplexModel m)) := z.property
      have h2 : closure E ∩ (U : Set (ComplexModel m)) ⊆ closure (E ∩ U) :=
        (hN.inter hΩ).closure_inter
      exact closure_mono (inter_subset_inter_right E inter_subset_right) (h2 ⟨h1, hzU⟩)
    exact hcl ⟨hz', z.property.2⟩
  have hEq : ((↑) ⁻¹' E : Set U) = closure ((↑) ⁻¹' E : Set U) :=
    Subset.antisymm subset_closure hclosed
  rw [hEq, htrace, Finset.closure_biUnion]
  refine ConstantRankImage.isComplexAnalyticSubset_biUnion Q fun q hq => ?_
  exact ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
    (isComplexAnalyticSubset_preimage_of_isHolZeroSetOn U (hQU q hq).1)
    (isComplexAnalyticSubset_preimage_of_isHolZeroSetOn U (hQU q hq).2)

/-- **Lemma (IV,7) in `ℂᵐ`.** A closed set constructible near every point is analytic. -/
theorem isComplexAnalyticSubset_of_isClosed_of_isConstructibleNear {E : Set (ComplexModel m)}
    (hcl : IsClosed E) (hE : ∀ p, IsConstructibleNear E p) : IsComplexAnalyticSubset (n := m) E :=
  AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens fun p =>
    exists_opens_isComplexAnalyticSubset (hE p) isOpen_univ (mem_univ p)
      (fun _ hz => hcl.closure_subset (closure_mono inter_subset_left hz.1))

end
end Hironaka.Analytic.Unibranch.HironakaG10FrAmbientIV7
