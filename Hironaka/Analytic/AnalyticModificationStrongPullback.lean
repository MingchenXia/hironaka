import Hironaka.Analytic.AnalyticModificationLocalDiscrepancy
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Resolution.StrictTransformComposition

set_option autoImplicit false

/-! # Proper analytic-modification geometry and internally genuine strong pullback -/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AnalyticModificationStrongPullback

open Hironaka.PositiveClasses Hironaka.BlowupSequences
  AnalyticModificationLocalDiscrepancy GlobalPotentialPullback

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Proper closed-image geometry and the actual inverse on a dense
analytic complement supply surjectivity. -/
theorem surjective_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) : Function.Surjective π := by
  obtain ⟨_, B, s, _, _, _, _, _, hBi, _, _, hright, _⟩ := hπ.2.2
  have hsub : Bᶜ ⊆ range π := fun x hx => ⟨s x, hright x hx⟩
  have hdense : Dense (range π) := (interior_eq_empty_iff_dense_compl.mp hBi).mono hsub
  have hclosed : IsClosed (range π) := by
    simpa only [image_univ] using hπ.2.1.isClosedMap univ isClosed_univ
  have hrange : range π = univ := hclosed.closure_eq.symm.trans hdense.closure_eq
  intro x
  have hx : x ∈ range π := by rw [hrange]; exact mem_univ x
  exact hx

/-- Proper preimages internally supply upstairs compactness. -/
theorem compactSpace_of_isAnalyticModification [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) : CompactSpace Y := by
  apply isCompact_univ_iff.mp
  simpa only [preimage_univ] using hπ.2.1.isCompact_preimage (isCompact_univ : IsCompact (univ : Set X))

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
private theorem not_exceptional_of_left_inverse_germ
    {π : Y → X} {s : X → Y} {y : Y}
    (hπ : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π y)
    (hs : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s (π y))
    (heq : (s ∘ π) =ᶠ[𝓝 y] id) : y ∉ exceptionalLocus n π := by
  let I := 𝓘(ℂ, ComplexModel n)
  have hder : (mfderiv I I s (π y)).comp (mfderiv I I π y) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← mfderiv_comp y hs hπ, heq.mfderiv_eq, mfderiv_id]
    rfl
  have hinj : Function.Injective (mfderiv I I π y) := by
    have hli : Function.LeftInverse (mfderiv I I s (π y)) (mfderiv I I π y) :=
      fun v => DFunLike.congr_fun hder v
    exact hli.injective
  let T : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    { toFun := mfderiv I I π y
      map_add' := (mfderiv I I π y).map_add
      map_smul' := (mfderiv I I π y).map_smul }
  have hinjT : Function.Injective T := hinj
  have hbij : Function.Bijective (mfderiv I I π y) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := T)).mp hinjT⟩
  simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hbij

/-- The actual inverse on a target analytic complement produces the
literal existing isomorphism-over predicate. -/
theorem exists_isIsomorphismOver_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    ∃ B : Set X, IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧
      interior B = ∅ ∧ IsComplexAnalyticSubset (n := n) (π ⁻¹' B) ∧
      interior (π ⁻¹' B) = ∅ ∧ IsIsomorphismOver n π Bᶜ := by
  obtain ⟨A, B, s, hAc, hAa, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hπ.2.2
  have hne (y : Y) (hy : π y ∉ B) : y ∉ A := by
    intro hyA
    apply hy
    change y ∈ π ⁻¹' B
    rwa [hpre]
  refine ⟨B, hBc, hBa, hBi, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rwa [hpre]
  · rwa [hpre]
  · exact fun y hy => hy
  · intro y hy z hz heq
    exact (hleft y (hne y hy)).symm.trans ((congrArg s heq).trans (hleft z (hne z hz)))
  · intro x hx
    refine ⟨s x, ?_, hright x hx⟩
    change π (s x) ∉ B
    rwa [hright x hx]
  · apply Set.disjoint_left.mpr
    intro y hy hyE
    have heq : (s ∘ π) =ᶠ[𝓝 y] id := by
      filter_upwards [hAc.isOpen_compl.mem_nhds (hne y hy)] with z hz
      exact hleft z hz
    exact not_exceptional_of_left_inverse_germ ((hπ.1 y).mdifferentiableAt (by simp))
      ((hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hy)).mdifferentiableAt (by simp)) heq hyE

/-- Local inverse openness and source nondegeneracy supply finite values
on every original upstairs neighborhood. -/
theorem isThetaPshPotential_comp_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val (fun y => u (π y)) := by
  refine ⟨thetaPlurisubharmonic_comp hπ.1 hu.1, ?_⟩
  obtain ⟨A, _, _, hint, _, hnonexc⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  intro y O hO hyO
  have hnot : ¬ O ⊆ A := by
    intro hsub
    have h := interior_maximal hsub hO
    rw [hint] at h
    exact h hyO
  obtain ⟨y₀, hy₀O, hy₀A⟩ := Set.not_subset.mp hnot
  have hmap := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
    hπ.1 (hnonexc y₀ hy₀A)
  have himage : π '' O ∈ 𝓝 (π y₀) := by
    rw [← hmap]
    change π ⁻¹' (π '' O) ∈ 𝓝 y₀
    exact Filter.mem_of_superset (hO.mem_nhds hy₀O) (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨V, hVsub, hV, hy₀V⟩ := _root_.mem_nhds_iff.mp himage
  obtain ⟨x, hxV, hxne⟩ := hu.2 (π y₀) V hV hy₀V
  obtain ⟨z, hzO, hzx⟩ := hVsub hxV
  exact ⟨z, hzO, by simpa only [hzx] using hxne⟩

end
end Hironaka.AnalyticModificationStrongPullback
