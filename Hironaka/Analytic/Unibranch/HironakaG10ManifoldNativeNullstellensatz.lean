import Hironaka.Analytic.Unibranch.HironakaG10AnalyticNullstellensatzQuotient
import Hironaka.Resolution.HironakaG10PNIdealNoetherModel

/-! # Nullstellensatz for native stalk ideal families on a manifold -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ManifoldNativeNullstellensatz
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  HironakaG10PNIdealFamily AnalyticGermDecomposition
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticNullstellensatzQuotient

noncomputable section

/-- On an actual complex manifold, support containment of a locally generated
  native ideal family gives the corresponding stalk radical inclusion. -/
theorem wholeVanishing_le_radical_of_support_subset {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (J : ∀ x : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M,
      Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk x))
    (hJ : IsLocallyFinitelyGenerated
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M) J)
    (C : Set M) (x : M)
    (hC : ∀ᶠ y in 𝓝 x, J y ≠ ⊤ → y ∈ C) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x ≤ (J x).radical := by
  obtain ⟨U,hxU,r,s,hs⟩ := hJ x
  let e := chartAt (ComplexModel n) x
  let t := preferredChartInverseMap (n := n) x
  let F : Fin r → ComplexModel n → ℂ := fun i z => sectionExtension (n := n) (M := M) U (s i) (t z)
  have hF (i : Fin r) : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (F i) z := by
    change ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun z => (fun w => sectionExtension (n := n) (M := M) U (s i) (e.symm w)) (z + e x)) z
    exact translated_holomorphic (e x)
      (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x)
        (sectionExtension_holomorphicAt (n := n) (M := M) U (s i) x hxU))
  let E := actualStalkChartEquiv (n := n) x
  let I := Ideal.map E.toRingHom (J x)
  have hFmem (i : Fin r) : HolGerm.mk (F i) (hF i) ∈ I := by
    have hg : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.germ U x hxU (s i) ∈ J x := by
      rw [hs x hxU]
      exact Ideal.subset_span ⟨i,rfl⟩
    have hm := Ideal.mem_map_of_mem E.toRingHom hg
    change actualStalkChartEquiv (n := n) x
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x hxU (s i)) ∈ I at hm
    rw [actualStalkChartEquiv_germ] at hm
    exact hm
  have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ i, F i z = 0) → t z ∈ C := by
    have ht := tendsto_preferredChartInverseMap (n := n) x
    filter_upwards [ht.eventually hC, ht.eventually (U.isOpen.mem_nhds hxU)] with z hzC hzU hzF
    apply hzC
    intro htop
    have hle : J (t z) ≤ Ideal.comap (actualStalkChartEquiv (n := n) (t z)).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))) := by
      rw [hs (t z) hzU]
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simp only [SetLike.mem_coe, Ideal.mem_comap]
      change actualStalkChartEquiv (n := n) (t z)
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U (t z) hzU (s i)) ∈ _
      rw [actualStalkChartEquiv_germ, HolGerm.mem_maximalIdeal_iff]
      simpa [sectionChartRingHom,chartTranslatedGerm,translatedGerm,HolGerm.eval_mk,
        (chartAt (ComplexModel n) (t z)).left_inv (mem_chart_source (ComplexModel n) (t z))] using hzF i
    have hone : (1 : HolGerm (ComplexModel n)) ∈ IsLocalRing.maximalIdeal _ := by
      have h := hle (by rw [htop]; trivial : (1 : _) ∈ J (t z))
      simpa using h
    exact (IsLocalRing.maximalIdeal.isMaximal (HolGerm (ComplexModel n))).ne_top
      (by rw [Ideal.eq_top_iff_one]; exact hone)
  have hvan : Ideal.map E.toRingHom (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x) ≤
      AnalyticGermDecomposition.vanishingIdeal (t ⁻¹' C) := by
    rw [map_actualWholeSheafStalkIdeal]
    unfold wholeChartStalkIdeal
    apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hmem,rfl⟩
    change HolGerm.mk (fun z => f (t z))
      (translated_holomorphic (e x)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hf)) ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    exact (tendsto_preferredChartInverseMap (n := n) x).eventually hmem.2
  have hrad := vanishingIdeal_le_radical_of_local_zero_containment I F
    (fun i => ⟨hF i,hFmem i⟩) (t ⁻¹' C) hzero
  intro a ha
  have hm : E a ∈ I.radical := hrad (hvan (Ideal.mem_map_of_mem E.toRingHom ha))
  have hback := Ideal.mem_radical_iff.mp hm
  obtain ⟨k,hk⟩ := hback
  apply Ideal.mem_radical_iff.mpr
  refine ⟨k,?_⟩
  have : E (a ^ k) ∈ Ideal.map E.toRingHom (J x) := by simpa [I] using hk
  have hmap : Ideal.map E.toRingHom (J x) = Ideal.comap E.symm.toRingHom (J x) :=
    Ideal.map_comap_of_equiv E
  rw [hmap] at this
  change E.symm (E (a ^ k)) ∈ J x at this
  simpa using this

end
end Hironaka.Analytic.Unibranch.HironakaG10ManifoldNativeNullstellensatz
