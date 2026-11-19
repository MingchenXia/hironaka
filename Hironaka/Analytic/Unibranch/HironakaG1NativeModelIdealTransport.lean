import Hironaka.Analytic.Unibranch.HironakaG1OriginalSingularCleanup

/-! # Whole original ideal transport between actual native manifold models

The actual full native isomorphism supplies its held genuine biholomorphism.
Whole ideal pullback is derived from the native stalk dictionaries, without
an ideal-correctness or cleanup-comparison premise. Blueprint first:
`hironaka-g1-native-model-ideal-transport.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeModelIdealTransport

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaEmbeddedNativeMorphism
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaNativePulledIdealSheaf HironakaSingularModuleSheafStalk RelativePrincipalizationSpan
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  HironakaG1OriginalSingularCleanup

noncomputable section

section Faithfulness

variable {n : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W]

private theorem originalGerm_mem_wholeIdeal_iff (A : GermIdeal n W) (hA : A.IsCoherent)
    (x : W) (g : W → ℂ) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x g hg ∈ actualWholeSheafStalkIdeal A x ↔ A.mem x g := by
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := hA x
  have hshol (i : Fin N) : HolomorphicAt n (s i) x :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hxU
  have hJ : actualWholeSheafStalkIdeal A x =
      Ideal.span (range fun i => actualOriginalFunctionGerm x (s i) (hshol i)) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨f, hf, hAf, rfl⟩
      obtain ⟨_, K, t, a, ht, ha, hsum⟩ := (hgen x hxU f).mp hAf
      choose k hk using ht
      have hthol (j : Fin K) : HolomorphicAt n (t j) x := (hk j) ▸ hshol (k j)
      have hsumhol : HolomorphicAt n (fun z => ∑ j, a j z * t j z) x :=
        HolomorphicAt.sum _ fun j _ => (ha j).mul (hthol j)
      rw [originalGerm_congr x hf hsumhol hsum, originalGerm_sum_mul x a t ha hthol hsumhol]
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k j, ?_⟩)
      exact originalGerm_congr x (hshol (k j)) (hthol j) (by rw [hk j])
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨s i, hshol i,
        (hgen x hxU (s i)).mpr
          (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hshol i)), rfl⟩
  constructor
  · intro hmem
    rw [hJ] at hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    choose a ha hac using fun i => exists_originalGerm_eq x (c i)
    have hsumhol : HolomorphicAt n (fun z => ∑ i, a i z * s i z) x :=
      HolomorphicAt.sum _ fun i _ => (ha i).mul (hshol i)
    apply (hgen x hxU g).mpr
    refine ⟨hg, N, s, a, fun i => ⟨i, rfl⟩, ha, ?_⟩
    apply eventuallyEq_of_originalGerm_eq x hg hsumhol
    rw [originalGerm_sum_mul x a s ha hshol hsumhol, ← hc]
    simp only [hac]
  · intro hAg
    exact Ideal.subset_span ⟨g, hg, hAg, rfl⟩

private theorem coherentIdeal_eq_of_wholeStalk_eq {A B : GermIdeal n W}
    (hA : A.IsCoherent) (hB : B.IsCoherent)
    (he : ∀ x : W, actualWholeSheafStalkIdeal A x = actualWholeSheafStalkIdeal B x) : A = B := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro h
    have hg := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA h
    exact (originalGerm_mem_wholeIdeal_iff B hB x g hg).mp
      ((he x) ▸ (originalGerm_mem_wholeIdeal_iff A hA x g hg).mpr h)
  · intro h
    have hg := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hB h
    exact (originalGerm_mem_wholeIdeal_iff A hA x g hg).mp
      ((he x).symm ▸ (originalGerm_mem_wholeIdeal_iff B hB x g hg).mpr h)

end Faithfulness

section Pullback

variable {n m : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W] {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V] {Z : LocallyRingedSpace.{0}}
  (B : SheafOfModules.{0} (forgetRing Z.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Z.toSheafedSpace.sheaf))

/-- The WHOLE native model ideal commutes with actual holomorphic pullback,
in arbitrary dimensions and before any radical or support replacement. -/
theorem modelGermIdeal_pullback [B.IsFiniteType]
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set W) ⟶ Z) {f : V → W}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    GermIdeal.pullback (m := m) f (modelGermIdeal B b F) =
      modelGermIdeal B b (actualSubspaceMap hf (fun y (_ : y ∈ (univ : Set V)) => mem_univ (f y)) ≫ F) := by
  apply coherentIdeal_eq_of_wholeStalk_eq
    (GermIdealPullbackCalculus.isCoherent_pullback hf (isCoherent_modelGermIdeal B b F))
    (isCoherent_modelGermIdeal B b _)
  intro x
  have hpull := map_wholeIdeal_pullback_modelGermIdeal B b F hf (modelPoint x)
  have hmodel := map_wholeIdeal_modelGermIdeal B b
    (actualSubspaceMap hf (fun y (_ : y ∈ (univ : Set V)) => mem_univ (f y)) ≫ F) (modelPoint x)
  have he := hpull.trans hmodel.symm
  let φ := ((actualSubspaceInclusion (n := m) (univ : Set V)).stalkMap (modelPoint x)).hom
  have hφ : Function.Bijective φ :=
    ConcreteCategory.bijective_of_isIso
      ((actualSubspaceInclusion (n := m) (univ : Set V)).stalkMap (modelPoint x))
  have he' := congrArg (Ideal.comap φ) he
  dsimp only [φ] at hφ he'
  simpa only [Ideal.comap_map_of_bijective _ hφ] using he'

end Pullback

section NativeModels

variable {n : ℕ} {M N : CMfd.{0} n}

/-- The held genuine native biholomorphism induces the SAME entire original
native isomorphism, including the full quotient-sheaf and scalar map. -/
theorem modelBiholomorphism_native (e : wholeModel (n := n) N ≅ wholeModel (n := n) M) :
    nativeMorphism (nativeDiffeomorph (isoLeft e) (Over.w e.hom.hom)).contMDiff = e.hom := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro x
  apply Subtype.ext
  rfl

/-- Different actual native models pull back the ENTIRE original singular
ideal automatically; no ideal-comparison packet is an input. -/
theorem originalSingularGermIdeal_transport (X : SourceReducedComplexSpace)
    (e : wholeModel (n := n) N ≅ wholeModel (n := n) M) (a : wholeModel (n := n) M ⟶ X) :
    originalSingularGermIdeal X (e.hom ≫ a) =
      GermIdeal.pullback (m := n) (nativeDiffeomorph (isoLeft e) (Over.w e.hom.hom))
        (originalSingularGermIdeal X a) := by
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  have h := modelGermIdeal_pullback
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) a.hom.left
    (nativeDiffeomorph (isoLeft e) (Over.w e.hom.hom)).contMDiff
  change GermIdeal.pullback (m := n) (nativeDiffeomorph (isoLeft e) (Over.w e.hom.hom))
    (originalSingularGermIdeal X a) =
      originalSingularGermIdeal X
        (nativeMorphism (nativeDiffeomorph (isoLeft e) (Over.w e.hom.hom)).contMDiff ≫ a) at h
  rw [modelBiholomorphism_native] at h
  exact h.symm

end NativeModels
end
end Hironaka.Analytic.Unibranch.HironakaG1NativeModelIdealTransport
