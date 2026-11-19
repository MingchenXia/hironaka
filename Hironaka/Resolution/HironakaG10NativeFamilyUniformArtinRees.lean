import Hironaka.Resolution.HironakaG10CoherentCentreUniformArtinRees
import Hironaka.Resolution.HironakaG10PNIdealFamily

/-! # Uniform Artin–Rees for native ideal families on Euclidean opens -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10NativeFamilyUniformArtinRees

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaG10ChowUniformArtinRees HironakaG10RegularCentreUniformArtinRees
  HironakaG10CoherentCentreUniformArtinRees
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  GermIdealPullbackCalculus FiniteGermIdealPullbackGenerators InvertibleIdealQuotient

private def localInclusion {n : ℕ} (X V : Opens (ComplexModel n)) (hVX : V ≤ X) : V → X :=
  fun y => ⟨y.val,hVX y.property⟩

private theorem localInclusion_holomorphic {n : ℕ} (X V : Opens (ComplexModel n))
    (hVX : V ≤ X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localInclusion X V hVX) := by
  apply (ContMDiff.subtypeVal_comp_iff X _).mp
  exact contMDiff_subtype_val

private theorem localInclusion_germ {n : ℕ} (X V : Opens (ComplexModel n))
    (hVX : V ≤ X) (y : V) :
    actualHolomorphicGermPullback (localInclusion_holomorphic X V hVX) y =
      AlgHom.id ℂ (HolGerm (ComplexModel n)) := by
  have hc := actualHolomorphicGermPullback_comp
    (f := (Subtype.val : X → ComplexModel n)) (g := localInclusion X V hVX)
    contMDiff_subtype_val (localInclusion_holomorphic X V hVX) y
  have hl : actualHolomorphicGermPullback
      (contMDiff_subtype_val.comp (localInclusion_holomorphic X V hVX)) y =
        AlgHom.id ℂ (HolGerm (ComplexModel n)) :=
    actualHolomorphicGermPullback_val V y
  rw [hl, actualHolomorphicGermPullback_val X (localInclusion X V hVX y)] at hc
  simpa only [AlgHom.comp_id] using hc.symm

private theorem isCoherent_composed_native_sections {n : ℕ}
    (X V : Opens (ComplexModel n)) (hVX : V ≤ X) (D : Opens X)
    (hVD : ∀ y : V, localInclusion X V hVX y ∈ D) {r : ℕ}
    (s : Fin r → actualComplexSection (n := n) D) :
    (HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal (n := n)
      (fun i => sectionExtension D (s i) ∘ localInclusion X V hVX)).IsCoherent := by
  apply HironakaActualCoherentWeightedCoefficientMarked.isCoherent_finiteFunctionIdeal
  intro i y
  have hh := (sectionExtension_holomorphicAt D (s i)
    (localInclusion X V hVX y) (hVD y)).comp_contMDiff
      (Eventually.of_forall fun z => (localInclusion_holomorphic X V hVX).contMDiffAt)
  exact hh.self_of_nhds

private theorem whole_composed_native_sections {n : ℕ}
    (X V : Opens (ComplexModel n)) (hVX : V ≤ X) (D : Opens X)
    (hVD : ∀ y : V, localInclusion X V hVX y ∈ D) {r : ℕ}
    (s : Fin r → actualComplexSection (n := n) D) (y : V) :
    wholeChartStalkIdeal
        (HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal
          (fun i => sectionExtension D (s i) ∘ localInclusion X V hVX))
        y y (mem_chart_source _ y) =
      Ideal.map (actualStalkChartEquiv (n := n) (localInclusion X V hVX y)).toRingHom
        (Ideal.span (range fun i =>
          (actualComplexStructureSheaf (n := n) X).presheaf.germ D
            (localInclusion X V hVX y) (hVD y) (s i))) := by
  have hh (i : Fin r) := sectionExtension_holomorphicAt D (s i)
    (localInclusion X V hVX y) (hVD y)
  have hc (i : Fin r) := (hh i).comp_contMDiff
    (Eventually.of_forall fun z => (localInclusion_holomorphic X V hVX).contMDiffAt)
  rw [wholeChartStalkIdeal_eq_actual_generator_span _ y _ hc (fun _ => Iff.rfl),
    Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change _ = actualStalkChartEquiv (n := n) (localInclusion X V hVX y)
    ((actualComplexStructureSheaf (n := n) X).presheaf.germ D
      (localInclusion X V hVX y) (hVD y) (s i))
  rw [actualStalkChartEquiv_germ]
  have he := actualHolomorphicGermPullback_original_function
    (localInclusion_holomorphic X V hVX) y (sectionExtension D (s i)) (hh i)
  rw [localInclusion_germ X V hVX y] at he
  change _ = chartTranslatedGerm (localInclusion X V hVX y)
    (localInclusion X V hVX y) (mem_chart_source _ _) (sectionExtension D (s i)) (hh i)
  simpa only [AlgHom.id_apply] using he.symm

/-- Native local finite section presentations on an actual Euclidean open
produce one neighbourhood and one Artin--Rees exponent, with no original
GermIdeal presentation or supplied uniformity bound as an input. -/
theorem exists_native_locallyFG_uniform_artinRees {n : ℕ}
    (X : Opens (ComplexModel n))
    (I K : ∀ y : X, Ideal (actualComplexStructureStalk (n := n) y))
    (hI : HironakaG10PNIdealFamily.IsLocallyFinitelyGenerated
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) X) I)
    (hK : HironakaG10PNIdealFamily.IsLocallyFinitelyGenerated
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) X) K) (x : X) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (I y) (K y) α := by
  classical
  have hI' : ∀ x : X, ∃ (D : Opens X) (_hxD : x ∈ D) (r : ℕ)
      (s : Fin r → actualComplexSection (n := n) D),
      ∀ (y : X) (hy : y ∈ D), I y = Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) X).presheaf.germ D y hy (s i)) := hI
  have hK' : ∀ x : X, ∃ (D : Opens X) (_hxD : x ∈ D) (r : ℕ)
      (s : Fin r → actualComplexSection (n := n) D),
      ∀ (y : X) (hy : y ∈ D), K y = Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) X).presheaf.germ D y hy (s i)) := hK
  obtain ⟨D,hxD,r,s,hs⟩ := hI' x
  obtain ⟨E,hxE,t,u,hu⟩ := hK' x
  let V : Opens (ComplexModel n) :=
    ⟨(Subtype.val : X → ComplexModel n) '' ((D : Set X) ∩ E),
      X.isOpen.isOpenMap_subtype_val _ (D.isOpen.inter E.isOpen)⟩
  have hVX : V ≤ X := by
    rintro z ⟨y,hy,rfl⟩
    exact y.property
  let ι := localInclusion X V hVX
  have hιDE : ∀ y : V, ι y ∈ (D : Set X) ∩ E := by
    intro y
    obtain ⟨z,hz,he⟩ := y.property
    have hzy : ι y = z := Subtype.ext he.symm
    simpa only [hzy] using hz
  let A : GermIdeal n V :=
    HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal
      (fun i => sectionExtension D (s i) ∘ ι)
  let B : GermIdeal n V :=
    HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal
      (fun j => sectionExtension E (u j) ∘ ι)
  have hA : A.IsCoherent :=
    isCoherent_composed_native_sections X V hVX D (fun y => (hιDE y).1) s
  have hB : B.IsCoherent :=
    isCoherent_composed_native_sections X V hVX E (fun y => (hιDE y).2) u
  have hwholeA (y : V) : wholeChartStalkIdeal A y y (mem_chart_source _ y) =
      Ideal.map (actualStalkChartEquiv (n := n) (ι y)).toRingHom (I (ι y)) := by
    rw [hs (ι y) (hιDE y).1]
    exact whole_composed_native_sections X V hVX D (fun y => (hιDE y).1) s y
  have hwholeB (y : V) : wholeChartStalkIdeal B y y (mem_chart_source _ y) =
      Ideal.map (actualStalkChartEquiv (n := n) (ι y)).toRingHom (K (ι y)) := by
    rw [hu (ι y) (hιDE y).2]
    exact whole_composed_native_sections X V hVX E (fun y => (hιDE y).2) u y
  let x' : V := ⟨x.val,⟨x,⟨hxD,hxE⟩,rfl⟩⟩
  obtain ⟨α,O,hO,hxO,hAR⟩ := exists_original_coherent_uniform_artinRees V A B hA hB x'
  let W : Set X := ι '' O
  have hOambient : IsOpen ((Subtype.val : V → ComplexModel n) '' O) :=
    V.isOpen.isOpenMap_subtype_val O hO
  have hWeq : W = (Subtype.val : X → ComplexModel n) ⁻¹'
      ((Subtype.val : V → ComplexModel n) '' O) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,he⟩
      exact ⟨z,hz,Subtype.ext he⟩
  have hW : IsOpen W := by
    rw [hWeq]
    exact hOambient.preimage continuous_subtype_val
  have hxι : ι x' = x := Subtype.ext rfl
  refine ⟨α,W,hW,⟨x',hxO,hxι⟩,?_⟩
  rintro y ⟨z,hz,rfl⟩
  have hh := hAR z hz
  rw [hwholeA z,hwholeB z] at hh
  have hback := isArtinReesNumber_map_ringEquiv
    (actualStalkChartEquiv (n := n) (ι z)).symm hh
  simpa only [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
    Ideal.map_id] using hback

end

end Hironaka.HironakaG10NativeFamilyUniformArtinRees
