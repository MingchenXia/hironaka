import Hironaka.Resolution.HironakaG10GraphCentreUniformArtinRees
import Hironaka.Blowup.BlowupExistenceOriginIdeal

/-!
# Uniform Artin--Rees for arbitrary coherent ideals on actual Euclidean opens

Mathematics first:
`work/hironaka-codex-20261112/G10-COHERENT-CENTRE-MATHEMATICS.md`.
Blueprint: `hironaka-g10-coherent-centre-uniform-artin-rees.tex`.
Source: Hironaka (1975), Lemma 3.2, printed p. 531 (PDF p. 30).

Only the two original coherent ideals and an original point are inputs.
The chosen source generators are holomorphic solely on their actual
coherence neighbourhood. A genuine smaller Euclidean open carries the
graph map, and public whole-ideal pullback dictionaries return both
entire original stalk ideals. No global extension is assumed.

The final statements assume only original coherence, and additionally an
original compact subset for compact assembly. The complete ideals retain
non-radical multiplicities. Analytic quotient/open-space transport and the
full G10 flattening consumers remain separate obligations.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG10CoherentCentreUniformArtinRees

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaG10ChowUniformArtinRees HironakaG10RegularCentreUniformArtinRees
  HironakaG10GraphCentreUniformArtinRees
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci
  HironakaSmoothCentreRealDomainActualSheafStalk
  GermIdealPullbackCalculus FiniteGermIdealPullbackGenerators
  InvertibleIdealQuotient

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

private theorem whole_localInclusion {n : ℕ} (X V : Opens (ComplexModel n))
    (hVX : V ≤ X) (A : GermIdeal n X) (hA : A.IsCoherent) (y : V) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := n) (localInclusion X V hVX) A)
        y y (mem_chart_source _ y) =
      wholeChartStalkIdeal A (localInclusion X V hVX y) (localInclusion X V hVX y)
        (mem_chart_source _ (localInclusion X V hVX y)) := by
  have hh := map_wholeChartStalkIdeal_actual_pullback
    (localInclusion_holomorphic X V hVX) A hA y
  rw [localInclusion_germ X V hVX y] at hh
  change Ideal.map (RingHom.id _)
    (wholeChartStalkIdeal A (localInclusion X V hVX y) (localInclusion X V hVX y)
      (mem_chart_source _ (localInclusion X V hVX y))) = _ at hh
  simpa only [Ideal.map_id] using hh.symm

/-- Arbitrary original coherent ideals on a genuine Euclidean open have
ONE Artin--Rees exponent on ONE original neighbourhood of any point.
The local generators, their actual holomorphic graph, and the bound are
all selected internally from coherence. No uniformity hypothesis or
global holomorphic extension is an input. -/
theorem exists_original_coherent_uniform_artinRees {n : ℕ}
    (X : Opens (ComplexModel n)) (I K : GermIdeal n X)
    (hI : I.IsCoherent) (hK : K.IsCoherent) (x : X) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (wholeChartStalkIdeal I y y (mem_chart_source _ y))
        (wholeChartStalkIdeal K y y (mem_chart_source _ y)) α := by
  classical
  obtain ⟨U,hU,hxU,r,G,hG,hgen⟩ := hK x
  let V : Opens (ComplexModel n) :=
    ⟨(Subtype.val : X → ComplexModel n) '' U, X.isOpen.isOpenMap_subtype_val U hU⟩
  have hVX : V ≤ X := by
    rintro z ⟨y,hy,rfl⟩
    exact y.property
  let ι := localInclusion X V hVX
  have hι := localInclusion_holomorphic X V hVX
  have hιU : ∀ y : V, ι y ∈ U := by
    intro y
    obtain ⟨z,hz,he⟩ := y.property
    have hzy : ι y = z := Subtype.ext he.symm
    simpa only [hzy] using hz
  have hGhol : ∀ (i : Fin r) (y : V), HolomorphicAt n (G i) (ι y) :=
    fun i y => holomorphicAt_of_mdifferentiableOn hU (hG i) (hιU y)
  let F : V → ComplexModel r := fun y => WithLp.toLp 2 (fun i => G i (ι y))
  have hF : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ F := by
    intro y
    apply BlowupExistenceOriginIdeal.contMDiffAt_toLp
    intro i
    apply BlowupExistenceOriginIdeal.HolomorphicAt.contMDiffAt
    exact (hGhol i y).comp_contMDiff (Eventually.of_forall fun z => hι.contMDiffAt)
  let T : Opens (ComplexModel r) := ⊤
  let f : V → T := fun y => ⟨F y, mem_univ _⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel r) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff T f).mp hF
  have hKres : GermIdeal.pullback (m := n) ι K = functionCentreIdeal V T f := by
    refine GermIdeal.ext (funext fun y => funext fun g => propext ?_)
    have hh := mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun z => hι.contMDiffAt) K G (fun i => hGhol i y)
      (hgen (ι y) (hιU y)) g
    simpa only [functionCentreIdeal,
      HironakaActualCoherentWeightedCoefficientMarked.finiteFunctionIdeal,
      f, F, Function.comp_def] using hh
  let J := GermIdeal.pullback (m := n) ι I
  have hJ : J.IsCoherent := isCoherent_pullback hι hI
  let x' : V := ⟨x.val,⟨x,hxU,rfl⟩⟩
  obtain ⟨α,O,hO,hxO,hAR⟩ :=
    exists_uniform_artinRees_functionCentre_all_starts V T f hf J hJ x'
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
  rw [← hKres] at hh
  change IsArtinReesNumber
    (wholeChartStalkIdeal (GermIdeal.pullback (m := n) ι I) z z (mem_chart_source _ z))
    (wholeChartStalkIdeal (GermIdeal.pullback (m := n) ι K) z z (mem_chart_source _ z)) α at hh
  rwa [whole_localInclusion X V hVX I hI z, whole_localInclusion X V hVX K hK z] at hh

/-- The same internally selected local bound is a statement about the
actual original structure-sheaf stalk ideals, independently of charts. -/
theorem exists_original_coherent_uniform_actualStalk_artinRees {n : ℕ}
    (X : Opens (ComplexModel n)) (I K : GermIdeal n X)
    (hI : I.IsCoherent) (hK : K.IsCoherent) (x : X) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (actualWholeSheafStalkIdeal I y) (actualWholeSheafStalkIdeal K y) α := by
  obtain ⟨α,O,hO,hxO,hAR⟩ := exists_original_coherent_uniform_artinRees X I K hI hK x
  refine ⟨α,O,hO,hxO,fun y hy => ?_⟩
  have hh := isArtinReesNumber_map_ringEquiv (actualStalkChartEquiv (n := n) y).symm
    (hAR y hy)
  simpa only [← actualWholeSheafStalkIdeal_eq_map_chart] using hh

/-- Existing compact assembly applied to the actual original ideal families
gives ONE exponent on ONE open containing any original compact subset. -/
theorem exists_compact_coherent_uniform_actualStalk_artinRees {n : ℕ}
    (X : Opens (ComplexModel n)) (I K : GermIdeal n X)
    (hI : I.IsCoherent) (hK : K.IsCoherent) (Q : Set X) (hQ : IsCompact Q) :
    ∃ α : ℕ, ∃ O : Set X, IsOpen O ∧ Q ⊆ O ∧ ∀ y ∈ O,
      IsArtinReesNumber (actualWholeSheafStalkIdeal I y) (actualWholeSheafStalkIdeal K y) α := by
  let Y := ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) X
  let IZ : ∀ y : Y, Ideal (Y.presheaf.stalk y) := fun y => actualWholeSheafStalkIdeal I y
  let IS : ∀ y : Y, Ideal (Y.presheaf.stalk y) := fun y => actualWholeSheafStalkIdeal K y
  obtain ⟨O,α,hO,hQO,hAR⟩ := exists_artinReesOn_of_local (X := Y) IZ IS Q hQ
    (fun y _ => by
      obtain ⟨a,U,hU,hyU,hlocal⟩ :=
        exists_original_coherent_uniform_actualStalk_artinRees X I K hI hK y
      exact ⟨U,hU.mem_nhds hyU,a,hlocal⟩)
  exact ⟨α,O,hO,hQO,hAR⟩

end

end Hironaka.HironakaG10CoherentCentreUniformArtinRees
