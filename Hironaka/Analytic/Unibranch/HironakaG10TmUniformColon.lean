import Hironaka.Resolution.HironakaG10NativeFamilyUniformArtinRees
import Hironaka.Coherence.CoherentIdealColon
import Hironaka.Resolution.HironakaLegacyCoherentIdealFiniteType
import Hironaka.Resolution.HironakaG10PNIdealNoetherOpen
import Hironaka.Resolution.HironakaAnalyticBaseChangeQuotientModel
import Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees
import Hironaka.Resolution.HironakaG10FiniteIdealFamilyArithmetic

/-!
# A locally uniform colon power on Euclidean opens (lane G10TM, plan item G10-03-06.a, part P1)

For two locally finitely generated native ideal families `A`, `B` on an open `U ⊆ ℂⁿ`, every point has a
neighbourhood `O` and one exponent `N` such that at every `y ∈ O` where SOME power `B_y^m` lies in `A_y`,
already `B_y^N ≤ A_y`.

Proof: near the point, `A` and `B` are the whole stalks of coherent germ ideals `A'`, `B'`; the iterated
colons `C₀ = A'`, `C_{k+1} = (C_k : B')` are coherent (Oka, `CoherentIdealColon.isCoherent_colon_of_isCoherent`)
and their whole stalks are the iterated colon ideals
(`wholeChartStalkIdeal_colon`, after the PrimeNov16 chart dictionary), i.e. `A_y : B_y^k`.
Their native whole stalk families form an ascending chain of locally finitely generated families, which is
stationary near the point (`HironakaG10PNIdealNoetherOpen.hasLocalNoetherProperty_manifoldOpen`).  At a point
where `B^m ≤ A`, the `m`-th colon contains `1`, hence so does the stationary one.  Only stalk statements are
transported back (through the chart ring isomorphisms).
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaLegacyCoherentIdealSheaf HironakaLegacyCoherentIdealFiniteType
  HironakaG10PNIdealFamily

/-! ### Iterated colons -/

/-- Membership in an iterated colon: `x ∈ c_k` iff `x * g ∈ a` for every `g ∈ b^k`. -/
theorem mem_iterColon {R : Type*} [CommRing R] (a b : Ideal R) (c : ℕ → Ideal R) (h0 : c 0 = a)
    (hs : ∀ k, c (k + 1) = (c k).colon (b : Set R)) :
    ∀ (k : ℕ) (x : R), x ∈ c k ↔ ∀ g ∈ b ^ k, x * g ∈ a
  | 0, x => by
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact ⟨fun hx g _ => a.mul_mem_right g hx, fun h => by simpa using h 1 Submodule.mem_top⟩
  | k + 1, x => by
    rw [hs k, Submodule.mem_colon]
    constructor
    · intro h g hg
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      · intro u hu v hv
        have h1 := (mem_iterColon a b c h0 hs k (x • v)).mp (h v hv) u hu
        simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h1
      · intro u v hu hv
        rw [mul_add]
        exact a.add_mem hu hv
    · intro h v hv
      rw [mem_iterColon a b c h0 hs k]
      intro g hg
      have : g * v ∈ b ^ (k + 1) := by
        rw [pow_succ]
        exact Submodule.mul_mem_mul hg hv
      simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h (g * v) this

private theorem comap_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) : Ideal.comap e.toRingHom (Ideal.map e.toRingHom I) = I :=
  Ideal.comap_map_of_bijective _ e.bijective

/-- `1` lies in the `k`-th iterated colon iff `b^k ≤ a`. -/
theorem one_mem_iterColon_iff {R : Type*} [CommRing R] (a b : Ideal R) (c : ℕ → Ideal R)
    (h0 : c 0 = a) (hs : ∀ k, c (k + 1) = (c k).colon (b : Set R)) (k : ℕ) :
    (1 : R) ∈ c k ↔ b ^ k ≤ a := by
  rw [mem_iterColon a b c h0 hs k]
  exact ⟨fun h g hg => by simpa using h g hg, fun h g hg => by simpa using h hg⟩

/-! ### The whole-stalk colon dictionary
(copied from `PrimeNov16AnalyticNormalizationCoherentChartDictionary`, whose Hironaka module is outside the G10
import closure) -/

section ColonDictionary

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem chart_mem_whole_iff (I : GermIdeal n M) (hI : I.IsCoherent)
    (x : M) (f : M → ℂ) (hf : HolomorphicAt n f x) :
    chartTranslatedGerm x x (mem_chart_source _ x) f hf ∈
      wholeChartStalkIdeal I x x (mem_chart_source _ x) ↔ I.mem x f := by
  obtain ⟨U, _hU, hxU, s, G, hsource, _hG, hfamily⟩ :=
    exists_coherent_whole_stalk_original_columns I hI x
  obtain ⟨_hGx, hmem, hwhole⟩ := hfamily x hxU
  rw [hwhole]
  exact (hmem f hf).symm

private theorem exists_original_function_chart (x : M) (a : HolGerm (ComplexModel n)) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x),
      chartTranslatedGerm x x (mem_chart_source _ x) f hf = a := by
  obtain ⟨r, hr⟩ := (actualStalkChartEquiv (n := n) x).surjective a
  obtain ⟨U, hxU, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨sectionExtension U s, sectionExtension_holomorphicAt U s x hxU, ?_⟩
  exact (actualStalkChartEquiv_germ U x hxU s).symm.trans hr

private theorem chartTranslatedGerm_mul (x : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun z => f z * g z) (hf.mul hg) =
      chartTranslatedGerm x x (mem_chart_source _ x) f hf *
        chartTranslatedGerm x x (mem_chart_source _ x) g hg := by
  simp only [chartTranslatedGerm, translatedGerm]
  exact HolGerm.mk_mul _ _ _ _

/-- The whole stalk of the colon of two coherent germ ideals is the colon of their whole stalks. -/
theorem wholeChartStalkIdeal_colon (I J : GermIdeal n M)
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (x : M) :
    wholeChartStalkIdeal (InvertibleIdealQuotient.colon I J) x x (mem_chart_source _ x) =
      (wholeChartStalkIdeal I x x (mem_chart_source _ x)).colon
        (wholeChartStalkIdeal J x x (mem_chart_source _ x) : Set (HolGerm (ComplexModel n))) := by
  have hcolon := CoherentIdealColon.isCoherent_colon_of_isCoherent hI hJ
  ext a
  obtain ⟨f, hf, rfl⟩ := exists_original_function_chart x a
  rw [chart_mem_whole_iff _ hcolon x f hf]
  constructor
  · intro hfc
    apply Submodule.mem_colon.mpr
    intro b hb
    obtain ⟨g, hg, rfl⟩ := exists_original_function_chart x b
    have hJg := (chart_mem_whole_iff J hJ x g hg).mp hb
    have hm := (chart_mem_whole_iff I hI x (fun z => g z * f z) (hg.mul hf)).mpr (hfc.2 g hJg)
    rw [chartTranslatedGerm_mul] at hm
    simpa only [smul_eq_mul, mul_comm] using hm
  · intro hfc
    refine ⟨hf, ?_⟩
    intro g hgJ
    have hg := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hgJ
    have hgmem := (chart_mem_whole_iff J hJ x g hg).mpr hgJ
    have hm := (Submodule.mem_colon.mp hfc) _ hgmem
    apply (chart_mem_whole_iff I hI x (fun z => g z * f z) (hg.mul hf)).mp
    rw [chartTranslatedGerm_mul]
    simpa only [smul_eq_mul, mul_comm] using hm

end ColonDictionary

/-! ### Germ ideals of native sections (as in `HironakaG10NativeFamilyUniformArtinRees`) -/

private def localInclusion {n : ℕ} (X V : Opens (ComplexModel n)) (hVX : V ≤ X) : V → X :=
  fun y => ⟨y.val, hVX y.property⟩

private theorem localInclusion_holomorphic {n : ℕ} (X V : Opens (ComplexModel n))
    (hVX : V ≤ X) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (localInclusion X V hVX) := by
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

/-! ### The iterated colon chain of coherent germ ideals -/

/-- The iterated colons `C₀ = A`, `C_{k+1} = (C_k : B)` of germ ideals. -/
def colonChain {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (A B : GermIdeal n M) : ℕ → GermIdeal n M
  | 0 => A
  | k + 1 => InvertibleIdealQuotient.colon (colonChain A B k) B

theorem isCoherent_colonChain {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : GermIdeal n M} (hA : A.IsCoherent) (hB : B.IsCoherent) :
    ∀ k, (colonChain A B k).IsCoherent
  | 0 => hA
  | k + 1 => CoherentIdealColon.isCoherent_colon_of_isCoherent (isCoherent_colonChain hA hB k) hB

/-- The native whole stalks of a coherent germ ideal form a locally finitely generated family. -/
theorem isLocallyFinitelyGenerated_actualWhole {n : ℕ} (V : Opens (ComplexModel n))
    (A : GermIdeal n V) (hA : A.IsCoherent) :
    IsLocallyFinitelyGenerated (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V)
      (fun y => actualWholeSheafStalkIdeal A y) := by
  intro x
  obtain ⟨U, hxU, r, s, _, hspan⟩ := exists_local_finite_generators A hA x
  refine ⟨U, hxU, r, fun i => (actualIdealModuleInclusion A).val.app (Opposite.op U) (s i), ?_⟩
  intro y hy
  exact (actualIdealModule_stalkRange A hA y).symm.trans (hspan y hy)

/-! ### The local uniform colon power -/

/-- **Locally uniform colon power on a Euclidean open.**  For locally finitely generated native ideal
families `A`, `B` on an open `U ⊆ ℂⁿ`, every point has an open neighbourhood `O` and one exponent `N`
such that `B_y^N ≤ A_y` at every `y ∈ O` where some power of `B_y` lies in `A_y`. -/
theorem exists_local_uniform_colon_power {n : ℕ} (X : Opens (ComplexModel n))
    (I K : ∀ y : X, Ideal (actualComplexStructureStalk (n := n) y))
    (hI : IsLocallyFinitelyGenerated (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) X) I)
    (hK : IsLocallyFinitelyGenerated (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) X) K)
    (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ N : ℕ, ∀ y ∈ O, (∃ m, K y ^ m ≤ I y) → K y ^ N ≤ I y := by
  classical
  have hI' : ∀ x : X, ∃ (D : Opens X) (_hxD : x ∈ D) (r : ℕ)
      (s : Fin r → actualComplexSection (n := n) D),
      ∀ (y : X) (hy : y ∈ D), I y = Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) X).presheaf.germ D y hy (s i)) := hI
  have hK' : ∀ x : X, ∃ (D : Opens X) (_hxD : x ∈ D) (r : ℕ)
      (s : Fin r → actualComplexSection (n := n) D),
      ∀ (y : X) (hy : y ∈ D), K y = Ideal.span (range fun i =>
        (actualComplexStructureSheaf (n := n) X).presheaf.germ D y hy (s i)) := hK
  obtain ⟨D, hxD, r, s, hs⟩ := hI' x
  obtain ⟨E, hxE, t, u, hu⟩ := hK' x
  let V : Opens (ComplexModel n) :=
    ⟨(Subtype.val : X → ComplexModel n) '' ((D : Set X) ∩ E),
      X.isOpen.isOpenMap_subtype_val _ (D.isOpen.inter E.isOpen)⟩
  have hVX : V ≤ X := by
    rintro z ⟨y, hy, rfl⟩
    exact y.property
  let ι := localInclusion X V hVX
  have hιDE : ∀ y : V, ι y ∈ (D : Set X) ∩ E := by
    intro y
    obtain ⟨z, hz, he⟩ := y.property
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
  -- the chain of whole stalk ideals
  have hC := isCoherent_colonChain hA hB
  let c : V → ℕ → Ideal (HolGerm (ComplexModel n)) := fun y k =>
    wholeChartStalkIdeal (colonChain A B k) y y (mem_chart_source _ y)
  have hc0 (y : V) : c y 0 = wholeChartStalkIdeal A y y (mem_chart_source _ y) := rfl
  have hcs (y : V) (k : ℕ) : c y (k + 1) =
      (c y k).colon (wholeChartStalkIdeal B y y (mem_chart_source _ y) : Set (HolGerm (ComplexModel n))) :=
    wholeChartStalkIdeal_colon (colonChain A B k) B (hC k) hB y
  -- the native chain on `V`
  let T : ℕ → ∀ y : V, Ideal (actualComplexStructureStalk (n := n) y) :=
    fun k y => actualWholeSheafStalkIdeal (colonChain A B k) y
  have hTc (k : ℕ) (y : V) :
      Ideal.map (actualStalkChartEquiv (n := n) y).toRingHom (T k y) = c y k :=
    map_actualWholeSheafStalkIdeal (colonChain A B k) y
  have hTle (k k' : ℕ) (y : V) : T k y ≤ T k' y ↔ c y k ≤ c y k' := by
    rw [← hTc k y, ← hTc k' y]
    constructor
    · exact Ideal.map_mono
    · intro h
      have h' := Ideal.comap_mono (f := (actualStalkChartEquiv (n := n) y).toRingHom) h
      rwa [comap_map_ringEquiv, comap_map_ringEquiv] at h'
  have hasc : IsAscending (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V) T := by
    intro k y
    rw [hTle k (k + 1) y, hcs y k]
    intro g hg
    rw [Submodule.mem_colon]
    intro b _
    exact (c y k).mul_mem_right b hg
  have hfg : ∀ k, IsLocallyFinitelyGenerated
      (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) V) (T k) :=
    fun k => isLocallyFinitelyGenerated_actualWhole V (colonChain A B k) (hC k)
  let x' : V := ⟨x.val, ⟨x, ⟨hxD, hxE⟩, rfl⟩⟩
  obtain ⟨N, W, hxW, hW⟩ :=
    HironakaG10PNIdealNoetherOpen.hasLocalNoetherProperty_manifoldOpen V T hasc hfg x'
  -- the key equivalence at a point of `V`
  have hkey (y : V) (k : ℕ) : (1 : HolGerm (ComplexModel n)) ∈ c y k ↔ K (ι y) ^ k ≤ I (ι y) := by
    rw [one_mem_iterColon_iff (wholeChartStalkIdeal A y y (mem_chart_source _ y))
      (wholeChartStalkIdeal B y y (mem_chart_source _ y)) (c y) (hc0 y) (hcs y) k,
      hwholeA y, hwholeB y, ← Ideal.map_pow]
    constructor
    · intro h
      have h' := Ideal.comap_mono (f := (actualStalkChartEquiv (n := n) (ι y)).toRingHom) h
      rwa [comap_map_ringEquiv, comap_map_ringEquiv] at h'
    · exact Ideal.map_mono
  -- transport the neighbourhood to `X`
  let W' : Set V := W.1
  have hW'o : IsOpen W' := W.2
  let O : Set X := ι '' W'
  have hOambient : IsOpen ((Subtype.val : V → ComplexModel n) '' W') :=
    V.isOpen.isOpenMap_subtype_val _ hW'o
  have hOeq : O = (Subtype.val : X → ComplexModel n) ⁻¹'
      ((Subtype.val : V → ComplexModel n) '' W') := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨z, hz, Subtype.ext he⟩
  have hO : IsOpen O := by
    rw [hOeq]
    exact hOambient.preimage continuous_subtype_val
  have hxι : ι x' = x := Subtype.ext rfl
  refine ⟨O, hO, ⟨x', hxW, hxι⟩, N, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ ⟨m, hm⟩
  have hmN : K (ι z) ^ max m N ≤ I (ι z) :=
    (Ideal.pow_le_pow_right (le_max_left m N)).trans hm
  have h1 : (1 : HolGerm (ComplexModel n)) ∈ c z (max m N) := (hkey z (max m N)).mpr hmN
  have hstat := hW (max m N) (le_max_right m N) z hz
  have h2 : c z (max m N) ≤ c z N := (hTle (max m N) N z).mp hstat
  exact (hkey z N).mp (h2 h1)

/-! ### Transport of the stalk condition along ring maps -/

/-- Along a surjective ring map, a power condition on preimages is the power condition itself. -/
theorem comap_pow_le_comap_iff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (K I : Ideal S) (m : ℕ) :
    Ideal.comap f K ^ m ≤ Ideal.comap f I ↔ K ^ m ≤ I := by
  constructor
  · intro h
    have h' := Ideal.map_mono (f := f) h
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective f hf,
      Ideal.map_comap_of_surjective f hf] at h'
  · intro h
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_comap_of_surjective f hf]
    exact h

/-- Along a bijective ring map, a power condition on images is the power condition itself. -/
theorem map_pow_le_map_iff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) (K I : Ideal R) (m : ℕ) :
    Ideal.map f K ^ m ≤ Ideal.map f I ↔ K ^ m ≤ I := by
  rw [← Ideal.map_pow]
  constructor
  · intro h
    have h' := Ideal.comap_mono (f := f) h
    rwa [Ideal.comap_map_of_bijective f hf, Ideal.comap_map_of_bijective f hf] at h'
  · exact Ideal.map_mono

/-! ### Embedded analytic models -/

open HironakaActualAnalyticSubspace HironakaG10PNIdealNoetherModel in
/-- **Locally uniform colon power on an embedded analytic model** `(C, 𝒪_U/𝓘_C)`. -/
theorem exists_local_uniform_colon_power_model {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C)
    (I K : ∀ c : actualSubspaceLocallyRingedSpace (n := n) C,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk c))
    (hI : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) C) I)
    (hK : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) C) K)
    (c : actualSubspaceLocallyRingedSpace (n := n) C) :
    ∃ O : Set (actualSubspaceLocallyRingedSpace (n := n) C), IsOpen O ∧ c ∈ O ∧
      ∃ N : ℕ, ∀ y ∈ O, (∃ m, K y ^ m ≤ I y) → K y ^ N ≤ I y := by
  have hpI := pushFamily_isLocallyFinitelyGenerated hC I hI
  have hpK := pushFamily_isLocallyFinitelyGenerated hC K hK
  obtain ⟨O', hO', hcO', N, hN⟩ := exists_local_uniform_colon_power U (pushFamily C I)
    (pushFamily C K) hpI hpK (c : C).val
  refine ⟨Subtype.val ⁻¹' O', hO'.preimage continuous_subtype_val, hcO', N, ?_⟩
  intro y hy ⟨m, hm⟩
  have hsurj := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C y
  have hpush (J : ∀ c : actualSubspaceLocallyRingedSpace (n := n) C,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk c)) :
      pushFamily C J (y : C).val =
        Ideal.comap ((actualSubspaceInclusion (n := n) C).stalkMap y).hom (J y) :=
    pushFamily_of_mem C J y
  have h1 : pushFamily C K (y : C).val ^ m ≤ pushFamily C I (y : C).val := by
    rw [hpush K, hpush I]
    exact (comap_pow_le_comap_iff _ hsurj (K y) (I y) m).mpr hm
  have h2 := hN (y : C).val hy ⟨m, h1⟩
  rw [hpush K, hpush I] at h2
  exact (comap_pow_le_comap_iff _ hsurj (K y) (I y) N).mp h2

/-! ### Native reduced complex spaces -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaResolutionSpaceComplex
  HironakaIntrinsicMorphismGluingAnalytic HironakaG10PNIdealNoetherModel HironakaG10HirIdealGerms
  HironakaG10FiniteIdealFamilyArithmetic

/-- The local analytic-model clause passes through an open immersion over the complex point
(copied from the private `HironakaG10SourceOpenUniformArtinRees.charts_of_openImmersion`). -/
private theorem charts_of_openImmersion {H T : LocallyRingedSpace}
    (σH : H ⟶ complexPoint) (σT : T ⟶ complexPoint)
    (hT : ∀ x : T, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ T,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σT = (modelOver U C).hom ∧ x ∈ range i.base)
    (j : H ⟶ T) [hj : LocallyRingedSpace.IsOpenImmersion j] (hjp : j ≫ σT = σH) :
    ∀ x : H, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ H,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σH = (modelOver U C).hom ∧
          x ∈ range i.base := by
  intro x
  obtain ⟨n, V, C, hC, i, hi, hip, c, hcx⟩ := hT (j.base x)
  change C at c
  change actualSubspaceLocallyRingedSpace (n := n) C ⟶ T at i
  change i.base c = j.base x at hcx
  change i ≫ σT = subspacePointMap (n := n) C at hip
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let Q : Opens (TopCat.of C) :=
    ⟨i.base ⁻¹' range j.base, hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  obtain ⟨O, hO, hOQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let A : Opens V := ⟨O, hO⟩
  have hcA : c.val ∈ A := by
    change c ∈ Subtype.val ⁻¹' O
    rw [hOQ]
    change i.base c ∈ range j.base
    rw [hcx]
    exact ⟨x, rfl⟩
  let C' : Set A := (Subtype.val : A → V) ⁻¹' C
  let R := actualOpenSubspaceMap (n := n) C A ≫ i
  have : LocallyRingedSpace.IsOpenImmersion R := by
    dsimp [R]
    infer_instance
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (⟨y.val.val, y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val, y.property⟩ : C) ∈ (Q : Set C)
      rw [← hOQ]
      exact y.val.property
    exact hy
  let L := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : L ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  have : LocallyRingedSpace.IsOpenImmersion L := by
    let : IsIso (pullback.snd j R) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j R hR
    dsimp [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hLp : L ≫ σH = subspacePointMap (n := n) C' := by
    rw [← hjp, ← Category.assoc, hfac]
    dsimp [R]
    rw [Category.assoc, hip]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let c' : C' := ⟨⟨c.val, hcA⟩, c.property⟩
  have hLc : L.base c' = x := by
    apply hj.base_open.injective
    calc
      j.base (L.base c') = R.base c' := congrArg (fun f => f.base c') hfac
      _ = j.base x := hcx
  have hC' : IsComplexAnalyticSubset (n := n) C' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC A
  obtain ⟨V', D, hD, k, hk, hkp, z, hzc⟩ := exists_model_chart hC' c'
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, V', D, hD, k ≫ L, inferInstance, ?_, z, ?_⟩
  · rw [Category.assoc, hLp]
    exact hkp
  · change L.base (k.base z) = x
    rw [hzc, hLc]

/-- **Locally uniform colon power on a reduced complex space**, for families generated on an open
domain `V`: every point of `V` has an open neighbourhood and one exponent `N` with `I_y^N ≤ J_y` at
every `y` of it where some power of `I_y` lies in `J_y`. -/
theorem exists_local_uniform_colon_power_on (X : SourceReducedComplexSpace)
    (V : Set X.obj.left) (hV : IsOpen V)
    (I J : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X.obj.left V I)
    (hJ : IsLocallyFinitelyGeneratedOn X.obj.left V J) (x : X.obj.left) (hx : x ∈ V) :
    ∃ O : Set X.obj.left, IsOpen O ∧ x ∈ O ∧
      ∃ N : ℕ, ∀ y ∈ O, (∃ m, I y ^ m ≤ J y) → I y ^ N ≤ J y := by
  let W : Opens X.obj.left := ⟨V, hV⟩
  let Y : LocallyRingedSpace := X.obj.left.restrict W.isOpenEmbedding
  let j : Y ⟶ X.obj.left := X.obj.left.ofRestrict W.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion j := LocallyRingedSpace.IsOpenImmersion.ofRestrict _ _
  have hc := charts_of_openImmersion (j ≫ X.obj.hom) X.obj.hom X.property.2.2 j rfl
  obtain ⟨n, U, C, hC, i, hi, _, hxi⟩ := hc ⟨x, hx⟩
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let f := i ≫ j
  have hf : ∀ y, f.base y ∈ V := fun y => (i.base y).property
  have hpI := HironakaG10SourceOpenUniformArtinRees.isLocallyFinitelyGenerated_pull_of_range_subset
    f V I hI hf
  have hpJ := HironakaG10SourceOpenUniformArtinRees.isLocallyFinitelyGenerated_pull_of_range_subset
    f V J hJ hf
  obtain ⟨c, hc⟩ := hxi
  obtain ⟨O, hO, hcO, N, hN⟩ := exists_local_uniform_colon_power_model U C hC
    (pullFamily f J) (pullFamily f I) hpJ hpI c
  have hfI : LocallyRingedSpace.IsOpenImmersion f := inferInstance
  have hfopen : IsOpenMap f.base := hfI.base_open.isOpenMap
  refine ⟨f.base '' O, hfopen O hO, ⟨c, hcO, ?_⟩, N, ?_⟩
  · change j.base (i.base c) = x
    rw [hc]
    rfl
  rintro _ ⟨y, hy, rfl⟩ ⟨m, hm⟩
  have hbij : Function.Bijective (f.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective (f.stalkMap y)).mp
      (LocallyRingedSpace.IsOpenImmersion.stalk_iso f y)
  have h1 : pullFamily f I y ^ m ≤ pullFamily f J y :=
    (map_pow_le_map_iff _ hbij (I (f.base y)) (J (f.base y)) m).mpr hm
  exact (map_pow_le_map_iff _ hbij (I (f.base y)) (J (f.base y)) N).mp (hN y hy ⟨m, h1⟩)

/-- **Uniform colon power over a compact set** (plan item G10-03-06.a, lane G10RD's statement): for
families generated on an open domain `V ⊇ L`, `L` compact, ONE exponent `N` works at every point of `L`
where some power works. -/
theorem exists_uniform_colon_power {X : SourceReducedComplexSpace} (V : Set X.obj.left)
    (hV : IsOpen V) (I J : ∀ x, Ideal (X.obj.left.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X.obj.left V I)
    (hJ : IsLocallyFinitelyGeneratedOn X.obj.left V J)
    (L : Set X.obj.left) (hL : IsCompact L) (hLV : L ⊆ V) :
    ∃ N, ∀ y ∈ L, (∃ n, ∀ᶠ z in 𝓝 y, I z ^ n ≤ J z) → ∀ n ≥ N, ∀ᶠ z in 𝓝 y, I z ^ n ≤ J z := by
  classical
  choose O hO hxO M hM using fun x : L => exists_local_uniform_colon_power_on X V hV I J hI hJ x.1
    (hLV x.2)
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover (fun x : L => O x) hO
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩)
  refine ⟨s.sup M, fun y hy ⟨n₀, hn₀⟩ n hn => ?_⟩
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs hy)
  have hyV := hLV hy
  have h0 : I y ^ M x ≤ J y := hM x y hyx ⟨n₀, hn₀.self_of_nhds⟩
  have hle : I y ^ n ≤ J y :=
    (Ideal.pow_le_pow_right ((Finset.le_sup (f := M) hxs).trans hn)).trans h0
  exact eventually_le_of_le (isLocallyFinitelyGeneratedOn_pow V I hI n) hJ hV hV hyV hyV hle

end

end Hironaka.Analytic.Unibranch.HironakaG10TmUniformColon
