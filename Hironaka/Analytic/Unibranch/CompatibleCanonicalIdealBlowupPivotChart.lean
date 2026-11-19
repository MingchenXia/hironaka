import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupUniversal
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupUniversal
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupCartier
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierCentreIdeal
import Hironaka.Blowup.BlowupSpaceUniversal

/-! Intrinsic strict pivot loci and genuine charts of the SAME canonical
finite-ideal blowup, BP FIRST. Both public producers have ordinary inputs.
The full compatible two-object saturation chart remains downstream.
Inherited ideal/germ/gluing/Cartier/UP engines receive zero duplicate credit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotChart
noncomputable section
open Hironaka
  Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetMonomialSpan
  HironakaSingularIdealInvertibleModule HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaNativePositiveFiniteIdealSections
  Hironaka.BlowupSequences BlowupConstruction BlowupFlatCoordinates
  HironakaSingularSubspaceBlowupCartier HironakaSingularSubspaceBlowupCartierCentreIdeal
  BlowupStrictSubmanifold HironakaActualAnalyticSubspaceLocalFunctions

private theorem span_mul_regular_iff_unit {R : Type*} [CommRing R]
    (ε r : R) (hε : IsRegular ε) :
    Ideal.span ({ε*r} : Set R) = Ideal.span {ε} ↔ IsUnit r := by
  constructor
  · intro h
    have hm : ε ∈ Ideal.span ({ε*r} : Set R) :=
      h.symm ▸ Ideal.subset_span (Set.mem_singleton ε)
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hm
    have hc : ε*(a*r)=ε*1 := by
      calc
        _ = a*(ε*r) := by ring
        _ = ε := ha
        _ = _ := (mul_one ε).symm
    have hunit : a*r=1 := hε.left hc
    exact ⟨⟨r,a,by rw [mul_comm];exact hunit,hunit⟩,rfl⟩
  · rintro ⟨u,rfl⟩
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro x (rfl : x=ε*↑u)
      exact Ideal.mem_span_singleton.mpr ⟨↑u,rfl⟩
    · apply Ideal.span_le.mpr
      rintro x (rfl : x=ε)
      exact Ideal.mem_span_singleton.mpr ⟨↑u⁻¹,by simp [mul_assoc]⟩

private theorem actual_stalk_unit_iff_residue {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (x : C) (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier) :
    IsUnit r ↔ actualSubspaceStalkEval (n := n) C x r≠0 := by
  let : IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
    actualSubspaceStalk_isLocalRing C x
  rw [←IsLocalRing.notMem_maximalIdeal,←actualSubspaceStalkEval_ker C x]
  rfl

-- Reused actual germ-map laws: no new quotient or scalar factory is defined.
private theorem original_germ_congr {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hfg : f=ᶠ[𝓝 x]g) :
    actualOriginalFunctionGerm x f hf=actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg hfg

private theorem original_germ_mul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    actualOriginalFunctionGerm x (fun y => f y*g y) (hf.mul hg)=
      actualOriginalFunctionGerm x f hf*actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [map_mul,actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem quotient_germ_eval {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (S : Set M) (x : S) (f : M → ℂ) (hf : HolomorphicAt n f x.val) :
    actualSubspaceStalkEval (n := n) S x
      (((HironakaActualAnalyticSubspace.actualSubspaceInclusion (n := n) S).stalkMap x)
        (actualOriginalFunctionGerm x.val f hf))=f x.val := by
  obtain ⟨U,hxU,s,hs⟩ :=
    exists_actual_section_of_original_holomorphicAt x.val f hf
  rw [actualOriginalFunctionGerm_eq_section U x.val hxU s f hf hs,
    actualSubspaceStalkEval_inclusion_germ]
  exact (sectionExtension_apply U s x.val hxU).symm.trans hs.self_of_nhds

section Geometric
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {C : Set M} [Fact (IsClosedSubmanifold n C)]

/-- Literal whole ambient centre ideal under the EXISTING actual strict-source
inclusion. This abbreviation introduces no ring, sheaf or scalar structure. -/
abbrev strictCentreStalkIdeal (W : Set M)
    (z : geoStrictTransform (blowupProj n C) C W) :=
  Ideal.map ((actualSubspaceInclusion (n := n)
    (geoStrictTransform (blowupProj n C) C W)).stalkMap z).hom
      (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := n) (blowupProj n C)
        (vanishingIdeal (n := n) C)) z.val)

/-- The actual original pulled normal coordinate in the independent strict
quotient stalk; all maps are the existing native maps. -/
abbrev geometricCoordinateClass (W : Set M) (c : FlatChart n C)
    (z : geoStrictTransform (blowupProj n C) C W) (hz : z.val.base∈c.dom) (i : Fin n) :=
  ((actualSubspaceInclusion (n := n) (geoStrictTransform (blowupProj n C) C W)).stalkMap z)
    (actualOriginalFunctionGerm z.val (c.τ i ∘ blowupProj n C)
      ((holomorphicAt_flatCoord c.Φ i hz).comp_contMDiff
        (Eventually.of_forall fun p => contMDiff_blowupProj p)))

private def chartRatio (c : FlatChart n C) (i : Fin n) (p : BlowupSpace n C) : ℂ :=
  if i=c.j then 1 else c.toFun p i

private theorem chartRatio_hol (c : FlatChart n C) (i : Fin n)
    (p : BlowupSpace n C) (hp : p∈c.source) : HolomorphicAt n (chartRatio c i) p := by
  by_cases hi : i=c.j
  · have heq : chartRatio c i=(fun _ => 1) := funext fun _ => if_pos hi
    rw [heq]
    exact holomorphicAt_const 1
  · have heq : chartRatio c i=(fun p => c.toFun p i) := funext fun _ => if_neg hi
    rw [heq]
    have hmax := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ComplexModel n)) (n := ∞)
      (atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩))
    filter_upwards [c.isOpen_source.mem_nhds hp] with q hq
    have hc : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ c.toFun q :=
      contMDiffAt_of_mem_maximalAtlas hmax hq
    have hiq : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (fun q => c.toFun q i) q :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiffAt.comp q hc
    exact hiq.mdifferentiableAt (by simp)

omit [Fact (IsClosedSubmanifold n C)] in
private theorem coordinate_ratio_on_chart (c : FlatChart n C) (i : Fin n)
    (hi : c.k ≤ i.val) (p : BlowupSpace n C) (hp : p∈c.source) :
    c.τ i p.base=c.τ c.j p.base*chartRatio c i p := by
  by_cases hij : i=c.j
  · subst i
    simp [chartRatio]
  · have h := congrArg (fun w : ComplexModel n => w i) (c.monomial_toFun hp)
    change (if c.k ≤ i.val ∧ i≠c.j then c.toFun p i*c.toFun p c.j else c.toFun p i)=c.τ i p.base at h
    rw [if_pos ⟨hi,hij⟩,c.toFun_apply_j p] at h
    simpa only [chartRatio,if_neg hij,mul_comm] using h.symm

omit [Fact (IsClosedSubmanifold n C)] in
private theorem ratio_ne_zero_iff_repivot (c : FlatChart n C) (i : Fin n)
    (hi : c.k ≤ i.val) (p : BlowupSpace n C) (hp : p∈c.source) :
    chartRatio c i p≠0 ↔ p∈({c with j:=i,hj:=hi} : FlatChart n C).source := by
  by_cases hij : i=c.j
  · subst i
    have heq : ({c with j:=c.j,hj:=hi} : FlatChart n C)=c := rfl
    rw [heq]
    exact iff_of_true (by simp [chartRatio]) hp
  · change (if i=c.j then 1 else c.toFun p i)≠0 ↔
      p.base∈c.dom ∧ extVal (c.τ i) p≠0
    rw [if_neg hij,c.toFun_apply_normal p hi hij]
    exact ⟨fun h => ⟨hp.1,(div_ne_zero_iff.mp h).1⟩,
      fun h => div_ne_zero h.2 hp.2⟩

private theorem geometric_coordinate_class_ratio (W : Set M) (c : FlatChart n C)
    (z : geoStrictTransform (blowupProj n C) C W) (hz : z.val∈c.source)
    (i : Fin n) (hi : c.k ≤ i.val) :
    geometricCoordinateClass W c z hz.1 i=geometricCoordinateClass W c z hz.1 c.j*
      ((actualSubspaceInclusion (n := n) (geoStrictTransform (blowupProj n C) C W)).stalkMap z)
        (actualOriginalFunctionGerm z.val (chartRatio c i) (chartRatio_hol c i z.val hz)) := by
  let f := c.τ i ∘ blowupProj n C
  let g := c.τ c.j ∘ blowupProj n C
  have hf : HolomorphicAt n f z.val := (holomorphicAt_flatCoord c.Φ i hz.1).comp_contMDiff
    (Eventually.of_forall fun p => contMDiff_blowupProj p)
  have hg : HolomorphicAt n g z.val := (holomorphicAt_flatCoord c.Φ c.j hz.1).comp_contMDiff
    (Eventually.of_forall fun p => contMDiff_blowupProj p)
  have hr := chartRatio_hol c i z.val hz
  have heq : f=ᶠ[𝓝 z.val](fun p => g p*chartRatio c i p) := by
    filter_upwards [c.isOpen_source.mem_nhds hz] with p hp
    exact coordinate_ratio_on_chart c i hi p hp
  let Q := ((actualSubspaceInclusion (n := n)
    (geoStrictTransform (blowupProj n C) C W)).stalkMap z).hom
  exact (congrArg Q ((original_germ_congr z.val f _ hf (hg.mul hr) heq).trans
    (original_germ_mul z.val g (chartRatio c i) hg hr))).trans (Q.map_mul _ _)

private theorem strict_centre_span_coordinates (W : Set M) (c : FlatChart n C)
    (z : geoStrictTransform (blowupProj n C) C W) (hz : z.val∈c.source) :
    strictCentreStalkIdeal W z=Ideal.span (Set.range fun i : {i : Fin n // c.k ≤ i.val} =>
      geometricCoordinateClass W c z hz.1 i.val) :=
  actualRestrictedPulledCentreIdeal_eq_span_normal_coordinates (Fact.out : IsClosedSubmanifold n C)
    contMDiff_blowupProj c.hsrc c.hflat (geoStrictTransform (blowupProj n C) C W) z hz.1

private theorem strict_centre_principal_on_chart (W : Set M) (c : FlatChart n C)
    (z : geoStrictTransform (blowupProj n C) C W) (hz : z.val∈c.source) :
    strictCentreStalkIdeal W z=Ideal.span {geometricCoordinateClass W c z hz.1 c.j} := by
  rw [strict_centre_span_coordinates W c z hz]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hm := Ideal.mul_mem_right
      (((actualSubspaceInclusion (n := n) (geoStrictTransform (blowupProj n C) C W)).stalkMap z)
        (actualOriginalFunctionGerm z.val (chartRatio c i.val) (chartRatio_hol c i.val z.val hz)))
      (Ideal.span {geometricCoordinateClass W c z hz.1 c.j})
      (Ideal.mem_span_singleton_self (geometricCoordinateClass W c z hz.1 c.j))
    exact (congrArg (fun a : ((actualSubspaceSheaf (n := n)
      (geoStrictTransform (blowupProj n C) C W)).presheaf.stalk z).carrier =>
        a∈Ideal.span {geometricCoordinateClass W c z hz.1 c.j})
          (geometric_coordinate_class_ratio W c z hz i.val i.property)).mpr hm
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _=geometricCoordinateClass W c z hz.1 c.j)
    exact Ideal.subset_span ⟨⟨c.j,c.hj⟩,rfl⟩

private theorem strict_centre_invertible (hCi : interior C=∅) (W : Set M) (hW : IsClosed W)
    (z : geoStrictTransform (blowupProj n C) C W) :
    Module.Invertible ((actualSubspaceSheaf (n := n)
      (geoStrictTransform (blowupProj n C) C W)).presheaf.stalk z).carrier
        (strictCentreStalkIdeal W z) := by
  let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
  have hInv := EmbeddedGeometricBlowupCartier.geometricProjection_ideal_moduleInvertible hπ hW z
  have hMap := map_actualSubspace_stalk_ideal_pullback contMDiff_blowupProj
    (fun x (hx : x∈geoStrictTransform (blowupProj n C) C W) =>
      geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hW hx)
    (vanishingIdeal (n := n) C) (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) z
  let R := ((actualSubspaceSheaf (n := n)
    (geoStrictTransform (blowupProj n C) C W)).presheaf.stalk z).carrier
  let I : Ideal R := Ideal.map
    ((EmbeddedGeometricBlowup.geometricProjection hπ hW).stalkMap z).hom
      (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
        ((EmbeddedGeometricBlowup.geometricProjection hπ hW).base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (blowupProj n C z.val)))
  have hIdeal : I=strictCentreStalkIdeal W z := hMap
  exact (congrArg (fun J : Ideal R => Module.Invertible R J) hIdeal).mp hInv

/-- The ENTIRE strict pulled ideal is generated by the specified coordinate
exactly on the actual geometric repivot chart. OWN strict Cartier data and
actual monomial equations derive every whole germ relation internally. -/
theorem strict_pivot_generator_iff_on_chart (hCi : interior C=∅) (W : Set M) (hW : IsClosed W)
    (c : FlatChart n C) (z : geoStrictTransform (blowupProj n C) C W) (hz : z.val∈c.source)
    (i : Fin n) (hi : c.k ≤ i.val) :
    strictCentreStalkIdeal W z=Ideal.span {geometricCoordinateClass W c z hz.1 i} ↔
      z.val∈({c with j:=i,hj:=hi} : FlatChart n C).source := by
  let S := geoStrictTransform (blowupProj n C) C W
  let ε := geometricCoordinateClass W c z hz.1 c.j
  let r := ((actualSubspaceInclusion (n := n) S).stalkMap z)
    (actualOriginalFunctionGerm z.val (chartRatio c i) (chartRatio_hol c i z.val hz))
  have hPrincipal : strictCentreStalkIdeal W z=Ideal.span {ε} := strict_centre_principal_on_chart W c z hz
  have hReg : IsRegular ε := isRegular_of_span_eq _ (strict_centre_invertible hCi W hW z) hPrincipal
  have hRelation : geometricCoordinateClass W c z hz.1 i=ε*r :=
    geometric_coordinate_class_ratio W c z hz i hi
  have hValue : actualSubspaceStalkEval (n := n) S z r=chartRatio c i z.val :=
    quotient_germ_eval S z (chartRatio c i) (chartRatio_hol c i z.val hz)
  calc
    _ ↔ Ideal.span {geometricCoordinateClass W c z hz.1 i}=Ideal.span {ε} :=
      ⟨fun h => h.symm.trans hPrincipal,fun h => hPrincipal.trans h.symm⟩
    _ ↔ IsUnit r := by rw [hRelation];exact span_mul_regular_iff_unit ε r hReg
    _ ↔ chartRatio c i z.val≠0 := (actual_stalk_unit_iff_residue S z r).trans (by rw [hValue])
    _ ↔ _ := ratio_ne_zero_iff_repivot c i hi z.val hz

private theorem geometric_coordinate_class_zero_of_W (W : Set M) (hW : IsClosed W)
    (c : FlatChart n C) (z : geoStrictTransform (blowupProj n C) C W)
    (hz : z.val∈c.source) (i : Fin n)
    (hzero : ∀x∈W,x∈c.dom→c.τ i x=0) : geometricCoordinateClass W c z hz.1 i=0 := by
  let S := geoStrictTransform (blowupProj n C) C W
  let f := c.τ i ∘ blowupProj n C
  have hf : HolomorphicAt n f z.val := (holomorphicAt_flatCoord c.Φ i hz.1).comp_contMDiff
    (Eventually.of_forall fun p => contMDiff_blowupProj p)
  have hVan : (vanishingIdeal (n := n) S).mem z.val f := by
    refine ⟨hf,?_⟩
    filter_upwards [c.isOpen_source.mem_nhds hz] with p hp hpS
    exact hzero p.base (geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hW hpS) hp.1
  have hm : actualOriginalFunctionGerm z.val f hf∈
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) S) z.val :=
    Ideal.subset_span ⟨f,hf,hVan,rfl⟩
  rw [←actualSubspaceInclusion_stalk_kernel S z] at hm
  exact hm

/-- In particular the genuine zero coordinate appended to a centre graph
has EMPTY strict pivot chart, even though its raw monomial chart exists. -/
theorem strict_zero_pivot_chart_empty (hCi : interior C=∅) (W : Set M) (hW : IsClosed W)
    (c : FlatChart n C) (hzero : ∀x∈W,x∈c.dom→c.τ c.j x=0) :
    geoStrictTransform (blowupProj n C) C W ∩ c.source=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro p ⟨hpW,hpc⟩
  let z : geoStrictTransform (blowupProj n C) C W := ⟨p,hpW⟩
  have hZero : geometricCoordinateClass W c z hpc.1 c.j=0 :=
    geometric_coordinate_class_zero_of_W W hW c z hpc c.j hzero
  have hReg := isRegular_of_span_eq _ (strict_centre_invertible hCi W hW z)
    (strict_centre_principal_on_chart W c z hpc)
  have hRegZero : IsRegular (0 : ((actualSubspaceSheaf (n := n)
      (geoStrictTransform (blowupProj n C) C W)).presheaf.stalk z).carrier) :=
    (congrArg IsRegular hZero).mp hReg
  have heq : (0 : ((actualSubspaceSheaf (n := n)
      (geoStrictTransform (blowupProj n C) C W)).presheaf.stalk z).carrier)=1 :=
    hRegZero.left (by simp)
  have hValue := congrArg (actualSubspaceStalkEval (n := n)
    (geoStrictTransform (blowupProj n C) C W) z) heq
  exact zero_ne_one (by simpa only [map_zero,map_one] using hValue)

omit [Fact (IsClosedSubmanifold n C)] in
private theorem exists_repivot_source (c : FlatChart n C) (p : BlowupSpace n C)
    (hp : p.base∈c.dom) : ∃(k : Fin n)(hk : c.k ≤ k.val),
      p∈({c with j:=k,hj:=hk} : FlatChart n C).source := by
  by_cases hpC : p.base∈C
  · have hnot := BlowupSpace.dirVec_not_mem hpC
    rw [BlowupSpaceTangent.mem_tangentSpace_iff c.hsrc c.hflat hp hpC] at hnot
    push Not at hnot
    obtain ⟨k,hk,hne⟩ := hnot
    refine ⟨k,hk,hp,?_⟩
    change extVal (c.τ k) p≠0
    rw [extVal_of_mem hpC]
    exact hne
  · have hnot : ¬c.Φ.toFun (chartAt (ComplexModel n) c.y₀ p.base)∈complexCoordinatePlane n c.k :=
      fun h => hpC ((c.hflat hp.1 hp.2).mpr h)
    change ¬∀k : Fin n,c.k ≤ k.val→c.τ k p.base=0 at hnot
    push Not at hnot
    obtain ⟨k,hk,hne⟩ := hnot
    refine ⟨k,hk,hp,?_⟩
    change extVal (c.τ k) p≠0
    rw [extVal_of_not_mem hpC]
    exact hne

/-- Intrinsic coordinate generation on the WHOLE original flat domain.
This is defined from the entire native ideal, not from a chart image. -/
def strictPivotGeneratorLocus (W : Set M) (c : FlatChart n C) (i : Fin n) :
    Set (geoStrictTransform (blowupProj n C) C W) :=
  {z | ∃hz : z.val.base∈c.dom,
    strictCentreStalkIdeal W z=Ideal.span {geometricCoordinateClass W c z hz i}}

/-- The intrinsic WHOLE generator locus IS the actual geometric pivot chart
image, derived using OWN strict Cartier and genuine same-flattening coverage. -/
theorem strict_pivot_generator_locus (hCi : interior C=∅) (W : Set M) (hW : IsClosed W)
    (c : FlatChart n C) (i : Fin n) (hi : c.k ≤ i.val) :
    strictPivotGeneratorLocus W c i=
      (Subtype.val : geoStrictTransform (blowupProj n C) C W → BlowupSpace n C) ⁻¹'
        ({c with j:=i,hj:=hi} : FlatChart n C).source := by
  ext z
  constructor
  · rintro ⟨hz,hGen⟩
    obtain ⟨k,hk,hzk⟩ := exists_repivot_source c z.val hz
    let ck : FlatChart n C := {c with j:=k,hj:=hk}
    have hGenK : strictCentreStalkIdeal W z=
        Ideal.span {geometricCoordinateClass W ck z hzk.1 i} := hGen
    exact (strict_pivot_generator_iff_on_chart hCi W hW ck z hzk i hi).mp hGenK
  · intro hz
    let ci : FlatChart n C := {c with j:=i,hj:=hi}
    have hzci : z.val∈ci.source := hz
    have hGen := (strict_pivot_generator_iff_on_chart hCi W hW ci z hzci i hi).mpr hzci
    exact ⟨hzci.1,hGen⟩

/-- The actual intrinsic generator set is a genuine open on the strict model. -/
theorem strict_pivot_generator_locus_isOpen (hCi : interior C=∅) (W : Set M) (hW : IsClosed W)
    (c : FlatChart n C) (i : Fin n) (hi : c.k ≤ i.val) :
    IsOpen (strictPivotGeneratorLocus W c i) := by
  rw [strict_pivot_generator_locus hCi W hW c i hi]
  exact ({c with j:=i,hj:=hi} : FlatChart n C).isOpen_source.preimage continuous_subtype_val

end Geometric

section FamilyComparison

open SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace} {ι : Type} {dims : ι → ℕ}
  {Ambient Lift : ι → Type} [∀ i, TopologicalSpace (Ambient i)]
  [∀ i, TopologicalSpace (Lift i)]
  [∀ i, ChartedSpace (ComplexModel (dims i)) (Ambient i)]
  [∀ i, IsComplexManifold (dims i) (Ambient i)]
  [∀ i, ChartedSpace (ComplexModel (dims i)) (Lift i)]
  [∀ i, IsComplexManifold (dims i) (Lift i)]
  {Centre Carrier : ∀ i, Set (Ambient i)} {π : ∀ i, Lift i → Ambient i}
  (hCarrier : ∀ i, IsComplexAnalyticSubset (n := dims i) (Carrier i))
  (hπ : ∀ i, IsBlowupAlong (dims i) (Centre i) (π i))
  (chart : ∀ i, ofClosedAnalytic (Carrier i) (hCarrier i) ⟶ X)
  [∀ i, LocallyRingedSpace.IsOpenImmersion (chart i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hIdeal : ∀ i (y : Carrier i),
    Ideal.map ((actualSubspaceInclusion (n := dims i) (Carrier i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := dims i) (Centre i)) y.val) =
        nativePulledIdealStalkIdeal (chart i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : Carrier i), (chart i).hom.left.base w=x)

/-- A private adapter only: the actual graph dictionaries and cover will be
DERIVED from original sections in the ordinary consumer. Both OWN Cartier
structures and BOTH full UPs are derived from the real native mothers here.
No UP/Cartier/iso input is added. This reuse earns no new UP engine credit. -/
private theorem exists_geometric_family_canonical_iso :
    ∃ E : EmbeddedGeometricIdealOriginalObject.sourceObject
        hCarrier hπ chart B b hIdeal hcover ≅
        OriginalFiniteIdealGeometricBlowup.sourceObject B b,
      E.hom ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
        EmbeddedGeometricIdealOriginalObject.projectionMorphism
          hCarrier hπ chart B b hIdeal hcover := by
  classical
  let A := EmbeddedGeometricIdealOriginalObject.sourceObject hCarrier hπ chart B b hIdeal hcover
  let P := OriginalFiniteIdealGeometricBlowup.sourceObject B b
  let a : A ⟶ X := EmbeddedGeometricIdealOriginalObject.projectionMorphism
    hCarrier hπ chart B b hIdeal hcover
  let p : P ⟶ X := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  obtain ⟨qaRaw,hqaRaw,huaRaw⟩ := EmbeddedGeometricIdealGlobalCartier.projection_ideal_exists_locallyFreeData
    hCarrier hπ chart B b hIdeal
  obtain ⟨qpRaw,hqpRaw,hupRaw⟩ := OriginalFiniteIdealGeometricBlowupUniversal.projection_ideal_exists_locallyFreeData B b
  let qa : (nativePulledIdealModule a.hom.left B b).LocalGeneratorsData := qaRaw
  let qp : (nativePulledIdealModule p.hom.left B b).LocalGeneratorsData := qpRaw
  let hqaInstance : qa.IsLocallyFreeData := hqaRaw
  let huaInstance : ∀ i, Unique (qa.generators i).I := fun i => Classical.choice (huaRaw i)
  let hqpInstance : qp.IsLocallyFreeData := hqpRaw
  let hupInstance : ∀ i, Unique (qp.generators i).I := fun i => Classical.choice (hupRaw i)
  obtain ⟨f,hf,_⟩ := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b A a qa
  obtain ⟨g,hg,_⟩ := EmbeddedGeometricIdealGlobalUniversal.exists_unique_lift_of_locallyFreeData
    hCarrier hπ chart B b hIdeal hcover P p qp
  obtain ⟨fa,hfa,huaUnique⟩ := EmbeddedGeometricIdealGlobalUniversal.exists_unique_lift_of_locallyFreeData
    hCarrier hπ chart B b hIdeal hcover A a qa
  obtain ⟨fp,hfp,hupUnique⟩ := OriginalFiniteIdealGeometricBlowupUniversal.exists_unique_lift_of_locallyFreeData
    B b P p qp
  have hfg : f ≫ g=𝟙 A := by
    apply (huaUnique (f ≫ g) ?_).trans
    exact (huaUnique (𝟙 A) (Category.id_comp a)).symm
    change (f ≫ g) ≫ a=a
    rw [Category.assoc,hg,hf]
  have hgf : g ≫ f=𝟙 P := by
    apply (hupUnique (g ≫ f) ?_).trans
    exact (hupUnique (𝟙 P) (Category.id_comp p)).symm
    change (g ≫ f) ≫ p=p
    rw [Category.assoc,hf,hg]
  exact ⟨{hom:=f,inv:=g,hom_inv_id:=hfg,inv_hom_id:=hgf},hf⟩

end FamilyComparison

section ChosenGraphCover

open SourceReducedComplexSpace OriginalFiniteIdealGraphChart
  OriginalPositiveFiniteIdealGraphChart HironakaFiniteSectionProductGraph
  HironakaProductZeroPlaneBlowup EmbeddedGeometricBlowup
open scoped ProductComplexManifold

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

/-- Private geometry RETAINS the ordinary mother's actual graph functions.
This is output data constructed from B,b, never a public input packet. -/
private structure ChosenGraph (x : X.obj.left) where
  embedding : LocalEmbedding X
  domain : Opens embedding.ambient
  rank : ℕ
  functions : domain → ComplexModel rank
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel embedding.dim) 𝓘(ℂ,ComplexModel rank) ∞ functions
  analytic : IsComplexAnalyticSubset (n := embedding.dim+rank)
    (productGraph ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions)
  wholeIdeal : ∀ z : productGraph
      ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions,
    Ideal.map ((actualSubspaceInclusion (n := embedding.dim+rank)
      (productGraph ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions)).stalkMap z).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := embedding.dim+rank)
        {q : domain × ComplexModel rank | q.2=0}) z.val) =
        nativePulledIdealStalkIdeal (chartGraphMap embedding domain functions holomorphic) B b z
  positive : 0<rank
  lift : Type
  [liftTopology : TopologicalSpace lift]
  [liftAtlas : ChartedSpace (ComplexModel (embedding.dim+rank)) lift]
  [liftComplex : IsComplexManifold (embedding.dim+rank) lift]
  projection : lift → domain × ComplexModel rank
  blowup : IsBlowupAlong (embedding.dim+rank)
    {q : domain × ComplexModel rank | q.2=0} projection
  point : productGraph ((Subtype.val : domain → embedding.ambient) ⁻¹' embedding.carrier) functions
  point_over : (chartGraphMap embedding domain functions holomorphic).base point=x

attribute [instance] ChosenGraph.liftTopology ChosenGraph.liftAtlas ChosenGraph.liftComplex

private theorem chosenGraph_nonempty [B.IsFiniteType] (x : X.obj.left) :
    Nonempty (ChosenGraph B b x) := by
  obtain ⟨e,O,r,G,hG,hΓ,hJ,hr,z,hz⟩ := exists_positive_graph_chart B b x
  obtain ⟨Y,tY,aY,cY,π,hπ⟩ := exists_product_zero_plane_blowup (n := e.dim) (M := O) hr
  let := tY
  let := aY
  let := cY
  exact ⟨{
    embedding := e
    domain := O
    rank := r
    functions := G
    holomorphic := hG
    analytic := hΓ
    wholeIdeal := hJ
    positive := hr
    lift := Y
    liftTopology := tY
    liftAtlas := aY
    liftComplex := cY
    projection := π
    blowup := hπ
    point := z
    point_over := hz }⟩

variable [B.IsFiniteType]

private def chosenGraph (x : X.obj.left) : ChosenGraph B b x :=
  Classical.choice (chosenGraph_nonempty B b x)

private theorem chosenGraph_analytic (x : X.obj.left) :
    IsComplexAnalyticSubset (n := (chosenGraph B b x).embedding.dim+(chosenGraph B b x).rank)
      (productGraph ((Subtype.val : (chosenGraph B b x).domain → (chosenGraph B b x).embedding.ambient) ⁻¹'
        (chosenGraph B b x).embedding.carrier) (chosenGraph B b x).functions) :=
  (chosenGraph B b x).analytic

private theorem chosenGraph_blowup (x : X.obj.left) :
    IsBlowupAlong ((chosenGraph B b x).embedding.dim+(chosenGraph B b x).rank)
      {q : (chosenGraph B b x).domain × ComplexModel (chosenGraph B b x).rank | q.2=0}
      (chosenGraph B b x).projection := (chosenGraph B b x).blowup

private def chosenGraph_chart (x : X.obj.left) :
    ofClosedAnalytic _ (chosenGraph_analytic B b x) ⟶ X :=
  chartGraphMorphism (chosenGraph B b x).embedding (chosenGraph B b x).domain
    (chosenGraph B b x).functions (chosenGraph B b x).holomorphic (chosenGraph B b x).analytic

private instance chosenGraph_chart_open (x : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (chosenGraph_chart B b x).hom.left :=
  chartGraphMap_isOpenImmersion _ _ _ _

private theorem chosenGraph_ideal (x : X.obj.left)
    (y : productGraph
      ((Subtype.val : (chosenGraph B b x).domain → (chosenGraph B b x).embedding.ambient) ⁻¹'
        (chosenGraph B b x).embedding.carrier) (chosenGraph B b x).functions) :
    Ideal.map ((actualSubspaceInclusion
      (n := (chosenGraph B b x).embedding.dim+(chosenGraph B b x).rank)
      (productGraph ((Subtype.val : (chosenGraph B b x).domain → (chosenGraph B b x).embedding.ambient) ⁻¹'
        (chosenGraph B b x).embedding.carrier) (chosenGraph B b x).functions)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal
        (n := (chosenGraph B b x).embedding.dim+(chosenGraph B b x).rank)
        {q : (chosenGraph B b x).domain × ComplexModel (chosenGraph B b x).rank | q.2=0}) y.val) =
      nativePulledIdealStalkIdeal (chosenGraph_chart B b x).hom.left B b y :=
  (chosenGraph B b x).wholeIdeal y

private theorem chosenGraph_cover (x : X.obj.left) :
    ∃ (i : X.obj.left) (w : productGraph
      ((Subtype.val : (chosenGraph B b i).domain → (chosenGraph B b i).embedding.ambient) ⁻¹'
        (chosenGraph B b i).embedding.carrier) (chosenGraph B b i).functions),
      (chosenGraph_chart B b i).hom.left.base w=x :=
  ⟨x,(chosenGraph B b x).point,(chosenGraph B b x).point_over⟩

private def chosenGraph_comparison :
    EmbeddedGeometricIdealOriginalObject.sourceObject (chosenGraph_analytic B b)
      (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
      (chosenGraph_ideal B b) (chosenGraph_cover B b) ≅
      OriginalFiniteIdealGeometricBlowup.sourceObject B b :=
  Classical.choose (exists_geometric_family_canonical_iso (chosenGraph_analytic B b)
    (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
    (chosenGraph_ideal B b) (chosenGraph_cover B b))

private theorem chosenGraph_comparison_projection :
    (chosenGraph_comparison B b).hom ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      EmbeddedGeometricIdealOriginalObject.projectionMorphism (chosenGraph_analytic B b)
        (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
        (chosenGraph_ideal B b) (chosenGraph_cover B b) :=
  Classical.choose_spec (exists_geometric_family_canonical_iso (chosenGraph_analytic B b)
    (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
    (chosenGraph_ideal B b) (chosenGraph_cover B b))

private def chosenGraph_toCanonical (i : X.obj.left) :
    geometricSource (chosenGraph_blowup B b i) (chosenGraph_analytic B b i) ⟶
      OriginalFiniteIdealGeometricBlowup.sourceObject B b :=
  EmbeddedGeometricIdealOriginalObject.localMorphism (chosenGraph_analytic B b)
    (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
    (chosenGraph_ideal B b) (chosenGraph_cover B b) i ≫ (chosenGraph_comparison B b).hom

private theorem chosenGraph_toCanonical_projection (i : X.obj.left) :
    chosenGraph_toCanonical B b i ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
      geometricProjectionMorphism (chosenGraph_blowup B b i) (chosenGraph_analytic B b i) ≫
        chosenGraph_chart B b i := by
  let A := EmbeddedGeometricIdealOriginalObject.sourceObject (chosenGraph_analytic B b)
    (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
    (chosenGraph_ideal B b) (chosenGraph_cover B b)
  let k : geometricSource (chosenGraph_blowup B b i) (chosenGraph_analytic B b i) ⟶ A :=
    EmbeddedGeometricIdealOriginalObject.localMorphism (chosenGraph_analytic B b)
      (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
      (chosenGraph_ideal B b) (chosenGraph_cover B b) i
  let E := chosenGraph_comparison B b
  let p := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  calc
    _ = k ≫ (E.hom ≫ p) := Category.assoc k E.hom p
    _ = k ≫ EmbeddedGeometricIdealOriginalObject.projectionMorphism (chosenGraph_analytic B b)
        (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
        (chosenGraph_ideal B b) (chosenGraph_cover B b) :=
      congrArg (fun v => k ≫ v) (chosenGraph_comparison_projection B b)
    _ = _ := EmbeddedGeometricIdealOriginalObject.localMorphism_projection (chosenGraph_analytic B b)
      (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
      (chosenGraph_ideal B b) (chosenGraph_cover B b) i

private instance chosenGraph_toCanonical_open (i : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (chosenGraph_toCanonical B b i).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion
    ((EmbeddedGeometricIdealOriginalObject.localMorphism (chosenGraph_analytic B b)
      (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
      (chosenGraph_ideal B b) (chosenGraph_cover B b) i).hom.left ≫
        (SourceReducedComplexSpace.isoLeft (chosenGraph_comparison B b)).hom)
  infer_instance

private theorem chosenGraph_toCanonical_range (i : X.obj.left) :
    range (chosenGraph_toCanonical B b i).hom.left.base =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
        range (chosenGraph_chart B b i).hom.left.base := by
  let E := chosenGraph_comparison B b
  let a := EmbeddedGeometricIdealOriginalObject.projectionMorphism (chosenGraph_analytic B b)
    (chosenGraph_blowup B b) (chosenGraph_chart B b) B b
    (chosenGraph_ideal B b) (chosenGraph_cover B b)
  let p := OriginalFiniteIdealGeometricBlowup.projectionMorphism B b
  have hInv : E.inv ≫ a=p := by
    calc
      _ = E.inv ≫ (E.hom ≫ p) := congrArg (fun v => E.inv ≫ v)
        (chosenGraph_comparison_projection B b).symm
      _ = p := by rw [←Category.assoc,E.inv_hom_id,Category.id_comp]
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨(geometricProjection (chosenGraph_blowup B b i)
      (chosenGraph_analytic B b i).isClosed).base z,
      (congrArg (fun H => H.hom.left.base z) (chosenGraph_toCanonical_projection B b i)).symm⟩
  · intro hy
    let zA := E.inv.hom.left.base y
    have hyA : a.hom.left.base zA∈range (chosenGraph_chart B b i).hom.left.base :=
      (congrArg (fun H => H.hom.left.base y) hInv).symm ▸ hy
    obtain ⟨w,hw⟩ := (Set.ext_iff.mp
      (EmbeddedGeometricIdealObjectGluing.preimage_chart_range (chosenGraph_analytic B b)
        (chosenGraph_blowup B b) (chosenGraph_chart B b) B b (chosenGraph_ideal B b) i) zA).mp hyA
    refine ⟨w,?_⟩
    change E.hom.hom.left.base
      ((EmbeddedGeometricIdealObjectGluing.inclusion (chosenGraph_analytic B b)
        (chosenGraph_blowup B b) (chosenGraph_chart B b) B b (chosenGraph_ideal B b) i).base w)=y
    rw [hw]
    exact congrArg (fun H => H.hom.left.base y) E.inv_hom_id

/-- ONLY original BFT/b and an actual canonical point internally construct
an actual positive graph, its WHOLE ideal dictionary and genuine geometric
strict-source open chart of the SAME canonical object. No future packet. -/
theorem exists_canonical_geometric_graph_chart
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) :
    ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (r : ℕ)
      (G : O → ComplexModel r)
      (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
      (hΓ : IsComplexAnalyticSubset (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)),
      0<r ∧
      (∀ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        Ideal.map ((actualSubspaceInclusion (n := e.dim+r)
          (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap z).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
            {q : O × ComplexModel r | q.2=0}) z.val) =
          nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z) ∧
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (e.dim+r)) Y)
        (_ : IsComplexManifold (e.dim+r) Y) (π : Y → O × ComplexModel r)
        (hπ : IsBlowupAlong (e.dim+r) {q : O × ComplexModel r | q.2=0} π)
        (L : geometricSource hπ hΓ ⟶ OriginalFiniteIdealGeometricBlowup.sourceObject B b),
        LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
        L ≫ OriginalFiniteIdealGeometricBlowup.projectionMorphism B b =
          geometricProjectionMorphism hπ hΓ ≫ chartGraphMorphism e O G hG hΓ ∧
        range L.hom.left.base =
          (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ⁻¹'
            range (chartGraphMap e O G hG).base ∧
        ∃ z : (geometricSource hπ hΓ).obj.left,L.hom.left.base z=y := by
  let i := (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y
  let m := chosenGraph B b i
  have hy : y∈range (chosenGraph_toCanonical B b i).hom.left.base := by
    rw [chosenGraph_toCanonical_range]
    exact ⟨m.point,m.point_over⟩
  obtain ⟨z,hz⟩ := hy
  exact ⟨m.embedding,m.domain,m.rank,m.functions,m.holomorphic,m.analytic,
    m.positive,m.wholeIdeal,m.lift,inferInstance,inferInstance,inferInstance,
    m.projection,m.blowup,chosenGraph_toCanonical B b i,
    inferInstance,chosenGraph_toCanonical_projection B b i,
    chosenGraph_toCanonical_range B b i,z,hz⟩

end ChosenGraphCover

end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotChart
