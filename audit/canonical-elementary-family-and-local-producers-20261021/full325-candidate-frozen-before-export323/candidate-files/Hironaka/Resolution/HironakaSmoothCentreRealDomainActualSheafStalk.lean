/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainIntrinsicStalkFreeness
import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-! # Literal complex structure-sheaf stalks and original relative modules
Complete four-node mathematical route precedes code. Complex smoothness is
used over COMPLEX scalar models. Actual colimit stalks, all original function
germs and both whole ideals are retained. Bundled normal-cone sheaf stalk
identification and ambient Hilbert--Samuel descent remain separate obligations.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped DirectSum Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits Opposite
namespace Hironaka.HironakaSmoothCentreRealDomainActualSheafStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreRealDomainOriginalCentreOpen HironakaSmoothCentreRealDomainIntrinsicStalkFreeness
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreCanonicalLayers
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  RelativePrincipalizationSpan InvertibleIdealQuotient HadamardBridge BlowupFlatCoordinates

section Manifold
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The ACTUAL complex-smooth (hence holomorphic) ring-valued structure sheaf. -/
abbrev actualComplexStructureSheaf (M : Type) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] :=
  smoothSheafCommRing 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) M ℂ

/-- The LITERAL neighbourhood colimit stalk, independently of any chart-germ definition. -/
abbrev actualComplexStructureStalk (y : M) : Type :=
  ((actualComplexStructureSheaf (n := n) M).presheaf.stalk y).carrier

/-- Actual complex-smooth sections on the genuine ORIGINAL open. -/
abbrev actualComplexSection (U : Opens M) : Type :=
  ((actualComplexStructureSheaf (n := n) M).presheaf.obj (op U)).carrier

/-- A total representative used only near included ORIGINAL points; it is not globally holomorphic. -/
def sectionExtension (U : Opens M) (s : actualComplexSection (n := n) U) : M → ℂ :=
  by
    classical
    exact fun z => if hz : z ∈ U then s ⟨z,hz⟩ else 0

omit [IsComplexManifold n M] in
/-- The total representative is the SAME actual section value at EVERY included point. -/
theorem sectionExtension_apply (U : Opens M) (s : actualComplexSection (n := n) U)
    (y : M) (hy : y ∈ U) : sectionExtension U s y = s ⟨y,hy⟩ := by
  simp only [sectionExtension,dif_pos hy]

omit [IsComplexManifold n M] in
/-- The actual extension is complex smooth ONLY at genuine included points. -/
theorem sectionExtension_contMDiffAt (U : Opens M) (s : actualComplexSection (n := n) U)
    (y : M) (hy : y ∈ U) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (sectionExtension U s) y := by
  have hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (s : U → ℂ) :=
    smoothSheaf.contMDiff_section s
  have heq : (fun z : U => sectionExtension U s z) = (s : U → ℂ) := by
    funext z
    exact sectionExtension_apply U s z z.2
  apply (contMDiffAt_subtype_iff (x := (⟨y,hy⟩ : U))).mp
  rw [heq]
  exact hs.contMDiffAt

omit [IsComplexManifold n M] in
/-- Complex sheaf sections are genuine ORIGINAL holomorphic representatives near each included point. -/
theorem sectionExtension_holomorphicAt (U : Opens M) (s : actualComplexSection (n := n) U)
    (y : M) (hy : y ∈ U) : HolomorphicAt n (sectionExtension U s) y := by
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  exact (sectionExtension_contMDiffAt U s z hz).mdifferentiableAt (by simp)

/-- The REAL recentered inverse of the actual preferred chart at the ORIGINAL point. -/
def preferredChartInverseMap (y : M) : ComplexModel n → M :=
  fun z => (chartAt (ComplexModel n) y).symm (z + chartAt (ComplexModel n) y y)

omit [IsComplexManifold n M] in
/-- Genuine actual chart inverse continuity carries the original neighbourhood filter. -/
theorem tendsto_preferredChartInverseMap (y : M) :
    Tendsto (preferredChartInverseMap (n := n) y) (𝓝 0) (𝓝 y) := by
  let e := chartAt (ComplexModel n) y
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  have htrans : Tendsto (fun z : ComplexModel n => z + e y) (𝓝 0) (𝓝 (e y)) := by
    have hc : ContinuousAt (fun z : ComplexModel n => z + e y) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  have ht := (e.continuousAt_symm (e.map_source hy)).tendsto.comp htrans
  change Tendsto (fun z : ComplexModel n => e.symm (z + e y)) (𝓝 0) (𝓝 y)
  simpa only [Function.comp_def,e.left_inv hy] using ht

/-- Original eventual equality gives the SAME whole preferred-chart germ. -/
theorem chartTranslatedGerm_congr_original (y : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f y) (hg : HolomorphicAt n g y) (hfg : f =ᶠ[𝓝 y] g) :
    chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y) f hf =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y) g hg := by
  dsimp only [chartTranslatedGerm,translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact (tendsto_preferredChartInverseMap y).eventually hfg

/-- The genuine ring map sends EVERY actual section to its SAME ORIGINAL full chart germ. -/
def sectionChartRingHom (U : Opens M) (y : M) (hy : y ∈ U) :
    actualComplexSection (n := n) U →+* HolGerm (ComplexModel n) where
  toFun s := chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
    (sectionExtension U s) (sectionExtension_holomorphicAt U s y hy)
  map_one' := by
    change chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
      (sectionExtension U (1 : actualComplexSection (n := n) U)) _ =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
        (fun _ => 1) (holomorphicAt_const 1)
    apply chartTranslatedGerm_congr_original
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    rw [sectionExtension_apply U 1 z hz]
    rfl
  map_mul' s t := by
    change chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
      (sectionExtension U (s*t)) _ =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
        (fun z => sectionExtension U s z * sectionExtension U t z)
        ((sectionExtension_holomorphicAt U s y hy).mul (sectionExtension_holomorphicAt U t y hy))
    apply chartTranslatedGerm_congr_original
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    rw [sectionExtension_apply U (s*t) z hz,sectionExtension_apply U s z hz,
      sectionExtension_apply U t z hz]
    rfl
  map_zero' := by
    change chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
      (sectionExtension U (0 : actualComplexSection (n := n) U)) _ =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
        (fun _ => 0) (holomorphicAt_const 0)
    apply chartTranslatedGerm_congr_original
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    rw [sectionExtension_apply U 0 z hz]
    rfl
  map_add' s t := by
    change chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
      (sectionExtension U (s+t)) _ =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
        (fun z => sectionExtension U s z + sectionExtension U t z)
        ((sectionExtension_holomorphicAt U s y hy).add (sectionExtension_holomorphicAt U t y hy))
    apply chartTranslatedGerm_congr_original
    filter_upwards [U.isOpen.mem_nhds hy] with z hz
    rw [sectionExtension_apply U (s+t) z hz,sectionExtension_apply U s z hz,
      sectionExtension_apply U t z hz]
    rfl

/-- Every TRUE open restriction containing the point preserves this whole original germ map. -/
theorem sectionChartRingHom_restrict (U V : Opens M) (hUV : U ≤ V)
    (y : M) (hy : y ∈ U) (s : actualComplexSection (n := n) V) :
    sectionChartRingHom U y hy
      ((actualComplexStructureSheaf (n := n) M).presheaf.map (homOfLE hUV).op s) =
      sectionChartRingHom V y (hUV hy) s := by
  refine chartTranslatedGerm_congr_original y _ _
    (sectionExtension_holomorphicAt U _ y hy)
    (sectionExtension_holomorphicAt V s y (hUV hy)) ?_
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  rw [sectionExtension_apply U _ z hz,sectionExtension_apply V s z (hUV hz)]
  rfl

/-- TRUE section maps form a cocone on the ACTUAL neighbourhood restriction diagram. -/
def sectionChartCocone (y : M) :
    Cocone ((OpenNhds.inclusion (y : TopCat.of M)).op ⋙
      (actualComplexStructureSheaf (n := n) M).presheaf) where
  pt := CommRingCat.of (HolGerm (ComplexModel n))
  ι := {
    app := fun U => CommRingCat.ofHom
      (sectionChartRingHom (unop U).val y (unop U).property)
    naturality := by
      intro U V i
      ext s
      change sectionChartRingHom (unop V).val y (unop V).property
          ((actualComplexStructureSheaf (n := n) M).presheaf.map
            (homOfLE (leOfHom i.unop)).op s) =
        sectionChartRingHom (unop U).val y (unop U).property s
      exact sectionChartRingHom_restrict (unop V).val (unop U).val
        (leOfHom i.unop) y (unop V).property s }

/-- The genuine colimit universal property, rather than a chosen chart definition, gives the stalk homomorphism. -/
def actualStalkToChartHom (y : M) :
    actualComplexStructureStalk (n := n) y →+* HolGerm (ComplexModel n) :=
  (colimit.desc _ (sectionChartCocone y)).hom

/-- EVERY actual section germ has the original representative formula by the colimit's genuine universal property. -/
theorem actualStalkToChartHom_germ (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualComplexSection (n := n) U) :
    actualStalkToChartHom y ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) =
      sectionChartRingHom U y hy s := by
  let D := (OpenNhds.inclusion (y : TopCat.of M)).op ⋙
    (actualComplexStructureSheaf (n := n) M).presheaf
  let N : OpenNhds (y : TopCat.of M) := by
    change {V : Opens (TopCat.of M) // y ∈ V}
    exact ⟨U,hy⟩
  change ((colimit.ι D (op N) ≫
    colimit.desc D (sectionChartCocone y)).hom) s = _
  rw [colimit.ι_desc]
  rfl

/-- EVERY original holomorphic function has an actual complex-smooth section on a genuine original neighbourhood. -/
theorem exists_actual_section_of_original_holomorphicAt (y : M) (f : M → ℂ)
    (hf : HolomorphicAt n f y) :
    ∃ (U : Opens M) (_hy : y ∈ U) (s : actualComplexSection (n := n) U),
      sectionExtension U s =ᶠ[𝓝 y] f := by
  obtain ⟨W,hWhol,hWopen,hyW⟩ := mem_nhds_iff.mp hf.eventually
  let U : Opens M := ⟨W,hWopen⟩
  let s : actualComplexSection (n := n) U := ⟨fun z : U => f z,by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : U => f z)
    intro z
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_eventually_mdifferentiableAt (hWhol z.2)⟩
  refine ⟨U,hyW,s,?_⟩
  filter_upwards [U.isOpen.mem_nhds hyW] with z hz
  rw [sectionExtension_apply U s z hz]

omit [IsComplexManifold n M] in
/-- Eventual equality on ORIGINAL neighbourhoods gives literal SHEAF colimit germ equality. -/
theorem actual_section_germ_eq_of_extension_eventuallyEq (U V : Opens M)
    (y : M) (hyU : y ∈ U) (hyV : y ∈ V)
    (s : actualComplexSection (n := n) U) (t : actualComplexSection (n := n) V)
    (heq : sectionExtension U s =ᶠ[𝓝 y] sectionExtension V t) :
    (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hyU s =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ V y hyV t := by
  obtain ⟨W,hWeq,hWopen,hyW⟩ := mem_nhds_iff.mp heq
  let Q : Opens M := ⟨W ∩ U ∩ V,(hWopen.inter U.isOpen).inter V.isOpen⟩
  have hyQ : y ∈ Q := ⟨⟨hyW,hyU⟩,hyV⟩
  have hQU : Q ≤ U := fun _ hz => hz.1.2
  have hQV : Q ≤ V := fun _ hz => hz.2
  apply (actualComplexStructureSheaf (n := n) M).presheaf.germ_ext Q hyQ
    (homOfLE hQU) (homOfLE hQV)
  apply ContMDiffMap.ext
  intro z
  change s ⟨z.1,hQU z.2⟩ = t ⟨z.1,hQV z.2⟩
  exact (sectionExtension_apply U s z.1 (hQU z.2)).symm.trans
    ((hWeq z.2.1.1).trans (sectionExtension_apply V t z.1 (hQV z.2)))

omit [IsComplexManifold n M] in
/-- Whole recentered equality reflects ORIGINAL equality through the REAL original chart identities. -/
theorem original_eventuallyEq_of_preferred_chart_eventuallyEq (y : M) (f g : M → ℂ)
    (heq : (fun z => f (preferredChartInverseMap (n := n) y z)) =ᶠ[𝓝 0]
      (fun z => g (preferredChartInverseMap (n := n) y z))) : f =ᶠ[𝓝 y] g := by
  let e := chartAt (ComplexModel n) y
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  have ht : Tendsto (fun z : M => e z - e y) (𝓝 y) (𝓝 0) := by
    have hc : ContinuousAt (fun z : M => e z - e y) y :=
      (e.continuousAt hy).sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [e.open_source.mem_nhds hy,ht.eventually heq] with z hz hfg
  change f (e.symm ((e z - e y) + e y)) = g (e.symm ((e z - e y) + e y)) at hfg
  rwa [sub_add_cancel,e.left_inv hz] at hfg

/-- No stalk equality certificate is assumed: genuine sections and actual chart identities prove injectivity. -/
theorem actualStalkToChartHom_injective (y : M) : Function.Injective (actualStalkToChartHom (n := n) y) := by
  intro a b hab
  let F := (actualComplexStructureSheaf (n := n) M).presheaf
  obtain ⟨U,hyU,s,rfl⟩ := F.exists_germ_eq a
  obtain ⟨V,hyV,t,rfl⟩ := F.exists_germ_eq b
  rw [actualStalkToChartHom_germ,actualStalkToChartHom_germ] at hab
  have hUhol := sectionExtension_holomorphicAt U s y hyU
  have hVhol := sectionExtension_holomorphicAt V t y hyV
  have hchart : (fun z => sectionExtension U s (preferredChartInverseMap (n := n) y z)) =ᶠ[𝓝 0]
      (fun z => sectionExtension V t (preferredChartInverseMap (n := n) y z)) := by
    apply (HolGerm.mk_eq_mk_iff
      (hf := translated_holomorphic (chartAt (ComplexModel n) y y)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) y) hUhol))
      (hg := translated_holomorphic (chartAt (ComplexModel n) y y)
        (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source (ComplexModel n) y) hVhol))).mp
    exact hab
  exact actual_section_germ_eq_of_extension_eventuallyEq U V y hyU hyV s t
    (original_eventuallyEq_of_preferred_chart_eventuallyEq y _ _ hchart)

/-- A whole original model representative pulls back through the REAL chart to an original holomorphic germ. -/
theorem holomorphicAt_comp_preferredChartForward (y : M) (G : ComplexModel n → ℂ)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) :
    HolomorphicAt n (fun z => G (chartAt (ComplexModel n) y z - chartAt (ComplexModel n) y y)) y := by
  let e := chartAt (ComplexModel n) y
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  have ht : Tendsto (fun z : M => e z - e y) (𝓝 y) (𝓝 0) := by
    have hc : ContinuousAt (fun z : M => e z - e y) y :=
      (e.continuousAt hy).sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  filter_upwards [e.open_source.mem_nhds hy,ht.eventually hG] with z hz hGz
  exact ((hGz.comp (e z) (differentiableAt_id.sub_const (e y))).mdifferentiableAt).comp z
    (mdifferentiableAt_chart (y₀ := y) hz)

/-- EVERY whole model germ has a genuine section preimage in the literal actual sheaf stalk. -/
theorem actualStalkToChartHom_surjective (y : M) : Function.Surjective (actualStalkToChartHom (n := n) y) := by
  intro g
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  let e := chartAt (ComplexModel n) y
  let f := fun z : M => G (e z - e y)
  have hf : HolomorphicAt n f y := holomorphicAt_comp_preferredChartForward y G hG
  obtain ⟨U,hyU,s,hsec⟩ := exists_actual_section_of_original_holomorphicAt y f hf
  refine ⟨(actualComplexStructureSheaf (n := n) M).presheaf.germ U y hyU s,?_⟩
  rw [actualStalkToChartHom_germ]
  change chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y)
    (sectionExtension U s) (sectionExtension_holomorphicAt U s y hyU) = HolGerm.mk G hG
  rw [chartTranslatedGerm_congr_original y _ f (sectionExtension_holomorphicAt U s y hyU) hf hsec]
  dsimp only [chartTranslatedGerm,translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  have htrans : Tendsto (fun z : ComplexModel n => z + e y) (𝓝 0) (𝓝 (e y)) := by
    have hc : ContinuousAt (fun z : ComplexModel n => z + e y) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  filter_upwards [htrans.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ y)))] with z hz
  change G (e (e.symm (z + e y)) - e y) = G z
  rw [e.right_inv hz,add_sub_cancel_right]

/-- The internally proved actual colimit homomorphism is a genuine whole ring equivalence. -/
def actualStalkChartEquiv (y : M) : actualComplexStructureStalk (n := n) y ≃+* HolGerm (ComplexModel n) :=
  RingEquiv.ofBijective (actualStalkToChartHom y)
    ⟨actualStalkToChartHom_injective y,actualStalkToChartHom_surjective y⟩

/-- The internally supplied actual ring equivalence retains EVERY original section germ formula. -/
theorem actualStalkChartEquiv_germ (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualComplexSection (n := n) U) :
    actualStalkChartEquiv y ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) =
      sectionChartRingHom U y hy s := actualStalkToChartHom_germ U y hy s

/-- The ACTUAL original function germ is a real section's colimit germ, using the internally proved local section existence. -/
def actualOriginalFunctionGerm (y : M) (f : M → ℂ) (hf : HolomorphicAt n f y) :
    actualComplexStructureStalk (n := n) y :=
  let data := exists_actual_section_of_original_holomorphicAt y f hf
  let U := Classical.choose data
  let hU := Classical.choose_spec data
  let hy := Classical.choose hU
  let hs := Classical.choose_spec hU
  let s := Classical.choose hs
  (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s

/-- Every actual ORIGINAL function germ maps to its SAME original chart representative. -/
theorem actualOriginalFunctionGerm_chart (y : M) (f : M → ℂ) (hf : HolomorphicAt n f y) :
    actualStalkChartEquiv y (actualOriginalFunctionGerm y f hf) =
      chartTranslatedGerm y y (mem_chart_source (ComplexModel n) y) f hf := by
  let data := exists_actual_section_of_original_holomorphicAt y f hf
  let U := Classical.choose data
  let hU := Classical.choose_spec data
  let hy := Classical.choose hU
  let hs := Classical.choose_spec hU
  let s := Classical.choose hs
  have hsec : sectionExtension U s =ᶠ[𝓝 y] f := Classical.choose_spec hs
  change actualStalkChartEquiv y
    ((actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s) = _
  rw [actualStalkChartEquiv_germ]
  exact chartTranslatedGerm_congr_original y _ f (sectionExtension_holomorphicAt U s y hy) hf hsec

/-- The actual function germ equals EVERY actual section representation, independently of its internally chosen neighbourhood. -/
theorem actualOriginalFunctionGerm_eq_section (U : Opens M) (y : M) (hy : y ∈ U)
    (s : actualComplexSection (n := n) U) (f : M → ℂ) (hf : HolomorphicAt n f y)
    (hsec : sectionExtension U s =ᶠ[𝓝 y] f) :
    actualOriginalFunctionGerm y f hf =
      (actualComplexStructureSheaf (n := n) M).presheaf.germ U y hy s := by
  apply (actualStalkChartEquiv y).injective
  rw [actualOriginalFunctionGerm_chart,actualStalkChartEquiv_germ]
  exact (chartTranslatedGerm_congr_original y _ f (sectionExtension_holomorphicAt U s y hy) hf hsec).symm

/-- ALL original membership-function germs generate the whole ideal in the LITERAL structure-sheaf stalk. -/
def actualWholeSheafStalkIdeal (A : GermIdeal n M) (y : M) : Ideal (actualComplexStructureStalk (n := n) y) :=
  Ideal.span {g | ∃ (f : M → ℂ) (hf : HolomorphicAt n f y),
    A.mem y f ∧ g = actualOriginalFunctionGerm y f hf}

/-- The entire actual stalk ideal maps to the ENTIRE original chart ideal, with BOTH span inclusions internally proved. -/
theorem map_actualWholeSheafStalkIdeal (A : GermIdeal n M) (y : M) :
    Ideal.map (actualStalkChartEquiv (n := n) y).toRingHom (actualWholeSheafStalkIdeal A y) =
      wholeChartStalkIdeal A y y (mem_chart_source (ComplexModel n) y) := by
  simp only [actualWholeSheafStalkIdeal,wholeChartStalkIdeal,Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_,⟨f,hf,hmem,rfl⟩,rfl⟩
    exact ⟨f,hf,hmem,actualOriginalFunctionGerm_chart y f hf⟩
  · rintro ⟨f,hf,hmem,rfl⟩
    exact ⟨actualOriginalFunctionGerm y f hf,⟨f,hf,hmem,rfl⟩,actualOriginalFunctionGerm_chart y f hf⟩

/-- Genuine inverse whole ideal images, used only after the actual stalk equivalence has been internally constructed. -/
theorem actualWholeSheafStalkIdeal_eq_map_chart (A : GermIdeal n M) (y : M) :
    actualWholeSheafStalkIdeal A y =
      Ideal.map (actualStalkChartEquiv (n := n) y).symm.toRingHom
        (wholeChartStalkIdeal A y y (mem_chart_source (ComplexModel n) y)) := by
  let E := actualStalkChartEquiv (n := n) y
  have he : E.symm.toRingHom.comp E.toRingHom = RingHom.id (actualComplexStructureStalk (n := n) y) := by
    apply RingHom.ext
    intro z
    exact E.symm_apply_apply z
  calc
    actualWholeSheafStalkIdeal A y =
        Ideal.map E.symm.toRingHom (Ideal.map E.toRingHom (actualWholeSheafStalkIdeal A y)) := by
      rw [Ideal.map_map,he,Ideal.map_id]
    _ = Ideal.map E.symm.toRingHom (wholeChartStalkIdeal A y y (mem_chart_source (ComplexModel n) y)) := by
      rw [map_actualWholeSheafStalkIdeal]

/-- ALL true original centre powers are retained by the actual structure-sheaf stalk equivalence. -/
theorem map_actualWholeSheafCentreIdeal_pow (C : Set M) (y : M) (q : ℕ) :
    Ideal.map (actualStalkChartEquiv (n := n) y).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) y ^ q) =
      wholeChartStalkIdeal (vanishingIdeal (n := n) C) y y (mem_chart_source (ComplexModel n) y) ^ q := by
  rw [Ideal.map_pow,map_actualWholeSheafStalkIdeal]

end Manifold

section Centre
variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original inputs INTERNALLY give ONE original centre open with ALL genuine relative modules free over the LITERAL complex structure-sheaf stalk quotient. -/
theorem exists_original_regular_all_relative_degrees_free_actual_sheaf_stalk_open
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ O : Set M, IsOpen O ∧ x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (_hyCO : y ∈ C ∩ O),
        allRelativeIdealDegreesFree (actualWholeSheafStalkIdeal A y)
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := d+t) C) y) := by
  obtain ⟨O,hO,hcl,hfree⟩ := exists_original_regular_intrinsic_all_stalk_degrees_free_centre_open C x hreg A hA hAC
  refine ⟨O,hO,hcl,?_⟩
  intro y hyCO
  have hc := (hfree y hyCO).1
  exact allRelativeIdealDegreesFree_of_ringEquiv _ _ _ _ (actualStalkChartEquiv y).symm
    (actualWholeSheafStalkIdeal_eq_map_chart A y)
    (actualWholeSheafStalkIdeal_eq_map_chart (vanishingIdeal (n := d+t) C) y) hc

end Centre

end
end Hironaka.HironakaSmoothCentreRealDomainActualSheafStalk
