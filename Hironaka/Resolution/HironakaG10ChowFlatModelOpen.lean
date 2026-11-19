import Hironaka.Resolution.HironakaG10ChowFlatGermOpen
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk

/-!
# Flat morphisms of embedded analytic models are open

Blueprint `hironaka-g10-chowside-flat-open.tex` (node `g10c:flat-model-open`).

Let `f : M → N` be a holomorphic map of complex manifolds, `C ⊆ M` analytic and `D ⊆ N` with
`f(C) ⊆ D`, and let `F = actualSubspaceMap f : (C, 𝒪_M ⧸ I_C) → (D, 𝒪_N ⧸ I_D)` be the induced
morphism of reduced models.  In the preferred charts the stalk map of `F` at `x` is
`[g] ↦ [g ∘ f̃]` with `f̃ = actualTranslatedMap f x` (`actualSubspaceMap_stalk_chart`).  Hence if
that stalk map is flat, `f` maps every neighbourhood of `x` in `C` onto a neighbourhood of
`f x` in `D` (`eventually_mem_image_of_stalk_flat`, from `HironakaG10ChowFlatGermOpen`).

Sorry-free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

namespace Hironaka.HironakaG10ChowFlatModelOpen

open Hironaka.HolomorphicIdealSheaves HironakaHolomorphicJetRankLoci
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspaceOpenRestriction HironakaHolomorphicJetChartInvariance

noncomputable section

/-! ### Chart germs of analytic subsets -/

section Manifold

variable {N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The germ at `0` of `A` read in the preferred chart at `x` and translated to the origin. -/
def translatedCarrier (A : Set M) (x : M) : Set (ComplexModel N) :=
  {z | z + chartAt (ComplexModel N) x x ∈ (chartAt (ComplexModel N) x).target ∧
    (chartAt (ComplexModel N) x).symm (z + chartAt (ComplexModel N) x x) ∈ A}

/-- The whole vanishing ideal of `A` at `x`, read in the preferred chart at `x`. -/
abbrev stalkIdeal (A : Set M) (x : M) : Ideal (HolGerm (ComplexModel N)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := N) A) x x (mem_chart_source _ x)

omit [IsComplexManifold N M] in
theorem tendsto_chart_symm_translate (x : M) :
    Tendsto (fun z : ComplexModel N =>
      (chartAt (ComplexModel N) x).symm (z + chartAt (ComplexModel N) x x))
      (𝓝 0) (𝓝 x) := by
  set e := chartAt (ComplexModel N) x
  have h1 : Tendsto (fun z : ComplexModel N => z + e x) (𝓝 0) (𝓝 (e x)) := by
    have hc : ContinuousAt (fun z : ComplexModel N => z + e x) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  have h2 : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto
    rwa [e.left_inv (mem_chart_source _ x)] at h
  exact h2.comp h1

omit [IsComplexManifold N M] in
theorem eventually_translate_mem_target (x : M) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel N),
      z + chartAt (ComplexModel N) x x ∈ (chartAt (ComplexModel N) x).target := by
  set e := chartAt (ComplexModel N) x
  have h1 : Tendsto (fun z : ComplexModel N => z + e x) (𝓝 0) (𝓝 (e x)) := by
    have hc : ContinuousAt (fun z : ComplexModel N => z + e x) 0 :=
      continuousAt_id.add continuousAt_const
    simpa only [zero_add] using hc.tendsto
  exact h1.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))

/-- The stalk ideal consists of germs vanishing on the translated carrier. -/
theorem stalkIdeal_le_vanishingIdeal (A : Set M) (x : M) :
    stalkIdeal (N := N) A x ≤
      AnalyticGermDecomposition.vanishingIdeal (translatedCarrier (N := N) A x) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, hmem, rfl⟩
  unfold chartTranslatedGerm translatedGerm
  refine AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr ?_
  filter_upwards [tendsto_chart_symm_translate (N := N) x |>.eventually hmem.2] with z hz hzA
  exact hz hzA.2

/-- **Local equations.**  An analytic subset is cut out near `x` by finitely many germs of the
stalk ideal. -/
theorem exists_localEquations {A : Set M} (hA : IsComplexAnalyticSubset (n := N) A) (x : M) :
    ∃ (s : ℕ) (g : Fin s → ComplexModel N → ℂ),
      (∀ j, ∃ h : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g j) z,
        HolGerm.mk (g j) h ∈ stalkIdeal (N := N) A x) ∧
      ∀ᶠ z in 𝓝 (0 : ComplexModel N), (∀ j, g j z = 0) →
        z ∈ translatedCarrier (N := N) A x := by
  obtain ⟨P⟩ := hA x
  set e := chartAt (ComplexModel N) x with he
  have hW : ∀ᶠ z in 𝓝 (0 : ComplexModel N), z + e x ∈ P.coordinateNeighborhood := by
    have h1 : Tendsto (fun z : ComplexModel N => z + e x) (𝓝 0) (𝓝 (e x)) := by
      have hc : ContinuousAt (fun z : ComplexModel N => z + e x) 0 :=
        continuousAt_id.add continuousAt_const
      simpa only [zero_add] using hc.tendsto
    exact h1.eventually (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
  refine ⟨P.generatorCount, fun j z => P.generator j (z + e x), fun j => ?_, ?_⟩
  · have hd : ∀ᶠ z in 𝓝 (0 : ComplexModel N),
        DifferentiableAt ℂ (fun z => P.generator j (z + e x)) z := by
      filter_upwards [hW] with z hz
      exact ((P.generator_holomorphic j).differentiableAt
        (P.isOpen_coordinateNeighborhood.mem_nhds hz)).comp z
          ((differentiableAt_id).add (differentiableAt_const _))
    refine ⟨hd, ?_⟩
    have hG : ∀ᶠ w in 𝓝 (0 : ComplexModel N),
        DifferentiableAt ℂ (fun w => P.generator j (w + e x)) w := hd
    have hhol : HolomorphicAt N (fun y => P.generator j (e y)) x := by
      have h := HironakaSmoothCentreRealDomainActualSheafStalk.holomorphicAt_comp_preferredChartForward
        x _ hG
      rw [← he] at h
      simpa only [sub_add_cancel] using h
    have hev : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ e y ∈ P.coordinateNeighborhood := by
      have hc : ContinuousAt e x := e.continuousAt (mem_chart_source _ x)
      have h1 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds (mem_chart_source _ x)
      exact h1.and
        (hc.eventually (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood))
    have hmem : (vanishingIdeal (n := N) A).mem x (fun y => P.generator j (e y)) := by
      refine ⟨hhol, ?_⟩
      filter_upwards [hev] with y hy hyA
      exact (P.zeroLocus hy.1 hy.2).mp hyA j
    refine Ideal.subset_span ⟨_, hhol, hmem, ?_⟩
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [eventually_translate_mem_target (N := N) x] with z hz
    change P.generator j (z + e x) = P.generator j (e (e.symm (z + e x)))
    rw [e.right_inv hz]
  · filter_upwards [hW] with z hz hg
    have ht : z + e x ∈ e.target := P.coordinateNeighborhood_subset_target hz
    refine ⟨ht, ?_⟩
    have hs : e.symm (z + e x) ∈ e.source := e.map_target ht
    have hes : e (e.symm (z + e x)) = z + e x := e.right_inv ht
    refine (P.zeroLocus hs ?_).mpr ?_
    · change (chartAt (ComplexModel N) x) (e.symm (z + e x)) ∈ _
      rw [← he, hes]
      exact hz
    · intro j
      change P.generator j ((chartAt (ComplexModel N) x) (e.symm (z + e x))) = 0
      rw [← he, hes]
      exact hg j

end Manifold

/-! ### The stalk map of a model morphism in the preferred charts -/

section Model

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The inclusion stalk map in the preferred chart is the quotient map. -/
theorem inclusion_stalk_chart (D : Set N) (x : D) (r : actualComplexStructureStalk (n := m) x.val) :
    actualSubspaceStalkChartEquiv (n := m) D x ((actualSubspaceInclusion (n := m) D).stalkMap x r) =
      Ideal.Quotient.mk _ (actualStalkChartEquiv (n := m) x.val r) := by
  change (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := m) x.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := m) D) x.val).symm)
    (actualSubspaceStalkWholeEquiv (n := m) D x ((actualSubspaceInclusion (n := m) D).stalkMap x r)) = _
  rw [actualSubspaceInclusion_stalk]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The stalk map of a model morphism is composition of chart germs.** -/
theorem actualSubspaceMap_stalk_chart {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C)
    (r : actualComplexStructureStalk (n := m) (f x.val)) :
    actualSubspaceStalkChartEquiv (n := n) C x ((actualSubspaceMap hf hCD).stalkMap x
      ((actualSubspaceInclusion (n := m) D).stalkMap (actualSubspaceMapTop hf hCD x) r)) =
      Ideal.Quotient.mk _ (actualHolomorphicGermPullback hf x.val
        (actualStalkChartEquiv (n := m) (f x.val) r)) := by
  have h := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hCD x) r
  simp only [ConcreteCategory.comp_apply] at h
  calc
    _ = actualSubspaceStalkChartEquiv (n := n) C x ((actualSubspaceInclusion (n := n) C).stalkMap x
          ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r)) :=
      congrArg (actualSubspaceStalkChartEquiv (n := n) C x) h
    _ = Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val
          ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r)) :=
      inclusion_stalk_chart C x _
    _ = _ := by rw [actualNativeStalk_chart_pullback]

/-- **Flat model morphisms are open.**  If the stalk map at `x` of the model morphism induced by a
holomorphic `f : M → N` with `f(C) ⊆ D`, `C` analytic, is flat, then for every neighbourhood `W`
of `x`, `f(C ∩ W)` contains a neighbourhood of `f x` in `D`. -/
theorem eventually_mem_image_of_stalk_flat {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hC : IsComplexAnalyticSubset (n := n) C) (hCD : ∀ x ∈ C, f x ∈ D)
    (x : C) (hflat : ((actualSubspaceMap hf hCD).stalkMap x).hom.Flat)
    {W : Set M} (hW : W ∈ 𝓝 x.val) :
    ∀ᶠ y in 𝓝 (f x.val), y ∈ D → y ∈ f '' (C ∩ W) := by
  classical
  set d : D := actualSubspaceMapTop hf hCD x with hd
  set IC := stalkIdeal (N := n) C x.val with hIC
  set ID := stalkIdeal (N := m) D (f x.val) with hID
  set κ := actualHolomorphicGermPullback hf x.val with hκ
  set G := actualTranslatedMap (n := m) (m := n) f x.val with hGdef
  have hG := actualTranslatedMap_holomorphic hf x.val
  have hG0 := actualTranslatedMap_zero (n := m) (m := n) f x.val
  set eC := actualSubspaceStalkChartEquiv (n := n) C x with heC
  set eD := actualSubspaceStalkChartEquiv (n := m) D d with heD
  -- `I_D ∘ f̃ ⊆ I_C`
  have hcomap : ID ≤ IC.comap (compAlgHom G hG hG0).toRingHom := by
    intro g hg
    obtain ⟨r, rfl⟩ := (actualStalkChartEquiv (n := m) (f x.val)).surjective g
    have h1 : eD ((actualSubspaceInclusion (n := m) D).stalkMap d r) = 0 := by
      rw [heD, inclusion_stalk_chart]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
    have h2 : (actualSubspaceInclusion (n := m) D).stalkMap d r = 0 :=
      eD.injective (h1.trans (map_zero eD).symm)
    have h3 := actualSubspaceMap_stalk_chart hf hCD x r
    rw [h2, map_zero, map_zero] at h3
    show κ (actualStalkChartEquiv (n := m) (f x.val) r) ∈ IC
    exact (Ideal.Quotient.eq_zero_iff_mem (I := IC)).mp h3.symm
  -- the germ map is conjugate to the stalk map
  have hφ : Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap =
      (eC.toRingHom.comp ((actualSubspaceMap hf hCD).stalkMap x).hom).comp eD.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext g
    obtain ⟨r, rfl⟩ := (actualStalkChartEquiv (n := m) (f x.val)).surjective g
    have h1 : eD.symm (Ideal.Quotient.mk ID (actualStalkChartEquiv (n := m) (f x.val) r)) =
        (actualSubspaceInclusion (n := m) D).stalkMap d r := by
      rw [RingEquiv.symm_apply_eq, heD, inclusion_stalk_chart]
      rfl
    change Ideal.Quotient.mk IC (κ (actualStalkChartEquiv (n := m) (f x.val) r)) =
      eC (((actualSubspaceMap hf hCD).stalkMap x).hom
        (eD.symm (Ideal.Quotient.mk ID (actualStalkChartEquiv (n := m) (f x.val) r))))
    rw [h1, heC, actualSubspaceMap_stalk_chart]
  have hφflat : (Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap).Flat := by
    rw [hφ]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective eD.symm.bijective)
      (RingHom.Flat.comp hflat (RingHom.Flat.of_bijective eC.bijective))
  -- local equations of `C` at `x`
  obtain ⟨q, c, hcI', hcC⟩ := exists_localEquations (N := n) hC x.val
  choose hc hcI using hcI'
  have h0C : (0 : ComplexModel n) ∈ translatedCarrier (N := n) C x.val := by
    refine ⟨?_, ?_⟩
    · rw [zero_add]
      exact (chartAt (ComplexModel n) x.val).map_source (mem_chart_source _ x.val)
    · rw [zero_add, (chartAt (ComplexModel n) x.val).left_inv (mem_chart_source _ x.val)]
      exact x.2
  -- the neighbourhood of `0` corresponding to `W`
  set eN := chartAt (ComplexModel m) (f x.val) with heN
  let U₀ : Set (ComplexModel n) := (fun z => (chartAt (ComplexModel n) x.val).symm
    (z + chartAt (ComplexModel n) x.val x.val)) ⁻¹' (W ∩ f ⁻¹' eN.source)
  have hU₀ : U₀ ∈ 𝓝 (0 : ComplexModel n) := by
    refine tendsto_chart_symm_translate (N := n) x.val (inter_mem hW ?_)
    exact hf.continuous.continuousAt.preimage_mem_nhds
      (eN.open_source.mem_nhds (mem_chart_source _ (f x.val)))
  have hev := HironakaG10ChowFlatGermOpen.eventually_mem_image_of_flat IC ID G hG hG0 hcomap
    (translatedCarrier (N := n) C x.val) (translatedCarrier (N := m) D (f x.val))
    (stalkIdeal_le_vanishingIdeal (N := n) C x.val) (stalkIdeal_le_vanishingIdeal (N := m) D (f x.val))
    h0C c hc hcI hcC hφflat U₀ hU₀
  -- back to `N`
  have hψ : Tendsto (fun y : N => eN y - eN (f x.val)) (𝓝 (f x.val)) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : N => eN y - eN (f x.val)) (f x.val) :=
      (eN.continuousAt (mem_chart_source _ (f x.val))).sub continuousAt_const
    simpa only [sub_self] using hcont.tendsto
  filter_upwards [hψ.eventually hev, eN.open_source.mem_nhds (mem_chart_source _ (f x.val))]
    with y hy hys hyD
  have hyD0 : eN y - eN (f x.val) ∈ translatedCarrier (N := m) D (f x.val) := by
    refine ⟨?_, ?_⟩
    · rw [sub_add_cancel]
      exact eN.map_source hys
    · rw [sub_add_cancel, eN.left_inv hys]
      exact hyD
  obtain ⟨z, ⟨hzC, hzU⟩, hzG⟩ := hy hyD0
  refine ⟨_, ⟨hzC.2, hzU.1⟩, ?_⟩
  have hfeq : eN (f ((chartAt (ComplexModel n) x.val).symm
      (z + chartAt (ComplexModel n) x.val x.val))) = eN y := by
    have h := hzG
    simp only [hGdef, actualTranslatedMap] at h
    exact sub_left_injective h
  exact eN.injOn hzU.2 hys hfeq

end Model

end

end Hironaka.HironakaG10ChowFlatModelOpen
