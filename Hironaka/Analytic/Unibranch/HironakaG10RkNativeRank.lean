import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular
import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference

/-!
# Native Remmert, item 5.3: the native rank and the rank-degeneracy set (lane G10R3)

Setting of `HironakaG10MwRemmertRegular` (lane G10MW): `Y` a native reduced complex space, second countable,
`φ : Y ⟶ ofClosedAnalytic C hC` a native morphism into a closed analytic subset of a complex manifold `M`,
`pointMap φ : Y → M`, the native rank `nativeRankAt d φ y` (the rank of `pointMap φ` on the manifold
`regLocus Y d`) and the rank-degeneracy set `rankDegeneracy d φ r = Sing(Y) ∪ {rank < r}`.

* `rankAt_eq_finrank_mfderiv`, `rankAt_eq_of_param`: the library rank `RankDegeneracy.rankAt` through `mfderiv`;
  at a regular point of dimension `m` of `A` it is the rank of `F ∘ ψ` for any holomorphic `ψ : P^m → A` with
  injective differential.
* `nativeRankAt_eq_rankAt_lift` (**chart bridge**): in every local embedding `(Ω, C)` of `Y`, for every holomorphic
  lift `G : W → M` (`W ⊆ Ω` open) of `pointMap φ`, `nativeRankAt d φ y = rankAt G (C ∩ W) c`.
* `isAnalyticSubset_rankDegeneracy`: for `Y` of pure dimension `d`, `rankDegeneracy d φ r` is analytic.
* `exists_maxRank_of_irreducible`: for `Y` irreducible of pure dimension `d` there is a maximal rank `r`, and
  `rankDegeneracy d φ r` is a proper analytic subset with empty interior.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Set TopologicalSpace Topology Filter CategoryTheory AlgebraicGeometry Module
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  RankDegeneracy AnalyticDimensionBasics HironakaG10MwRemmertRegular
  Hironaka.HolomorphicIdealSheaves

noncomputable section

/-! ### The library rank through `mfderiv` -/

section Manifold

variable {n n' m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n') Z]
  [IsComplexManifold n' Z] {P : Type*} [TopologicalSpace P] [ChartedSpace (ComplexModel m) P]
  [IsComplexManifold m P]

variable (n n') in
/-- The differential `mfderiv`, as a continuous linear map between the model spaces. -/
abbrev mfd (F : X → Z) (x : X) : ComplexModel n →L[ℂ] ComplexModel n' :=
  mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F x

/-- `mfderiv` is the differential read in the preferred charts. -/
theorem mfderiv_eq_chartDeriv {F : X → Z} {x : X}
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F x) :
    mfd n n' F x = chartDeriv (complexChartAt (n := n) x) (complexChartAt (n := n') (F x)) F x := by
  show mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F x = _
  rw [hF.mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

/-- The tangent space of `univ` is everything. -/
theorem tangentSpaceIn_univ (e : ComplexChart n X) {x : X} (hx : x ∈ e.val.source) :
    tangentSpaceIn e (univ : Set X) x = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [mem_tangentSpaceIn]
  intro g hg
  have hq : e.val x ∈ e.val.target := e.val.map_source hx
  have hz : (fun w => g (e.val.symm w)) =ᶠ[𝓝 (e.val x)] fun _ => 0 := by
    have hlim : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
      have := e.val.continuousAt_symm hq
      rwa [ContinuousAt, e.val.left_inv hx] at this
    filter_upwards [hlim.eventually hg.2] with w hw
    exact hw (mem_univ _)
  rw [hz.fderiv_eq, fderiv_const_apply]
  rfl

/-- **The rank on `univ` is the rank of `mfderiv`.** -/
theorem rankAt_univ_eq_finrank_mfderiv {F : X → Z} {x : X}
    (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F x) :
    rankAt (n := n) (n' := n') F univ x =
      finrank ℂ (LinearMap.range (mfd n n' F x : ComplexModel n →ₗ[ℂ] ComplexModel n')) := by
  unfold rankAt rankIn
  rw [tangentSpaceIn_univ _ (mem_complexChartAt_source x), Submodule.map_top,
    mfderiv_eq_chartDeriv hF]

/-- **The rank through a parametrization.**  If `A` is regular of dimension `m` at `x` and `ψ : P → X`
(`dim P = m`) is holomorphic at `p`, maps a neighbourhood of `p` into `A`, sends `p` to `x` and has injective
differential, then the rank of `F` on `A` at `x` is the rank of the differential of `F ∘ ψ` at `p`. -/
theorem rankAt_eq_of_param {A : Set X} {x : X} (hA : RegularAtDim (n := n) A x m)
    {ψ : P → X} {p : P} (hψp : ψ p = x)
    (hψ : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ψ p)
    (hψA : ∀ᶠ q in 𝓝 p, ψ q ∈ A)
    (hinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ψ p))
    {F : X → Z} (hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') F x) :
    rankAt (n := n) (n' := n') F A x =
      finrank ℂ (LinearMap.range (mfd m n' (F ∘ ψ) p : ComplexModel m →ₗ[ℂ] ComplexModel n')) := by
  subst hψp
  set e := complexChartAt (n := n) (ψ p) with he
  set eP := complexChartAt (n := m) p with heP
  set Dψ : ComplexModel m →L[ℂ] ComplexModel n :=
    mfderiv 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ψ p with hDψ
  have hxe : ψ p ∈ e.val.source := mem_complexChartAt_source _
  have hpe : p ∈ eP.val.source := mem_complexChartAt_source _
  have hqP : eP.val p ∈ eP.val.target := eP.val.map_source hpe
  have hqe : e.val (ψ p) ∈ e.val.target := e.val.map_source hxe
  -- the differential of `ψ` read in charts
  have hDψc : Dψ = fderiv ℂ (fun w => e.val (ψ (eP.val.symm w))) (eP.val p) :=
    mfderiv_eq_chartDeriv hψ
  have hdψ : DifferentiableAt ℂ (fun w => e.val (ψ (eP.val.symm w))) (eP.val p) :=
    differentiableAt_chartReading eP e hpe hxe hψ
  -- the range of `dψ` lies in the tangent space
  have hle : LinearMap.range (Dψ : ComplexModel m →ₗ[ℂ] ComplexModel n) ≤ tangentSpaceIn e A (ψ p) := by
    rintro _ ⟨u, rfl⟩
    rw [mem_tangentSpaceIn]
    intro g hg
    have hgd : DifferentiableAt ℂ (fun w => g (e.val.symm w)) (e.val (ψ p)) :=
      StokesSingularLocusAnalytic.differentiableAt_chart e hqe
        (by rw [e.val.left_inv hxe]; exact hg.1.self_of_nhds)
    have hψc : ContinuousAt ψ p := hψ.continuousAt
    have hlimP : Tendsto eP.val.symm (𝓝 (eP.val p)) (𝓝 p) := by
      have := (eP.val.continuousAt_symm hqP).tendsto
      rwa [eP.val.left_inv hpe] at this
    have hlim : Tendsto (fun w => ψ (eP.val.symm w)) (𝓝 (eP.val p)) (𝓝 (ψ p)) :=
      (hψc.tendsto).comp hlimP
    have hzero : (fun w => g (e.val.symm (e.val (ψ (eP.val.symm w))))) =ᶠ[𝓝 (eP.val p)]
        fun _ => 0 := by
      filter_upwards [hlim.eventually hg.2, hlim.eventually (e.val.open_source.mem_nhds hxe),
        hlimP.eventually hψA] with w hw hws hwA
      rw [e.val.left_inv hws]
      exact hw hwA
    have hc := fderiv_comp_of_eq (g := fun w => g (e.val.symm w))
      (f := fun w => e.val (ψ (eP.val.symm w))) (by rw [eP.val.left_inv hpe]) hgd hdψ
    rw [hzero.fderiv_eq, fderiv_const_apply] at hc
    have h := congrArg (fun L => L u) hc
    rw [hDψc]
    simpa using h.symm
  -- equality by dimension
  have hfin : finrank ℂ (tangentSpaceIn e A (ψ p)) = m :=
    finrank_tangentSpaceIn_of_regularAtDim e hxe hA
  have hfinR : finrank ℂ (LinearMap.range (Dψ : ComplexModel m →ₗ[ℂ] ComplexModel n)) = m := by
    rw [LinearMap.finrank_range_of_inj (f := (Dψ : ComplexModel m →ₗ[ℂ] ComplexModel n)) hinj,
      finrank_euclideanSpace, Fintype.card_fin]
  have heq : LinearMap.range (Dψ : ComplexModel m →ₗ[ℂ] ComplexModel n) = tangentSpaceIn e A (ψ p) :=
    Submodule.eq_of_le_of_finrank_eq hle (hfinR.trans hfin.symm)
  -- the rank
  have hcomp : mfd m n' (F ∘ ψ) p = (mfd n n' F (ψ p)).comp Dψ := mfderiv_comp p hF hψ
  have hFe : mfd n n' F (ψ p) = chartDeriv e (complexChartAt (n := n') (F (ψ p))) F (ψ p) :=
    mfderiv_eq_chartDeriv hF
  rw [hcomp]
  show finrank ℂ ((tangentSpaceIn e A (ψ p)).map
    ((chartDeriv e (complexChartAt (n := n') (F (ψ p))) F (ψ p) : ComplexModel n →L[ℂ] ComplexModel n') :
      ComplexModel n →ₗ[ℂ] ComplexModel n')) = _
  rw [← heq, ← hFe, ← LinearMap.range_comp]
  rfl

end Manifold

/-! ### Extension of maps defined on open subsets -/

section Extend

open Classical in
/-- A map defined on an open subset, extended by a constant. -/
def extendOpens {α β : Type*} [TopologicalSpace α] (U : Opens α) (f : U → β) (b : β) : α → β :=
  fun x => if h : x ∈ U then f ⟨x, h⟩ else b

theorem extendOpens_of_mem {α β : Type*} [TopologicalSpace α] (U : Opens α) (f : U → β) (b : β)
    {x : α} (h : x ∈ U) : extendOpens U f b x = f ⟨x, h⟩ := by
  unfold extendOpens
  exact dif_pos h

theorem extendOpens_comp_val {α β : Type*} [TopologicalSpace α] (U : Opens α) (f : U → β) (b : β) :
    (fun x : U => extendOpens U f b x) = f := by
  funext x
  exact extendOpens_of_mem U f b x.property

theorem contMDiffAt_extendOpens {n n' : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n') Z] (U : Opens X) {f : U → Z} (b : Z) {x : X} (hx : x ∈ U)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ f ⟨x, hx⟩) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ (extendOpens U f b) x := by
  have h := hf
  rw [← extendOpens_comp_val U f b] at h
  exact contMDiffAt_subtype_iff.mp h

end Extend

/-! ### Regular charts as local embeddings; ambient lifts -/

section Native

open HironakaActualAnalyticSubspaceManifoldCharts HironakaResolutionSpaceComplex

variable {Y : SourceReducedComplexSpace} {d k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {C : Set M}
  {hC : IsComplexAnalyticSubset (n := k) C}

/-- A regular chart of dimension `d` as a local embedding with ambient its domain and carrier `univ`. -/
abbrev regChartEmbedding (D : RegChart Y d) : LocalEmbedding Y where
  dim := d
  ambient := D.domain
  carrier := univ
  analytic := isComplexAnalyticSubset_univ
  map := (actualSubspaceUnivIso (n := d) (M := D.domain)).hom ≫ D.map
  isOpenImmersion := by
    let := D.openImmersion
    infer_instance
  overPoint := by
    rw [Category.assoc, D.overPoint]
    rfl

theorem regChartEmbedding_toPoint (D : RegChart Y d) (w : (regChartEmbedding D).carrier) :
    (regChartEmbedding D).toPoint w = D.map.base w.val := rfl

theorem regChart_injective_base (D : RegChart Y d) : Function.Injective D.map.base :=
  D.openImmersion.base_open.injective

/-- **Ambient lifts.**  Near every carrier point of every local embedding, `pointMap φ` is the restriction of
a holomorphic map on an open subset of the ambient space. -/
theorem exists_lift (φ : Y ⟶ ofClosedAnalytic C hC) (a : LocalEmbedding Y) (c : a.carrier) :
    ∃ W : Opens a.ambient, c.val ∈ W ∧ ∃ G : W → M,
      ContMDiff 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) ∞ G ∧
      ∀ (c' : a.carrier) (h : c'.val ∈ W), G ⟨c'.val, h⟩ = pointMap φ (a.toPoint c') := by
  obtain ⟨x, hx⟩ : ∃ x : M, x = pointMap φ (a.toPoint c) := ⟨_, rfl⟩
  have hw : φ.hom.left ≫ (ofClosedAnalytic C hC).obj.hom = Y.obj.hom := Over.w φ.hom
  have hF : (a.map ≫ φ.hom.left) ≫ (ofClosedAnalytic C hC).obj.hom =
      (modelOver a.ambient a.carrier).hom := by
    rw [Category.assoc, hw, a.overPoint]
  have hc : (a.map ≫ φ.hom.left).base c ∈ range (LocalEmbedding.ofChart C hC x).toPoint := by
    have hxC : x ∈ C := hx ▸ (φ.hom.left.base (a.toPoint c)).property
    obtain ⟨z, hz⟩ := mem_range_chartModelMap (n := k) C hxC
    refine ⟨z, ?_⟩
    change (chartModelMap (n := k) C x).base z = φ.hom.left.base (a.map.base c)
    rw [hz]
    exact Subtype.ext hx
  obtain ⟨O, hcO, f, hf, hfac⟩ :=
    LocalEmbedding.exists_contMDiff_factor (a.map ≫ φ.hom.left) hF (LocalEmbedding.ofChart C hC x) c hc
  refine ⟨O, hcO, fun w => (((chartDiffeo (n := k) x).symm (f w) : chartDomain (n := k) x) : M),
    contMDiff_subtype_val.comp ((chartDiffeo (n := k) x).symm.contMDiff.comp hf), ?_⟩
  intro c' h
  obtain ⟨z, hz, hzt⟩ := hfac c' h
  have h2 : ((LocalEmbedding.ofChart C hC x).toPoint z).val = pointMap φ (a.toPoint c') := by
    rw [hzt]
    rfl
  rw [← h2]
  show (((chartDiffeo (n := k) x).symm (f ⟨c'.val, h⟩) : chartDomain (n := k) x) : M) =
    ((chartModelMap (n := k) C x).base z).val
  rw [← hz]
  rfl

/-! ### The chart bridge -/

/-- **The bridge for an arbitrary regular chart.**  If `G : W → M` is a holomorphic lift of `pointMap φ` in
a local embedding `a`, then the rank of `G` on the carrier at `c` equals the rank of `pointMap φ` read in any
regular chart `(D, v)` at the same point. -/
theorem rankAt_lift_eq_rankAt_regChart (φ : Y ⟶ ofClosedAnalytic C hC) (D : RegChart Y d)
    (v : D.domain) (a : LocalEmbedding Y) (c : a.carrier) (hcv : a.toPoint c = D.map.base v)
    (W : Opens a.ambient) (hcW : c.val ∈ W) (G : W → M)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) ∞ G)
    (hGl : ∀ (c' : a.carrier) (h : c'.val ∈ W), G ⟨c'.val, h⟩ = pointMap φ (a.toPoint c')) :
    rankAt (n := a.dim) (n' := k) G ((↑) ⁻¹' a.carrier : Set W) ⟨c.val, hcW⟩ =
      rankAt (n := d) (n' := k) (fun w : D.domain => pointMap φ (D.map.base w)) univ v := by
  classical
  -- regularity of the carrier at `c`
  have hreg : RegularAtDim (n := a.dim) a.carrier c.val d :=
    (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y a c d).mp
      (by rw [hcv]; exact D.mem_regLocus v)
  have hregW : RegularAtDim (n := a.dim) ((↑) ⁻¹' a.carrier : Set W) ⟨c.val, hcW⟩ d :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hreg
  -- the parametrization `ψ₀` of the carrier by the chart
  obtain ⟨O₁, hvO₁, ψ₀, hψ₀, hfac₁⟩ := LocalEmbedding.exists_contMDiff_factor
    (regChartEmbedding D).map (regChartEmbedding D).overPoint a
    (⟨v, trivial⟩ : (regChartEmbedding D).carrier) ⟨c, hcv⟩
  -- the inverse `H₀` of the chart, read on the carrier
  obtain ⟨O₂, hcO₂, H₀, hH₀, hfac₂⟩ := LocalEmbedding.exists_contMDiff_factor a.map a.overPoint
    (regChartEmbedding D) c ⟨⟨v, trivial⟩, hcv.symm⟩
  -- extensions
  set ψ₁ : D.domain → a.ambient := extendOpens O₁ ψ₀ c.val with hψ₁
  have hψ₁v : ψ₁ v = c.val := by
    rw [hψ₁, extendOpens_of_mem O₁ ψ₀ c.val hvO₁]
    obtain ⟨z, hz, hzt⟩ := hfac₁ ⟨v, trivial⟩ hvO₁
    have hzc : z = c := a.toPoint_injective (hzt.trans hcv.symm)
    rw [← hz, hzc]
  have hψ₁d : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ∞ ψ₁ v :=
    contMDiffAt_extendOpens O₁ c.val hvO₁ (hψ₀ _)
  set ψ : D.domain → W := fun q => if h : ψ₁ q ∈ W then ⟨ψ₁ q, h⟩ else ⟨c.val, hcW⟩ with hψ
  have hWev : ∀ᶠ q in 𝓝 v, ψ₁ q ∈ W ∧ ψ₁ q ∈ O₂ ∧ q ∈ O₁ := by
    have hcont := hψ₁d.continuousAt
    have h1 : ∀ᶠ q in 𝓝 v, ψ₁ q ∈ W :=
      hcont.preimage_mem_nhds (by rw [hψ₁v]; exact W.isOpen.mem_nhds hcW)
    have h2 : ∀ᶠ q in 𝓝 v, ψ₁ q ∈ O₂ :=
      hcont.preimage_mem_nhds (by rw [hψ₁v]; exact O₂.isOpen.mem_nhds hcO₂)
    have h3 : ∀ᶠ q in 𝓝 v, q ∈ O₁ := O₁.isOpen.mem_nhds hvO₁
    exact h1.and (h2.and h3)
  have hψval : (fun q => (ψ q : a.ambient)) =ᶠ[𝓝 v] ψ₁ := by
    filter_upwards [hWev] with q hq
    simp only [hψ, dif_pos hq.1]
  have hψv : ψ v = ⟨c.val, hcW⟩ := by
    apply Subtype.ext
    simp only [hψ, dif_pos (show ψ₁ v ∈ W by rw [hψ₁v]; exact hcW), hψ₁v]
  have hψd : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ∞ ψ v := by
    rw [← ContMDiffAt.subtypeVal_comp_iff]
    exact hψ₁d.congr_of_eventuallyEq hψval
  set H : W → D.domain := fun q => extendOpens O₂ H₀ v q.val with hH
  have hHd : ContMDiffAt 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel d) ∞ H ⟨c.val, hcW⟩ := by
    show ContMDiffAt 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel d) ∞
      (fun q : W => extendOpens O₂ H₀ v q.val) ⟨c.val, hcW⟩
    exact (contMDiffAt_extendOpens (n := a.dim) (n' := d) O₂ v hcO₂ (hH₀ _)).comp
      (⟨c.val, hcW⟩ : W) contMDiff_subtype_val.contMDiffAt
  -- the key identities near `v`
  have hkey : ∀ᶠ q in 𝓝 v, (ψ q : a.ambient) ∈ a.carrier ∧ H (ψ q) = q ∧
      G (ψ q) = pointMap φ (D.map.base q) := by
    filter_upwards [hWev] with q hq
    obtain ⟨hqW, hqO₂, hqO₁⟩ := hq
    have hψq : (ψ q : a.ambient) = ψ₁ q := by simp only [hψ, dif_pos hqW]
    obtain ⟨z, hz, hzt⟩ := hfac₁ ⟨q, trivial⟩ hqO₁
    have hzq : z.val = ψ₁ q := by rw [hψ₁, extendOpens_of_mem O₁ ψ₀ c.val hqO₁]; exact hz
    have hzt' : a.toPoint z = D.map.base q := hzt
    refine ⟨by rw [hψq, ← hzq]; exact z.property, ?_, ?_⟩
    · have hzO₂ : z.val ∈ O₂ := by rw [hzq]; exact hqO₂
      obtain ⟨z', hz', hz't⟩ := hfac₂ z hzO₂
      have h1 : D.map.base z'.val = a.toPoint z := hz't
      have h2 : H (ψ q) = H₀ ⟨z.val, hzO₂⟩ := by
        show extendOpens O₂ H₀ v (ψ q : a.ambient) = _
        rw [hψq, ← hzq, extendOpens_of_mem O₂ H₀ v hzO₂]
      rw [h2, ← hz']
      exact regChart_injective_base D (h1.trans hzt')
    · have h1 : ψ q = ⟨z.val, by rw [hzq]; exact hqW⟩ := Subtype.ext (hψq.trans hzq.symm)
      rw [h1, hGl z, hzt']
  -- the differential of `ψ` is injective
  have hinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel a.dim) ψ v) := by
    have hHψ : (H ∘ ψ) =ᶠ[𝓝 v] id := by
      filter_upwards [hkey] with q hq
      exact hq.2.1
    have hHd' : MDifferentiableAt 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel d) H (ψ v) := by
      rw [hψv]; exact hHd.mdifferentiableAt (by simp)
    have hc : mfd d d (H ∘ ψ) v = (mfd a.dim d H (ψ v)).comp (mfd d a.dim ψ v) :=
      mfderiv_comp v hHd' (hψd.mdifferentiableAt (by simp))
    have hid : mfd d d (H ∘ ψ) v = ContinuousLinearMap.id ℂ (ComplexModel d) := by
      rw [mfd, hHψ.mfderiv_eq, mfderiv_id]
      rfl
    have hall : ∀ u, mfd a.dim d H (ψ v) (mfd d a.dim ψ v u) = u := fun u =>
      ContinuousLinearMap.ext_iff.mp (hc.symm.trans hid) u
    intro u u' huu
    calc u = mfd a.dim d H (ψ v) (mfd d a.dim ψ v u) := (hall u).symm
      _ = mfd a.dim d H (ψ v) (mfd d a.dim ψ v u') := congrArg (mfd a.dim d H (ψ v)) huu
      _ = u' := hall u'
  -- conclude
  have hGd : MDifferentiableAt 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) G ⟨c.val, hcW⟩ :=
    (hG _).mdifferentiableAt (by simp)
  have hφd : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k)
      (fun w : D.domain => pointMap φ (D.map.base w)) v :=
    (contMDiff_pointMap_comp D φ v).mdifferentiableAt (by simp)
  rw [rankAt_eq_of_param hregW hψv (hψd.mdifferentiableAt (by simp))
      (hkey.mono fun q hq => hq.1) hinj hGd,
    rankAt_univ_eq_finrank_mfderiv hφd]
  have hev : (G ∘ ψ) =ᶠ[𝓝 v] fun w : D.domain => pointMap φ (D.map.base w) := by
    filter_upwards [hkey] with q hq
    exact hq.2.2
  show finrank ℂ (LinearMap.range (mfd d k (G ∘ ψ) v : ComplexModel d →ₗ[ℂ] ComplexModel k)) = _
  rw [mfd, hev.mfderiv_eq]

/-- **The native rank read in the chosen regular chart.** -/
theorem nativeRankAt_eq_rankAt_regChartAt [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) (y : regLocus Y d) (v : (regChartAt y).domain)
    (hv : (regChartAt y).pointMap v = y) :
    nativeRankAt d φ y = rankAt (n := d) (n' := k)
      (fun w : (regChartAt y).domain => pointMap φ ((regChartAt y).map.base w)) univ v := by
  have hF1 : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) (regPointMap d φ) y :=
    (contMDiff_regPointMap φ y).mdifferentiableAt (by simp)
  have hF2 : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k)
      (fun w : (regChartAt y).domain => pointMap φ ((regChartAt y).map.base w)) v :=
    (contMDiff_pointMap_comp (regChartAt y) φ v).mdifferentiableAt (by simp)
  rw [nativeRankAt, rankAt_univ_eq_finrank_mfderiv hF1, rankAt_univ_eq_finrank_mfderiv hF2,
    mfderiv_eq_chartDeriv hF1, mfderiv_eq_chartDeriv hF2]
  have hbv : (regChartAt y).map.base v = y.val := congrArg Subtype.val hv
  have hFv : pointMap φ ((regChartAt y).map.base v) = regPointMap d φ y := by
    rw [hbv]
    rfl
  have h1 : (complexChartAt (n := d) y).val y = v.val := by
    change (regChartAt y).chart y = v.val
    have h := (regChartAt y).chart_pointMap v
    rw [hv] at h
    exact h
  have h2 : (complexChartAt (n := d) v).val v = v.val := rfl
  have hder : chartDeriv (complexChartAt (n := d) y) (complexChartAt (n := k) (regPointMap d φ y))
      (regPointMap d φ) y = chartDeriv (complexChartAt (n := d) v)
      (complexChartAt (n := k) (pointMap φ ((regChartAt y).map.base v)))
      (fun w : (regChartAt y).domain => pointMap φ ((regChartAt y).map.base w)) v := by
    unfold chartDeriv
    rw [hFv, h1, h2]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(regChartAt y).domain.isOpen.mem_nhds v.property,
      TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (regChartAt y).domain (x := v)] with w hw hw'
    have e1 : (complexChartAt (n := d) y).val.symm w = (regChartAt y).pointMap ⟨w, hw⟩ := (regChartAt y).chart_symm w hw
    have e2 : (complexChartAt (n := d) v).val.symm w = ⟨w, hw⟩ := Subtype.ext hw'.symm
    rw [e1, e2]
    rfl
  rw [hder]

/-- **The chart bridge** (item 5.3, chart independence).  In every local embedding `a` of `Y`, for every
holomorphic lift `G : W → M` of `pointMap φ` on an open `W ⊆ Ω` (`Ω` the ambient space), the native rank at a
regular point of dimension `d` is the library rank of `G` on the carrier. -/
theorem nativeRankAt_eq_rankAt_lift [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) (a : LocalEmbedding Y) (c : a.carrier)
    (hc : a.toPoint c ∈ regLocus Y d) (W : Opens a.ambient) (hcW : c.val ∈ W) (G : W → M)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel a.dim) 𝓘(ℂ, ComplexModel k) ∞ G)
    (hGl : ∀ (c' : a.carrier) (h : c'.val ∈ W), G ⟨c'.val, h⟩ = pointMap φ (a.toPoint c')) :
    nativeRankAt d φ ⟨a.toPoint c, hc⟩ =
      rankAt (n := a.dim) (n' := k) G ((↑) ⁻¹' a.carrier : Set W) ⟨c.val, hcW⟩ := by
  obtain ⟨v, hv⟩ := mem_range_regChartAt (⟨a.toPoint c, hc⟩ : regLocus Y d)
  rw [nativeRankAt_eq_rankAt_regChartAt φ _ v hv,
    rankAt_lift_eq_rankAt_regChart φ (regChartAt _) v a c (congrArg Subtype.val hv).symm W hcW G hG hGl]

/-- The native rank at a regular point of dimension `d` is at most `d`. -/
theorem nativeRankAt_le [SecondCountableTopology Y.obj.left] (φ : Y ⟶ ofClosedAnalytic C hC)
    (y : regLocus Y d) : nativeRankAt d φ y ≤ d := by
  rw [nativeRankAt, rankAt_univ_eq_finrank_mfderiv ((contMDiff_regPointMap φ y).mdifferentiableAt
    (by simp))]
  calc _ ≤ finrank ℂ (ComplexModel d) := LinearMap.finrank_range_le _
    _ = d := by rw [finrank_euclideanSpace, Fintype.card_fin]

/-! ### Analyticity of the rank-degeneracy set -/

/-- **A local criterion for native analyticity** (converse of `IsAnalyticSubset.exists_local_trace`). -/
theorem isAnalyticSubset_of_local {A : Set Y.obj.left}
    (h : ∀ (e : LocalEmbedding Y) (c : e.carrier), ∃ O : Opens e.ambient, c.val ∈ O ∧ ∃ A'' : Set O,
      IsComplexAnalyticSubset (n := e.dim) A'' ∧
        ∀ (y : e.carrier) (hy : y.val ∈ O), e.toPoint y ∈ A ↔ (⟨y.val, hy⟩ : O) ∈ A'') :
    Y.IsAnalyticSubset A := by
  intro x
  let e := LocalEmbedding.ofPoint Y x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint Y x, HironakaG10EpNativeDim.trace e A, ?_, ?_⟩
  · apply AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
    intro u
    by_cases hu : u ∈ e.carrier
    · obtain ⟨O, huO, A'', hA'', hiff⟩ := h e ⟨u, hu⟩
      refine ⟨O, huO, ?_⟩
      have hCO : IsComplexAnalyticSubset (n := e.dim) ((↑) ⁻¹' e.carrier : Set O) :=
        AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O
      have heq : ((↑) ⁻¹' HironakaG10EpNativeDim.trace e A : Set O) =
          A'' ∩ ((↑) ⁻¹' e.carrier : Set O) := by
        ext o
        constructor
        · rintro ⟨b, hb, hbo⟩
          have hoC : (o : e.ambient) ∈ e.carrier := hbo ▸ b.property
          refine ⟨?_, hoC⟩
          apply (hiff ⟨o.val, hoC⟩ o.property).mp
          have : (⟨o.val, hoC⟩ : e.carrier) = b := Subtype.ext hbo.symm
          rw [this]
          exact hb
        · rintro ⟨ho, hoC⟩
          exact ⟨⟨o.val, hoC⟩, (hiff ⟨o.val, hoC⟩ o.property).mpr ho, rfl⟩
      rw [heq]
      exact hA''.inter hCO
    · refine ⟨⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩, hu, ?_⟩
      have he : ((↑) ⁻¹' HironakaG10EpNativeDim.trace e A :
          Set (⟨e.carrierᶜ, e.analytic.isClosed.isOpen_compl⟩ : Opens e.ambient)) = ∅ := by
        ext o
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨b, -, hbo⟩
        exact o.property (hbo ▸ b.property)
      rw [he]
      exact isComplexAnalyticSubset_empty
  · ext c
    exact (HironakaG10EpNativeDim.mem_trace e A c).symm

/-- Regular points of the carrier of a local embedding restricted to an open `W` of the ambient space are the
intrinsic regular points. -/
theorem regularAtDim_carrier_restrict_iff (a : LocalEmbedding Y) (W : Opens a.ambient) (c : a.carrier)
    (hcW : c.val ∈ W) (j : ℕ) :
    RegularAtDim (n := a.dim) ((↑) ⁻¹' a.carrier : Set W) ⟨c.val, hcW⟩ j ↔
      intrinsicRegularAtDim Y.obj (a.toPoint c) j :=
  AnalyticSubsetOpens.regularAtDim_preimage_val_iff.trans
    (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y a c j).symm

/-- **The rank-degeneracy set is analytic** (item 5.3): for `Y` of pure dimension `d`, the set
`Sing(Y) ∪ {y ∈ Reg_d(Y) | rank_y φ < r}` is a native analytic subset, for every `r`. -/
theorem isAnalyticSubset_rankDegeneracy [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) (hY : NativePureDim Y d) (r : ℕ) :
    Y.IsAnalyticSubset (rankDegeneracy d φ r) := by
  apply isAnalyticSubset_of_local
  intro a c
  obtain ⟨W, hcW, G, hG, hGl⟩ := exists_lift φ a c
  set A' : Set W := (↑) ⁻¹' a.carrier with hA'
  have hA'a : IsComplexAnalyticSubset (n := a.dim) A' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val a.analytic W
  have hpure : IsPureDim (n := a.dim) A' d := by
    intro z j hz
    have hzC : (z : a.ambient) ∈ a.carrier := hz.2.1
    have hz' : RegularAtDim (n := a.dim) A' ⟨(⟨z.val, hzC⟩ : a.carrier).val, z.property⟩ j := hz
    exact hY _ j ((regularAtDim_carrier_restrict_iff a W ⟨z.val, hzC⟩ z.property j).mp hz')
  refine ⟨W, hcW, rankDegeneracyLocus a.dim k G A' d r,
    isComplexAnalyticSubset_rankDegeneracyLocus hA'a hpure (hG.mdifferentiable (by simp)) r, ?_⟩
  intro y hy
  have hyA' : (⟨y.val, hy⟩ : W) ∈ A' := y.property
  have hreg := regularAtDim_carrier_restrict_iff a W y hy d
  have hsing : a.toPoint y ∈ intrinsicSingularLocus Y.obj ↔
      ¬ intrinsicRegularAtDim Y.obj (a.toPoint y) d := by
    constructor
    · intro h hr
      exact h ⟨d, hr⟩
    · rintro h ⟨j, hj⟩
      exact h (hY _ j hj ▸ hj)
  simp only [rankDegeneracy, rankDegeneracyLocus, mem_union, mem_ofPred_eq, Set.mem_sdiff, regularLocus]
  rw [hsing]
  constructor
  · rintro (h | ⟨hr, hlt⟩)
    · exact Or.inl ⟨hyA', fun h' => h (hreg.mp h')⟩
    · rw [nativeRankAt_eq_rankAt_lift φ a y hr W hy G hG hGl] at hlt
      exact Or.inr ⟨hreg.mpr hr, hlt⟩
  · rintro (⟨-, h⟩ | ⟨hr, hlt⟩)
    · exact Or.inl fun h' => h (hreg.mpr h')
    · refine Or.inr ⟨hreg.mp hr, ?_⟩
      rw [nativeRankAt_eq_rankAt_lift φ a y (hreg.mp hr) W hy G hG hGl]
      exact hlt

/-! ### The maximal rank on an irreducible space -/

/-- **The maximal rank** (item 5.3): on an irreducible `Y` of pure dimension `d` the native rank is bounded by
some `r` attained at a regular point; the rank-degeneracy set `S_r` is then a proper analytic subset with empty
interior. -/
theorem exists_maxRank_of_irreducible [SecondCountableTopology Y.obj.left]
    (φ : Y ⟶ ofClosedAnalytic C hC) (hY : NativePureDim Y d)
    (hirr : Y.IsIrreducibleAnalyticSubset univ) :
    ∃ r, (∀ y, nativeRankAt d φ y ≤ r) ∧ ¬ (univ ⊆ rankDegeneracy d φ r) ∧
      interior (rankDegeneracy d φ r) = ∅ := by
  classical
  -- a regular point
  obtain ⟨y₀, -⟩ := hirr.2.1
  have : Nonempty Y.obj.left := ⟨y₀⟩
  obtain ⟨x₀, j, hj⟩ := (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).nonempty
  have hx₀d : x₀ ∈ regLocus Y d := (hY x₀ j hj) ▸ hj
  -- the maximal rank
  let Q : ℕ → Prop := fun i => ∃ y : regLocus Y d, nativeRankAt d φ y = i
  set r := Nat.findGreatest Q d with hr
  have hmax : ∀ y, nativeRankAt d φ y ≤ r := fun y =>
    Nat.le_findGreatest (P := Q) (nativeRankAt_le φ y) ⟨y, rfl⟩
  obtain ⟨y₁, hy₁⟩ : Q r :=
    Nat.findGreatest_spec (P := Q) (m := nativeRankAt d φ ⟨x₀, hx₀d⟩) (nativeRankAt_le φ _)
      ⟨⟨x₀, hx₀d⟩, rfl⟩
  have hy₁S : (y₁ : Y.obj.left) ∉ rankDegeneracy d φ r := by
    rintro (h | ⟨h, hlt⟩)
    · exact h ⟨d, y₁.property⟩
    · have : (⟨(y₁ : Y.obj.left), h⟩ : regLocus Y d) = y₁ := rfl
      rw [this, hy₁] at hlt
      exact lt_irrefl _ hlt
  have hSa := isAnalyticSubset_rankDegeneracy φ hY r
  refine ⟨r, hmax, fun h => hy₁S (h (mem_univ _)), ?_⟩
  by_contra hne
  obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr hne
  have hSu := HironakaG10NativeAnalyticClosureDifference.eq_of_subset_of_inter_open_subset hSa hirr
    (subset_univ _) isOpen_interior ⟨z, mem_univ _, hz⟩
    (fun x hx => interior_subset hx.2)
  exact hy₁S (hSu ▸ mem_univ _)

end Native

end

end Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank
