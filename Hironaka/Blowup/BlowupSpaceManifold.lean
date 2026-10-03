/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSpaceAtlas
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupSpace
import Hironaka.Blowup.BlowupSpaceRatio
import Hironaka.Blowup.BlowupSpaceTangent
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The blowup along a smooth centre is a complex manifold

Source: Demailly, *Complex analytic and differential geometry*, VII.12.2--12.3 (`agbook.tex` lines 20306--20333).

Fifth module of the construction of the blowup. For a closed submanifold `C` of `X` (`[Fact (IsClosedSubmanifold n
C)]`), the atlas `blowupAtlas n C` (Demailly's monomial charts and the charts of `X \ C`) defines, through
`ChartedSpaceCore`, a topology and a charted space structure on `BlowupSpace n C`:

* every point lies in a chart: off `C` in a chart of `X`, over `y ∈ C` in a monomial chart `τ̃ⱼ`
  over the chosen flattening at `y`, for a normal index `j` with `d_yτⱼ(ξ_p) ≠ 0`
  (`exists_mem_flatSource`);
* `IsManifold`: the coordinate changes are holomorphic (`BlowupSpaceAtlas`);
* `T2Space`: two points over the same `y ∈ C` lie in monomial charts `τ̃ⱼ, τ̃ₗ` over the same
  flattening, and are separated either in one chart or by `|wₗ| < 1`, `|w'ⱼ| < 1`, because
  `wₗ · w'ⱼ = 1` on the overlap; points over different points of `X` are separated by `π`;
* `SecondCountableTopology`: countably many chart domains cover (`X` is second countable);
* hence `IsComplexManifold n (BlowupSpace n C)`, and `blowupProj` is holomorphic.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupConstruction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupSpaceTangent BlowupSpace

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C : Set X}

/-! ### The chosen flattening at a point of the centre -/

section Choice

variable [hC : Fact (IsClosedSubmanifold n C)]
include hC

theorem isClosed_centre : IsClosed C := hC.out.1

theorem exists_flattening {y : X} (hy : y ∈ C) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y)),
      Φ.source ⊆ (chartAt (ComplexModel n) y).target ∧
      ∀ {x : X}, x ∈ (chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y x ∈ Φ.source →
          (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y x) ∈ complexCoordinatePlane n k) := by
  obtain ⟨k, -, -, Φ, hsrc, -, hflat⟩ := hC.out.2 y hy
  exact ⟨k, Φ, hsrc, hflat⟩

variable (n) in
/-- The dimension of the chosen flattening at `y ∈ C`. -/
def flatK {y : X} (hy : y ∈ C) : ℕ := Classical.choose (exists_flattening (n := n) hy)

variable (n) in
/-- The chosen flattening at `y ∈ C`. -/
def flatΦ {y : X} (hy : y ∈ C) : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y) :=
  Classical.choose (Classical.choose_spec (exists_flattening (n := n) hy))

theorem flatΦ_spec {y : X} (hy : y ∈ C) :
    (flatΦ n hy).source ⊆ (chartAt (ComplexModel n) y).target ∧
      ∀ {x : X}, x ∈ (chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y x ∈ (flatΦ n hy).source →
          (x ∈ C ↔ (flatΦ n hy).toFun (chartAt (ComplexModel n) y x) ∈
            complexCoordinatePlane n (flatK n hy)) :=
  Classical.choose_spec (Classical.choose_spec (exists_flattening hy))

/-- The monomial chart with normal index `j` over the chosen flattening at `y ∈ C`. -/
def mkFlat {y : X} (hy : y ∈ C) (j : Fin n) (hj : flatK n hy ≤ j.1) : FlatChart n C :=
  ⟨y, flatK n hy, flatΦ n hy, (flatΦ_spec hy).1, (flatΦ_spec hy).2, j, hj⟩

@[simp] theorem mkFlat_y₀ {y : X} (hy : y ∈ C) (j : Fin n) (hj : flatK n hy ≤ j.1) :
    (mkFlat hy j hj).y₀ = y := rfl

@[simp] theorem mkFlat_Φ {y : X} (hy : y ∈ C) (j : Fin n) (hj : flatK n hy ≤ j.1) :
    (mkFlat hy j hj).Φ = flatΦ n hy := rfl

@[simp] theorem mkFlat_j {y : X} (hy : y ∈ C) (j : Fin n) (hj : flatK n hy ≤ j.1) :
    (mkFlat hy j hj).j = j := rfl

/-- **Every point over the flat domain of the chosen flattening lies in one of its monomial
charts.** -/
theorem exists_mem_flatSource {y : X} (hy : y ∈ C) {p : BlowupSpace n C}
    (hp : p.base ∈ flatDomain (flatΦ n hy)) (hpC : p.base ∈ C) :
    ∃ (j : Fin n) (hj : flatK n hy ≤ j.1), p ∈ (mkFlat hy j hj).source := by
  have hnot := dirVec_not_mem hpC
  rw [mem_tangentSpace_iff (flatΦ_spec hy).1 (flatΦ_spec hy).2 hp hpC] at hnot
  push Not at hnot
  obtain ⟨j, hj, hne⟩ := hnot
  refine ⟨j, hj, hp, ?_⟩
  show extVal (flatCoord (flatΦ n hy) j) p ≠ 0
  rw [extVal_of_mem hpC]
  exact hne

/-- Every point lies in the domain of a chart of the atlas. -/
theorem exists_chart (p : BlowupSpace n C) : ∃ a ∈ blowupAtlas n C, p ∈ a.source := by
  by_cases h : p.base ∈ C
  · obtain ⟨j, hj, hp⟩ := exists_mem_flatSource h (mem_flatDomain_self (flatΦ n h)) h
    exact ⟨_, Or.inl ⟨mkFlat h j hj, rfl⟩, hp⟩
  · exact ⟨_, Or.inr ⟨⟨p.base, h⟩, rfl⟩, mem_chart_source _ p.base, h⟩

/-- The preferred chart at a point. -/
def prefChart (p : BlowupSpace n C) : PartialEquiv (BlowupSpace n C) (ComplexModel n) :=
  Classical.choose (exists_chart p)

theorem prefChart_mem (p : BlowupSpace n C) : prefChart p ∈ blowupAtlas n C :=
  (Classical.choose_spec (exists_chart p)).1

theorem mem_prefChart_source (p : BlowupSpace n C) : p ∈ (prefChart p).source :=
  (Classical.choose_spec (exists_chart p)).2

variable (n C) in
/-- **The blowup as a charted space without topology**: Demailly's atlas. -/
def blowupCore : ChartedSpaceCore (ComplexModel n) (BlowupSpace n C) where
  atlas := blowupAtlas n C
  chartAt := prefChart
  mem_chart_source := mem_prefChart_source
  chart_mem_atlas := prefChart_mem
  open_source _ _ he he' := (isOpen_transSource_and_differentiableOn (isClosed_centre (n := n)) he he').1
  continuousOn_toFun _ _ he he' :=
    (isOpen_transSource_and_differentiableOn (isClosed_centre (n := n)) he he').2.continuousOn

end Choice

section Manifold

variable [hC : Fact (IsClosedSubmanifold n C)]

instance topologicalSpace : TopologicalSpace (BlowupSpace n C) := (blowupCore n C).toTopologicalSpace

instance chartedSpace : ChartedSpace (ComplexModel n) (BlowupSpace n C) := (blowupCore n C).toChartedSpace

/-- A chart of the atlas as an open partial homeomorphism. -/
def atlasHomeo (a : PartialEquiv (BlowupSpace n C) (ComplexModel n)) (ha : a ∈ blowupAtlas n C) :
    OpenPartialHomeomorph (BlowupSpace n C) (ComplexModel n) :=
  (blowupCore n C).openPartialHomeomorph a ha

@[simp] theorem atlasHomeo_toPartialEquiv (a : PartialEquiv (BlowupSpace n C) (ComplexModel n))
    (ha : a ∈ blowupAtlas n C) : (atlasHomeo a ha).toPartialEquiv = a := rfl

theorem isOpen_source_of_mem {a : PartialEquiv (BlowupSpace n C) (ComplexModel n)}
    (ha : a ∈ blowupAtlas n C) : IsOpen a.source :=
  (atlasHomeo a ha).open_source

theorem atlasHomeo_mem_atlas (a : PartialEquiv (BlowupSpace n C) (ComplexModel n))
    (ha : a ∈ blowupAtlas n C) : atlasHomeo a ha ∈ atlas (ComplexModel n) (BlowupSpace n C) := by
  show atlasHomeo a ha ∈ ⋃ (e₀ : PartialEquiv (BlowupSpace n C) (ComplexModel n))
    (he₀ : e₀ ∈ (blowupCore n C).atlas), {(blowupCore n C).openPartialHomeomorph e₀ he₀}
  rw [mem_iUnion]
  exact ⟨a, by rw [mem_iUnion]; exact ⟨ha, rfl⟩⟩

theorem exists_eq_atlasHomeo {e : OpenPartialHomeomorph (BlowupSpace n C) (ComplexModel n)}
    (he : e ∈ atlas (ComplexModel n) (BlowupSpace n C)) :
    ∃ a, ∃ ha : a ∈ blowupAtlas n C, e = atlasHomeo a ha := by
  have he' : e ∈ ⋃ (e₀ : PartialEquiv (BlowupSpace n C) (ComplexModel n))
      (he₀ : e₀ ∈ (blowupCore n C).atlas), {(blowupCore n C).openPartialHomeomorph e₀ he₀} := he
  rw [mem_iUnion] at he'
  obtain ⟨a, he'⟩ := he'
  rw [mem_iUnion] at he'
  obtain ⟨ha, he'⟩ := he'
  exact ⟨a, ha, he'⟩

instance isManifold : IsManifold 𝓘(ℂ, ComplexModel n) ∞ (BlowupSpace n C) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨a, ha, rfl⟩ := exists_eq_atlasHomeo he
  obtain ⟨b, hb, rfl⟩ := exists_eq_atlasHomeo he'
  have h := isOpen_transSource_and_differentiableOn (isClosed_centre (n := n)) ha hb
  simp only [mfld_simps]
  exact (contDiffOn_of_differentiableOn_complex h.2 h.1).congr fun z _ => rfl

theorem FlatChart.isOpen_source (c : FlatChart n C) : IsOpen c.source :=
  isOpen_source_of_mem (Or.inl ⟨c, rfl⟩)

/-- A monomial chart as an open partial homeomorphism. -/
def FlatChart.homeo (c : FlatChart n C) : OpenPartialHomeomorph (BlowupSpace n C) (ComplexModel n) :=
  atlasHomeo c.toPartialEquiv (Or.inl ⟨c, rfl⟩)

@[simp] theorem FlatChart.homeo_source (c : FlatChart n C) : c.homeo.source = c.source := rfl
@[simp] theorem FlatChart.homeo_apply (c : FlatChart n C) (p : BlowupSpace n C) :
    c.homeo p = c.toFun p := rfl

/-! ### The projection is continuous -/

theorem continuousAt_proj_symm {a : PartialEquiv (BlowupSpace n C) (ComplexModel n)}
    (ha : a ∈ blowupAtlas n C) {z : ComplexModel n} (hz : z ∈ a.target) :
    ContinuousAt (blowupProj n C ∘ a.symm) z := by
  rcases ha with ⟨c, rfl⟩ | ⟨o, rfl⟩
  · have hev : blowupProj n C ∘ c.toPartialEquiv.symm =ᶠ[𝓝 z] c.pt := by
      filter_upwards [c.isOpen_target.mem_nhds hz] with w hw
      exact c.blowupProj_invFun hw
    exact (show ContinuousAt c.pt z from c.continuousAt_pt hz).congr hev.symm
  · have hT : IsOpen o.toPartialEquiv.target :=
      o.e.isOpen_inter_preimage_symm (isClosed_centre (n := n)).isOpen_compl
    have hev : blowupProj n C ∘ o.toPartialEquiv.symm =ᶠ[𝓝 z] o.e.symm := by
      filter_upwards [hT.mem_nhds hz] with w hw
      have h : o.e.symm w ∉ C := hw.2
      simp only [Function.comp_apply, o.toPartialEquiv_symm_apply_of_not_mem h]
      rfl
    exact (o.e.continuousAt_symm hz.1).congr hev.symm

theorem continuous_blowupProj : Continuous (blowupProj n C) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  set a := prefChart p
  have ha := prefChart_mem p
  have hp := mem_prefChart_source p
  have h1 : ContinuousAt (atlasHomeo a ha) p := (atlasHomeo a ha).continuousAt hp
  have h2 := continuousAt_proj_symm ha (a.map_source hp)
  have h3 : ContinuousAt ((blowupProj n C ∘ a.symm) ∘ (atlasHomeo a ha)) p := h2.comp h1
  refine h3.congr ?_
  filter_upwards [(isOpen_source_of_mem ha).mem_nhds hp] with q hq
  simp only [Function.comp_apply]
  show blowupProj n C (a.symm (a q)) = blowupProj n C q
  rw [a.left_inv hq]

/-! ### Hausdorff -/

/-- Two distinct points in the domain of one chart are separated by that chart. -/
theorem exists_separating_of_common (e : OpenPartialHomeomorph (BlowupSpace n C) (ComplexModel n))
    {p q : BlowupSpace n C} (hpq : p ≠ q) (hp : p ∈ e.source) (hq : q ∈ e.source) :
    ∃ u v : Set (BlowupSpace n C), IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  have hne : e p ≠ e q := fun h => hpq (by rw [← e.left_inv hp, h, e.left_inv hq])
  obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ := t2_separation hne
  refine ⟨e.source ∩ e ⁻¹' A, e.source ∩ e ⁻¹' B, e.isOpen_inter_preimage hA,
    e.isOpen_inter_preimage hB, ⟨hp, hpA⟩, ⟨hq, hqB⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro r ⟨-, hrA⟩ ⟨-, hrB⟩
  exact (Set.disjoint_left.mp hAB) hrA hrB

theorem exists_separating_of_base_eq {p q : BlowupSpace n C} (hpq : p ≠ q) (hb : p.base = q.base) :
    ∃ u v : Set (BlowupSpace n C), IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  have hpC : p.base ∈ C := by
    by_contra h; exact hpq (eq_of_base_eq_of_not_mem hb h)
  have hqC : q.base ∈ C := by rw [← hb]; exact hpC
  have hdomp : p.base ∈ flatDomain (flatΦ n hpC) := mem_flatDomain_self _
  have hdomq : q.base ∈ flatDomain (flatΦ n hpC) := by rw [← hb]; exact hdomp
  obtain ⟨jp, hjp, hp⟩ := exists_mem_flatSource hpC hdomp hpC
  obtain ⟨jq, hjq, hq⟩ := exists_mem_flatSource hpC hdomq hqC
  set cp := mkFlat hpC jp hjp with hcp
  set cq := mkFlat hpC jq hjq with hcq
  by_cases hqp : q ∈ cp.source
  · exact exists_separating_of_common cp.homeo hpq hp hqp
  by_cases hpq' : p ∈ cq.source
  · exact exists_separating_of_common cq.homeo hpq hpq' hq
  -- `q ∉ τ̃_{jp}` and `p ∉ τ̃_{jq}`: separate by `|w_{jq}| < 1` and `|w'_{jp}| < 1`
  have hεq : extVal (cp.τ jq) p = 0 := by
    by_contra h; exact hpq' ⟨hdomp, h⟩
  have hεp : extVal (cp.τ jp) q = 0 := by
    by_contra h; exact hqp ⟨hdomq, h⟩
  have hjne : jq ≠ jp := by
    rintro rfl; exact hqp hq
  have hball : ∀ i : Fin n, IsOpen {w : ComplexModel n | ‖w i‖ < 1} := fun i =>
    isOpen_lt (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.norm continuous_const
  refine ⟨cp.homeo.source ∩ cp.homeo ⁻¹' {w | ‖w jq‖ < 1},
    cq.homeo.source ∩ cq.homeo ⁻¹' {w | ‖w jp‖ < 1},
    cp.homeo.isOpen_inter_preimage (hball jq), cq.homeo.isOpen_inter_preimage (hball jp),
    ⟨hp, ?_⟩, ⟨hq, ?_⟩, ?_⟩
  · show ‖cp.toFun p jq‖ < 1
    rw [cp.toFun_apply_normal p hjq hjne]
    simp [hεq]
  · show ‖cq.toFun q jp‖ < 1
    rw [cq.toFun_apply_normal q hjp hjne.symm]
    show ‖extVal (cp.τ jp) q / extVal (cq.τ jq) q‖ < 1
    simp [hεp]
  · rw [Set.disjoint_left]
    rintro r ⟨hrp, hr1⟩ ⟨hrq, hr2⟩
    have hεrp : extVal (cp.τ jp) r ≠ 0 := hrp.2
    have hεrq : extVal (cq.τ jq) r ≠ 0 := hrq.2
    change ‖cp.toFun r jq‖ < 1 at hr1
    change ‖cq.toFun r jp‖ < 1 at hr2
    rw [cp.toFun_apply_normal r hjq hjne] at hr1
    rw [cq.toFun_apply_normal r hjp hjne.symm] at hr2
    change ‖extVal (cq.τ jp) r / extVal (cq.τ jq) r‖ < 1 at hr2
    have hprod : ‖extVal (cp.τ jq) r / extVal (cp.τ jp) r‖ *
        ‖extVal (cq.τ jp) r / extVal (cq.τ jq) r‖ = 1 := by
      rw [← norm_mul]
      have : extVal (cp.τ jq) r / extVal (cp.τ jp) r * (extVal (cq.τ jp) r / extVal (cq.τ jq) r)
          = 1 := by
        change extVal (cq.τ jq) r / extVal (cp.τ jp) r * (extVal (cp.τ jp) r / extVal (cq.τ jq) r) = 1
        field_simp
      rw [this, norm_one]
    have hlt : ‖extVal (cp.τ jq) r / extVal (cp.τ jp) r‖ *
        ‖extVal (cq.τ jp) r / extVal (cq.τ jq) r‖ < 1 :=
      calc _ ≤ 1 * ‖extVal (cq.τ jp) r / extVal (cq.τ jq) r‖ :=
            mul_le_mul_of_nonneg_right hr1.le (norm_nonneg _)
        _ < 1 := by simpa using hr2
    exact absurd hprod (ne_of_lt hlt)

instance t2Space : T2Space (BlowupSpace n C) := by
  refine ⟨fun {p q} hpq => ?_⟩
  by_cases hb : p.base = q.base
  · exact exists_separating_of_base_eq hpq hb
  · obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation hb
    exact ⟨blowupProj n C ⁻¹' U, blowupProj n C ⁻¹' V, hU.preimage continuous_blowupProj,
      hV.preimage continuous_blowupProj, hpU, hqV, hUV.preimage _⟩

/-! ### Second countability -/

instance secondCountableTopology : SecondCountableTopology (BlowupSpace n C) := by
  classical
  -- countably many charts of `X` cover `X \ C`, countably many flat domains cover `C`
  obtain ⟨t, htC, htc, htU⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := Cᶜ)
    (f := fun x => (chartAt (ComplexModel n) x).source)
    fun x _ => mem_nhdsWithin_of_mem_nhds
      ((chartAt (ComplexModel n) x).open_source.mem_nhds (mem_chart_source _ x))
  obtain ⟨t', ht'C, ht'c, ht'U⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := C)
    (f := fun y => if hy : y ∈ C then flatDomain (flatΦ n hy) else univ)
    fun y hy => by
      simp only [dif_pos hy]
      exact mem_nhdsWithin_of_mem_nhds ((isOpen_flatDomain _).mem_nhds (mem_flatDomain_self _))
  have : Countable t := htc.to_subtype
  have : Countable t' := ht'c.to_subtype
  let ι := t ⊕ {yj : t' × Fin n // ∃ h : (yj.1 : X) ∈ C, flatK n h ≤ yj.2.1}
  let a : ι → PartialEquiv (BlowupSpace n C) (ComplexModel n) := fun i => match i with
    | Sum.inl x => (⟨x.1, htC x.2⟩ : OffChart n C).toPartialEquiv
    | Sum.inr yj => (mkFlat yj.2.1 yj.1.2 yj.2.2).toPartialEquiv
  have ha : ∀ i, a i ∈ blowupAtlas n C := fun i => match i with
    | Sum.inl _ => Or.inr ⟨_, rfl⟩
    | Sum.inr _ => Or.inl ⟨_, rfl⟩
  have : ∀ i, SecondCountableTopology ((a i).source) := fun i =>
    (atlasHomeo (a i) (ha i)).secondCountableTopology_source
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i => (a i).source) (fun i => isOpen_source_of_mem (ha i)) ?_
  refine eq_univ_of_forall fun p => mem_iUnion.mpr ?_
  by_cases hpC : p.base ∈ C
  · have := ht'U hpC
    rw [mem_iUnion₂] at this
    obtain ⟨y, hyt, hpy⟩ := this
    have hy : y ∈ C := ht'C hyt
    rw [dif_pos hy] at hpy
    obtain ⟨j, hj, hpj⟩ := exists_mem_flatSource hy hpy hpC
    exact ⟨Sum.inr ⟨(⟨y, hyt⟩, j), hy, hj⟩, hpj⟩
  · have := htU hpC
    rw [mem_iUnion₂] at this
    obtain ⟨x, hxt, hpx⟩ := this
    exact ⟨Sum.inl ⟨x, hxt⟩, hpx, hpC⟩

/-- **The blowup along a closed submanifold is a complex manifold.** -/
instance isComplexManifold : IsComplexManifold n (BlowupSpace n C) where

/-! ### The projection is holomorphic -/

theorem contMDiffAt_proj_symm {a : PartialEquiv (BlowupSpace n C) (ComplexModel n)}
    (ha : a ∈ blowupAtlas n C) {z : ComplexModel n} (hz : z ∈ a.target) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (blowupProj n C ∘ a.symm) z := by
  rcases ha with ⟨c, rfl⟩ | ⟨o, rfl⟩
  · have hev : blowupProj n C ∘ c.toPartialEquiv.symm =ᶠ[𝓝 z] c.pt := by
      filter_upwards [c.isOpen_target.mem_nhds hz] with w hw
      exact c.blowupProj_invFun hw
    have hw : monomial c.k c.j z ∈ c.Φ.target := hz
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c.Φ.invFun
        (monomial c.k c.j z) :=
      (contDiffAt_of_differentiableOn_complex c.Φ.invFun_holomorphic c.Φ.isOpen_target hw).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun (monomial c.k c.j z)) :=
      (contMDiffOn_chart_symm (n := ∞)).contMDiffAt
        ((chartAt (ComplexModel n) c.y₀).open_target.mem_nhds (c.hsrc (c.Φ.mapsTo_invFun hw)))
    have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ c.pt z :=
      h2.comp z (h1.comp z (contDiff_monomial c.k c.j).contMDiff.contMDiffAt)
    exact h3.congr_of_eventuallyEq hev
  · have hT : IsOpen o.toPartialEquiv.target :=
      o.e.isOpen_inter_preimage_symm (isClosed_centre (n := n)).isOpen_compl
    have hev : blowupProj n C ∘ o.toPartialEquiv.symm =ᶠ[𝓝 z] o.e.symm := by
      filter_upwards [hT.mem_nhds hz] with w hw
      have h : o.e.symm w ∉ C := hw.2
      simp only [Function.comp_apply, o.toPartialEquiv_symm_apply_of_not_mem h]
      rfl
    exact ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
      (o.e.open_target.mem_nhds hz.1)).congr_of_eventuallyEq hev

/-- **The projection of the blowup is holomorphic.** -/
theorem contMDiff_blowupProj :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (blowupProj n C) := by
  intro p
  set a := prefChart p
  have ha := prefChart_mem p
  have hp := mem_prefChart_source p
  have hmax := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (atlasHomeo_mem_atlas a ha)
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (atlasHomeo a ha) p :=
    (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt ((isOpen_source_of_mem ha).mem_nhds hp)
  have h2 := contMDiffAt_proj_symm ha (a.map_source hp)
  have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((blowupProj n C ∘ a.symm) ∘ (atlasHomeo a ha)) p := h2.comp p h1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_source_of_mem ha).mem_nhds hp] with q hq
  simp only [Function.comp_apply]
  show blowupProj n C q = blowupProj n C (a.symm (a q))
  rw [a.left_inv hq]

end Manifold

end

end Hironaka.BlowupConstruction
