import Hironaka.Analytic.Unibranch.HironakaG10GfModStart
import Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
import Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep
import Hironaka.Resolution.HironakaIntrinsicReducedCentreChartIdeal
import Hironaka.Resolution.HironakaG10FlatOrdinaryPointFlattener

/-!
# The native vanishing ideal read in a base chart (lane G10GF, run 0081, plan item G10-03-05.c2''.b)

For a local embedding `e` of a reduced complex space `X` (model `(Ω, C)`, `C ⊆ Ω ⊆ ℂᵈ`), a carrier point `c`
and ANY subset `A ⊆ X`, the preimage of the native pointwise vanishing ideal `vanishingIdealAt X A (e c)`
(`HironakaG10RelativeNonflatStrata.vanishingIdealAt`, the reduced structure of `A`) under the chart presentation
`baseChartLiftAt e c` (lane G10SB) is the ideal of ambient germs at `c` vanishing on the trace
`trace e A = {u ∈ ℂᵈ | u = c' for a carrier point c' with e c' ∈ A}`
(**`comap_vanishingIdealAt_baseChartLiftAt`**).  With `HironakaG10GfModStart` this identifies the base ideal
of the native relative non-flat set with the ideal `baseIdeal (trace e A) c` of the chart local criterion.

* `wholeChartStalkIdeal_vanishing_eq`: on an open `U ⊆ ℂᵈ`, the whole chart stalk ideal of the sheaf vanishing
  ideal of `B ⊆ U` at `y` is the germ vanishing ideal of the translated set `val '' B − y`.

No named input.  Blueprint: `hironaka-g10gf-relative.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GfNativeVanishing

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenPullback
  HironakaG10FlatOrdinaryPointFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkIdentity Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep
  Hironaka.Analytic.Unibranch.HironakaG10GfModStart

variable {d : ℕ}

theorem chartAt_opens_apply (U : Opens (ComplexModel d)) (x z : U) :
    chartAt (ComplexModel d) x z = (z : ComplexModel d) := by
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  rfl

theorem chartAt_opens_symm_val (U : Opens (ComplexModel d)) (x : U) {v : ComplexModel d}
    (hv : v ∈ U) : ((chartAt (ComplexModel d) x).symm v : ComplexModel d) = v := by
  have h := chartAt_opens_apply U x ⟨v, hv⟩
  have hsrc : (⟨v, hv⟩ : U) ∈ (chartAt (ComplexModel d) x).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
    simp
  have := (chartAt (ComplexModel d) x).left_inv hsrc
  rw [h] at this
  rw [this]

/-- **The whole chart stalk ideal of a sheaf vanishing ideal is a germ vanishing ideal.** -/
theorem wholeChartStalkIdeal_vanishing_eq (U : Opens (ComplexModel d)) (B : Set U) (y : U) :
    wholeChartStalkIdeal (vanishingIdeal (n := d) B) y y (mem_chart_source (ComplexModel d) y) =
      AnalyticGermDecomposition.vanishingIdeal
        {w : ComplexModel d | (y : ComplexModel d) + w ∈ Subtype.val '' B} := by
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro _ ⟨f, hf, ⟨-, hvan⟩, rfl⟩
    unfold chartTranslatedGerm translatedGerm
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.2
    set ψ : ComplexModel d → U := fun w => (chartAt (ComplexModel d) y).symm (w + chartAt (ComplexModel d) y y)
      with hψdef
    have hyt : chartAt (ComplexModel d) y y ∈ (chartAt (ComplexModel d) y).target :=
      (chartAt (ComplexModel d) y).map_source (mem_chart_source _ y)
    have hψ0 : ψ 0 = y := by
      simp only [hψdef, zero_add]
      exact (chartAt (ComplexModel d) y).left_inv (mem_chart_source _ y)
    have hadd : ∀ c : ComplexModel d, Tendsto (fun w : ComplexModel d => w + c) (𝓝 0) (𝓝 c) := by
      intro c
      have := (tendsto_id (x := 𝓝 (0 : ComplexModel d))).add (tendsto_const_nhds (x := c))
      rwa [zero_add] at this
    have hψt : Tendsto ψ (𝓝 0) (𝓝 y) := by
      have := ((chartAt (ComplexModel d) y).continuousAt_symm hyt).tendsto.comp
        (hadd (chartAt (ComplexModel d) y y))
      rwa [(chartAt (ComplexModel d) y).left_inv (mem_chart_source _ y)] at this
    have hU : ∀ᶠ w in 𝓝 (0 : ComplexModel d), w + (y : ComplexModel d) ∈ U :=
      (hadd (y : ComplexModel d)).eventually (U.isOpen.mem_nhds y.property)
    filter_upwards [hψt.eventually hvan, hU] with w hw hwU hwB
    obtain ⟨b, hbB, hb⟩ := hwB
    have hψw : ψ w = b := by
      apply Subtype.ext
      simp only [hψdef]
      rw [chartAt_opens_apply U y y, chartAt_opens_symm_val U y hwU, hb, add_comm]
    have := hw (hψw ▸ hbB)
    exact this
  · intro g hg
    obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk g
    apply mk_mem_wholeChartStalkIdeal_vanishing B y H hH
    have h1 := AnalyticGermDecomposition.mem_vanishingIdeal_mk.1 hg
    have ht : Tendsto (fun z : U => (z : ComplexModel d) - y) (𝓝 y) (𝓝 0) := by
      have := (continuous_subtype_val.tendsto y).sub (tendsto_const_nhds (x := (y : ComplexModel d)))
      rwa [sub_self] at this
    filter_upwards [ht.eventually h1] with z hz hzB
    rw [chartAt_opens_apply U y z, chartAt_opens_apply U y y]
    apply hz
    exact ⟨z, hzB, by simp⟩

variable {X : SourceReducedComplexSpace}

/-- The trace of `A ⊆ X` in a local embedding, as a subset of the ambient open. -/
def traceIn (e : LocalEmbedding X) (A : Set X.obj.left) : Set e.ambient :=
  {m | ∃ c : e.carrier, c.val = m ∧ e.toPoint c ∈ A}

/-- The trace of `A ⊆ X` in a local embedding, in the ambient coordinates `ℂᵈ`. -/
def trace (e : LocalEmbedding X) (A : Set X.obj.left) : Set (ComplexModel e.dim) :=
  Subtype.val '' traceIn e A

theorem traceIn_subset (e : LocalEmbedding X) (A : Set X.obj.left) : traceIn e A ⊆ e.carrier := by
  rintro m ⟨c, rfl, -⟩
  exact c.property

theorem mem_trace_of_mem (e : LocalEmbedding X) {A : Set X.obj.left} {c : e.carrier}
    (hc : e.toPoint c ∈ A) : (c.val : ComplexModel e.dim) ∈ trace e A :=
  ⟨c.val, ⟨c, rfl, hc⟩, rfl⟩

theorem toPoint_mem_of_mem_trace (e : LocalEmbedding X) {A : Set X.obj.left} {c : e.carrier}
    (hc : (c.val : ComplexModel e.dim) ∈ trace e A) : e.toPoint c ∈ A := by
  obtain ⟨m, ⟨c', rfl, hc'⟩, hm⟩ := hc
  have : c' = c := Subtype.ext (Subtype.ext hm)
  rw [← this]
  exact hc'

theorem preimage_map_base (e : LocalEmbedding X) (A : Set X.obj.left) :
    e.map.base ⁻¹' A = (Subtype.val : e.carrier → e.ambient) ⁻¹' traceIn e A := by
  ext c
  constructor
  · intro hc
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c', hc', hA⟩
    have : c' = c := Subtype.ext hc'
    rw [← this]
    exact hA

/-- **The native vanishing ideal of `A` read through the chart presentation** is the ideal of ambient germs at
`c` vanishing on the trace of `A`. -/
theorem comap_vanishingIdealAt_baseChartLift (e : LocalEmbedding X) (c : e.carrier)
    (A : Set X.obj.left) :
    (vanishingIdealAt X.obj.left A (e.toPoint c)).comap (baseChartLift e c) =
      baseIdeal (trace e A) (c.val : ComplexModel e.dim) := by
  have : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  set J := vanishingIdealAt X.obj.left A (e.toPoint c) with hJ
  set K := wholeChartStalkIdeal (vanishingIdeal (n := e.dim) (traceIn e A)) c.val c.val
    (mem_chart_source (ComplexModel e.dim) c.val) with hK
  -- the open immersion
  have hA : Ideal.map (e.map.stalkMap c).hom J =
      Ideal.map ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim) (traceIn e A)) c.val) := by
    rw [hJ]
    change Ideal.map (e.map.stalkMap c).hom (vanishingIdealAt X.obj.left A (e.map.base c)) = _
    rw [map_vanishingIdealAt_openImmersion e.map A c, preimage_map_base,
      vanishingIdealAt_eq_intrinsicCentreStalkRange]
    exact intrinsicReducedCentreStalkInclusion_range_model (traceIn_subset e A) c
  -- through the chart
  have hB : Ideal.map (baseChartStalkEquiv e c) J = Ideal.map (Ideal.Quotient.mk (chartIdeal e c)) K := by
    have h1 : Ideal.map (baseChartStalkEquiv e c) J =
        Ideal.map (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c).toRingHom
          (Ideal.map (e.map.stalkMap c).hom J) := by
      rw [Ideal.map_map]
      rfl
    rw [h1, hA, Ideal.map_map]
    have h2 : (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c).toRingHom.comp
        ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom =
        (Ideal.Quotient.mk (chartIdeal e c)).comp (actualStalkChartEquiv (n := e.dim) c.val).toRingHom :=
      RingHom.ext fun r => inclusion_stalk_chart e.carrier c r
    rw [h2, ← Ideal.map_map, map_actualWholeSheafStalkIdeal]
  -- the kernel of the presentation lies in `K`
  have hker : chartIdeal e c ≤ K := by
    rw [hK, chartIdeal, wholeChartStalkIdeal_vanishing_eq, wholeChartStalkIdeal_vanishing_eq]
    apply AnalyticGermDecomposition.vanishingIdeal_anti
    refine Eventually.of_forall fun w hw => ?_
    obtain ⟨m, hm, hmw⟩ := hw
    exact ⟨m, traceIn_subset e A hm, hmw⟩
  have hC : J.comap (baseChartLift e c) = K := by
    have h3 : J.comap (baseChartLift e c) =
        (J.comap (baseChartStalkEquiv e c).symm.toRingHom).comap (Ideal.Quotient.mk (chartIdeal e c)) := rfl
    rw [h3]
    have h4 : J.comap (baseChartStalkEquiv e c).symm.toRingHom = Ideal.map (baseChartStalkEquiv e c) J :=
      Ideal.comap_symm (baseChartStalkEquiv e c)
    rw [h4, hB, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    apply le_antisymm
    · apply sup_le le_rfl
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact hker ha
    · exact le_sup_left
  rw [hC, hK, wholeChartStalkIdeal_vanishing_eq]
  rfl

/-- The same, at any point equal to the chart point. -/
theorem comap_vanishingIdealAt_baseChartLiftAt (e : LocalEmbedding X) (c : e.carrier)
    (x : X.obj.left) (hc : e.toPoint c = x) (A : Set X.obj.left) :
    (vanishingIdealAt X.obj.left A x).comap (baseChartLiftAt e c x hc) =
      baseIdeal (trace e A) (c.val : ComplexModel e.dim) := by
  subst hc
  rw [← comap_vanishingIdealAt_baseChartLift e c A]
  rfl

end

end Hironaka.Analytic.Unibranch.HironakaG10GfNativeVanishing
