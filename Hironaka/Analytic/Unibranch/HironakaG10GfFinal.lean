import Hironaka.Analytic.Unibranch.HironakaG10GfWindow
import Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness

/-!
# hF2: generic flatness over a reduced base (lane G10GF, run 0081, plan item G10-03-05.c3)

Frisch 1967, Prop. (IV,14) (`references/frisch67-points-platitude`, p. 135; Hironaka 1975 p. 536, "`s_{i+1}(F, f/B)`
is nowhere dense in `s_i(F, f/B)`"), in lane G10RD's form:

`hF2_of_proper : A ⊆ closure (A \ relNonflat f A)` for every analytic `A` and proper `f`.

Assembly: at `x ∈ A` choose a base chart in which `A` is analytic; cover the compact fibre over `x` by
finitely many chart windows (`HironakaG10GfWindow.exists_window_dictionary`), which cover the fibres over a
neighbourhood `V₀` of `x` (properness); in the trace `T` of `A` find, window after window, a point flat over
`T` along each window (`HironakaG10GfRegularChart.exists_forall_relFibreFlatAt_of_analytic` and the openness
`HironakaG10LocEuclideanCartan.eventually_relFibreFlatAt_compact`); there the native base ideal is
`baseIdeal T` (`HironakaG10GfNativeVanishing`), the relative start is a start modulo it
(`HironakaG10GfModStart`), and the chart local criterion (lane G10LF's
`HironakaG10TmLocalFlatness.chartFlat_iff_fibreExactAt`, Matsumura Th. 22.3) gives chart flatness, hence native
flatness by the window dictionary (`HironakaG10GfWindow`).

Also, for lane G10FR's reading of the non-flat locus: **`chartFlat_baseIdeal_iff_fibreExactAt`** — for a
relatively exact start over `T` at `p`, chart flatness over `I_T` is exactness of the fibre start.

No named input.  Blueprint: `hironaka-g10gf-final.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GfFinal

noncomputable section

open Hironaka Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10LocFibreOpen HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
  Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
  Hironaka.Analytic.Unibranch.HironakaG10GfRegularChart Hironaka.Analytic.Unibranch.HironakaG10GfModStart
  Hironaka.Analytic.Unibranch.HironakaG10GfNativeVanishing Hironaka.Analytic.Unibranch.HironakaG10GfWindow

/-- **Chart flatness over the vanishing ideal of `T` is fibre exactness of a relatively exact start**
(`HironakaG10GfModStart.exactStartMod_of_relExactStartOn` + lane G10LF's chart local criterion). -/
theorem chartFlat_baseIdeal_iff_fibreExactAt {d t a b c : ℕ} {T : Set (ComplexModel d)}
    {W : Set (ComplexModel d × ComplexModel t)} {G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ}
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ} (h : RelExactStartOn T W G F)
    (hW : IsOpen W) {p : ComplexModel d × ComplexModel t} (hpW : p ∈ W) (hpT : p.1 ∈ T) :
    ChartFlat d t F p (baseIdeal T p.1) ↔ FibreExactAt G F p.1 p.2 :=
  HironakaG10TmLocalFlatness.chartFlat_iff_fibreExactAt d t _ (baseIdeal_le_maximalIdeal hpT) F G p
    (fun i j => holAt_of_differentiableOn hW (h.holA i j) hpW)
    (fun j k => holAt_of_differentiableOn hW (h.holG j k) hpW)
    (exactStartMod_of_relExactStartOn h hW hpW hpT)

/-- **Relative flatness over the trace gives chart flatness over the base ideal.** -/
theorem chartFlat_of_relFibreFlatAt {d t a b : ℕ} {T : Set (ComplexModel d)}
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ} {p : ComplexModel d × ComplexModel t}
    (hpT : p.1 ∈ T) (h : RelFibreFlatAt T F p) : ChartFlat d t F p (baseIdeal T p.1) := by
  obtain ⟨c, G, W, hW, hpW, hstart, hfib⟩ := h
  exact (chartFlat_baseIdeal_iff_fibreExactAt hstart hW hpW hpT).2 hfib

/-- Conversely, chart flatness over the base ideal gives relative flatness wherever a relatively exact start
exists. -/
theorem relFibreFlatAt_of_chartFlat {d t a b c : ℕ} {T : Set (ComplexModel d)}
    {W : Set (ComplexModel d × ComplexModel t)} {G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ}
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ} (h : RelExactStartOn T W G F)
    (hW : IsOpen W) {p : ComplexModel d × ComplexModel t} (hpW : p ∈ W) (hpT : p.1 ∈ T)
    (hflat : ChartFlat d t F p (baseIdeal T p.1)) : RelFibreFlatAt T F p :=
  ⟨c, G, W, hW, hpW, h, (chartFlat_baseIdeal_iff_fibreExactAt h hW hpW hpT).1 hflat⟩

/-- **hF2 (Frisch 1967 Prop. (IV,14)) for a proper morphism.** -/
theorem hF2_of_proper {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (A : Set X.obj.left) (hA : X.IsAnalyticSubset A) :
    A ⊆ closure (A \ relNonflat f A) := by
  classical
  intro x hxA
  rw [mem_closure_iff]
  intro N hN hxN
  obtain ⟨e, ⟨c₀, hc₀⟩, A', hA', htr⟩ := hA x
  -- windows over the fibre of `x`
  choose W hW hyW m b F Ω K hΩ hK hKΩ hF hdict using
    fun y : {y : Y.obj.left // f.hom.left.base y = x} =>
      exists_window_dictionary f e y.val c₀ (y.property.trans hc₀.symm)
  have hcomp : IsCompact (f.hom.left.base ⁻¹' {x}) := hf.isCompact_preimage isCompact_singleton
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun y => W y) (fun y => hW y) (by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hyW ⟨y, hy⟩⟩)
  let Ωw : Set Y.obj.left := ⋃ i ∈ t, W i
  have hΩw : IsOpen Ωw := isOpen_biUnion fun i _ => hW i
  let V₀ : Set X.obj.left := (f.hom.left.base '' Ωwᶜ)ᶜ
  have hV₀ : IsOpen V₀ := (hf.isClosedMap _ hΩw.isClosed_compl).isOpen_compl
  have hxV₀ : x ∈ V₀ := by
    rintro ⟨y, hy, hyx⟩
    exact hy (ht hyx)
  have hcov : ∀ x' ∈ V₀, ∀ y', f.hom.left.base y' = x' → ∃ i ∈ t, y' ∈ W i := by
    intro x' hx' y' hy'
    by_contra hn
    apply hx'
    refine ⟨y', ?_, hy'⟩
    intro hyΩ
    obtain ⟨i, hi⟩ := mem_iUnion.1 hyΩ
    obtain ⟨hit, hyi⟩ := mem_iUnion.1 hi
    exact hn ⟨i, hit, hyi⟩
  -- the trace of `A` and its analyticity
  have htraceIn : traceIn e A = A' ∩ e.carrier := by
    ext m
    constructor
    · rintro ⟨c, rfl, hcA⟩
      exact ⟨(show c ∈ Subtype.val ⁻¹' A' by rw [← htr]; exact hcA), c.property⟩
    · rintro ⟨hmA, hmC⟩
      exact ⟨⟨m, hmC⟩, rfl, (show (⟨m, hmC⟩ : e.carrier) ∈ e.toPoint ⁻¹' A by rw [htr]; exact hmA)⟩
  have hTan : IsComplexAnalyticSubset (n := e.dim) (traceIn e A) := by
    rw [htraceIn]
    exact hA'.inter e.analytic
  -- an open set of the ambient for `N ∩ V₀`
  have hpre : IsOpen (e.toPoint ⁻¹' (N ∩ V₀)) :=
    (hN.inter hV₀).preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 hpre
  let V : Set (ComplexModel e.dim) := Subtype.val '' O
  have hV : IsOpen V := e.ambient.isOpen.isOpenMap_subtype_val O hO
  have hc₀O : c₀.val ∈ O := by
    have : c₀ ∈ e.toPoint ⁻¹' (N ∩ V₀) := by
      show e.toPoint c₀ ∈ N ∩ V₀
      rw [hc₀]
      exact ⟨hxN, hxV₀⟩
    rw [← hOeq] at this
    exact this
  have hc₀T : (c₀.val : ComplexModel e.dim) ∈ trace e A :=
    mem_trace_of_mem e (by rw [hc₀]; exact hxA)
  -- window after window
  have key : ∀ s : Finset {y : Y.obj.left // f.hom.left.base y = x},
      ∀ V' : Set (ComplexModel e.dim), IsOpen V' → (V' ∩ trace e A).Nonempty →
        ∃ q ∈ V' ∩ trace e A, ∀ i ∈ s, ∀ z ∈ K i, RelFibreFlatAt (trace e A) (F i) (q, z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro V' _ hne
        obtain ⟨q, hq⟩ := hne
        exact ⟨q, hq, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert i s hi ih =>
        intro V' hV' hne
        obtain ⟨q₁, hq₁, hgood₁⟩ := exists_forall_relFibreFlatAt_of_analytic e.ambient hTan (F i)
          (isOpen_univ.prod (hΩ i)) (hF i) hV' hne (hK i)
          (fun q _ z hz => ⟨mem_univ q, hKΩ i hz⟩)
        have hev := HironakaG10LocEuclideanCartan.eventually_relFibreFlatAt_compact (trace e A) (F i)
          (hK i) hq₁.2 hgood₁
        obtain ⟨V₁, hV₁sub, hV₁, hq₁V₁⟩ := mem_nhds_iff.1 hev
        obtain ⟨q, hq, hgood⟩ := ih (V₁ ∩ V') (hV₁.inter hV') ⟨q₁, ⟨hq₁V₁, hq₁.1⟩, hq₁.2⟩
        refine ⟨q, ⟨hq.1.2, hq.2⟩, fun j hj z hz => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hjs
        · exact hV₁sub hq.1.1 hq.2 z hz
        · exact hgood j hjs z hz
  obtain ⟨q, ⟨hqV, hqT⟩, hgood⟩ := key t V hV ⟨c₀.val.val, ⟨c₀.val, hc₀O, rfl⟩, hc₀T⟩
  -- the corresponding point of `X`
  obtain ⟨mq, ⟨cq, hcqm, hcqA⟩, rfl⟩ := hqT
  subst hcqm
  have hcqO : cq.val ∈ O := by
    obtain ⟨o, ho, hoq⟩ := hqV
    have : o = cq.val := Subtype.ext hoq
    rw [← this]
    exact ho
  have hcqN : e.toPoint cq ∈ N ∩ V₀ := by
    have : cq ∈ (Subtype.val : e.carrier → e.ambient) ⁻¹' O := hcqO
    rw [hOeq] at this
    exact this
  refine ⟨e.toPoint cq, hcqN.1, hcqA, fun hnf => hnf.2 ?_⟩
  intro y' h
  obtain ⟨i, hi, hy'i⟩ := hcov _ hcqN.2 y' h
  obtain ⟨z, hzK, hz⟩ := hdict i y' hy'i cq h
  apply hz
  rw [comap_vanishingIdealAt_baseChartLiftAt]
  exact chartFlat_of_relFibreFlatAt (mem_trace_of_mem e hcqA) (hgood i hi z hzK)

/-- **hF2 in the shape consumed by `HironakaG10TmFinal.hironakaFlattening_of_frisch_of_theoremI`** (second
conjunct of `hFrisch`). -/
theorem hF2_stage :
    ∀ s : HironakaG10ChowFlatteningDriver.Stage, CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base →
        ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A) :=
  fun s _ hf A hA => hF2_of_proper s.f hf A hA

end

end Hironaka.Analytic.Unibranch.HironakaG10GfFinal
