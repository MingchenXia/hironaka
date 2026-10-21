/- Complete original CoefficientRestrictionTower complement; provisional dependency closure. -/
import Hironaka.Support.CoefficientRestrictionSupportOriginalExact
import Hironaka.Support.NormalDerivativeChartIdealOriginalExact
import Hironaka.MarkedIdeal.CoefficientRestrictionTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal along multiple test blow-ups: the support

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:normal-coefficient-invariant`, `mc:coefficient-restriction-full`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, proof of Lemma `le:S`; GGT 2008
(`wlodarczyk09-analytic-resolution`), proof of Proposition 5.6.4 (2)-(3): the coefficients `c_{α f k}` of the
transforms `f_k` in the normal coordinates of the strict transforms `S_k` satisfy
`c_{α f k}|_{S_k} ∈ (σ^k|_{S_k})^c(𝓓^{|α|}(𝓘)|_S)`.

**The invariant** (`GoodAt`): at a point `p` of `S_T` there are a flat chart for `S_T` and generators of the transformed
ideal `𝔪_T` at `p` whose normal derivatives `∂^L` (`|L| < μ`) restrict on `S_T` into the transformed derivative ideals
`[𝓓^{|L|} 𝔪]_T`.

* `GoodAt.mem_cosupp` (the conclusion): at a good point of `S_T` where every `[𝓓^i 𝔪]_T` has order `≥ μ - i` along
  `S_T`, the point lies in `cosupp 𝔪_T` (`NormalTaylorOrder`).
* `goodAt_refl`: every point of `S` is good (normal derivatives of germs of `𝔞` lie in `𝓓^{|L|} 𝔞`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientRestrictionTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal
  HomogenizedGlueingTower CoefficientIdealRestriction HolomorphicTaylorTail NormalTaylorOrder NormalDerivativeChart
  NormalDerivativeMonomial BlowupControlledTransform

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}


/-- **The coefficient invariant at a point** of the strict transform `S_T` of `S` along `T`: a flat chart `c` for `S_T`
at `p` (dimension `k ≤ n`) and generators `G` of `(𝔪_T)_p` such that for every generator `g` and every list `L` of normal
directions with `|L| < μ`, the normal derivative `∂^L g` restricts on `S_T` near `p` into `[𝓓^{|L|} 𝔪]_T`. -/
def GoodAt (𝔪 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (p : Y) : Prop :=
  ∃ (k : ℕ) (_ : k ≤ n) (c : FlatChart n (strictAlong T S) p k) (G : (Y → ℂ) → Prop),
    (∀ g, G g → (geoTransformAlong 𝔪 T).ideal.mem p g) ∧
    (∀ f, (geoTransformAlong 𝔪 T).ideal.mem p f → IsInSpanAt (n := n) G p f) ∧
    ∀ g, G g → ∀ L : List (Fin n), NormalIdx k L → L.length < 𝔪.d →
      IsInSpanOnAt (n := n) (strictAlong T S) ((geoTransformAlong (derivMarked 𝔪 L.length) T).ideal.mem p) p
        (c.nd L g)

/-- **The conclusion of the invariant**: at a good point `p ∈ S_T` where every `[𝓓^i 𝔪]_T` (`i < μ`) has order
`≥ μ - i` along `S_T`, every germ of `𝔪_T` lies in `𝔪_p^μ`. -/
theorem GoodAt.orderGE (𝔪 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} {T : BlowupTower X Y} {p : Y}
    (hp : GoodAt 𝔪 S T p) (hcoh : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hD : ∀ i < 𝔪.d, OrderGE n (strictAlong T S) (geoTransformAlong (derivMarked 𝔪 i) T).ideal p (𝔪.d - i)) :
    ∀ f, (geoTransformAlong 𝔪 T).ideal.mem p f → (idealPow (pointIdeal n p) 𝔪.d).mem p f := by
  obtain ⟨k, -, c, G, hGmem, hGgen, hGder⟩ := hp
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh
  have hG : ∀ g, G g → (idealPow (pointIdeal n p) 𝔪.d).mem p g := by
    intro g hg
    refine c.mem_idealPow_of_vanishesToOrderOn (hhol p g (hGmem g hg)) fun L hL hLlen => ?_
    exact vanishesToOrderOn_of_isInSpanOnAt (hGder g hg L hL hLlen) fun s hs =>
      hD L.length hLlen s hs
  intro f hf
  exact mem_idealPow_of_isInSpanAt ((hGgen f hf).mono fun g hg => hG g hg)

/-- **Every point of `S` is good** for the empty tower: in a flat chart, the normal derivatives of germs of `𝔞` lie in
`𝓓^{|L|} 𝔞`. -/
theorem goodAt_refl (𝔪 : MarkedIdeal n X) (h𝔞 : 𝔪.ideal.IsCoherent) {S : Set X} (hS : IsClosedSubmanifold n S)
    {p : X} (hp : p ∈ S) : GoodAt 𝔪 S (BlowupTower.refl : BlowupTower X X) p := by
  obtain ⟨k, hk⟩ := hS.2 p hp
  refine ⟨k, hk.1, FlatChart.ofRegularAtDim hk, 𝔪.ideal.mem p, fun g hg => hg,
    fun f hf => InvertibleIdealQuotient.isInSpanAt_self hf
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞 p f hf), fun g hg L _ _ => ?_⟩
  have hmem := (FlatChart.ofRegularAtDim hk).nd_mem_iterDerivIdeal h𝔞 hg L
  exact ⟨1, fun _ => (FlatChart.ofRegularAtDim hk).nd L g, fun _ => 1, fun _ => hmem,
    fun _ => holomorphicAt_const 1, Eventually.of_forall fun y _ => by simp⟩

/-! ### Tools -/

section Tools

variable {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]


/-- **A flat chart from a holomorphic map with injective derivative.** -/
theorem FlatChart.exists_of_map {S' : Set Z} {z : Z} {k : ℕ} {W : Z → ComplexModel n} {O : Set Z} (hO : IsOpen O)
    (hzO : z ∈ O) (hW : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W y) (hWz : W z = 0)
    (hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)))
    (hflat : ∀ y ∈ O, (y ∈ S' ↔ W y ∈ complexCoordinatePlane n k)) :
    ∃ c : FlatChart n S' z k, c.ψ =ᶠ[𝓝 z] W := by
  set e := chartAt (ComplexModel n) z with he
  set Nset : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
  have hzN : e z ∈ Nset := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ (fun ζ => W (e.symm ζ)) Nset := fun ζ hζ => by
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) (chart_mem_atlas (ComplexModel n) z) hζ.1
    exact (mdifferentiableAt_iff_differentiableAt.mp ((hW _ hζ.2).comp _ h1)).differentiableWithinAt
  obtain ⟨Θ, hΘN, hΘF, -⟩ := Hironaka.exists_localHolomorphicEquivAt hNo hzN hFd hinj
  refine ⟨⟨Θ, fun ζ hζ => (hΘN hζ).1, ?_, ?_⟩, ?_⟩
  · rw [hΘF]
    show W (e.symm (e z)) = 0
    rw [e.left_inv (mem_chart_source _ z)]; exact hWz
  · intro y hy hyΘ
    have hyO : y ∈ O := by
      have h := (hΘN hyΘ).2
      rwa [mem_preimage, e.left_inv hy] at h
    rw [hΘF]
    show y ∈ S' ↔ W (e.symm (e y)) ∈ _
    rw [e.left_inv hy]; exact hflat y hyO
  · filter_upwards [e.open_source.mem_nhds (mem_chart_source _ z)] with y hy
    show Θ.toFun (e y) = W y
    rw [hΘF]
    show W (e.symm (e y)) = W y
    rw [e.left_inv hy]

/-- For a flat chart `c` with `c.ψ = W` near `z`, `W (c.inv u) = u` near `0`. -/
theorem FlatChart.eventually_map_inv {S' : Set Z} {z : Z} {k : ℕ} (c : FlatChart n S' z k) {W : Z → ComplexModel n}
    (hcW : c.ψ =ᶠ[𝓝 z] W) : ∀ᶠ u in 𝓝 (0 : ComplexModel n), W (c.inv u) = u := by
  filter_upwards [c.eventually_ψ_inv, c.tendsto_inv.eventually hcW] with u hu hu'
  rw [← hu', hu]

end Tools

/-! ### The step off the centre -/

section OffCentre

variable {Y Z : CMfd.{u} n}

/-- **The invariant off the centre**: if `π z ∉ C` and `π z` is good for `T`, then `z` is good for the tower
continued by the blowup `π` along `C` (the generators pull back, `π` is a local biholomorphism). -/
theorem goodAt_step_of_notMem (𝔪 : MarkedIdeal n X) {S : Set X} (T : BlowupTower X Y) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNT : (geoTransformAlong 𝔪 T).N = univ)
    (hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hDN : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).N = univ)
    (hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).ideal.IsCoherent)
    (hSc : IsClosed (strictAlong T S)) {z : Z} (hzC : π z ∉ C) (hgood : GoodAt 𝔪 S T (π z)) :
    GoodAt 𝔪 S (.step T C π hπ) z := by
  obtain ⟨k, hkn, c, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have hSev : ∀ᶠ y in 𝓝 z, (y ∈ strictAlong (.step T C π hπ) S ↔ π y ∈ strictAlong T S) := by
    filter_upwards [(hπ.1.1.isOpen_compl.preimage hπc).mem_nhds hzC] with y hy
    rw [strictAlong_step]
    refine ⟨fun h => ?_, fun h => subset_closure ⟨h, hy⟩⟩
    exact closure_minimal (preimage_mono sdiff_subset) (hSc.preimage hπc) h
  -- the new coordinates `W = ψ ∘ π`
  set W : Z → ComplexModel n := fun y => c.ψ (π y) with hWdef
  have hev : ∀ᶠ y in 𝓝 z, π y ∈ BlowupFlatCoordinates.flatDomain c.Φ ∧
      (y ∈ strictAlong (.step T C π hπ) S ↔ π y ∈ strictAlong T S) :=
    ((hπc.tendsto z).eventually c.eventually_mem_flatDomain).and hSev
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hev
  have hW : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W y := fun y hy =>
    (c.mdifferentiableAt_ψ (hOsub hy).1).comp y (hπd y)
  have hflat : ∀ y ∈ O, (y ∈ strictAlong (.step T C π hπ) S ↔ W y ∈ complexCoordinatePlane n k) := fun y hy => by
    rw [(hOsub hy).2]; exact c.flat (hOsub hy).1.1 (hOsub hy).1.2
  have hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z)) := by
    set I := 𝓘(ℂ, ComplexModel n) with hI
    have hrange : range I = univ := by simp [hI]
    set e := chartAt (ComplexModel n) z with he
    set e' := chartAt (ComplexModel n) (π z) with he'
    set F : ComplexModel n → ComplexModel n := fun u => e' (π (e.symm u)) with hF
    have hmd : MDifferentiableAt I I π z := hπd z
    have hderiv : mfderiv I I π z = fderiv ℂ F (e z) := by
      rw [hmd.mfderiv, hrange, fderivWithin_univ]
      rfl
    have hFinj : Function.Injective (fderiv ℂ F (e z)) := by
      have hz : z ∉ BlowupSequences.exceptionalLocus n π :=
        fun h => hzC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
      simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hz
      rw [hderiv] at hz
      exact hz.1
    -- `W ∘ e⁻¹ = Φ ∘ F` near `e z`
    have hzs : z ∈ e.source := mem_chart_source _ z
    have hFz : F (e z) = e' (π z) := by simp only [hF, e.left_inv hzs]
    have hloc : (fun ζ => W (e.symm ζ)) =ᶠ[𝓝 (e z)] fun ζ => c.Φ.toFun (F ζ) := by
      filter_upwards with ζ
      rfl
    have hFd : DifferentiableAt ℂ F (e z) := by
      have h := (contMDiffOn_iff.mp (hπ.contMDiff.contMDiffOn (s := univ))).2 z (π z)
      have hset : (e.target ∩ e.symm ⁻¹' (univ ∩ π ⁻¹' e'.source)) ∈ 𝓝 (e z) := by
        refine (e.continuousOn_symm.isOpen_inter_preimage e.open_target
          (isOpen_univ.inter (hπc.isOpen_preimage _ e'.open_source))).mem_nhds ?_
        exact ⟨e.map_source hzs, by rw [mem_preimage, e.left_inv hzs]; exact ⟨mem_univ _, mem_chart_source _ _⟩⟩
      refine ((h.differentiableOn (by simp)).mono ?_).differentiableAt hset
      intro u hu
      exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
    have hΦd : DifferentiableAt ℂ c.Φ.toFun (F (e z)) := by
      rw [hFz]
      exact c.Φ.toFun_holomorphic.differentiableAt (c.Φ.isOpen_source.mem_nhds c.Φ.center_mem_source)
    have hcomp : HasFDerivAt (fun ζ => c.Φ.toFun (F ζ))
        ((fderiv ℂ c.Φ.toFun (F (e z))).comp (fderiv ℂ F (e z))) (e z) :=
      hΦd.hasFDerivAt.comp (e z) hFd.hasFDerivAt
    rw [hloc.fderiv_eq, hcomp.fderiv]
    refine (c.injective_fderiv_Φ ?_).comp hFinj
    rw [hFz]; exact c.Φ.center_mem_source
  obtain ⟨c', hc'⟩ := FlatChart.exists_of_map hO hzO hW c.ψ_self hinj hflat
  -- `π ∘ c'.inv = c.inv` near `0`
  have hWinv := FlatChart.eventually_map_inv c' hc'
  have hπinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), π (c'.inv u) = c.inv u := by
    have ht : Tendsto (fun u => π (c'.inv u)) (𝓝 (0 : ComplexModel n)) (𝓝 (π z)) :=
      (hπc.tendsto z).comp c'.tendsto_inv
    filter_upwards [hWinv, ht.eventually c.eventually_inv_ψ] with u hu hu'
    rw [← hu', show c.ψ (π (c'.inv u)) = u from hu]
  -- normal derivatives of pulled-back generators
  have hnd : ∀ (g : Y → ℂ) (L : List (Fin n)), c'.nd L (g ∘ π) =ᶠ[𝓝 z] fun z' => c.nd L g (π z') := by
    intro g L
    have hgerm : (fun u => (g ∘ π) (c'.inv u)) =ᶠ[𝓝 (0 : ComplexModel n)] fun u => g (c.inv u) := by
      filter_upwards [hπinv] with u hu
      simp only [Function.comp_apply, hu]
    have hiter := iterDeriv_congr_of_eventuallyEq hgerm (L.map bv)
    filter_upwards [c'.tendsto_ψ.eventually hiter, hc'] with z' h1 h2
    simp only [FlatChart.nd]
    rw [h1, h2]
  -- the transformed ideals at `z`
  have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
  have hideal : (geoTransformAlong 𝔪 (.step T C π hπ)).ideal =
      controlledTransform hπ (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
    rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, hd]
  have hpb : ∀ {𝔟 : GermIdeal n Y} {g : Y → ℂ}, 𝔟.IsCoherent → 𝔟.mem (π z) g →
      (GermIdeal.pullback (m := n) π 𝔟).mem z (g ∘ π) := fun {𝔟} {g} h𝔟 hg =>
    InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (π z) a ∧ s = a ∘ π) ⟨g, hg, rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd)
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔟 _ _ hg))
  refine ⟨k, hkn, c', fun h => ∃ g, G g ∧ h = g ∘ π, ?_, ?_, ?_⟩
  · rintro h ⟨g, hg, rfl⟩
    rw [hideal]
    exact GlueingTrivialAction.pullback_le_controlledTransform hπ hcohT 𝔪.d z _ (hpb hcohT (hGmem g hg))
  · intro f hf
    -- `f ∈ π^*𝔪_T` at `z` (off the centre the denominator contains `1`)
    have hf' : (GermIdeal.pullback (m := n) π (geoTransformAlong 𝔪 T).ideal).mem z f := by
      have h1 := MarkedIdeals.MarkedIdeal.one_mem_idealPow (n := n)
        (MarkedIdeals.MarkedIdeal.one_mem_pullback_vanishingIdeal (n := n) (π := π) hzC hπ.1.1) 𝔪.d
      have hf2 := hf
      rw [geoTransformAlong_step, geoTransform_ideal, hNT, MarkedIdeals.MarkedIdeal.geoStrictTransform_univ hπ, hd]
        at hf2
      have h3 := (InvertibleIdealQuotient.mem_colon_iff.mp hf2).2 _ h1
      rw [BlowupTowerTransforms.restrictOn_univ (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcohT)]
        at h3
      exact NormalDerivativeChart.mem_congr_of_isCoherent (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcohT) h3
        (Eventually.of_forall fun y => by simp)
    refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => ?_)
      (show IsInSpanAt (n := n) (fun s => ∃ a, (geoTransformAlong 𝔪 T).ideal.mem (π z) a ∧ s = a ∘ π) z f from hf')
    obtain ⟨a, ha, rfl⟩ := ht
    exact (isInSpanAt_comp_map (Eventually.of_forall hπd) (hGgen a ha)).mono fun s ⟨g, hg, hs⟩ => ⟨g, hg, hs⟩
  · rintro h ⟨g, hg, rfl⟩ L hL hLlen
    obtain ⟨K, s, a, hs, ha, hsum⟩ := hGder g hg L hL hLlen
    have hdL : L.length ≤ 𝔪.d := hLlen.le
    have hDideal : (geoTransformAlong (derivMarked 𝔪 L.length) (.step T C π hπ)).ideal =
        controlledTransform hπ (geoTransformAlong (derivMarked 𝔪 L.length) T).ideal
          (geoTransformAlong (derivMarked 𝔪 L.length) T).d := by
      rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform (hDN _ hdL) (hDcoh _ hdL) hπ]
    refine ⟨K, fun i => s i ∘ π, fun i => a i ∘ π, fun i => ?_, fun i =>
      HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (ha i), ?_⟩
    · rw [hDideal]
      exact GlueingTrivialAction.pullback_le_controlledTransform hπ (hDcoh _ hdL) _ z _
        (hpb (hDcoh _ hdL) (hs i))
    · filter_upwards [hnd g L, hSev, (hπc.tendsto z).eventually hsum] with z' h1 h2 h3 hz'
      rw [h1]
      exact h3 (h2.mp hz')

end OffCentre

/-! ### The step over the centre -/

section Centre

open BlowupFlatCoordinates BlowupMonomialCharts

variable {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]


/-- **The normal derivatives through a monomial chart, on the manifolds.**  Let `c''` be a flat chart at `π z`,
`W` coordinates near `z` with `c''.ψ ∘ π = σⱼ ∘ W` on an open `O ∋ z`, and `c'` a flat chart at `z` with
`c'.ψ = W - W z` near `z`.  If `g ∘ π = Wⱼ^d · h'` near `z`, then for normal directions `L` (`l ≠ j`, `k_C ≤ l`)
`Wⱼ^d · ∂^L h' = Wⱼ^{|L|} · (∂^L g) ∘ π` near `z`. -/
theorem nd_monomial_identity {π : Z → Y} (hπ : Continuous π) {z : Z} {S : Set Y} {S'' : Set Z}
    {k'' k' kC : ℕ} (c'' : FlatChart n S (π z) k'') (c' : FlatChart n S'' z k') {W : Z → ComplexModel n}
    {O : Set Z} (hO : IsOpen O) (hzO : z ∈ O) {j : Fin n}
    (hWeq : ∀ z' ∈ O, c''.ψ (π z') = monomial kC j (W z')) (hc' : c'.ψ =ᶠ[𝓝 z] fun y => W y - W z)
    {d : ℕ} {g : Y → ℂ} {h' : Z → ℂ} (hg : HolomorphicAt n g (π z)) (hh' : HolomorphicAt n h' z)
    (hrel : ∀ᶠ y in 𝓝 z, g (π y) = W y j ^ d * h' y) (L : List (Fin n)) (hL : ∀ l ∈ L, l ≠ j ∧ kC ≤ l.1) :
    ∀ᶠ z' in 𝓝 z, W z' j ^ d * c'.nd L h' z' = W z' j ^ L.length * c''.nd L g (π z') := by
  have hσc : Continuous (monomial (n := n) kC j) := (contDiff_monomial kC j).continuous
  have hσd : Differentiable ℂ (monomial (n := n) kC j) := (contDiff_monomial kC j).differentiable (by simp)
  have hσa : monomial kC j (W z) = 0 := by rw [← hWeq z hzO]; exact c''.ψ_self
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.mp (c''.eventually_differentiableAt_comp_inv hg)
  have hG₀ : DifferentiableOn ℂ (fun w => g (c''.inv w)) (ball 0 r₁) := fun w hw =>
    (hball₁ w hw).differentiableWithinAt
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.eventually_nhds_iff_ball.mp (c'.eventually_differentiableAt_comp_inv hh')
  have hH : DifferentiableOn ℂ (fun u => h' (c'.inv u)) (ball 0 r₀) := fun u hu =>
    (hball₀ u hu).differentiableWithinAt
  obtain ⟨U, hU⟩ : ∃ U : Set (ComplexModel n), U = monomial kC j ⁻¹' ball 0 r₁ := ⟨_, rfl⟩
  have hUo : IsOpen U := hU ▸ isOpen_ball.preimage hσc
  have hUσ : MapsTo (monomial (n := n) kC j) U (ball 0 r₁) := fun w hw => by rw [hU] at hw; exact hw
  have hGσ : DifferentiableOn ℂ (fun w => g (c''.inv (monomial kC j w))) U := fun w hw =>
    (((hG₀ _ (hUσ hw)).differentiableAt (isOpen_ball.mem_nhds (hUσ hw))).comp w (hσd w)).differentiableWithinAt
  have hW'inv := FlatChart.eventually_map_inv c' hc'
  have hinv : Tendsto c'.inv (𝓝 (0 : ComplexModel n)) (𝓝 z) := c'.tendsto_inv
  have hπinv : Tendsto (fun u => π (c'.inv u)) (𝓝 (0 : ComplexModel n)) (𝓝 (π z)) :=
    (hπ.tendsto z).comp hinv
  have hid : (fun u => (u + W z) j ^ d * h' (c'.inv u)) =ᶠ[𝓝 (0 : ComplexModel n)]
      fun u => g (c''.inv (monomial kC j (u + W z))) := by
    filter_upwards [hW'inv, hinv.eventually (hO.mem_nhds hzO), hinv.eventually hrel,
      hπinv.eventually c''.eventually_inv_ψ] with u hu huO hurel huinv
    have hu' : W (c'.inv u) - W z = u := hu
    have hWu : W (c'.inv u) = u + W z := sub_eq_iff_eq_add.mp hu'
    rw [← hWu, ← hurel, ← hWeq _ huO, huinv]
  have hI := iterDeriv_congr_of_eventuallyEq hid (L.map bv)
  have ht : Tendsto c'.ψ (𝓝 z) (𝓝 (0 : ComplexModel n)) := c'.tendsto_ψ
  have hshift : ∀ᶠ z' in 𝓝 z, c'.ψ z' + W z ∈ U := by
    have hcont : ContinuousAt (fun u : ComplexModel n => u + W z) 0 := (continuous_add_const (W z)).continuousAt
    have h0 : (0 : ComplexModel n) + W z ∈ U := by
      rw [hU, Set.mem_preimage, zero_add, hσa]; exact mem_ball_self hr₁
    exact ht.eventually (hcont.eventually (hUo.mem_nhds h0))
  have hLj : ∀ l ∈ L, ∀ (w : ComplexModel n) (t : ℂ), (fun u : ComplexModel n => (u + W z) j ^ d) (w + t • bv l) =
      (fun u : ComplexModel n => (u + W z) j ^ d) w := fun l hl w t => by
    have hjl : j ≠ l := Ne.symm (hL l hl).1
    simp [bv, hjl]
  have hcd : Differentiable ℂ (fun u : ComplexModel n => (u + W z) j ^ d) := fun u =>
    (((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt).comp u
      (differentiableAt_id.add_const (W z))).pow d
  filter_upwards [ht.eventually hI, ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr₀)), hshift, hc',
    hO.mem_nhds hzO] with z' h1 h2 h3 h4 hz'O
  have hlhs := iterDeriv_mul_of_const isOpen_ball hcd hH L hLj (c'.ψ z') h2
  have hrhs1 := iterDeriv_comp_add hUo hGσ (W z) L h3
  have hrhs2 := iterDeriv_comp_monomial (G := fun w => g (c''.inv w)) hUo isOpen_ball hUσ hG₀ L hL
    (c'.ψ z' + W z) h3
  have h4' : c'.ψ z' = W z' - W z := h4
  have hWz' : c'.ψ z' + W z = W z' := by rw [h4']; abel
  simp only [FlatChart.nd]
  rw [hlhs, hrhs1, hrhs2, hWz'] at h1
  rw [hWeq z' hz'O]
  simpa [hWz'] using h1

end Centre

section CentreStep

open BlowupFlatCoordinates BlowupMonomialCharts

variable {Y Z : CMfd.{u} n}

/-- **The invariant over the centre**: if `π z ∈ C`, `z` lies on the strict transform of `S_T` and `π z` is good for `T`,
then `z` is good for the tower continued by the blowup `π` along `C`.  The new coordinates are a monomial chart
`x' = x / y_m` over nested product-form coordinates for `C ⊆ S_T`, the new generators are the controlled transforms
`h' = W_j^{-μ} (g ∘ π)` of the old ones, and `W_j^μ ∂^L h' = W_j^{|L|} (∂^L g) ∘ π` (`nd_monomial_identity`). -/
theorem goodAt_step_of_mem (𝔪 : MarkedIdeal n X) {S : Set X} (T : BlowupTower X Y) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNT : (geoTransformAlong 𝔪 T).N = univ)
    (hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent)
    (hDN : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).N = univ)
    (hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).ideal.IsCoherent)
    (hCadm : (geoTransformAlong 𝔪 T).IsAdmissibleCentre C)
    (hDadm : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).IsAdmissibleCentre C)
    (hSc : IsClosed (strictAlong T S)) (hCS : C ⊆ strictAlong T S) {z : Z}
    (hz : z ∈ strictAlong (.step T C π hπ) S) (hzC : π z ∈ C) (hgood : GoodAt 𝔪 S T (π z)) :
    GoodAt 𝔪 S (.step T C π hπ) z := by
  obtain ⟨k, hkn, c, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcohT
  -- nested product-form coordinates for `C ⊆ S_T` at `π z`
  obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
  have hSreg : RegularAtDim (n := n) (strictAlong T S) (π z) k := ⟨hkn, hCS hzC, c.Φ, c.src, c.zero, c.flat⟩
  have hkCk : kC ≤ k := BlowupStrictSubmanifold.le_of_regularAtDim_subset hkC hSreg hCS
  obtain ⟨c'', hc''C, hc''nd⟩ := FlatChart.exists_nested c hkCk hkn hkC hCS
  -- the monomial chart at `z`
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hℓ, hiff⟩ :=
    BlowupStrictSubmanifold.exists_local_geoStrictTransform hπ c''.src hc''C c''.flat
      (mem_flatDomain_self c''.Φ)
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ c''.src hc''C hj
  have hWeq : ∀ z' ∈ O, π z' ∈ flatDomain c''.Φ ∧
      monomial kC j (W z') = c''.Φ.toFun (chartAt (ComplexModel n) (π z) (π z')) := by
    intro z' hz'
    have hw := hWmem z' hz'
    have h1 := hℓ ℓ hℓs hℓπ z' hz' hw
    have h2 := congrFun hℓπ (LiftedOpen.mk _ (W z') hw)
    rw [Function.comp_apply, h1] at h2
    have h3 := flatInverse_mem c''.Φ hw c''.src
    rw [h2]
    simp only [monomialChart, LiftedOpen.toModel_mk]
    exact ⟨h3.1, h3.2.symm⟩
  have hWeq' : ∀ z' ∈ O, c''.ψ (π z') = monomial kC j (W z') := fun z' hz' => (hWeq z' hz').2.symm
  obtain ⟨hjk, hWz⟩ := (hiff z hzO).mp hz
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hc''C (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2,
      BlowupStrictSubmanifold.monomial_mem_plane_iff hj]
  -- the new flat chart `W - W z`
  have hW' : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun y => W y - W z) y :=
    fun y hy => ((hWs y hy).mdifferentiableAt (by simp)).sub mdifferentiableAt_const
  have hflat' : ∀ y ∈ O, (y ∈ strictAlong (.step T C π hπ) S ↔ W y - W z ∈ complexCoordinatePlane n k) := by
    intro y hy
    rw [BlowupStrictSubmanifold.sub_mem_plane_iff hWz]
    exact (hiff y hy).trans ⟨fun h => h.2, fun h => ⟨hjk, h⟩⟩
  have hinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ) - W z) (chartAt (ComplexModel n) z z)) := by
    set e := chartAt (ComplexModel n) z with he
    have hFd : DifferentiableAt ℂ (fun ζ => W (e.symm ζ)) (e z) := by
      have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) (chart_mem_atlas (ComplexModel n) z)
        (e.map_source (mem_chart_source _ z))
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (e.symm (e z)) := by
        rw [e.left_inv (mem_chart_source _ z)]; exact (hWs z hzO).mdifferentiableAt (by simp)
      exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
    rw [fderiv_sub_const]
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    by_contra hv0
    apply BlowupFibreDirection.fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hzO hv0
    rw [hFd.fderiv_restrictScalars ℝ]
    exact hv
  obtain ⟨c', hc'⟩ := FlatChart.exists_of_map hO hzO hW' (sub_self _) hinj hflat'
  -- the local equation `W_j` of the exceptional divisor
  have hl : BlowupFunctionTransform.IsLocalEquation hπ O (fun p => W p j) :=
    GlueingTrivialAction.isLocalEquation_monomial hπ c''.src hc''C hj hO hWs hWeq
  have hlhol : HolomorphicAt n (fun p => W p j ^ 𝔪.d) z := by
    have h1 : HolomorphicAt n (fun p => W p j) z := by
      filter_upwards [hO.mem_nhds hzO] with y hy
      exact (hl.mdifferentiableOn y hy).mdifferentiableAt (hO.mem_nhds hy)
    exact h1.mono fun y hy => hy.pow _
  -- the transformed ideals
  have hd : (geoTransformAlong 𝔪 T).d = 𝔪.d := d_geoTransformAlong 𝔪 T
  have hideal : (geoTransformAlong 𝔪 (.step T C π hπ)).ideal =
      controlledTransform hπ (geoTransformAlong 𝔪 T).ideal 𝔪.d := by
    rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, hd]
  have hDideal : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) (.step T C π hπ)).ideal =
      controlledTransform hπ (geoTransformAlong (derivMarked 𝔪 i) T).ideal (𝔪.d - i) := fun i hi => by
    rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform (hDN i hi) (hDcoh i hi) hπ,
      d_geoTransformAlong, derivMarked_d]
  have h𝔪le : (geoTransformAlong 𝔪 T).ideal.Le (idealPow (vanishingIdeal (n := n) C) 𝔪.d) := by
    have := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcohT hCadm
    rwa [hd] at this
  have hDle : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).ideal.Le
      (idealPow (vanishingIdeal (n := n) C) (𝔪.d - i)) := fun i hi => by
    have := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (hDN i hi) (hDcoh i hi) (hDadm i hi)
    rwa [d_geoTransformAlong, derivMarked_d] at this
  -- `W_j` vanishes on no relatively open subset of the strict transform
  have hnonS : ∀ V : Set Z, IsOpen V → V ⊆ O → (V ∩ strictAlong (.step T C π hπ) S).Nonempty →
      ∃ y ∈ V ∩ strictAlong (.step T C π hπ) S, W y j ^ 𝔪.d ≠ 0 := by
    rintro V hV hVO ⟨y₀, hy₀V, hy₀S⟩
    rw [strictAlong_step] at hy₀S
    obtain ⟨y₁, hy₁V, hy₁S, hy₁C⟩ :=
      mem_closure_iff.mp (show y₀ ∈ closure (π ⁻¹' (strictAlong T S \ C)) from hy₀S) V hV hy₀V
    refine ⟨y₁, ⟨hy₁V, ?_⟩, pow_ne_zero _ fun h => hy₁C ((hCu y₁ (hVO hy₁V)).mpr h)⟩
    rw [strictAlong_step]
    exact subset_closure ⟨hy₁S, hy₁C⟩
  have hnonU : ∀ V : Set Z, IsOpen V → V ⊆ O → (V ∩ univ).Nonempty → ∃ y ∈ V ∩ univ, W y j ^ 𝔪.d ≠ 0 := by
    rintro V hV hVO ⟨y₀, hy₀V, -⟩
    obtain ⟨y, hyV, hy⟩ := hl.nonvanishing V hV hVO ⟨y₀, hy₀V⟩
    exact ⟨y, ⟨hyV, mem_univ _⟩, pow_ne_zero _ hy⟩
  refine ⟨k, hkn, c', fun h' => ∃ g, G g ∧ HolomorphicAt n h' z ∧
    ∀ᶠ y in 𝓝 z, g (π y) = W y j ^ 𝔪.d * h' y, ?_, ?_, ?_⟩
  · -- the new generators are germs of the transform
    rintro h' ⟨g, hg, hh', hrel⟩
    rw [hideal]
    exact BlowupFunctionTransform.mem_controlledTransform_of_eq_pow_mul hl hzO (hGmem g hg) hh' hrel
  · -- they generate it
    intro f hf
    have hfhol : HolomorphicAt n f z := (show (controlledTransform hπ (geoTransformAlong 𝔪 T).ideal 𝔪.d).mem z f
      by rw [← hideal]; exact hf).1
    have hWf : (GermIdeal.pullback (m := n) π (geoTransformAlong 𝔪 T).ideal).mem z
        (fun y => W y j ^ 𝔪.d * f y) := by
      have hf' : (controlledTransform hπ (geoTransformAlong 𝔪 T).ideal 𝔪.d).mem z f := by rw [← hideal]; exact hf
      refine (InvertibleIdealQuotient.mem_colon_iff.mp hf').2 _ ?_
      exact (hl.idealPow_mem_iff 𝔪.d z hzO _).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hlhol)
    -- every generator `g ∘ π` is `W_j^μ h'` with `h'` a new generator
    have hgen : ∀ g, G g → IsInSpanAt (n := n) (fun t => ∃ h', (∃ g', G g' ∧ HolomorphicAt n h' z ∧
        ∀ᶠ y in 𝓝 z, g' (π y) = W y j ^ 𝔪.d * h' y) ∧ t = fun y => W y j ^ 𝔪.d * h' y) z (g ∘ π) := by
      intro g hg
      obtain ⟨h', hh', heq⟩ := BlowupFunctionTransform.exists_eq_pow_mul hl hzO (h𝔪le _ _ (hGmem g hg))
      exact isInSpanAt_of_eq_mul ⟨h', ⟨g, hg, hh', heq.mono fun y hy => hy⟩, rfl⟩
        (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (hhol _ _ (hGmem g hg)))
        (holomorphicAt_const 1) (heq.mono fun y hy => by simp only [one_mul]; exact hy)
    have hspan : IsInSpanAt (n := n) (fun t => ∃ h', (∃ g', G g' ∧ HolomorphicAt n h' z ∧
        ∀ᶠ y in 𝓝 z, g' (π y) = W y j ^ 𝔪.d * h' y) ∧ t = fun y => W y j ^ 𝔪.d * h' y) z
        (fun y => W y j ^ 𝔪.d * f y) := RelativePrincipalizationSpan.IsInSpanAt.trans (fun t ht => ?_)
      (show IsInSpanAt (n := n) (fun s => ∃ a, (geoTransformAlong 𝔪 T).ideal.mem (π z) a ∧ s = a ∘ π) z
        (fun y => W y j ^ 𝔪.d * f y) from hWf)
    · obtain ⟨-, K, t, b, ht, hb, hsum⟩ := hspan
      choose h' hh' htdef using ht
      refine ⟨hfhol, K, h', b, fun i => hh' i, hb, ?_⟩
      have hcan := RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within (W := univ) hO hnonU hzO
        (F := f) (G := fun y => ∑ i, b i y * h' i y) hfhol
        (HolomorphicAt.sum _ fun i _ => (hb i).mul (hh' i).choose_spec.2.1) ?_
      · filter_upwards [hcan] with y hy using hy (mem_univ y)
      · filter_upwards [hsum] with y hy _
        rw [hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [htdef i]; ring
    · obtain ⟨a, ha, rfl⟩ := ht
      exact RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => by
          obtain ⟨g, hg, rfl⟩ := hs; exact hgen g hg)
        (isInSpanAt_comp_map (Eventually.of_forall hπd) (hGgen a ha))
  · -- the normal derivatives
    rintro h' ⟨g, hg, hh', hrel⟩ L hL hLlen
    have hgp : HolomorphicAt n g (π z) := hhol _ _ (hGmem g hg)
    have hLj : ∀ l ∈ L, l ≠ j ∧ kC ≤ l.1 := fun l hl' => by
      have := hL l hl'
      exact ⟨fun h => by rw [h] at this; omega, by omega⟩
    have hid := nd_monomial_identity hπc c'' c' hO hzO hWeq' hc' hgp hh' hrel L hLj
    have hnd := (hπc.tendsto z).eventually (hc''nd L hL g hgp)
    obtain ⟨K, s, aa, hs, haa, hsum⟩ := hGder g hg L hL hLlen
    have hdL : L.length ≤ 𝔪.d := hLlen.le
    have hex : ∀ i, ∃ s' : Z → ℂ, HolomorphicAt n s' z ∧
        (s i ∘ π) =ᶠ[𝓝 z] fun y => W y j ^ (𝔪.d - L.length) * s' y := fun i =>
      BlowupFunctionTransform.exists_eq_pow_mul hl hzO (hDle _ hdL _ _ (hs i))
    choose s' hs'hol hs'eq using hex
    have hs'mem : ∀ i, (geoTransformAlong (derivMarked 𝔪 L.length) (.step T C π hπ)).ideal.mem z (s' i) := fun i => by
      rw [hDideal _ hdL]
      exact BlowupFunctionTransform.mem_controlledTransform_of_eq_pow_mul hl hzO (hs i) (hs'hol i) (hs'eq i)
    have hsub : ∀ᶠ z' in 𝓝 z, z' ∈ strictAlong (.step T C π hπ) S → π z' ∈ strictAlong T S :=
      Eventually.of_forall fun z' hz' =>
        BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπc hSc hz'
    have hmul : ∀ᶠ z' in 𝓝 z, z' ∈ strictAlong (.step T C π hπ) S →
        W z' j ^ 𝔪.d * c'.nd L h' z' = W z' j ^ 𝔪.d * ∑ i, (aa i ∘ π) z' * s' i z' := by
      filter_upwards [hid, hnd, (hπc.tendsto z).eventually hsum, eventually_all.mpr hs'eq, hsub] with
        z' h1 h2 h3 h4 h5 hz'
      rw [h1, h2, h3 (h5 hz'), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4i : s i (π z') = W z' j ^ (𝔪.d - L.length) * s' i z' := h4 i
      have e : W z' j ^ 𝔪.d = W z' j ^ L.length * W z' j ^ (𝔪.d - L.length) := by
        rw [← pow_add, Nat.add_sub_cancel' hdL]
      rw [h4i, Function.comp_apply, e]
      ring
    have hcan := RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hO hnonS hzO
      (FlatChart.holomorphicAt_nd c' hh' L)
      (HolomorphicAt.sum _ fun i _ =>
        (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i)).mul (hs'hol i)) hmul
    exact ⟨K, s', fun i => aa i ∘ π, hs'mem,
      fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i), hcan⟩

end CentreStep

/-! ### Along multiple test blow-ups -/

section Tower

/-- **Every point of the strict transform of `S` is good** along a multiple test blow-up of `𝔪` with centres in the
strict transforms of `S` (induction on the tower: `goodAt_refl`, `goodAt_step_of_mem`, `goodAt_step_of_notMem`). -/
theorem goodAt_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) {S : Set X}
    (hS : IsClosedSubmanifold n S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → CentresIn S T →
      ∀ p ∈ strictAlong T S, GoodAt 𝔪 S T p
  | _, .refl => fun _ _ p hp => goodAt_refl 𝔪 h𝔞 hS hp
  | _, .step T C π hπ => fun hT hTS z hz => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hTS0, hCS⟩ := hTS
      obtain ⟨-, hNT, -, hSsub, -, -⟩ := restrict_tower 𝔪 hN h𝔞 hS T hT0 hTS0
      have hSc : IsClosed (strictAlong T S) := hSsub.1
      have hpz : π z ∈ strictAlong T S :=
        BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hSc hz
      have hgood := goodAt_tower 𝔪 hN h𝔞 hS T hT0 hTS0 (π z) hpz
      have hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent :=
        (inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le _) T hT0).2.2.2.2.1
      have hDN : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).N = univ := fun i hi =>
        (inclusions_tower 𝔪 hN h𝔞 hi T hT0).2.2.1
      have hDcoh : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).ideal.IsCoherent := fun i hi =>
        (inclusions_tower 𝔪 hN h𝔞 hi T hT0).2.2.2.2.2.1
      have hDadm : ∀ i ≤ 𝔪.d, (geoTransformAlong (derivMarked 𝔪 i) T).IsAdmissibleCentre C := fun i hi =>
        ((isGeoTestTower_step_iff _ T C π hπ).mp (inclusions_tower 𝔪 hN h𝔞 hi (.step T C π hπ) hT).1).2
      by_cases hzC : π z ∈ C
      · exact goodAt_step_of_mem 𝔪 T hπ hNT hcohT hDN hDcoh hC hDadm hSc hCS hz hzC hgood
      · exact goodAt_step_of_notMem 𝔪 T hπ hNT hcohT hDN hDcoh hSc hzC hgood

/-- **Włodarczyk `le:S` (2), the inclusion `⊆`** (GGT Proposition 5.6.4 (2)): along a multiple test blow-up `T` of
`𝔪 = (X, X, E, 𝔞, μ)` with centres in the strict transforms of a closed submanifold `S`,
`supp[𝓒(𝔪)|_S]_T ⊆ supp(𝔪_T)`. -/
theorem cosupp_coeff_withN_tower_subset (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) (hTS : CentresIn S T) :
    (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp ⊆ (geoTransformAlong 𝔪 T).cosupp := by
  intro x hx
  obtain ⟨-, hRE, -⟩ := coeff_restrict_tower 𝔪 hN h𝔞 hd hS T hT hTS
  obtain ⟨-, hNT, -, hST, -, -⟩ := restrict_tower 𝔪 hN h𝔞 hS T hT hTS
  have hfam := isAmbientFamily_derivMarked hN h𝔞
  have hall : ∀ i < 𝔪.d, IsGeoTestTower (derivMarked 𝔪 i) T :=
    fun i hi => (inclusions_tower 𝔪 hN h𝔞 (le_of_lt hi) T hT).1
  obtain ⟨-, hmsum⟩ := geoTransformAlong_msum (fun i => derivMarked 𝔪 i) hd hfam T
  obtain ⟨he, hfamT⟩ := hmsum hall
  -- `x` is in the cosupport of `𝓒(𝔪)_T` along `S_T`
  have hx1 : x ∈ cosupport n (strictAlong T S) (geoTransformAlong (coeffMarked 𝔪) T).ideal (coeffMarked 𝔪).d := by
    rw [hRE.cosupp_eq] at hx
    have := hx
    rwa [cosupp_withN, d_geoTransformAlong] at this
  have hxS : x ∈ strictAlong T S := hx1.1
  -- hence every `[𝓓^i 𝔪]_T` has order `≥ μ - i` along `S_T` at `x`
  have hD : ∀ i < 𝔪.d, OrderGE n (strictAlong T S) (geoTransformAlong (derivMarked 𝔪 i) T).ideal x (𝔪.d - i) := by
    intro i hi
    have hx2 := hx1
    rw [show (geoTransformAlong (coeffMarked 𝔪) T) = msum (fun i => geoTransformAlong (derivMarked 𝔪 i) T) 𝔪.d
      from he] at hx2
    have hJ : ∀ i < 𝔪.d, ∀ y g, (idealPow (geoTransformAlong (derivMarked 𝔪 i) T).ideal
        (sumExp (fun j => (geoTransformAlong (derivMarked 𝔪 j) T).d) 𝔪.d i)).mem y g → HolomorphicAt n g y :=
      fun _ _ _ _ hg => holomorphicAt_of_mem_idealPow hg
    have hmark : (coeffMarked 𝔪).d = (Finset.range 𝔪.d).prod fun j => (geoTransformAlong (derivMarked 𝔪 j) T).d := by
      simp only [d_geoTransformAlong]; rfl
    rw [hmark] at hx2
    have hx3 := ((mem_cosupport_finSumIdeal hJ).mp hx2).2 i hi
    have hD1 : ∀ j < 𝔪.d, 1 ≤ (geoTransformAlong (derivMarked 𝔪 j) T).d := fun j hj => by
      rw [d_geoTransformAlong, derivMarked_d]; omega
    have hpow := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hST.2
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hfamT.coh i hi)) (one_le_sumExp hD1 i)
      (geoTransformAlong (derivMarked 𝔪 i) T).d
    rw [mul_sumExp (fun j => (geoTransformAlong (derivMarked 𝔪 j) T).d) hi] at hpow
    rw [hpow, d_geoTransformAlong, derivMarked_d] at hx3
    exact hx3.2
  -- the invariant gives the order of `𝔪_T`
  have hgood := goodAt_tower 𝔪 hN h𝔞 hS T hT hTS x hxS
  have hcohT : (geoTransformAlong 𝔪 T).ideal.IsCoherent :=
    (inclusions_tower 𝔪 hN h𝔞 (Nat.zero_le _) T hT).2.2.2.2.1
  have hord := hgood.orderGE 𝔪 S hcohT hD
  rw [MarkedIdeal.cosupp, hNT, d_geoTransformAlong]
  exact ⟨mem_univ x, fun f hf => ⟨f, hord f hf, Eventually.of_forall fun _ _ => rfl⟩⟩

/-- `supp[𝓒(𝔪)|_S]_T = supp(𝔪_T) ∩ S_T` along a multiple test blow-up of `𝔪` with centres in the strict transforms. -/
theorem cosupp_coeff_withN_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) (hTS : CentresIn S T) :
    (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp = (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S := by
  refine Subset.antisymm (fun x hx => ⟨cosupp_coeff_withN_tower_subset 𝔪 hN h𝔞 hd hS T hT hTS hx, ?_⟩)
    (coeff_restrict_tower 𝔪 hN h𝔞 hd hS T hT hTS).2.2
  have h := (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp_subset_N hx
  rwa [N_geoTransformAlong_withN] at h

/-- **Włodarczyk `le:S` in full** (GGT Proposition 5.6.4): for `𝔪 = (X, X, E, 𝔞, μ)` with `𝔞` coherent and `μ ≥ 1`
and a closed submanifold `S`, a tower is a multiple test blow-up of `𝓒(𝔪)|_S` if and only if it is a multiple test
blow-up of `𝔪` with centres in the strict transforms of `S`, and along it
`supp[𝓒(𝔪)|_S]_T = supp(𝔪_T) ∩ S_T`. -/
theorem coeff_restrict_tower_iff (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (withN (coeffMarked 𝔪) S) T ↔ IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower (withN (coeffMarked 𝔪) S) T →
        (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp = (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S)
  | _, .refl => ⟨⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩, fun _ => cosupp_coeff_withN 𝔪 hN h𝔞 hd S⟩
  | _, .step T C π hπ => by
      obtain ⟨ih, -⟩ := coeff_restrict_tower_iff 𝔪 hN h𝔞 hd hS T
      have hE : (geoTransformAlong (withN (coeffMarked 𝔪) S) T).E = (geoTransformAlong 𝔪 T).E :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := withN (coeffMarked 𝔪) S) (𝔫 := 𝔪) rfl T
      have hiff : IsGeoTestTower (withN (coeffMarked 𝔪) S) (.step T C π hπ) ↔
          IsGeoTestTower 𝔪 (.step T C π hπ) ∧ CentresIn S (.step T C π hπ) := by
        rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff, centresIn_step_iff]
        constructor
        · rintro ⟨h0, hC⟩
          obtain ⟨hT0, hTS0⟩ := ih.mp h0
          have hcos := cosupp_coeff_withN_tower 𝔪 hN h𝔞 hd hS T hT0 hTS0
          refine ⟨⟨hT0, hC.1, fun x hx => (hcos ▸ hC.2.1 hx).1, hE ▸ hC.2.2⟩, hTS0, fun x hx => (hcos ▸ hC.2.1 hx).2⟩
        · rintro ⟨⟨hT0, hC⟩, hTS0, hCS⟩
          have hcos := cosupp_coeff_withN_tower 𝔪 hN h𝔞 hd hS T hT0 hTS0
          refine ⟨ih.mpr ⟨hT0, hTS0⟩, hC.1, fun x hx => ?_, hE.symm ▸ hC.2.2⟩
          rw [hcos]; exact ⟨hC.2.1 hx, hCS hx⟩
      refine ⟨hiff, fun h => ?_⟩
      obtain ⟨hT', hTS'⟩ := hiff.mp h
      exact cosupp_coeff_withN_tower 𝔪 hN h𝔞 hd hS _ hT' hTS'

end Tower

end

end Hironaka.CoefficientRestrictionTower
