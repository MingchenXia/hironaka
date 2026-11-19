import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedProductCoordinates

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient invariant along `N` at a stage (G8 lane, run 0080, round 5; (B') port P4, part 1)

Blueprint: `hironaka-g8-resume-contact-stage-invariant.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2
(P4, Bierstone--Milman 2008 Corollary 4.2), G8 `REPORT-r4.md` (route).

The library proves Włodarczyk's Lemma `le:S` along `N` (GGT 2008, Proposition 5.6.4) along multiple test blow-ups from a
FIXED base (`CoefficientIdealAlongRestrictionFull.GoodAtAlong 𝔪 S T p`: the transforms `𝔪_T`, `[𝓓_N^i 𝔪]_T`, `S_T` along
`T`).  The local form of Bierstone--Milman's Corollary 4.2 (P4) needs the invariant at a stage reached by ANY local
history (blowups, products with a line, open restrictions), so here its data are variables:

* **`GoodAt P F S p`**: the body of `GoodAtAlong` with the stage marked ideal `P`, a family `F` of marked ideals (the
  stand-ins for the transformed derivative ideals, `F i` of mark `d - i`) and a set `S` as variables; `GoodAt.orderGE`;
  `goodAt_base` (for `F = 𝓓_N^• 𝔪` at the base: `goodAtAlong_refl`);
* **`goodAt_step_of_notMem`, `goodAt_step_of_mem`**: one admissible blowup (copies of the library's
  `goodAtAlong_step_of_notMem` / `goodAtAlong_step_of_mem` with stage-only hypotheses);
* **`goodAt_pullback_submersion`**: pullback along a holomorphic submersion `f : Y' → Y` (`dim Y' = n + r`), in the
  adapted product coordinates of `HironakaSmoothSubmersionAdaptedProductCoordinates` (fibre coordinates first): the flat
  chart, the generators `g ∘ f` and the normal derivatives `∂^{L'}(g ∘ f) = (∂^L g) ∘ f` (`nd_pullback_submersion`,
  from `iterDeriv_comp_clm'`).  Products with a line (`Prod.fst`) and open restrictions (`Subtype.val`) are such pullbacks.

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ContactGood

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealAlongRestrictionTower NormalTaylorOrder NormalDerivativeChart NormalDerivativeMonomial
  NormalDerivativeAlong BlowupStrictSubmanifold BlowupFunctionTransform RelativePrincipalizationSpan
  CoefficientIdealAlongRestrictionFull HolomorphicTaylorTail

noncomputable section

/-! ### The invariant at a stage -/

section Invariant

variable {n : ℕ} {Y : CMfd.{u} n}

/-- **The coefficient invariant along `N` at a stage**, at a point `p` of `S`: a flat chart `c` for `S` at `p` (plane
`ℂ^{k_S} × 0`) in which `P.N` is the plane `ℂ^{k_N} × 0` (`k_S ≤ k_N ≤ n`), and generators `G` of `P.ideal` along `P.N`
at `p` such that for every generator `g` and every list `L` of directions in `[k_S, k_N)` with `|L| < P.d`, the
derivative `∂^L g` restricts on `S` near `p` into `(F |L|).ideal`.  For `P = 𝔪_T`, `F i = [𝓓_N^i 𝔪]_T`, `S = S_T` this
is the library's `GoodAtAlong 𝔪 S T p`. -/
def GoodAt (P : MarkedIdeal n Y) (F : ℕ → MarkedIdeal n Y) (S : Set Y) (p : Y) : Prop :=
  ∃ (kS kN : ℕ) (_ : kS ≤ kN) (_ : kN ≤ n) (c : FlatChart n S p kS),
    (∀ {y : Y}, y ∈ (chartAt (ComplexModel n) p).source → chartAt (ComplexModel n) p y ∈ c.Φ.source →
      (y ∈ P.N ↔ c.Φ.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n kN)) ∧
    ∃ G : (Y → ℂ) → Prop,
      (∀ g, G g → P.ideal.mem p g) ∧
      (∀ f, P.ideal.mem p f → IsInSpanOnAt (n := n) P.N G p f) ∧
      ∀ g, G g → ∀ L : List (Fin n), NormalIdx kS L → (∀ l ∈ L, l.1 < kN) → L.length < P.d →
        IsInSpanOnAt (n := n) S ((F L.length).ideal.mem p) p (c.nd L g)

/-- **The conclusion of the invariant**: at a good point `p ∈ S` where every `F i` (`i < d`) has order `≥ d - i` along
`S`, the ideal `P.ideal` has order `≥ d` along `P.N` at `p`. -/
theorem GoodAt.orderGE {P : MarkedIdeal n Y} {F : ℕ → MarkedIdeal n Y} {S : Set Y} {p : Y}
    (hp : GoodAt P F S p) (hcoh : P.ideal.IsCoherent)
    (hD : ∀ i < P.d, OrderGE n S (F i).ideal p (P.d - i)) :
    OrderGE n P.N P.ideal p P.d := by
  obtain ⟨kS, kN, hk, -, c, hcN, G, hGmem, hGgen, hGder⟩ := hp
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh
  have hNev : ∀ᶠ y in 𝓝 p, y ∈ P.N → c.ψ y ∈ complexCoordinatePlane n kN := by
    filter_upwards [c.eventually_mem_flatDomain] with y hy hyN using (hcN hy.1 hy.2).mp hyN
  have hG : ∀ g, G g → VanishesToOrderOn n P.N p P.d g := by
    intro g hg
    refine NormalDerivativeAlong.FlatChart.vanishesToOrderOn_of_nd c hk hNev (hhol p g (hGmem g hg))
      fun L hL hLt hLlen => ?_
    exact CoefficientRestrictionTower.vanishesToOrderOn_of_isInSpanOnAt (hGder g hg L hL hLt hLlen) fun s hs =>
      hD L.length hLlen s hs
  intro f hf
  exact CoefficientRestrictionTower.vanishesToOrderOn_of_isInSpanOnAt (hGgen f hf) hG

/-- **Every point of `S` is good at the base**, for the derivative ideals along `N` (`goodAtAlong_refl`). -/
theorem goodAt_base (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {S : Set Y} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N) {p : Y} (hp : p ∈ S) :
    GoodAt 𝔪 (fun i => derivMarkedAlong 𝔪 i) S p :=
  goodAtAlong_refl 𝔪 hN h𝔞 hS hSN hp

end Invariant

/-! ### One admissible blowup -/

section Blowup

open BlowupFlatCoordinates BlowupMonomialCharts

variable {n : ℕ} {Y Z : CMfd.{u} n}

/-- **The invariant off the centre** (copy of `goodAtAlong_step_of_notMem` with stage-only hypotheses): if `π z ∉ C` and
`π z` is good, then `z` is good for the transforms (the chart and the generators pull back; `π` is a local
biholomorphism near `z`). -/
theorem goodAt_step_of_notMem (P : MarkedIdeal n Y) (F : ℕ → MarkedIdeal n Y) {S : Set Y} {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNc : IsClosed P.N) (hcohT : P.ideal.IsCoherent)
    (hDcoh : ∀ i < P.d, (F i).ideal.IsCoherent) (hSc : IsClosed S) {z : Z} (hzC : π z ∉ C)
    (hgood : GoodAt P F S (π z)) :
    GoodAt (P.geoTransform C π) (fun i => (F i).geoTransform C π) (geoStrictTransform π C S) z := by
  obtain ⟨kS, kN, hk, hkn, c, hcN, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  set NT := P.N with hNTdef
  have hN' : (P.geoTransform C π).N = geoStrictTransform π C NT := rfl
  have hoff : ∀ᶠ y in 𝓝 z, π y ∉ C := (hπ.1.1.isOpen_compl.preimage hπc).mem_nhds hzC
  have hSev : ∀ᶠ y in 𝓝 z, (y ∈ geoStrictTransform π C S ↔ π y ∈ S) := by
    filter_upwards [hoff] with y hy
    exact mem_geoStrictTransform_iff_of_notMem hπc hSc hy
  have hNev : ∀ᶠ y in 𝓝 z, (y ∈ (P.geoTransform C π).N ↔ π y ∈ NT) := by
    filter_upwards [hoff] with y hy
    rw [hN']
    exact mem_geoStrictTransform_iff_of_notMem hπc hNc hy
  -- the new coordinates `W = ψ ∘ π`
  set W : Z → ComplexModel n := fun y => c.ψ (π y) with hWdef
  have hev : ∀ᶠ y in 𝓝 z, π y ∈ BlowupFlatCoordinates.flatDomain c.Φ ∧
      (y ∈ geoStrictTransform π C S ↔ π y ∈ S) ∧
      (y ∈ (P.geoTransform C π).N ↔ π y ∈ NT) :=
    ((hπc.tendsto z).eventually c.eventually_mem_flatDomain).and (hSev.and hNev)
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hev
  have hW : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W y := fun y hy =>
    (c.mdifferentiableAt_ψ (hOsub hy).1).comp y (hπd y)
  have hflat : ∀ y ∈ O, (y ∈ geoStrictTransform π C S ↔ W y ∈ complexCoordinatePlane n kS) := fun y hy => by
    rw [(hOsub hy).2.1]; exact c.flat (hOsub hy).1.1 (hOsub hy).1.2
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
  obtain ⟨c', hc', hdom⟩ := FlatChart.exists_of_map' hO hzO hW c.ψ_self hinj hflat
  have hc'N : ∀ {y : Z}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ c'.Φ.source →
      (y ∈ (P.geoTransform C π).N ↔
        c'.Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n kN) := by
    intro y hy hyΦ
    obtain ⟨hyO, hΦy⟩ := hdom hy hyΦ
    rw [hΦy, (hOsub hyO).2.2]
    exact hcN (hOsub hyO).1.1 (hOsub hyO).1.2
  -- `π ∘ c'.inv = c.inv` near `0`
  have hWinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), W (c'.inv u) = u := by
    filter_upwards [c'.eventually_ψ_inv, c'.tendsto_inv.eventually hc'] with u hu hu'
    rw [← hu']; exact hu
  have hπinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), π (c'.inv u) = c.inv u := by
    have ht : Tendsto (fun u => π (c'.inv u)) (𝓝 (0 : ComplexModel n)) (𝓝 (π z)) :=
      (hπc.tendsto z).comp c'.tendsto_inv
    filter_upwards [hWinv, ht.eventually c.eventually_inv_ψ] with u hu hu'
    rw [← hu', show c.ψ (π (c'.inv u)) = u from hu]
  have hnd : ∀ (g : Y → ℂ) (L : List (Fin n)), c'.nd L (g ∘ π) =ᶠ[𝓝 z] fun z' => c.nd L g (π z') := by
    intro g L
    have hgerm : (fun u => (g ∘ π) (c'.inv u)) =ᶠ[𝓝 (0 : ComplexModel n)] fun u => g (c.inv u) := by
      filter_upwards [hπinv] with u hu
      simp only [Function.comp_apply, hu]
    have hiter := iterDeriv_congr_of_eventuallyEq hgerm (L.map bv)
    filter_upwards [c'.tendsto_ψ.eventually hiter, hc'] with z' h1 h2
    simp only [FlatChart.nd]
    rw [h1, h2]
  have hpb : ∀ {𝔟 : GermIdeal n Y} {g : Y → ℂ}, 𝔟.mem (π z) g → HolomorphicAt n g (π z) →
      (GermIdeal.pullback (m := n) π 𝔟).mem z (g ∘ π) := fun {𝔟} {g} hg hghol =>
    InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (π z) a ∧ s = a ∘ π) ⟨g, hg, rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) hghol)
  have hN'sub : (P.geoTransform C π).N ⊆ π ⁻¹' NT := by
    rw [hN']; exact geoStrictTransform_subset_preimage hπc hNc
  refine ⟨kS, kN, hk, hkn, c', hc'N, fun h => ∃ g, G g ∧ h = g ∘ π, ?_, ?_, ?_⟩
  · rintro h ⟨g, hg, rfl⟩
    have hgm := hGmem g hg
    exact mem_geoTransform_of_mem_pullback _ (hpb hgm (hol_of_isCoherent hcohT _ _ hgm))
  · intro f hf
    have h1 := isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem hπ P hzC hf
    refine IsInSpanOnAt.trans (fun t ht => ?_) h1
    refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ht))
    obtain ⟨a, ha, rfl⟩ := hs
    exact IsInSpanOnAt.mono (fun t ⟨g, hg, ht⟩ => ⟨g, hg, ht⟩) (isInSpanOnAt_comp hπc hπd hN'sub (hGgen a ha))
  · rintro h ⟨g, hg, rfl⟩ L hL hLt hLlen
    obtain ⟨K, s, a, hs, ha, hsum⟩ := hGder g hg L hL hLt hLlen
    refine ⟨K, fun i => s i ∘ π, fun i => a i ∘ π, fun i => ?_, fun i =>
      HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (ha i), ?_⟩
    · exact mem_geoTransform_of_mem_pullback _ (hpb (hs i) (hol_of_isCoherent (hDcoh _ hLlen) _ _ (hs i)))
    · filter_upwards [hnd g L, hSev, (hπc.tendsto z).eventually hsum] with z' h1 h2 h3 hz'
      rw [h1]
      exact h3 (h2.mp hz')

/-- **The invariant over the centre** (copy of `goodAtAlong_step_of_mem` with stage-only hypotheses): if `π z ∈ C`,
`z ∈ S'` and `π z` is good, then `z` is good for the transforms (a monomial chart over nested product-form coordinates
for `C ⊆ S ⊆ N`; new generators `h'` with `g ∘ π = W_j^d h'` on `N'`). -/
theorem goodAt_step_of_mem (P : MarkedIdeal n Y) (F : ℕ → MarkedIdeal n Y) {S : Set Y} {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hNT : IsClosedSubmanifold n P.N) (hcohT : P.ideal.IsCoherent)
    (hDN : ∀ i < P.d, (F i).N = P.N) (hDd : ∀ i < P.d, (F i).d = P.d - i)
    (hDcoh : ∀ i < P.d, (F i).ideal.IsCoherent)
    (hCadm : P.IsAdmissibleCentre C) (hDadm : ∀ i < P.d, (F i).IsAdmissibleCentre C)
    (hSc : IsClosed S) (hSN : S ⊆ P.N) (hCS : C ⊆ S) {z : Z}
    (hz : z ∈ geoStrictTransform π C S) (hzC : π z ∈ C) (hgood : GoodAt P F S (π z)) :
    GoodAt (P.geoTransform C π) (fun i => (F i).geoTransform C π) (geoStrictTransform π C S) z := by
  obtain ⟨kS, kN, hk, hkn, c, hcN, G, hGmem, hGgen, hGder⟩ := hgood
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hπd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcohT
  set NT := P.N with hNTdef
  have hN' : (P.geoTransform C π).N = geoStrictTransform π C NT := rfl
  -- nested product-form coordinates for `C ⊆ S_T ⊆ N_T` at `π z`
  obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
  have hSreg : RegularAtDim (n := n) (S) (π z) kS :=
    ⟨le_trans hk hkn, hCS hzC, c.Φ, c.src, c.zero, c.flat⟩
  have hkCk : kC ≤ kS := le_of_regularAtDim_subset hkC hSreg hCS
  obtain ⟨c'', hc''C, hc''N, hc''nd⟩ :=
    NormalDerivativeAlong.FlatChart.exists_nested_pair c hkCk (le_trans hk hkn) hk hkC hCS hcN
  -- one monomial chart for both strict transforms
  obtain ⟨j, hj, O, hO, hzO, W, hWs, hWmem, hWeq, hℓ, hiffS, hiffN⟩ :=
    exists_local_geoStrictTransform_pair hπ c''.src hc''C c''.flat hc''N (mem_flatDomain_self c''.Φ)
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ c''.src hc''C hj
  have hWeq' : ∀ z' ∈ O, c''.ψ (π z') = monomial kC j (W z') := fun z' hz' => (hWeq z' hz').2.symm
  obtain ⟨hjk, hWz⟩ := (hiffS z hzO).mp hz
  have hjN : j.1 < kN := lt_of_lt_of_le hjk hk
  have hWzN : W z ∈ complexCoordinatePlane n kN := plane_mono hk hWz
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hc''C (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  -- the new flat chart `W - W z`
  have hW' : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun y => W y - W z) y :=
    fun y hy => ((hWs y hy).mdifferentiableAt (by simp)).sub mdifferentiableAt_const
  have hflat' : ∀ y ∈ O, (y ∈ geoStrictTransform π C S ↔ W y - W z ∈ complexCoordinatePlane n kS) := by
    intro y hy
    rw [sub_mem_plane_iff hWz]
    exact (hiffS y hy).trans ⟨fun h => h.2, fun h => ⟨hjk, h⟩⟩
  have hflatN' : ∀ y ∈ O, (y ∈ (P.geoTransform C π).N ↔
      W y - W z ∈ complexCoordinatePlane n kN) := by
    intro y hy
    rw [sub_mem_plane_iff hWzN, hN']
    exact (hiffN y hy).trans ⟨fun h => h.2, fun h => ⟨hjN, h⟩⟩
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
  obtain ⟨c', hc', hdom⟩ := FlatChart.exists_of_map' hO hzO hW' (sub_self _) hinj hflat'
  have hc'N : ∀ {y : Z}, y ∈ (chartAt (ComplexModel n) z).source → chartAt (ComplexModel n) z y ∈ c'.Φ.source →
      (y ∈ (P.geoTransform C π).N ↔
        c'.Φ.toFun (chartAt (ComplexModel n) z y) ∈ complexCoordinatePlane n kN) := by
    intro y hy hyΦ
    obtain ⟨hyO, hΦy⟩ := hdom hy hyΦ
    rw [hΦy]; exact hflatN' y hyO
  have hN'ev : ∀ᶠ y in 𝓝 z, (y ∈ (P.geoTransform C π).N ↔
      c'.ψ y ∈ complexCoordinatePlane n kN) := by
    filter_upwards [c'.eventually_mem_flatDomain] with y hy using hc'N hy.1 hy.2
  -- the local equation `W_j` of the exceptional divisor
  have hl : IsLocalEquation hπ O (fun p => W p j) :=
    GlueingTrivialAction.isLocalEquation_monomial hπ c''.src hc''C hj hO hWs hWeq
  -- `W_j` vanishes on no relatively open subset of a strict transform
  have hnon : ∀ (A : Set Y) (μ : ℕ), ∀ V : Set Z, IsOpen V → V ⊆ O → (V ∩ geoStrictTransform π C A).Nonempty →
      ∃ y ∈ V ∩ geoStrictTransform π C A, W y j ^ μ ≠ 0 := by
    rintro A μ V hV hVO ⟨y₀, hy₀V, hy₀S⟩
    obtain ⟨y₁, hy₁V, hy₁S, hy₁C⟩ := mem_closure_iff.mp hy₀S V hV hy₀V
    exact ⟨y₁, ⟨hy₁V, subset_closure ⟨hy₁S, hy₁C⟩⟩,
      pow_ne_zero _ fun h => hy₁C ((hCu y₁ (hVO hy₁V)).mpr h)⟩
  have hd : P.d = P.d := rfl
  have hzN : z ∈ geoStrictTransform π C NT := geoStrictTransform_mono' π C hSN hz
  refine ⟨kS, kN, hk, hkn, c', hc'N, fun h' => ∃ g, G g ∧ HolomorphicAt n h' z ∧
    (P.geoTransform C π).ideal.mem z h' ∧
    ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C NT → g (π y) = W y j ^ P.d * h' y,
    fun h' ⟨_, _, _, hm, _⟩ => hm, ?_, ?_⟩
  · -- the new generators generate the transform along `N'`
    intro f hf
    have hfhol : HolomorphicAt n f z := by
      have h := hf
      rw [geoTransform_ideal] at h
      exact h.1
    have h1 := isInSpanOnAt_pow_mul_of_mem_geoTransform hπ P hl hzO hf
    rw [hd] at h1
    have hspan : IsInSpanOnAt (n := n) (geoStrictTransform π C NT)
        (fun t => ∃ h', (∃ g, G g ∧ HolomorphicAt n h' z ∧
          (P.geoTransform C π).ideal.mem z h' ∧
          ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C NT → g (π y) = W y j ^ P.d * h' y) ∧
          t = fun y => W y j ^ P.d * h' y) z (fun y => W y j ^ P.d * f y) := by
      refine IsInSpanOnAt.trans (fun t ht => ?_) h1
      refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ht))
      obtain ⟨a, ha, rfl⟩ := hs
      refine IsInSpanOnAt.trans (fun t' ht' => ?_)
        (isInSpanOnAt_comp hπc hπd (geoStrictTransform_subset_preimage hπc hNT.1) (hGgen a ha))
      obtain ⟨g, hg, rfl⟩ := ht'
      obtain ⟨h', hh'hol, hh'mem, hrel⟩ :=
        exists_mem_geoTransform_eq_pow_mul hπ P hNT hcohT hCadm hl hzO hzN (hGmem g hg)
      rw [hd] at hrel
      refine ⟨1, fun _ => fun y => W y j ^ P.d * h' y, fun _ _ => 1,
        fun _ => ⟨h', ⟨g, hg, hh'hol, hh'mem, hrel⟩, rfl⟩, fun _ => holomorphicAt_const 1, ?_⟩
      filter_upwards [hrel] with y hy hyN
      simp [hy hyN]
    obtain ⟨K, t, b, ht, hb, hsum⟩ := hspan
    choose h' hh' htdef using ht
    refine ⟨K, h', b, fun i => hh' i, hb, ?_⟩
    exact RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hO (hnon NT P.d) hzO
      (F := f) (G := fun y => ∑ i, b i y * h' i y) hfhol
      (HolomorphicAt.sum _ fun i _ => (hb i).mul (hh' i).choose_spec.2.1) (by
        filter_upwards [hsum] with y hy hyN
        rw [hy hyN, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [htdef i]; ring)
  · -- the derivatives
    rintro h' ⟨g, hg, hh', -, hrel⟩ L hL hLt hLlen
    have hgp : HolomorphicAt n g (π z) := hhol _ _ (hGmem g hg)
    have hLj : ∀ l ∈ L, l ≠ j ∧ kC ≤ l.1 ∧ l.1 < kN := fun l hl' => by
      have h1 := hL l hl'
      have h2 := hLt l hl'
      exact ⟨fun h => by rw [h] at h1; omega, by omega, h2⟩
    have hrel' : ∀ᶠ y in 𝓝 z, y ∈ (P.geoTransform C π).N →
        g (π y) = W y j ^ P.d * h' y := hrel
    have hid := nd_monomial_identity_along hπc c'' c' hO hzO hWeq' hc' hN'ev hgp hh' hrel' L hLj
    have hnd := (hπc.tendsto z).eventually (hc''nd L hL g hgp)
    obtain ⟨K, s, aa, hs, haa, hsum⟩ := hGder g hg L hL hLt hLlen
    have hdL : L.length ≤ P.d := hLlen.le
    have h𝔫N : (F L.length).N = NT := hDN _ hLlen
    have h𝔫d : (F L.length).d = P.d - L.length := hDd _ hLlen
    have hzN𝔫 : z ∈ geoStrictTransform π C (F L.length).N := by
      rw [h𝔫N]; exact hzN
    have hex : ∀ i, ∃ s' : Z → ℂ, HolomorphicAt n s' z ∧
        ((F L.length).geoTransform C π).ideal.mem z s' ∧
        ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C (F L.length).N →
          s i (π y) = W y j ^ (F L.length).d * s' y := fun i =>
      exists_mem_geoTransform_eq_pow_mul hπ _ (h𝔫N ▸ hNT) (hDcoh _ hLlen) (hDadm _ hLlen) hl hzO hzN𝔫 (hs i)
    choose s' hs'hol hs'mem hs'eq using hex
    have hsub : ∀ᶠ z' in 𝓝 z, z' ∈ geoStrictTransform π C S → π z' ∈ S :=
      Eventually.of_forall fun z' hz' => geoStrictTransform_subset_preimage hπc hSc hz'
    have hmul : ∀ᶠ z' in 𝓝 z, z' ∈ geoStrictTransform π C (S) →
        W z' j ^ P.d * c'.nd L h' z' = W z' j ^ P.d * ∑ i, (aa i ∘ π) z' * s' i z' := by
      filter_upwards [hid, hnd, (hπc.tendsto z).eventually hsum, eventually_all.mpr hs'eq, hsub] with
        z' h1 h2 h3 h4 h5 hz'
      have hz'N : z' ∈ geoStrictTransform π C NT := geoStrictTransform_mono' π C hSN hz'
      rw [h1 (by rw [hN']; exact hz'N), h2, h3 (h5 hz'), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4i : s i (π z') = W z' j ^ (P.d - L.length) * s' i z' := by
        rw [← h𝔫d]; exact h4 i (by rw [h𝔫N]; exact hz'N)
      have e : W z' j ^ P.d = W z' j ^ L.length * W z' j ^ (P.d - L.length) := by
        rw [← pow_add, Nat.add_sub_cancel' hdL]
      rw [h4i, Function.comp_apply, e]
      ring
    have hcan := RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hO
      (hnon (S) P.d) hzO
      (CoefficientRestrictionTower.FlatChart.holomorphicAt_nd c' hh' L)
      (HolomorphicAt.sum _ fun i _ =>
        (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i)).mul (hs'hol i)) hmul
    exact ⟨K, s', fun i => aa i ∘ π, hs'mem,
      fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hπd) (haa i), hcan⟩

end Blowup

/-! ### Pullback along a holomorphic submersion -/

section Pullback

open HironakaSmoothSubmersionAdaptedProductCoordinates BlowupFlatCoordinates

/-- Restricted spans pull back along a holomorphic map between manifolds of different dimensions. -/
theorem isInSpanOnAt_comp_map {n m : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} m} {f : Y' → Y} (hfc : Continuous f)
    (hfd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w) {A : Set Y} {A' : Set Y'}
    (hA : A' ⊆ f ⁻¹' A) {T : (Y → ℂ) → Prop} {z : Y'} {a : Y → ℂ} (ha : IsInSpanOnAt (n := n) A T (f z) a) :
    IsInSpanOnAt (n := m) A' (fun t => ∃ s, T s ∧ t = s ∘ f) z (a ∘ f) := by
  obtain ⟨K, s, c, hs, hc, hsum⟩ := ha
  refine ⟨K, fun i => s i ∘ f, fun i => c i ∘ f, fun i => ⟨s i, hs i, rfl⟩,
    fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hfd) (hc i), ?_⟩
  filter_upwards [(hfc.tendsto z).eventually hsum] with y hy hyA
  exact hy (hA hyA)

/-- The pullback of a germ of `𝔟` lies in the pullback ideal. -/
theorem comp_mem_pullback {n m : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} m} {f : Y' → Y}
    (hfd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w) {𝔟 : GermIdeal n Y} {z : Y'}
    {g : Y → ℂ} (hg : 𝔟.mem (f z) g) (hghol : HolomorphicAt n g (f z)) :
    (GermIdeal.pullback (m := m) f 𝔟).mem z (g ∘ f) :=
  InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f z) a ∧ s = a ∘ f) ⟨g, hg, rfl⟩
    (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hfd) hghol)

/-- **Iterated directional derivatives commute with a continuous linear substitution** between two spaces (the
two-space form of `HolomorphicTaylorTail.iterDeriv_comp_clm`). -/
theorem iterDeriv_comp_clm' {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {G : E' → ℂ} {U : Set E'} (hG : DifferentiableOn ℂ G U) (hU : IsOpen U) (pr : E →L[ℂ] E') :
    ∀ (L : List E) (z : E), pr z ∈ U → iterDeriv L (fun u => G (pr u)) z = iterDeriv (L.map pr) G (pr z)
  | [], _, _ => rfl
  | v :: L, z, hz => by
    have hopen : IsOpen (pr ⁻¹' U) := hU.preimage pr.continuous
    have heq : iterDeriv L (fun u => G (pr u)) =ᶠ[𝓝 z] fun u => iterDeriv (L.map pr) G (pr u) :=
      eventually_of_mem (hopen.mem_nhds hz) fun u hu => iterDeriv_comp_clm' hG hU pr L u hu
    have hd : DifferentiableAt ℂ (iterDeriv (L.map pr) G) (pr z) :=
      (differentiableOn_iterDeriv hG hU _).differentiableAt (hU.mem_nhds hz)
    have h2 : HasFDerivAt (fun u => iterDeriv (L.map pr) G (pr u))
        ((fderiv ℂ (iterDeriv (L.map pr) G) (pr z)).comp pr) z :=
      hd.hasFDerivAt.comp z pr.hasFDerivAt
    simp only [iterDeriv_cons, List.map_cons, dirDeriv]
    rw [heq.fderiv_eq, h2.fderiv]
    rfl

/-- The target projection of the adapted product coordinates, as a continuous linear map. -/
def targetProj (n r : ℕ) : ComplexModel (n + r) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel n)).comp
    ((fibreFirstSplit n r : ComplexModel (n + r) ≃L[ℂ] (ComplexModel r × ComplexModel n)) :
      ComplexModel (n + r) →L[ℂ] (ComplexModel r × ComplexModel n))

theorem targetProj_apply (n r : ℕ) (w : ComplexModel (n + r)) : targetProj n r w = adaptedTargetProjection n r w :=
  rfl

/-- The coordinate direction of the adapted coordinates lifting the target direction `j`. -/
def liftDir (n r : ℕ) (j : Fin n) : Fin (n + r) := rotateBlocks n r (Fin.castAdd r j)

theorem liftDir_val (n r : ℕ) (j : Fin n) : (liftDir n r j).1 = r + j.1 := rotateBlocks_target n r j

theorem targetProj_bv (n r : ℕ) (j : Fin n) : targetProj n r (bv (liftDir n r j)) = bv j := by
  ext j'
  rw [targetProj_apply, adaptedTargetProjection_apply]
  have hinj : rotateBlocks n r (Fin.castAdd r j') = liftDir n r j ↔ j' = j := by
    constructor
    · intro h
      have h1 := congrArg Fin.val h
      rw [liftDir_val, rotateBlocks_target] at h1
      exact Fin.ext (by omega)
    · rintro rfl; rfl
  by_cases h : j' = j
  · subst h; simp [bv, liftDir]
  · have h' : rotateBlocks n r (Fin.castAdd r j') ≠ liftDir n r j := fun h'' => h (hinj.mp h'')
    simp [bv, h, h']

/-- Lists of directions in `[r + a, r + b)` with `b ≤ n` are lifts of lists of target directions in `[a, b)`. -/
theorem exists_lift_list (n r a b : ℕ) (hb : b ≤ n) :
    ∀ L' : List (Fin (n + r)), NormalIdx (r + a) L' → (∀ l ∈ L', l.1 < r + b) →
      ∃ L : List (Fin n), L' = L.map (liftDir n r) ∧ NormalIdx a L ∧ ∀ l ∈ L, l.1 < b
  | [], _, _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | l' :: L', hL, hlt => by
    obtain ⟨L, hL', hLa, hLb⟩ := exists_lift_list n r a b hb L' (fun l hl => hL l (List.mem_cons_of_mem _ hl))
      (fun l hl => hlt l (List.mem_cons_of_mem _ hl))
    have h1 := hL l' List.mem_cons_self
    have h2 := hlt l' List.mem_cons_self
    let j : Fin n := ⟨l'.1 - r, by omega⟩
    have hj : liftDir n r j = l' := Fin.ext (by rw [liftDir_val]; simp only [j]; omega)
    refine ⟨j :: L, by rw [List.map_cons, hj, hL'], fun l hl => ?_, fun l hl => ?_⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · simp only [j]; omega
      · exact hLa l hl
    · rcases List.mem_cons.mp hl with rfl | hl
      · simp only [j]; omega
      · exact hLb l hl

variable {n r : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} (n + r)} {f : Y' → Y}

/-- **A flat chart pulled back along a submersion**: in the adapted coordinates at `y` (fibre coordinates first),
`f⁻¹S` is the plane `ℂ^{r + k} × 0`. -/
def pullbackChart
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f) {S : Set Y} {y : Y'} {k : ℕ}
    (c : FlatChart n S (f y) k) : FlatChart (n + r) (f ⁻¹' S) y (r + k) where
  Φ := adaptedCoordinates (hf.isSubmersionAt y) c.Φ c.zero
  src := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) c.Φ c.zero).1
  zero := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) c.Φ c.zero).2.1
  flat := fun hz hzΦ => adaptedCoordinates_whole_centre (hf.isSubmersionAt y) c.Φ c.zero S k
    (fun _ hw => c.flat hw.1 hw.2) _ ⟨hz, hzΦ⟩

theorem pullbackChart_flat_of
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f) {S : Set Y} {y : Y'} {k : ℕ}
    (c : FlatChart n S (f y) k) {A : Set Y} {kA : ℕ}
    (hA : ∀ {x : Y}, x ∈ (chartAt (ComplexModel n) (f y)).source → chartAt (ComplexModel n) (f y) x ∈ c.Φ.source →
      (x ∈ A ↔ c.Φ.toFun (chartAt (ComplexModel n) (f y) x) ∈ complexCoordinatePlane n kA))
    {z : Y'} (hz : z ∈ (chartAt (ComplexModel (n + r)) y).source)
    (hzΦ : chartAt (ComplexModel (n + r)) y z ∈ (pullbackChart hf c).Φ.source) :
    (z ∈ f ⁻¹' A ↔ (pullbackChart hf c).Φ.toFun (chartAt (ComplexModel (n + r)) y z) ∈
      complexCoordinatePlane (n + r) (r + kA)) :=
  adaptedCoordinates_whole_centre (hf.isSubmersionAt y) c.Φ c.zero A kA (fun _ hw => hA hw.1 hw.2) _ ⟨hz, hzΦ⟩

/-- **The adapted coordinates read the target coordinates**: `targetProj (ψ' z) = ψ (f z)` on the flat domain. -/
theorem targetProj_pullbackChart_ψ
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f) {S : Set Y} {y : Y'} {k : ℕ}
    (c : FlatChart n S (f y) k) {z : Y'} (hz : z ∈ flatDomain (pullbackChart hf c).Φ) :
    f z ∈ flatDomain c.Φ ∧ targetProj n r ((pullbackChart hf c).ψ z) = c.ψ (f z) := by
  obtain ⟨-, -, hd⟩ := adaptedCoordinates_dictionary (hf.isSubmersionAt y) c.Φ c.zero
  obtain ⟨h1, h2⟩ := hd z hz
  refine ⟨h1, ?_⟩
  ext j
  rw [targetProj_apply, adaptedTargetProjection_apply]
  exact h2 j

/-- **Normal derivatives pull back along a submersion**: `∂^{L'}(g ∘ f) = (∂^L g) ∘ f` near `y`, for `L'` the lift of
`L` to the adapted coordinates. -/
theorem nd_pullbackChart
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f) {S : Set Y} {y : Y'} {k : ℕ}
    (c : FlatChart n S (f y) k) {g : Y → ℂ} (hg : HolomorphicAt n g (f y)) (L : List (Fin n)) :
    (pullbackChart hf c).nd (L.map (liftDir n r)) (g ∘ f) =ᶠ[𝓝 y] fun z => c.nd L g (f z) := by
  set c' := pullbackChart hf c with hc'
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (c.eventually_differentiableAt_comp_inv hg)
  have hGU : DifferentiableOn ℂ (fun u => g (c.inv u)) (ball 0 ρ) := fun z hz => (hball z hz).differentiableWithinAt
  set V : Set (ComplexModel (n + r)) := c'.Φ.target ∩ targetProj n r ⁻¹' ball 0 ρ with hV
  have hVo : IsOpen V := c'.Φ.isOpen_target.inter (isOpen_ball.preimage (targetProj n r).continuous)
  have hV0 : (0 : ComplexModel (n + r)) ∈ V := ⟨c'.zero_mem_target, by simp [hρ]⟩
  -- on `V`, `g ∘ f ∘ inv' = (g ∘ inv) ∘ targetProj`
  have hrel : ∀ w ∈ V, g (f (c'.inv w)) = g (c.inv (targetProj n r w)) := by
    intro w hw
    obtain ⟨hz, hzw⟩ := flatInverse_mem c'.Φ hw.1 c'.src
    obtain ⟨h1, h2⟩ := targetProj_pullbackChart_ψ hf c hz
    have hψ : c'.ψ (c'.inv w) = w := hzw
    have h2' : targetProj n r (c'.ψ (c'.inv w)) = c.ψ (f (c'.inv w)) := h2
    rw [hψ] at h2'
    rw [h2']
    show g (f (c'.inv w)) = g ((chartAt (ComplexModel n) (f y)).symm (c.Φ.invFun (c.ψ (f (c'.inv w)))))
    exact congrArg g (flatInverse_flat c.Φ h1).symm
  filter_upwards [c'.eventually_mem_flatDomain, c'.tendsto_ψ.eventually (hVo.mem_nhds hV0)] with z hz hzV
  obtain ⟨-, hproj⟩ := targetProj_pullbackChart_ψ hf c hz
  have hloc : (fun w => (g ∘ f) (c'.inv w)) =ᶠ[𝓝 (c'.ψ z)] fun w => g (c.inv (targetProj n r w)) :=
    eventually_of_mem (hVo.mem_nhds hzV) fun w hw => hrel w hw
  have h1 := (NormalDerivativeMonomial.iterDeriv_congr_of_eventuallyEq hloc
    ((L.map (liftDir n r)).map bv)).self_of_nhds
  have h2 := iterDeriv_comp_clm' hGU isOpen_ball (targetProj n r) ((L.map (liftDir n r)).map bv) (c'.ψ z) hzV.2
  have hmap : ((L.map (liftDir n r)).map bv).map (targetProj n r) = L.map bv := by
    simp only [List.map_map]
    exact List.map_congr_left fun j _ => targetProj_bv n r j
  simp only [FlatChart.nd]
  rw [h1, h2, hmap, hproj]

/-- **The invariant pulls back along a holomorphic submersion** `f : Y' → Y` (`dim Y' = n + r`): for `P'`, `F'` the
pullbacks of `P`, `F` (any boundaries), every point of `f⁻¹S` over a good point is good. -/
theorem goodAt_pullback_submersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    {P : MarkedIdeal n Y} {F : ℕ → MarkedIdeal n Y} {S : Set Y} {P' : MarkedIdeal (n + r) Y'}
    {F' : ℕ → MarkedIdeal (n + r) Y'} (hPN : P'.N = f ⁻¹' P.N)
    (hPI : P'.ideal = GermIdeal.pullback (m := n + r) f P.ideal) (hPd : P'.d = P.d)
    (hFI : ∀ i < P.d, (F' i).ideal = GermIdeal.pullback (m := n + r) f (F i).ideal)
    (hcoh : P.ideal.IsCoherent) (hFcoh : ∀ i < P.d, (F i).ideal.IsCoherent)
    {y : Y'} (hgood : GoodAt P F S (f y)) : GoodAt P' F' (f ⁻¹' S) y := by
  obtain ⟨kS, kN, hk, hkn, c, hcN, G, hGmem, hGgen, hGder⟩ := hgood
  have hfc : Continuous f := hf.contMDiff.continuous
  have hfd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) f w :=
    fun w => (hf.contMDiff w).mdifferentiableAt (by simp)
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh
  have hpb : ∀ {𝔟 : GermIdeal n Y} {z : Y'} {g : Y → ℂ}, 𝔟.mem (f z) g → HolomorphicAt n g (f z) →
      (GermIdeal.pullback (m := n + r) f 𝔟).mem z (g ∘ f) := fun {𝔟} {z} {g} hg hghol =>
    InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f z) a ∧ s = a ∘ f) ⟨g, hg, rfl⟩
      (HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hfd) hghol)
  refine ⟨r + kS, r + kN, by omega, by omega, pullbackChart hf c, ?_, fun h => ∃ g, G g ∧ h = g ∘ f, ?_, ?_, ?_⟩
  · intro z hz hzΦ
    rw [hPN]
    exact pullbackChart_flat_of hf c hcN hz hzΦ
  · rintro h ⟨g, hg, rfl⟩
    rw [hPI]
    exact hpb (hGmem g hg) (hhol _ _ (hGmem g hg))
  · intro h hh
    rw [hPI] at hh
    rw [hPN]
    refine IsInSpanOnAt.trans (fun s hs => ?_) (IsInSpanAt.restrict
      (show IsInSpanAt (n := n + r) (fun s => ∃ a, P.ideal.mem (f y) a ∧ s = a ∘ f) y h from hh))
    obtain ⟨a, ha, rfl⟩ := hs
    exact IsInSpanOnAt.mono (fun t ⟨g, hg, ht⟩ => ⟨g, hg, ht⟩)
      (isInSpanOnAt_comp_map hfc hfd (subset_refl _) (hGgen a ha))
  · rintro h ⟨g, hg, rfl⟩ L' hL' hLt' hLlen'
    obtain ⟨L, rfl, hL, hLt⟩ := exists_lift_list n r kS kN hkn L' hL' hLt'
    rw [List.length_map] at hLlen' ⊢
    rw [hPd] at hLlen'
    have h1 := isInSpanOnAt_comp_map (A' := f ⁻¹' S) hfc hfd (subset_refl _) (hGder g hg L hL hLt hLlen')
    have h2 : IsInSpanOnAt (n := n + r) (f ⁻¹' S) ((F' L.length).ideal.mem y) y (fun z => c.nd L g (f z)) := by
      refine IsInSpanOnAt.mono (fun t ⟨s, hs, ht⟩ => ?_) h1
      rw [ht, hFI _ hLlen']
      exact hpb hs (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hFcoh _ hLlen') _ _ hs)
    obtain ⟨K, s, a, hs, ha, hsum⟩ := h2
    refine ⟨K, s, a, hs, ha, ?_⟩
    filter_upwards [hsum, nd_pullbackChart hf c (hhol _ _ (hGmem g hg)) L] with z hz hz' hzS
    rw [hz', hz hzS]

end Pullback

end

end Hironaka.HironakaG8ContactGood
