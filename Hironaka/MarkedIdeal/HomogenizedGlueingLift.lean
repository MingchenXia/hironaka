import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.Coherence.VanishingIdealCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Glueing Lemma along multiple test blow-ups: the lifts of the glueing biholomorphism

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:coordinate-change-trivial`, `mc:glueing-trivial`
(`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, Lemma `le:homo` (4) and its proof, in the analytic
adaptation of design note D7 (`φ_v` the inclusion of an open set `U`, `φ_u = φ` a biholomorphism `U ≅ U'`).

## The base case

* `eventually_mdifferentiableAt_W`, `eventually_trivialAt_coordMap`: **a coordinate change
  `φ(p) = e⁻¹Ψ(W(p) + h(p)eᵢ)` acts trivially modulo every coherent ideal `J ∋ h` at the zeros of `J` near `x`**:
  `g ∘ φ - g = h · T(W, h)` (Taylor's formula with holomorphic remainder along `eᵢ`).

## Glueing data acting trivially

* `extendMap Φ` (a map between open sets extended by the identity), `trivialAt_congr`, `trivialAt_mono`, `zeroSet_mono`,
  `cosupport_one_subset_zeroSet`;
* `glueIdeal 𝔞 μ = 𝓓^{μ-1}(𝓗(𝔞)) ⊇ T(𝔞)` and `exists_glueingData_trivial`: the glueing maps `φ`, `ψ` act trivially modulo
  `𝓓^{μ-1}(𝓗(𝔞))` at its zeros in `W`.

## One step

* `preimage_lift_geoStrictTransform`, `pullback_lift_geoTransform`: under the lift `Φ₁` of `Φ : A ≅ B` along a blowup,
  strict transforms and transforms correspond if they do under `Φ`.

## The lifts along a multiple test blow-up (`le:homo` (4))

* `IsGlueingLift G T Φ`: `Φ` maps the preimage of `U` onto that of `U'` in the last stage of `T`, lifts `φ`, acts
  trivially (as does `Φ⁻¹`) modulo the transformed `𝓓^{μ-1}(𝓗(𝔞))` at its zeros, identifies the restrictions of the
  transform of `(𝓗(𝔞), μ)` and the strict transforms of `V(u)` and `V(v)`;
* `exists_isGlueingLift`: **it exists along every multiple test blow-up of `(𝓗(𝔞), μ)`** (induction: the centre lies in
  the zeros of the transformed tangent ideal, `Φ_T` fixes them, so the centres correspond and `Φ_T` lifts
  (`BlowupBiholomorphismLift.exists_lift`); the lift acts trivially by `GlueingTrivialAction.trivialAt_lift`);
* `IsGlueingLift.apply_eq_of_mem_cosupp`: the lifts fix the cosupports; `glueing_lemma_lift`: the package.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers HomogenizedIdeal HomogenizedGlueing HomogenizedGlueingTower GlueingTrivialAction
  HolomorphicTaylorTail

noncomputable section

/-! ### The base case: coordinate changes act trivially -/

section Base

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coordinates `W` of a coordinate change are holomorphic near `x`. -/
theorem eventually_mdifferentiableAt_W {x : M} (d : CoordinateChange (n := n) x) :
    ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d.W p := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  filter_upwards [e.val.open_source.mem_nhds hxs,
    (e.val.continuousAt hxs).preimage_mem_nhds (d.isOpen.mem_nhds d.mem)] with p hp hpN
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val p :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hp
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (d.W ∘ e.val.symm) (e.val p) :=
    ((d.differentiableOn _ hpN).differentiableAt (d.isOpen.mem_nhds hpN)).mdifferentiableAt
  refine (h2.comp p h1).congr_of_eventuallyEq ?_
  filter_upwards [e.val.open_source.mem_nhds hp] with q hq
  simp [e.val.left_inv hq]

/-- **A coordinate change acts trivially modulo every coherent ideal containing its `h`, at the zeros of the ideal
near `x`** (Włodarczyk, proof of `le:homo` (4): `φ_u^*(f) - φ_v^*(f) ∈ (h)`). -/
theorem eventually_trivialAt_coordMap {x : M} (d : CoordinateChange (n := n) x) {J : GermIdeal n M}
    (hJ : J.IsCoherent) (hh : J.mem x d.h) :
    ∀ᶠ y in 𝓝 x, y ∈ zeroSet J → TrivialAt d.coordMap J y := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hWc : ContinuousAt d.W x := d.continuousAt_W
  filter_upwards [eventually_mem hJ hh, eventually_coordMap_eq_self d,
    (eventually_mdifferentiableAt_coordMap d).eventually_nhds, d.left_inv.eventually_nhds,
    e.val.open_source.mem_nhds hxs, hWc.eventually d.differentiableAt.eventually_nhds,
    DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt d.holomorphicAt,
    (eventually_mdifferentiableAt_W d).eventually_nhds]
    with y hJy hfix hmd hΨW hys hΨd hhh hWdy hyJ
  have hy0 : d.h y = 0 := hyJ _ hJy
  refine ⟨hfix hy0, hmd, fun g hg => ?_⟩
  set F : ComplexModel n → ℂ := fun w => g (e.val.symm (d.Ψ w)) with hFdef
  have hΨy : d.Ψ (d.W y) = e.val y := hΨW.self_of_nhds
  have hFd : ∀ᶠ w in 𝓝 (d.W y), DifferentiableAt ℂ F w := by
    have hge := eventually_differentiableAt_comp_symm e hys hg
    have hΨc : Tendsto d.Ψ (𝓝 (d.W y)) (𝓝 (e.val y)) := by
      rw [← hΨy]; exact hΨd.self_of_nhds.continuousAt
    filter_upwards [hΨd, hΨc.eventually hge] with w h1 h2
    exact h2.comp w h1
  obtain ⟨T, hT, hTeq⟩ := exists_taylor_tail hFd (EuclideanSpace.single d.i (1 : ℂ)) 1
  have hγ : Tendsto (fun p => (d.W p, d.h p)) (𝓝 y) (𝓝 (d.W y, (0 : ℂ))) := by
    rw [← hy0]
    exact hWdy.self_of_nhds.continuousAt.prodMk_nhds hhh.self_of_nhds.continuousAt
  have hTγ : HolomorphicAt n (fun p => T (d.W p, d.h p)) y := by
    filter_upwards [hWdy, hhh, hγ.eventually hT] with p h1 h2 h3
    exact h3.mdifferentiableAt.comp p (h1.prodMk_space h2)
  have heq : (fun p => T (d.W p, d.h p) * d.h p) =ᶠ[𝓝 y] fun p => g (d.coordMap p) - g p := by
    filter_upwards [hγ.eventually hTeq, hΨW, e.val.open_source.mem_nhds hys] with p hp1 hp2 hp3
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul, List.replicate_zero, iterDeriv_nil, pow_zero, mul_one, pow_one] at hp1
    have hgp : g p = F (d.W p) := by
      simp only [hFdef, hp2]
      exact congrArg g ((complexChartAt (n := n) x).val.left_inv hp3).symm
    have hgφ : g (d.coordMap p) = F (d.W p + d.h p • EuclideanSpace.single d.i 1) := rfl
    rw [hgφ, hgp, hp1]
    ring
  exact HomogenizedIdeal.mem_congr hJ (mul_mem hJ hTγ hJy) heq

end Base

/-! ### Maps between open sets, extended by the identity -/

section Extend

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

open scoped Classical in
/-- A map between open subsets of `Y`, extended by the identity to a map `Y → Y`. -/
def extendMap {A B : Opens Y} (Φ : A → B) : Y → Y := fun y => if h : y ∈ A then (Φ ⟨y, h⟩ : Y) else y

theorem extendMap_of_mem {A B : Opens Y} (Φ : A → B) {y : Y} (h : y ∈ A) : extendMap Φ y = Φ ⟨y, h⟩ := by
  classical
  simp only [extendMap, dif_pos h]

theorem extendMap_val {A B : Opens Y} (Φ : A → B) (y : A) : extendMap Φ y = Φ y :=
  extendMap_of_mem Φ y.2

theorem contMDiffAt_extendMap {A B : Opens Y} {Φ : A → B}
    (hΦ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ) (y : A) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (extendMap Φ) y := by
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun p : A => extendMap Φ p) y := by
    have : (fun p : A => extendMap Φ p) = Subtype.val ∘ Φ := funext fun p => extendMap_val Φ p
    rw [this]
    exact (contMDiff_subtype_val.comp hΦ) y
  exact contMDiffAt_subtype_iff.mp h1

theorem eventually_mdifferentiableAt_extendMap {A B : Opens Y} {Φ : A → B}
    (hΦ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ) (y : A) :
    ∀ᶠ p in 𝓝 (y : Y), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (extendMap Φ) p := by
  filter_upwards [A.isOpen.mem_nhds y.2] with p hp
  exact (contMDiffAt_extendMap hΦ ⟨p, hp⟩).mdifferentiableAt (by simp)

/-- Trivial action depends only on the germ of the map. -/
theorem trivialAt_congr {f g : Y → Y} {J : GermIdeal n Y} (hJ : J.IsCoherent) {y : Y} (h : TrivialAt f J y)
    (hfg : f =ᶠ[𝓝 y] g) : TrivialAt g J y := by
  refine ⟨hfg.self_of_nhds.symm.trans h.apply_eq, ?_, fun g' hg' => ?_⟩
  · filter_upwards [h.mdifferentiableAt, hfg.eventually_nhds] with p hp hfgp
    exact hp.congr_of_eventuallyEq (show f =ᶠ[𝓝 p] g from hfgp).symm
  · refine HomogenizedIdeal.mem_congr hJ (h.sub_mem g' hg') ?_
    filter_upwards [hfg] with p hp
    rw [hp]

/-- Trivial action modulo `J` implies trivial action modulo any larger ideal. -/
theorem trivialAt_mono {f : Y → Y} {J J' : GermIdeal n Y} (hJJ' : J.Le J') {y : Y} (h : TrivialAt f J y) :
    TrivialAt f J' y :=
  ⟨h.apply_eq, h.mdifferentiableAt, fun g hg => hJJ' _ _ (h.sub_mem g hg)⟩

theorem zeroSet_mono {J J' : GermIdeal n Y} (hJJ' : J.Le J') : zeroSet J' ⊆ zeroSet J :=
  fun _ hy g hg => hy g (hJJ' _ g hg)

/-- Points of `cosupp(J, 1)` are zeros of `J`. -/
theorem cosupport_one_subset_zeroSet {J : GermIdeal n Y} (hJ : J.IsCoherent) :
    cosupport n univ J 1 ⊆ zeroSet J := fun _ hy _ hg =>
  MaximalContact.apply_eq_zero_of_mem_cosupport (fun _ _ h => holomorphicAt_of_mem hJ h) le_rfl hy hg

end Extend

/-! ### Glueing data acting trivially -/

section GlueingTrivial

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The ideal `𝓓^{μ-1}(𝓗(𝔞))` (the tangent ideal of the homogenized ideal), modulo which the glueing maps act
trivially. -/
abbrev glueIdeal (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M := iterDerivIdeal (homogenizedIdeal 𝔞 μ) (μ - 1)

theorem isCoherent_glueIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) : (glueIdeal 𝔞 μ).IsCoherent :=
  isCoherent_iterDerivIdeal (isCoherent_homogenizedIdeal h𝔞 μ) (μ - 1)

/-- `T(𝔞) ⊆ 𝓓^{μ-1}(𝓗(𝔞))`. -/
theorem tangentIdeal_le_glueIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) :
    (tangentIdeal 𝔞 μ).Le (glueIdeal 𝔞 μ) :=
  iterDerivIdeal_mono (le_homogenizedIdeal (fun _ _ hg => holomorphicAt_of_mem h𝔞 hg) hμ) (μ - 1)

/-- **Glueing data whose maps act trivially modulo `𝓓^{μ-1}(𝓗(𝔞))`** at its zeros in `W` (Włodarczyk, proof of
`le:homo` (4): `φ_u^*(f) - φ_v^*(f) ∈ (h) ⊆ T(𝓘)`). -/
theorem exists_glueingData_trivial {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n univ 𝔞 μ) {U U' : Set M} {u v : M → ℂ}
    (hu : MaximalContact.IsTangentDirection 𝔞 μ U u) (hxU : x ∈ U)
    (hv : MaximalContact.IsTangentDirection 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingData 𝔞 μ u v, x ∈ G.W ∧ ∀ y ∈ G.W, y ∈ zeroSet (glueIdeal 𝔞 μ) →
      TrivialAt G.φ (glueIdeal 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdeal 𝔞 μ) y := by
  have hT := isCoherent_iterDerivIdeal h𝔞 (μ - 1)
  have hJ := isCoherent_glueIdeal h𝔞 μ
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg => holomorphicAt_of_mem h𝔞 hg
  have hux : (tangentIdeal 𝔞 μ).mem x u := hu.mem x hxU
  have hvx : (tangentIdeal 𝔞 μ).mem x v := hv.mem x hxU'
  have hu0 : u x = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hx hux
  have hv0 : v x = 0 := MaximalContact.apply_eq_zero_of_mem_cosupport hhol hμ hx hvx
  obtain ⟨P⟩ := exists_coordinatePair (holomorphicAt_of_mem hT hux) (holomorphicAt_of_mem hT hvx)
    (by rw [hu0, hv0]) (hu.multiplicity_one x hxU hu0) (hv.multiplicity_one x hxU' hv0)
  have htr := eventually_trivialAt_coordMap P.d hJ
    (tangentIdeal_le_glueIdeal h𝔞 hμ _ _ (P.mem_tangentIdeal_h h𝔞 hux hvx))
  have htr' := eventually_trivialAt_coordMap P.d' hJ
    (tangentIdeal_le_glueIdeal h𝔞 hμ _ _ (P.mem_tangentIdeal_h' h𝔞 hux hvx))
  have hfix : ∀ᶠ y in 𝓝 x, y ∈ cosupport n univ 𝔞 μ → P.d.coordMap y = y := by
    filter_upwards [P.eventually_coordMap_eq_self_of_mem_cosupport h𝔞 hμ hux hvx] with y hy hyc
    exact (hy hyc).1
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp
    (((eventually_mdifferentiableAt_coordMap P.d).and (eventually_mdifferentiableAt_coordMap P.d')).and
      ((P.left_inv.and P.right_inv).and ((P.eventually_pullback_homogenizedIdeal h𝔞 hμ hux hvx).and
        (P.comp_d.and (hfix.and (htr.and htr'))))))
  refine ⟨⟨P.d.coordMap, P.d'.coordMap, W, ⟨hWo, fun p hp => (hWsub hp).1.1, fun p hp => (hWsub hp).1.2,
    fun p hp => (hWsub hp).2.1.1, fun p hp => (hWsub hp).2.1.2⟩, fun y hy => (hWsub hy).2.2.1,
    fun p hp => (hWsub hp).2.2.2.1, fun y hy => (hWsub hy).2.2.2.2.1⟩, hxW, fun y hy hyJ =>
      ⟨(hWsub hy).2.2.2.2.2.1 hyJ, (hWsub hy).2.2.2.2.2.2 hyJ⟩⟩

end GlueingTrivial

/-! ### One step of the lift: transforms and strict transforms correspond -/

section Step

open BlowupBiholomorphismLift MarkedIdealRestrictOpen MarkedIdealBiholomorphism BlowupStrictSubmanifold BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupRestrictOpen

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) {A B : Opens Y}
  (Φ : CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B)
  (hcorr : Φ ⁻¹' ((↑) ⁻¹' C : Set B) = ((↑) ⁻¹' C : Set A))
  (Φ₁ : CMfd.of (n := n) (preOpen hπ A) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (preOpen hπ B))
  (hΦ₁ : ∀ p : preOpen hπ A, π (Φ₁ p : Z) = (Φ (restrictMap hπ A p) : Y))
include hcorr hΦ₁

theorem restrictMap_comp_lift : restrictMap hπ B ∘ Φ₁ = Φ ∘ restrictMap hπ A :=
  funext fun p => Subtype.ext (hΦ₁ p)

/-- **Strict transforms correspond under the lift.** -/
theorem preimage_lift_geoStrictTransform {Su Sv : Set Y} (hS : Φ ⁻¹' ((↑) ⁻¹' Su : Set B) = ((↑) ⁻¹' Sv : Set A)) :
    Φ₁ ⁻¹' ((↑) ⁻¹' geoStrictTransform π C Su : Set (preOpen hπ B)) =
      ((↑) ⁻¹' geoStrictTransform π C Sv : Set (preOpen hπ A)) := by
  have hBr : ((↑) ⁻¹' geoStrictTransform π C Su : Set (preOpen hπ B)) =
      geoStrictTransform (restrictMap hπ B) ((↑) ⁻¹' C : Set B) ((↑) ⁻¹' Su : Set B) :=
    (geoStrictTransform_restrict B (preOpen hπ B).isOpen Su).symm
  have hAr : ((↑) ⁻¹' geoStrictTransform π C Sv : Set (preOpen hπ A)) =
      geoStrictTransform (restrictMap hπ A) ((↑) ⁻¹' C : Set A) ((↑) ⁻¹' Sv : Set A) :=
    (geoStrictTransform_restrict A (preOpen hπ A).isOpen Sv).symm
  rw [hBr, hAr, ← geoStrictTransform_comp_diffeo Φ₁, restrictMap_comp_lift hπ Φ hcorr Φ₁ hΦ₁]
  unfold geoStrictTransform
  rw [preimage_comp, preimage_sdiff, hS, hcorr]

/-- **Transforms correspond under the lift**: if `Φ^*(𝔪|_B) = 𝔪|_A`, then `Φ₁^*((𝔪')|_{π⁻¹B}) = (𝔪')|_{π⁻¹A}` for the
transform `𝔪'` of `𝔪` along `π` (coherent ideals, `C` a closed submanifold). -/
theorem pullback_lift_geoTransform {m : MarkedIdeal n Y} (hm : m.ideal.IsCoherent)
    (hc : (m.geoTransform C π).ideal.IsCoherent)
    (hpb : MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B → Y) m) =
      MarkedIdeal.pullback (Subtype.val : A → Y) m) :
    MarkedIdeal.pullback Φ₁ (MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π)) =
      MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m.geoTransform C π) := by
  have hmB : (MarkedIdeal.pullback (Subtype.val : B → Y) m).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hm
  have hICB : (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set B)).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_preimage_val hπ.1 B)
  have hBr : MarkedIdeal.pullback (Subtype.val : preOpen hπ B → Z) (m.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B) (restrictMap hπ B) :=
    (geoTransform_pullback_val hm hπ hc B (preOpen hπ B).isOpen).symm
  have hAr : MarkedIdeal.pullback (Subtype.val : preOpen hπ A → Z) (m.geoTransform C π) =
      (MarkedIdeal.pullback (Subtype.val : A → Y) m).geoTransform ((↑) ⁻¹' C : Set A) (restrictMap hπ A) :=
    (geoTransform_pullback_val hm hπ hc A (preOpen hπ A).isOpen).symm
  have hcB : ((MarkedIdeal.pullback (Subtype.val : B → Y) m).geoTransform ((↑) ⁻¹' C : Set B)
      (restrictMap hπ B)).ideal.IsCoherent := by
    rw [← hBr]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hnat := MarkedIdeal.geoTransform_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply (MarkedIdeal.pullback (Subtype.val : B → Y) m) hmB ((↑) ⁻¹' C : Set B)
    (Φ.contMDiff.comp (isBlowupAlong_restrictMap hπ A).contMDiff)
  have hsimp : (Φ.symm ∘ Φ ∘ restrictMap hπ A) = restrictMap hπ A := funext fun p => by simp
  rw [hBr, hAr, ← geoTransform_comp_diffeo Φ₁ _ hmB _ hICB (isBlowupAlong_restrictMap hπ B).contMDiff hcB,
    restrictMap_comp_lift hπ Φ hcorr Φ₁ hΦ₁, ← hnat, hpb, hcorr, hsimp]

end Step

/-! ### The lifts along a multiple test blow-up -/

section Tower

open BlowupBiholomorphismLift MarkedIdealRestrictOpen BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal DerivativeIdealTower MarkedIdealBiholomorphism BlowupControlledTransform

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingData 𝔞 μ u v)

/-- The marked ideal `(M, M, ∅, 𝓓^{μ-1}𝓗(𝔞), 1)`; along a multiple test blow-up of `(𝓗(𝔞), μ)` its transforms are the
transformed tangent ideals. -/
abbrev tanMarked (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M := derivMarked (homogenizedMarked 𝔞 μ) (μ - 1)

/-- **The lift of the glueing biholomorphism along a tower `T`** (Włodarczyk's `φ_{ui}` against `φ_{vi}`): a
biholomorphism `Φ` from the preimage of `U` onto the preimage of `U'` in the last stage, lifting `φ`, acting trivially
(as does its inverse) modulo the transformed tangent ideal at its zeros, identifying the restrictions of the transform
of `(𝓗(𝔞), μ)`, and identifying the strict transforms of `V(u)` and `V(v)`. -/
structure IsGlueingLift {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)) : Prop where
  proj_eq : ∀ p, T.proj (Φ p : Y) = G.φ (T.proj p)
  trivial : ∀ p : openPreimage T G.dom, (p : Y) ∈ zeroSet (geoTransformAlong (tanMarked 𝔞 μ) T).ideal →
    TrivialAt (extendMap Φ) (geoTransformAlong (tanMarked 𝔞 μ) T).ideal p
  trivial_symm : ∀ q : openPreimage T G.cod, (q : Y) ∈ zeroSet (geoTransformAlong (tanMarked 𝔞 μ) T).ideal →
    TrivialAt (extendMap Φ.symm) (geoTransformAlong (tanMarked 𝔞 μ) T).ideal q
  pullback_eq : MarkedIdeal.pullback Φ
      (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y) (geoTransformAlong (homogenizedMarked 𝔞 μ) T)) =
    MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (geoTransformAlong (homogenizedMarked 𝔞 μ) T)
  strict_eq : Φ ⁻¹' ((↑) ⁻¹' strictAlong T {x | u x = 0} : Set (openPreimage T G.cod)) =
    ((↑) ⁻¹' strictAlong T {x | v x = 0} : Set (openPreimage T G.dom))

/-- **Sets in the zero set of the transformed tangent ideal have the same trace on both sides** of the lift. -/
theorem IsGlueingLift.preimage_inter_eq {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)} (hL : IsGlueingLift G T Φ) {C : Set Y}
    (hC : C ⊆ zeroSet (geoTransformAlong (tanMarked 𝔞 μ) T).ideal) :
    Φ ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.cod)) = ((↑) ⁻¹' C : Set (openPreimage T G.dom)) := by
  ext p
  constructor
  · intro hp
    have h1 := (hL.trivial_symm (Φ p) (hC hp)).apply_eq
    rw [extendMap_val, Φ.symm_apply_apply] at h1
    change ((p : Y)) ∈ C
    rw [h1]
    exact hp
  · intro hp
    have h1 := (hL.trivial p (hC hp)).apply_eq
    rw [extendMap_val] at h1
    change ((Φ p : Y)) ∈ C
    rw [h1]
    exact hp

/-- **The lift of the glueing biholomorphism exists along every multiple test blow-up** of `(𝓗(𝔞), μ)` (Włodarczyk,
`le:homo` (4), analytic form), provided the glueing maps act trivially modulo `𝓓^{μ-1}𝓗(𝔞)` at its zeros in `W`
(`exists_glueingData_trivial`). -/
theorem exists_isGlueingLift (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdeal 𝔞 μ) →
      TrivialAt G.φ (glueIdeal 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdeal 𝔞 μ) y) :
    {Y : CMfd.{u} n} → (T : BlowupTower (CMfd.of (n := n) M) Y) →
      IsGeoTestTower (homogenizedMarked 𝔞 μ) T → ∃ Φ, IsGlueingLift G T Φ
  | _, .refl, _ => by
      have hJ := isCoherent_glueIdeal h𝔞 μ
      refine ⟨G.equiv, fun p => rfl, fun p hp => ?_, fun q hq => ?_, G.pullback_restrict h𝔞,
        G.preimage_zeroSet⟩
      · refine trivialAt_congr hJ (htriv p.1 p.2.1 hp).1 ?_
        filter_upwards [G.dom.isOpen.mem_nhds p.2] with y hy
        exact (extendMap_of_mem (A := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.dom)
          (B := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.cod) G.equiv hy).symm
      · refine trivialAt_congr hJ (htriv q.1 q.2.1 hq).2 ?_
        filter_upwards [G.cod.isOpen.mem_nhds q.2] with y hy
        exact (extendMap_of_mem (A := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.cod)
          (B := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.dom) G.equiv.symm hy).symm
  | _, .step T C π hπ, hT => by
      have hT0 : IsGeoTestTower (homogenizedMarked 𝔞 μ) T := hT.1
      have hC : (geoTransformAlong (homogenizedMarked 𝔞 μ) T).IsAdmissibleCentre C := hT.2
      obtain ⟨Φ, hL⟩ := exists_isGlueingLift h𝔞 hμ htriv T hT0
      have hH := isCoherent_homogenizedIdeal h𝔞 μ
      obtain ⟨hJT', -, -, -, -, -, -⟩ := inclusions_tower (X := CMfd.of (n := n) M) (homogenizedMarked 𝔞 μ) rfl hH (j := μ - 1)
        (Nat.sub_le μ 1) (.step T C π hπ) hT
      obtain ⟨-, hNT, hNJ, -, hcohH, hcohJ, -⟩ := inclusions_tower (X := CMfd.of (n := n) M) (homogenizedMarked 𝔞 μ) rfl hH (j := μ - 1)
        (Nat.sub_le μ 1) T hT0
      have hCJ := hJT'.2
      have hdJ : (geoTransformAlong (tanMarked 𝔞 μ) T).d = 1 := by
        rw [d_geoTransformAlong]
        show μ - (μ - 1) = 1
        omega
      set J := (geoTransformAlong (tanMarked 𝔞 μ) T).ideal with hJdef
      have hCzero : C ⊆ zeroSet J := by
        intro y hy
        have := hCJ.2.1 hy
        rw [MarkedIdeal.cosupp, hNJ, hdJ] at this
        exact cosupport_one_subset_zeroSet hcohJ this
      have hJ' : (geoTransformAlong (tanMarked 𝔞 μ) (.step T C π hπ)).ideal = controlledTransform hπ J 1 := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNJ hcohJ hπ, hdJ]
      have hcorr := hL.preimage_inter_eq G hCzero
      obtain ⟨Φ₁, hΦ₁⟩ := exists_lift hπ Φ hcorr
      have hcorr' : Φ.symm ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.dom)) =
          ((↑) ⁻¹' C : Set (openPreimage T G.cod)) := by
        ext q
        have := congrArg (fun S => Φ.symm q ∈ S) hcorr
        simp only [mem_preimage, Diffeomorph.apply_symm_apply] at this
        exact Iff.of_eq this.symm
      have hΦ₁s : ∀ q : preOpen hπ (openPreimage T G.cod),
          π (Φ₁.symm q).1 = (Φ.symm (restrictMap hπ _ q) : _) := by
        intro q
        have h1 := hΦ₁ (Φ₁.symm q)
        rw [Diffeomorph.apply_symm_apply] at h1
        have h2 : restrictMap hπ _ q = Φ (restrictMap hπ _ (Φ₁.symm q)) := Subtype.ext h1
        rw [h2, Diffeomorph.symm_apply_apply]
        rfl
      have hcohT' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
        (by rw [hNT]; exact isClosedSubmanifold_univ) hcohH hC hπ
      refine ⟨Φ₁, fun p => ?_, fun p hp => ?_, fun q hq => ?_, ?_, ?_⟩
      · change T.proj (π (Φ₁ p)) = G.φ (T.proj (π p))
        rw [hΦ₁ p]
        exact hL.proj_eq _
      · rw [hJ'] at hp ⊢
        have hpz : π p ∈ zeroSet J := mem_zeroSet_of_mem_zeroSet_controlledTransform hπ hcohJ hp
        have hA : π p ∈ openPreimage T G.dom := p.2
        refine trivialAt_lift hπ hcohJ hCzero hp (eventually_mdifferentiableAt_extendMap Φ₁.contMDiff p) ?_ ?_
          (hL.trivial ⟨π p, hA⟩ hpz)
        · filter_upwards [(preOpen hπ (openPreimage T G.dom)).isOpen.mem_nhds p.2] with q hq
          have e1 : extendMap Φ₁ q = (Φ₁ ⟨q, hq⟩ : _) := extendMap_of_mem _ hq
          have e2 : extendMap Φ (π q) = (Φ ⟨π q, hq⟩ : _) :=
            extendMap_of_mem (A := openPreimage T G.dom) (B := openPreimage T G.cod) Φ
              (show π q ∈ openPreimage T G.dom from hq)
          exact (congrArg π e1).trans ((hΦ₁ ⟨q, hq⟩).trans e2.symm)
        · filter_upwards [(openPreimage T G.dom).isOpen.mem_nhds hA] with y hy hyC
          rw [extendMap_of_mem Φ hy]
          intro hΦy
          apply hyC
          have : (⟨y, hy⟩ : openPreimage T G.dom) ∈ Φ ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.cod)) := hΦy
          rw [hcorr] at this
          exact this
      · rw [hJ'] at hq ⊢
        have hqz : π q ∈ zeroSet J := mem_zeroSet_of_mem_zeroSet_controlledTransform hπ hcohJ hq
        have hB : π q ∈ openPreimage T G.cod := q.2
        refine trivialAt_lift hπ hcohJ hCzero hq (eventually_mdifferentiableAt_extendMap Φ₁.symm.contMDiff q) ?_ ?_
          (hL.trivial_symm ⟨π q, hB⟩ hqz)
        · filter_upwards [(preOpen hπ (openPreimage T G.cod)).isOpen.mem_nhds q.2] with r hr
          have e1 : extendMap Φ₁.symm r = (Φ₁.symm ⟨r, hr⟩ : _) := extendMap_of_mem _ hr
          have e2 : extendMap Φ.symm (π r) = (Φ.symm ⟨π r, hr⟩ : _) :=
            extendMap_of_mem (A := openPreimage T G.cod) (B := openPreimage T G.dom) Φ.symm
              (show π r ∈ openPreimage T G.cod from hr)
          exact (congrArg π e1).trans ((hΦ₁s ⟨r, hr⟩).trans e2.symm)
        · filter_upwards [(openPreimage T G.cod).isOpen.mem_nhds hB] with y hy hyC
          rw [extendMap_of_mem Φ.symm hy]
          intro hΦy
          apply hyC
          have : (⟨y, hy⟩ : openPreimage T G.cod) ∈
              Φ.symm ⁻¹' ((↑) ⁻¹' C : Set (openPreimage T G.dom)) := hΦy
          rw [hcorr'] at this
          exact this
      · exact pullback_lift_geoTransform hπ Φ hcorr Φ₁ hΦ₁ hcohH hcohT' hL.pullback_eq
      · exact preimage_lift_geoStrictTransform hπ Φ hcorr Φ₁ hΦ₁ hL.strict_eq

/-- **The lift fixes the cosupport** of the transform of `(𝓗(𝔞), μ)` (Włodarczyk `le:homo` (4)(c)). -/
theorem IsGlueingLift.apply_eq_of_mem_cosupp (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {Y : CMfd.{u} n}
    {T : BlowupTower (CMfd.of (n := n) M) Y} (hT : IsGeoTestTower (homogenizedMarked 𝔞 μ) T)
    {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)} (hL : IsGlueingLift G T Φ) (p : openPreimage T G.dom)
    (hp : (p : Y) ∈ (geoTransformAlong (homogenizedMarked 𝔞 μ) T).cosupp) : (Φ p : Y) = p := by
  have hH := isCoherent_homogenizedIdeal h𝔞 μ
  obtain ⟨-, hNT, -, -, hcohH, hcohJ, hle⟩ := inclusions_tower (X := CMfd.of (n := n) M) (homogenizedMarked 𝔞 μ) rfl hH (j := μ - 1)
    (Nat.sub_le μ 1) T hT
  have h1 : (p : Y) ∈ cosupport n univ (geoTransformAlong (homogenizedMarked 𝔞 μ) T).ideal (1 + (μ - 1)) := by
    have := hp
    rw [MarkedIdeal.cosupp, hNT, d_geoTransformAlong] at this
    rwa [show 1 + (μ - 1) = μ by omega]
  have h2 := MaximalContact.cosupport_add_subset_cosupport_iterDerivIdeal _ 1 (μ - 1) h1
  have h3 := cosupport_one_subset_zeroSet (isCoherent_iterDerivIdeal hcohH (μ - 1)) h2
  have h4 := zeroSet_mono hle h3
  have := (hL.trivial p h4).apply_eq
  rwa [extendMap_val] at this

/-- **The Glueing Lemma with the lifts** (Włodarczyk 2005, `le:homo` (1)–(4), `E = ∅`, analytic form): for tangent
directions `u`, `v` of `(𝔞, μ)` on open sets containing `x ∈ cosupp(𝔞, μ)` there are glueing data `G` (a biholomorphism
`Φ : U ≅ U'` with `x ∈ U ∩ U'`, `Φ^*((𝓗(𝔞), μ)|_{U'}) = (𝓗(𝔞), μ)|_U`, `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`, fixing
`cosupp(𝔞, μ) ∩ U`) such that along every multiple test blow-up of `(𝓗(𝔞), μ)` the biholomorphism lifts
(`IsGlueingLift`). -/
theorem glueing_lemma_lift (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {x : M} (hx : x ∈ cosupport n univ 𝔞 μ)
    {U₁ U₂ : Set M} (hu : MaximalContact.IsTangentDirection 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : MaximalContact.IsTangentDirection 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ G : GlueingData 𝔞 μ u v, x ∈ G.dom ∧ x ∈ G.cod ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y),
        IsGeoTestTower (homogenizedMarked 𝔞 μ) T → ∃ Φ, IsGlueingLift G T Φ := by
  obtain ⟨G, hxW, htriv⟩ := exists_glueingData_trivial h𝔞 hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  exact ⟨G, hxd, hxc, fun T hT => exists_isGlueingLift G h𝔞 hμ htriv T hT⟩

end Tower

end

end Hironaka.HomogenizedGlueingLift
