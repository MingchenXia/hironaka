/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueingLift
import Hironaka.MarkedIdeal.HomogenizedGlueingAlongTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedGlueingAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Glueing Lemma along a submanifold along multiple test blow-ups: the lifts of the glueing biholomorphism

Source: Włodarczyk 2005, Lemma `le:homo` (4) and its proof, for the marked ideal `(M, N, ∅, 𝓗_N(𝔞), μ)` of
`HomogenizedGlueingAlongTower` (`φ_v` the inclusion of an open set `U`, `φ_u = φ` the glueing biholomorphism `U ≅
U'`, which preserves `N`).

* `glueIdealAlong N 𝔞 μ = 𝓓_N^{μ-1}(𝓗_N(𝔞)) ⊇ T_N(𝔞)` and `exists_glueingDataAlong_trivial`: glueing data along `N` whose
  maps act trivially modulo `𝓓_N^{μ-1}(𝓗_N(𝔞))` at its zeros in `W` (the coordinate changes of the glueing lemma along `N`
  are `HomogenizedIdeal.CoordinateChange`s with `h = v - u ∈ T_N(𝔞)`, so `HomogenizedGlueingLift.eventually_trivialAt_coordMap`
  applies).
* `glueMarkedAlong N 𝔞 μ = (M, M, ∅, 𝓓_N^{μ-1}(𝓗_N(𝔞)), 1)`, the AMBIENT marked ideal of the glue ideal, whose transforms are
  controlled transforms; `withN (glueMarkedAlong N 𝔞 μ) N = 𝓓_N^{μ-1}(𝓗_N(𝔞), μ)` (`μ ≥ 1`).  `glue_tower`: every multiple test
  blow-up of `(𝓗_N(𝔞), μ)` is one of `glueMarkedAlong`, with centres in the strict transforms of `N`, and along it the
  cosupport of `(𝓗_N(𝔞), μ)_T` lies in the zeros of the transformed glue ideal (`le:S` restriction `CoefficientIdealRestriction.restrict_tower`
  for `S = N`, and the inclusions along `N`, `HomogenizedIdealAlongTower.mem_cosupp_derivMarkedAlong_tower`).
* `IsGlueingLiftAlong G T Φ` and `exists_isGlueingLiftAlong` (Włodarczyk `le:homo` (4) along `N`): along every
  multiple test blow-up `T` of `(𝓗_N(𝔞), μ)` a biholomorphism `Φ_T` from the preimage of `U` onto that of `U'` lifts
  `φ`, acts trivially (as does `Φ_T⁻¹`) modulo the transformed glue ideal at its zeros, identifies the restrictions
  of `(𝓗_N(𝔞), μ)_T` (so `N_T` too) and the strict transforms of `V(u)`, `V(v)` and of `N ∩ V(u)`, `N ∩ V(v)`;
  `IsGlueingLiftAlong.apply_eq_of_mem_cosupp`: it fixes the cosupport.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingLiftAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal DerivativeIdealAlong GiraudAlong DerivativeIdealAlongCoherent TangentDirectionAlong IdealWeightPowers HomogenizedIdealAlong HomogenizedGlueingAlong HomogenizedGlueingAlongTower HadamardBridgeAlong BlowupFlatCoordinates GlueingTrivialAction HomogenizedGlueingLift RelativePrincipalizationSpan
open HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### Glueing data along `N` acting trivially -/

section GlueingTrivial

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Iterated derivative ideals along `N` are monotone in the ideal. -/
theorem iterDerivIdealAlong_mono {N : Set M} {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    ∀ j, (iterDerivIdealAlong N 𝔞 j).Le (iterDerivIdealAlong N 𝔟 j)
  | 0 => h
  | j + 1 => derivIdealAlong_mono (iterDerivIdealAlong_mono h j)

/-- **The glue ideal along `N`**: `𝓓_N^{μ-1}(𝓗_N(𝔞))`, modulo which the glueing maps act trivially. -/
abbrev glueIdealAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  iterDerivIdealAlong N (homogenizedIdealAlong N 𝔞 μ) (μ - 1)

theorem isCoherent_glueIdealAlong {N : Set M} {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (μ : ℕ) : (glueIdealAlong N 𝔞 μ).IsCoherent :=
  isCoherent_iterDerivIdealAlong (isCoherent_homogenizedIdealAlong h𝔞 hN μ) hN (μ - 1)

/-- `T_N(𝔞) ⊆ 𝓓_N^{μ-1}(𝓗_N(𝔞))`. -/
theorem tangentIdealAlong_le_glueIdealAlong {N : Set M} {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hμ : 1 ≤ μ) : (tangentIdealAlong N 𝔞 μ).Le (glueIdealAlong N 𝔞 μ) :=
  iterDerivIdealAlong_mono (le_homogenizedIdealAlong
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) hμ) (μ - 1)

/-- **Glueing data along `N` acting trivially** (Włodarczyk, proof of `le:homo` (4), along `N`): for tangent directions
`u`, `v` along `N` at `x ∈ cosupp(𝔞|_N, μ)` there are glueing data along `N` with `x ∈ W` whose maps act trivially
modulo `𝓓_N^{μ-1}(𝓗_N(𝔞))` at its zeros in `W` (recording the coordinate changes, whose `h = ±(v - u)` lies in
`T_N(𝔞)`). -/
theorem exists_glueingDataAlong_trivial {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {N : Set M}
    (hN : IsClosedSubmanifold n N) {μ : ℕ} (hμ : 1 ≤ μ) {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {U U' : Set M}
    {u v : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong N 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.W ∧ ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y := by
  classical
  have hhol : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hT := isCoherent_tangentIdealAlong h𝔞 hN μ
  have hH := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  have hJ := isCoherent_glueIdealAlong h𝔞 hN μ
  have hTJ := tangentIdealAlong_le_glueIdealAlong (N := N) h𝔞 hμ
  have hxN : x ∈ N := hx.1
  have hux : (tangentIdealAlong N 𝔞 μ).mem x u := hu.mem x hxU
  have hvx : (tangentIdealAlong N 𝔞 μ).mem x v := hv.mem x hxU'
  have hu0 : u x = 0 := apply_eq_zero_of_mem_cosupport hhol hμ hx hux
  have hv0 : v x = 0 := apply_eq_zero_of_mem_cosupport hhol hμ hx hvx
  have huh : ∀ y ∈ U, HolomorphicAt n u y := fun y hy =>
    holomorphicAt_of_mem_iterDerivIdealAlong hhol (μ - 1) y u (hu.mem y hy)
  have hvh : ∀ y ∈ U', HolomorphicAt n v y := fun y hy =>
    holomorphicAt_of_mem_iterDerivIdealAlong hhol (μ - 1) y v (hv.mem y hy)
  -- a flat chart of `N` at `x` and a common tangential direction
  obtain ⟨k, hk⟩ := hN.2 x hxN
  obtain ⟨Φ, hΦsrc, hΦx, hflat⟩ := exists_flatChart_of_regularAtDim hk
  obtain ⟨w, i, hw, hi, hwi, hℓu, hℓv⟩ := exists_common_direction hΦsrc hflat hxN (huh x hxU) (hvh x hxU')
    (hu.multiplicity_one x hxU hu0) (hv.multiplicity_one x hxU' hv0)
  -- the two adapted flat charts
  obtain ⟨Θu, hΘut, hΘu0, hΘu, hflatu⟩ :=
    exists_flatChart_alongCoords hΦsrc hflat hΦx hw hi hwi hu.isOpen hxU huh hu0 hℓu
  obtain ⟨Θv, hΘvt, hΘv0, hΘv, hflatv⟩ :=
    exists_flatChart_alongCoords hΦsrc hflat hΦx hw hi hwi hv.isOpen hxU' hvh hv0 hℓv
  have hAu : ∀ᶠ p in 𝓝 x, flatMap Θu p = alongCoords Φ w i u p := by
    filter_upwards [(isOpen_flatDomain Θu).mem_nhds (mem_flatDomain_self Θu)] with p hp
    exact (hΘu hp.1 hp.2).2
  have hAv : ∀ᶠ p in 𝓝 x, flatMap Θv p = alongCoords Φ w i v p := by
    filter_upwards [(isOpen_flatDomain Θv).mem_nhds (mem_flatDomain_self Θv)] with p hp
    exact (hΘv hp.1 hp.2).2
  have hrel1 : ∀ᶠ p in 𝓝 x, flatMap Θv p = flatMap Θu p + (v p - u p) • EuclideanSpace.single i 1 ∧
      flatMap Θu p i = u p := by
    filter_upwards [hAu, hAv] with p hpu hpv
    exact ⟨by rw [hpu, hpv, alongCoords_sub], by rw [hpu, alongCoords_apply_self hwi]⟩
  have hrel2 : ∀ᶠ p in 𝓝 x, flatMap Θu p = flatMap Θv p + (u p - v p) • EuclideanSpace.single i 1 ∧
      flatMap Θv p i = v p := by
    filter_upwards [hAu, hAv] with p hpu hpv
    exact ⟨by rw [hpu, hpv, alongCoords_sub (u := v) (v := u)], by rw [hpv, alongCoords_apply_self hwi]⟩
  -- the coordinate changes
  have hhuv : HolomorphicAt n (fun p => v p - u p) x := GiraudAlong.holomorphicAt_sub (hvh x hxU') (huh x hxU)
  have hhvu : HolomorphicAt n (fun p => u p - v p) x := GiraudAlong.holomorphicAt_sub (huh x hxU) (hvh x hxU')
  have h0uv : (fun p => v p - u p) x = 0 := by show v x - u x = 0; rw [hu0, hv0, sub_zero]
  have h0vu : (fun p => u p - v p) x = 0 := by show u x - v x = 0; rw [hu0, hv0, sub_zero]
  set d := flatChange Θu hΘut _ hhuv h0uv i with hd
  set d' := flatChange Θv hΘvt _ hhvu h0vu i with hd'
  have hP1 := eventually_flatChange_pair hΘut hΘvt hflatu hflatv hhuv h0uv hhvu h0vu hΘu0 hΘv0 hrel1
  have hP2 := eventually_flatChange_pair hΘvt hΘut hflatv hflatu hhvu h0vu hhuv h0uv hΘv0 hΘu0 hrel2
  have hcomp : ∀ g, (homogenizedIdealAlong N 𝔞 μ).mem x g →
      (homogenizedIdealAlong N 𝔞 μ).mem x (g ∘ d.coordMap) := fun g hg =>
    comp_mem_homogenizedIdealAlong_of_mem hΘut hflatu hhuv h0uv h𝔞 hN hi
      (HomogenizedGlueing.sub_mem hT hvx hux) hg
  have hcomp' : ∀ g, (homogenizedIdealAlong N 𝔞 μ).mem x g →
      (homogenizedIdealAlong N 𝔞 μ).mem x (g ∘ d'.coordMap) := fun g hg =>
    comp_mem_homogenizedIdealAlong_of_mem hΘvt hflatv hhvu h0vu h𝔞 hN hi
      (HomogenizedGlueing.sub_mem hT hux hvx) hg
  have hinv1 : ∀ᶠ p in 𝓝 x, d'.coordMap (d.coordMap p) = p := hP1.mono fun p hp => hp.2.1
  have hinv2 : ∀ᶠ p in 𝓝 x, d.coordMap (d'.coordMap p) = p := hP2.mono fun p hp => hp.2.1
  have hfix : ∀ᶠ y in 𝓝 x, y ∈ cosupport n N 𝔞 μ → d.coordMap y = y ∧ d'.coordMap y = y := by
    filter_upwards [hu.isOpen.mem_nhds hxU, hv.isOpen.mem_nhds hxU',
      HomogenizedGlueing.eventually_coordMap_eq_self d, HomogenizedGlueing.eventually_coordMap_eq_self d']
      with y hyU hyU' hy hy' hyc
    have h0u : u y = 0 := apply_eq_zero_of_mem_cosupport hhol hμ hyc (hu.mem y hyU)
    have h0v : v y = 0 := apply_eq_zero_of_mem_cosupport hhol hμ hyc (hv.mem y hyU')
    exact ⟨hy (show v y - u y = 0 by rw [h0u, h0v, sub_zero]), hy' (show u y - v y = 0 by rw [h0u, h0v, sub_zero])⟩
  -- the trivial action modulo the glue ideal
  have htr := eventually_trivialAt_coordMap d hJ (hTJ _ _ (HomogenizedGlueing.sub_mem hT hvx hux))
  have htr' := eventually_trivialAt_coordMap d' hJ (hTJ _ _ (HomogenizedGlueing.sub_mem hT hux hvx))
  have hd2 := (HomogenizedGlueing.eventually_mdifferentiableAt_coordMap d).and
    (HomogenizedGlueing.eventually_mdifferentiableAt_coordMap d')
  have hpb := eventually_pullback_iff_of_inverse hH d d' hcomp hcomp' hinv1
  have hcomp2 := (hP1.and hP2).mono fun p hp => (⟨hp.1.1, hp.2.1⟩ : _ ∧ _)
  have hNp := (hP1.and hP2).mono fun p hp => (⟨hp.1.2.2, hp.2.2.2⟩ : _ ∧ _)
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (hd2.and ((hinv1.and hinv2).and (hpb.and (hcomp2.and
    (hfix.and (hNp.and (htr.and htr')))))))
  exact ⟨⟨d.coordMap, d'.coordMap, W, ⟨hWo, fun p hp => (hWsub hp).1.1, fun p hp => (hWsub hp).1.2,
    fun p hp => (hWsub hp).2.1.1, fun p hp => (hWsub hp).2.1.2⟩, fun y hy => (hWsub hy).2.2.1,
    fun p hp => ((hWsub hp).2.2.2.1).1, fun y hy hyc => ((hWsub hy).2.2.2.2.1 hyc).1,
    fun p hp => ((hWsub hp).2.2.2.2.2.1).1⟩, hxW, fun y hy hyJ =>
      ⟨(hWsub hy).2.2.2.2.2.2.1 hyJ, (hWsub hy).2.2.2.2.2.2.2 hyJ⟩⟩

end GlueingTrivial

/-! ### The glue ideal along multiple test blow-ups -/

section GlueTower

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlongTower

variable {n : ℕ}

/-- **The ambient marked ideal of the glue ideal** `(M, M, ∅, 𝓓_N^{μ-1}(𝓗_N(𝔞)), 1)`: its transforms along multiple test
blow-ups are controlled transforms. -/
def glueMarkedAlong {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (N : Set M)
    (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M where
  N := univ
  E := []
  ideal := iterDerivIdealAlong N (homogenizedIdealAlong N 𝔞 μ) (μ - 1)
  d := 1

/-- Restricted to `N`, the glue marked ideal is `𝓓_N^{μ-1}(𝓗_N(𝔞), μ)` (`μ ≥ 1`). -/
theorem withN_glueMarkedAlong {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N : Set M}
    {𝔞 : GermIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ) :
    withN (glueMarkedAlong N 𝔞 μ) N = derivMarkedAlong (homogenizedMarkedAlong N 𝔞 μ) (μ - 1) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl rfl
    (by show 1 = μ - (μ - 1); omega)

variable {X : CMfd.{u} n} {N : Set X} {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **The cosupport lies in the zeros of the transformed glue ideal**: along a tower that is a multiple test blow-up of
`(𝓗_N(𝔞), μ)` and of the glue marked ideal, with centres in the strict transforms of `N`, `cosupp(𝓗_N(𝔞), μ)_T` lies in the
zero set of the (ambient) transform of `𝓓_N^{μ-1}(𝓗_N(𝔞))`; that transform is coherent with `N` the whole space. -/
theorem cosupp_subset_zeroSet_glue (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hH : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T)
    (hG : IsGeoTestTower (glueMarkedAlong N 𝔞 μ) T) (hTS : CentresIn N T) :
    (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).cosupp ⊆
        zeroSet (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal ∧
      (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal.IsCoherent ∧
      (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).N = univ := by
  have hJ : (glueMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_glueIdealAlong h𝔞 hN μ
  obtain ⟨-, hNT, hcohJ, hNTsub, -, hRE⟩ := restrict_tower (glueMarkedAlong N 𝔞 μ) rfl hJ hN T hG hTS
  refine ⟨fun x hx => ?_, hcohJ, hNT⟩
  have hHcoh : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  have h1 := mem_cosupp_derivMarkedAlong_tower (homogenizedMarkedAlong N 𝔞 μ) hN hHcoh hH
    (Nat.sub_le μ 1) hx
  rw [← withN_glueMarkedAlong hμ, hRE.cosupp_eq, cosupp_withN, d_geoTransformAlong] at h1
  obtain ⟨hxN, hord⟩ := h1
  intro g hg
  have hghol : HolomorphicAt n g x := GermIdeal.IsCoherent.holomorphicAt_mem hcohJ hg
  exact (vanishesToOrderOn_one_iff hxN hghol).mp (hord g hg)

/-- **Multiple test blow-ups of `(𝓗_N(𝔞), μ)` carry the glue ideal**: every multiple test blow-up of `(M, N, ∅, 𝓗_N(𝔞),
μ)` is one of the ambient glue marked ideal, with centres in the strict transforms of `N`; along it `cosupp(𝓗_N(𝔞),
μ)_T` lies in the zeros of the transformed glue ideal, which is coherent with `N` the whole space. -/
theorem glue_tower (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T →
      IsGeoTestTower (glueMarkedAlong N 𝔞 μ) T ∧ CentresIn N T ∧
      (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).cosupp ⊆
        zeroSet (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal ∧
      (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal.IsCoherent ∧
      (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).N = univ
  | _, .refl, hH => ⟨trivial, trivial, cosupp_subset_zeroSet_glue h𝔞 hN hμ _ hH trivial trivial⟩
  | _, .step T C π hπ, hH => by
      obtain ⟨hH0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hH
      obtain ⟨hG0, hTS0, hzero0, hcoh0, hN0⟩ := glue_tower h𝔞 hN hμ T hH0
      have hE : (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).E =
          (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).E :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
          (𝔪 := glueMarkedAlong N 𝔞 μ) (𝔫 := homogenizedMarkedAlong N 𝔞 μ) rfl T
      have hCG : (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).IsAdmissibleCentre C := by
        refine ⟨hC.1, fun x hx => ?_, hE ▸ hC.2.2⟩
        have hxz := hzero0 (hC.2.1 hx)
        show x ∈ cosupport n _ _ _
        rw [hN0, d_geoTransformAlong]
        refine ⟨mem_univ x, fun g hg => ?_⟩
        exact (vanishesToOrderOn_one_iff (mem_univ x) (GermIdeal.IsCoherent.holomorphicAt_mem hcoh0 hg)).mpr
          (hxz g hg)
      have hG : IsGeoTestTower (glueMarkedAlong N 𝔞 μ) (.step T C π hπ) :=
        (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hG0, hCG⟩
      have hNT : (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).N = strictAlong T N :=
        HomogenizedGlueingTower.N_geoTransformAlong _ T
      have hTS : CentresIn N (.step T C π hπ) :=
        (centresIn_step_iff N T C π hπ).mpr ⟨hTS0, fun x hx => hNT ▸ hC.subset_N hx⟩
      exact ⟨hG, hTS, cosupp_subset_zeroSet_glue h𝔞 hN hμ _ hH hG hTS⟩

end GlueTower

/-! ### The lifts along a multiple test blow-up -/

section Lift

open BlowupBiholomorphismLift MarkedIdealRestrictOpen BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupControlledTransform HomogenizedIdealAlongTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- **The lift along `N` of the glueing biholomorphism along a tower `T`** (Włodarczyk's `φ_{ui}` against `φ_{vi}`, along
`N`): a biholomorphism `Φ` from the preimage of `U` onto the preimage of `U'` in the last stage, lifting `φ`, acting
trivially (as does its inverse) modulo the transformed glue ideal at its zeros, identifying the restrictions of the
transform of `(𝓗_N(𝔞), μ)` (its submanifold `N_T` included), and identifying the strict transforms of `V(u)` and `V(v)`
and of `N ∩ V(u)` and `N ∩ V(v)`. -/
structure IsGlueingLiftAlong {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)) : Prop where
  proj_eq : ∀ p, T.proj (Φ p : Y) = G.φ (T.proj p)
  trivial : ∀ p : openPreimage T G.dom, (p : Y) ∈ zeroSet (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal →
    TrivialAt (extendMap Φ) (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal p
  trivial_symm : ∀ q : openPreimage T G.cod, (q : Y) ∈ zeroSet (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal →
    TrivialAt (extendMap Φ.symm) (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal q
  pullback_eq : MarkedIdeal.pullback Φ
      (MarkedIdeal.pullback (Subtype.val : openPreimage T G.cod → Y)
        (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T)) =
    MarkedIdeal.pullback (Subtype.val : openPreimage T G.dom → Y) (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T)
  strict_eq : Φ ⁻¹' ((↑) ⁻¹' strictAlong T {x | u x = 0} : Set (openPreimage T G.cod)) =
    ((↑) ⁻¹' strictAlong T {x | v x = 0} : Set (openPreimage T G.dom))
  strict_eq_N : Φ ⁻¹' ((↑) ⁻¹' strictAlong T (N ∩ {x | u x = 0}) : Set (openPreimage T G.cod)) =
    ((↑) ⁻¹' strictAlong T (N ∩ {x | v x = 0}) : Set (openPreimage T G.dom))

/-- **Sets in the zero set of the transformed glue ideal have the same trace on both sides** of the lift. -/
theorem IsGlueingLiftAlong.preimage_inter_eq {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)} (hL : IsGlueingLiftAlong G T Φ) {C : Set Y}
    (hC : C ⊆ zeroSet (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal) :
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

/-- **The lift of the glueing biholomorphism along `N` exists along every multiple test blow-up** of `(𝓗_N(𝔞), μ)`
(Włodarczyk, `le:homo` (4), along `N`), provided the glueing maps act trivially modulo `𝓓_N^{μ-1}(𝓗_N(𝔞))` at its zeros in
`W` (`exists_glueingDataAlong_trivial`): at each step the centre lies in the zeros of the transformed glue ideal
(`glue_tower`), which `Φ_T` fixes, so the centres correspond and `Φ_T` lifts (`BlowupBiholomorphismLift.exists_lift`); the
lift acts trivially by `GlueingTrivialAction.trivialAt_lift`, and transforms and strict transforms correspond
(`HomogenizedGlueingLift.pullback_lift_geoTransform`, `preimage_lift_geoStrictTransform`). -/
theorem exists_isGlueingLiftAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    (htriv : ∀ y ∈ G.W, y ∈ zeroSet (glueIdealAlong N 𝔞 μ) →
      TrivialAt G.φ (glueIdealAlong N 𝔞 μ) y ∧ TrivialAt G.ψ (glueIdealAlong N 𝔞 μ) y) :
    {Y : CMfd.{u} n} → (T : BlowupTower (CMfd.of (n := n) M) Y) →
      IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T → ∃ Φ, IsGlueingLiftAlong G T Φ
  | _, .refl, _ => by
      have hJ := isCoherent_glueIdealAlong h𝔞 hN μ
      refine ⟨G.equiv, fun p => rfl, fun p hp => ?_, fun q hq => ?_, G.pullback_restrict h𝔞 hN,
        G.preimage_zeroSet, ?_⟩
      · refine trivialAt_congr hJ (htriv p.1 p.2.1 hp).1 ?_
        filter_upwards [G.dom.isOpen.mem_nhds p.2] with y hy
        exact (extendMap_of_mem (A := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.dom)
          (B := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.cod) G.equiv hy).symm
      · refine trivialAt_congr hJ (htriv q.1 q.2.1 hq).2 ?_
        filter_upwards [G.cod.isOpen.mem_nhds q.2] with y hy
        exact (extendMap_of_mem (A := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.cod)
          (B := openPreimage (BlowupTower.refl : BlowupTower (CMfd.of (n := n) M) (CMfd.of (n := n) M)) G.dom) G.equiv.symm hy).symm
      · ext p
        change G.φ p.1 ∈ N ∩ {x | u x = 0} ↔ p.1 ∈ N ∩ {x | v x = 0}
        rw [mem_inter_iff, mem_inter_iff, G.mem_N_iff p.1 p.2.1, mem_ofPred_eq, mem_ofPred_eq, G.comp_eq p.1 p.2.1]
  | _, .step T C π hπ, hT => by
      have hT0 : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T := hT.1
      have hC : (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).IsAdmissibleCentre C := hT.2
      obtain ⟨Φ, hL⟩ := exists_isGlueingLiftAlong h𝔞 hN hμ htriv T hT0
      have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent := isCoherent_homogenizedIdealAlong h𝔞 hN μ
      obtain ⟨-, -, -, hNT, hcohH, -, -⟩ := inclusions_tower_along (X := CMfd.of (n := n) M)
        (homogenizedMarkedAlong N 𝔞 μ) hN hH (j := 0) (Nat.zero_le _) T hT0
      obtain ⟨-, -, hzero, hcohJ, hNJ⟩ := glue_tower (X := CMfd.of (n := n) M) h𝔞 hN hμ T hT0
      set J := (geoTransformAlong (glueMarkedAlong N 𝔞 μ) T).ideal with hJdef
      have hCzero : C ⊆ zeroSet J := fun y hy => hzero (hC.2.1 hy)
      have hJ' : (geoTransformAlong (glueMarkedAlong N 𝔞 μ) (.step T C π hπ)).ideal = controlledTransform hπ J 1 := by
        rw [geoTransformAlong_step, geoTransform_ideal_eq_controlledTransform hNJ hcohJ hπ, d_geoTransformAlong]
        rfl
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
        have h2 : restrictMap hπ _ q = Φ (restrictMap hπ _ (Φ₁.symm q)) :=
          Subtype.ext h1
        rw [h2, Diffeomorph.symm_apply_apply]
        rfl
      have hcohT' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcohH hC hπ
      refine ⟨Φ₁, fun p => ?_, fun p hp => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
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
      · exact preimage_lift_geoStrictTransform hπ Φ hcorr Φ₁ hΦ₁ hL.strict_eq_N

/-- **The lift fixes the cosupport** of the transform of `(𝓗_N(𝔞), μ)` (Włodarczyk `le:homo` (4)(c) along `N`). -/
theorem IsGlueingLiftAlong.apply_eq_of_mem_cosupp (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ)
    {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y} (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T)
    {Φ : CMfd.of (n := n) (openPreimage T G.dom) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T G.cod)} (hL : IsGlueingLiftAlong G T Φ) (p : openPreimage T G.dom)
    (hp : (p : Y) ∈ (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).cosupp) : (Φ p : Y) = p := by
  obtain ⟨-, -, hzero, -, -⟩ := glue_tower (X := CMfd.of (n := n) M) h𝔞 hN hμ T hT
  have := (hL.trivial p (hzero hp)).apply_eq
  rwa [extendMap_val] at this

end Lift

end

end Hironaka.HomogenizedGlueingLiftAlong
