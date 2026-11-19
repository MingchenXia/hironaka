import Hironaka.MarkedIdeal.HomogenizedGlueingAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma along a submanifold, on open sets and along multiple test blow-ups (pullback form)

Hironaka phase H3 (TN23-ENVELOPES): the part of step (4d) of item (4) of `hir:along-calculus` that does not use the
transforms along `N` (claimed on I-0981 C-0048); blueprint `mc:glueing-biholomorphism-along`,
`mc:glueing-tower-pullback-along` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, Lemma `le:homo`
(1)--(3) restated on open sets and the part of (4) that follows from the functoriality of multiple test blow-ups under
étale maps (Proposition `pr:funct`), for the marked ideal `(𝓗_N(𝔞), μ)` on the submanifold `N`, in the ambient encoding:
the marked ideal is `homogenizedMarkedAlong N 𝔞 μ = (M, N, ∅, 𝓗_N(𝔞), μ)`, and the glueing biholomorphism preserves `N`.

This is the along-`N` version of `HomogenizedGlueingTower` (`N = M`), built on `HomogenizedGlueingAlong.glueing_lemma_along`
and on TN-CLASSICAL's transport and restriction lemmas (`MarkedIdealTowerTransport`, `MarkedIdealRestrictOpen`,
`MarkedIdealOpenBiholomorphism`), which hold for a marked ideal whose `N` is any closed submanifold.

* `GlueingDataAlong N 𝔞 μ u v`: a local inverse pair `(φ, ψ)` on an open `W` with the conclusions of the glueing lemma along
  `N` on `W` (including `φ⁻¹N = N`); `exists_glueingDataAlong`.
* `GlueingDataAlong.pullback_restrict`: **`Φ^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U` as marked ideals** (the submanifold
  `N ∩ U'` pulls back to `N ∩ U`); `preimage_zeroSet`: `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`; `apply_eq_of_mem_cosupport`,
  `preimage_inter_eq`: `Φ` fixes `cosupp(𝔞|_N, μ) ∩ U` and `Φ⁻¹(C ∩ U') = C ∩ U` for `C ⊆ cosupp(𝔞|_N, μ)`.
* Towers: `isGeoTestTower_restrict_dom`, `isGeoTestTower_pullbackTower` (the `φ`-pullback of a multiple test blow-up of
  `(𝓗_N(𝔞), μ)` is one of `(𝓗_N(𝔞), μ)|_U`), `geoTransformAlong_pullbackTower_step`, `cosupp_pullbackTower`,
  `isGeoResolution_pullbackTower`, `strictAlong_pullbackTower_zeroSet`; the package `glueing_lemma_along_tower`.

Not here: the stage-by-stage lifts of `Φ` along a tower (the along-`N` form of `mc:glueing-lift`), which use the inclusions
of derivative ideals along `N` under blowups (item (2) of `hir:along-calculus`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingAlongTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  MarkedIdealRestrictOpen BlowupTowerTransforms BlowupRestrictOpen MarkedIdealOpenBiholomorphism
  HomogenizedIdealAlong HomogenizedGlueingAlong TangentDirectionAlong
open HomogenizedGlueingTower (LocalInversePair strictAlong strictAlong_restrict strictAlong_transport)

noncomputable section

/-! ### The glueing biholomorphism along `N` -/

section Glueing

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The homogenized marked ideal along `N`** `(M, N, ∅, 𝓗_N(𝔞), μ)`. -/
def homogenizedMarkedAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M where
  N := N
  E := []
  ideal := homogenizedIdealAlong N 𝔞 μ
  d := μ

/-- `cosupp(𝓗_N(𝔞)|_N, μ) = cosupp(𝔞|_N, μ)` (`μ ≥ 1`). -/
theorem cosupp_homogenizedMarkedAlong {N : Set M} {𝔞 : GermIdeal n M} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {μ : ℕ} (hμ : 1 ≤ μ) : (homogenizedMarkedAlong N 𝔞 μ).cosupp = cosupport n N 𝔞 μ :=
  cosupport_homogenizedIdealAlong h𝔞 hμ

/-- **The glueing data along `N` of two tangent directions** `u`, `v` of `(𝔞|_N, μ)`: a local inverse pair `(φ, ψ)` on an
open set `W` on which `φ^*𝓗_N(𝔞) = 𝓗_N(𝔞)`, `u ∘ φ = v`, `φ` fixes `cosupp(𝔞|_N, μ)` pointwise, and `φ⁻¹N = N`. -/
structure GlueingDataAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) (u v : M → ℂ) where
  /-- The coordinate change replacing `u` by `v`. -/
  φ : M → M
  /-- Its inverse. -/
  ψ : M → M
  /-- The open set on which everything holds. -/
  W : Set M
  pair : LocalInversePair (n := n) φ ψ W
  pullback_iff : ∀ y ∈ W, ∀ g, (GermIdeal.pullback (m := n) φ (homogenizedIdealAlong N 𝔞 μ)).mem y g ↔
    (homogenizedIdealAlong N 𝔞 μ).mem y g
  comp_eq : ∀ p ∈ W, u (φ p) = v p
  apply_eq_self : ∀ y ∈ W, y ∈ cosupport n N 𝔞 μ → φ y = y
  mem_N_iff : ∀ p ∈ W, (φ p ∈ N ↔ p ∈ N)

/-- **Existence of the glueing data along `N`** (Włodarczyk `le:homo` (1)--(3) along `N`, analytic form): near every point
`x` of `cosupp(𝔞|_N, μ)` at which `u` and `v` are tangent directions along `N` (`𝔞` coherent, `N` a closed submanifold). -/
theorem exists_glueingDataAlong {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {N : Set M} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hμ : 1 ≤ μ) {x : M} (hx : x ∈ cosupport n N 𝔞 μ) {U U' : Set M} {u v : M → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) (hxU : x ∈ U)
    (hv : IsTangentDirectionAlong N 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingDataAlong N 𝔞 μ u v, x ∈ G.W := by
  obtain ⟨φ, ψ, -, -, hd, hinv, hpb, -, hcomp, hfix, hNp⟩ := glueing_lemma_along h𝔞 hN hμ hx hu hxU hv hxU'
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (hd.and (hinv.and (hpb.and (hcomp.and (hfix.and hNp)))))
  exact ⟨⟨φ, ψ, W, ⟨hWo, fun p hp => (hWsub hp).1.1, fun p hp => (hWsub hp).1.2,
    fun p hp => (hWsub hp).2.1.1, fun p hp => (hWsub hp).2.1.2⟩, fun y hy => (hWsub hy).2.2.1,
    fun p hp => ((hWsub hp).2.2.2.1).1, fun y hy hyc => ((hWsub hy).2.2.2.2.1 hyc).1,
    fun p hp => ((hWsub hp).2.2.2.2.2).1⟩, hxW⟩

namespace GlueingDataAlong

variable {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- The open neighbourhood `U = W ∩ φ⁻¹W`. -/
abbrev dom : Opens M := G.pair.dom

/-- Its image `U' = φ(U)`. -/
abbrev cod : Opens M := G.pair.cod

/-- **The glueing biholomorphism** `Φ : U ≅ U'`, `p ↦ φ p`. -/
abbrev equiv : CMfd.of (n := n) G.dom ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) G.cod :=
  G.pair.toDiffeomorph

theorem equiv_apply (p : G.dom) : (G.equiv p : M) = G.φ p := rfl

/-- A point of the cosupport in `W` lies in both `U` and `U'`. -/
theorem mem_dom_and_mem_cod {x : M} (hxW : x ∈ G.W) (hx : x ∈ cosupport n N 𝔞 μ) :
    x ∈ G.dom ∧ x ∈ G.cod := by
  have hφx : G.φ x = x := G.apply_eq_self x hxW hx
  have hdom : x ∈ G.dom := ⟨hxW, by rw [mem_preimage, hφx]; exact hxW⟩
  refine ⟨hdom, hxW, ?_⟩
  have hψx : G.ψ x = x := by
    have h := G.pair.left_inv x hxW
    rwa [hφx] at h
  show G.ψ x ∈ G.dom
  rw [hψx]
  exact hdom

/-- **`Φ` fixes the cosupport** (`le:homo` (3) along `N`). -/
theorem apply_eq_of_mem_cosupport (p : G.dom) (hp : (p : M) ∈ cosupport n N 𝔞 μ) : (G.equiv p : M) = p :=
  G.apply_eq_self p.1 p.2.1 hp

/-- **Sets inside the cosupport have the same trace on `U` and `U'`**: `Φ⁻¹(C ∩ U') = C ∩ U` for `C ⊆ cosupp(𝔞|_N, μ)`. -/
theorem preimage_inter_eq {C : Set M} (hC : C ⊆ cosupport n N 𝔞 μ) :
    G.equiv ⁻¹' ((↑) ⁻¹' C : Set G.cod) = ((↑) ⁻¹' C : Set G.dom) := by
  ext p
  change G.φ p.1 ∈ C ↔ p.1 ∈ C
  constructor
  · intro hp
    have hφW : G.φ p ∈ G.W := p.2.2
    have h1 : G.φ (G.φ p) = G.φ p := G.apply_eq_self _ hφW (hC hp)
    have h2 : G.ψ (G.φ (G.φ p)) = G.φ p := G.pair.left_inv _ hφW
    have h3 : G.ψ (G.φ p) = p := G.pair.left_inv _ p.2.1
    rw [h1, h3] at h2
    rwa [← h2] at hp
  · intro hp
    rw [G.apply_eq_self p.1 p.2.1 (hC hp)]
    exact hp

/-- **`Φ` maps `V(v)` onto `V(u)`** (`le:homo` (2)): `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`. -/
theorem preimage_zeroSet :
    G.equiv ⁻¹' ((↑) ⁻¹' {y | u y = 0} : Set G.cod) = ((↑) ⁻¹' {y | v y = 0} : Set G.dom) := by
  ext p
  change u (G.φ p.1) = 0 ↔ v p.1 = 0
  rw [G.comp_eq p.1 p.2.1]

/-- **`Φ` preserves `N`**: `Φ⁻¹(N ∩ U') = N ∩ U`. -/
theorem preimage_N : G.equiv ⁻¹' ((↑) ⁻¹' N : Set G.cod) = ((↑) ⁻¹' N : Set G.dom) := by
  ext p
  exact G.mem_N_iff p.1 p.2.1

/-- `(φ|_U)^* 𝓗_N(𝔞) = 𝓗_N(𝔞)|_U`. -/
theorem pullback_comp_val (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := n) (fun p : G.dom => G.φ p) (homogenizedIdealAlong N 𝔞 μ) =
      GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdealAlong N 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  refine GermIdeal.ext (funext fun p => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨b, hb, rfl⟩
    have hφp : ∀ᶠ q in 𝓝 (p : M),
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) G.φ q :=
      eventually_of_mem (G.pair.isOpen.mem_nhds p.2.1) G.pair.mdifferentiableAt_left
    have hbφ : (homogenizedIdealAlong N 𝔞 μ).mem p (b ∘ G.φ) :=
      (G.pullback_iff p.1 p.2.1 _).mp (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self ⟨b, hb, rfl⟩
          (HadamardBridge.holomorphicAt_comp_map hφp (HomogenizedGlueing.holomorphicAt_of_mem hH hb))))
    exact ⟨b ∘ G.φ, hbφ, rfl⟩
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨g, hg, rfl⟩
    have h1 := RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp
      ((G.pullback_iff p.1 p.2.1 g).mpr hg)
    refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (U := G.dom)) (y := p) h1)
    rintro s ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩

/-- **The glueing biholomorphism preserves the homogenized marked ideal along `N`** (`le:homo` (1) on `U`, with `N`):
`Φ^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U`. -/
theorem pullback_restrict (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    MarkedIdeal.pullback G.equiv
        (MarkedIdeal.pullback (Subtype.val : G.cod → M) (homogenizedMarkedAlong N 𝔞 μ)) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of G.preimage_N rfl ?_ rfl
  change GermIdeal.pullback (m := n) G.equiv
      (GermIdeal.pullback (m := n) (Subtype.val : G.cod → M) (homogenizedIdealAlong N 𝔞 μ)) =
    GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdealAlong N 𝔞 μ)
  rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val G.equiv.contMDiff hH]
  exact G.pullback_comp_val h𝔞 hN

/-- **The first centres agree** (`le:homo` (4), the first blowup, along `N`): for an admissible centre `C` of
`(𝓗_N(𝔞), μ)`, `Φ⁻¹(C ∩ U') = C ∩ U`. -/
theorem preimage_inter_eq_of_isAdmissibleCentre (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {C : Set M}
    (hC : (homogenizedMarkedAlong N 𝔞 μ).IsAdmissibleCentre C) :
    G.equiv ⁻¹' ((↑) ⁻¹' C : Set G.cod) = ((↑) ⁻¹' C : Set G.dom) :=
  G.preimage_inter_eq (hC.2.1.trans (cosupp_homogenizedMarkedAlong
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hμ).subset)

end GlueingDataAlong

end Glueing

/-! ### The glueing lemma along `N` along multiple test blow-ups -/

section GlueingTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

theorem isCoherent_homogenizedMarkedAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent :=
  isCoherent_homogenizedIdealAlong h𝔞 hN μ

theorem isCoherent_restrict (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (U : Opens M) :
    (MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarkedAlong N 𝔞 μ)).ideal.IsCoherent :=
  GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_homogenizedIdealAlong h𝔞 hN μ)

namespace GlueingDataAlong

variable (G : GlueingDataAlong N 𝔞 μ u v)

/-- **The `φ`-pullback of a tower** `T` over `M`: the transport along `Φ : U ≅ U'` of the restriction of `T` to `U'`. -/
abbrev pullbackTower {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y) :
    TowerTransport (CMfd.of (n := n) G.dom) (CMfd.of (n := n) (openPreimage T G.cod)) :=
  transport G.equiv (restrict G.cod T)

variable (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
include h𝔞 hN

/-- **The restriction of a multiple test blow-up of `(𝓗_N(𝔞), μ)` to `U` is one of `(𝓗_N(𝔞), μ)|_U`.** -/
theorem isGeoTestTower_restrict_dom {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ))
      (restrict G.dom T) :=
  isGeoTestTower_restrict G.dom hN (isCoherent_homogenizedMarkedAlong h𝔞 hN) T hT

/-- **The `φ`-pullback of a multiple test blow-up of `(𝓗_N(𝔞), μ)` is a multiple test blow-up of `(𝓗_N(𝔞), μ)|_U`**
(Włodarczyk `le:homo` (4)(a) along `N`). -/
theorem isGeoTestTower_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ))
      (G.pullbackTower T).tower := by
  have h := isGeoTestTower_transport_restrict G.cod G.equiv hN
    (isCoherent_homogenizedMarkedAlong h𝔞 hN) T hT
  rwa [G.pullback_restrict h𝔞 hN] at h

/-- **From the first blowup on, the transforms along the `φ`-pullback are the restrictions of the transforms.** -/
theorem geoTransformAlong_pullbackTower_step {Y Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) (.step T C π hπ)) :
    geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ))
        (G.pullbackTower (.step T C π hπ)).tower =
      MarkedIdeal.pullback (Subtype.val : openPreimage (.step T C π hπ) G.cod → Z)
        (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) (.step T C π hπ)) := by
  rw [← G.pullback_restrict h𝔞 hN]
  exact geoTransformAlong_transport_restrict_step G.cod G.equiv hN
    (isCoherent_homogenizedMarkedAlong h𝔞 hN) T C π hπ hT

/-- **Cosupports along the `φ`-pullback**: the cosupport of the transform of `(𝓗_N(𝔞), μ)|_U` along the `φ`-pullback of
`T` is the preimage, under the last-stage biholomorphism, of the trace of the cosupport of the transform along `T`. -/
theorem cosupp_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T) :
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ))
        (G.pullbackTower T).tower).cosupp =
      (G.pullbackTower T).back ⁻¹'
        ((↑) ⁻¹' (geoTransformAlong (homogenizedMarkedAlong N 𝔞 μ) T).cosupp :
          Set (openPreimage T G.cod)) := by
  obtain ⟨-, hc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN
    (isCoherent_homogenizedMarkedAlong h𝔞 hN) T hT
  rw [← G.pullback_restrict h𝔞 hN, cosupp_geoTransformAlong_transport G.equiv (isCoherent_restrict h𝔞 hN G.cod),
    geoTransformAlong_restrict G.cod hN
      (isCoherent_homogenizedMarkedAlong h𝔞 hN) T hT,
    cosupp_pullback_val _ (fun _ _ hg => HomogenizedGlueing.holomorphicAt_of_mem hc hg)]

/-- **Resolutions pull back to resolutions.** -/
theorem isGeoResolution_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoResolution (homogenizedMarkedAlong N 𝔞 μ) T) :
    IsGeoResolution (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ))
      (G.pullbackTower T).tower := by
  have h := isGeoResolution_transport_restrict G.cod G.equiv hN
    (isCoherent_homogenizedMarkedAlong h𝔞 hN) hT
  rwa [G.pullback_restrict h𝔞 hN] at h

omit h𝔞 hN in
/-- **The strict transforms of the hypersurfaces of maximal contact correspond** (`le:homo` (4)(b), pullback form). -/
theorem strictAlong_pullbackTower_zeroSet {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y) :
    strictAlong (G.pullbackTower T).tower ((↑) ⁻¹' {y | v y = 0} : Set G.dom) =
      (G.pullbackTower T).back ⁻¹' ((↑) ⁻¹' strictAlong T {y | u y = 0} : Set (openPreimage T G.cod)) := by
  rw [← G.preimage_zeroSet, strictAlong_transport G.equiv (restrict G.cod T),
    strictAlong_restrict G.cod T]

end GlueingDataAlong

/-- **The Glueing Lemma along `N`, on open sets, with multiple test blow-ups** (Włodarczyk 2005, `le:homo` (1)--(3) and
the pullback form of (4), for the marked ideal `(𝓗_N(𝔞), μ)` on `N`, `E = ∅`, analytic form).  Let `𝔞` be coherent, `N`
a closed submanifold, `μ ≥ 1`, and `u`, `v` tangent directions of `(𝔞|_N, μ)` along `N` on open sets containing
`x ∈ cosupp(𝔞|_N, μ)`.  There are open sets `U, U' ∋ x` and a biholomorphism `Φ : U ≅ U'` with `Φ x = x` such that
1. `Φ^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U` (as marked ideals: in particular `Φ⁻¹(N ∩ U') = N ∩ U`);
2. `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`;
3. `Φ` fixes `cosupp(𝔞|_N, μ) ∩ U` pointwise;
4. for every multiple test blow-up `T` of `(𝓗_N(𝔞), μ)`, the `φ`-pullback `transport Φ (T|_{U'})` is a multiple test
   blow-up of `(𝓗_N(𝔞), μ)|_U`, and the strict transform of `V(v) ∩ U` along it corresponds to that of `V(u)` along `T`. -/
theorem glueing_lemma_along_tower (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) {U₁ U₂ : Set M} (hu : IsTangentDirectionAlong N 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : IsTangentDirectionAlong N 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ (U U' : Opens M) (Φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U')
      (hxU : x ∈ U), x ∈ U' ∧ (Φ ⟨x, hxU⟩ : M) = x ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U' → M) (homogenizedMarkedAlong N 𝔞 μ)) =
        MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarkedAlong N 𝔞 μ) ∧
      Φ ⁻¹' ((↑) ⁻¹' {y | u y = 0} : Set U') = ((↑) ⁻¹' {y | v y = 0} : Set U) ∧
      (∀ p : U, (p : M) ∈ cosupport n N 𝔞 μ → (Φ p : M) = p) ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y),
        IsGeoTestTower (homogenizedMarkedAlong N 𝔞 μ) T →
          IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarkedAlong N 𝔞 μ))
            (transport Φ (restrict U' T)).tower ∧
          strictAlong (transport Φ (restrict U' T)).tower ((↑) ⁻¹' {y | v y = 0} : Set U) =
            (transport Φ (restrict U' T)).back ⁻¹'
              ((↑) ⁻¹' strictAlong T {y | u y = 0} : Set (openPreimage T U')) := by
  obtain ⟨G, hxW⟩ := exists_glueingDataAlong h𝔞 hN hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  exact ⟨G.dom, G.cod, G.equiv, hxd, hxc, G.apply_eq_of_mem_cosupport ⟨x, hxd⟩ hx, G.pullback_restrict h𝔞 hN,
    G.preimage_zeroSet, G.apply_eq_of_mem_cosupport, fun T hT =>
      ⟨G.isGeoTestTower_pullbackTower h𝔞 hN hT, G.strictAlong_pullbackTower_zeroSet T⟩⟩

end GlueingTower

end

end Hironaka.HomogenizedGlueingAlongTower
