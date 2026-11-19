import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma along multiple test blow-ups (pullback form)

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:local-inverse-biholomorphism`, `mc:glueing-biholomorphism`,
`mc:strict-along`, `mc:glueing-tower-pullback` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.10,
Lemma `le:homo` (Glueing Lemma) (1)–(3) restated on open sets, and the part of (4) that follows from the
functoriality of multiple test blow-ups under étale maps (Proposition `pr:funct`), in the analytic adaptation
of design note D7: the étale neighbourhoods `φ_u, φ_v : X̄ → X` become an open neighbourhood `U` of `x`
with `φ_v` the inclusion and `φ_u = φ` a biholomorphism of `U` onto an open `U'`.

Built on `HomogenizedGlueing.glueing_lemma` (TN23), TN-CLASSICAL's `MarkedIdealTowerTransport.transport`
(towers along a biholomorphism of the base), `MarkedIdealRestrictOpen` (restriction to open subsets) and
`MarkedIdealOpenBiholomorphism` (their composite, and smoothness of holomorphic maps), and TN3's
`BlowupTowerTransforms.restrict`.

## Biholomorphisms between open sets

* `LocalInversePair φ ψ W`: on the open set `W`, `φ` and `ψ` are holomorphic and inverse to each other;
  `LocalInversePair.dom = W ∩ φ⁻¹W`, `LocalInversePair.cod = W ∩ ψ⁻¹(dom)` and
  `LocalInversePair.toDiffeomorph : dom ≃ cod` (`p ↦ φ p`, inverse `q ↦ ψ q`).  Unlike
  `MarkedIdealOpenBiholomorphism.exists_diffeomorph_opens_of_localInverse`, the open sets are explicit, so that
  `U ⊆ W` and further properties of `φ` on `W` hold on `U`.

## The glueing biholomorphism

* `GlueingData 𝔞 μ u v` bundles `φ, ψ, W` with the conclusions of the glueing lemma on `W`;
  `exists_glueingData`: it exists near every point of the cosupport where `u` and `v` are tangent
  directions; `GlueingData.mem_dom_and_mem_cod`: `x ∈ U` and `x ∈ U'`.
* `homogenizedMarked 𝔞 μ = (M, M, ∅, 𝓗(𝔞), μ)`.
* `GlueingData.pullback_restrict`: **`Φ^*((𝓗(𝔞), μ)|_{U'}) = (𝓗(𝔞), μ)|_U`** (`le:homo` (1) on `U`);
  `GlueingData.preimage_zeroSet`: `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U` (`le:homo` (2));
  `GlueingData.apply_eq_of_mem_cosupport`, `GlueingData.preimage_inter_eq`: `Φ` fixes `cosupp(𝔞, μ) ∩ U`
  pointwise and `Φ⁻¹(C ∩ U') = C ∩ U` for every `C ⊆ cosupp(𝔞, μ)` (`le:homo` (3); in particular the first
  centre of a multiple test blow-up of `(𝓗(𝔞), μ)` is the same for `φ_u` and `φ_v`).

## Towers

* `strictAlong T A`: the iterated strict transform of `A` along a tower; `strictAlong_restrict`,
  `strictAlong_transport`: it commutes with restriction to open sets and with transport along a
  biholomorphism; `N_geoTransformAlong`: it is the `N` of the transform.
* `GlueingData.pullbackTower T = transport Φ (T|_{U'})`, Włodarczyk's `φ_u^*(X_i)` (and `restrict U T` is
  `φ_v^*(X_i)`): `GlueingData.isGeoTestTower_pullbackTower` (**the `φ`-pullback of a multiple test blow-up `T` of
  `(𝓗(𝔞), μ)` is a multiple test blow-up of `(𝓗(𝔞), μ)|_U`**, as is `restrict U T`,
  `GlueingData.isGeoTestTower_restrict_dom`), `GlueingData.geoTransformAlong_pullbackTower_step` (from the first
  blowup on its transforms are the restrictions of the transforms of `(𝓗(𝔞), μ)` along `T` to the preimage of
  `U'`), `GlueingData.cosupp_pullbackTower`, `GlueingData.isGeoResolution_pullbackTower` (resolutions pull back to
  resolutions);
* `GlueingData.strictAlong_pullbackTower_zeroSet` (**the strict transform of `V(v) ∩ U` along the `φ`-pullback of
  `T` corresponds to the strict transform of `V(u)` along `T`**);
* `glueing_lemma_tower`: the package at a point `x` of the cosupport.

Not here: the identification of the `φ`-pullback of `T` with the restriction of `T` to `U` stage by stage
(the lifts `φ_i` of `φ` along `T` and the fact that they fix the cosupports, Włodarczyk's induction in the
proof of `le:homo` (4)).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal
  HomogenizedIdeal HomogenizedGlueing BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen BlowupTowerTransforms
  BlowupRestrictOpen MarkedIdealOpenBiholomorphism

noncomputable section

/-! ### Biholomorphisms between open sets -/

section LocalInverse

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A local inverse pair**: on the open set `W`, the maps `φ` and `ψ` are holomorphic and inverse to each
other. -/
structure LocalInversePair (φ ψ : M → M) (W : Set M) : Prop where
  isOpen : IsOpen W
  mdifferentiableAt_left : ∀ p ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p
  mdifferentiableAt_right : ∀ p ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p
  left_inv : ∀ p ∈ W, ψ (φ p) = p
  right_inv : ∀ p ∈ W, φ (ψ p) = p

namespace LocalInversePair

variable {φ ψ : M → M} {W : Set M} (P : LocalInversePair (n := n) φ ψ W)
include P

theorem continuousOn_left : ContinuousOn φ W := fun p hp =>
  (P.mdifferentiableAt_left p hp).continuousAt.continuousWithinAt

theorem continuousOn_right : ContinuousOn ψ W := fun p hp =>
  (P.mdifferentiableAt_right p hp).continuousAt.continuousWithinAt

/-- The domain `U = W ∩ φ⁻¹W`. -/
def dom : Opens M := ⟨W ∩ φ ⁻¹' W, P.continuousOn_left.isOpen_inter_preimage P.isOpen P.isOpen⟩

/-- The codomain `U' = W ∩ ψ⁻¹U`. -/
def cod : Opens M :=
  ⟨W ∩ ψ ⁻¹' (P.dom : Set M), P.continuousOn_right.isOpen_inter_preimage P.isOpen P.dom.isOpen⟩

theorem mem_dom_iff {p : M} : p ∈ P.dom ↔ p ∈ W ∧ φ p ∈ W := Iff.rfl

theorem mem_cod_iff {q : M} : q ∈ P.cod ↔ q ∈ W ∧ ψ q ∈ P.dom := Iff.rfl

theorem apply_mem_cod {p : M} (hp : p ∈ P.dom) : φ p ∈ P.cod :=
  ⟨hp.2, show ψ (φ p) ∈ P.dom by rw [P.left_inv p hp.1]; exact hp⟩

theorem apply_mem_dom {q : M} (hq : q ∈ P.cod) : ψ q ∈ P.dom := hq.2

theorem contMDiff_dom :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun p : P.dom => φ p) := fun p =>
  (contMDiffAt_of_eventually_mdifferentiableAt'
    (eventually_of_mem (P.isOpen.mem_nhds p.2.1) P.mdifferentiableAt_left)).comp p
    (contMDiff_subtype_val p)

theorem contMDiff_cod :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun q : P.cod => ψ q) := fun q =>
  (contMDiffAt_of_eventually_mdifferentiableAt'
    (eventually_of_mem (P.isOpen.mem_nhds q.2.1) P.mdifferentiableAt_right)).comp q
    (contMDiff_subtype_val q)

/-- **The biholomorphism `U ≅ U'`** given by `φ`, with inverse `ψ`. -/
def toDiffeomorph :
    CMfd.of (n := n) P.dom ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) P.cod where
  toFun p := ⟨φ p, P.apply_mem_cod p.2⟩
  invFun q := ⟨ψ q, P.apply_mem_dom q.2⟩
  left_inv p := Subtype.ext (P.left_inv p.1 p.2.1)
  right_inv q := Subtype.ext (P.right_inv q.1 q.2.1)
  contMDiff_toFun := contMDiff_opens_mk P.contMDiff_dom fun p => P.apply_mem_cod p.2
  contMDiff_invFun := contMDiff_opens_mk P.contMDiff_cod fun q => P.apply_mem_dom q.2

@[simp] theorem toDiffeomorph_apply (p : P.dom) : (P.toDiffeomorph p : M) = φ p := rfl

@[simp] theorem toDiffeomorph_symm_apply (q : P.cod) : (P.toDiffeomorph.symm q : M) = ψ q := rfl

end LocalInversePair

end LocalInverse

/-! ### The glueing biholomorphism -/

section Glueing

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The homogenized marked ideal** `(M, M, ∅, 𝓗(𝔞), μ)`. -/
def homogenizedMarked (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M where
  N := univ
  E := []
  ideal := homogenizedIdeal 𝔞 μ
  d := μ

/-- `cosupp(𝓗(𝔞), μ) ⊆ cosupp(𝔞, μ)`, as `𝔞 ⊆ 𝓗(𝔞)`. -/
theorem cosupp_homogenizedMarked_subset {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) :
    (homogenizedMarked 𝔞 μ).cosupp ⊆ cosupport n univ 𝔞 μ := fun _ hx =>
  ⟨hx.1, fun g hg => hx.2 g (le_homogenizedIdeal (fun _ _ hg => holomorphicAt_of_mem h𝔞 hg) hμ _ g hg)⟩

/-- **The glueing data of two tangent directions** `u`, `v` of `(𝔞, μ)`: a local inverse pair `(φ, ψ)` on an
open set `W` on which the conclusions of the glueing lemma hold: `φ^* 𝓗(𝔞) = 𝓗(𝔞)`, `u ∘ φ = v`, and `φ`
fixes `cosupp(𝔞, μ)` pointwise. -/
structure GlueingData (𝔞 : GermIdeal n M) (μ : ℕ) (u v : M → ℂ) where
  /-- The coordinate change replacing `u` by `v`. -/
  φ : M → M
  /-- Its inverse. -/
  ψ : M → M
  /-- The open set on which everything holds. -/
  W : Set M
  pair : LocalInversePair (n := n) φ ψ W
  pullback_iff : ∀ y ∈ W, ∀ g, (GermIdeal.pullback (m := n) φ (homogenizedIdeal 𝔞 μ)).mem y g ↔
    (homogenizedIdeal 𝔞 μ).mem y g
  comp_eq : ∀ p ∈ W, u (φ p) = v p
  apply_eq_self : ∀ y ∈ W, y ∈ cosupport n univ 𝔞 μ → φ y = y

/-- **Existence of the glueing data** (Włodarczyk `le:homo` (1)–(3), analytic form): near every point `x` of
`cosupp(𝔞, μ)` at which `u` and `v` are tangent directions. -/
theorem exists_glueingData {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n univ 𝔞 μ) {U U' : Set M} {u v : M → ℂ}
    (hu : MaximalContact.IsTangentDirection 𝔞 μ U u) (hxU : x ∈ U)
    (hv : MaximalContact.IsTangentDirection 𝔞 μ U' v) (hxU' : x ∈ U') :
    ∃ G : GlueingData 𝔞 μ u v, x ∈ G.W := by
  obtain ⟨φ, ψ, -, hd, hinv, hpb, hcomp, hfix⟩ := glueing_lemma h𝔞 hμ hx hu hxU hv hxU'
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (hd.and (hinv.and (hpb.and (hcomp.and hfix))))
  exact ⟨⟨φ, ψ, W, ⟨hWo, fun p hp => (hWsub hp).1.1, fun p hp => (hWsub hp).1.2,
    fun p hp => (hWsub hp).2.1.1, fun p hp => (hWsub hp).2.1.2⟩, fun y hy => (hWsub hy).2.2.1,
    fun p hp => (hWsub hp).2.2.2.1, fun y hy => (hWsub hy).2.2.2.2⟩, hxW⟩

namespace GlueingData

variable {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingData 𝔞 μ u v)

/-- The open neighbourhood `U = W ∩ φ⁻¹W` of the glueing data. -/
abbrev dom : Opens M := G.pair.dom

/-- Its image `U' = φ(U)`. -/
abbrev cod : Opens M := G.pair.cod

/-- **The glueing biholomorphism** `Φ : U ≅ U'`, `p ↦ φ p`. -/
abbrev equiv : CMfd.of (n := n) G.dom ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) G.cod :=
  G.pair.toDiffeomorph

theorem equiv_apply (p : G.dom) : (G.equiv p : M) = G.φ p := rfl

/-- A point of the cosupport in `W` lies in both `U` and `U'`. -/
theorem mem_dom_and_mem_cod {x : M} (hxW : x ∈ G.W) (hx : x ∈ cosupport n univ 𝔞 μ) :
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

/-- **`Φ` fixes the cosupport** (`le:homo` (3)): `Φ p = p` for `p ∈ U ∩ cosupp(𝔞, μ)`. -/
theorem apply_eq_of_mem_cosupport (p : G.dom) (hp : (p : M) ∈ cosupport n univ 𝔞 μ) :
    (G.equiv p : M) = p :=
  G.apply_eq_self p.1 p.2.1 hp

/-- **Sets inside the cosupport have the same trace on `U` and `U'`**: `Φ⁻¹(C ∩ U') = C ∩ U` for every
`C ⊆ cosupp(𝔞, μ)` (in particular for the centres of multiple test blow-ups). -/
theorem preimage_inter_eq {C : Set M} (hC : C ⊆ cosupport n univ 𝔞 μ) :
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

/-- `(φ|_U)^* 𝓗(𝔞) = 𝓗(𝔞)|_U`. -/
theorem pullback_comp_val (h𝔞 : 𝔞.IsCoherent) :
    GermIdeal.pullback (m := n) (fun p : G.dom => G.φ p) (homogenizedIdeal 𝔞 μ) =
      GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdeal 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdeal h𝔞 μ
  refine GermIdeal.ext (funext fun p => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨b, hb, rfl⟩
    have hφp : ∀ᶠ q in 𝓝 (p : M),
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) G.φ q :=
      eventually_of_mem (G.pair.isOpen.mem_nhds p.2.1) G.pair.mdifferentiableAt_left
    have hbφ : (homogenizedIdeal 𝔞 μ).mem p (b ∘ G.φ) :=
      (G.pullback_iff p.1 p.2.1 _).mp (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self ⟨b, hb, rfl⟩
          (HadamardBridge.holomorphicAt_comp_map hφp (holomorphicAt_of_mem hH hb))))
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

/-- **The glueing biholomorphism preserves the homogenized marked ideal** (`le:homo` (1) on `U`):
`Φ^*((𝓗(𝔞), μ)|_{U'}) = (𝓗(𝔞), μ)|_U`. -/
theorem pullback_restrict (h𝔞 : 𝔞.IsCoherent) :
    MarkedIdeal.pullback G.equiv
        (MarkedIdeal.pullback (Subtype.val : G.cod → M) (homogenizedMarked 𝔞 μ)) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdeal h𝔞 μ
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) G.equiv
      (GermIdeal.pullback (m := n) (Subtype.val : G.cod → M) (homogenizedIdeal 𝔞 μ)) =
    GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdeal 𝔞 μ)
  rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val G.equiv.contMDiff hH]
  exact G.pullback_comp_val h𝔞

/-- **The first centres agree** (`le:homo` (4), the first blowup): for an admissible centre `C` of
`(𝓗(𝔞), μ)`, `Φ⁻¹(C ∩ U') = C ∩ U`. -/
theorem preimage_inter_eq_of_isAdmissibleCentre (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {C : Set M}
    (hC : (homogenizedMarked 𝔞 μ).IsAdmissibleCentre C) :
    G.equiv ⁻¹' ((↑) ⁻¹' C : Set G.cod) = ((↑) ⁻¹' C : Set G.dom) :=
  G.preimage_inter_eq (hC.2.1.trans (cosupp_homogenizedMarked_subset h𝔞 hμ))

end GlueingData

end Glueing

/-! ### Strict transforms along towers -/

section Strict

variable {n : ℕ}

/-- **The iterated strict transform** of `A ⊆ X` along a tower: `A` for the empty tower, and
`closure (π⁻¹(A' \ C))` after a blowup `π` along `C` on top of a tower along which `A` has strict transform
`A'`. -/
def strictAlong {X : CMfd.{u} n} : {Y : CMfd.{u} n} → BlowupTower X Y → Set X → Set Y
  | _, .refl, A => A
  | _, .step T C π _, A => BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T A)

variable {X X' : CMfd.{u} n}

@[simp] theorem strictAlong_refl (A : Set X) :
    strictAlong (BlowupTower.refl : BlowupTower X X) A = A := rfl

theorem strictAlong_step {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (A : Set X) :
    strictAlong (.step T C π hπ) A = BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T A) :=
  rfl

/-- The `N` of the transform of a marked ideal along a tower is the strict transform of `N`. -/
theorem N_geoTransformAlong (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    (geoTransformAlong 𝔪 T).N = strictAlong T 𝔪.N
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [N_geoTransformAlong_step, N_geoTransformAlong 𝔪 T]
      rfl

/-- **Strict transforms commute with restriction to an open set**: the strict transform of `A ∩ U` along the
restricted tower is the trace of the strict transform of `A` on the open preimage of `U`. -/
theorem strictAlong_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A : Set X) →
    strictAlong (restrict U T) ((↑) ⁻¹' A : Set U) = (↑) ⁻¹' strictAlong T A
  | _, .refl, _ => rfl
  | _, .step T C π hπ, A => by
      change BlowupStrictSubmanifold.geoStrictTransform _ ((↑) ⁻¹' C : Set (openPreimage T U))
          (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U)) = _
      rw [strictAlong_restrict U T A]
      exact geoStrictTransform_restrict (openPreimage T U) _ (strictAlong T A)

/-- **Strict transforms commute with transport along a biholomorphism** `Φ : X' ≅ X`: the strict transform of
`Φ⁻¹A` along the transported tower is the preimage of the strict transform of `A` under the last-stage
biholomorphism. -/
theorem strictAlong_transport (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A : Set X) →
      strictAlong (transport Φ T).tower (Φ ⁻¹' A) = (transport Φ T).back ⁻¹' strictAlong T A
  | _, .refl, _ => rfl
  | _, .step T C π hπ, A => by
      have ih := strictAlong_transport Φ T A
      change BlowupStrictSubmanifold.geoStrictTransform ((transport Φ T).back.symm ∘ π)
          ((transport Φ T).back ⁻¹' C) (strictAlong (transport Φ T).tower (Φ ⁻¹' A)) =
        BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T A)
      rw [ih]
      unfold BlowupStrictSubmanifold.geoStrictTransform
      congr 1
      ext z
      simp

end Strict

/-! ### The glueing lemma along multiple test blow-ups -/

section GlueingTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

theorem isClosedSubmanifold_univ : IsClosedSubmanifold n (univ : Set M) :=
  ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩

theorem isCoherent_restrict (h𝔞 : 𝔞.IsCoherent) (U : Opens M) :
    (MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarked 𝔞 μ)).ideal.IsCoherent :=
  GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (isCoherent_homogenizedIdeal h𝔞 μ)

namespace GlueingData

variable (G : GlueingData 𝔞 μ u v)

/-- **The `φ`-pullback of a tower** `T` over `M`: the transport along `Φ : U ≅ U'` of the restriction of `T` to
`U'` (Włodarczyk's `φ_u^*(X_i)`; its stages from the first blowup on are those of the restriction of `T` to
`U'`). -/
abbrev pullbackTower {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y) :
    TowerTransport (CMfd.of (n := n) G.dom) (CMfd.of (n := n) (openPreimage T G.cod)) :=
  transport G.equiv (restrict G.cod T)

variable (h𝔞 : 𝔞.IsCoherent)
include h𝔞

/-- **The restriction of a multiple test blow-up of `(𝓗(𝔞), μ)` to `U` is one of `(𝓗(𝔞), μ)|_U`**
(Włodarczyk's `φ_v^*(X_i)`, `φ_v` the inclusion of `U`). -/
theorem isGeoTestTower_restrict_dom {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarked 𝔞 μ) T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ))
      (restrict G.dom T) :=
  isGeoTestTower_restrict G.dom isClosedSubmanifold_univ (isCoherent_homogenizedIdeal h𝔞 μ) T hT

/-- **The `φ`-pullback of a multiple test blow-up of `(𝓗(𝔞), μ)` is a multiple test blow-up of
`(𝓗(𝔞), μ)|_U`** (Włodarczyk `le:homo` (4)(a), the multiple test blow-up `φ_u^*(X_i)` of
`φ_u^*(𝓗(𝔞), μ) = (𝓗(𝔞), μ)|_U`). -/
theorem isGeoTestTower_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarked 𝔞 μ) T) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ))
      (G.pullbackTower T).tower := by
  have h := isGeoTestTower_transport_restrict G.cod G.equiv isClosedSubmanifold_univ
    (isCoherent_homogenizedIdeal h𝔞 μ) T hT
  rwa [G.pullback_restrict h𝔞] at h

/-- **From the first blowup on, the transforms along the `φ`-pullback are the restrictions of the transforms**:
for a multiple test blow-up `T` of `(𝓗(𝔞), μ)` ending with a blowup, the transform of `(𝓗(𝔞), μ)|_U` along the
`φ`-pullback of `T` is the restriction of the transform of `(𝓗(𝔞), μ)` along `T` to the preimage of `U'`
(Włodarczyk `le:homo` (4)(a): `φ_{ui}^*(𝓗(𝔞)_i, μ)`). -/
theorem geoTransformAlong_pullbackTower_step {Y Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (homogenizedMarked 𝔞 μ) (.step T C π hπ)) :
    geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ))
        (G.pullbackTower (.step T C π hπ)).tower =
      MarkedIdeal.pullback (Subtype.val : openPreimage (.step T C π hπ) G.cod → Z)
        (geoTransformAlong (homogenizedMarked 𝔞 μ) (.step T C π hπ)) := by
  rw [← G.pullback_restrict h𝔞]
  exact geoTransformAlong_transport_restrict_step G.cod G.equiv isClosedSubmanifold_univ
    (isCoherent_homogenizedIdeal h𝔞 μ) T C π hπ hT

/-- **Cosupports along the `φ`-pullback**: the cosupport of the transform of `(𝓗(𝔞), μ)|_U` along the
`φ`-pullback of `T` is the preimage, under the last-stage biholomorphism, of the trace of the cosupport of the
transform of `(𝓗(𝔞), μ)` along `T`. -/
theorem cosupp_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoTestTower (homogenizedMarked 𝔞 μ) T) :
    (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ))
        (G.pullbackTower T).tower).cosupp =
      (G.pullbackTower T).back ⁻¹'
        ((↑) ⁻¹' (geoTransformAlong (homogenizedMarked 𝔞 μ) T).cosupp :
          Set (openPreimage T G.cod)) := by
  obtain ⟨-, hc⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong isClosedSubmanifold_univ
    (isCoherent_homogenizedIdeal h𝔞 μ) T hT
  rw [← G.pullback_restrict h𝔞, cosupp_geoTransformAlong_transport G.equiv (isCoherent_restrict h𝔞 G.cod),
    geoTransformAlong_restrict G.cod isClosedSubmanifold_univ (isCoherent_homogenizedIdeal h𝔞 μ) T hT,
    cosupp_pullback_val _ (fun _ _ hg => holomorphicAt_of_mem hc hg)]

/-- **Resolutions pull back to resolutions**: the `φ`-pullback of a resolution of `(𝓗(𝔞), μ)` resolves
`(𝓗(𝔞), μ)|_U`. -/
theorem isGeoResolution_pullbackTower {Y : CMfd.{u} n} {T : BlowupTower (CMfd.of (n := n) M) Y}
    (hT : IsGeoResolution (homogenizedMarked 𝔞 μ) T) :
    IsGeoResolution (MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarked 𝔞 μ))
      (G.pullbackTower T).tower := by
  have h := isGeoResolution_transport_restrict G.cod G.equiv isClosedSubmanifold_univ
    (isCoherent_homogenizedIdeal h𝔞 μ) hT
  rwa [G.pullback_restrict h𝔞] at h

omit h𝔞 in
/-- **The strict transforms of the hypersurfaces of maximal contact correspond** (Włodarczyk `le:homo` (4)(b),
pullback form): the strict transform of `V(v) ∩ U` along the `φ`-pullback of any tower `T` is the preimage,
under the last-stage biholomorphism, of the trace of the strict transform of `V(u)` along `T`. -/
theorem strictAlong_pullbackTower_zeroSet {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y) :
    strictAlong (G.pullbackTower T).tower ((↑) ⁻¹' {y | v y = 0} : Set G.dom) =
      (G.pullbackTower T).back ⁻¹' ((↑) ⁻¹' strictAlong T {y | u y = 0} : Set (openPreimage T G.cod)) := by
  rw [← G.preimage_zeroSet, strictAlong_transport G.equiv (restrict G.cod T),
    strictAlong_restrict G.cod T]

end GlueingData

/-- **The Glueing Lemma on open sets, with multiple test blow-ups** (Włodarczyk 2005, `le:homo` (1)–(3) and the
pullback form of (4), `E = ∅`, analytic form).  Let `𝔞` be coherent, `μ ≥ 1`, and let `u`, `v` be tangent
directions of `(𝔞, μ)` on open sets containing `x ∈ cosupp(𝔞, μ)`.  There are open sets `U, U' ∋ x` and a
biholomorphism `Φ : U ≅ U'` with `Φ x = x` such that
1. `Φ^*((𝓗(𝔞), μ)|_{U'}) = (𝓗(𝔞), μ)|_U`;
2. `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`;
3. `Φ` fixes `cosupp(𝔞, μ) ∩ U` pointwise;
4. for every multiple test blow-up `T` of `(𝓗(𝔞), μ)`, the `φ`-pullback `transport Φ (T|_{U'})` is a multiple test
   blow-up of `(𝓗(𝔞), μ)|_U`, and the strict transform of `V(v) ∩ U` along it corresponds to the strict transform
   of `V(u)` along `T`. -/
theorem glueing_lemma_tower (h𝔞 : 𝔞.IsCoherent) (hμ : 1 ≤ μ) {x : M} (hx : x ∈ cosupport n univ 𝔞 μ)
    {U₁ U₂ : Set M} (hu : MaximalContact.IsTangentDirection 𝔞 μ U₁ u) (hxU₁ : x ∈ U₁)
    (hv : MaximalContact.IsTangentDirection 𝔞 μ U₂ v) (hxU₂ : x ∈ U₂) :
    ∃ (U U' : Opens M) (Φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U')
      (hxU : x ∈ U), x ∈ U' ∧ (Φ ⟨x, hxU⟩ : M) = x ∧
      MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U' → M) (homogenizedMarked 𝔞 μ)) =
        MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarked 𝔞 μ) ∧
      Φ ⁻¹' ((↑) ⁻¹' {y | u y = 0} : Set U') = ((↑) ⁻¹' {y | v y = 0} : Set U) ∧
      (∀ p : U, (p : M) ∈ cosupport n univ 𝔞 μ → (Φ p : M) = p) ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) M) Y),
        IsGeoTestTower (homogenizedMarked 𝔞 μ) T →
          IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → M) (homogenizedMarked 𝔞 μ))
            (transport Φ (restrict U' T)).tower ∧
          strictAlong (transport Φ (restrict U' T)).tower ((↑) ⁻¹' {y | v y = 0} : Set U) =
            (transport Φ (restrict U' T)).back ⁻¹'
              ((↑) ⁻¹' strictAlong T {y | u y = 0} : Set (openPreimage T U')) := by
  obtain ⟨G, hxW⟩ := exists_glueingData h𝔞 hμ hx hu hxU₁ hv hxU₂
  obtain ⟨hxd, hxc⟩ := G.mem_dom_and_mem_cod hxW hx
  exact ⟨G.dom, G.cod, G.equiv, hxd, hxc, G.apply_eq_of_mem_cosupport ⟨x, hxd⟩ hx, G.pullback_restrict h𝔞,
    G.preimage_zeroSet, G.apply_eq_of_mem_cosupport, fun T hT =>
      ⟨G.isGeoTestTower_pullbackTower h𝔞 hT, G.strictAlong_pullbackTower_zeroSet T⟩⟩

end GlueingTower

end

end Hironaka.HomogenizedGlueingTower
