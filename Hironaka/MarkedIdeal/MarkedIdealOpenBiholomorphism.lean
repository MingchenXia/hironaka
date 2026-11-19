import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.GeoTransformWellFormed

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local biholomorphisms: biholomorphisms between open subsets, and towers along them

Blueprint `hir:open-biholomorphism`, `hir:tower-transport-open` (`blueprint/src/hironaka.tex`, Hironaka phase H1).
Sources: Włodarczyk 2005 §2.4 (Proposition `pr:funct`, étale neighbourhoods) and the Glueing Lemma `le:homo` (4) (the
multiple test blow-ups induced by two étale neighbourhoods `φ_u, φ_v : X̄ → X`); in the analytic setting the étale
neighbourhoods are an open inclusion and a biholomorphism between open sets.

* `contMDiffAt_of_eventually_mdifferentiableAt'`: a map between complex manifolds that is holomorphic near a point is
  `C^∞` there (the normed-space case is `HolomorphicIdealSheaves.contMDiffAt_of_eventually_mdifferentiableAt`);
* `exists_diffeomorph_opens_of_localInverse`: **a local inverse pair `(φ, ψ)` near `x` (holomorphic, `ψ ∘ φ = id` and
  `φ ∘ ψ = id` near `x`, `φ x = x`) is a biholomorphism `Φ : U ≅ V` between open neighbourhoods of `x`** (Mathlib
  `Diffeomorph` between the open submanifolds), with `Φ = φ` and `Φ⁻¹ = ψ` pointwise -- the form in which the
  glueing lemma's coordinate change (`HomogenizedGlueing.glueing_lemma`, TN23) meets tower transport;
* `isWellFormed_geoTransformAlong`: every stage of a multiple test blow-up of a well-formed marked ideal is well
  formed (TN3's one-step `GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre`, by induction);
* for a tower `T` over `X`, an open `V ⊆ X` and a biholomorphism `Φ : U' ≅ V`, the tower
  `transport Φ (restrict V T)` over `U'`: `geoTransformAlong_transport_restrict_step` (from the first blowup on its
  transforms of `Φ^*(𝔪|_V)` are the restrictions of those of `𝔪`), `isGeoTestTower_transport_restrict`,
  `isGeoResolution_transport_restrict`, `isWellFormed_geoTransformAlong_transport_restrict`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealOpenBiholomorphism

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealTowerTransport Hironaka.MarkedIdealRestrictOpen
  Hironaka.BlowupTowerTransforms Hironaka.BlowupRestrictOpen

noncomputable section

/-! ### Biholomorphisms between open subsets -/

section Open

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A map that is holomorphic near a point is `C^∞` there** (target a complex manifold). -/
theorem contMDiffAt_of_eventually_mdifferentiableAt' {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y] {f : Y → M} {y : Y}
    (hf : ∀ᶠ y' in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f y') :
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y := by
  have hc : ContinuousAt f y := hf.self_of_nhds.continuousAt
  rw [contMDiffAt_iff_target]
  refine ⟨hc, contMDiffAt_of_eventually_mdifferentiableAt ?_⟩
  filter_upwards [hf, hc.preimage_mem_nhds
    ((chartAt (ComplexModel n) (f y)).open_source.mem_nhds (mem_chart_source _ _))] with y' hy' hy's
  exact (mdifferentiableAt_extChartAt hy's).comp y' hy'

/-- **A local inverse pair is a biholomorphism between open neighbourhoods.**  If `φ, ψ : M → M` are holomorphic
near `x`, `ψ ∘ φ = id` and `φ ∘ ψ = id` near `x`, and `φ x = x`, there are open `U, V ∋ x` and a biholomorphism
`Φ : U ≅ V` (a `Diffeomorph` of the open submanifolds) with `Φ = φ` and `Φ⁻¹ = ψ` pointwise. -/
theorem exists_diffeomorph_opens_of_localInverse {φ ψ : M → M} {x : M}
    (hd : ∀ᶠ p in 𝓝 x, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p)
    (hinv : ∀ᶠ p in 𝓝 x, ψ (φ p) = p ∧ φ (ψ p) = p) (hx : φ x = x) :
    ∃ (U V : Opens M) (Φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V),
      x ∈ U ∧ x ∈ V ∧ (∀ p : U, ((Φ p : V) : M) = φ p) ∧ (∀ q : V, ((Φ.symm q : U) : M) = ψ q) := by
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp (hd.and hinv)
  have hφc : ContinuousOn φ O := fun p hp => ((hOsub hp).1.1.continuousAt).continuousWithinAt
  have hψc : ContinuousOn ψ O := fun p hp => ((hOsub hp).1.2.continuousAt).continuousWithinAt
  set U : Opens M := ⟨O ∩ φ ⁻¹' O, hφc.isOpen_inter_preimage hOopen hOopen⟩ with hUdef
  set V : Opens M := ⟨O ∩ ψ ⁻¹' (U : Set M), hψc.isOpen_inter_preimage hOopen U.isOpen⟩ with hVdef
  have hxU : x ∈ U := ⟨hxO, by show φ x ∈ O; rw [hx]; exact hxO⟩
  have hxV : x ∈ V := by
    refine ⟨hxO, ?_⟩
    show ψ x ∈ (U : Set M)
    have h1 : ψ (φ x) = x := ((hOsub hxO).2).1
    rw [hx] at h1
    rw [h1]
    exact hxU
  have hfV : ∀ p : U, φ p.1 ∈ V := fun p => ⟨p.2.2, by
    show ψ (φ p.1) ∈ (U : Set M)
    rw [((hOsub p.2.1).2).1]
    exact p.2⟩
  have hgU : ∀ q : V, ψ q.1 ∈ U := fun q => q.2.2
  -- smoothness of `φ` and `ψ` on `O`
  have hφs : ∀ p ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ p := fun p hp =>
    contMDiffAt_of_eventually_mdifferentiableAt' (Filter.mem_of_superset (hOopen.mem_nhds hp)
      fun q hq => (hOsub hq).1.1)
  have hψs : ∀ p ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ p := fun p hp =>
    contMDiffAt_of_eventually_mdifferentiableAt' (Filter.mem_of_superset (hOopen.mem_nhds hp)
      fun q hq => (hOsub hq).1.2)
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun p : U => (⟨φ p.1, hfV p⟩ : V)) :=
    contMDiff_opens_mk (fun p => (hφs p.1 p.2.1).comp p (contMDiff_subtype_val p)) hfV
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun q : V => (⟨ψ q.1, hgU q⟩ : U)) :=
    contMDiff_opens_mk (fun q => (hψs q.1 q.2.1).comp q (contMDiff_subtype_val q)) hgU
  refine ⟨U, V, ⟨⟨fun p => ⟨φ p.1, hfV p⟩, fun q => ⟨ψ q.1, hgU q⟩, fun p => ?_, fun q => ?_⟩, hf, hg⟩,
    hxU, hxV, fun _ => rfl, fun _ => rfl⟩
  · exact Subtype.ext ((hOsub p.2.1).2).1
  · exact Subtype.ext ((hOsub q.2.1).2).2

end Open

/-! ### Well-formed stages -/

section WellFormed

variable {n : ℕ} {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Every stage of a multiple test blow-up of a well-formed marked ideal is well formed.** -/
theorem isWellFormed_geoTransformAlong (h : 𝔪.IsWellFormed) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T → (geoTransformAlong 𝔪 T).IsWellFormed
  | _, .refl, _ => h
  | _, .step T _ _ hπ, hT =>
      GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
        (isWellFormed_geoTransformAlong h T hT.1) hT.2 hπ

end WellFormed

/-! ### Towers along a biholomorphism onto an open subset -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (V : Opens X) {U' : CMfd.{u} n}
  (Φ : U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V)

/-- **From the first blowup on, the transforms along `transport Φ (restrict V T)` are restrictions**: for a multiple
test blow-up `T` of `𝔪` (`N` a closed submanifold, `𝔞` coherent), the transform of `Φ^*(𝔪|_V)` along the transported
restricted tower is the restriction of the transform of `𝔪` along `T`. -/
theorem geoTransformAlong_transport_restrict_step (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) :
    geoTransformAlong (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪))
        (transport Φ (restrict V (.step T C π hπ))).tower =
      MarkedIdeal.pullback (Subtype.val : openPreimage (.step T C π hπ) V → Z)
        (geoTransformAlong 𝔪 (.step T C π hπ)) := by
  have hcoh : (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞
  exact (geoTransformAlong_transport_step Φ hcoh _ _ _ _).trans
    (geoTransformAlong_restrict V hN h𝔞 (.step T C π hπ) hT)

/-- **Multiple test blow-ups transport to multiple test blow-ups of `Φ^*(𝔪|_V)`.** -/
theorem isGeoTestTower_transport_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    IsGeoTestTower (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪))
      (transport Φ (restrict V T)).tower :=
  (isGeoTestTower_transport_iff Φ (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞)
    (restrict V T)).mpr (isGeoTestTower_restrict V hN h𝔞 T hT)

/-- **Resolutions transport to resolutions of `Φ^*(𝔪|_V)`.** -/
theorem isGeoResolution_transport_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoResolution 𝔪 T) :
    IsGeoResolution (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪))
      (transport Φ (restrict V T)).tower :=
  (isGeoResolution_transport_iff Φ (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞)
    (restrict V T)).mpr (isGeoResolution_restrict V hN h𝔞 hT)

/-- **Well-formed stages**: along a multiple test blow-up of a well-formed `𝔪`, every stage of the transported
restricted tower is well formed. -/
theorem isWellFormed_geoTransformAlong_transport_restrict (h𝔪 : 𝔪.IsWellFormed) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪))
      (transport Φ (restrict V T)).tower).IsWellFormed :=
  isWellFormed_geoTransformAlong (IsWellFormed.pullback (IsWellFormed.pullback_val h𝔪 V)) _
    (isGeoTestTower_transport_restrict V Φ h𝔪.isClosedSubmanifold_N h𝔪.isCoherent T hT)

end Tower

end

end Hironaka.MarkedIdealOpenBiholomorphism
