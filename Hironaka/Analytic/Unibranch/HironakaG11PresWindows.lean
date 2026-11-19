import Hironaka.Analytic.Unibranch.HironakaG11PresPresentation
import Hironaka.Analytic.Unibranch.HironakaG11HSMinimalWindows
import Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingInitialHS
import Hironaka.Resolution.HironakaG11PresNativePhase
import Hironaka.Resolution.HironakaG11InvCommonMark

/-!
# Minimal Hilbert–Samuel windows with presenting records (goal G11, step (3a))

The records of step (3a) of the Hilbert–Samuel route (human decision Option 1): at every point of the
Hilbert–Samuel stratum of a complex space `X`, inside every open neighbourhood, a MINIMAL window
(ambient dimension `H(1) − 1`, lane G11B's minimal local embedding) carrying a record which presents
`H` along all multiple test blow-ups — Hironaka's standard-basis presentation of the library's native
Hilbert–Samuel phase (`HironakaG11PresNativePhase.exists_native_hs_phase_window`), read in the
window. Such a record has lane G11A's presentation property `HSPresentation R w 𝔪 H` for EVERY
route invariant `R` of index `H(1) − 1`. Finitely many such windows cover the (compact) stratum
with compact footprints, and their records can be normalized to ONE common mark (powers).

* `IsHSWindowRecord w 𝔪 H` (domain of index `N`, carrier `univ`, empty boundary, `HSTowerState`),
  `IsHSWindowRecord.hsPresentation`;
* `HSTowerState.of_wEquiv`, `IsHSWindowRecord.powerMarked` (the presentation only depends on the
  test towers and cosupports; powers `(𝔞^e, de)`);
* **`exists_native_window_at`**, **`exists_native_phase_windows`** (finitely many minimal windows
  inside prescribed neighbourhoods, compact footprints covering the stratum, presenting records of
  one common mark);
* **`hsPhaseData_of_hsWindowRecords`**: such a family and a route invariant with well-ordered values
  transporting along the admissible overlaps (step (3b), not proved here) give lane G11A's
  `HSPhaseData X H`.

Nothing here proves or assumes G11; (3b) is not addressed. Blueprint:
`hironaka-g11-pres-presentation.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11PresWindows

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalLocalEmbeddingInitialHS
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers HironakaG11HSPhaseInduction
  HironakaG11HSMinimalWindows HironakaG11PresPresentation HironakaG11PresTowerState
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  HironakaActualPowerBoundaryExponents MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### Window records presenting the Hilbert–Samuel function -/

section Records

variable {X : SourceReducedComplexSpace} {N : ℕ}

/-- **A Hilbert–Samuel window record**: a record on the ambient of the window `w`, in the domain of
the invariant of index `N`, with carrier the whole ambient and empty boundary, which presents `H` on
the window carrier along all multiple test blow-ups. -/
def IsHSWindowRecord (w : DimEmbedding X N) (𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient))
    (H : ℕ → ℕ) : Prop :=
  IsInvDomain N 𝔪 ∧ 𝔪.N = univ ∧ 𝔪.E = [] ∧ HSTowerState 𝔪 w.carrier H

/-- **(3a) for Hilbert–Samuel window records**, for every route invariant of index `N`. -/
theorem IsHSWindowRecord.hsPresentation {w : DimEmbedding X N}
    {𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient)} {H : ℕ → ℕ} (h : IsHSWindowRecord w 𝔪 H)
    {Λ : Type*} [LinearOrder Λ] (R : ResolutionInvariant.{0} N N Λ) : HSPresentation R w 𝔪 H :=
  hsPresentation_of_hsTowerState R w 𝔪 H h.1 h.2.2.2

/-- The presentation only depends on the multiple test blow-ups and their cosupports. -/
theorem HSTowerState.of_wEquiv {n : ℕ} {M : CMfd.{0} n} {𝔪 𝔫 : MarkedIdeal n M} (h : WEquiv 𝔪 𝔫)
    {W : Set M} {H : ℕ → ℕ} (hs : HSTowerState 𝔪 W H) : HSTowerState 𝔫 W H := by
  intro Y T hT
  have hT' : IsGeoTestTower 𝔪 T := ((h.2 T).1).mpr hT
  have hcos := (h.2 T).2 hT'
  obtain ⟨hA, hsub, hle, hcut, hsing⟩ := hs T hT'
  rw [← hcos]
  exact ⟨hA, hsub, hle, hcut, hsing⟩

/-- **Powers of a Hilbert–Samuel window record** `(𝔞, d) ↦ (𝔞^e, de)` are Hilbert–Samuel window
records. -/
theorem IsHSWindowRecord.powerMarked {w : DimEmbedding X N}
    {𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient)} {H : ℕ → ℕ} (h : IsHSWindowRecord w 𝔪 H)
    {e : ℕ} (he : 1 ≤ e) : IsHSWindowRecord w (powerMarked 𝔪 e) H :=
  ⟨powerMarked_isInvDomain 𝔪 h.1 he, h.2.1, h.2.2.1,
    HSTowerState.of_wEquiv (HironakaG11InvCommonMark.wEquiv_powerMarked 𝔪 h.1 he) h.2.2.2⟩

end Records

/-! ### Native minimal windows -/

section Windows

/-- **A native minimal window at a point of the Hilbert–Samuel stratum**: inside any open
neighbourhood `V` of `x`, a window of ambient dimension `H(1) − 1` through `x`, with a compact
footprint around the point over `x`, carrying a Hilbert–Samuel window record for `H`. -/
theorem exists_native_window_at (X : SourceReducedComplexSpace) (H : ℕ → ℕ) {x : X.obj.left}
    (hx : x ∈ hsStratum X H) {V : Set X.obj.left} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ (w : DimEmbedding X (H 1 - 1)) (𝔪 : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient))
      (c : w.carrier) (K : Set w.ambient),
      IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x ∧
        range w.toLocalEmbedding.toPoint ⊆ V ∧ IsHSWindowRecord w 𝔪 H := by
  obtain ⟨e, hdim, hxr, hrange⟩ :=
    HironakaG11InvMinimalLocalEmbedding.exists_minimal_localEmbedding_at x hV hxV
  rw [hx.2] at hdim
  obtain ⟨d, amb, car, an, map, imm, hov⟩ := e
  have hd : d = H 1 - 1 := by
    change d + 1 = H 1 at hdim
    omega
  subst hd
  let e : LocalEmbedding X := ⟨H 1 - 1, amb, car, an, map, imm, hov⟩
  obtain ⟨c, hc⟩ := hxr
  have hcs : c.val ∈ singularSet (n := H 1 - 1) car := by
    have h : c ∈ e.toPoint ⁻¹' intrinsicSingularLocus X.obj := by
      rw [mem_preimage]
      rw [show e.toPoint c = x from hc]
      exact hx.1
    rw [OriginalIntrinsicSingularLocus.intrinsicSingularLocus_localEmbedding_preimage X e] at h
    exact h
  obtain ⟨U, V', η, O, hOU, z₀, Q, hz₀, -, hDom, hQN, hQE, hState⟩ :=
    HironakaG11PresNativePhase.exists_native_hs_phase_window (M := amb) car an c.val hcs univ
      isOpen_univ trivial
  let eU := presentationLocalEmbedding X e U V' η
  let eO := eU.restrict O hOU
  let w : DimEmbedding X (H 1 - 1) := DimEmbedding.ofLocalEmbedding eO
  let Φ : CMfd.of (n := H 1 - 1) O ≃ₘ⟮𝓘(ℂ, ComplexModel (H 1 - 1)), 𝓘(ℂ, ComplexModel (H 1 - 1))⟯
      CMfd.of (n := H 1 - 1) (HironakaG11PresNativePhase.opensIn U O) :=
    opensWithinDiffeo U O hOU
  let 𝔪 : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient) :=
    MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ Q
  have hHc : hilbertSamuelAt (vanishingIdeal (n := H 1 - 1) car) c.val = H := by
    funext ℓ
    rw [← originalStalkHS_localEmbedding_eq X e c ℓ]
    rw [show e.toPoint c = x from hc, hx.2]
  have hState' : HSTowerState (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ Q)
      (Φ ⁻¹' ((Subtype.val : HironakaG11PresNativePhase.opensIn U O → U) ⁻¹'
        ((fun z : U => (η z : amb)) ⁻¹' car))) H := by
    intro Y T hT
    have h := HSTowerState.pullback Φ hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hState T hT
    rwa [hHc] at h
  have hz₀car : (η (Opens.inclusion hOU z₀) : amb) ∈ car := by
    rw [hz₀]
    exact c.property
  let d₀ : w.carrier := ⟨z₀, hz₀car⟩
  have hd₀ : w.toLocalEmbedding.toPoint d₀ = x := by
    change e.toPoint ⟨(η (Opens.inclusion hOU z₀) : amb), hz₀car⟩ = x
    rw [show (⟨(η (Opens.inclusion hOU z₀) : amb), hz₀car⟩ : car) = c from Subtype.ext hz₀]
    exact hc
  have : LocallyCompactSpace w.ambient :=
    ChartedSpace.locallyCompactSpace (ComplexModel (H 1 - 1)) w.ambient
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds d₀.val
  refine ⟨w, 𝔪, d₀, K, hK, mem_interior_iff_mem_nhds.mpr hKc, hd₀, ?_, ?_⟩
  · rintro _ ⟨d', rfl⟩
    exact hrange ⟨_, rfl⟩
  · refine ⟨InvDomainTowerAlong.isInvDomain_pullback Φ hDom, ?_, ?_, ?_⟩
    · change Φ ⁻¹' Q.N = univ
      rw [hQN, preimage_univ]
    · change Q.E.map (Φ ⁻¹' ·) = []
      rw [hQE, List.map_nil]
    · intro Y T hT
      exact hState' T hT

/-- **The native minimal windows of a phase**: finitely many minimal windows (ambient dimension
`H(1) − 1`), each inside a prescribed neighbourhood of a point of the (compact) stratum, with compact
footprints covering the stratum, carrying Hilbert–Samuel window records for `H` of ONE common mark. -/
theorem exists_native_phase_windows (X : SourceReducedComplexSpace) (H : ℕ → ℕ)
    (hD : IsCompact (hsStratum X H)) (Nb : X.obj.left → Set X.obj.left)
    (hNb : ∀ x ∈ hsStratum X H, IsOpen (Nb x) ∧ x ∈ Nb x) :
    ∃ (ι : Type) (_ : Finite ι) (w : ι → DimEmbedding X (H 1 - 1))
      (𝔪 : ∀ i, MarkedIdeal (H 1 - 1) (Amb w i)) (K : ∀ i, Set (w i).ambient) (D : ℕ),
      (∀ i, IsCompact (K i)) ∧
      (∀ i, ∃ x ∈ hsStratum X H, range (w i).toLocalEmbedding.toPoint ⊆ Nb x) ∧
      (∀ x ∈ hsStratum X H, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧
        (w i).toLocalEmbedding.toPoint c = x) ∧
      (∀ i, IsHSWindowRecord (w i) (𝔪 i) H) ∧ 0 < D ∧ ∀ i, (𝔪 i).d = D := by
  classical
  have hex : ∀ x : hsStratum X H, ∃ (w : DimEmbedding X (H 1 - 1))
      (𝔪 : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient)) (c : w.carrier)
      (K : Set w.ambient), IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x.val ∧
        range w.toLocalEmbedding.toPoint ⊆ Nb x.val ∧ IsHSWindowRecord w 𝔪 H :=
    fun x => exists_native_window_at X H x.property (hNb x x.property).1 (hNb x x.property).2
  choose w 𝔪₀ c K hK hcK hcx hrange hrec using hex
  let W : hsStratum X H → Set X.obj.left := fun x =>
    (w x).toLocalEmbedding.toPoint '' ((Subtype.val : (w x).carrier → (w x).ambient) ⁻¹' interior (K x))
  have hWo : ∀ x, IsOpen (W x) := fun x =>
    (w x).toLocalEmbedding.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage continuous_subtype_val)
  have hcov : hsStratum X H ⊆ ⋃ x, W x := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, c ⟨y, hy⟩, hcK ⟨y, hy⟩, hcx ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hD.elim_finite_subcover W hWo hcov
  let marks : t → ℕ := fun i => (𝔪₀ i.val).d
  let D : ℕ := ∏ i, marks i
  have hmarks : ∀ i, 1 ≤ marks i := fun i => (hrec i.val).1.one_le_d
  have hDpos : 0 < D := HironakaG11InvCommonMark.prodMark_pos marks hmarks
  refine ⟨t, inferInstance, fun i => w i.val, fun i => powerMarked (𝔪₀ i.val) (D / marks i),
    fun i => K i.val, D, fun i => hK i.val, fun i => ⟨i.val.val, i.val.property, hrange i.val⟩,
    ?_, fun i => (hrec i.val).powerMarked
      (HironakaG11InvCommonMark.one_le_div_of_dvd hDpos (HironakaG11InvCommonMark.dvd_prodMark marks i)),
    hDpos, fun i => HironakaG11InvCommonMark.powerMarked_div_d (𝔪₀ i.val)
      (HironakaG11InvCommonMark.dvd_prodMark marks i)⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  obtain ⟨d, hd, rfl⟩ := hyx
  exact ⟨⟨x, hxt⟩, d, interior_subset hd, rfl⟩

end Windows

/-! ### Hilbert–Samuel phase data -/

section PhaseData

/-- **Phase data from Hilbert–Samuel window records and transport.** A finite family of windows of
one dimension carrying Hilbert–Samuel window records for `H`, with compact footprints covering the
`H`-stratum, and a route invariant (index the window dimension, well-ordered values) whose values
transport along the admissible overlaps (step (3b)), give lane G11A's `HSPhaseData X H`; the
presentation property (3a) is `IsHSWindowRecord.hsPresentation`. -/
theorem hsPhaseData_of_hsWindowRecords (X : SourceReducedComplexSpace) (H : ℕ → ℕ) {N : ℕ}
    {ι : Type} [Finite ι] (w : ι → DimEmbedding X N) (𝔪 : ∀ i, MarkedIdeal N (Amb w i))
    (K : ∀ i, Set (w i).ambient) (hK : ∀ i, IsCompact (K i))
    (hfoot : ∀ x ∈ hsStratum X H, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧
      (w i).toLocalEmbedding.toPoint c = x)
    (hrec : ∀ i, IsHSWindowRecord (w i) (𝔪 i) H)
    {Λ : Type} [LinearOrder Λ] [WellFoundedLT Λ] (R : ResolutionInvariant.{0} N N Λ)
    (hTr : RecordsTransport R 𝔪 (mapAdm w)) : HSPhaseData X H := by
  have hP : ∀ i, HSPresentation R (w i) (𝔪 i) H := fun i => (hrec i).hsPresentation R
  refine ⟨N, N, Λ, inferInstance, inferInstance, R, ι, inferInstance, w, 𝔪, K, fun i => (hrec i).1,
    hK, ?_, hTr, hP, ?_⟩
  · intro i c hc
    have hHS := (HSPresentation.mem_cosupp_iff hP i c).mp hc
    have hsing : (w i).toLocalEmbedding.toPoint c ∈ intrinsicSingularLocus X.obj := by
      have h := ((hP i BlowupTower.refl trivial).2 (w i).analytic c).2.2 hc
      have h2 : c ∈ (EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding).hom.left.base ⁻¹'
          intrinsicSingularLocus X.obj := by
        rw [HironakaG11CompatibleAnalyticCover.preimage_intrinsicSingularLocus_of_isOpenImmersion
          (EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding) (w i).isOpenImmersion]
        exact h
      exact h2
    exact hfoot _ ⟨hsing, hHS⟩
  · intro x hx hxH
    obtain ⟨i, c, -, hc⟩ := hfoot x ⟨hx, hxH⟩
    exact ⟨i, c, hc⟩

end PhaseData

end

end Hironaka.Analytic.Unibranch.HironakaG11PresWindows
