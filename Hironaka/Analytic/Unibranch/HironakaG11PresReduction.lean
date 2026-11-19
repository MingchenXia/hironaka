import Hironaka.Analytic.Unibranch.HironakaG11PresWindows
import Hironaka.Analytic.Unibranch.HironakaG11BennettStabilization
import Hironaka.Resolution.HironakaG11PresNativeStateWindow
import Hironaka.Resolution.HironakaG11PresClassTransport

/-!
# The G11 reduction along the native Hilbert–Samuel window records (goal G11, steps (3a) + (3b))

The Hilbert–Samuel route to `g11:general` (human decisions Option 1 and (B')) with every step proved except two named
inputs, each a classical theorem that is not a restatement of G11:

* `HironakaG11PresLineState.NativeLineStability` — step (3a-lines): the native Hilbert–Samuel state (Hironaka's standard-basis
  presentation) is stable under the product with a line (BM97 Thm 9.4, test (ii));
* **`ClassFunctorialInvariants`** — for every `N`, a resolution invariant of index `N` with well-ordered values that is class
  functorial for G8's local equivalence `LocWPEquiv` (lane G11B's `HironakaG11InvBMClass.BMInvariant`, the target of repair
  (B'): Bierstone–Milman 2008, Thm 7.1, "strong functoriality": the invariant of a marked ideal depends only on its
  equivalence class).

Bennett's stabilization is proved (lane G11A, `HironakaG11BennettStabilization.hsStabilization`).

* `IsNativeWindowRecord w 𝔪 H` (domain of index `N`, empty boundary, native state for the window carrier and `H`),
  `IsNativeWindowRecord.isHSWindowRecord`;
* `exists_native_state_window_at`, **`exists_native_state_phase_windows`**: native window records on minimal windows
  through every point of the Hilbert–Samuel stratum, finitely many with compact footprints covering the (compact) stratum;
* **`recordsTransport_of_native`**: for a class-functorial invariant, common-mark powers of native window records transport
  along the admissible overlaps (`RecordsTransport`, step (3b)) — given `NativeLineStability`;
* **`compactSingularCentreResolution_of_nativeLineStability`**: `NativeLineStability → ClassFunctorialInvariants →
  CompactSingularCentreResolution` (`g11:general`).

Blueprint: `hironaka-g11-pres-reduction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11PresReduction

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalLocalEmbeddingInitialHS
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedAnalytic HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers HironakaG11HSPhaseInduction
  HironakaG11HSMinimalWindows HironakaG11PresPresentation HironakaG11PresTowerState HironakaG11PresWindows
  HironakaG11PresLineState HironakaG11PresClassTransport HironakaG11SingularCentreModification
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  HironakaActualPowerBoundaryExponents
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.HironakaG11InvBMClass (BMInvariant)
open _root_.Hironaka.HironakaG8LocalHistory (LocWPEquiv)

noncomputable section

/-! ### Native window records -/

section Records

variable {X : SourceReducedComplexSpace} {N : ℕ}

/-- **A native Hilbert–Samuel window record**: a record on the ambient of the window `w`, in the domain of the invariant of
index `N`, with empty boundary, in the native Hilbert–Samuel state for the window carrier and `H`. -/
def IsNativeWindowRecord (w : DimEmbedding X N) (𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient))
    (H : ℕ → ℕ) : Prop :=
  IsInvDomain N 𝔪 ∧ 𝔪.E = [] ∧ NativeHSState 𝔪 w.carrier H

/-- A native window record is a Hilbert–Samuel window record (round 1). -/
theorem IsNativeWindowRecord.isHSWindowRecord {w : DimEmbedding X N}
    {𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient)} {H : ℕ → ℕ} (h : IsNativeWindowRecord w 𝔪 H) :
    IsHSWindowRecord w 𝔪 H := by
  obtain ⟨hD, hE, hs⟩ := h
  exact ⟨hD, hs.2.2.1, hE, hs.hsTowerState⟩

end Records

/-! ### Native minimal windows -/

section Windows

/-- **A native minimal window at a point of the Hilbert–Samuel stratum**: inside any open neighbourhood `V` of `x`, a window
of ambient dimension `H(1) − 1` through `x`, with a compact footprint around the point over `x`, carrying a native window
record for `H`. -/
theorem exists_native_state_window_at (X : SourceReducedComplexSpace) (H : ℕ → ℕ) {x : X.obj.left}
    (hx : x ∈ hsStratum X H) {V : Set X.obj.left} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ (w : DimEmbedding X (H 1 - 1)) (𝔪 : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient))
      (c : w.carrier) (K : Set w.ambient),
      IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x ∧
        range w.toLocalEmbedding.toPoint ⊆ V ∧ IsNativeWindowRecord w 𝔪 H := by
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
  obtain ⟨U, V', η, O, hOU, z₀, Q, hz₀, -, hDom, hQE, hState⟩ :=
    HironakaG11PresNativeStateWindow.exists_native_state_phase_window (M := amb) car an c.val hcs univ
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
  have hState' : NativeHSState (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ Q)
      (Φ ⁻¹' ((Subtype.val : HironakaG11PresNativePhase.opensIn U O → U) ⁻¹'
        ((fun z : U => (η z : amb)) ⁻¹' car))) H := by
    have h := hState.pullback Φ
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
  · refine ⟨InvDomainTowerAlong.isInvDomain_pullback Φ hDom, ?_, hState'⟩
    change Q.E.map (Φ ⁻¹' ·) = []
    rw [hQE, List.map_nil]

/-- **The native minimal windows of a phase**: finitely many minimal windows (ambient dimension `H(1) − 1`), each inside a
prescribed neighbourhood of a point of the (compact) stratum, with compact footprints covering the stratum, carrying native
window records for `H`. -/
theorem exists_native_state_phase_windows (X : SourceReducedComplexSpace) (H : ℕ → ℕ)
    (hD : IsCompact (hsStratum X H)) (Nb : X.obj.left → Set X.obj.left)
    (hNb : ∀ x ∈ hsStratum X H, IsOpen (Nb x) ∧ x ∈ Nb x) :
    ∃ (ι : Type) (_ : Finite ι) (w : ι → DimEmbedding X (H 1 - 1))
      (𝔪 : ∀ i, MarkedIdeal (H 1 - 1) (Amb w i)) (K : ∀ i, Set (w i).ambient),
      (∀ i, IsCompact (K i)) ∧
      (∀ i, ∃ x ∈ hsStratum X H, range (w i).toLocalEmbedding.toPoint ⊆ Nb x) ∧
      (∀ x ∈ hsStratum X H, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧
        (w i).toLocalEmbedding.toPoint c = x) ∧
      ∀ i, IsNativeWindowRecord (w i) (𝔪 i) H := by
  classical
  have hex : ∀ x : hsStratum X H, ∃ (w : DimEmbedding X (H 1 - 1))
      (𝔪 : MarkedIdeal (H 1 - 1) (CMfd.of (n := H 1 - 1) w.ambient)) (c : w.carrier)
      (K : Set w.ambient), IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x.val ∧
        range w.toLocalEmbedding.toPoint ⊆ Nb x.val ∧ IsNativeWindowRecord w 𝔪 H :=
    fun x => exists_native_state_window_at X H x.property (hNb x x.property).1 (hNb x x.property).2
  choose w 𝔪 c K hK hcK hcx hrange hrec using hex
  let W : hsStratum X H → Set X.obj.left := fun x =>
    (w x).toLocalEmbedding.toPoint '' ((Subtype.val : (w x).carrier → (w x).ambient) ⁻¹' interior (K x))
  have hWo : ∀ x, IsOpen (W x) := fun x =>
    (w x).toLocalEmbedding.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage continuous_subtype_val)
  have hcov : hsStratum X H ⊆ ⋃ x, W x := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, c ⟨y, hy⟩, hcK ⟨y, hy⟩, hcx ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hD.elim_finite_subcover W hWo hcov
  refine ⟨t, inferInstance, fun i => w i.val, fun i => 𝔪 i.val, fun i => K i.val, fun i => hK i.val,
    fun i => ⟨i.val.val, i.val.property, hrange i.val⟩, ?_, fun i => hrec i.val⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  obtain ⟨d, hd, rfl⟩ := hyx
  exact ⟨⟨x, hxt⟩, d, interior_subset hd, rfl⟩

end Windows

/-! ### Transport and the reduction -/

section Reduction

/-- **(3b) for native window records**: for a class-functorial invariant of index `N` (lane G11B's `BMInvariant` for
`LocWPEquiv`), powers `𝔪_i^{e_i}` of native window records with one common mark transport along the admissible overlaps,
given `NativeLineStability`. -/
theorem recordsTransport_of_native (hL : NativeLineStability) {X : SourceReducedComplexSpace} {N : ℕ} {Λ : Type}
    [LinearOrder Λ] (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') N Λ) {ι : Type*}
    (w : ι → DimEmbedding X N) (𝔪₀ : ∀ i, MarkedIdeal N (Amb w i)) (H : ℕ → ℕ)
    (hrec : ∀ i, IsNativeWindowRecord (w i) (𝔪₀ i) H) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hd : ∀ i j, (powerMarked (𝔪₀ i) (e i)).d = (powerMarked (𝔪₀ j) (e j)).d) :
    RecordsTransport B.toResolutionInvariant (fun i => powerMarked (𝔪₀ i) (e i)) (mapAdm w) := by
  intro i j U U' Φ hadm Y Y' T T' hcan hcan' χ hiso p
  obtain ⟨hDi, hEi, hsi⟩ := hrec i
  obtain ⟨hDj, hEj, hsj⟩ := hrec j
  have hNi : (𝔪₀ i).N = univ := hsi.2.2.1
  have hNj : (𝔪₀ j).N = univ := hsj.2.2.1
  exact inv_eq_on_overlap_of_classFunctorial B U U' Φ (powerMarked_isInvDomain (𝔪₀ i) hDi (he i))
    (powerMarked_isInvDomain (𝔪₀ j) hDj (he j)) hNi hNj hEi hEj (hd i j)
    (locWPEquiv_overlap_of_native hL hDi hDj hEi hEj hsi hsj U U' Φ (mapAdm_carrier hadm) (he i) (he j))
    hcan' hcan hiso p

/-- **Class-functorial resolution invariants** (named input; lane G11B's target, repair (B')): for every `N` a resolution
invariant of index `N` on marked ideals of dimension `N` (properties (1)–(7), (4'), (8) of `ResolutionInvariantSeq`), with
well-ordered values, which is class functorial for G8's local equivalence `LocWPEquiv` (`HironakaG11InvBMClass.BMInvariant`:
two `LocWPEquiv`-equivalent marked ideals of the domain with the same mark, divisor, carrier dimensions and boundary
exponents have the same canonical segments and the same values along them). Bierstone–Milman 2008, Theorem 7.1 (with
Remark 1.8 / §5 Step I.A for local blowings-up, products with a line and no exceptional blowups, BPRIME-PLAN D1). -/
def ClassFunctorialInvariants : Prop :=
  ∀ N : ℕ, ∃ (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ),
    Nonempty (BMInvariant N (fun {Y : CMfd.{0} N} A A' => LocWPEquiv (X := Y) A A') N Λ)

/-- **G11 along the native Hilbert–Samuel window records.** Native line stability ((3a-lines)) and class-functorial
resolution invariants give `g11:general`: every compact reduced complex space has a resolution by finitely many blowups with
smooth centres in the singular loci. (Bennett's stabilization and the presentation (3a) along blowups are proved; the
transport (3b) is derived from class functoriality.) -/
theorem compactSingularCentreResolution_of_nativeLineStability (hL : NativeLineStability)
    (hB : ClassFunctorialInvariants) : CompactSingularCentreResolution := by
  apply HironakaG11BennettStabilization.compactSingularCentreResolution_of_hsPhaseData'
  intro X _ hns a ha hmax
  have hD : IsCompact (hsStratum X (originalStalkHS X a)) := by
    obtain ⟨a', ha', hmax', hDEq, -, -, -, hDc, -⟩ :=
      OriginalIntrinsicHSSuperlevels.exists_original_compact_singular_hs_maximal_stratum X hns
    have hHH : originalStalkHS X a = originalStalkHS X a' :=
      toLex.injective (le_antisymm (hmax' a ha) (hmax a' ha'))
    have hstr : hsStratum X (originalStalkHS X a') =
        OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold X (originalStalkHS X a') :=
      hDEq.symm
    rw [hHH, hstr]
    exact hDc
  obtain ⟨ι, hfin, w, 𝔪₀, K, hK, -, hfoot, hrec⟩ :=
    exists_native_state_phase_windows X (originalStalkHS X a) hD (fun _ => univ) (fun _ _ => ⟨isOpen_univ, trivial⟩)
  obtain ⟨Λ, hlin, hwf, ⟨B⟩⟩ := hB (originalStalkHS X a 1 - 1)
  have : Fintype ι := Fintype.ofFinite ι
  let marks : ι → ℕ := fun i => (𝔪₀ i).d
  let D : ℕ := ∏ i, marks i
  have hmarks : ∀ i, 1 ≤ marks i := fun i => (hrec i).1.one_le_d
  have hDpos : 0 < D := HironakaG11InvCommonMark.prodMark_pos marks hmarks
  have he : ∀ i, 1 ≤ D / marks i := fun i =>
    HironakaG11InvCommonMark.one_le_div_of_dvd hDpos (HironakaG11InvCommonMark.dvd_prodMark marks i)
  have hdD : ∀ i, (powerMarked (𝔪₀ i) (D / marks i)).d = D := fun i =>
    HironakaG11InvCommonMark.powerMarked_div_d (𝔪₀ i) (HironakaG11InvCommonMark.dvd_prodMark marks i)
  exact hsPhaseData_of_hsWindowRecords X (originalStalkHS X a) w (fun i => powerMarked (𝔪₀ i) (D / marks i)) K hK
    hfoot (fun i => (hrec i).isHSWindowRecord.powerMarked (he i)) B.toResolutionInvariant
    (recordsTransport_of_native hL B w 𝔪₀ (originalStalkHS X a) hrec (fun i => D / marks i) he
      (fun i j => (hdD i).trans (hdD j).symm))

end Reduction

end

end Hironaka.Analytic.Unibranch.HironakaG11PresReduction
