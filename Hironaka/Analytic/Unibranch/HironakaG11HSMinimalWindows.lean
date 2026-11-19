import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
import Hironaka.Analytic.Unibranch.HironakaG11InvMinimalLocalEmbedding
import Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels

/-!
# Hilbert–Samuel phase data on minimal windows (goal G11, route steps 1–5)

The windows of a Hilbert–Samuel phase are lane G11B's minimal local embeddings
(`HironakaG11InvMinimalLocalEmbedding.exists_minimal_localEmbedding_at`: through every point, inside
every open neighbourhood, of ambient dimension `HS(1) − 1`), all of the dimension `H(1) − 1` for the
maximal value `H`. This file builds the windows and their compact footprints, so that the remaining
input of `HironakaG11HSPhaseInduction` is a statement about RECORDS on given minimal windows only.

* `hsStratum X H` (the singular points with value `H`), `exists_minimal_window_at`,
  **`exists_minimal_phase_windows`**: finitely many minimal windows of dimension `H(1) − 1`, each
  inside a prescribed neighbourhood of a point of the stratum, with compact footprints covering the
  (compact) stratum;
* **`HSRecords w H`** (named property of given windows: records in the domain of a route invariant with
  well-ordered values which present `H` ((3a), `HSPresentation`) and transport along the admissible
  overlaps ((a), `RecordsTransport`)), `hsPhaseData_of_hsRecords`;
* **`compactSingularCentreResolution_of_hsRecords`**: Bennett's stabilization and, for every compact
  non-smooth `X` with lexicographically maximal singular value `H`, neighbourhoods of the stratum such
  that every finite family of minimal windows inside them carries such records, imply
  `CompactSingularCentreResolution`.

The named inputs are local (records on small minimal windows; Bennett); nothing proves or assumes G11.
Blueprint: `hironaka-g11-resume-hs-phase-induction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11HSMinimalWindows

open Hironaka Hironaka HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG11HSPhaseInduction
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  HironakaG11SingularCentreModification OriginalLocalEmbeddingStalkHS
  BlowupTowers MarkedIdeals ResolutionInvariantSeq
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

/-- **The Hilbert–Samuel stratum**: the singular points with value `H`. -/
def hsStratum (X : SourceReducedComplexSpace) (H : ℕ → ℕ) : Set X.obj.left :=
  {x | x ∈ intrinsicSingularLocus X.obj ∧ originalStalkHS X x = H}

/-- **A minimal window at a point of the stratum** (G11B's minimal local embedding), of ambient
dimension `H(1) − 1`, inside a prescribed open neighbourhood, with a compact footprint around the point. -/
theorem exists_minimal_window_at (X : SourceReducedComplexSpace) (H : ℕ → ℕ) {x : X.obj.left}
    (hx : x ∈ hsStratum X H) {V : Set X.obj.left} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ (w : DimEmbedding X (H 1 - 1)) (c : w.carrier) (K : Set w.ambient),
      IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x ∧
        range w.toLocalEmbedding.toPoint ⊆ V := by
  obtain ⟨e, hdim, hxr, hrange⟩ :=
    HironakaG11InvMinimalLocalEmbedding.exists_minimal_localEmbedding_at x hV hxV
  rw [hx.2] at hdim
  obtain ⟨d, amb, car, an, map, imm, hov⟩ := e
  have hd : d = H 1 - 1 := by
    change d + 1 = H 1 at hdim
    omega
  subst hd
  obtain ⟨c, hc⟩ := hxr
  have : LocallyCompactSpace amb := ChartedSpace.locallyCompactSpace (ComplexModel (H 1 - 1)) amb
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds c.val
  exact ⟨⟨amb, car, an, map, imm, hov⟩, c, K, hK, mem_interior_iff_mem_nhds.mpr hKc, hc, hrange⟩

/-- **The minimal windows of a phase**: finitely many minimal windows of dimension `H(1) − 1`, each
inside a prescribed neighbourhood of a point of the (compact) stratum, with compact footprints covering
the stratum. -/
theorem exists_minimal_phase_windows (X : SourceReducedComplexSpace) (H : ℕ → ℕ)
    (hD : IsCompact (hsStratum X H)) (Nb : X.obj.left → Set X.obj.left)
    (hNb : ∀ x ∈ hsStratum X H, IsOpen (Nb x) ∧ x ∈ Nb x) :
    ∃ (ι : Type) (_ : Finite ι) (w : ι → DimEmbedding X (H 1 - 1)) (K : ∀ i, Set (w i).ambient),
      (∀ i, IsCompact (K i)) ∧
      (∀ i, ∃ x ∈ hsStratum X H, range (w i).toLocalEmbedding.toPoint ⊆ Nb x) ∧
      ∀ x ∈ hsStratum X H, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧ (w i).toLocalEmbedding.toPoint c = x := by
  have hex : ∀ x : hsStratum X H, ∃ (w : DimEmbedding X (H 1 - 1)) (c : w.carrier) (K : Set w.ambient),
      IsCompact K ∧ c.val ∈ interior K ∧ w.toLocalEmbedding.toPoint c = x.val ∧
        range w.toLocalEmbedding.toPoint ⊆ Nb x.val :=
    fun x => exists_minimal_window_at X H x.property (hNb x x.property).1 (hNb x x.property).2
  choose w c K hK hcK hcx hrange using hex
  let W : hsStratum X H → Set X.obj.left := fun x =>
    (w x).toLocalEmbedding.toPoint '' ((Subtype.val : (w x).carrier → (w x).ambient) ⁻¹' interior (K x))
  have hWo : ∀ x, IsOpen (W x) := fun x =>
    (w x).toLocalEmbedding.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage continuous_subtype_val)
  have hcov : hsStratum X H ⊆ ⋃ x, W x := fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, c ⟨y, hy⟩, hcK ⟨y, hy⟩, hcx ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hD.elim_finite_subcover W hWo hcov
  refine ⟨t, inferInstance, fun i => w i.val, fun i => K i.val, fun i => hK i.val,
    fun i => ⟨i.val.val, i.val.property, hrange i.val⟩, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  obtain ⟨d, hd, rfl⟩ := hyx
  exact ⟨⟨x, hxt⟩, d, interior_subset hd, rfl⟩

/-- **(a) + (b) on given windows**: records in the domain of a route invariant with well-ordered values,
presenting the Hilbert–Samuel value `H` along canonical towers ((3a), `HSPresentation`) and transporting
along the admissible overlaps ((a), `RecordsTransport` with `mapAdm`). -/
def HSRecords {X : SourceReducedComplexSpace} {ι : Type} {N : ℕ} (w : ι → DimEmbedding X N)
    (H : ℕ → ℕ) : Prop :=
  ∃ (k : ℕ) (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ) (R : ResolutionInvariant.{0} N k Λ)
    (𝔪 : ∀ i, MarkedIdeal N (Amb w i)),
    (∀ i, IsInvDomain k (𝔪 i)) ∧ RecordsTransport R 𝔪 (mapAdm w) ∧
      ∀ i, HSPresentation R (w i) (𝔪 i) H

/-- **Phase data from records on minimal windows.** -/
theorem hsPhaseData_of_hsRecords (X : SourceReducedComplexSpace) (H : ℕ → ℕ)
    (hD : IsCompact (hsStratum X H)) (Nb : X.obj.left → Set X.obj.left)
    (hNb : ∀ x ∈ hsStratum X H, IsOpen (Nb x) ∧ x ∈ Nb x)
    (hrec : ∀ (ι : Type) [Finite ι] (w : ι → DimEmbedding X (H 1 - 1)),
      (∀ i, ∃ x ∈ hsStratum X H, range (w i).toLocalEmbedding.toPoint ⊆ Nb x) → HSRecords w H) :
    HSPhaseData X H := by
  obtain ⟨ι, _, w, K, hK, hwN, hfoot⟩ := exists_minimal_phase_windows X H hD Nb hNb
  obtain ⟨k, Λ, _, _, R, 𝔪, hD', hTr, hP⟩ := hrec ι w hwN
  refine ⟨H 1 - 1, k, Λ, inferInstance, inferInstance, R, ι, inferInstance, w, 𝔪, K, hD', hK, ?_, hTr,
    hP, ?_⟩
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
    obtain ⟨j, c', hc'K, hc'⟩ := hfoot _ ⟨hsing, hHS⟩
    exact ⟨j, c', hc'K, hc'⟩
  · intro x hx hxH
    obtain ⟨i, c, -, hc⟩ := hfoot x ⟨hx, hxH⟩
    exact ⟨i, c, hc⟩

/-- **G11 from records on minimal windows and Bennett's stabilization.** If Hilbert–Samuel functions
stabilize and every compact non-smooth `X`, with lexicographically maximal singular value `H`, has open
neighbourhoods of the points of its `H`-stratum such that every finite family of minimal windows (of
dimension `H(1) − 1`) inside them carries records presenting `H` and transporting along the admissible
overlaps, then every compact reduced complex space has a resolution by finitely many blowups with
smooth centres in the singular loci (`g11:general`). -/
theorem compactSingularCentreResolution_of_hsRecords (hS : HSStabilization)
    (hrec : ∀ (X : SourceReducedComplexSpace) [CompactSpace X.obj.left], ¬X.IsSmooth →
      ∀ a ∈ intrinsicSingularLocus X.obj,
        (∀ x ∈ intrinsicSingularLocus X.obj,
          toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a)) →
        ∃ Nb : X.obj.left → Set X.obj.left,
          (∀ x ∈ hsStratum X (originalStalkHS X a), IsOpen (Nb x) ∧ x ∈ Nb x) ∧
          ∀ (ι : Type) [Finite ι] (w : ι → DimEmbedding X (originalStalkHS X a 1 - 1)),
            (∀ i, ∃ x ∈ hsStratum X (originalStalkHS X a),
              range (w i).toLocalEmbedding.toPoint ⊆ Nb x) →
            HSRecords w (originalStalkHS X a)) :
    CompactSingularCentreResolution := by
  apply compactSingularCentreResolution_of_hsPhaseData hS
  intro X _ hns a ha hmax
  obtain ⟨Nb, hNb, hw⟩ := hrec X hns a ha hmax
  refine hsPhaseData_of_hsRecords X _ ?_ Nb hNb hw
  obtain ⟨a', ha', hmax', hDEq, -, -, -, hDc, -⟩ :=
    OriginalIntrinsicHSSuperlevels.exists_original_compact_singular_hs_maximal_stratum X hns
  have hHH : originalStalkHS X a = originalStalkHS X a' :=
    toLex.injective (le_antisymm (hmax' a ha) (hmax a' ha'))
  have hstr : hsStratum X (originalStalkHS X a') =
      OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold X (originalStalkHS X a') :=
    hDEq.symm
  rw [hHH, hstr]
  exact hDc

end

end Hironaka.Analytic.Unibranch.HironakaG11HSMinimalWindows
