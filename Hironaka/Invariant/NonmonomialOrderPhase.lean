import Hironaka.Invariant.NonmonomialOrderTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion phase of the general step: admissible centres, and finitely many orders over a compact set

Hironaka phase H2 (TN3), for TN-CLASSICAL's general step (`hir:general-step`); claim I-0977 C-0194.  Blueprint
`bcalc:nonmonomial-order-phase` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`),
Step 2a of Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

Two inputs of the general step's value on the side of the companion phase:

* property (1): the level sets of the value at a point of order `o ≥ 1` are those of the maximal-order invariant of the
  companion ideal `𝓞(𝔫, o)` (`𝔫` the transform at the start of the run, restricted to the mask), and their admissibility for
  the companion's transform must be read for the transform of `𝔫`.  **`isAdmissibleCentre_companion_iff`**: along a multiple
  test blow-up `T` of `𝓞(𝔫, o)`, a set is an admissible centre of `𝓞(𝔫, o)_T` iff it is one of `𝔫_T` lying in `{ν ≥ o}`
  (same divisor, `cosupp 𝓞_T = {ν ≥ o} ∩ cosupp 𝔫_T`, `NonmonomialOrderTail.cosupp_companionOf_geoTransformAlong`);
  **`isAdmissibleCentre_pullback_val_companion_iff`**: the same on every open subset of the last stage (the form the
  patching of `MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens` consumes);
* property (8): over a compact set only finitely many orders occur, along the whole segment.
  **`exists_nmOrd_le_of_isCompact`**: `ν` is bounded on every compact subset of `N` (upper semicontinuity);
  **`exists_nmOrd_le_of_isCompact_of_canonical`**: along every canonical segment of a value function whose order dominates
  `ν` (`NonmonomialOrderCanonical.OrdMonotone`) which is a multiple test blow-up, `ν` at the points of the cosupport over a
  compact `K` of the base is at most one bound depending only on `K` (the order never goes up,
  `NonmonomialOrderCanonical.nmOrd_le_nmOrd_proj`).  This holds whichever form of (8) is chosen (I-1139).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.CompanionReductionAlong
  Hironaka.CompanionRebase Hironaka.GermIdealOrder
  Hironaka.DivisorExponentAlong Hironaka.BlowupTowers
  Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen
  Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderCanonical
  Hironaka.NonmonomialOrderTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Admissible centres of the companion ideal along its multiple test blow-ups -/

section Admissible

variable {Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Z}

/-- **Admissible centres of the companion's transform** (`𝔫` in the domain, `n > 0`, `o ≥ 1`, `ν ≤ o` on `cosupp 𝔫`):
along a multiple test blow-up `T` of `𝓞(𝔫, o)`, `C` is an admissible centre of `𝓞(𝔫, o)_T` iff it is an admissible centre of
`𝔫_T` contained in `{ν_{𝔫_T} ≥ o}`. -/
theorem isAdmissibleCentre_companion_iff (hn : 0 < n) (h : IsInvDomain k 𝔫) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔫.cosupp, x ∉ ordGe 𝔫 (o + 1)) {Y : CMfd.{u} n} (T : BlowupTower Z Y)
    (hT : IsGeoTestTower (companionOf n 𝔫 o) T) (C : Set Y) :
    (geoTransformAlong (companionOf n 𝔫 o) T).IsAdmissibleCentre C ↔
      (geoTransformAlong 𝔫 T).IsAdmissibleCentre C ∧ C ⊆ ordGe (geoTransformAlong 𝔫 T) o := by
  have hcos := cosupp_companionOf_geoTransformAlong hn h ho hbound T hT
  have hE := E_geoTransformAlong_congr (companionAlong_E 𝔫.N 𝔫.E (MonomialPartAlong.nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E)
    (MonomialPartAlong.monomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E) o 𝔫.d) T
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hcos] at h2
    rw [hE] at h3
    exact ⟨⟨h1, fun x hx => (h2 hx).2, h3⟩, fun x hx => (h2 hx).1⟩
  · rintro ⟨⟨h1, h2, h3⟩, hC⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [hcos]
      exact fun x hx => ⟨hC hx, h2 hx⟩
    · rw [hE]
      exact h3

/-- **Admissible centres of the companion's transform on an open set** (hypotheses of
`isAdmissibleCentre_companion_iff`): on every open `W''` of the last stage, `C ⊂ W''` is an admissible centre of the
restriction of `𝓞(𝔫, o)_T` iff it is one of the restriction of `𝔫_T` lying over `{ν_{𝔫_T} ≥ o}`. -/
theorem isAdmissibleCentre_pullback_val_companion_iff (hn : 0 < n) (h : IsInvDomain k 𝔫) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔫.cosupp, x ∉ ordGe 𝔫 (o + 1)) {Y : CMfd.{u} n} (T : BlowupTower Z Y)
    (hT : IsGeoTestTower (companionOf n 𝔫 o) T) (W'' : Opens Y) (C : Set W'') :
    (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong (companionOf n 𝔫 o) T)).IsAdmissibleCentre C ↔
      (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong 𝔫 T)).IsAdmissibleCentre C ∧
        ∀ x ∈ C, (x : Y) ∈ ordGe (geoTransformAlong 𝔫 T) o := by
  have hcos := cosupp_companionOf_geoTransformAlong hn h ho hbound T hT
  have hE := E_geoTransformAlong_congr (companionAlong_E 𝔫.N 𝔫.E (MonomialPartAlong.nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E)
    (MonomialPartAlong.monomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E) o 𝔫.d) T
  have hT𝔫 := (CompanionOpen.companionOf_reduction hn h.isWellFormed h.isNonzeroAlongAt ho hbound T hT).1
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT𝔫
  have hdomO := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (InvDomainCompanion.isInvDomain_companionAlong hn h ho) T hT
  have hcosO := cosupp_pullback_val (geoTransformAlong (companionOf n 𝔫 o) T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomO.isWellFormed.isCoherent hg)
    W''
  have hcos𝔫 := cosupp_pullback_val (geoTransformAlong 𝔫 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomT.isWellFormed.isCoherent hg)
    W''
  have hEp : (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong (companionOf n 𝔫 o) T)).E =
      (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong 𝔫 T)).E := by
    show List.map _ (geoTransformAlong (companionOf n 𝔫 o) T).E = List.map _ (geoTransformAlong 𝔫 T).E
    rw [hE]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hcosO, hcos] at h2
    rw [hEp] at h3
    refine ⟨⟨h1, fun x hx => ?_, h3⟩, fun x hx => (h2 hx).1⟩
    rw [hcos𝔫]
    exact (h2 hx).2
  · rintro ⟨⟨h1, h2, h3⟩, hC⟩
    refine ⟨h1, fun x hx => ?_, ?_⟩
    · rw [hcos𝔫] at h2
      rw [hcosO, hcos]
      exact ⟨hC x hx, h2 hx⟩
    · rw [hEp]
      exact h3

end Admissible

/-! ### Finitely many orders over a compact set -/

section Bound

/-- **The order of the nonmonomial part is bounded on a compact subset of `N`** (`𝔫` well formed and nonzero along `N`,
`n > 0`): it is upper semicontinuous (`NonmonomialOrderLocal.eventually_nmOrd_le`); a finite subcover gives the bound. -/
theorem exists_nmOrd_le_of_isCompact (hn : 0 < n) {M : CMfd.{u} n} {𝔫 : MarkedIdeal n M} (h𝔫 : 𝔫.IsWellFormed)
    (hne : ∀ y ∈ 𝔫.N, IsNonzeroAlongAt 𝔫.N 𝔫.ideal y) {K : Set M} (hK : IsCompact K) (hKN : K ⊆ 𝔫.N) :
    ∃ q : ℕ, ∀ y ∈ K, nmOrd 𝔫 y ≤ q := by
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover (fun y => {y' | nmOrd 𝔫 y' ≤ nmOrd 𝔫 y})
    fun y hy => eventually_nmOrd_le hn h𝔫 hne (hKN hy)
  refine ⟨t.sup (nmOrd 𝔫), fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
  exact (show nmOrd 𝔫 y ≤ nmOrd 𝔫 x from hyx).trans (Finset.le_sup (f := nmOrd 𝔫) hx)

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Over a compact set the order is bounded along every canonical segment** (`𝔪` in the domain, `n > 0`): for a compact
`K` of the base there is `q` such that along every multiple test blow-up `T` of `𝔪` which is a canonical segment of `f`
(whose order dominates `ν`), `ν ≤ q` at every point of `cosupp 𝔪_T` over `K` -- the image of such a point lies in
`cosupp 𝔪 ∩ K ⊂ N ∩ K`, compact, and the order never goes up along the segment
(`NonmonomialOrderCanonical.nmOrd_le_nmOrd_proj`). -/
theorem exists_nmOrd_le_of_isCompact_of_canonical (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {K : Set X} (hK : IsCompact K) :
    ∃ q : ℕ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → IsCanonical 𝔪 f T →
      ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, T.proj y ∈ K → nmOrd (geoTransformAlong 𝔪 T) y ≤ q := by
  obtain ⟨q, hq⟩ := exists_nmOrd_le_of_isCompact hn h.isWellFormed h.isNonzeroAlongAt
    (hK.inter_right h.isWellFormed.isClosedSubmanifold_N.1) Set.inter_subset_right
  refine ⟨q, fun T hT hcan y hy hyK => ?_⟩
  have hT' : IsGeoTestTower 𝔪 ((BlowupTower.refl : BlowupTower X X).append T) := by
    rw [BlowupTower.refl_append]
    exact hT
  have hcan' : IsCanonical 𝔪 f ((BlowupTower.refl : BlowupTower X X).append T) := by
    rw [BlowupTower.refl_append]
    exact hcan
  have hy' : y ∈ (geoTransformAlong 𝔪 ((BlowupTower.refl : BlowupTower X X).append T)).cosupp := by
    rw [BlowupTower.refl_append]
    exact hy
  obtain ⟨h1, h2⟩ := nmOrd_le_nmOrd_proj hn h hf .refl T hT' hcan' y hy'
  rw [BlowupTower.refl_append] at h2
  exact h2.trans (hq _ ⟨hyK, 𝔪.cosupp_subset_N h1⟩)

end Bound

end

end Hironaka.NonmonomialOrderPhase
