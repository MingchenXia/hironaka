import Hironaka.Resolution.HironakaHypersurfaceMultiplicityDescent
import Hironaka.Resolution.HironakaActualHypersurfaceBlowupHS
import Hironaka.Resolution.HironakaG11PresTowerState
import Hironaka.Resolution.HironakaG11InvTransport

/-!
# Hypersurface records: the powers of the vanishing ideal present the Hilbert–Samuel function

For a closed analytic subset `W` of pure codimension one of a complex manifold of dimension `n = m + 1`
(a hypersurface), the Hilbert–Samuel function of `W` at a point is the binomial profile of the order
`μ` of `𝓘_W` there (`hypersurfaceHS n μ`, the profile of `𝒪/(f)`, `ord f = μ`), and the marked ideal
`(univ, [], 𝓘_W, μ)` (`vanishingPowerRecord`) with `μ ≥ 2` the maximal order presents the maximal
Hilbert–Samuel value along every multiple test blow-up: its controlled transforms are the ideals of the
strict transforms (`HironakaHypersurfaceMultiplicityDescent.strictIdeal_and_geometry_geoTransformAlong`),
so its cosupport is the locus of order `μ` = the locus where the Hilbert–Samuel function equals
`hypersurfaceHS n μ`, and points of order `≥ 2` are singular.  This is lane G11C's `HSTowerState`
(G11 step (3a)) for these records, with no standard basis.

The record is DETERMINED BY THE CARRIER: it pulls back to the record of the preimage along open
holomorphic embeddings (`pullback_vanishingPowerRecord`), so after any biholomorphism carrying carrier
to carrier the two records are restricted-equivalent (`restrictEquiv_vanishingPowerRecord`), which is
what the naturality properties (5)–(7) of a resolution invariant need for the transport (3b)
(`HironakaG1RHypersurfaceWindows`).

* `hypersurfaceHS`, `hypersurfaceHS_mono`, `eq_of_hypersurfaceHS_eq`,
  `exists_order_hilbertSamuelAt_eq_hypersurfaceHS`;
* `vanishingPowerRecord`, `cosupp_vanishingPowerRecord`, `isInvDomain_vanishingPowerRecord`,
  `pullback_vanishingPowerRecord`, `restrictEquiv_vanishingPowerRecord`;
* `geoTransformAlong_vanishingPowerRecord`, **`hsTowerState_vanishingPowerRecord`**,
  `strictAlong_vanishingPowerRecord`.

Sources: Bierstone–Milman 1997 §1 and Remark 1.17 (the hypersurface case: the Hilbert–Samuel function
of a hypersurface is determined by the order; `(𝓘_W, μ)` is a presentation of the maximal stratum);
Hironaka 1964.  Blueprint: `hironaka-g1-r-hypersurface-record.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG1RHypersurfaceRecord

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
open HironakaHypersurfaceMultiplicityDescent HironakaG11PresTowerState HironakaHolomorphicJetChartInvariance
open HironakaEmbeddedAnalytic (singularSet mem_singularSet_iff)
open HomogenizedGlueingTower (strictAlong)
open MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)

noncomputable section

/-! ### The Hilbert–Samuel profile of a hypersurface -/

/-- **The Hilbert–Samuel profile of a hypersurface germ of order `μ` in `n` variables**:
`ℓ ↦ dim 𝒪/((f) + 𝔪^{ℓ+1}) = C(n+ℓ, n) − C(n+ℓ−μ, n)` (the second term `0` for `ℓ < μ`). -/
def hypersurfaceHS (n μ : ℕ) (ℓ : ℕ) : ℕ :=
  Nat.choose (n + ℓ) n - (if μ ≤ ℓ then Nat.choose (n + (ℓ - μ)) n else 0)

theorem hypersurfaceHS_mono (n : ℕ) {μ ν : ℕ} (h : μ ≤ ν) (ℓ : ℕ) :
    hypersurfaceHS n μ ℓ ≤ hypersurfaceHS n ν ℓ :=
  HironakaActualHypersurfaceBlowupHS.actual_principal_binomial_hs_mono n μ ν ℓ h

/-- **The profile determines the order.** -/
theorem eq_of_hypersurfaceHS_eq (n : ℕ) {μ ν : ℕ} (h : ∀ ℓ, hypersurfaceHS n μ ℓ = hypersurfaceHS n ν ℓ) :
    μ = ν := by
  have key : ∀ {a b : ℕ}, a < b → hypersurfaceHS n a a ≠ hypersurfaceHS n b a := by
    intro a b hab heq
    have h1 : hypersurfaceHS n a a = Nat.choose (n + a) n - 1 := by
      simp [hypersurfaceHS]
    have h2 : hypersurfaceHS n b a = Nat.choose (n + a) n := by
      simp [hypersurfaceHS, show ¬ b ≤ a by omega]
    have hpos : 0 < Nat.choose (n + a) n := Nat.choose_pos (by omega)
    omega
  rcases lt_trichotomy μ ν with hlt | heq | hgt
  · exact absurd (h μ) (key hlt)
  · exact heq
  · exact absurd (h ν).symm (key hgt)

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The Hilbert–Samuel function of an invertible ideal is the hypersurface profile of its order.** -/
theorem exists_order_hilbertSamuelAt_eq_hypersurfaceHS (A : GermIdeal n M) (hA : A.IsInvertible) (x : M) :
    ∃ μ : ℕ, order n univ A x = (μ : ℕ∞) ∧ ∀ ℓ, hilbertSamuelAt A x ℓ = hypersurfaceHS n μ ℓ :=
  HironakaActualInvertibleIntrinsicHS.exists_actual_original_order_intrinsic_hs A hA x

/-! ### The records -/

variable (n) in
/-- **The `μ`-th vanishing-ideal record** `(univ, [], 𝓘_C, μ)` of a subset `C`. -/
def vanishingPowerRecord (C : Set M) (μ : ℕ) : MarkedIdeal n M :=
  ⟨univ, [], vanishingIdeal (n := n) C, μ⟩

omit [IsComplexManifold n M] in
/-- The cosupport of the `μ`-th vanishing-ideal record is the locus where `𝓘_C` has order `≥ μ`. -/
theorem cosupp_vanishingPowerRecord (C : Set M) (μ : ℕ) :
    (vanishingPowerRecord n C μ).cosupp = {x | (μ : ℕ∞) ≤ order n univ (vanishingIdeal (n := n) C) x} := by
  ext x
  change x ∈ cosupport n univ (vanishingIdeal (n := n) C) μ ↔ _
  simp only [cosupport, mem_ofPred_eq, mem_univ, true_and]
  exact (le_order_iff (𝔞 := vanishingIdeal (n := n) C) (fun _ hg => hg.1)).symm

/-- The `μ`-th vanishing-ideal record of an analytic set without interior is in the domain of the
invariants of index `n` (for `μ ≥ 1`). -/
theorem isInvDomain_vanishingPowerRecord {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) {μ : ℕ} (hμ : 1 ≤ μ) :
    ResolutionInvariantSpec.IsInvDomain n (vanishingPowerRecord n W μ) := by
  have hd1 := HironakaEmbeddedBoundary.isInvDomain_boundary hWa hint (E₀ := [])
    NormalCrossings.isSNCDivisor_nil
  exact ⟨⟨hd1.isWellFormed.isClosedSubmanifold_N, hd1.isWellFormed.isCoherent,
      hd1.isWellFormed.isSNCDivisor, hd1.isWellFormed.isTransverse⟩,
    hd1.dimLE, hμ, hd1.isNonzeroAlongAt⟩

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **The record is determined by the carrier**: it pulls back to the record of the preimage along open
holomorphic embeddings (in particular inclusions of opens and biholomorphisms). -/
theorem pullback_vanishingPowerRecord (b : M' → M) (hb : HironakaBaseChange.IsOpenHoloEmbedding n b)
    (C : Set M) (μ : ℕ) :
    MarkedIdealBiholomorphism.MarkedIdeal.pullback b (vanishingPowerRecord n C μ) =
      vanishingPowerRecord n (b ⁻¹' C) μ :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_isOpenHoloEmbedding b hb C) rfl

/-- **Records of corresponding carriers are restricted-equivalent after transport**: for a
biholomorphism `Φ : M' ≅ M` with `Φ⁻¹C = C'` (and coherent `𝓘_{C'}`), `Φ^*(univ, [], 𝓘_C, μ)` and
`(univ, [], 𝓘_{C'}, μ)` are equal, hence restricted-equivalent. -/
theorem restrictEquiv_vanishingPowerRecord
    (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) {C : Set M} {C' : Set M'}
    (hC : Φ ⁻¹' C = C') (hcoh : (vanishingIdeal (n := n) C').IsCoherent) (μ : ℕ) :
    RestrictEquiv (MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ (vanishingPowerRecord n C μ))
      (vanishingPowerRecord n C' μ) := by
  have h : MarkedIdealBiholomorphism.MarkedIdeal.pullback Φ (vanishingPowerRecord n C μ) =
      vanishingPowerRecord n (Φ ⁻¹' C) μ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
      (HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_biholomorphism Φ C) rfl
  rw [h, hC]
  exact MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv.refl hcoh

end

/-! ### The presentation along multiple test blow-ups -/

section TowerState

variable {m : ℕ} {X : CMfd.{u} (m + 1)}

/-- **The geometry of the transforms of a hypersurface record along its test towers**: for `W`
analytic of pure dimension `m` in an `(m + 1)`-manifold, `2 ≤ μ` and `ord_x 𝓘_W ≤ μ` on `W`, along every
multiple test blow-up `T` of `(univ, [], 𝓘_W, μ)` the strict transform `W_T = strictTransform T.proj W` is
analytic, of pure dimension `m`, with invertible vanishing ideal of order `≤ μ` everywhere; the
transformed cosupport is the locus of order `≥ μ` of `𝓘_{W_T}` and lies in the singular set of `W_T`. -/
theorem geoTransformAlong_vanishingPowerRecord {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞))
    {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower (vanishingPowerRecord (m + 1) W μ) T) :
    IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) T.proj W) ∧
    strictTransform (m + 1) T.proj W ⊆
      closure (regularLocus (n := m + 1) (strictTransform (m + 1) T.proj W) m) ∧
    (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)).IsInvertible ∧
    (∀ z, order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) z ≤
      (μ : ℕ∞)) ∧
    (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).cosupp =
      {z | (μ : ℕ∞) ≤ order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) z} ∧
    (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).cosupp ⊆
      singularSet (n := m + 1) (strictTransform (m + 1) T.proj W) := by
  have hI := HironakaPureCodimensionOneInvertibleIdeal.isInvertible_vanishingIdeal_of_pure hWa hpure
  obtain ⟨hSa, hSpure, hSI, hTI, hmax⟩ :=
    strictIdeal_and_geometry_geoTransformAlong hWa hI hpure NormalCrossings.isSNCDivisor_nil hμ hbound T hT
  have hcoh : (vanishingPowerRecord (m + 1) W μ).ideal.IsCoherent := CartanIrreducible.cartanCoherence W hWa
  obtain ⟨hNT, -, -⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := vanishingPowerRecord (m + 1) W μ) rfl hcoh T hT
  change (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).ideal = _ at hTI
  change MaximalContact.IsMaximalOrder (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).ideal μ at hmax
  have hord : ∀ z, order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) z ≤
      (μ : ℕ∞) := fun z => by
    rw [← hTI]
    exact order_le_of_isMaximalOrder hmax z
  have hcos : (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).cosupp =
      {z | (μ : ℕ∞) ≤ order (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) z} := by
    have hM : geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T =
        (⟨univ, (geoTransformAlong (vanishingPowerRecord (m + 1) W μ) T).E,
          vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W), μ⟩ : MarkedIdeal (m + 1) Y) :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of hNT rfl hTI (d_geoTransformAlong _ T)
    rw [hM]
    ext z
    change z ∈ cosupport (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) μ ↔ _
    simp only [cosupport, mem_ofPred_eq, mem_univ, true_and]
    exact (le_order_iff (𝔞 := vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W))
      (fun _ hg => hg.1)).symm
  refine ⟨hSa, hSpure, hSI, hord, hcos, ?_⟩
  intro z hz
  rw [hcos] at hz
  have hz' : z ∈ cosupport (m + 1) univ (vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W)) μ :=
    ⟨mem_univ z, (le_order_iff (𝔞 := vanishingIdeal (n := m + 1) (strictTransform (m + 1) T.proj W))
      (fun _ hg => hg.1)).mp hz⟩
  have h1 := HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus hSa.isClosed
    (Nat.lt_succ_self m) hμ hz'
  rw [HironakaEmbeddedReducible.diff_regularLocus_eq_of_pure hSpure] at h1
  exact mem_singularSet_iff.mpr h1

/-- **The maximal-order record of a hypersurface presents the maximal Hilbert–Samuel value along all
multiple test blow-ups** (G11 step (3a) for hypersurfaces): for `W` analytic of pure dimension `m` in
an `(m + 1)`-manifold, `2 ≤ μ` and `ord_x 𝓘_W ≤ μ` on `W`, the record `(univ, [], 𝓘_W, μ)` satisfies
`HSTowerState` for the value `hypersurfaceHS (m + 1) μ`. -/
theorem hsTowerState_vanishingPowerRecord {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞)) :
    HSTowerState (vanishingPowerRecord (m + 1) W μ) W (hypersurfaceHS (m + 1) μ) := by
  apply hsTowerState_of_strictTransform _ hWa.isClosed
  intro Y T hT
  obtain ⟨hSa, -, hSI, hord, hcos, hsing⟩ :=
    geoTransformAlong_vanishingPowerRecord hWa hpure hμ hbound T hT
  refine ⟨hSa, fun z ℓ => ?_, ?_, hsing⟩
  · obtain ⟨ν, hν, hHS⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS _ hSI z
    rw [hHS ℓ]
    apply hypersurfaceHS_mono
    have h := hord z
    rw [hν] at h
    exact_mod_cast h
  · rw [hcos]
    ext z
    obtain ⟨ν, hν, hHS⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS _ hSI z
    have h2 := hord z
    rw [hν] at h2
    simp only [mem_ofPred_eq, hν]
    constructor
    · intro h ℓ
      have : ν = μ := le_antisymm (by exact_mod_cast h2) (by exact_mod_cast h)
      rw [hHS ℓ, this]
    · intro h
      have := eq_of_hypersurfaceHS_eq (m + 1) (fun ℓ => (hHS ℓ).symm.trans (h ℓ))
      rw [this]

/-- **The iterated geometric strict transforms along the test towers of a hypersurface record** are the
strict transforms, analytic and of pure dimension `m`. -/
theorem strictAlong_vanishingPowerRecord {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, order (m + 1) univ (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞))
    {Y : CMfd.{u} (m + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower (vanishingPowerRecord (m + 1) W μ) T) :
    strictAlong T W = strictTransform (m + 1) T.proj W ∧
      IsComplexAnalyticSubset (n := m + 1) (strictAlong T W) ∧
      strictAlong T W ⊆ closure (regularLocus (n := m + 1) (strictAlong T W) m) := by
  have heq := strictAlong_eq_strictTransform_of_singular (vanishingPowerRecord (m + 1) W μ) hWa.isClosed
    (fun T hT => ⟨(geoTransformAlong_vanishingPowerRecord hWa hpure hμ hbound T hT).1,
      (geoTransformAlong_vanishingPowerRecord hWa hpure hμ hbound T hT).2.2.2.2.2⟩) T hT
  obtain ⟨hSa, hSpure, -⟩ := geoTransformAlong_vanishingPowerRecord hWa hpure hμ hbound T hT
  rw [heq]
  exact ⟨rfl, hSa, hSpure⟩

end TowerState

end Hironaka.HironakaG1RHypersurfaceRecord
