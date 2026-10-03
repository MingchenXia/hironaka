/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialPartEtale
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.IdealPowers
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion ideal of the general step: functoriality and re-basing across steps empty near the point

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` ("By Step 1 we can resolve the
marked ideal of maximal order `O(𝓘, μ)` ... Then we repeat the procedure") and §2.4 (commutativity with étale
morphisms); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

At a point where the order `o` of the nonmonomial part is positive, the general step computes the value from the
maximal-order invariant of the companion ideal
`𝓞(𝔪, o) = (N, E, 𝓝_N(𝔞), o) + (N, E, 𝓜_N(𝔞), d - o)` (`o < d`), resp. `(N, E, 𝓝_N(𝔞), o)` (`o ≥ d`)
(`companionOf`, an abbreviation of `CompanionReductionAlong.companionAlong` at the parts of `MonomialPartAlong`), formed
at the stage where `o` was first reached near the point and restricted to an open set.  Nearby points with different
start stages are compared by re-basing (property (4') of `ResolutionInvariantExt.ResolutionInvariant`): between the two
stages the centres miss the open set (`RestrictEmptyTower`), and the companion ideal formed at the earlier stage,
transformed along those steps, must be the one formed at the later stage.  This module proves that, up to restricted
equivalence, with the domain and the identity of values, and the functoriality of `𝓞` it rests on.

## Main results

* `companionAlong_ideal`, `companionAlong_d`, **`pullback_companionAlong`**: the companion of a factorization commutes with
  pullback along a holomorphic map (coherent factors);
* **`pullback_companionOf_of_local`**: `φ^*𝓞(𝔪, o) = 𝓞(φ^*𝔪, o)` for a local biholomorphism `φ` (`𝔪` well formed and
  nonzero along `N`); `pullback_val_companionOf` (**open sets**), `pullback_diffeo_companionOf` (**biholomorphisms**);
* **`companionOf_congr`**: restricted-equivalent marked ideals have the same companion ideal (property (7));
* **`restrictEquiv_companionOf_geoTransform_empty`**: across a step with empty centre, `𝓞(𝔪', o) ≃ 𝓞(𝔪, o)'`;
* `restrictEquiv_companionOf_geoTransformAlong_of_isEmptyTower`: along a tower with only empty centres;
* **`restrictEquiv_companionOf_rebase`**: for `T` a multiple test blow-up of `𝔪` whose centres miss the open `W`,
  `𝓞(𝔪_T, o)|_{T⁻¹W} ≃ (𝓞(𝔪, o)|_W)_{T|_W}`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.CompanionRebase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.MonomialPartEtale Hironaka.IdealWeightPowers Hironaka.RestrictedIdealExtension Hironaka.DerivativeIdealAlongEtale Hironaka.RestrictedIdealWeight Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.MarkedIdealOperationsTransform.MarkedIdeal Hironaka.DivisorExponentAlong Hironaka.BlowupTowers

noncomputable section

variable {n : ℕ}

/-! ### The companion of a factorization -/

section Factorization

variable {M : CMfd.{u} n}

/-- The ideal of the companion: `𝔟^{d - o} + 𝔠^o` if `o < d`, and `𝔟` otherwise. -/
theorem companionAlong_ideal (N : Set M) (E : List (Set M)) (𝔟 𝔠 : GermIdeal n M) (o d : ℕ) :
    (companionAlong N E 𝔟 𝔠 o d).ideal = if o < d then sumIdeal (idealPow 𝔟 (d - o)) (idealPow 𝔠 o) else 𝔟 := by
  unfold companionAlong
  split_ifs <;> rfl

/-- The mark of the companion: `o (d - o)` if `o < d`, and `o` otherwise. -/
theorem companionAlong_d (N : Set M) (E : List (Set M)) (𝔟 𝔠 : GermIdeal n M) (o d : ℕ) :
    (companionAlong N E 𝔟 𝔠 o d).d = if o < d then o * (d - o) else o := by
  unfold companionAlong
  split_ifs <;> rfl

variable {M' : CMfd.{u} n}

/-- **The companion of a factorization commutes with pullback** along a holomorphic map (coherent factors):
`φ^*((N, E, 𝔟, o) + (N, E, 𝔠, d - o)) = (φ⁻¹N, φ⁻¹E, φ^*𝔟, o) + (φ⁻¹N, φ⁻¹E, φ^*𝔠, d - o)`, resp. the single term. -/
theorem pullback_companionAlong {φ : M' → M} (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    {𝔟 𝔠 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent) (N : Set M) (E : List (Set M)) (o d : ℕ) :
    MarkedIdeal.pullback φ (companionAlong N E 𝔟 𝔠 o d) =
      companionAlong (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ 𝔟)
        (GermIdeal.pullback (m := n) φ 𝔠) o d := by
  refine ext_of ?_ ?_ ?_ ?_
  · simp [MarkedIdeal.pullback]
  · simp [MarkedIdeal.pullback]
  · show GermIdeal.pullback (m := n) φ (companionAlong N E 𝔟 𝔠 o d).ideal = _
    rw [companionAlong_ideal, companionAlong_ideal]
    split_ifs
    · rw [MarkedIdealOperationsTransform.pullback_sumIdeal hφ
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          (GermIdealPullbackCalculus.isCoherent_idealPow h𝔟 _) hg)
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          (GermIdealPullbackCalculus.isCoherent_idealPow h𝔠 _) hg),
        BlowupExceptionalDivisor.pullback_idealPow hφ h𝔟, BlowupExceptionalDivisor.pullback_idealPow hφ h𝔠]
    · rfl
  · show (companionAlong N E 𝔟 𝔠 o d).d = _
    rw [companionAlong_d, companionAlong_d]

end Factorization

/-! ### The companion ideal of a marked ideal -/

section Companion

variable {M : CMfd.{u} n}

variable (n) in
/-- **The companion ideal** `𝓞(𝔪, o)` of `𝔪 = (M, N, E, 𝔞, d)` with order `o` (`hir:companion-ideal`):
`CompanionReductionAlong.companionAlong` at the nonmonomial and monomial parts along `N`
(`MonomialPartAlong.nonmonomialPartAlong`, `monomialPartAlong`); an abbreviation, the form used by
`InvDomainCompanion` and `InvDomainRebase`. -/
abbrev companionOf (𝔪 : MarkedIdeal n M) (o : ℕ) : MarkedIdeal n M :=
  companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d

/-- **Restricted-equivalent marked ideals have the same companion ideal** (property (7) at the level of the ideal; `N`
closed): the parts only depend on `Res_N 𝔞` (`MonomialPartEtale.monomialPartAlong_congr`, `nonmonomialPartAlong_congr`). -/
theorem companionOf_congr {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (o : ℕ) :
    companionOf n 𝔪 o = companionOf n 𝔫 o := by
  have hM := monomialPartAlong_congr (E := 𝔪.E) h.le h.ge
  have hNN := nonmonomialPartAlong_congr (E := 𝔪.E) hN h.le h.ge
  simp only [companionOf]
  rw [← h.N_eq, ← h.E_eq, ← h.d_eq, hM, hNN]

variable {M' : CMfd.{u} n}

/-- **The companion ideal commutes with pullback along a local biholomorphism** (a holomorphic map with a local inverse at
every point): `φ^*𝓞(𝔪, o) = 𝓞(φ^*𝔪, o)` for `𝔪` well formed and nonzero along `N` (`n > 0`). -/
theorem pullback_companionOf_of_local (hn : 0 < n) {φ : M' → M}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (o : ℕ) :
    MarkedIdeal.pullback φ (companionOf n 𝔪 o) = companionOf n (MarkedIdeal.pullback φ 𝔪) o := by
  have hN := h𝔪.isClosedSubmanifold_N
  have hE := h𝔪.isSNCDivisor
  have hT := h𝔪.isTransverse
  have h𝔞 := h𝔪.isCoherent
  have hM := isCoherent_monomialPartAlong hn hN hE hT h𝔞 hne
  have hNN := isCoherent_nonmonomialPartAlong hn hN hE hT h𝔞 hne
  simp only [companionOf]
  rw [pullback_companionAlong hφ hNN hM, pullback_nonmonomialPartAlong hloc h𝔞 hM hNN,
    pullback_monomialPartAlong hloc
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)]
  rfl

/-- **The companion ideal commutes with restriction to open sets**: `𝓞(𝔪, o)|_U = 𝓞(𝔪|_U, o)`. -/
theorem pullback_val_companionOf (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (U : Opens M) (o : ℕ) :
    MarkedIdeal.pullback (Subtype.val : U → M) (companionOf n 𝔪 o) =
      companionOf n (M := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) o :=
  pullback_companionOf_of_local (M' := CMfd.of (n := n) U) hn contMDiff_subtype_val (fun y => ⟨openInv U y, isLocalInverseAt_val U y⟩) h𝔪
    hne o

/-- A biholomorphism is a local biholomorphism, with local inverse its inverse. -/
theorem isLocalInverseAt_diffeo (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M) (y : M') :
    IsLocalInverseAt n Φ Φ.symm y :=
  ⟨Eventually.of_forall fun p => (Φ.contMDiff p).mdifferentiableAt (by simp),
    Eventually.of_forall fun q => (Φ.symm.contMDiff q).mdifferentiableAt (by simp),
    Eventually.of_forall fun p => Φ.symm_apply_apply p, Eventually.of_forall fun q => Φ.apply_symm_apply q⟩

/-- **The companion ideal commutes with biholomorphisms**: `Φ^*𝓞(𝔪, o) = 𝓞(Φ^*𝔪, o)`. -/
theorem pullback_diffeo_companionOf (hn : 0 < n) (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)
    {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed) (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (o : ℕ) :
    MarkedIdeal.pullback Φ (companionOf n 𝔪 o) = companionOf n (MarkedIdeal.pullback Φ 𝔪) o :=
  pullback_companionOf_of_local hn Φ.contMDiff (fun y => ⟨Φ.symm, isLocalInverseAt_diffeo Φ y⟩) h𝔪 hne o

end Companion

/-! ### Steps with empty centre -/

section EmptyStep

open BlowupStrictSubmanifold ContactCanonicalAlong

variable {Y Z : CMfd.{u} n} {π : Z → Y}

/-- **The companion ideal across a step with empty centre**: for the blowup `π` along `∅` and `𝔪` well formed and nonzero
along `N` (`n > 0`), the companion ideal of the transform is restricted-equivalent to the transform of the companion ideal,
`𝓞(𝔪', o) ≃ 𝓞(𝔪, o)'`.  Both have the submanifold `π⁻¹N` and the divisor `π⁻¹E ++ [∅]`; on `π⁻¹N` the transform of `𝔞` is
`π^*𝔞` (`ContactCanonicalAlong`), whose parts are the pullbacks of those of `𝔞` (`MonomialPartEtale`), and the empty
member changes neither part. -/
theorem restrictEquiv_companionOf_geoTransform_empty (hn : 0 < n) (𝔪 : MarkedIdeal n Y) (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hπ : IsBlowupAlong n (∅ : Set Y) π) (o : ℕ) :
    RestrictEquiv (companionOf n (𝔪.geoTransform ∅ π) o) ((companionOf n 𝔪 o).geoTransform ∅ π) := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hloc := exists_isLocalInverseAt_of_isBlowupAlong_empty hπ
  have hN := h𝔪.isClosedSubmanifold_N
  have hE := h𝔪.isSNCDivisor
  have hT := h𝔪.isTransverse
  have h𝔞 := h𝔪.isCoherent
  have hM := isCoherent_monomialPartAlong hn hN hE hT h𝔞 hne
  have hNN := isCoherent_nonmonomialPartAlong hn hN hE hT h𝔞 hne
  have hN' : (𝔪.geoTransform ∅ π).N = π ⁻¹' 𝔪.N := geoStrictTransform_empty hπc hN.1
  have hN'c : IsClosed (𝔪.geoTransform ∅ π).N := by rw [hN']; exact hN.1.preimage hπc
  have hE' : (𝔪.geoTransform ∅ π).E = 𝔪.E.map (π ⁻¹' ·) ++ [∅] := by
    rw [geoTransform_E, preimage_empty]
    congr 1
    exact List.map_congr_left fun H hH => geoStrictTransform_empty hπc (hE.1 H hH)
  have hle1 := restrictLe_geoTransform_empty_le_pullback hπ 𝔪
  have hle2 := restrictLe_pullback_le_geoTransform (π := π) ∅ 𝔪
  -- the companion ideal of the transform, with the parts pulled back
  have h1 : companionOf n (𝔪.geoTransform ∅ π) o =
      companionAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).E
        (GermIdeal.pullback (m := n) π (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E))
        (GermIdeal.pullback (m := n) π (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)) o 𝔪.d := by
    simp only [companionOf]
    rw [monomialPartAlong_congr hle1 hle2, nonmonomialPartAlong_congr hN'c hle1 hle2,
      pullback_nonmonomialPartAlong hloc h𝔞 hM hNN,
      pullback_monomialPartAlong hloc
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg),
      hN', hE', monomialPartAlong_append_empty, nonmonomialPartAlong_append_empty]
    rfl
  -- its ideal is the pullback of the ideal of the companion
  have hI : (companionOf n (𝔪.geoTransform ∅ π) o).ideal = GermIdeal.pullback (m := n) π (companionOf n 𝔪 o).ideal := by
    rw [h1]
    have h2 := congrArg MarkedIdeal.ideal (pullback_companionAlong hπ.contMDiff hNN hM 𝔪.N 𝔪.E o 𝔪.d)
    rw [companionAlong_ideal] at h2 ⊢
    exact h2.symm
  have hNeq : (companionOf n (𝔪.geoTransform ∅ π) o).N = ((companionOf n 𝔪 o).geoTransform ∅ π).N := by
    simp only [companionOf, companionAlong_N, geoTransform_N]
  have hEeq : (companionOf n (𝔪.geoTransform ∅ π) o).E = ((companionOf n 𝔪 o).geoTransform ∅ π).E := by
    simp only [companionOf, companionAlong_E, geoTransform_E]
  have hdeq : (companionOf n (𝔪.geoTransform ∅ π) o).d = ((companionOf n 𝔪 o).geoTransform ∅ π).d := by
    simp only [companionOf, companionAlong_d, geoTransform_d]
  refine ⟨hNeq, hEeq, hdeq, ?_, ?_⟩
  · rw [hI, hNeq]
    exact restrictLe_pullback_le_geoTransform (π := π) ∅ (companionOf n 𝔪 o)
  · rw [hI, hNeq]
    exact restrictLe_geoTransform_empty_le_pullback hπ (companionOf n 𝔪 o)

end EmptyStep

/-! ### Along towers with only empty centres, and re-basing -/

section Tower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open BlowupTowers BlowupTowerTransforms MarkedIdealRestrictOpen ResolutionInvariantExt RestrictEmptyTower InvDomainCompanion InvDomainRebase

variable {X : CMfd.{u} n}

/-- **The companion ideal along a tower with only empty centres**: for `𝔪` in the domain (`n > 0`, `o ≥ 1`) and `T` a
sequence of blowups along `∅`, `𝓞(𝔪_T, o) ≃ 𝓞(𝔪, o)_T`. -/
theorem restrictEquiv_companionOf_geoTransformAlong_of_isEmptyTower (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T →
      RestrictEquiv (companionOf n (geoTransformAlong 𝔪 T) o) (geoTransformAlong (companionOf n 𝔪 o) T)
  | _, .refl, _ => RestrictEquiv.refl (isInvDomain_companionAlong hn h ho).isWellFormed.isCoherent
  | _, .step T C π hπ, hT => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      have hdomT := isInvDomain_geoTransformAlong_of_isEmptyTower h T hT
      have hK := restrictEquiv_companionOf_geoTransform_empty hn (geoTransformAlong 𝔪 T) hdomT.isWellFormed
        hdomT.isNonzeroAlongAt hπ o
      have ih := restrictEquiv_companionOf_geoTransformAlong_of_isEmptyTower hn h ho T hT
      have hcT := isInvDomain_companionAlong hn hdomT ho
      have hcT' := isInvDomain_geoTransformAlong_of_isEmptyTower (isInvDomain_companionAlong hn h ho) T hT
      have heq := ih.geoTransform_eq hcT.isWellFormed.isClosedSubmanifold_N.1 hcT.isWellFormed.isCoherent
        hcT'.isWellFormed.isCoherent (C := ∅) hπ.contMDiff
      show RestrictEquiv (companionOf n ((geoTransformAlong 𝔪 T).geoTransform ∅ π) o)
        ((geoTransformAlong (companionOf n 𝔪 o) T).geoTransform ∅ π)
      rw [← heq]
      exact hK

/-- **Re-basing the companion ideal across steps that are empty over an open set**: for `𝔪` in the domain (`n > 0`,
`o ≥ 1`), `T` a multiple test blow-up of `𝔪` whose centres miss the open `W` (`RestrictEmptyTower.CentresAvoid`), the
companion ideal formed at the last stage, restricted to the open preimage of `W`, is restricted-equivalent to the companion
ideal formed at the first stage, restricted to `W` and transformed along the restricted tower `T|_W` (whose centres are
empty): `𝓞(𝔪_T, o)|_{T⁻¹W} ≃ (𝓞(𝔪, o)|_W)_{T|_W}`. -/
theorem restrictEquiv_companionOf_rebase (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (W : Opens X)
    (hW : CentresAvoid W T) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y) (companionOf n (geoTransformAlong 𝔪 T) o))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) (companionOf n 𝔪 o)) (restrict W T)) := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hW' := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hK := restrictEquiv_companionOf_geoTransformAlong_of_isEmptyTower (X := CMfd.of (n := n) W) hn hW' ho
    (restrict W T) he
  rw [geoTransformAlong_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT] at hK
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  rw [← pullback_val_companionOf hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T W) o,
    ← pullback_val_companionOf hn h.isWellFormed h.isNonzeroAlongAt W o] at hK
  exact hK

end Tower

end

end Hironaka.CompanionRebase
