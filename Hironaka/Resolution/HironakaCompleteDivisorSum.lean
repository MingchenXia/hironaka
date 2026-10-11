/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSNCComponentCoefficients
import Hironaka.Resolution.HironakaConnectedBoundaryComponents
import Hironaka.Resolution.HironakaEffectiveDivisorSum
import Hironaka.Resolution.HironakaCanonicalPrincipalization
import Hironaka.Blowup.NormalCrossingsComparison

set_option autoImplicit false

/-!
# Complete actual divisor sums in canonical principalization

The actual connected-component refinement, factorization and original exponent
producers supply the sum; no decomposition certificate is an input.
Blueprint: `hironaka-complete-divisor-sum-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaCompleteDivisorSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealTotalTransform HironakaEffectiveDivisorSum HironakaConnectedBoundaryComponents
  HironakaSNCComponentCoefficients HironakaSNCSupportedMonomialIdeal DivisorExponent
  NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaAdmissibleSequence RestrictEmptyTower
  DivisorExponentAlong MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  CanonicalResolution BlowupTowerIsomorphism BlowupTowerTransforms
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsCanonical)
open ResolutionDriver (IsCanonicalSegment)

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A complete actual sum over the genuine connected components meeting the support. -/
def HasFiniteComponentSum (D : EffectiveDivisor n M) (E : List (Set M)) : Prop :=
  ∃ F : List (Set M), F.Nodup ∧
    (∀ C, C ∈ F ↔ C ∈ boundaryComponents E ∧ (C ∩ D.support).Nonempty) ∧
    IsSNCDivisor n F ∧
    ∃ A : List (Set M × ℕ), A.map Prod.fst = F ∧
      ∃ hA : ∀ p ∈ A, IsClosed p.1 ∧
        ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n,
        D = componentSum A hA ∧
        ∀ p ∈ A, ∀ x ∈ p.1, divExp n D.ideal p.1 x = p.2

/-- The full ideal and original coefficients produce an actual divisor sum. -/
theorem exists_componentSum (D : EffectiveDivisor n M) (F : List (Set M))
    (hF : IsSNCDivisor n F) (hnd : F.Nodup)
    (hconnected : ∀ W ∈ F, ∃ d, IsClosedConnectedSubmanifold n W d ∧ d + 1 = n)
    (hsupport : D.support ⊆ ⋃ W ∈ F, W) :
    ∃ A : List (Set M × ℕ), A.map Prod.fst = F ∧
      ∃ hA : ∀ p ∈ A, IsClosed p.1 ∧
        ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n,
        D = componentSum A hA ∧
        ∀ p ∈ A, ∀ x ∈ p.1, divExp n D.ideal p.1 x = p.2 := by
  obtain ⟨A, hAF, hD, hcoeff⟩ :=
    exists_componentPowerProduct_eq_original_exponents D F hF hnd hconnected hsupport
  have hA : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n := by
    intro p hp
    have hpF : p.1 ∈ F := by
      rw [← hAF]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨d, hgeom, hdn⟩ := hconnected p.1 hpF
    exact ⟨hgeom.1, fun x hx => ⟨d, hgeom.2.2 x hx, hdn⟩⟩
  exact ⟨A, hAF, hA, eq_componentSum_of_ideal_eq D A hA hD, hcoeff⟩

/-- Compact actual support selects and sums genuine connected SNC components. -/
theorem hasFiniteComponentSum_of_isCompact_support (D : EffectiveDivisor n M)
    {E : List (Set M)} (hE : IsSNCDivisor n E) (hK : IsCompact D.support)
    (hsupport : D.support ⊆ ⋃ H ∈ E, H) : HasFiniteComponentSum D E := by
  cases n with
  | zero =>
    have hBC := boundaryComponents_eq_empty_of_isSNCDivisor_zero hE
    have hempty : D.support = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp (hsupport hx)
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hW
      exact notMem_member_of_dim_zero E hE i x hxW
    have hunit := BlowupTowerTransforms.eq_unitIdeal_of_zeroLocus_eq_empty
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hempty
    have hA : ∀ p ∈ ([] : List (Set M × ℕ)), IsClosed p.1 ∧
        ∀ x ∈ p.1, ∃ d, RegularAtDim (n := 0) p.1 x d ∧ d + 1 = 0 := by simp
    refine ⟨[], List.nodup_nil, ?_, isSNCDivisor_nil, [], rfl, hA, ?_, ?_⟩
    · intro C
      simp [hBC]
    · exact effectiveDivisor_eq_of_ideal_eq hunit
    · simp
  | succ m =>
    obtain ⟨F, hnd, hmem, hF, hgeom, hKeq, -⟩ :=
      exists_finite_refinement_on_compact hE hK
    have hDF : D.support ⊆ ⋃ C ∈ F, C := by
      intro x hx
      have h : x ∈ D.support ∩ (⋃ C ∈ F, C) := by
        rw [hKeq]
        exact ⟨hx, hsupport hx⟩
      exact h.2
    obtain ⟨A, hAF, hA, hsum, hcoeff⟩ := exists_componentSum D F hF hnd
      (fun W hW => ⟨m, hgeom W hW, rfl⟩) hDF
    exact ⟨F, hnd, hmem, hF, A, hAF, hA, hsum, hcoeff⟩

/-- The same actual canonical principalization tower carries the complete divisor sum. -/
theorem exists_canonical_principalization_componentSum {X : CMfd.{u} n}
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x)
    (hZ : IsCompact 𝔞.zeroLocus) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y) (D : EffectiveDivisor n Y) (E : List (Set Y)),
      IsAdmissibleBlowupSequence n X E₀ 𝔞.zeroLocus Y T.proj E ∧
      GermIdeal.pullback (m := n) T.proj 𝔞 = D.ideal ∧ IsSNCDivisor n E ∧
      D.support = ⋃ H ∈ E.drop E₀.length, H ∧ D.support = T.proj ⁻¹' 𝔞.zeroLocus ∧
      IsIsomorphismOver n T.proj 𝔞.zeroLocusᶜ ∧
      IsGeoResolution (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X) T ∧
      IsCanonicalSegment (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)
        ((CanonicalCentres.canonicalInvariant n).inv (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)) T ∧
      (∀ U : Opens X, IsCanonical
        (pullback (Subtype.val : U → X) (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))
        ((CanonicalCentres.canonicalInvariant n).inv
          (pullback (Subtype.val : U → X) (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))) (restrict U T)) ∧
      (∀ {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
        {Y' : CMfd.{u} n} (T' : BlowupTower X' Y'),
        IsCanonicalSegment (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))
          ((CanonicalCentres.canonicalInvariant n).inv
            (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X))) T' →
        IsGeoResolution (pullback Φ (⟨univ, E₀, 𝔞, 1⟩ : MarkedIdeal n X)) T' →
        ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
          IsTowerIso Φ T' T χ) ∧ HasFiniteComponentSum D (E.drop E₀.length) := by
  obtain ⟨Y, T, D, E, hadm, hpb, hE, hnew, hsupp, hiso, hres, hseg, hopen, hbi⟩ :=
    HironakaCanonicalPrincipalization.exists_canonical_principalization_boundary h𝔞 hne hZ hE₀
  have hK : IsCompact D.support := by
    rw [hsupp]
    exact (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hZ
  have hEnew : IsSNCDivisor n (E.drop E₀.length) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hE (List.drop_sublist _ _)
  have hsum := hasFiniteComponentSum_of_isCompact_support D hEnew hK
    (fun _ hx => hnew ▸ hx)
  exact ⟨Y, T, D, E, hadm, hpb, hE, hnew, hsupp, hiso, hres, hseg, hopen, hbi, hsum⟩

end
end Hironaka.HironakaCompleteDivisorSum
