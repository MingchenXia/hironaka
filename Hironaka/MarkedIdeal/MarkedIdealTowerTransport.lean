/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Transport of multiple test blow-ups along a biholomorphism of the base

Sources: Włodarczyk 2005 §2.4 (Proposition `pr:funct`: multiple test blow-ups and resolutions pull back along étale
maps; here biholomorphisms), Bierstone--Milman 2008 Theorem 1.3 (functoriality); the canonicity clause (3) of
`hir:canonical-resolution`.

Let `Φ : X' ≃ₘ⟮𝓘(ℂ, ℂⁿ), 𝓘(ℂ, ℂⁿ)⟯ X` be a biholomorphism (Mathlib's `Diffeomorph`, smooth of order `∞`
for the complex model with corners) and `𝔪` a marked ideal on `X` with coherent ideal.

## Invariance under biholomorphisms

* `isSNCDivisor_map_preimage_iff`, `hasNormalCrossings_preimage_iff`, `isTransverse_preimage_iff`,
  `isClosedSubmanifold_preimage_iff`: the normal crossings notions and closed submanifolds are invariant;
* `cosupp_pullback_eq`, `isAdmissibleCentre_pullback_iff`: `Φ⁻¹C` is an admissible centre of `Φ^*𝔪` iff `C` is
  one of `𝔪`;
* `IsWellFormed.pullback`: `Φ^*𝔪` is well formed if `𝔪` is.

## Transport of towers

`transport Φ T` (a `TowerTransport`) is the tower over `X'` with the same stages `Y₁, …, Y_r` as `T`, the first
blowup `σ₁ : Y₁ → X` replaced by `Φ⁻¹ ∘ σ₁ : Y₁ → X'` (a blowup along `Φ⁻¹C₁`,
`MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse`) and the later ones unchanged; its field `back` is the
biholomorphism of the last stages (`Φ` for the empty tower, the identity otherwise).  Stage by stage:
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealTowerTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.GermIdealPullbackCalculus

noncomputable section

/-! ### Invariance under biholomorphisms -/

section Invariance

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  (Φ : M' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ M)

/-- A biholomorphism has no exceptional points. -/
theorem notMem_exceptionalLocus (p : M') : p ∉ exceptionalLocus n Φ :=
  notMem_exceptionalLocus_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply p

/-- A biholomorphism pulls back adapted coordinates. -/
theorem pullsBackCoordinates : PullsBackCoordinates n Φ :=
  pullsBackCoordinates_of_forall_notMem_exceptionalLocus Φ.contMDiff (notMem_exceptionalLocus Φ)

/-- `Φ⁻¹(Φ⁻¹⁻¹ A) = A`. -/
theorem symm_preimage_preimage (A : Set M) : Φ.symm ⁻¹' (Φ ⁻¹' A) = A := by
  ext x
  simp

/-- Mapping a list of sets by `Φ⁻¹` and back. -/
theorem map_symm_preimage_map_preimage (E : List (Set M)) :
    (E.map (Φ ⁻¹' ·)).map (Φ.symm ⁻¹' ·) = E := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id E]
  exact List.map_congr_left fun A _ => symm_preimage_preimage Φ A

/-- **Closed submanifolds are invariant.** -/
theorem isClosedSubmanifold_preimage_iff {C : Set M} :
    IsClosedSubmanifold n (Φ ⁻¹' C) ↔ IsClosedSubmanifold n C := by
  refine ⟨fun h => ?_, isClosedSubmanifold_preimage Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
    Φ.symm_apply_apply⟩
  have := isClosedSubmanifold_preimage Φ.symm.contMDiff Φ.contMDiff Φ.symm_apply_apply
    Φ.apply_symm_apply h
  rwa [symm_preimage_preimage] at this

/-- **Simple normal crossings divisors are invariant.** -/
theorem isSNCDivisor_map_preimage_iff {E : List (Set M)} :
    IsSNCDivisor n (E.map (Φ ⁻¹' ·)) ↔ IsSNCDivisor n E := by
  refine ⟨fun h => ?_, isSNCDivisor_map_preimage (pullsBackCoordinates Φ) Φ.continuous⟩
  have := isSNCDivisor_map_preimage (pullsBackCoordinates Φ.symm) Φ.symm.continuous h
  rwa [map_symm_preimage_map_preimage] at this

/-- **Normal crossings are invariant.** -/
theorem hasNormalCrossings_preimage_iff {C : Set M} {E : List (Set M)} :
    HasNormalCrossings n (Φ ⁻¹' C) (E.map (Φ ⁻¹' ·)) ↔ HasNormalCrossings n C E := by
  refine ⟨fun h => ?_, hasNormalCrossings_preimage (pullsBackCoordinates Φ)⟩
  have := hasNormalCrossings_preimage (pullsBackCoordinates Φ.symm) h
  rwa [map_symm_preimage_map_preimage, symm_preimage_preimage] at this

/-- **Transversality is invariant.** -/
theorem isTransverse_preimage_iff {N : Set M} {E : List (Set M)} :
    IsTransverse n (Φ ⁻¹' N) (E.map (Φ ⁻¹' ·)) ↔ IsTransverse n N E := by
  refine ⟨fun h => ?_, isTransverse_preimage (pullsBackCoordinates Φ)⟩
  have := isTransverse_preimage (pullsBackCoordinates Φ.symm) h
  rwa [map_symm_preimage_map_preimage, symm_preimage_preimage] at this

variable {Φ}

/-- **Cosupports are invariant** (any `N`, coherent ideal). -/
theorem cosupp_pullback_eq {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent) :
    (MarkedIdeal.pullback Φ 𝔪).cosupp = Φ ⁻¹' 𝔪.cosupp :=
  MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply 𝔪
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg

/-- **Admissible centres are invariant**: `Φ⁻¹C` is an admissible centre of `Φ^*𝔪` iff `C` is one of
`𝔪`. -/
theorem isAdmissibleCentre_pullback_iff {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent) {C : Set M} :
    (MarkedIdeal.pullback Φ 𝔪).IsAdmissibleCentre (Φ ⁻¹' C) ↔ 𝔪.IsAdmissibleCentre C := by
  unfold IsAdmissibleCentre
  rw [cosupp_pullback_eq h𝔞, isClosedSubmanifold_preimage_iff,
    preimage_subset_preimage_iff fun x _ => ⟨Φ.symm x, Φ.apply_symm_apply x⟩]
  exact and_congr_right fun _ => and_congr_right fun _ => hasNormalCrossings_preimage_iff Φ

/-- **Well-formedness is invariant.** -/
theorem IsWellFormed.pullback {𝔪 : MarkedIdeal n M} (h : 𝔪.IsWellFormed) :
    (MarkedIdeal.pullback Φ 𝔪).IsWellFormed where
  isClosedSubmanifold_N := (isClosedSubmanifold_preimage_iff Φ).mpr h.isClosedSubmanifold_N
  isCoherent := isCoherent_pullback Φ.contMDiff h.isCoherent
  isSNCDivisor := (isSNCDivisor_map_preimage_iff Φ).mpr h.isSNCDivisor
  isTransverse := (isTransverse_preimage_iff Φ).mpr h.isTransverse

end Invariance

/-! ### Transport of towers -/

section Transport

variable {n : ℕ}

/-- **A tower over `X'` with a biholomorphism of its last stage onto `Y`**: the result of transporting a tower
over `X` ending at `Y` along a biholomorphism `X' ≅ X`. -/
structure TowerTransport (X' Y : CMfd.{u} n) : Type (u + 1) where
  /-- The last stage of the transported tower. -/
  target : CMfd.{u} n
  /-- The transported tower. -/
  tower : BlowupTower X' target
  /-- The biholomorphism between the last stages. -/
  back : target ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)

/-- **The transport of a tower along a biholomorphism `Φ : X' ≅ X` of the base.**  The empty tower goes to the
empty tower over `X'` (last-stage biholomorphism `Φ`).  A blowup `σ : Z → Y` along `C` on top of `T` becomes the
blowup `back⁻¹ ∘ σ : Z → Y'` along `back⁻¹ C` on top of the transport `(Y', back)` of `T`
(`MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse`), with last-stage biholomorphism the identity of `Z`.
So the stages from the first blowup on are those of `T`. -/
def transport : {Y : CMfd.{u} n} → BlowupTower X Y → TowerTransport X' Y
  | _, .refl => ⟨X', .refl, Φ⟩
  | _, .step T C π hπ =>
      ⟨_, .step (transport T).tower ((transport T).back ⁻¹' C) ((transport T).back.symm ∘ π)
        (isBlowupAlong_comp_inverse (transport T).back.contMDiff (transport T).back.symm.contMDiff
          (transport T).back.apply_symm_apply (transport T).back.symm_apply_apply hπ),
        Diffeomorph.refl _ _ _⟩

@[simp] theorem transport_refl_target : (transport Φ (BlowupTower.refl : BlowupTower X X)).target = X' := rfl

@[simp] theorem transport_refl_tower :
    (transport Φ (BlowupTower.refl : BlowupTower X X)).tower = BlowupTower.refl := rfl

@[simp] theorem transport_refl_back : (transport Φ (BlowupTower.refl : BlowupTower X X)).back = Φ := rfl

end Transport

end

end Hironaka.MarkedIdealTowerTransport
