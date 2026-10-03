/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of the monomial phase under the operations of the general step

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2b of Proposition `pr:resol` and the functoriality of the
invariant (commutation with étale maps); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), §5 and Theorem
1.3.

At the points of order `0` the value of the general step is read off `γ_T = MonomialStepAlong.towerInvAlong 𝔪 T`, the invariant
of the monomial case of the transform `𝔪_T`.  Properties (4)--(7) of `hir:centre-function` for the general value need, at these
points, that `γ_T` behaves under the operations of the general step as the order `ν` does
(`NonmonomialOrderTransport`); restriction to open sets is `MonomialInvariantFunctorialAlong.towerInvAlong_restrict`.  Here:

* `gammaAlong_congr_of_cosupport`, `gammaAlong_congr_of_restrictEquiv`: `γ` only depends on `N`, `E`, the mark and the
  cosupports `cosupp(𝔞|_N, e)`, hence only on the restriction of the ideal to `N`;
* **`towerInvAlong_congr`** (property (7)): restricted-equivalent marked ideals have the same invariant along every tower;
* **`towerInvAlong_isTowerIso`** (property (6)): along an isomorphism of towers `χ : T' → T` over a biholomorphism `Φ`,
  `γ` of `Φ^*𝔪` along `T'` at `p` is `γ` of `𝔪` along `T` at `χ p`;
* **`towerInvAlong_append`** (property (4')): `γ` of `𝔪` along `P T₁` is `γ` of `𝔪_P` along `T₁`, for every `P`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialOrderMonomialTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialInvariant Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.DivisorExponentAlong Hironaka.GermIdealOrder Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderMonomial Hironaka.NonmonomialOrderMonomialCanonical
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### The invariant only sees the cosupports along `N` -/

section Congr

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`γ` only depends on the cosupports along `N`**: ideals with the same cosupports `cosupp(·|_N, e)` for every `e` have
the same exponents along `N` along every member, hence the same invariant. -/
theorem gammaAlong_congr_of_cosupport {N : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h : ∀ e, cosupport n N 𝔞 e = cosupport n N 𝔟 e) (E : List (Set M)) (d : ℕ) :
    gammaAlong n N 𝔞 E d = gammaAlong n N 𝔟 E d := by
  have hdiv : ∀ (H : Set M) (x : M), divExpAlong n N 𝔞 H x = divExpAlong n N 𝔟 H x := by
    intro H x
    have hfun : IsDivNearAlong n N 𝔞 H = IsDivNearAlong n N 𝔟 H := by
      funext e y
      unfold IsDivNearAlong
      rw [h e]
    unfold divExpAlong
    rw [hfun]
  funext x
  unfold gammaAlong expDataAlong
  simp only [hdiv]

/-- **Restricted-equivalent marked ideals have the same invariant `γ`**: same `N`, `E` and mark, and the cosupports along `N`
agree for every order (`MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe`, both ways). -/
theorem gammaAlong_congr_of_restrictEquiv {𝔪 𝔫 : MarkedIdeal n M} (hEq : RestrictEquiv 𝔪 𝔫) :
    gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d = gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d := by
  rw [← hEq.N_eq, ← hEq.E_eq, ← hEq.d_eq]
  exact gammaAlong_congr_of_cosupport (fun e => Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hEq.ge e)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hEq.le e)) _ _

end Congr

/-! ### Along towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **(7) Representatives**: restricted-equivalent marked ideals (closed `N`, coherent ideals) have the same invariant `γ`
along every tower -- at the base by `gammaAlong_congr_of_restrictEquiv`, and from the first blowup on their transforms are
equal (`MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq`). -/
theorem towerInvAlong_congr {𝔪 𝔫 : MarkedIdeal n X} (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), towerInvAlong 𝔪 T = towerInvAlong 𝔫 T
  | _, .refl => gammaAlong_congr_of_restrictEquiv hEq
  | _, .step T C π hπ => by
      unfold towerInvAlong
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hEq hN h𝔪 h𝔫 T C π hπ]

/-- **(6) Isomorphisms of towers**: for `χ : T' → T` over a biholomorphism `Φ : X' ≅ X` and `T` a multiple test blow-up of `𝔪`
(closed submanifold `N`, coherent ideal), the invariant of `Φ^*𝔪` along `T'` at `p` is that of `𝔪` along `T` at `χ p`: the
transform of `Φ^*𝔪` along `T'` is `χ^*𝔪_T` (`BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq`) and `γ` is invariant
under biholomorphisms (`MonomialInvariantFunctorialAlong.gammaAlong_pullback_diffeomorph`). -/
theorem towerInvAlong_isTowerIso {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hT : IsGeoTestTower 𝔪 T) (p : Y') :
    towerInvAlong (MarkedIdeal.pullback Φ 𝔪) T' p = towerInvAlong 𝔪 T (χ p) := by
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  unfold towerInvAlong
  rw [IsTowerIso.geoTransformAlong_eq Φ hN h𝔞 hiso hT]
  exact MonomialInvariantFunctorialAlong.gammaAlong_pullback_diffeomorph χ (geoTransformAlong 𝔪 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) p _

/-- **(4') Re-basing**: the invariant of `𝔪` along `P T₁` is the invariant of `𝔪_P` along `T₁`, for every tower `P`. -/
theorem towerInvAlong_append (𝔪 : MarkedIdeal n X) {Y₀ Y : CMfd.{u} n} (P : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) :
    towerInvAlong 𝔪 (P.append T₁) = towerInvAlong (geoTransformAlong 𝔪 P) T₁ := by
  unfold towerInvAlong
  rw [geoTransformAlong_append]

end Tower

end

end Hironaka.NonmonomialOrderMonomialTransport
