/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Resolution.FactorizationDomain
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Invariant.ResolutionDriver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Relative principalization from given resolutions of marked ideals

Hironaka phase H5a (design I-0981 C-0161): the geometry of `hir:factorization-from-resolution`
(`blueprint/src/hironaka.tex`), with the two resolutions of the proof taken as hypotheses.  Blueprint
`mc:factorization-ambient`, `mc:factorization-thin-centre`, `mc:factorization-tower`, `mc:factorization-second`,
`mc:factorization-assembly` (`blueprint/src/maximal-contact.tex`).  Source: Copy-4
(`transcendental-nakamaye-copy4-20260911`), the proof of `lem:relative-principalization`, identities `eq:rp-induction`.

Let `𝔪 = (X, N, E, 𝔞, 1)` be a marked ideal with mark one, `N` a closed submanifold and `𝔞` coherent, and
`𝔪' = (X, X, E, 𝔞, 1)` the same data with `N` replaced by the whole manifold.  Along a multiple test blow-up `T` of `𝔪`
the ideal of the transform `𝔪_T` is an ideal of `𝒪_{N_T}`, represented by a colon ideal along `N_T`; the transform
`𝔪'_T` carries the ambient controlled transform `𝔞'_T = 𝒪(E_T)·T^*𝔞`.  Copy-4's third identity
`Res_{W_i} 𝔞_i = 𝔟_i` says that the two agree along `N_T`.

## Main results

* `ambient 𝔪`: the marked ideal `(X, X, E, 𝔞, d)`; `cosupp_eq_inter_zeroLocus` (mark one: `cosupp = N ∩ Z(𝔞)`);
* **`isGeoTestTower_and_restrictEquiv`**: every multiple test blow-up `T` of `𝔪` is one of `𝔪'`, and `𝔪_T` is
  restricted-equivalent to `𝔪_T` with its ideal replaced by `𝔞'_T`; `cosupp_geoTransformAlong_eq`: hence
  `cosupp 𝔪_T = N_T ∩ Z(𝔞'_T)`;
* one blowup along a thin centre `C` inside a closed connected submanifold `N` of dimension `k`:
  `lt_of_regularAtDim_of_frequently` (`dim C < k`), `mem_exceptionalLocus_of_regularAtDim` (codimension `≥ 2`: every point
  over `C` is exceptional), `isPreconnected_preimage_of_disjoint`, `mem_geoStrictTransform_iff_of_notMem`,
  **`geoStrictTransform_data`** (`N' = closure (π⁻¹(N \ C))` is the strict transform `closure (π⁻¹N \ Exc π)` and a closed
  connected submanifold of dimension `k`), `pullback_vanishingIdeal_eq_of_disjoint` (`π^*𝓘_A = 𝓘_{π⁻¹A}` for `A ∩ C = ∅`);
* along a multiple test blow-up `T` of `𝔪` in the domain, with mark one and `N` a closed connected submanifold of
  dimension `k < n`: `support_add_subset`, `frequently_mem_N_notMem_of_isInvDomain`, **`tower_data`** -- `N_T` is a closed
  connected submanifold of dimension `k` and the strict transform of `N`; `T` is adapted to `N`;
  `T^*𝓘_N = 𝒪(-E_T)·𝓘_{N_T}` (Copy-4's first identity); the support of `E_T` lies in `Exc T`;
* the second stage, for `(X, X, E, 𝔟, 1)` with `𝔟` coherent and a closed connected submanifold `A` of dimension `k` missing
  `Z(𝔟)`: `disjoint_preimage_of_isAdmissibleCentre` (admissible centres along a test tower `S` miss `S⁻¹A`), **`second_data`**
  (`S⁻¹A` is a closed connected submanifold of dimension `k` and the strict transform of `A`, `E_S` misses it,
  `S^*𝓘_A = 𝓘_{S⁻¹A}`);
* the assembly: `pullDivisor` (`S^*D`, with `pullDivisor_ideal`, `support_pullDivisor`), `idealPow_one_of_isCoherent`,
  `isAdaptedBlowupSequence_comp`, `lt_of_ne_univ`, **`factorizationData_of_isGeoResolution`** (from a resolution `T₁` of
  `(Y, W, ∅, 𝔞, 1)` and a resolution `T₂` of `(Y_t, Y_t, ∅, 𝔞_t, 1)`, `𝔞_t` the ambient controlled transform along `T₁`: the body of
  `RelativePrincipalization.FactorizationData W k 𝔞`, written out, with `f = T₁ ∘ T₂`, `H = T₂^*E_{T₁}`, `H' = E_{T₂}`) and
  **`factorizationData_of_exists_resolution`** (the same from the existence of resolutions of every marked ideal of the domain
  in dimension `≤ j`, `n ≤ j`, on compact manifolds -- the output of a resolution invariant's driver).

`RelativePrincipalization` is not imported: its `FactorizationData` is written out in the conclusions above (checked
definitionally equal by a throwaway probe outside the repository).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.FactorizationFromResolution

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}


section Ambient

variable {X : CMfd.{u} n}


/-- The cosupport of a marked ideal with mark one and coherent ideal is `N ∩ Z(𝔞)`. -/
theorem cosupp_eq_inter_zeroLocus {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔫 : MarkedIdeal n M} (hd : 𝔫.d = 1) (h : 𝔫.ideal.IsCoherent) :
    𝔫.cosupp = 𝔫.N ∩ 𝔫.ideal.zeroLocus := by
  rw [MarkedIdeal.cosupp, hd]
  exact cosupport_one fun _ _ hg => SubmanifoldRestrictLe.holomorphicAt_of_mem_of_isCoherent h hg

end Ambient


section Tower

variable {X : CMfd.{u} n}


/-- **Points of the submanifold off a centre accumulate at the centre**: for `𝔫` in the domain with mark one and an
admissible centre `C`, every point of `C` is a limit of points of `N \ C` (a germ of `𝔞` nonzero along `N` does not vanish
at nearby points of `N`, which therefore lie off the cosupport). -/
theorem frequently_mem_N_notMem_of_isInvDomain {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔫 : MarkedIdeal n M} {k : ℕ} (h : IsInvDomain k 𝔫) (hd : 𝔫.d = 1) {C : Set M}
    (hC : C ⊆ 𝔫.cosupp) : ∀ c ∈ C, ∃ᶠ y in 𝓝 c, y ∈ 𝔫.N ∧ y ∉ C := by
  intro c hc
  have hcoh := h.isWellFormed.isCoherent
  obtain ⟨g, hg, hfr⟩ := h.isNonzeroAlongAt c (𝔫.cosupp_subset_N (hC hc))
  refine (hfr.and_eventually (HadamardBridge.eventually_mem_of_isCoherent hcoh hg)).mono ?_
  rintro y ⟨⟨hyN, hgy⟩, hmem⟩
  refine ⟨hyN, fun hyC => hgy ?_⟩
  have hy := hC hyC
  rw [cosupp_eq_inter_zeroLocus hd hcoh] at hy
  exact hy.2 g hmem

end Tower


end

end Hironaka.FactorizationFromResolution
