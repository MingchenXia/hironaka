/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CodimOneAdmissibleAlong
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.Invariant.DivisorExponent
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The codimension-one part along `N` along multiple test blow-ups

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 1b of Proposition `pr:resol`; Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`) Step 1ba (printed p. 57).

In Step 1 of the algorithm for a marked ideal `(M, N, E, 𝔞, d)` of maximal order along `N`, Step 1ba
blows up the codimension-one part `Z₁ = codimOnePartAlong N 𝔞 d` of the cosupport along `N`, and
Step 1bb evaluates the invariant of the restriction `𝒮_w` of the coefficient ideal to a
hypersurface of maximal contact `N_T ∩ V(w)`.  The inductive invariant (`hir:centre-function`) is
only defined for marked ideals whose ideal vanishes identically on no nonempty open subset of their
submanifold.  This module proves that `𝒮_w` has that property at every stage after Step 1ba.

## Main results

* `codimOnePartAlong_geoTransformAlong_subset`: along every multiple test blow-up `T` of a well-formed marked ideal
  of maximal order along `N` with `d ≥ 1`, the codimension-one part along `N_T` lies over the original one: `Z₁(𝔪_T)
  ⊆ T⁻¹ Z₁(𝔪)`. (Near each of its points `Z₁(𝔪_T)` is the strict transform of a hypersurface of maximal contact
  (`MaximalContactAlongTower.exists_contact_along`), whose points off the last centre are dense in it; off the
  centre `Z₁` corresponds (`CodimOnePartCanonical`); induction on `T`.)
* `IsTangentDirectionAlong.exists_regularAtDim_succ`: at a point of a hypersurface of maximal contact
  `N ∩ V(u) ∩ U`, `N` is regular of some dimension `k + 1` and the hypersurface of dimension `k`.
* `eventually_forall_eq_zero_of_not_isNonzeroAlongAt`: if no germ of a coherent ideal at `y` is
  nonzero on `A` near `y`, the ideal vanishes on `A` near every point near `y`.
* `isNonzeroAlongAt_of_notMem_codimOnePartAlong`: let `A` be regular of dimension `k` at `y` where `N`
  is regular of dimension `k + 1`, with `cosupp(𝔞|_N, μ) ⊆ A` and `cosupp(𝔟|_A, ν) ⊆ cosupp(𝔞|_N, μ)`
  near `y`, `𝔟` coherent.  If `y ∉ Z₁(N, 𝔞, μ)`, then `𝔟|_A` does not vanish near `y`
  (`DivisorExponentAlong.IsNonzeroAlongAt`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOnePartTowerAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.HomogenizedGlueingTower Hironaka.MarkedIdealRestrictOpen Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealBiholomorphism Hironaka.CodimOnePartCanonical Hironaka.GermIdealOrder Hironaka.HomogenizedIdealAlong Hironaka.TangentDirectionAlong Hironaka.MaximalContactAlongTower Hironaka.TransformOffCentre Hironaka.DivisorExponentAlong Hironaka.CoefficientIdealRestriction Hironaka.MarkedIdealEquivalence Hironaka.ContactEquivalenceAlong Hironaka.GiraudAlong Hironaka.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ}

/-! ### The codimension-one part along towers -/

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **The codimension-one part along `N_T` lies over the original one.**  Let `𝔪 = (X, N, E, 𝔞, d)` be
well formed, of maximal order along `N`, `d ≥ 1`, and `T` a multiple test blow-up.  Then
`Z₁(𝔪_T) ⊆ T⁻¹ Z₁(𝔪)`.  Near a point `x ∈ Z₁(𝔪_T)` the codimension-one part is `N_T ∩ V(w)`
(`CodimOneSupportAlong`), the strict transform of a hypersurface of maximal contact `A = N ∩ V(u) ∩ U`
(`MaximalContactAlongTower.exists_contact_along`); after the last blowup `π` along `C`, the strict
transform of `A` is the closure of `π⁻¹(A_T \ C)`, so `x` is a limit of points `y ∈ Z₁(𝔪_T)` with
`π y ∉ C`, at which `Z₁` corresponds (`CodimOnePartCanonical.mem_codimOnePartAlong_geoTransformAlong_step_iff`)
and the induction hypothesis applies; `Z₁(𝔪)` is closed. -/
theorem codimOnePartAlong_geoTransformAlong_subset (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
        (geoTransformAlong 𝔪 T).d ⊆ T.proj ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d
  | _, .refl, _ => fun _ hx => hx
  | _, .step T C π hπ, hT => by
      intro x hx
      have hN := h𝔪.isClosedSubmanifold_N
      have h𝔞 := h𝔪.isCoherent
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      set T' : BlowupTower X _ := .step T C π hπ with hT'
      obtain ⟨hNT, h𝔞T⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T' hT
      have hx' : x ∈ codimOnePartAlong (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal 𝔪.d := by
        rw [← d_geoTransformAlong 𝔪 T']; exact hx
      have hxS : x ∈ cosupport n (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal 𝔪.d :=
        codimOnePartAlong_subset hx'
      have hx0 : T'.proj x ∈ 𝔪.cosupp := cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T' hT (by
        show x ∈ cosupport n (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal
          (geoTransformAlong 𝔪 T').d
        rw [d_geoTransformAlong]; exact hxS)
      obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirectionAlong h𝔞 hN hμ hx0
        fun h => hmax (T'.proj x) ⟨hx0.1, h⟩
      obtain ⟨O, w, hxO, hO, -, hw, hwD, hw1, hwA⟩ :=
        exists_contact_along 𝔪 hN h𝔞 hμ hu T' hT x hxS.1 hxU
      have hR := eventually_mem_codimOnePartAlong_iff_eq_zero_of_isInSpanOnAt h𝔞T hNT hμ hO hw hwD hw1
        hxO hx'
      set A : Set X := 𝔪.N ∩ {y | u y = 0} ∩ U with hA
      have hAN : A ⊆ 𝔪.N := fun _ hy => hy.1.1
      have hxw : x ∈ (geoTransformAlong 𝔪 T').N ∧ w x = 0 := hR.self_of_nhds.mp hx'
      have hxA : x ∈ closure (π ⁻¹' (strictAlong T A \ C)) := (hwA x hxO hxw.1).mp hxw.2
      have hZc : IsClosed (T'.proj ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) :=
        (isClosed_codimOnePartAlong h𝔞 hN hμ hmax).preimage T'.contMDiff_proj.continuous
      rw [← hZc.closure_eq, mem_closure_iff_nhds]
      intro t ht
      obtain ⟨y, ⟨⟨hyt, hyR⟩, hyO⟩, hyA, hyC⟩ :=
        mem_closure_iff_nhds.mp hxA _ (inter_mem (inter_mem ht hR) (hO.mem_nhds hxO))
      have hyA' : y ∈ strictAlong T' A := subset_closure ⟨hyA, hyC⟩
      have hyN : y ∈ (geoTransformAlong 𝔪 T').N := strictAlong_subset_N 𝔪 hAN T' hyA'
      have hyZ : y ∈ codimOnePartAlong (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal
          (geoTransformAlong 𝔪 T').d := by
        rw [d_geoTransformAlong]
        exact hyR.mpr ⟨hyN, (hwA y hyO hyN).mpr hyA'⟩
      have hπy := (mem_codimOnePartAlong_geoTransformAlong_step_iff hN h𝔞 T hT0 C π hπ hyC).mp hyZ
      exact ⟨y, hyt, codimOnePartAlong_geoTransformAlong_subset h𝔪 hμ hmax T hT0 hπy⟩

end Tower

/-! ### The restriction to a hypersurface of maximal contact is nonzero off the codimension-one part -/

section Nonzero

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A hypersurface of maximal contact has dimension one less than `N`, which is at least one**: at a
point of `N ∩ V(u) ∩ U` for a tangent direction `u` of `(𝔞|_N, μ)` along the closed submanifold `N` on
`U`, `N` is regular of some dimension `k + 1` and `N ∩ V(u) ∩ U` of dimension `k`. -/
theorem IsTangentDirectionAlong.exists_regularAtDim_succ {N : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (hN : IsClosedSubmanifold n N) {μ : ℕ} {U : Set M}
    {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {y : M} (hy : y ∈ N ∩ {y | u y = 0} ∩ U) :
    ∃ k, RegularAtDim (n := n) N y (k + 1) ∧ RegularAtDim (n := n) (N ∩ {y | u y = 0} ∩ U) y k := by
  obtain ⟨k, hk, hk'⟩ := hu.regularAtDim_contact h𝔞 hN hy
  obtain ⟨⟨hyN, hyu⟩, hyU⟩ := hy
  have hk2 := hk
  obtain ⟨-, -, Φ, hΦsrc, -, hflat⟩ := hk2
  obtain ⟨e, ξ, hξ, hne⟩ := hu.multiplicity_one y hyU hyu
  have huhol : HolomorphicAt n u y :=
    holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y hyU)
  obtain ⟨j, hj, -⟩ := TangentDirectionAlong.exists_flatPartial_ne_zero hΦsrc hflat
    (BlowupFlatCoordinates.mem_flatDomain_self Φ) hyN huhol hξ hne
  refine ⟨k - 1, ?_, hk'⟩
  rw [Nat.sub_add_cancel (by omega)]
  exact hk

/-- **A coherent ideal none of whose germs at `y` is nonzero on `A` near `y` vanishes on `A` near every
point near `y`.** -/
theorem eventually_forall_eq_zero_of_not_isNonzeroAlongAt {A : Set M} {𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsCoherent) {y : M} (h : ¬ IsNonzeroAlongAt A 𝔟 y) :
    ∀ᶠ z in 𝓝 y, ∀ g, 𝔟.mem z g → ∀ᶠ z' in 𝓝 z, z' ∈ A → g z' = 0 := by
  obtain ⟨U, hUo, hyU, K, s, hs, hgen⟩ := h𝔟 y
  have hsy : ∀ i, ∀ᶠ z in 𝓝 y, z ∈ A → s i z = 0 := fun i => by
    have hmem : 𝔟.mem y (s i) := (hgen y hyU _).mpr (isInSpanAt_of_eq_mul ⟨i, rfl⟩
      (DivisorExponent.holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hyU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
    have h' : ¬ ∃ᶠ z in 𝓝 y, z ∈ A ∧ s i z ≠ 0 := fun hf => h ⟨s i, hmem, hf⟩
    rw [not_frequently] at h'
    filter_upwards [h'] with z hz hzA
    by_contra hne
    exact hz ⟨hzA, hne⟩
  filter_upwards [hUo.mem_nhds hyU, (eventually_all.mpr hsy).eventually_nhds] with z hzU hz g hg
  obtain ⟨-, K', t, a, ht, -, hga⟩ := (hgen z hzU g).mp hg
  filter_upwards [hga, hz] with z' hz'g hz' hz'A
  rw [hz'g]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i, hi⟩ := ht j
  rw [← hi, hz' i hz'A, mul_zero]

/-- **Off the codimension-one part the restriction to a hypersurface containing the cosupport is
nonzero.**  Let `A` be regular of dimension `k` at `y`, where `N` is regular of dimension `k + 1`, assume
that near `y` the cosupport of `(𝔞|_N, μ)` lies in `A` and the cosupport of `(𝔟|_A, ν)` in that of
`(𝔞|_N, μ)`, and that `𝔟` is coherent.  If `y` is not in the codimension-one part `Z₁(N, 𝔞, μ)`, then
`𝔟|_A` does not vanish near `y`: otherwise `𝔟` vanishes on `A` near `y`, every point of `A` near `y` lies in
the cosupport of `(𝔟|_A, ν)`, hence in that of `(𝔞|_N, μ)`, which therefore agrees with `A` near `y` and
is regular of dimension `k` there. -/
theorem isNonzeroAlongAt_of_notMem_codimOnePartAlong {N A : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν k : ℕ}
    (h𝔟 : 𝔟.IsCoherent) {y : M} (hN : RegularAtDim (n := n) N y (k + 1))
    (hA : RegularAtDim (n := n) A y k) (hsub : ∀ᶠ z in 𝓝 y, z ∈ cosupport n N 𝔞 μ → z ∈ A)
    (hcos : ∀ᶠ z in 𝓝 y, z ∈ cosupport n A 𝔟 ν → z ∈ cosupport n N 𝔞 μ)
    (hy : y ∉ codimOnePartAlong N 𝔞 μ) : IsNonzeroAlongAt A 𝔟 y := by
  by_contra h
  refine hy ((mem_codimOnePartAlong_iff_of_eventually (A := N) (S := A)
    (Eventually.of_forall fun _ => Iff.rfl) ?_).mpr ⟨k, hN, hA⟩)
  filter_upwards [hsub, hcos, eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝔟 h] with z h1 h2 h3
  exact ⟨h1, fun hzA => h2 ⟨hzA, fun g hg => ⟨fun _ => 0, zero_mem_idealPow _ z ν, h3 g hg⟩⟩⟩

end Nonzero

end

end Hironaka.CodimOnePartTowerAlong
