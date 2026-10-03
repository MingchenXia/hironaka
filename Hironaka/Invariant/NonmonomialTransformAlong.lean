/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialStepAlong
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionReduction
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GeoTransformWellFormed
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberTraceIdealAlong
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Blowup.SimultaneousNormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transforms of the monomial and nonmonomial parts inside a submanifold

For `N = M` this is `NonmonomialTransformTower`.

## Main results

* `factor_along_along`: let `N` be a closed submanifold, `E` simple normal crossings transverse to `N`, `𝓜` coherent,
  nonzero and monomial along `N`, `𝔟` coherent, nonzero along `N` and, restricted to `N`, contained in the ideal of no
  member at the points of `N`, `o ≥ 1`, and `ord(𝔟|_N) ≤ o` on `cosupp((𝔟𝓜)|_N, d)`.  Along every multiple test blow-up
  `T` of the companion ideal `companionAlong N E 𝔟 𝓜 o d` (`CompanionReductionAlong`): the transform `𝔪_T` of
  `(N, E, 𝔟𝓜, d)` is well formed, the transform `𝔫_T` of `(N, E, 𝔟, o)` lives on the same `N_T`, `E_T`, is coherent,
  nonzero along `N_T` and in the ideal of no member of `E_T` on `N_T`, and `Res_{N_T} 𝔞_T = Res_{N_T} (𝔫_T 𝓜_T)` with
  `𝓜_T` coherent, nonzero and monomial along `N_T` (`NonmonomialStepAlong.step_along` at each stage, the admissibility of
  the centres and the bound from `CompanionReductionAlong.companion_reduction_along`).
* uniqueness of the factorization along `N` (the along-`N` form of `hir:monomial-factorization-unique`):
  `isDivNearAlong_mul_iff` (a factor in no member ideal does not change divisibility by the members along `N`; identity
  principle along `N ∩ E_i`), `monomialPartAlong_eq_of_factor` (`Res_N 𝔞 = Res_N (𝔟𝓜)` gives `𝓜_N(𝔞) = 𝓜_N(𝓜)`),
  `le_nonmonomialPartAlong_of_factor` (`𝔟 ⊆ 𝓝_N(𝔞)`), `restrictLe_nonmonomialPartAlong_of_factor`
  (`Res_N 𝓝_N(𝔞) ⊆ Res_N 𝔟`, cancelling the local generator of `𝓜_N(𝓜)` along `N`), with the helpers
  `isDivNearAlong_eq_of_cosupport_eq`, `divExpAlong_eq_of_isDivNearAlong_eq`, `monomialPartAlong_eq_of_divExpAlong_eq`,
  `exists_isInSpanOnAt_of_mul_generator`, `le_nonmonomialPartAlong_self`, `isPrincipalMonomialAlongAt_monomialPartAlong`,
  `parts_hypotheses`;
* `nonmonomialPart_geoTransformAlong_along` (`hir:nonmonomial-transform` for `N ≠ M`): for `(X, N, E, 𝔞, d)` well
  formed with `𝔞` nonzero along `N` and `ord(𝓝_N(𝔞)|_N) ≤ o` on the cosupport, along every multiple test blow-up `T`
  of the companion ideal of `(𝓝_N(𝔞), 𝓜_N(𝔞), o)`, `T` is one of `(X, N, E, 𝔞, d)`, the transform of `(N, E, 𝓝_N(𝔞),
  o)` is the nonmonomial part of `𝔞_T` along `N_T` (contained in it, equal to it on `N_T`), the monomial part of
  `𝔞_T` is that of a monomial `𝓜_T`, and `ord(𝓝_{N_T}(𝔞_T)|_{N_T}) ≤ o` on the cosupport.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.NonmonomialTransformAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.MonomialPartAlong Hironaka.NormalCrossings Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.BlowupStrictSubmanifold Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.RestrictedIdealWeight Hironaka.MarkedIdealOperationsTransform.MarkedIdeal Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.CompanionReductionAlong Hironaka.NonmonomialStepAlong Hironaka.RelativePrincipalizationSpan Hironaka.InvertibleIdealQuotient Hironaka.BlowupFlatCoordinates

noncomputable section

variable {n : ℕ}

/-! ### The factorization along the companion tower -/

section Tower

variable {X : CMfd.{u} n}

open Classical in
/-- **The factorization along the companion tower, inside `N`** (the induction behind `hir:nonmonomial-transform` for
`N ≠ M`).  See the module docstring. -/
theorem factor_along_along (hn : 0 < n) {N : Set X} (hN : IsClosedSubmanifold n N) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) {𝔟 𝓜 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent)
    (h𝓜 : 𝓜.IsCoherent) (hne𝓜 : ∀ y ∈ N, IsNonzeroAlongAt N 𝓜 y) (hmono : IsMonomialAlong n N 𝓜 E)
    (hnd : ∀ y ∈ N, ∀ i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧
      ¬ IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem y) y a)
    (hnz : ∀ y ∈ N, IsNonzeroAlongAt N 𝔟 y) {o d : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ cosupport n N (𝔟.mul 𝓜) d, x ∉ cosupport n N 𝔟 (o + 1)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (companionAlong N E 𝔟 𝓜 o d) T →
      (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).IsWellFormed ∧
      (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).N =
        (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N ∧
      (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).E =
        (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E ∧
      (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N,
        IsNonzeroAlongAt (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N
          (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal y) ∧
      (∀ y ∈ (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N, ∀ i,
        y ∈ (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E.get i → ∃ a,
          (geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.mem y a ∧
          ¬ IsInSpanOnAt (n := n) (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N
            ((vanishingIdeal (n := n)
              ((geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E.get i)).mem y) y a) ∧
      ∃ 𝓜T : GermIdeal n Y, 𝓜T.IsCoherent ∧
        RestrictLe (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N
          (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).ideal
          ((geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.mul 𝓜T) ∧
        RestrictLe (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N
          ((geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T).ideal.mul 𝓜T)
          (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).ideal ∧
        (∀ y ∈ (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N,
          IsNonzeroAlongAt (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N 𝓜T y) ∧
        IsMonomialAlong n (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).N 𝓜T
          (geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T).E
  | _, .refl, _ => by
      have hcoh : (𝔟.mul 𝓜).IsCoherent := isCoherent_mul h𝔟 h𝓜
      exact ⟨⟨hN, hcoh, hE, hTr⟩, rfl, rfl, h𝔟, hnz, hnd, 𝓜, h𝓜,
        RestrictLeCalculus.restrictLe_refl hcoh, RestrictLeCalculus.restrictLe_refl hcoh, hne𝓜, hmono⟩
  | Z, .step T C π hπ, hT => by
      obtain ⟨hTp, -⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      obtain ⟨hwfT, hNeq, hEeq, hcoh𝔫T, hnzT, hndT, 𝓜T, h𝓜T, hf1, hf2, hne𝓜T, hmonoT⟩ :=
        factor_along_along hn hN hE hTr h𝔟 h𝓜 hne𝓜 hmono hnd hnz ho hbound T hTp
      obtain ⟨hTm', hTn', -, -⟩ := companion_reduction_along hN E h𝔟 h𝓜 ho hbound (.step T C π hπ) hT
      obtain ⟨-, -, hbT, -⟩ := companion_reduction_along hN E h𝔟 h𝓜 ho hbound T hTp
      obtain ⟨-, hCm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hTm'
      obtain ⟨-, hCn⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hTn'
      set 𝔪T := geoTransformAlong (⟨N, E, 𝔟.mul 𝓜, d⟩ : MarkedIdeal n X) T with h𝔪T
      set 𝔫T := geoTransformAlong (⟨N, E, 𝔟, o⟩ : MarkedIdeal n X) T with h𝔫T
      have hd𝔪 : 𝔪T.d = d := d_geoTransformAlong _ T
      have hd𝔫 : 𝔫T.d = o := d_geoTransformAlong _ T
      have hNT := hwfT.isClosedSubmanifold_N
      have hcohP : (𝔫T.ideal.mul 𝓜T).IsCoherent := isCoherent_mul hcoh𝔫T h𝓜T
      have h𝔫Teq : 𝔫T = ⟨𝔪T.N, 𝔪T.E, 𝔫T.ideal, o⟩ := ext_of hNeq hEeq rfl hd𝔫
      have hREq : RestrictEquiv 𝔪T ⟨𝔪T.N, 𝔪T.E, 𝔫T.ideal.mul 𝓜T, d⟩ := ⟨rfl, rfl, hd𝔪, hf1, hf2⟩
      have h𝔪Teq : 𝔪T.geoTransform C π =
          (⟨𝔪T.N, 𝔪T.E, 𝔫T.ideal.mul 𝓜T, d⟩ : MarkedIdeal n _).geoTransform C π :=
        hREq.geoTransform_eq hNT.1 hwfT.isCoherent hcohP hπ.contMDiff
      have hCa : C ⊆ cosupport n 𝔪T.N (𝔫T.ideal.mul 𝓜T) d := by
        have h := hCm.2.1
        rw [hREq.cosupp_eq] at h
        exact h
      have hCb : C ⊆ cosupport n 𝔪T.N 𝔫T.ideal o := by
        have h := hCn.2.1
        rw [MarkedIdeal.cosupp, hNeq, hd𝔫] at h
        exact h
      have hbd : ∀ x ∈ C, x ∉ cosupport n 𝔪T.N 𝔫T.ideal (o + 1) := by
        intro x hx
        have h := hbT x (hCm.2.1 hx)
        rw [hNeq] at h
        exact h
      obtain ⟨h𝓜', f1, f2, hP', hnd', hnz'⟩ :=
        step_along hn hπ hNT hwfT.isSNCDivisor hwfT.isTransverse hcoh𝔫T h𝓜T hne𝓜T hmonoT hndT hnzT hCm.2.2 hCb
          hCa hbd
      have hwf' : (𝔪T.geoTransform C π).IsWellFormed :=
        GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwfT hCm hπ
      have hcoh𝔫' : ((⟨𝔪T.N, 𝔪T.E, 𝔫T.ideal, o⟩ : MarkedIdeal n _).geoTransform C π).ideal.IsCoherent :=
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
          (𝔪 := ⟨𝔪T.N, 𝔪T.E, 𝔫T.ideal, o⟩) hNT hcoh𝔫T ⟨hπ.1, hCb, hCm.2.2⟩ hπ
      obtain ⟨hne', hmono'⟩ := isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hwf'.isClosedSubmanifold_N
        hwf'.isSNCDivisor hwf'.isTransverse h𝓜' fun x hx => (hP' x hx).choose_spec.isPrincipalMonomialAlongAt
      rw [geoTransformAlong_step, geoTransformAlong_step, ← h𝔪T, ← h𝔫T, h𝔫Teq]
      refine ⟨hwf', rfl, rfl, hcoh𝔫', hnz', hnd', monomialFactor n π C 𝔪T.N 𝔪T.E 𝓜T o d, h𝓜', ?_, ?_, hne', hmono'⟩
      · rw [h𝔪Teq]; exact f1
      · rw [h𝔪Teq]; exact f2

end Tower

/-! ### Uniqueness of the factorization along `N` -/

section Unique

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {E : List (Set M)}

/-- `IsDivNearAlong` only sees the cosupports along `N`. -/
theorem isDivNearAlong_eq_of_cosupport_eq {𝔞 𝔟 : GermIdeal n M} (h : ∀ e, cosupport n N 𝔞 e = cosupport n N 𝔟 e)
    (H : Set M) : IsDivNearAlong n N 𝔞 H = IsDivNearAlong n N 𝔟 H := by
  funext e x
  simp only [IsDivNearAlong, h e]

/-- The exponent along `N` only sees `IsDivNearAlong`. -/
theorem divExpAlong_eq_of_isDivNearAlong_eq {𝔞 𝔟 : GermIdeal n M} {H : Set M}
    (h : IsDivNearAlong n N 𝔞 H = IsDivNearAlong n N 𝔟 H) (x : M) :
    divExpAlong n N 𝔞 H x = divExpAlong n N 𝔟 H x := by
  unfold divExpAlong
  rw [h]

/-- **Divisibility of a product by a member, along `N`, when the other factor lies in no member ideal**: if `𝔟` is, at
every point of `N ∩ E_i`, not contained on `N` in `𝓘_{E_i}`, then near `x` the points of `N ∩ E_i` lie in
`cosupp((𝔟𝓜)|_N, e)` iff they lie in `cosupp(𝓜|_N, e)`.  (⇐) `cosupp(𝔟|_N, 0) ∩ cosupp(𝓜|_N, e) ⊆ cosupp((𝔟𝓜)|_N, e)`.
(⇒) a germ `a ∈ 𝔟_x` does not vanish on `N ∩ E_i` near `x`; at the points `y` where `a(y) ≠ 0`, `ord(𝔟|_N) = 0`, so
`cosupp((𝔟𝓜)|_N, e) ⊆ cosupp(𝓜|_N, e)` near `y` (`CompanionReductionAlong.mem_cosupport_of_mem_cosupport_mul_along`);
these points accumulate at `x`, and the identity principle along `N ∩ E_i`
(`DivisorExponentAlong.isDivNearAlong_of_frequently`) concludes. -/
theorem isDivNearAlong_mul_iff (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) {𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) (h𝓜 : 𝓜.IsCoherent)
    (hnd : ∀ y ∈ N, ∀ i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧
      ¬ IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem y) y a)
    (i : Fin E.length) (e : ℕ) (x : M) :
    IsDivNearAlong n N (𝔟.mul 𝓜) (E.get i) e x ↔ IsDivNearAlong n N 𝓜 (E.get i) e x := by
  have hhol𝔟 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔟
  have hhol𝓜 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝓜
  constructor
  · intro hd
    by_cases hx : x ∈ N ∩ E.get i
    · obtain ⟨k, hk⟩ := hN.2 x hx.1
      obtain ⟨r, hr⟩ := exists_isLocalRetraction hk
      obtain ⟨k', hk'⟩ := regularAtDim_inter_get hn hN.1 hE hT i hx.1 hx.2
      obtain ⟨a, ha, hna⟩ := hnd x hx.1 i hx.2
      have hahol := hhol𝔟 x a ha
      have hfreq : ∃ᶠ y in 𝓝 x, y ∈ N ∧ y ∈ E.get i ∧ a y ≠ 0 := by
        by_contra hcon
        rw [Filter.not_frequently] at hcon
        refine hna ((MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx.1 i hahol).mpr ⟨hahol, ?_⟩)
        exact hcon.mono fun y hy hyNE => by
          by_contra h
          exact hy ⟨hyNE.1, hyNE.2, h⟩
      have hkey : ∀ᶠ y in 𝓝 x, (∀ᶠ z in 𝓝 y, 𝔟.mem z a) ∧ IsDivNearAlong n N (𝔟.mul 𝓜) (E.get i) e y :=
        (HadamardBridge.eventually_mem_of_isCoherent h𝔟 ha).eventually_nhds.and hd.eventually
      refine isDivNearAlong_of_frequently h𝓜 hr hk' ((hfreq.and_eventually hkey).mono
        fun y ⟨⟨hyN, hyH, hay⟩, hmem, hdy⟩ => ⟨hyN, hyH, ?_⟩)
      have hayhol := hhol𝔟 y a hmem.self_of_nhds
      filter_upwards [hmem, hdy, hayhol.continuousAt.eventually (isOpen_ne.mem_nhds hay)]
        with z hz1 hz2 hz3 hzN hzH
      have hnot : z ∉ cosupport n N 𝔟 (0 + 1) := fun h =>
        hz3 ((vanishesToOrderOn_one_iff hzN (hhol𝔟 z a hz1)).mp (h.2 a hz1))
      have := CompanionReductionAlong.mem_cosupport_of_mem_cosupport_mul_along hN.2 hhol𝔟 hhol𝓜 (Nat.zero_le e)
        (hz2 hzN hzH) hnot
      simpa using this
    · exact isDivNearAlong_of_notMem (hN.1.inter (hE.1 _ (List.get_mem E i))) hx e
  · intro hd
    filter_upwards [hd] with z hz hzN hzH
    have h1 := IdealOrderArithmetic.inter_cosupport_subset_cosupport_mul (𝔞 := 𝔟) (𝔟 := 𝓜) (N := N) 0 e
      ⟨by rw [cosupport_zero hhol𝔟]; exact hzN, hz hzN hzH⟩
    simpa using h1

/-- The monomial part along `N` only sees the exponents along `N` at the points of `N`. -/
theorem monomialPartAlong_eq_of_divExpAlong_eq {𝔞 𝔟 : GermIdeal n M}
    (h : ∀ i : Fin E.length, ∀ y ∈ N, y ∈ E.get i →
      divExpAlong n N 𝔞 (E.get i) y = divExpAlong n N 𝔟 (E.get i) y) :
    monomialPartAlong n N 𝔞 E = monomialPartAlong n N 𝔟 E := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ?_)
  simp only [monomialPartAlong]
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun hyN => forall_congr' fun hyi => ?_)
  rw [h i y hyN hyi]

/-- **Uniqueness of the monomial part along `N`** (the along-`N` form of `hir:monomial-factorization-unique`): if
`Res_N 𝔞 = Res_N (𝔟𝓜)` and `𝔟` is, at the points of `N`, contained on `N` in the ideal of no member, then `𝔞` and `𝓜` have
the same exponents along `N` and the same monomial part along `N`. -/
theorem monomialPartAlong_eq_of_factor (hn : 0 < n) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) {𝔞 𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) (h𝓜 : 𝓜.IsCoherent)
    (hnd : ∀ y ∈ N, ∀ i, y ∈ E.get i → ∃ a, 𝔟.mem y a ∧
      ¬ IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem y) y a)
    (hf1 : RestrictLe N 𝔞 (𝔟.mul 𝓜)) (hf2 : RestrictLe N (𝔟.mul 𝓜) 𝔞) :
    monomialPartAlong n N 𝔞 E = monomialPartAlong n N 𝓜 E := by
  have hcos : ∀ e, cosupport n N 𝔞 e = cosupport n N (𝔟.mul 𝓜) e := fun e =>
    Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hf2 e)
      (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hf1 e)
  refine monomialPartAlong_eq_of_divExpAlong_eq fun i y _ _ => ?_
  rw [divExpAlong_eq_of_isDivNearAlong_eq (isDivNearAlong_eq_of_cosupport_eq hcos _) y]
  refine divExpAlong_eq_of_isDivNearAlong_eq ?_ y
  funext e x
  exact propext (isDivNearAlong_mul_iff hn hN hE hT h𝔟 h𝓜 hnd i e x)

/-- **Cofactor of a restricted principal factor**: if `Res_W B_z = Res_W (q)` and `g` lies on `W` in the span of
`(AB)_z`, then `g = h q` on `W` near `z` with `h` holomorphic at `z` and in the span of `A_z` on `W`. -/
theorem exists_isInSpanOnAt_of_mul_generator {W : Set M} {A B : GermIdeal n M}
    (hA : ∀ y g, A.mem y g → HolomorphicAt n g y) (hB : ∀ y g, B.mem y g → HolomorphicAt n g y)
    {z : M} {q : M → ℂ}
    (hBg : ∀ g, IsInSpanOnAt (n := n) W (B.mem z) z g ↔ IsInSpanOnAt (n := n) W (· = q) z g) {g : M → ℂ}
    (hg : IsInSpanOnAt (n := n) W ((A.mul B).mem z) z g) :
    ∃ h, HolomorphicAt n h z ∧ IsInSpanOnAt (n := n) W (A.mem z) z h ∧
      ∀ᶠ y in 𝓝 z, y ∈ W → g y = h y * q y := by
  have h1 : IsInSpanOnAt (n := n) W (fun s => ∃ a, A.mem z a ∧ s = fun p => a p * q p) z g := by
    refine IsInSpanOnAt.trans (fun t ht => ?_) hg
    refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (InvertibleIdealQuotient.mem_mul_iff.mp ht))
    rintro s ⟨a, b, ha, hb, rfl⟩
    obtain ⟨c, hc, hbc⟩ :=
      isInSpanOnAt_eq_iff.mp ((hBg b).mp (IsInSpanAt.restrict (isInSpanAt_self hb (hB z b hb))))
    refine ⟨1, fun _ p => a p * q p, fun _ => c, fun _ => ⟨a, ha, rfl⟩, fun _ => hc, ?_⟩
    filter_upwards [hbc] with y hy hyW
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.mul_apply]
    rw [hy hyW]
    ring
  obtain ⟨K, s, c, hs, hc, hsum⟩ := h1
  choose a ha has using hs
  refine ⟨fun p => ∑ k, c k p * a k p, HolomorphicAt.sum _ fun k _ => (hc k).mul (hA z (a k) (ha k)),
    ⟨K, a, c, ha, hc, Eventually.of_forall fun _ _ => rfl⟩, ?_⟩
  filter_upwards [hsum] with y hy hyW
  rw [hy hyW, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [has k]
  ring

/-- **`𝔟 ⊆ 𝓝_N(𝔞)`** when `Res_N (𝔟𝓜) ⊆ Res_N 𝔞`, `𝓜` is monomial along `N` and `𝓜_N(𝔞) = 𝓜_N(𝓜)`: for `g ∈ 𝓜_N(𝔞)_y`,
`g|_N` lies in `𝓜|_N`, so `g f ∈ Res_N (𝔟𝓜) ⊆ Res_N 𝔞`. -/
theorem le_nonmonomialPartAlong_of_factor (hN : IsClosed N) {𝔞 𝔟 𝓜 : GermIdeal n M}
    (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y) (h𝓜 : ∀ y g, 𝓜.mem y g → HolomorphicAt n g y)
    (hmono : IsMonomialAlong n N 𝓜 E) (heq : monomialPartAlong n N 𝔞 E = monomialPartAlong n N 𝓜 E)
    (hf2 : RestrictLe N (𝔟.mul 𝓜) 𝔞) : 𝔟.Le (nonmonomialPartAlong n N 𝔞 E) := by
  intro y f hf
  have hfhol := h𝔟 y f hf
  refine ⟨hfhol, fun g hg => ⟨(hg.1 : HolomorphicAt n g y).mul hfhol, ?_⟩⟩
  by_cases hyN : y ∈ N
  · have hg' : (monomialPartAlong n N 𝓜 E).mem y g := by rw [← heq]; exact hg
    have hf' : IsInSpanOnAt (n := n) N (𝔟.mem y) y f := IsInSpanAt.restrict (isInSpanAt_self hf hfhol)
    have h1 := MarkedIdealOperationsAlong.IsInSpanOnAt.mul hf' (hmono y hyN g hg')
    have h2 : IsInSpanOnAt (n := n) N ((𝔟.mul 𝓜).mem y) y (f * g) := by
      refine IsInSpanOnAt.mono (fun t ht => ?_) h1
      obtain ⟨a, b, ha, hb, rfl⟩ := ht
      exact IdealOrderArithmetic.mul_mem_mul ha hb ((h𝔟 y a ha).mul (h𝓜 y b hb))
    have h3 : IsInSpanOnAt (n := n) N (𝔞.mem y) y (f * g) := IsInSpanOnAt.trans (fun s hs => hf2 y hyN s hs) h2
    have hfg : (fun p => g p * f p) = f * g := funext fun p => mul_comm _ _
    rw [hfg]
    exact h3
  · exact MarkedIdealOperationsAlong.isInSpanOnAt_of_notMem hN hyN _

/-- **`Res_N 𝓝_N(𝔞) ⊆ Res_N 𝔟`** when `Res_N 𝔞 ⊆ Res_N (𝔟𝓜)`, `𝓜` is nonzero and monomial along `N` and
`𝓜_N(𝔞) = 𝓜_N(𝓜)`: at `y ∈ N`, `𝓜_N(𝓜)` and `𝓜` restrict to `(m)` for the local generator `m`
(`MonomialPartAlong.exists_generator_monomialPartAlong`); for `f ∈ 𝓝_N(𝔞)_y`, `m f ∈ Res_N 𝔞 ⊆ Res_N (𝔟 (m))`, so
`m f = m h` on `N` with `h` in the span of `𝔟_y` on `N`; `m` vanishes identically on no open subset of `N`, so `f = h` on
`N` (`RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within`). -/
theorem restrictLe_nonmonomialPartAlong_of_factor (hn : 0 < n) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {𝔞 𝔟 𝓜 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    (h𝓜 : 𝓜.IsCoherent) (hne𝓜 : ∀ y ∈ N, IsNonzeroAlongAt N 𝓜 y) (hmono : IsMonomialAlong n N 𝓜 E)
    (heq : monomialPartAlong n N 𝔞 E = monomialPartAlong n N 𝓜 E) (hf1 : RestrictLe N 𝔞 (𝔟.mul 𝓜)) :
    RestrictLe N (nonmonomialPartAlong n N 𝔞 E) 𝔟 := by
  intro y hyN f hf
  have hhol𝔟 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔟
  have hhol𝓜 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝓜
  obtain ⟨m, hmhol, -, hgen, hfreq⟩ := exists_generator_monomialPartAlong hn hN hE hT h𝓜 hne𝓜 hyN
  have hmy : HolomorphicAt n m y := hmhol.self_of_nhds
  have hmM : (monomialPartAlong n N 𝓜 E).mem y m :=
    (hgen.self_of_nhds m).mpr ⟨hmy, NonmonomialStepAlong.isInSpanOnAt_self_eq⟩
  have hMg : ∀ g, IsInSpanOnAt (n := n) N (𝓜.mem y) y g ↔ IsInSpanOnAt (n := n) N (· = m) y g := by
    intro g
    constructor
    · intro hg
      exact IsInSpanOnAt.trans (fun s hs => ((hgen.self_of_nhds s).mp (le_monomialPartAlong hn hE hT h𝓜 y s hs)).2) hg
    · intro hg
      refine IsInSpanOnAt.trans (fun s hs => ?_) hg
      rw [hs]
      exact hmono y hyN m hmM
  have hm𝔞 : (monomialPartAlong n N 𝔞 E).mem y m := by rw [heq]; exact hmM
  have h1 : IsInSpanOnAt (n := n) N (𝔞.mem y) y (fun p => m p * f p) := (hf.2 m hm𝔞).2
  have h2 : IsInSpanOnAt (n := n) N ((𝔟.mul 𝓜).mem y) y (fun p => m p * f p) :=
    IsInSpanOnAt.trans (fun s hs => hf1 y hyN s hs) h1
  obtain ⟨h, hh, hhspan, hfh⟩ := exists_isInSpanOnAt_of_mul_generator hhol𝔟 hhol𝓜 hMg h2
  obtain ⟨U, hUsub, hUo, hyU⟩ := eventually_nhds_iff.mp hfreq
  have hnon : ∀ V : Set M, IsOpen V → V ⊆ U → (V ∩ N).Nonempty → ∃ w ∈ V ∩ N, m w ≠ 0 := by
    rintro V hVo hVU ⟨p, hpV, hpN⟩
    obtain ⟨w, ⟨hwN, hwm⟩, hwV⟩ := ((hUsub p (hVU hpV) hpN).and_eventually (hVo.mem_nhds hpV)).exists
    exact ⟨w, ⟨hwV, hwN⟩, hwm⟩
  have hcan := RestrictedIdealQuotient.eventuallyEq_within_of_mul_eventuallyEq_within hUo hnon hyU hf.1 hh
    (hfh.mono fun p hp hpN => by linear_combination hp hpN)
  obtain ⟨K, s, c, hs, hc, hsum⟩ := hhspan
  refine ⟨K, s, c, hs, hc, ?_⟩
  filter_upwards [hcan, hsum] with p hp1 hp2 hpN
  rw [hp1 hpN, hp2 hpN]

/-- **A coherent ideal lies in its nonmonomial part along `N`**: `𝔞 ⊆ (Res_N 𝔞 : 𝓜_N(𝔞))`. -/
theorem le_nonmonomialPartAlong_self {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    𝔞.Le (nonmonomialPartAlong n N 𝔞 E) := by
  intro y f hf
  have hfhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞 y f hf
  refine ⟨hfhol, fun g hg => ⟨(hg.1 : HolomorphicAt n g y).mul hfhol, ?_⟩⟩
  exact IsInSpanAt.restrict (isInSpanAt_self (CompanionReduction.mul_mem_of_isCoherent h𝔞 hg.1 hf)
    ((hg.1 : HolomorphicAt n g y).mul hfhol))

open Classical in
/-- **The monomial part along `N` is principal monomial at every point of `N`**, in coordinates adapted to `N` and `E`
(`MonomialPartAlong.monomialPartAlong_mem_iff`). -/
theorem isPrincipalMonomialAlongAt_monomialPartAlong (hn : 0 < n) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N 𝔞 y) {x : M} (hx : x ∈ N) :
    IsPrincipalMonomialAlongAt n N (monomialPartAlong n N 𝔞 E) E x := by
  obtain ⟨kC, kN, Φ, σ, hΦsrc, hσk, hσinj, hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT hT.hasNormalCrossings hx
  have hNflat : ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n kN) :=
    fun hz1 hz2 => (hflat hz1 hz2).2.1
  have hA : ∀ i, x ∈ E.get i → ∀ {z : M}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x z) (σ i) = 0) :=
    fun i hi _ hz1 hz2 => (hflat hz1 hz2).2.2 i hi
  have hmem := (monomialPartAlong_mem_iff hΦsrc hNflat hA hn hN hE hT h𝔞 hne hx hσk hσinj).self_of_nhds
  have hgen : HolomorphicAt n (fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ E.get i),
      flatCoord Φ (σ i) z ^ divExpAlong n N 𝔞 (E.get i) x) x :=
    holomorphicAt_generator _ _ (mem_flatDomain_self Φ)
  refine ⟨kN, Φ, σ, fun i => divExpAlong n N 𝔞 (E.get i) x, hΦsrc, hNflat, hσk, hσinj, hA,
    fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact IsInSpanOnAt.trans (fun s hs => ((hmem s).mp hs).2) hg
  · refine IsInSpanOnAt.trans (fun s hs => ?_) hg
    rw [hs]
    exact IsInSpanAt.restrict (isInSpanAt_self ((hmem _).mpr ⟨hgen, NonmonomialStepAlong.isInSpanOnAt_self_eq⟩) hgen)

/-- **The hypotheses of the companion tower for the parts of a marked ideal along `N`** (`n > 0`, well formed, `𝔞`
nonzero along `N`): `𝓝_N(𝔞)` and `𝓜_N(𝔞)` are coherent, `𝓜_N(𝔞)` is nonzero and monomial along `N`, `𝓝_N(𝔞)` is nonzero
along `N` and in the ideal of no member on `N`, and `𝔪` is restricted-equivalent to `(N, E, 𝓝_N(𝔞) 𝓜_N(𝔞), d)`. -/
theorem parts_hypotheses (hn : 0 < n) (𝔪 : MarkedIdeal n M) (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) :
    (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).IsCoherent ∧ (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).IsCoherent ∧
      (∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) y) ∧
      IsMonomialAlong n 𝔪.N (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) 𝔪.E ∧
      (∀ y ∈ 𝔪.N, ∀ i, y ∈ 𝔪.E.get i → ∃ a, (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mem y a ∧
        ¬ IsInSpanOnAt (n := n) 𝔪.N ((vanishingIdeal (n := n) (𝔪.E.get i)).mem y) y a) ∧
      (∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) y) ∧
      RestrictEquiv 𝔪 ⟨𝔪.N, 𝔪.E, (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E).mul
        (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E), 𝔪.d⟩ := by
  have hN := h𝔪.isClosedSubmanifold_N
  have hE := h𝔪.isSNCDivisor
  have hTr := h𝔪.isTransverse
  have h𝔞 := h𝔪.isCoherent
  have h𝓜 := isCoherent_monomialPartAlong hn hN hE hTr h𝔞 hne
  refine ⟨isCoherent_nonmonomialPartAlong hn hN hE hTr h𝔞 hne, h𝓜, fun y hy => ?_,
    (isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hN hE hTr h𝓜
      fun x hx => isPrincipalMonomialAlongAt_monomialPartAlong hn hN hE hTr h𝔞 hne hx).2,
    fun y hy i hyi => exists_mem_nonmonomialPartAlong_not hn hN hE hTr h𝔞 hne hy hyi, fun y hy => ?_, ?_⟩
  · obtain ⟨m, hmhol, -, hgen, hfreq⟩ := exists_generator_monomialPartAlong hn hN hE hTr h𝔞 hne hy
    exact ⟨m, (hgen.self_of_nhds m).mpr ⟨hmhol.self_of_nhds, NonmonomialStepAlong.isInSpanOnAt_self_eq⟩,
      hfreq.self_of_nhds hy⟩
  · obtain ⟨g, hg, hgf⟩ := hne y hy
    exact ⟨g, le_nonmonomialPartAlong_self h𝔞 y g hg, hgf⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · have h := restrictLe_mul_along hn hN hE hTr h𝔞 hne
      rw [RestrictLeCalculus.mul_comm'] at h
      exact h
    · have h := restrictLe_mul_along' (E := 𝔪.E) hN h𝔞
      rw [RestrictLeCalculus.mul_comm'] at h
      exact h

end Unique

/-! ### The transforms of the monomial and nonmonomial parts along the companion tower -/

section Main

variable {X : CMfd.{u} n}

/-- **The transforms of the monomial and nonmonomial parts inside a submanifold** (`hir:nonmonomial-transform` for
`N ≠ M`; Bierstone--Milman 2008 §5, Włodarczyk 2005 Step 2a).  Let `(X, N, E, 𝔞, d)` be well formed with `𝔞` nonzero
along `N`, `o ≥ 1`, and `ord(𝓝_N(𝔞)|_N) ≤ o` on `cosupp(𝔞|_N, d)`.  Along every multiple test blow-up `T` of the companion
ideal of `(𝓝_N(𝔞), 𝓜_N(𝔞), o)`: `T` is a multiple test blow-up of `(X, N, E, 𝔞, d)`, the transform `𝔪_T` is well formed,
the transform `𝔫_T` of `(N, E, 𝓝_N(𝔞), o)` lives on `N_T`, is coherent, contained in the nonmonomial part
`𝓝_{N_T}(𝔞_T)` of the transform and equal to it on `N_T`; the monomial part `𝓜_{N_T}(𝔞_T)` is that of a coherent
`𝓜_T` nonzero and monomial along `N_T`; and `ord(𝓝_{N_T}(𝔞_T)|_{N_T}) ≤ o` on `cosupp 𝔪_T`. -/
theorem nonmonomialPart_geoTransformAlong_along (hn : 0 < n) (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔪.cosupp, x ∉ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) (o + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)
      (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d) T) :
    IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsWellFormed ∧
      (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).N =
        (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal.IsCoherent ∧
      (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal.Le
        (nonmonomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E) ∧
      RestrictLe (geoTransformAlong 𝔪 T).N
        (nonmonomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E)
        (geoTransformAlong (⟨𝔪.N, 𝔪.E, nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E, o⟩ : MarkedIdeal n X) T).ideal ∧
      (∃ 𝓜T : GermIdeal n Y, 𝓜T.IsCoherent ∧
        (∀ y ∈ (geoTransformAlong 𝔪 T).N, IsNonzeroAlongAt (geoTransformAlong 𝔪 T).N 𝓜T y) ∧
        IsMonomialAlong n (geoTransformAlong 𝔪 T).N 𝓜T (geoTransformAlong 𝔪 T).E ∧
        monomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E =
          monomialPartAlong n (geoTransformAlong 𝔪 T).N 𝓜T (geoTransformAlong 𝔪 T).E) ∧
      ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, z ∉ cosupport n (geoTransformAlong 𝔪 T).N
        (nonmonomialPartAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E)
        (o + 1) := by
  have hN := h𝔪.isClosedSubmanifold_N
  have hE := h𝔪.isSNCDivisor
  have hTr := h𝔪.isTransverse
  have h𝔞 := h𝔪.isCoherent
  obtain ⟨h𝓝, h𝓜, hne𝓜, hmono, hnd, hnz, hREq⟩ := parts_hypotheses hn 𝔪 h𝔪 hne
  set 𝔟₀ := nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E with h𝔟₀def
  set 𝓜₀ := monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E with h𝓜₀def
  have hcohP : (𝔟₀.mul 𝓜₀).IsCoherent := isCoherent_mul h𝓝 h𝓜
  have hbound' : ∀ x ∈ cosupport n 𝔪.N (𝔟₀.mul 𝓜₀) 𝔪.d, x ∉ cosupport n 𝔪.N 𝔟₀ (o + 1) := fun x hx =>
    hbound x (by rw [hREq.cosupp_eq]; exact hx)
  obtain ⟨hwf₀, hNeq, -, hcoh𝔫T, hnzT, hndT, 𝓜T, h𝓜T, hf1, hf2, hne𝓜T, hmonoT⟩ :=
    factor_along_along hn hN hE hTr h𝓝 h𝓜 hne𝓜 hmono hnd hnz ho hbound' T hT
  obtain ⟨hT₀, -, hbT, -⟩ := companion_reduction_along hN 𝔪.E h𝓝 h𝓜 ho hbound' T hT
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hREq hN.1 h𝔞 hcohP
  have hTm : IsGeoTestTower 𝔪 T := ((hW.2 T).1).mpr hT₀
  have hwf : (geoTransformAlong 𝔪 T).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T hTm
  have hREqT : RestrictEquiv (geoTransformAlong 𝔪 T)
      (geoTransformAlong (⟨𝔪.N, 𝔪.E, 𝔟₀.mul 𝓜₀, 𝔪.d⟩ : MarkedIdeal n X) T) := by
    cases T with
    | refl => exact hREq
    | step T' C π hπ =>
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hREq hN.1 h𝔞 hcohP T' C π hπ]
      exact RestrictEquiv.refl hwf₀.isCoherent
  have hN' := hREqT.N_eq
  have hE' := hREqT.E_eq
  rw [← hN'] at hnzT hne𝓜T hf1 hf2 hNeq
  rw [← hN', ← hE'] at hndT hmonoT
  have hf1' := RestrictLeCalculus.RestrictLe.trans hREqT.le hf1
  have hf2' := RestrictLeCalculus.RestrictLe.trans hf2 hREqT.ge
  have heqM := monomialPartAlong_eq_of_factor hn hwf.isClosedSubmanifold_N hwf.isSNCDivisor hwf.isTransverse
    hcoh𝔫T h𝓜T hndT hf1' hf2'
  have hL := le_nonmonomialPartAlong_of_factor hwf.isClosedSubmanifold_N.1
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh𝔫T)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝓜T) hmonoT heqM hf2'
  have hR := restrictLe_nonmonomialPartAlong_of_factor hn hwf.isClosedSubmanifold_N hwf.isSNCDivisor
    hwf.isTransverse hcoh𝔫T h𝓜T hne𝓜T hmonoT heqM hf1'
  refine ⟨hTm, hwf, hNeq, hcoh𝔫T, hL, hR, ⟨𝓜T, h𝓜T, hne𝓜T, hmonoT, heqM⟩, fun z hz hz' => ?_⟩
  have hz₀ : z ∈ (geoTransformAlong (⟨𝔪.N, 𝔪.E, 𝔟₀.mul 𝓜₀, 𝔪.d⟩ : MarkedIdeal n X) T).cosupp := by
    rw [← hREqT.cosupp_eq]; exact hz
  refine hbT z hz₀ ?_
  rw [hNeq]
  exact ⟨hz'.1, fun g hg => hz'.2 g (hL z g hg)⟩

end Main

end

end Hironaka.NonmonomialTransformAlong
