/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.NonmonomialOrderZero
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GeoTransformWellFormed
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial phase of the general step: the invariant `γ` where the nonmonomial part has order zero

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (where the nonmonomial part is
trivial the marked ideal is monomial and Step 2b, the monomial case, applies); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.A.

At a point of order `ν = 0` of the nonmonomial part the general step's value is read off the invariant
`γ_𝔫 = MonomialCaseAlong.gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d` of the current marked ideal.  The monomial case along `N`
(`MonomialCaseAlong`, `MonomialStepAlong`) needs a marked ideal which is monomial along all of `N`; here the marked ideal is
monomial only on the open set `ordMask 𝔫 0 = {ν = 0}` (`NonmonomialOrderZero.isMonomialAlong_pullback_val`).  This module
restricts to that open set, applies the monomial case there, and reads the result back
(`MarkedIdealRestrictOpen.geoTransform_pullback_val`, `MonomialInvariantFunctorialAlong.gammaAlong_pullback_val`).  For
`𝔫` in the domain (`IsInvDomain k 𝔫`) and `n > 0`:

* `isMonomialAlong_pullback_val_ordMask`: `𝔫|_{ordMask 𝔫 0}` is monomial along its submanifold;
* **`isAdmissibleCentre_gammaAlong_level_of_ordZero`** (property (1) at `o = 0`): on an open `W` on which the
  cosupport has order `0` and `γ ≤ v`, the points of the cosupport with `γ = v` form an admissible centre of `𝔫|_W`
  (the patching of `MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens`); in particular the
  maximum locus of `γ_𝔫` on a cosupport of order `0` is an admissible centre;
* **`gammaAlong_geoTransform_eq_of_notMem_of_ordZero`** (properties (3), (4) off the centre at `o = 0`): for any admissible
  centre `C` (`C = ∅` allowed) and `z ∈ N'` with `π z ∉ C` of order `0`, `γ_{𝔫'}(z) = γ_𝔫(π z)`;
* **`gammaAlong_geoTransform_lt_of_ordZero`** (property (3) over the centre at `o = 0`): if the whole cosupport has order
  `0` and `C` is the maximum locus of `γ_𝔫` on it, `γ_{𝔫'}(z) < γ_𝔫(π z)` at every `z ∈ N'` over `C`.

Upper semicontinuity of `γ_𝔫` on `N` needs no monomiality (`MonomialCaseAlong.eventually_gammaAlong_le`, with
`IsInvDomain.isNonzeroAlongAt`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderMonomial

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.MonomialInvariant Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Monomial on the mask of order zero -/

section Mask

variable {Y : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}

/-- **On the mask of order `0` the marked ideal is monomial** along its submanifold
(`NonmonomialOrderZero.isMonomialAlong_pullback_val`; the mask misses `{ν ≥ 1}`). -/
theorem isMonomialAlong_pullback_val_ordMask (h𝔞 : 𝔫.ideal.IsCoherent) :
    IsMonomialAlong n (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).N
      (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).ideal
      (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).E :=
  NonmonomialOrderZero.isMonomialAlong_pullback_val h𝔞 (ordMask 𝔫 0) fun _ hy => notMem_ordGe_of_mem_ordMask hy

/-- **A point of order `0` lies in the mask of order `0`.** -/
theorem mem_ordMask_zero (hn : 0 < n) (h : IsInvDomain k 𝔫) {y : Y} (hy : y ∉ ordGe 𝔫 1) : y ∈ ordMask 𝔫 0 :=
  (mem_ordMask_iff hn h.isWellFormed h.isNonzeroAlongAt 0 y).mpr hy

/-- **Admissible level sets of `γ` where the cosupport has order `0`** (property (1) of `hir:general-step` at `o = 0`;
`n > 0`, `𝔫` in the domain): on an open `W` on which every point of the cosupport has order `0` and `γ_𝔫 ≤ v`, the points of
the cosupport over `W` with `γ_𝔫 = v` form an admissible centre of `𝔫|_W`.  Near a point of `W` of order `0`, on
`W ∩ ordMask 𝔫 0` the marked ideal is monomial and `MonomialCaseAlong.isAdmissibleCentre_gammaAlong_eq` applies (`γ = ⊥`
exactly off the cosupport there); near a point of `W` of order `≥ 1` there is no point of the cosupport; the pieces are
patched by `MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens`. -/
theorem isAdmissibleCentre_gammaAlong_level_of_ordZero (hn : 0 < n) (h : IsInvDomain k 𝔫) (W : Opens Y)
    (v : WithBot Val) (h0 : ∀ y ∈ 𝔫.cosupp, y ∈ W → y ∉ ordGe 𝔫 1)
    (hv : ∀ y ∈ 𝔫.cosupp, y ∈ W → gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d y ≤ v) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ 𝔫.cosupp ∧ gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d y = v}) := by
  have h𝔞 := h.isWellFormed.isCoherent
  have hhol : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hcl : IsClosed 𝔫.cosupp :=
    GiraudAlong.isClosed_cosupport_along h𝔞 h.isWellFormed.isClosedSubmanifold_N 𝔫.d
  refine MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens h𝔞 W fun x hxW => ?_
  by_cases hx0 : x ∈ ordGe 𝔫 1
  · -- near a point of order `≥ 1` of `W` there is no point of the cosupport
    have hxc : x ∉ 𝔫.cosupp := fun hc => h0 x hc hxW hx0
    refine ⟨W ⊓ ⟨𝔫.cosuppᶜ, hcl.isOpen_compl⟩, ⟨hxW, hxc⟩, inf_le_left, ?_⟩
    have hemp : (Subtype.val : (W ⊓ ⟨𝔫.cosuppᶜ, hcl.isOpen_compl⟩ : Opens Y) → Y) ⁻¹'
        {y | y ∈ 𝔫.cosupp ∧ gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d y = v} = ∅ := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hq
      exact absurd hq q.2.2
    rw [hemp]
    exact isAdmissibleCentre_empty _
  · -- near a point of order `0`: the monomial case on `W ∩ ordMask 𝔫 0`
    set V : Opens Y := W ⊓ ordMask 𝔫 0 with hVdef
    have hxV : x ∈ V := ⟨hxW, mem_ordMask_zero hn h hx0⟩
    refine ⟨V, hxV, inf_le_left, ?_⟩
    have hV := InvDomainTowerAlong.isInvDomain_pullback_val V h
    have hmono : IsMonomialAlong n (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N
        (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).E :=
      NonmonomialOrderZero.isMonomialAlong_pullback_val h𝔞 V fun _ hy => notMem_ordGe_of_mem_ordMask hy.2
    have hwfV := hV.isWellFormed
    have hcosV := cosupp_pullback_val 𝔫 hhol V
    have hγ : ∀ q : V,
        gammaAlong n (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).E
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).d q =
          gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d q.1 :=
      fun q => MonomialInvariantFunctorialAlong.gammaAlong_pullback_val 𝔫 hhol V q 𝔫.d
    have hbot : ∀ q : V, q ∈ (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N →
        (gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d q.1 = ⊥ ↔ q.1 ∉ 𝔫.cosupp) := by
      intro q hq
      rw [← hγ q, gammaAlong_eq_bot_iff_of_isMonomialAlong hn hwfV.isClosedSubmanifold_N hwfV.isSNCDivisor
        hwfV.isTransverse hwfV.isCoherent hV.isNonzeroAlongAt hmono _ hq]
      show q ∉ (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).cosupp ↔ _
      rw [hcosV]
      rfl
    cases v with
    | bot =>
      have hemp : (Subtype.val : V → Y) ⁻¹' {y | y ∈ 𝔫.cosupp ∧ gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d y = ⊥} = ∅ := by
        ext q
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hq hγq
        have hqN : q ∈ (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N := 𝔫.cosupp_subset_N hq
        exact (hbot q hqN).mp hγq hq
      rw [hemp]
      exact isAdmissibleCentre_empty _
    | coe w =>
      have hmax : ∀ q ∈ (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N,
          gammaAlong n (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).E
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).d q ≤ (w : WithBot Val) := by
        intro q hqN
        rw [hγ q]
        by_cases hq : q.1 ∈ 𝔫.cosupp
        · exact hv q.1 hq q.2.1
        · rw [(hbot q hqN).mpr hq]
          exact bot_le
      have hadm := isAdmissibleCentre_gammaAlong_eq hn hwfV.isClosedSubmanifold_N hwfV.isSNCDivisor
        hwfV.isTransverse hwfV.isCoherent hV.isNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫) rfl rfl
        rfl rfl hmono hmax
      have hset : {q | q ∈ (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N ∧
          gammaAlong n (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).ideal (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).E
            (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).d q = (w : WithBot Val)} =
          (Subtype.val : V → Y) ⁻¹' {y | y ∈ 𝔫.cosupp ∧ gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d y = w} := by
        ext q
        simp only [mem_preimage, mem_ofPred_eq, hγ q]
        constructor
        · rintro ⟨hqN, hγq⟩
          refine ⟨?_, hγq⟩
          by_contra hq
          rw [(hbot q hqN).mpr hq] at hγq
          exact WithBot.bot_ne_coe hγq
        · rintro ⟨hq, hγq⟩
          exact ⟨𝔫.cosupp_subset_N hq, hγq⟩
      rw [← hset]
      exact hadm

end Mask

/-! ### One blowup, read on the mask -/

section Step

variable {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y} {C : Set Y} {π : Z → Y}

/-- **The invariant of a transform, read on an open set**: for an open `W` of the base, `V = π⁻¹W` and the restriction
`r : V → W` of the blowup, the invariant along `N'` of the transform of `𝔫|_W` at `p` is that of the transform of `𝔫` at
`p` (coherent ideal and coherent transformed ideal). -/
theorem gammaAlong_geoTransform_pullback_val (h𝔞 : 𝔫.ideal.IsCoherent) (hπ : IsBlowupAlong n C π)
    (hc : (𝔫.geoTransform C π).ideal.IsCoherent) (W : Opens Y) (hV : IsOpen (π ⁻¹' (W : Set Y)))
    (p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z)) (d : ℕ) :
    gammaAlong n ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W)
        (fun p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) => (⟨π p.1, p.2⟩ : W))).N
      ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W)
        (fun p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) => (⟨π p.1, p.2⟩ : W))).ideal
      ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W)
        (fun p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) => (⟨π p.1, p.2⟩ : W))).E d p =
      gammaAlong n (𝔫.geoTransform C π).N (𝔫.geoTransform C π).ideal (𝔫.geoTransform C π).E d p.1 := by
  rw [geoTransform_pullback_val h𝔞 hπ hc W hV]
  exact MonomialInvariantFunctorialAlong.gammaAlong_pullback_val (𝔫.geoTransform C π)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg) _ p d

/-- **Off the centre, at a point of order `0`, the invariant does not change** (properties (3) and (4) of
`hir:general-step` off the centre, at `o = 0`; `n > 0`, `𝔫` in the domain): for an admissible centre `C` (possibly empty)
and `z ∈ N'` with `π z ∉ C` and `ν(π z) = 0`, `γ_{𝔫'}(z) = γ_𝔫(π z)`.  On `W = ordMask 𝔫 0` the marked ideal is monomial,
and `MonomialStepAlong.gammaAlong_geoTransform_eq_of_notMem` applies to `𝔫|_W` and the restricted blowup. -/
theorem gammaAlong_geoTransform_eq_of_notMem_of_ordZero (hn : 0 < n) (h : IsInvDomain k 𝔫)
    (hC : 𝔫.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {z : Z} (hzN : z ∈ (𝔫.geoTransform C π).N)
    (hz : π z ∉ C) (h0 : π z ∉ ordGe 𝔫 1) (d : ℕ) :
    gammaAlong n (𝔫.geoTransform C π).N (𝔫.geoTransform C π).ideal (𝔫.geoTransform C π).E d z =
      gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E d (π z) := by
  have h𝔞 := h.isWellFormed.isCoherent
  have hc : (𝔫.geoTransform C π).ideal.IsCoherent :=
    (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre h.isWellFormed hC hπ).isCoherent
  set W : Opens Y := ordMask 𝔫 0 with hWdef
  have hV : IsOpen (π ⁻¹' (W : Set Y)) := W.isOpen.preimage hπ.contMDiff.continuous
  set r : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) → W := fun p => (⟨π p.1, p.2⟩ : W) with hrdef
  have hr : IsBlowupAlong n ((↑) ⁻¹' C : Set W) r := BlowupRestrictOpen.isBlowupAlong_restrict hπ W hV
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hmono := isMonomialAlong_pullback_val_ordMask (𝔫 := 𝔫) h𝔞
  have heq := geoTransform_pullback_val h𝔞 hπ hc W hV
  have hzW : π z ∈ (W : Set Y) := mem_ordMask_zero hn h h0
  set p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) := ⟨z, hzW⟩ with hpdef
  have hc' : ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W) r).ideal.IsCoherent := by
    rw [heq]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hpN : p ∈ ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W) r).N := by
    rw [heq]
    exact hzN
  have hrp : r p ∉ ((↑) ⁻¹' C : Set W) := hz
  have key := MonomialStepAlong.gammaAlong_geoTransform_eq_of_notMem hn hW.isWellFormed hW.isNonzeroAlongAt hmono hr
    hc' hpN hrp d
  rw [gammaAlong_geoTransform_pullback_val h𝔞 hπ hc W hV p d,
    MonomialInvariantFunctorialAlong.gammaAlong_pullback_val 𝔫
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) W (r p) d] at key
  exact key

/-- **The maximum locus of `γ` on a cosupport of order `0`, read on the mask**: if every point of the cosupport has order
`0`, the trace on `W = ordMask 𝔫 0` of the maximum locus of `γ_𝔫` on the cosupport is the maximum locus of `γ` of `𝔫|_W` on
its cosupport (`MonomialStepAlong.maxLocusA`). -/
theorem preimage_maxLocus_gammaAlong_eq_maxLocusA (hn : 0 < n) (h : IsInvDomain k 𝔫)
    (hcos : ∀ y ∈ 𝔫.cosupp, y ∉ ordGe 𝔫 1) :
    (Subtype.val : ordMask 𝔫 0 → Y) ⁻¹' maxLocus (gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d) 𝔫.cosupp =
      maxLocusA (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫) := by
  have h𝔞 := h.isWellFormed.isCoherent
  have hhol : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hcosW := cosupp_pullback_val 𝔫 hhol (ordMask 𝔫 0)
  have hγ : ∀ q : ordMask 𝔫 0,
      gammaAlong n (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).N
          (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).ideal
          (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).E
          (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).d q =
        gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d q.1 :=
    fun q => MonomialInvariantFunctorialAlong.gammaAlong_pullback_val 𝔫 hhol (ordMask 𝔫 0) q 𝔫.d
  ext p
  show p.1 ∈ maxLocus _ 𝔫.cosupp ↔ p ∈ maxLocus _ (MarkedIdeal.pullback (Subtype.val : ordMask 𝔫 0 → Y) 𝔫).cosupp
  simp only [maxLocus, mem_ofPred_eq, hcosW, mem_preimage, hγ]
  constructor
  · rintro ⟨hp, hmax⟩
    exact ⟨hp, fun q hq => hmax q.1 hq⟩
  · rintro ⟨hp, hmax⟩
    exact ⟨hp, fun y hy => hmax ⟨y, mem_ordMask_zero hn h (hcos y hy)⟩ hy⟩

/-- **Over the centre, on a cosupport of order `0`, the invariant drops** (property (3) of `hir:general-step` over the
centre, at `o = 0`; `n > 0`, `𝔫` in the domain): if every point of the cosupport has order `0` and `C` is the maximum locus
of `γ_𝔫` on the cosupport, then `γ_{𝔫'}(z) < γ_𝔫(π z)` at every `z ∈ N'` over `C`.  On `W = ordMask 𝔫 0` the trace of `C`
is the maximum locus of `γ` of the monomial marked ideal `𝔫|_W` (`preimage_maxLocus_gammaAlong_eq_maxLocusA`), and
`MonomialStepAlong.gammaAlong_geoTransform_lt_of_mem` applies to the restricted blowup. -/
theorem gammaAlong_geoTransform_lt_of_ordZero (hn : 0 < n) (h : IsInvDomain k 𝔫)
    (hcos : ∀ y ∈ 𝔫.cosupp, y ∉ ordGe 𝔫 1) (hCeq : C = maxLocus (gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d) 𝔫.cosupp)
    (hCadm : 𝔫.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {z : Z} (hzN : z ∈ (𝔫.geoTransform C π).N)
    (hz : π z ∈ C) :
    gammaAlong n (𝔫.geoTransform C π).N (𝔫.geoTransform C π).ideal (𝔫.geoTransform C π).E 𝔫.d z <
      gammaAlong n 𝔫.N 𝔫.ideal 𝔫.E 𝔫.d (π z) := by
  have h𝔞 := h.isWellFormed.isCoherent
  set W : Opens Y := ordMask 𝔫 0 with hWdef
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hmono := isMonomialAlong_pullback_val_ordMask (𝔫 := 𝔫) h𝔞
  have hset : ((↑) ⁻¹' C : Set W) = maxLocusA (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) := by
    rw [hCeq]
    exact preimage_maxLocus_gammaAlong_eq_maxLocusA hn h hcos
  have hc : (𝔫.geoTransform C π).ideal.IsCoherent :=
    (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre h.isWellFormed hCadm hπ).isCoherent
  have hV : IsOpen (π ⁻¹' (W : Set Y)) := W.isOpen.preimage hπ.contMDiff.continuous
  set r : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) → W := fun p => (⟨π p.1, p.2⟩ : W) with hrdef
  have hr : IsBlowupAlong n ((↑) ⁻¹' C : Set W) r := BlowupRestrictOpen.isBlowupAlong_restrict hπ W hV
  have heq := geoTransform_pullback_val h𝔞 hπ hc W hV
  have hzW : π z ∈ (W : Set Y) := mem_ordMask_zero hn h (hcos _ (hCeq ▸ hz).1)
  set p : (⟨π ⁻¹' (W : Set Y), hV⟩ : Opens Z) := ⟨z, hzW⟩ with hpdef
  have hc' : ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W) r).ideal.IsCoherent := by
    rw [heq]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hpN : p ∈ ((MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).geoTransform ((↑) ⁻¹' C : Set W) r).N := by
    rw [heq]
    exact hzN
  have hrp : r p ∈ ((↑) ⁻¹' C : Set W) := hz
  rw [hset] at hr hc' hpN hrp
  have key := MonomialStepAlong.gammaAlong_geoTransform_lt_of_mem hn hW.isWellFormed hW.isNonzeroAlongAt hmono hr
    hc' hpN hrp
  rw [← hset] at key
  rw [gammaAlong_geoTransform_pullback_val h𝔞 hπ hc W hV p,
    MonomialInvariantFunctorialAlong.gammaAlong_pullback_val 𝔫
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) W (r p)] at key
  exact key

end Step

end

end Hironaka.NonmonomialOrderMonomial
