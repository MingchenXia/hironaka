/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionReduction
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GeoTransformWellFormed
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialStepAlong
import Hironaka.Invariant.NonmonomialTransformAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Invariant.StepOneRegime
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The order of the nonmonomial part along canonical segments of the general step

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

The value of the general step at a point `y` of the cosupport has as first entry the order `ν(y) = ord_y(𝓝(𝔪_T)|_{N_T})` of
the nonmonomial part (`NonmonomialOrderLocal.nmOrd`), followed by a value read off the companion ideal (`o ≥ 1`) or the
monomial invariant (`o = 0`).  This module proves what follows from that first entry alone, for ANY value function `f`
whose order dominates `ν` (`OrdMonotone`: `f T y ≤ f T y'` gives `ν y ≤ ν y'` on the cosupport, along multiple test
blow-ups; true for `toLex (ν, ·)`, `ordMonotone_toLex`):

* **`nmOrd_geoTransform_le_of_level`**: `ν` does not go up over an admissible centre on which it is constant -- for every
  value `q` of `ν`; the case `q = 0` (`notMem_ordGe_one_geoTransform_of_mem`, points over a centre of order `0` keep order
  `0`) is new here, the case `q ≥ 1` is `NonmonomialOrderLocal.nmOrd_geoTransform_le_of_mem`;
* the maximum locus of `f` lies in one level set of `ν` (`nmOrd_eq_of_mem_maxLocus`, `nmOrd_le_of_mem_maxLocus`);
  **`nmOrd_step_le_of_canonical`**, **`nmOrd_le_nmOrd_proj`**: along a canonical segment of `f` which is a multiple test
  blow-up, `ν(z) ≤ ν(π z)` at every point of the cosupport -- the order never goes up along the segment;
* **`isInvUSCOn_of_ordMonotone`**: `f` is upper semicontinuous on the cosupport as soon as it is so among the nearby points
  of the same order (the closed sets `{ν ≥ q}`);
* **re-basing at the start of the run** (`NonmonomialOrderRegime.OrdRegime`): `mem_cosupp_and_succ_le_before_start` -- if
  the run of `y` (with `ν(y) = o`) is shorter than the tower, the image of `y` one stage before its start lies in the
  cosupport with `ν ≥ o + 1`; **`centresOrdGt_of_canonical`** -- if a point of order `≥ o + 1` lies in the cosupport at the
  stage before the last step of `M σ`, every centre of `M σ` lies in `{ν ≥ o + 1}`, the hypothesis of
  `NonmonomialOrderRegime.centresAvoid_of_centresOrdGt` / `companionOf_rebase_of_centresOrdGt`;
  `centresAvoid_of_canonical`: hence the centres between two start stages miss an open set on which `ν ≤ o`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.GermIdealOrder Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.RestrictEmptyTower Hironaka.RelativePrincipalizationSpan Hironaka.InvertibleIdealQuotient Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealExtension Hironaka.IdealWeightPowers Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Over a centre of order zero the order stays zero -/

section Zero

/-- **Over a centre of order `0` the order stays `0`** (`𝔫` in the domain, `n > 0`): if the admissible centre `C` of a
blowup misses `{ν ≥ 1}`, every point of the strict transform `N'` over `C` has `ν = 0`.  With `𝔞|_N = 𝓝 𝓜` (the
nonmonomial and monomial parts), `NonmonomialStepAlong.step_along` at `o = 0` factors the transform as `𝔟' 𝓜'` with `𝓜'`
monomial and `𝔟' = (π^*𝓝 : 1)` the transform of `(N, E, 𝓝, 0)`; then `𝔟' ⊆ 𝓝(𝔞')`
(`NonmonomialTransformAlong.le_nonmonomialPartAlong_of_factor`), and the pullback of a germ of `𝓝` not vanishing at `π z`
is a germ of `𝓝(𝔞')` not vanishing at `z`. -/
theorem notMem_ordGe_one_geoTransform_of_mem (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hC0 : Disjoint C (ordGe 𝔫 1)) {z : Z} (hzN : z ∈ (𝔫.geoTransform C π).N) (hzC : π z ∈ C) :
    z ∉ ordGe (𝔫.geoTransform C π) 1 := by
  have h𝔪 := h.isWellFormed
  have hN := h𝔪.isClosedSubmanifold_N
  obtain ⟨h𝓝, h𝓜, hne𝓜, hmono, hnd, hnz, hREq⟩ :=
    NonmonomialTransformAlong.parts_hypotheses hn 𝔫 h𝔪 h.isNonzeroAlongAt
  set 𝔟 := nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E with h𝔟def
  set 𝓜 := monomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E with h𝓜def
  have hhol𝔟 := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝓝
  have hcohP : (𝔟.mul 𝓜).IsCoherent := isCoherent_mul h𝓝 h𝓜
  have hCa : C ⊆ cosupport n 𝔫.N (𝔟.mul 𝓜) 𝔫.d := by
    have h1 := hC.2.1
    rw [hREq.cosupp_eq] at h1
    exact h1
  have hCb : C ⊆ cosupport n 𝔫.N 𝔟 0 := by
    rw [cosupport_zero hhol𝔟]
    exact fun x hx => 𝔫.cosupp_subset_N (hC.2.1 hx)
  have hbd : ∀ x ∈ C, x ∉ cosupport n 𝔫.N 𝔟 (0 + 1) := fun x hx => Set.disjoint_left.mp hC0 hx
  obtain ⟨h𝓜', f1, f2, hP', hnd', -⟩ :=
    NonmonomialStepAlong.step_along hn hπ hN h𝔪.isSNCDivisor h𝔪.isTransverse h𝓝 h𝓜 hne𝓜 hmono hnd hnz
      hC.2.2 hCb hCa hbd
  have hwf' : (𝔫.geoTransform C π).IsWellFormed :=
    GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre h𝔪 hC hπ
  have h𝔪eq : 𝔫.geoTransform C π = (⟨𝔫.N, 𝔫.E, 𝔟.mul 𝓜, 𝔫.d⟩ : MarkedIdeal n Y).geoTransform C π :=
    hREq.geoTransform_eq hN.1 h𝔪.isCoherent hcohP hπ.contMDiff
  have hcoh𝔟' : ((⟨𝔫.N, 𝔫.E, 𝔟, 0⟩ : MarkedIdeal n Y).geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      (𝔪 := ⟨𝔫.N, 𝔫.E, 𝔟, 0⟩) hN h𝓝 ⟨hπ.1, hCb, hC.2.2⟩ hπ
  obtain ⟨-, hmono'⟩ := MonomialCaseAlong.isNonzeroAlongAt_and_isMonomialAlong_of_principal hn
    hwf'.isClosedSubmanifold_N hwf'.isSNCDivisor hwf'.isTransverse h𝓜'
    fun x hx => (hP' x hx).choose_spec.isPrincipalMonomialAlongAt
  rw [← h𝔪eq] at f1 f2
  have heqM := NonmonomialTransformAlong.monomialPartAlong_eq_of_factor hn hwf'.isClosedSubmanifold_N
    hwf'.isSNCDivisor hwf'.isTransverse hcoh𝔟' h𝓜' hnd' f1 f2
  have hL := NonmonomialTransformAlong.le_nonmonomialPartAlong_of_factor hwf'.isClosedSubmanifold_N.1
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh𝔟')
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝓜') hmono' heqM f2
  -- a germ of `𝓝` not vanishing at `π z`
  have hπzN : π z ∈ 𝔫.N := 𝔫.cosupp_subset_N (hC.2.1 hzC)
  have hnot : ¬ OrderGE n 𝔫.N 𝔟 (π z) 1 := fun h1 => Set.disjoint_left.mp hC0 hzC ⟨hπzN, h1⟩
  unfold OrderGE at hnot
  push Not at hnot
  obtain ⟨c, hc, hcv⟩ := hnot
  have hchol : HolomorphicAt n c (π z) := hhol𝔟 _ _ hc
  have hcz : c (π z) ≠ 0 := fun h0 => hcv ((vanishesToOrderOn_one_iff hπzN hchol).mpr h0)
  -- its pullback lies in the transform of `(N, E, 𝓝, 0)`
  have hfat : ∀ᶠ y in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y :=
    Eventually.of_forall fun y => hπ.contMDiff.contMDiffAt
  have hcπ : HolomorphicAt n (c ∘ π) z := hchol.comp_contMDiff hfat
  have hpb : (GermIdeal.pullback (m := n) π 𝔟).mem z (c ∘ π) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcπ (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
  have hmem : ((⟨𝔫.N, 𝔫.E, 𝔟, 0⟩ : MarkedIdeal n Y).geoTransform C π).ideal.mem z (c ∘ π) := by
    rw [geoTransform_ideal]
    refine ⟨hcπ, fun g hg => ?_⟩
    have hg' : HolomorphicAt n g z := hg
    have hgc : (GermIdeal.pullback (m := n) π 𝔟).mem z (fun y => g y * (c ∘ π) y) :=
      CompanionReduction.mul_mem_of_isCoherent
        (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff h𝓝) hg' hpb
    exact ⟨hg'.mul hcπ, IsInSpanAt.restrict (isInSpanAt_self hgc (hg'.mul hcπ))⟩
  intro hzq
  exact hcz ((vanishesToOrderOn_one_iff hzN hcπ).mp (hzq.2 (c ∘ π) (hL z _ hmem)))

/-- **The order does not go up over an admissible centre on which it is constant**, for every value `q` (`𝔫` in the
domain, `n > 0`): `q = 0` is `notMem_ordGe_one_geoTransform_of_mem`, `q ≥ 1` is
`NonmonomialOrderLocal.nmOrd_geoTransform_le_of_mem`. -/
theorem nmOrd_geoTransform_le_of_level (hn : 0 < n) {Y Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Y}
    (h : IsInvDomain k 𝔫) {C : Set Y} (hC : 𝔫.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π)
    {q : ℕ} (hCq : ∀ c ∈ C, nmOrd 𝔫 c = q) {z : Z} (hz : z ∈ (𝔫.geoTransform C π).cosupp) (hzC : π z ∈ C) :
    nmOrd (𝔫.geoTransform C π) z ≤ q := by
  have hCN : ∀ c ∈ C, c ∈ 𝔫.N := fun c hc => 𝔫.cosupp_subset_N (hC.2.1 hc)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine nmOrd_le_of_notMem (q := 0) ?_
    refine notMem_ordGe_one_geoTransform_of_mem hn h hC hπ ?_ ((𝔫.geoTransform C π).cosupp_subset_N hz) hzC
    refine Set.disjoint_left.mpr fun c hc hc1 => ?_
    have h1 := (mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt (hCN c hc) 1).mp hc1
    rw [hCq c hc] at h1
    omega
  · refine nmOrd_geoTransform_le_of_mem hn h hC hπ hq (fun c hc => ?_) ?_ hz hzC
    · exact (mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt (hCN c hc) q).mpr (hCq c hc).ge
    · refine Set.disjoint_left.mpr fun c hc hc1 => ?_
      have h1 := (mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt (hCN c hc) (q + 1)).mp hc1
      rw [hCq c hc] at h1
      omega

end Zero

/-! ### Value functions whose order dominates the order of the nonmonomial part -/

section Monotone

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- **A value function whose order dominates the order of the nonmonomial part**: along every multiple test blow-up `T`
of `𝔪`, at the points of the cosupport, `f T y ≤ f T y'` implies `ν(y) ≤ ν(y')` (`ν = nmOrd` of the transform).  The
value of the general step, `(ν, ·)` lexicographically, is such a function (`ordMonotone_toLex`). -/
def OrdMonotone (𝔪 : MarkedIdeal n X) (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
    ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, ∀ y' ∈ (geoTransformAlong 𝔪 T).cosupp,
      f T y ≤ f T y' → nmOrd (geoTransformAlong 𝔪 T) y ≤ nmOrd (geoTransformAlong 𝔪 T) y'

/-- **The lexicographic value `(ν, g)` dominates `ν`**, whatever `g` is. -/
theorem ordMonotone_toLex (𝔪 : MarkedIdeal n X) {Λ' : Type v} [LinearOrder Λ']
    (g : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ') :
    OrdMonotone 𝔪 (fun {Y} T y => toLex (nmOrd (geoTransformAlong 𝔪 T) y, g (Y := Y) T y)) := by
  intro Y T _ y _ y' _ hle
  rcases Prod.Lex.toLex_le_toLex.mp hle with hlt | ⟨heq, -⟩
  · exact hlt.le
  · exact heq.le

variable {𝔪 : MarkedIdeal n X} {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The order at a point of the maximum locus is the largest order on the cosupport.** -/
theorem nmOrd_le_of_mem_maxLocus (hf : OrdMonotone 𝔪 f) {Y : CMfd.{u} n} {T : BlowupTower X Y}
    (hT : IsGeoTestTower 𝔪 T) {c : Y} (hc : c ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp) {y : Y}
    (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) :
    nmOrd (geoTransformAlong 𝔪 T) y ≤ nmOrd (geoTransformAlong 𝔪 T) c :=
  hf T hT y hy c hc.1 (hc.2 y hy)

/-- **The maximum locus lies in one level set of the order.** -/
theorem nmOrd_eq_of_mem_maxLocus (hf : OrdMonotone 𝔪 f) {Y : CMfd.{u} n} {T : BlowupTower X Y}
    (hT : IsGeoTestTower 𝔪 T) {c c' : Y} (hc : c ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp)
    (hc' : c' ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp) :
    nmOrd (geoTransformAlong 𝔪 T) c' = nmOrd (geoTransformAlong 𝔪 T) c :=
  le_antisymm (nmOrd_le_of_mem_maxLocus hf hT hc hc'.1) (nmOrd_le_of_mem_maxLocus hf hT hc' hc.1)

/-- **A canonical centre lies where the order is at least that of any point of the cosupport**: if `C` is empty or the
maximum locus of `f` and `w` is a point of the cosupport of order `≥ q`, then `C ⊆ {ν ≥ q}` (`𝔪` in the domain). -/
theorem subset_ordGe_of_canonical {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {Y : CMfd.{u} n}
    {S : BlowupTower X Y} (hS : IsGeoTestTower 𝔪 S) {C : Set Y}
    (hC : C = ∅ ∨ C = maxLocus (f S) (geoTransformAlong 𝔪 S).cosupp) {w : Y}
    (hw : w ∈ (geoTransformAlong 𝔪 S).cosupp) {q : ℕ} (hq : q ≤ nmOrd (geoTransformAlong 𝔪 S) w) :
    C ⊆ ordGe (geoTransformAlong 𝔪 S) q := by
  have hdomS := InvDomainTowerAlong.isInvDomain_geoTransformAlong h S hS
  rcases hC with rfl | rfl
  · exact Set.empty_subset _
  · intro c hc
    exact (mem_ordGe_iff hdomS.isWellFormed hdomS.isNonzeroAlongAt ((geoTransformAlong 𝔪 S).cosupp_subset_N hc.1)
      q).mpr (hq.trans (nmOrd_le_of_mem_maxLocus hf hS hc hw))

/-- **The order does not go up along a canonical step** (`𝔪` in the domain, `n > 0`): if the centre `C` of the last
step of a multiple test blow-up is empty or the maximum locus of `f`, every point `z` of the new cosupport lies over the
old cosupport and `ν(z) ≤ ν(π z)` -- off `C` the order is that of the image, over `C` the centre lies in one level set of
`ν` (`nmOrd_eq_of_mem_maxLocus`) and `nmOrd_geoTransform_le_of_level` applies. -/
theorem nmOrd_step_le_of_canonical (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) (hC : C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp)
    {z : Z} (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp) :
    π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧
      nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z ≤ nmOrd (geoTransformAlong 𝔪 T) (π z) := by
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
  have hz' : z ∈ ((geoTransformAlong 𝔪 T).geoTransform C π).cosupp := hz
  by_cases hzC : π z ∈ C
  · refine ⟨hCadm.2.1 hzC, ?_⟩
    rcases hC with hC | hC
    · rw [hC] at hzC
      exact absurd hzC (Set.notMem_empty _)
    · have hzC' := hzC
      rw [hC] at hzC'
      show nmOrd ((geoTransformAlong 𝔪 T).geoTransform C π) z ≤ _
      refine nmOrd_geoTransform_le_of_level hn hdomT hCadm hπ (fun c hc => ?_) hz' hzC
      rw [hC] at hc
      exact nmOrd_eq_of_mem_maxLocus hf hTT hzC' hc
  · have hcos : π z ∈ (geoTransformAlong 𝔪 T).cosupp :=
      (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T)
          hdomT.isWellFormed.isClosedSubmanifold_N.1
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
            hdomT.isWellFormed.isCoherent hg) hπ hzC).mp hz'
    refine ⟨hcos, ?_⟩
    show nmOrd ((geoTransformAlong 𝔪 T).geoTransform C π) z ≤ _
    rw [nmOrd_geoTransform_of_notMem hn hdomT hCadm hπ hzC]

/-- **The order never goes up along a canonical segment** (`𝔪` in the domain, `n > 0`): along a multiple test blow-up
`T₀ M` of `𝔪` which is a canonical segment of `f`, every point `z` of the cosupport at the last stage lies over the
cosupport at the last stage of `T₀`, and `ν(z) ≤ ν(M z)`. -/
theorem nmOrd_le_nmOrd_proj (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (M : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T₀.append M) → IsCanonical 𝔪 f (T₀.append M) →
      ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append M)).cosupp,
        M.proj z ∈ (geoTransformAlong 𝔪 T₀).cosupp ∧
          nmOrd (geoTransformAlong 𝔪 (T₀.append M)) z ≤ nmOrd (geoTransformAlong 𝔪 T₀) (M.proj z)
  | _, .refl, _, _, _, hz => ⟨hz, le_rfl⟩
  | _, .step M C π hπ, hT, hcan, z, hz => by
      have hT' : IsGeoTestTower 𝔪 (.step (T₀.append M) C π hπ) := hT
      have hcan' : IsCanonical 𝔪 f (T₀.append M) ∧
          (C = ∅ ∨ C = maxLocus (f (T₀.append M)) (geoTransformAlong 𝔪 (T₀.append M)).cosupp) := hcan
      obtain ⟨h1, h2⟩ := nmOrd_step_le_of_canonical hn h hf (T₀.append M) C π hπ hT' hcan'.2 (z := z) hz
      obtain ⟨h3, h4⟩ := nmOrd_le_nmOrd_proj hn h hf T₀ M hT'.1 hcan'.1 (π z) h1
      exact ⟨h3, h2.trans h4⟩

end Monotone

/-! ### Upper semicontinuity through the closed sets `{ν ≥ q}` -/

section USC

open ResolutionInvariantOrder (IsInvUSCOn)

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Upper semicontinuity reduces to points of the same order** (`𝔪` in the domain, `n > 0`): along a multiple test
blow-up `T`, if near every point `y` of the cosupport the cosupport points of the same order have values `≤ f T y`, then
`f T` is upper semicontinuous on the cosupport -- nearby points have order `≤ ν(y)` (the sets `{ν ≥ q}` are closed,
`NonmonomialOrderLocal.eventually_nmOrd_le`), and a smaller order gives a smaller value (`OrdMonotone`). -/
theorem isInvUSCOn_of_ordMonotone (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (hlev : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, ∀ᶠ y' in 𝓝 y, y' ∈ (geoTransformAlong 𝔪 T).cosupp →
      nmOrd (geoTransformAlong 𝔪 T) y' = nmOrd (geoTransformAlong 𝔪 T) y → f T y' ≤ f T y) :
    IsInvUSCOn (f T) (geoTransformAlong 𝔪 T).cosupp := by
  intro y hy
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  filter_upwards [eventually_nmOrd_le hn hdomT.isWellFormed hdomT.isNonzeroAlongAt
    ((geoTransformAlong 𝔪 T).cosupp_subset_N hy), hlev y hy] with y' h1 h2 hy'
  rcases h1.lt_or_eq with hlt | heq
  · by_contra hcon
    have h3 := hf T hT y hy y' hy' (not_le.mp hcon).le
    omega
  · exact h2 hy' heq

end USC

/-! ### Re-basing at the start of the run -/

section Start

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **One stage before the start of its run a point had a larger order** (`𝔪` in the domain, `n > 0`): along a multiple
test blow-up `T` of `𝔪` which is a canonical segment of `f`, let `y` be a point of the cosupport with `ν(y) = o` whose run
`r` in the regime `OrdRegime 𝔪 o` is shorter than `T`.  Then, splitting `T` after its first `|T| - (r + 1)` blowups, the
image of `y` lies in the cosupport and has order `≥ o + 1` (it is out of the regime, and the order never goes up,
`nmOrd_le_nmOrd_proj`). -/
theorem mem_cosupp_and_succ_le_before_start (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 f T) {y : Y}
    (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ} (hyo : nmOrd (geoTransformAlong 𝔪 T) y = o) {j : ℕ}
    (hj : regimeRun (OrdRegime 𝔪 o) T y + 1 = j) (hr : regimeRun (OrdRegime 𝔪 o) T y < T.length) :
    (BlowupTowerSplit.tail T j).proj y ∈ (geoTransformAlong 𝔪 (BlowupTowerSplit.head T j)).cosupp ∧
      o + 1 ≤ nmOrd (geoTransformAlong 𝔪 (BlowupTowerSplit.head T j)) ((BlowupTowerSplit.tail T j).proj y) := by
  have hnot := not_regime_head_regimeRun (OrdRegime 𝔪 o) T y hr
  rw [hj] at hnot
  have hT' : IsGeoTestTower 𝔪 ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j)) := by
    rw [BlowupTowerSplit.head_append_tail]
    exact hT
  have hcan' : IsCanonical 𝔪 f ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j)) := by
    rw [BlowupTowerSplit.head_append_tail]
    exact hcan
  have hy' : y ∈ (geoTransformAlong 𝔪 ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j))).cosupp := by
    rw [BlowupTowerSplit.head_append_tail]
    exact hy
  obtain ⟨h1, h2⟩ := nmOrd_le_nmOrd_proj hn h hf (BlowupTowerSplit.head T j) (BlowupTowerSplit.tail T j) hT' hcan' y hy'
  rw [BlowupTowerSplit.head_append_tail, hyo] at h2
  refine ⟨h1, ?_⟩
  rcases h2.lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ⟨h1, heq.symm⟩ hnot

/-- **Between two start stages the centres lie in `{ν ≥ o + 1}`** (`𝔪` in the domain, `n > 0`): along a multiple test
blow-up `T₀ M σ` of `𝔪` (`σ` the blowup along `C`) which is a canonical segment of `f`, if some point `w` of the cosupport
at the last stage of `T₀ M` has order `≥ o + 1`, every centre of `M σ` lies in `{ν ≥ o + 1}` of the transform at its stage
(`NonmonomialOrderRegime.CentresOrdGt` for `𝔪_{T₀}`): the centre `C` is empty or the maximum locus, where `f ≥ f(w)`, and
the images of `w` keep order `≥ o + 1` (`nmOrd_step_le_of_canonical`).  This is the hypothesis of
`NonmonomialOrderRegime.centresAvoid_of_centresOrdGt` and `companionOf_rebase_of_centresOrdGt`; in the application `w` is
the image, one stage before its start (`mem_cosupp_and_succ_le_before_start`), of a point whose run started later than that
of a nearby point (the general step's analogue of `StepOneValueMasked.centresAvoid_lowerMaskL`). -/
theorem centresOrdGt_of_canonical (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {o : ℕ}
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y Z : CMfd.{u} n} (M : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (T₀.append (.step M C π hπ)) → IsCanonical 𝔪 f (T₀.append (.step M C π hπ)) →
      ∀ w ∈ (geoTransformAlong 𝔪 (T₀.append M)).cosupp, o + 1 ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append M)) w →
        CentresOrdGt (geoTransformAlong 𝔪 T₀) o (.step M C π hπ)
  | _, _, .refl, C, π, hπ, hT, hcan, w, hw, hwo => by
      have hT' : IsGeoTestTower 𝔪 (.step (T₀.append .refl) C π hπ) := hT
      have hcan' : IsCanonical 𝔪 f (T₀.append .refl) ∧
          (C = ∅ ∨ C = maxLocus (f (T₀.append .refl)) (geoTransformAlong 𝔪 (T₀.append .refl)).cosupp) := hcan
      refine (centresOrdGt_step_iff _ o _ C π hπ).mpr ⟨trivial, ?_⟩
      exact subset_ordGe_of_canonical h hf hT'.1 hcan'.2 hw hwo
  | _, _, .step M C' π' hπ', C, π, hπ, hT, hcan, w, hw, hwo => by
      have hT' : IsGeoTestTower 𝔪 (.step (T₀.append (.step M C' π' hπ')) C π hπ) := hT
      have hcan' : IsCanonical 𝔪 f (T₀.append (.step M C' π' hπ')) ∧
          (C = ∅ ∨ C = maxLocus (f (T₀.append (.step M C' π' hπ')))
            (geoTransformAlong 𝔪 (T₀.append (.step M C' π' hπ'))).cosupp) := hcan
      have hTM : IsGeoTestTower 𝔪 (.step (T₀.append M) C' π' hπ') := hT'.1
      have hcanM : IsCanonical 𝔪 f (T₀.append M) ∧
          (C' = ∅ ∨ C' = maxLocus (f (T₀.append M)) (geoTransformAlong 𝔪 (T₀.append M)).cosupp) := hcan'.1
      obtain ⟨hw', hwle⟩ := nmOrd_step_le_of_canonical hn h hf (T₀.append M) C' π' hπ' hTM hcanM.2 (z := w) hw
      have ih := centresOrdGt_of_canonical hn h hf T₀ M C' π' hπ' hT'.1 hcan'.1 (π' w) hw' (hwo.trans hwle)
      refine (centresOrdGt_step_iff _ o _ C π hπ).mpr ⟨ih, ?_⟩
      have hsub := subset_ordGe_of_canonical h hf hT'.1 hcan'.2 hw hwo
      rw [geoTransformAlong_append] at hsub
      exact hsub

/-- **The centres between two start stages miss the earlier mask** (`𝔪` in the domain, `n > 0`; the general step's
analogue of `StepOneValueMasked.centresAvoid_lowerMaskL`): under the hypotheses of `centresOrdGt_of_canonical`, for an open
set `W` of the last stage of `T₀` on which `ν ≤ o` at the points of the cosupport, the centres of `M σ` miss the preimages of
`W` and `ν ≤ o` persists at the cosupport points over `W` (`NonmonomialOrderRegime.centresAvoid_of_centresOrdGt`). -/
theorem centresAvoid_of_canonical (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {o : ℕ}
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (W : Opens Y₀)
    (hbound : ∀ x ∈ (geoTransformAlong 𝔪 T₀).cosupp, x ∈ W → x ∉ ordGe (geoTransformAlong 𝔪 T₀) (o + 1))
    {Y Z : CMfd.{u} n} (M : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (T₀.append (.step M C π hπ))) (hcan : IsCanonical 𝔪 f (T₀.append (.step M C π hπ)))
    {w : Y} (hw : w ∈ (geoTransformAlong 𝔪 (T₀.append M)).cosupp)
    (hwo : o + 1 ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append M)) w) :
    CentresAvoid W (.step M C π hπ) ∧
      ∀ z ∈ (geoTransformAlong (geoTransformAlong 𝔪 T₀) (.step M C π hπ)).cosupp, (BlowupTower.step M C π hπ).proj z ∈ W →
        z ∉ ordGe (geoTransformAlong (geoTransformAlong 𝔪 T₀) (.step M C π hπ)) (o + 1) := by
  obtain ⟨hT₀, hTM⟩ := (isGeoTestTower_append_iff 𝔪 T₀ (.step M C π hπ)).mp hT
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  exact centresAvoid_of_centresOrdGt hn hdom₀ W hbound (.step M C π hπ) hTM
    (centresOrdGt_of_canonical hn h hf T₀ M C π hπ hT hcan w hw hwo)

end Start

end

end Hironaka.NonmonomialOrderCanonical
