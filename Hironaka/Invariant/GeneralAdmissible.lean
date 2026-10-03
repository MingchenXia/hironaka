/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralUSC
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralValue
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical
import Hironaka.Invariant.NonmonomialOrderPhase
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Property (1) of the general value; canonical segments are multiple test blow-ups

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2a: the maximum locus of `(ν,
inv_𝓞)` is, near each of its points, the maximum locus of the maximal-order invariant of the companion ideal, an
admissible centre of the companion's transform and hence of the transform of the marked ideal (it lies in `{ν ≥
o}`).

Let `𝔪` lie in the domain (`0 < n`), `M` a value function for the marked ideals of maximal order and `T` a canonical segment of the
general value `genInv M 𝔪` which is a multiple test blow-up.  On an open `W` of the last stage on which the value is `≤ l` on the
cosupport, the points of the cosupport over `W` with value `l` form an admissible centre of `𝔪_T|_W` (`genInv_admissible`):

* at a value `(o, λ)` with `o ≥ 1` and `λ ∈ Λ`, near a point of the level set the level set is that of `M` for the
  companion ideal formed at the start of the point (on the open set over its mask), admissible for the companion's
  transform by property (1) of `M`, hence for the transform of `𝔪`
  (`NonmonomialOrderPhase.isAdmissibleCentre_pullback_val_companion_iff`); away from the level set a neighbourhood
  misses it (upper semicontinuity, `GeneralUSC.genInv_usc`); admissible centres are local
  (`MaxLocusLocal.isAdmissibleCentre_pullback_val_of_forall_exists_opens`);
* at a value `(0, γ)` this is `NonmonomialOrderMonomialCanonical.isAdmissibleCentre_level_of_nmOrd_eq_zero`;
* at the other values the level set is empty (the companion value is finite on the domain).

Hence the maximum locus is an admissible centre and **canonical segments of the general value are multiple test
blow-ups** (`isGeoTestTower_of_isCanonical_genInv`), and the canonical-tail theorem, upper semicontinuity and the
drop property hold along every canonical segment.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralAdmissible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCanonicalTail Hironaka.GeneralUSC Hironaka.MaxLocusLocal Hironaka.StepOneWellFounded
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-! ### Local pieces -/

section Local

/-- **Away from a level set of the maximum on `W`, a neighbourhood misses it** (upper semicontinuity and the closed
cosupport). -/
theorem exists_opens_preimage_eq_empty (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T)
    (W : Opens Y) (l : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))
    (hle : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → genInv M 𝔪 T y ≤ l) {x : Y} (hxW : x ∈ W)
    (hx : ¬ (x ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T x = l)) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y = l} = ∅ := by
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT
  obtain ⟨t, hto, hxt, hdisj⟩ : ∃ t : Set Y, IsOpen t ∧ x ∈ t ∧ ∀ y ∈ t,
      ¬ (y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y = l) := by
    by_cases hxc : x ∈ (geoTransformAlong 𝔪 T).cosupp
    · have hxl : genInv M 𝔪 T x < l := lt_of_le_of_ne (hle x hxc hxW) fun h => hx ⟨hxc, h⟩
      obtain ⟨t, hts, hto, hxt⟩ := mem_nhds_iff.mp (genInv_usc hM hn h T hT hcan x hxc)
      exact ⟨t, hto, hxt, fun y hy hyl => absurd hyl.2 (((hts hy) hyl.1).trans_lt hxl).ne⟩
    · have hcl : IsClosed (geoTransformAlong 𝔪 T).cosupp :=
        GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
      exact ⟨_, hcl.isOpen_compl, hxc, fun y hy hyl => hy hyl.1⟩
  refine ⟨W ⊓ ⟨t, hto⟩, ⟨hxW, hxt⟩, inf_le_left, ?_⟩
  exact eq_empty_iff_forall_notMem.mpr fun v hv => hdisj v v.2.2 hv

/-- **Near a point of the level set of a value `(o, λ)`, `o ≥ 1`**, the level set is an admissible centre: on the open set over
the mask of the start of the point it is the level set of `M` for the companion ideal formed there, admissible for the
companion's transform by property (1) of `M`, hence for the transform of `𝔪`. -/
theorem exists_opens_isAdmissibleCentre_of_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T)
    (W : Opens Y) {o : ℕ} (ho : 1 ≤ o) (l : Λ)
    (hle : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → genInv M 𝔪 T y ≤
      toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ)))
    {x : Y} (hxW : x ∈ W) (hx : x ∈ (geoTransformAlong 𝔪 T).cosupp) (hxo : nmOrd (geoTransformAlong 𝔪 T) x = o) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y =
          toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))}) := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  have hD := hasGenLowerData_of_isCanonical M hM hn h T hT hcan
  set r := regimeRun (OrdRegime 𝔪 o) T x with hr
  obtain ⟨hxM, hdom₀, hmax₀, hcan₀, -⟩ := hD x hx o hxo ho
  have hTW := isGeoTestTower_companion_tail_of_canonical hn h hf ho T hT hcan x
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_iff_head_tail 𝔪 T r).mp hT
  have hdomh := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T r) hT₀
  set P : Opens Y := openPreimage (tail T r) (ordMask (geoTransformAlong 𝔪 (head T r)) o) with hP
  have hVP : W ⊓ P ≤ P := inf_le_right
  refine ⟨W ⊓ P, ⟨hxW, hxM⟩, inf_le_left, ?_⟩
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT
  have hcT := hwfT.isCoherent
  have hVc : (MarkedIdeal.pullback (Subtype.val : (W ⊓ P : Opens Y) → Y) (geoTransformAlong 𝔪 T)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcT
  -- the companion's cosupport over `P`
  have hcos : ∀ q : P, q ∈ (geoTransformAlong (compAt 𝔪 o (head T r))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r))).cosupp ↔
        (q : Y) ∈ (geoTransformAlong 𝔪 T).cosupp ∧ nmOrd (geoTransformAlong 𝔪 T) q = o := by
    intro q
    rw [mem_cosupp_compAt_iff hn h ho _ _ hT₀ hT₁ hTW q, ← geoTransformAlong_head_tail 𝔪 T]
  -- `M ≤ λ` on the companion's cosupport over `W ∩ P`
  have hle'' : ∀ q ∈ (geoTransformAlong (compAt 𝔪 o (head T r))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r))).cosupp,
        q ∈ nestedOpens P (W ⊓ P) →
        M (compAt 𝔪 o (head T r)) (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r)) q ≤ l := by
    intro q hq hqV
    have hv := genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcan hD hx hxo ho rfl hcan₀ q hq
    have hq' := hle q ((hcos q).mp hq).1 hqV.1
    rw [hv, Prod.Lex.toLex_le_toLex] at hq'
    rcases hq' with h' | ⟨-, h'⟩
    · exact absurd h' (lt_irrefl _)
    · exact WithTop.coe_le_coe.mp (Sum.Lex.inr_le_inr_iff.mp h')
  -- property (1) of `M` on `W ∩ P`, then from the companion to `𝔪_{head}` restricted to the mask
  have hadm := hM.admissible _ hdom₀ hmax₀ _ hcan₀ (nestedOpens P (W ⊓ P)) l hle''
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (ordMask (geoTransformAlong 𝔪 (head T r)) o) hdomh
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 (head T r)) o → _)
      (geoTransformAlong 𝔪 (head T r))).cosupp, x ∉ ordGe (M := CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪
        (head T r)) o)) (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 (head T r)) o → _)
          (geoTransformAlong 𝔪 (head T r))) (o + 1) := by
    intro x _ hx
    rw [mem_ordGe_pullback_val_iff hn hdomh.isWellFormed hdomh.isNonzeroAlongAt] at hx
    exact (mem_ordMask_iff hn hdomh.isWellFormed hdomh.isNonzeroAlongAt o x).mp x.2 hx
  have htr := ((NonmonomialOrderPhase.isAdmissibleCentre_pullback_val_companion_iff hn hdomW ho hbound _ hTW
    (nestedOpens P (W ⊓ P)) _).mp hadm).1
  have hrest := geoTransformAlong_restrict (U := ordMask (geoTransformAlong 𝔪 (head T r)) o)
    hdomh.isWellFormed.isClosedSubmanifold_N hdomh.isWellFormed.isCoherent (tail T r) hT₁
  rw [hrest, ← geoTransformAlong_head_tail 𝔪 T r, pullback_val_pullback_val hcT hVP] at htr
  -- the two level sets agree
  have hset : (Subtype.val : nestedOpens P (W ⊓ P) → P) ⁻¹'
      {q | q ∈ (geoTransformAlong (compAt 𝔪 o (head T r))
          (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r))).cosupp ∧
        M (compAt 𝔪 o (head T r)) (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r)) q = l} =
      (nestedOpensDiffeo (n := n) hVP) ⁻¹' ((Subtype.val : (W ⊓ P : Opens Y) → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y =
          toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))}) := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hql⟩
      refine ⟨((hcos _).mp hq).1, ?_⟩
      show genInv M 𝔪 T ((w : P) : Y) = _
      rw [genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcan hD hx hxo ho rfl hcan₀ _ hq, hql]
    · rintro ⟨hc, hv⟩
      replace hc : ((w : P) : Y) ∈ (geoTransformAlong 𝔪 T).cosupp := hc
      replace hv : genInv M 𝔪 T ((w : P) : Y) =
          toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ)) := hv
      have hord : nmOrd (geoTransformAlong 𝔪 T) ((w : P) : Y) = o := by
        have h' := congrArg (fun p => (ofLex p).1) hv
        simp only [ofLex_toLex] at h'
        rw [← h']
        rfl
      have hq := (hcos (w : P)).mpr ⟨hc, hord⟩
      refine ⟨hq, ?_⟩
      rw [genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcan hD hx hxo ho rfl hcan₀ _ hq] at hv
      have h' := congrArg (fun p => (ofLex p).2) hv
      simp only [ofLex_toLex] at h'
      have h'' := congrArg ofLex h'
      simp only [ofLex_toLex, Sum.inr.injEq] at h''
      exact WithTop.coe_injective h''
  rw [hset] at htr
  exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff (Φ := nestedOpensDiffeo (n := n) hVP) hVc).mp htr

end Local

/-! ### Property (1) at every value -/

section Admissible

/-- **Property (1) at the values `(o, λ)`, `o ≥ 1`, `λ ∈ Λ`** (glued from the local pieces). -/
theorem genInv_admissible_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T)
    (W : Opens Y) {o : ℕ} (ho : 1 ≤ o) (l : Λ)
    (hle : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → genInv M 𝔪 T y ≤
      toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y =
        toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))}) := by
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT
  refine isAdmissibleCentre_pullback_val_of_forall_exists_opens hwfT.isCoherent W fun x hxW => ?_
  by_cases hx : x ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T x =
      toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))
  · obtain ⟨hxc, hxv⟩ := hx
    have hxo : nmOrd (geoTransformAlong 𝔪 T) x = o := by
      have h' := congrArg (fun p => (ofLex p).1) hxv
      simp only [ofLex_toLex] at h'
      rw [← h']
      rfl
    exact exists_opens_isAdmissibleCentre_of_pos hM hn h T hT hcan W ho l hle hxW hxc hxo
  · obtain ⟨V, hxV, hVW, hV⟩ := exists_opens_preimage_eq_empty hM hn h T hT hcan W _ hle hxW hx
    refine ⟨V, hxV, hVW, ?_⟩
    rw [hV]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Property (1) of the general value at every value**: along a canonical segment `T` of the general value which is a
multiple test blow-up, on an open `W` on which the value is `≤ l` on the cosupport, the points of `W` in the cosupport with
value `l` form an admissible centre of `𝔪_T|_W`. -/
theorem genInv_admissible (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T)
    (W : Opens Y) (l : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))
    (hle : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → genInv M 𝔪 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y = l}) := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  -- if the level set is empty there is nothing to prove
  by_cases hne : ∃ y₀, y₀ ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y₀ = l
  swap
  · have hempty : {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ genInv M 𝔪 T y = l} = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun y hy => hne ⟨y, hy⟩
    rw [hempty, preimage_empty]
    exact MarkedIdeal.isAdmissibleCentre_empty _
  obtain ⟨y₀, hy₀, hy₀l⟩ := hne
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) y₀) with h0 | hpos
  · -- order `0`
    have hv : NonmonomialOrderMonomialCanonical.OrdZeroValue 𝔪 (genInv M 𝔪)
        (fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) :=
      ordZeroValue_genInv M 𝔪
    exact NonmonomialOrderMonomialCanonical.isAdmissibleCentre_level_of_nmOrd_eq_zero (f := genInv M 𝔪)
      (ψ := fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) hn h hf
      NonmonomialOrderMonomialCanonical.strictMono_toLex_zero_inl hv hT W hle hy₀ hy₀l h0
  · -- positive order: the level is `(o, λ)` with `λ ∈ Λ`
    set o := nmOrd (geoTransformAlong 𝔪 T) y₀ with ho
    have hD := hasGenLowerData_of_isCanonical M hM hn h T hT hcan
    have hy₀v := genInv_of_nmOrd_ne_zero M 𝔪 T (rfl : nmOrd (geoTransformAlong 𝔪 T) y₀ = o) (by omega)
    obtain ⟨hm, -⟩ := hD y₀ hy₀ o rfl hpos
    rw [genLowerValue_eq_of_mem M 𝔪 hm] at hy₀v
    rw [← hy₀l, hy₀v] at hle ⊢
    exact genInv_admissible_pos hM hn h T hT hcan W hpos _ hle

/-- **The maximum locus of the general value is an admissible centre** along a canonical segment which is a multiple test
blow-up. -/
theorem isAdmissibleCentre_maxLocus_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := genInv_admissible hM hn h T hT hcan ⊤ (genInv M 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← ResolutionInvariantDriver.maxLocus_eq_level hy₀] at hadm
    have hcT := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact ResolutionInvariantDriver.isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments of the general value are multiple test blow-ups.** -/
theorem isGeoTestTower_of_isCanonical_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (genInv M 𝔪) T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
      have hC : C = ∅ ∨ C = maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
      have hTt := isGeoTestTower_of_isCanonical_genInv hM hn h T hcanT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus_genInv hM hn h T hTt hcanT

end Admissible

end

end Hironaka.GeneralAdmissible
