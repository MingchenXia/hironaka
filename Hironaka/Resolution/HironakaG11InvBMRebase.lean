import Hironaka.Resolution.HironakaG11InvBMLowerTailSucc
import Hironaka.Invariant.ContactEmptyPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Re-basing Bierstone--Milman's lower marked ideals across steps that miss the mask (repair (B'), plan module 7, part (d1))

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6b, item (d1).
Source: Bierstone--Milman 2008, §5 Step I.B (the lower ideals of a year are TRANSFORMS of the ideal formed at its start
`q_k`), §7.2 ("the values of the invariants at `x` equal their values in year `q_k`"); Włodarczyk 2005, the lemma on the
commutativity of the procedure with étale morphisms (blowups whose centres miss an open set restrict to isomorphisms).

Bierstone--Milman's lower ideals are transforms (`HironakaG11InvBMLower`), so re-basing them along a tower `M` whose centres
miss the mask `W'` needs no re-forming (unlike W's family, `InvDomainRebase`/`ContactStageRebase`):

* **`restrictEquiv_tail_contactCoeffBM`**: for every multiple test blow-up `T₁` of `𝓒_N(𝔍_∅)_{T₀}` and every open
  `W ⊆ T₀⁻¹U`, the transform of `contactCoeffBM 𝔍 u T₀|_W` along `T₁|_W` is restricted-equivalent to
  `contactCoeffBM 𝔍 u (T₀ T₁)|_{T₁⁻¹W}` (the `RestrictEquiv` behind `HironakaG11InvBMLowerTail`);
* `pullback_lowerIdealBM_succ_eq_sumMarked`: on every open set, the lower ideal of level `s + 1` is the same-mark sum of the
  coefficient ideal on maximal contact and the `ℰ`-marked ideal of the traces of the members;
* `RestrictEquiv.sumMarked`: restricted equivalence is a congruence for same-mark sums;
* **`restrictEquiv_rebase_lowerBM`**: for `T₀' M` a multiple test blow-up of `J̄` whose last part `M` misses the mask `W'` of
  `a = M(q)` at the stage `T₀'`, the transform of `lowerBM 𝔍 s T₀' a` along the (empty) tower `M|_{W'}` is
  restricted-equivalent to the lower ideal formed at the stage `T₀' M` at `q`, restricted to `M⁻¹W'`;
* **`inv_rebase_lowerBM`**: hence (`InvDomainRebase.inv_rebase`) the domain, canonical segments and values of a resolution
  invariant correspond.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMRebase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.HomogenizedIdealAlongTower
  Hironaka.TangentDirectionAlong Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower Hironaka.ContactEquivalenceAlong
  Hironaka.ContactStageInvDomain Hironaka.MemberInterTowerAlong
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG11InvSameMarkSum Hironaka.HironakaG11InvBMExceptionalTerm
  Hironaka.RestrictEmptyTower
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open Hironaka.MemberInterLocusAlong (strictAlong_append)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv IsSubmanifoldPair
  hol_of_isCoherent)
open Hironaka.MarkedIdealOperationsAlong (restrictLe_sumIdeal)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### Restricted equivalence of same-mark sums -/

section Sum

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Restricted equivalence is a congruence for same-mark sums** (the summands of the second sum with coherent ideals, on one
carrier). -/
theorem RestrictEquiv.sumMarked {𝔪₁ 𝔪₂ 𝔫₁ 𝔫₂ : MarkedIdeal n M} (h₁ : RestrictEquiv 𝔪₁ 𝔫₁) (h₂ : RestrictEquiv 𝔪₂ 𝔫₂)
    (hN : 𝔪₁.N = 𝔪₂.N) (h𝔪₁ : 𝔪₁.ideal.IsCoherent) (h𝔪₂ : 𝔪₂.ideal.IsCoherent) (h𝔫₁ : 𝔫₁.ideal.IsCoherent)
    (h𝔫₂ : 𝔫₂.ideal.IsCoherent) :
    RestrictEquiv (HironakaG11InvSameMarkSum.sumMarked 𝔪₁ 𝔪₂) (HironakaG11InvSameMarkSum.sumMarked 𝔫₁ 𝔫₂) := by
  refine ⟨h₁.N_eq, h₁.E_eq, h₁.d_eq, ?_, ?_⟩
  · exact restrictLe_sumIdeal (hol_of_isCoherent h𝔫₁) (hol_of_isCoherent h𝔫₂) h₁.le (hN ▸ h₂.le)
  · exact restrictLe_sumIdeal (hol_of_isCoherent h𝔪₁) (hol_of_isCoherent h𝔪₂) h₁.ge (hN ▸ h₂.ge)

end Sum

/-! ### The tails of the coefficient ideal on maximal contact, as restricted equivalences -/

section Tail

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
  (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
  (hT₀ : IsGeoTestTower (coeffEmptyBM 𝔍) T₀) (W : Opens Y₀) (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U)

include h𝔍 hd hu hT₀ hWU in
/-- **The transform of `contactCoeffBM 𝔍 u T₀|_W` along `T₁|_W` is `contactCoeffBM 𝔍 u (T₀ T₁)|_{T₁⁻¹W}`** up to restricted
equivalence, for every multiple test blow-up `T₁` of `𝓒_N(𝔍_∅)_{T₀}` (Giraud along `T₀ T`, le:cf on `W`). -/
theorem restrictEquiv_tail_contactCoeffBM {Z : CMfd.{u} n} (T₁ : BlowupTower Y₀ Z)
    (hT₁ : IsGeoTestTower (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T₁) :
    RestrictEquiv (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) (contactCoeffBM 𝔍 u T₀))
        (restrict W T₁))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z) (contactCoeffBM 𝔍 u (T₀.append T₁))) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → Y₀) := contMDiff_subtype_val
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀
  have hT₀e : IsGeoTestTower (emptyBoundary 𝔍) T₀ := (coeffAlong_tower (emptyBoundary 𝔍) hN h𝔞 hd T₀).1.mp hT₀
  have hA : IsClosedSubmanifold n ((Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) :=
    isClosedSubmanifold_strictAlong_stage_of_le (emptyBoundary 𝔍) hN h𝔞 hd U hu T₀ hT₀e W hWU
  have hAN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N := by
    rw [HomogenizedGlueingTower.N_geoTransformAlong]
    exact strictAlong_mono T₀ (fun x hx => hx.1)
  have hNW : IsClosedSubmanifold n
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT W
  have hcW : (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval hcT
  have hR := isGeoTestTower_restrict (𝔪 := geoTransformAlong (coeffEmptyBM 𝔍) T₀) W hNT hcT T₁ hT₁
  have hC : CentresIn ((Subtype.val : W → Y₀) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) (restrict W T₁) :=
    centresIn_restrict_of_forall (geoTransformAlong (coeffEmptyBM 𝔍) T₀) W
      (fun T C hT hCa => HironakaG11InvBMLowerTail.cosupp_tail_subset_strictAlong_BM h𝔍 hd U hu T₀ hT₀ W hWU T C hT hCa)
      T₁ hT₁
  obtain ⟨-, -, -, -, -, -, hRE⟩ := restrict_tower_along (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffEmptyBM 𝔍) T₀)) hNW hcW hA
    (preimage_mono hAN) (restrict W T₁) hR hC
  rw [geoTransformAlong_restrict W hNT hcT T₁ hT₁, strictAlong_restrict W T₁] at hRE
  have e : MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z) (contactCoeffBM 𝔍 u (T₀.append T₁)) =
      withN (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ W → Z)
          (geoTransformAlong (geoTransformAlong (coeffEmptyBM 𝔍) T₀) T₁))
        ((Subtype.val : openPreimage T₁ W → Z) ⁻¹' strictAlong T₁ (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))) := by
    rw [contactCoeffBM, geoTransformAlong_append, strictAlong_append]
    rfl
  rw [e]
  exact hRE

end Tail

/-! ### The lower ideal of level `s + 1` on an open set -/

section OnOpen

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **On every open set, the lower ideal of level `s + 1` is the same-mark sum** of the coefficient ideal on maximal
contact and the `ℰ`-marked ideal of the traces of the original members through the anchor (members closed submanifolds,
at least one, coherent coefficient ideal). -/
theorem pullback_lowerIdealBM_succ_eq_sumMarked {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) (s : ℕ)
    (O : Opens Y₀) (hSm : ∀ H ∈ throughMembers 𝔍 T₀ y₀, IsClosedSubmanifold n H) (hSne : throughMembers 𝔍 T₀ y₀ ≠ [])
    (hC : (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal.IsCoherent) :
    MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM 𝔍 (s + 1) T₀ y₀) =
      sumMarked (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀))
        (excMarked n (MarkedIdeal.pullback (Subtype.val : O → Y₀)
            (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀)).N
          (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀)).E
          ((throughMembers 𝔍 T₀ y₀).map ((Subtype.val : O → Y₀) ⁻¹' ·))
          (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  show GermIdeal.pullback (m := n) (Subtype.val : O → Y₀)
      (sumIdeal (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal
        (exceptionalTermBM (throughMembers 𝔍 T₀ y₀) (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d)) = _
  rw [MarkedIdealOperationsTransform.pullback_sumIdeal contMDiff_subtype_val (hol_of_isCoherent hC)
      (hol_of_isCoherent (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSm _)),
    pullback_val_exceptionalTermBM _ hSm hSne]
  rfl

end OnOpen

/-! ### Re-basing -/

section Rebase

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

open Classical in
/-- **The original members through a point over an open set missed by the centres** correspond to those through its image:
`throughMembers (T₀' M) q = (throughMembers T₀' (M q)).map (strictAlong M)` when the centres of `M` miss `W'` and `q` lies over
`W'` (closed members). -/
theorem throughMembers_append_of_centresAvoid (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y₁ Y₀ : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (W' : Opens Y₁) (hM : CentresAvoid W' M)
    (q : openPreimage M W') :
    throughMembers 𝔍 (T₀'.append M) (q : Y₀) = (throughMembers 𝔍 T₀' (M.proj q)).map (strictAlong M) := by
  have he : IsEmptyTower (restrict W' M) := (isEmptyTower_restrict_iff W' M).mpr hM
  have hiff : ∀ H ∈ origMembers 𝔍 T₀', (q : Y₀) ∈ strictAlong M H ↔ M.proj q ∈ H := fun H hH => by
    have hHc := StepOneLowerDomain.isClosed_of_mem_origMembers 𝔍 hE T₀' H hH
    have h := ContactEmptyPrefix.strictAlong_of_isEmptyTower (X := CMfd.of (n := n) W')
      (A := (Subtype.val : W' → Y₁) ⁻¹' H) (hHc.preimage continuous_subtype_val) (restrict W' M) he
    rw [strictAlong_restrict] at h
    have hq := congrArg (fun A : Set (openPreimage M W') => q ∈ A) h
    simp only [eq_iff_iff, mem_preimage] at hq
    rw [BlowupTowerTransforms.proj_restrict] at hq
    exact hq
  unfold throughMembers
  rw [StepOneMaskTower.origMembers_append, List.filter_map]
  congr 1
  refine List.filter_congr fun H hH => ?_
  simp only [Function.comp_apply, decide_eq_decide]
  exact hiff H hH

/-- **Re-basing Bierstone--Milman's lower marked ideal**: let `T₀' M` be a multiple test blow-up of `J̄` (`𝔍` well formed,
`d ≥ 1`, of maximal order, `0 < n`), `q` a point of the last stage over the mask `W'` of `a = M(q)` at the stage `T₀'`, with
`a` in the cosupport of level `s`, and suppose the centres of `M` miss `W'`.  Then the transform of `lowerBM 𝔍 s T₀' a` along
the (empty) tower `M|_{W'}` is restricted-equivalent to the lower ideal formed at the stage `T₀' M` at `q`, restricted to
`M⁻¹W'`. -/
theorem restrictEquiv_rebase_lowerBM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₁ Y₀ : CMfd.{u} n} (T₀' : BlowupTower X Y₁)
    (M : BlowupTower Y₁ Y₀) (hT : IsGeoTestTower (barMarked 𝔍) (T₀'.append M)) {s : ℕ} {a : Y₁}
    (ha : a ∈ (geoTransformAlong (barMarked 𝔍) T₀').cosupp) (hla : level 𝔍 T₀' a = s)
    (hM : CentresAvoid (maskBM 𝔍 s T₀' a) M) (q : openPreimage M (maskBM 𝔍 s T₀' a)) (hqa : M.proj q = a) :
    RestrictEquiv (geoTransformAlong (lowerBM 𝔍 s T₀' a) (restrict (maskBM 𝔍 s T₀' a) M))
      (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 s T₀' a) → Y₀)
        (lowerIdealBM 𝔍 s (T₀'.append M) (q : Y₀))) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨hT₀', -⟩ := (isGeoTestTower_append_iff _ T₀' M).mp hT
  have hTa : IsGeoTestTower 𝔍 (T₀'.append M) := isGeoTestTower_of_barMarked h𝔍 hd _ hT
  have hTc : IsGeoTestTower (coeffEmptyBM 𝔍) (T₀'.append M) :=
    isGeoTestTower_coeffEmptyBM h𝔍 hd _ (isGeoTestTower_emptyBoundary 𝔍 _ hTa)
  obtain ⟨hT₀c, hMc⟩ := (isGeoTestTower_append_iff _ T₀' M).mp hTc
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀' hT₀' ha)
  have hbase : (T₀'.append M).proj (q : Y₀) = T₀'.proj a := by
    rw [BlowupTower.proj_append]
    exact congrArg T₀'.proj hqa
  have hWU : ((maskBM 𝔍 s T₀' a : Opens Y₁) : Set Y₁) ⊆
      openPreimage T₀' ⟨(tangentChoice 𝔍 (T₀'.proj a)).1, hU.isOpen⟩ := fun z hz => by
    match s, hz with
    | 0, hz => exact (interior_subset hz).1
    | _ + 1, hz => exact (interior_subset (s := T₀'.proj ⁻¹' (tangentChoice 𝔍 (T₀'.proj a)).1) hz.2 : _)
  have h0 := restrictEquiv_tail_contactCoeffBM h𝔍 hd ⟨(tangentChoice 𝔍 (T₀'.proj a)).1, hU.isOpen⟩ hU T₀' hT₀c
    (maskBM 𝔍 s T₀' a) hWU M hMc
  match s, hla, hM, q, hqa, h0 with
  | 0, hla, hM, q, hqa, h0 =>
    show RestrictEquiv _ (MarkedIdeal.pullback _ (contactCoeffBM 𝔍 (tangentChoice 𝔍 ((T₀'.append M).proj (q : Y₀))).2
      (T₀'.append M)))
    rw [hbase]
    exact h0
  | s' + 1, hla, hM, q, hqa, h0 =>
    set w := (tangentChoice 𝔍 (T₀'.proj a)).2 with hw
    have hwfc := isWellFormed_coeffEmptyBM h𝔍
    obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
      hwfc.isCoherent T₀' hT₀c
    obtain ⟨-, hC'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
      hwfc.isCoherent _ hTc
    have hSm := HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀' hT₀' a
    have hSne := HironakaG11InvBMLowerTailSucc.throughMembers_ne_nil 𝔍 T₀' hla
    have hthr := throughMembers_append_of_centresAvoid 𝔍 hE T₀' M (maskBM 𝔍 (s' + 1) T₀' a) hM q
    rw [hqa] at hthr
    have hSm' : ∀ H ∈ throughMembers 𝔍 (T₀'.append M) (q : Y₀), IsClosedSubmanifold n H :=
      HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn _ hT _
    have hSne' : throughMembers 𝔍 (T₀'.append M) (q : Y₀) ≠ [] := by
      rw [hthr]
      simpa using hSne
    have hkn : ResolutionInvariantSpec.DimLE n 𝔍.N n := fun x hx => by
      obtain ⟨k, hk⟩ := h𝔍.isClosedSubmanifold_N.2 x hx
      exact ⟨k, hk.1, hk⟩
    obtain ⟨hwf0, -⟩ := HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd
      ⟨(tangentChoice 𝔍 (T₀'.proj a)).1, hU.isOpen⟩ hU T₀' hkn hT₀' (maskBM 𝔍 (s' + 1) T₀' a) hWU
    set L₀ := MarkedIdeal.pullback (Subtype.val : (maskBM 𝔍 (s' + 1) T₀' a) → Y₁) (contactCoeffBM 𝔍 w T₀') with hL₀
    set SW := (throughMembers 𝔍 T₀' a).map ((Subtype.val : (maskBM 𝔍 (s' + 1) T₀' a) → Y₁) ⁻¹' ·) with hSWdef
    set Lℰ := excMarked n L₀.N L₀.E SW (contactCoeffBM 𝔍 w T₀').d with hLℰ
    have hSWm : ∀ H ∈ SW, IsClosedSubmanifold n H := fun H hH => by
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hSm H₀ hH₀) (maskBM 𝔍 (s' + 1) T₀' a)
    have hSWne : SW ≠ [] := by simpa [hSWdef] using hSne
    have hdpos : 1 ≤ (contactCoeffBM 𝔍 w T₀').d := by
      rw [contactCoeffBM_d]
      exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
    have h1 : lowerBM 𝔍 (s' + 1) T₀' a = sumMarked L₀ Lℰ :=
      HironakaG11InvBMLowerTailSucc.lowerBM_succ_eq_sumMarked 𝔍 h𝔍 hn T₀' hT₀' hla hC
    have hcohℰ : Lℰ.ideal.IsCoherent := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSWm _
    have hpair : IsSubmanifoldPair L₀ Lℰ := ⟨rfl, rfl, hwf0.isClosedSubmanifold_N, hwf0.isCoherent, hcohℰ⟩
    have he : IsEmptyTower (restrict (maskBM 𝔍 (s' + 1) T₀' a) M) := (isEmptyTower_restrict_iff (maskBM 𝔍 (s' + 1) T₀' a) M).mpr hM
    have hT0 := ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower L₀ _ he
    have hTℰ := ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower Lℰ _ he
    obtain ⟨hsum, hpairM, -⟩ := (geoTransformAlong_sumMarked_along L₀ Lℰ hpair rfl (restrict (maskBM 𝔍 (s' + 1) T₀' a) M)).2 hT0 hTℰ
    obtain ⟨hℰ, hSWm'⟩ := geoTransformAlong_excMarked (X := CMfd.of (n := n) (maskBM 𝔍 (s' + 1) T₀' a)) hwf0.isClosedSubmanifold_N hSWm hSWne
      hdpos (restrict (maskBM 𝔍 (s' + 1) T₀' a) M) hTℰ
    -- the target as a same-mark sum
    have h2 := pullback_lowerIdealBM_succ_eq_sumMarked 𝔍 (T₀'.append M) (q : Y₀) s' (openPreimage M (maskBM 𝔍 (s' + 1) T₀' a)) hSm' hSne' hC'
    have hbw : (tangentChoice 𝔍 ((T₀'.append M).proj (q : Y₀))).2 = w := by rw [hbase]
    rw [hbw] at h2
    rw [h1, h2]
    have hcohE' := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM (n := n) hSWm' (contactCoeffBM 𝔍 w T₀').d
    have hcoh₀' : (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 (s' + 1) T₀' a) → Y₀)
        (contactCoeffBM 𝔍 w (T₀'.append M))).ideal.IsCoherent :=
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hC'
    have h3 := RestrictEquiv.sumMarked h0 hℰ hpairM.N_eq hpairM.coh₁ hpairM.coh₂ hcoh₀' hcohE'
    -- the two `ℰ`-terms agree
    have hS12 : (throughMembers 𝔍 (T₀'.append M) (q : Y₀)).map ((Subtype.val : openPreimage M (maskBM 𝔍 (s' + 1) T₀' a) → Y₀) ⁻¹' ·) =
        SW.map (strictAlong (restrict (maskBM 𝔍 (s' + 1) T₀' a) M)) := by
      rw [hthr, hSWdef, List.map_map, List.map_map]
      refine List.map_congr_left fun H _ => ?_
      simp only [Function.comp_apply]
      exact (strictAlong_restrict (maskBM 𝔍 (s' + 1) T₀' a) M H).symm
    have hd12 : (contactCoeffBM 𝔍 w (T₀'.append M)).d = (contactCoeffBM 𝔍 w T₀').d := by
      rw [contactCoeffBM_d, contactCoeffBM_d]
    refine ContactEmptyPrefix.restrictEquiv_trans hsum ?_
    convert h3 using 1
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
    simp only [sumMarked_ideal, excMarked_ideal]
    rw [hS12, hd12]

/-- **The lower ideal at a stage has a coherent ideal** (`T₀` a multiple test blow-up of `J̄`, `0 < n`). -/
theorem isCoherent_lowerIdealBM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (y₀ : Y₀) (s : ℕ) :
    (lowerIdealBM 𝔍 s T₀ y₀).ideal.IsCoherent := by
  have hTa : IsGeoTestTower 𝔍 T₀ := isGeoTestTower_of_barMarked h𝔍 hd _ hT₀
  have hTc : IsGeoTestTower (coeffEmptyBM 𝔍) T₀ :=
    isGeoTestTower_coeffEmptyBM h𝔍 hd _ (isGeoTestTower_emptyBoundary 𝔍 _ hTa)
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hTc
  cases s with
  | zero => exact hC
  | succ s =>
    rw [lowerIdealBM_succ_ideal]
    exact RestrictedIdealExtension.isCoherent_sumIdeal hC (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM
      (HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ y₀) _)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Re-basing the values of a resolution invariant on Bierstone--Milman's lower marked ideals**: in the situation of
`restrictEquiv_rebase_lowerBM`, if `lowerBM 𝔍 s T₀' a` lies in the domain of `R` and `M|_{W'}` followed by `T₁` is one of its
canonical segments, then the lower ideal formed at `T₀' M` at `q`, restricted to `M⁻¹W'`, lies in the domain, `T₁` is one of its
canonical segments, and the values agree on the cosupport (`InvDomainRebase.inv_rebase`). -/
theorem inv_rebase_lowerBM (R : ResolutionInvariant.{u, v} n k Λ) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₁ Y₀ : CMfd.{u} n} (T₀' : BlowupTower X Y₁)
    (M : BlowupTower Y₁ Y₀) (hT : IsGeoTestTower (barMarked 𝔍) (T₀'.append M)) {s : ℕ} {a : Y₁}
    (ha : a ∈ (geoTransformAlong (barMarked 𝔍) T₀').cosupp) (hla : level 𝔍 T₀' a = s)
    (hM : CentresAvoid (maskBM 𝔍 s T₀' a) M) (q : openPreimage M (maskBM 𝔍 s T₀' a)) (hqa : M.proj q = a)
    (hdom : IsInvDomain k (lowerBM 𝔍 s T₀' a)) {Z : CMfd.{u} n}
    (T₁ : BlowupTower (CMfd.of (n := n) (openPreimage M (maskBM 𝔍 s T₀' a))) Z)
    (hcan : IsCanonical (lowerBM 𝔍 s T₀' a) (R.inv (lowerBM 𝔍 s T₀' a))
      ((restrict (maskBM 𝔍 s T₀' a) M).append T₁)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 s T₀' a) → Y₀)
        (lowerIdealBM 𝔍 s (T₀'.append M) (q : Y₀))) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 s T₀' a) → Y₀)
          (lowerIdealBM 𝔍 s (T₀'.append M) (q : Y₀)))
        (R.inv (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 s T₀' a) → Y₀)
          (lowerIdealBM 𝔍 s (T₀'.append M) (q : Y₀)))) T₁ ∧
      ∀ z ∈ (geoTransformAlong (lowerBM 𝔍 s T₀' a) ((restrict (maskBM 𝔍 s T₀' a) M).append T₁)).cosupp,
        R.inv (lowerBM 𝔍 s T₀' a) ((restrict (maskBM 𝔍 s T₀' a) M).append T₁) z =
          R.inv (MarkedIdeal.pullback (Subtype.val : openPreimage M (maskBM 𝔍 s T₀' a) → Y₀)
            (lowerIdealBM 𝔍 s (T₀'.append M) (q : Y₀))) T₁ z := by
  have he : IsEmptyTower (restrict (maskBM 𝔍 s T₀' a) M) :=
    (isEmptyTower_restrict_iff (maskBM 𝔍 s T₀' a) M).mpr hM
  have hEq := restrictEquiv_rebase_lowerBM 𝔍 h𝔍 hd hn hmax T₀' M hT ha hla hM q hqa
  have hcoh := GermIdealPullbackCalculus.isCoherent_pullback
    (contMDiff_subtype_val (U := openPreimage M (maskBM 𝔍 s T₀' a)))
    (isCoherent_lowerIdealBM 𝔍 h𝔍 hd hn (T₀'.append M) hT (q : Y₀) s)
  exact InvDomainRebase.inv_rebase (X := CMfd.of (n := n) (maskBM 𝔍 s T₀' a)) R hdom
    (restrict (maskBM 𝔍 s T₀' a) M) he (InvDomainRebase.restrictEquiv_symm hEq) hcoh T₁ hcan

end Rebase

end

end Hironaka.HironakaG11InvBMRebase
