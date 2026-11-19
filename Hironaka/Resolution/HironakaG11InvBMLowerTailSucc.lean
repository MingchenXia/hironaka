import Hironaka.Resolution.HironakaG11InvBMExceptionalTerm
import Hironaka.Resolution.HironakaG11InvBMLowerTail
import Hironaka.Invariant.StepOneCompare

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The cosupports of Bierstone--Milman's lower marked ideals along restricted tails (repair (B'), plan module 5)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 5, §6 item 5).
Source: Bierstone--Milman 2008, §5 Step I.B (along the year, the test blowings-up of `𝒞 + ℰ` are those of `𝒞` with centres in
the intersection `H_S` of the original members through the point, and the cosupport of `(𝒞 + ℰ)_{T₁}` is
`cosupp 𝒞_{T₁} ∩ H_S'`), Corollary 4.2.

On the mask `W = maskA ⊓ tangentOpen` of level `s + 1` around `y₀`, the lower marked ideal is the same-mark sum of the
coefficient ideal on maximal contact `L₀ = contactCoeffBM 𝔍 w T₀|_W` and the `ℰ`-marked ideal of the traces of the original
members through `y₀` (`lowerBM_succ_eq_sumMarked`).  Along a restricted tail `T₁|_W` which is a multiple test blow-up of it,
both summands have `T₁|_W` as a multiple test blow-up (`HironakaG11InvSameMarkSum`), the cosupport of `L₀` is the trace of
`cosupp 𝔍_{T₀T₁}` (`HironakaG11InvBMLowerTail`), and that of the `ℰ`-term is the strict transform of the carrier on the strict
transforms of the members (`HironakaG11InvBMExceptionalTerm`):

* `throughMembers_ne_nil`, `isClosedSubmanifold_of_mem_throughMembers`;
* `lowerBM_succ_eq_sumMarked`;
* **`mem_cosupp_lowerBM_succ_iff`**: a point over `W` lies in the cosupport of `lowerBM 𝔍 (s + 1) T₀ y₀` along `T₁|_W` iff it
  lies in `cosupp J̄_{T₀T₁}` and on the strict transforms of the original members through `y₀`;
* **`mem_cosupp_lowerBM_iff`** (both levels, the analogue of `StepOneCanonicalTail.mem_cosupp_lowerMarkedM_iff`): along a
  restricted tail which is a multiple test blow-up of the lower marked ideal of level `s`, a point over the mask lies in its
  cosupport iff it lies in `cosupp J̄_{T₀T₁}` and has level `s`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11InvBMLowerTailSucc

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.TangentDirectionAlong
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG11InvSameMarkSum Hironaka.HironakaG11InvBMExceptionalTerm
  Hironaka.BoundaryCount Hironaka.HomogenizedIdealAlongTower
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict N_geoTransformAlong)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv IsSubmanifoldPair
  hol_of_isCoherent)

noncomputable section

variable {n : ℕ}

section Succ

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- At a point of level `s + 1` some original member passes. -/
theorem throughMembers_ne_nil {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {y₀ : Y₀} {s : ℕ}
    (hl : level 𝔍 T₀ y₀ = s + 1) : throughMembers 𝔍 T₀ y₀ ≠ [] := by
  classical
  have hpos : 0 < (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length =>
      y₀ ∈ (origMembers 𝔍 T₀).get i).card := by
    have : boundaryCount (origMembers 𝔍 T₀) y₀ = s + 1 := hl
    unfold boundaryCount at this
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact List.ne_nil_of_mem (mem_throughMembers.mpr ⟨List.get_mem _ _, hi⟩)

/-- The original members through a point are closed submanifolds (along a multiple test blow-up of `J̄`, `0 < n`). -/
theorem isClosedSubmanifold_of_mem_throughMembers (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (y₀ : Y₀) :
    ∀ H ∈ throughMembers 𝔍 T₀ y₀, IsClosedSubmanifold n H := fun H hH => by
  have h𝔪 := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked 𝔍 h𝔍) T₀ hT₀
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_take (mem_throughMembers.mp hH).1)
  exact MonomialPart.isClosedSubmanifold_get hn h𝔪.isSNCDivisor i

/-- **On its mask, the lower marked ideal of level `s + 1` is the same-mark sum** of the coefficient ideal on maximal
contact and the `ℰ`-marked ideal of the traces of the original members through `y₀`. -/
theorem lowerBM_succ_eq_sumMarked (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} {s : ℕ} (hl : level 𝔍 T₀ y₀ = s + 1)
    (hC : (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal.IsCoherent) :
    lowerBM 𝔍 (s + 1) T₀ y₀ =
      sumMarked (MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 (s + 1) T₀ y₀ → Y₀)
          (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀))
        (excMarked n (MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 (s + 1) T₀ y₀ → Y₀)
            (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀)).N
          (MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 (s + 1) T₀ y₀ → Y₀)
            (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀)).E
          ((throughMembers 𝔍 T₀ y₀).map ((Subtype.val : maskBM 𝔍 (s + 1) T₀ y₀ → Y₀) ⁻¹' ·))
          (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d) := by
  have hSm := isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ y₀
  have hSne := throughMembers_ne_nil 𝔍 T₀ hl
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  show GermIdeal.pullback (m := n) (Subtype.val : maskBM 𝔍 (s + 1) T₀ y₀ → Y₀)
      (sumIdeal (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal
        (exceptionalTermBM (throughMembers 𝔍 T₀ y₀) (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d)) = _
  rw [MarkedIdealOperationsTransform.pullback_sumIdeal contMDiff_subtype_val (hol_of_isCoherent hC)
      (hol_of_isCoherent (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSm _)),
    pullback_val_exceptionalTermBM _ hSm hSne]
  rfl

/-- **The cosupport of Bierstone--Milman's lower marked ideal of level `s + 1` along the restricted tail**: along a multiple
test blow-up `T₀ T₁` of `J̄` (`𝔍` well formed, `d ≥ 1`, of maximal order, `0 < n`), for `y₀` in the cosupport at `T₀` of level
`s + 1` and `T₁|_W` a multiple test blow-up of `lowerBM 𝔍 (s + 1) T₀ y₀` (`W` its mask), a point over `W` lies in the cosupport
of the lower marked ideal along `T₁|_W` iff it lies in `cosupp J̄_{T₀ T₁}` and on the strict transforms of the original
members through `y₀`. -/
theorem mem_cosupp_lowerBM_succ_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl : level 𝔍 T₀ y₀ = s + 1)
    (hTW : IsGeoTestTower (lowerBM 𝔍 (s + 1) T₀ y₀) (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁))
    (q : openPreimage T₁ (maskBM 𝔍 (s + 1) T₀ y₀)) :
    q ∈ (geoTransformAlong (lowerBM 𝔍 (s + 1) T₀ y₀) (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁)).cosupp ↔
      (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp ∧
        ∀ H ∈ origMembers 𝔍 T₀, y₀ ∈ H → (q : Y) ∈ strictAlong T₁ H := by
  classical
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hTa : IsGeoTestTower 𝔍 (T₀.append T₁) := isGeoTestTower_of_barMarked h𝔍 hd _ hT
  have hTc : IsGeoTestTower (coeffEmptyBM 𝔍) (T₀.append T₁) :=
    isGeoTestTower_coeffEmptyBM h𝔍 hd _ (isGeoTestTower_emptyBoundary 𝔍 _ hTa)
  obtain ⟨hT₀c, hT₁c⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hTc
  obtain ⟨hxU, hU⟩ := StepOneLowerDomain.tangentChoice_spec 𝔍
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
  set U : Opens X := ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ with hUdef
  set w := (tangentChoice 𝔍 (T₀.proj y₀)).2 with hwdef
  have hWU : ((maskBM 𝔍 (s + 1) T₀ y₀) : Set Y₀) ⊆ openPreimage T₀ U := fun z hz =>
    (interior_subset (s := T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1) hz.2 : _)
  have hkn : ResolutionInvariantSpec.DimLE n 𝔍.N n := fun x hx => by
    obtain ⟨k, hk⟩ := h𝔍.isClosedSubmanifold_N.2 x hx
    exact ⟨k, hk.1, hk⟩
  obtain ⟨hwf0, -⟩ := HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd U hU T₀ hkn hT₀ (maskBM 𝔍 (s + 1) T₀ y₀)
    hWU
  obtain ⟨hT0, hcos0⟩ := HironakaG11InvBMLowerTail.isGeoTestTower_tail_contactCoeffBM h𝔍 hd U hU T₀ hT₀c (maskBM 𝔍 (s + 1) T₀ y₀) hWU T₁ hT₁c
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hT₀c
  set L₀ := MarkedIdeal.pullback (Subtype.val : (maskBM 𝔍 (s + 1) T₀ y₀) → Y₀) (contactCoeffBM 𝔍 w T₀) with hL₀
  set S := throughMembers 𝔍 T₀ y₀ with hSdef
  set SW := S.map ((Subtype.val : (maskBM 𝔍 (s + 1) T₀ y₀) → Y₀) ⁻¹' ·) with hSWdef
  set Lℰ := excMarked n L₀.N L₀.E SW (contactCoeffBM 𝔍 w T₀).d with hLℰ
  have hSm := isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn T₀ hT₀ y₀
  have hSne := throughMembers_ne_nil 𝔍 T₀ hl
  have hSWm : ∀ H ∈ SW, IsClosedSubmanifold n H := fun H hH => by
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hSm H₀ hH₀) (maskBM 𝔍 (s + 1) T₀ y₀)
  have hSWne : SW ≠ [] := by simpa [hSWdef] using hSne
  have hdpos : 1 ≤ (contactCoeffBM 𝔍 w T₀).d := by
    rw [contactCoeffBM_d]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have h1 : lowerBM 𝔍 (s + 1) T₀ y₀ = sumMarked L₀ Lℰ := lowerBM_succ_eq_sumMarked 𝔍 h𝔍 hn T₀ hT₀ hl hC
  have hpair : IsSubmanifoldPair L₀ Lℰ :=
    ⟨rfl, rfl, hwf0.isClosedSubmanifold_N, hwf0.isCoherent,
      HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hSWm _⟩
  rw [h1] at hTW ⊢
  obtain ⟨hT₁0, hT₁ℰ⟩ := (geoTransformAlong_sumMarked_along L₀ Lℰ hpair rfl (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁)).1.mp hTW
  have hcs := cosupp_geoTransformAlong_sumMarked (X := CMfd.of (n := n) (maskBM 𝔍 (s + 1) T₀ y₀)) L₀ Lℰ hpair rfl
    (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁) hT₁0 hT₁ℰ
  have hce := cosupp_geoTransformAlong_excMarked (X := CMfd.of (n := n) (maskBM 𝔍 (s + 1) T₀ y₀))
    hwf0.isClosedSubmanifold_N hSWm hSWne hdpos (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁) hT₁ℰ
  rw [hcs, hcos0, hce]
  have hWJ := coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
  rw [(hWJ.2 (T₀.append T₁)).2 hT]
  have hcosN : ∀ p : openPreimage T₁ (maskBM 𝔍 (s + 1) T₀ y₀), (p : Y) ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp →
      p ∈ strictAlong (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁) L₀.N := fun p hp => by
    have hp' : p ∈ (geoTransformAlong L₀ (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁)).cosupp := by
      rw [hcos0]
      exact hp
    have h := (geoTransformAlong L₀ (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁)).cosupp_subset_N hp'
    rwa [N_geoTransformAlong] at h
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨hqc, -, hqS⟩
    refine ⟨hqc, fun H hH hyH => ?_⟩
    have h := hqS _ (List.mem_map_of_mem (f := ((Subtype.val : (maskBM 𝔍 (s + 1) T₀ y₀) → Y₀) ⁻¹' ·)) (mem_throughMembers.mpr ⟨hH, hyH⟩))
    rw [strictAlong_restrict] at h
    exact h
  · rintro ⟨hqc, hqS⟩
    refine ⟨hqc, hcosN q hqc, fun H hH => ?_⟩
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    obtain ⟨hH₀E, hyH₀⟩ := mem_throughMembers.mp hH₀
    show q ∈ strictAlong (restrict (maskBM 𝔍 (s + 1) T₀ y₀) T₁) ((Subtype.val : (maskBM 𝔍 (s + 1) T₀ y₀) → Y₀) ⁻¹' H₀)
    rw [strictAlong_restrict]
    exact hqS H₀ hH₀E hyH₀

/-- **The cosupport of Bierstone--Milman's lower marked ideals along restricted tails, both levels** (the analogue of
`StepOneCanonicalTail.mem_cosupp_lowerMarkedM_iff`): along a multiple test blow-up `T₀ T₁` of `J̄`, for `y₀` in the cosupport
at `T₀` of level `s` and `T₁|_W` a multiple test blow-up of `lowerBM 𝔍 s T₀ y₀` (`W` its mask), a point over `W` lies in the
cosupport of the lower marked ideal along `T₁|_W` iff it lies in `cosupp J̄_{T₀ T₁}` and has level `s`. -/
theorem mem_cosupp_lowerBM_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl₀ : level 𝔍 T₀ y₀ = s)
    (hTW : IsGeoTestTower (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁))
    (q : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) :
    q ∈ (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁)).cosupp ↔
      (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp ∧ level 𝔍 (T₀.append T₁) q = s := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  match s, hl₀, hTW, q with
  | 0, hl₀, hTW, q =>
    have h := (HironakaG11InvBMLowerTail.isGeoTestTower_tail_lowerBM_zero 𝔍 h𝔍 hd hmax T₀ T₁ hT hy₀).2
    have hl := StepOneMaskTower.level_eq_zero_of_mem_maskB 𝔍 hE T₀ T₁ q.2
    have hWJ := coeff_homAlong_wEquiv 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
    rw [h, (hWJ.2 (T₀.append T₁)).2 hT]
    exact ⟨fun hq => ⟨hq, hl⟩, fun hq => hq.1⟩
  | s' + 1, hl₀, hTW, q =>
    have h := mem_cosupp_lowerBM_succ_iff 𝔍 h𝔍 hd hn hmax T₀ T₁ hT hy₀ hl₀ hTW q
    have hlev := StepOneCompare.level_eq_iff_of_mem_maskA 𝔍 hE T₀ T₁ (y₀ := y₀) (q := (q : Y)) q.2.1
    rw [hl₀] at hlev
    exact h.trans (and_congr_right fun _ => hlev.symm)

end Succ

end

end Hironaka.HironakaG11InvBMLowerTailSucc
