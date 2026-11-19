import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Resolution.HironakaG8LogFiniteSumTransform
import Hironaka.Resolution.HironakaG8LogClosureHistory
import Hironaka.Resolution.HironakaG8LogFiniteSumCut
import Hironaka.Resolution.HironakaControlledTransform
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Invariant.SmoothCentreHomogeneity
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The `ℰ`-sum respects the local equivalence (G8 lane, run 0080, round 4; (B') port P5, the `ℰ`-sum)

Blueprint: `hironaka-g8-resume-local-exceptional-sum.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P5:
"`(𝒞 + ℰ_S) ≈ (𝒞' + ℰ_S)` whenever `𝒞 ≈ 𝒞'` (same carrier dimension)"), D5 and BM08 §5 Step I.B: at level `s ≥ 1` the lower
ideal is the same-mark sum `𝒞 + ℰ_S`, `ℰ_S = ∑_{H ∈ S} 𝓘_H^{d}` over the original members `S` through the anchor
(`HironakaG11InvBMLower.lowerIdealBM`, `exceptionalTermBM`).

* `excBase`, `excExp`, `excMark`, `excIdeal I S e = 𝔞 + ∑_{H ∈ S} 𝓘_H^e` (as one common-mark finite sum: `𝔞` of mark `e` with
  exponent `1`, each `𝓘_H` of mark `1` with exponent `e`), **`addExc A S = (N, E, excIdeal 𝔞 S d, d)`**;
* `throughSet S = ⋂_{H ∈ S} H` and **`cosupport_excIdeal`**: `cosupp(A ⊕ ℰ_S) = cosupp A ∩ ⋂_{H∈S} H` (no condition relating
  the members to the carrier);
* `geoTransform_member_restrictLe`/`_ge`: for `C ⊆ H` admissible, the transform along the carrier of `(𝓘_H, 1)` is
  `𝓘_{H'}` on the strict transform of the carrier (`HironakaControlledTransform.controlled_transform`,
  `BlowupStrictIdeal.controlledTransform_vanishingIdeal`); **`geoTransform_addExc_restrictLe/_ge`**: the transform of
  `A ⊕ ℰ_S` is `A' ⊕ ℰ_{S'}` on the new carrier (`S'` the strict transforms);
* pullbacks of `ℰ`-sums along holomorphic maps that pull vanishing ideals back to vanishing ideals (products with a line,
  open inclusions);
* `ExcRel`, `ExcPair κ`, **`isLocStable_excPair`** and **`locEquiv_addExc`**: if `A ≈ B` (`LocEquiv κ`, no exceptional
  blowups, both of the native domain, the same mark; carriers may differ) and `S` is a list of closed submanifolds, then
  `A ⊕ ℰ_S ≈ B ⊕ ℰ_S`.

Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalExcSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism RelativePrincipalizationSpan
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.IdealWeightPowers (idealPow)
open Hironaka.GermIdealOrder (cosupport)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.RestrictedIdealQuotient (colonAlong)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform)
open Hironaka.HironakaG8LogFiniteSumTransform (finSumIdeal_congr mem_finSumIdeal_of_mem
  restrictLe_finSumIdeal restrictLe_colonAlong_finSum_le restrictLe_finSum_le_colonAlong)
open Hironaka.HironakaG8LogControlledMarked (restrictLe_colonAlong_of_restrictLe)
open Hironaka.HironakaG8LogMixedHistory (restrictLe_pullback_of_restrictLe)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open scoped ProductComplexManifold

noncomputable section

/-! ### The `ℰ`-sum -/

section Defs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The generators of the `ℰ`-sum: `𝔞`, then the ideals of the members. -/
def excBase (I : GermIdeal n M) (S : List (Set M)) : ℕ → GermIdeal n M
  | 0 => I
  | i + 1 => vanishingIdeal (n := n) (S.getD i ∅)

/-- The exponents: `1` for `𝔞`, `e` for the members. -/
def excExp (e : ℕ) : ℕ → ℕ
  | 0 => 1
  | _ + 1 => e

/-- The marks: `e` for `𝔞`, `1` for the members. -/
def excMark (e : ℕ) : ℕ → ℕ
  | 0 => e
  | _ + 1 => 1

theorem excMark_mul_excExp (e : ℕ) : ∀ i, excMark e i * excExp e i = e
  | 0 => Nat.mul_one e
  | _ + 1 => Nat.one_mul e

/-- **The `ℰ`-sum ideal** `𝔞 + ∑_{H ∈ S} 𝓘_H^e`. -/
def excIdeal (I : GermIdeal n M) (S : List (Set M)) (e : ℕ) : GermIdeal n M :=
  finSumIdeal (fun i => idealPow (excBase I S i) (excExp e i)) (S.length + 1)

/-- **The `ℰ`-sum of a marked ideal**: `A ⊕ ℰ_S = (N, E, 𝔞 + ∑_{H ∈ S} 𝓘_H^d, d)`. -/
def addExc (A : MarkedIdeal n M) (S : List (Set M)) : MarkedIdeal n M :=
  ⟨A.N, A.E, excIdeal A.ideal S A.d, A.d⟩

/-- The intersection of the members. -/
def throughSet (S : List (Set M)) : Set M := {x | ∀ H ∈ S, x ∈ H}

theorem getD_mem {S : List (Set M)} {i : ℕ} (hi : i < S.length) : S.getD i ∅ ∈ S := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem forall_getD_iff {S : List (Set M)} {x : M} : (∀ i < S.length, x ∈ S.getD i ∅) ↔ x ∈ throughSet S := by
  constructor
  · intro h H hH
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hH
    have := h i hi
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro h i hi
    exact h _ (getD_mem hi)

theorem getD_map_of_lt {β : Type*} (f : Set M → β) (S : List (Set M)) (d : β) {i : ℕ} (hi : i < S.length) :
    (S.map f).getD i d = f (S.getD i ∅) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

end Defs

section Basic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem excBase_hol {I : GermIdeal n M} (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) (S : List (Set M)) :
    ∀ i x g, (excBase I S i).mem x g → HolomorphicAt n g x
  | 0, x, g, hg => hI x g hg
  | _ + 1, _, _, hg => hg.1

theorem excIdeal_hol (I : GermIdeal n M) (S : List (Set M)) (e : ℕ) :
    ∀ x g, (excIdeal I S e).mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1

/-- `cosupp(𝓘_H|_N, 1) = N ∩ H` for a closed `H`. -/
theorem cosupport_vanishingIdeal_one {N H : Set M} (hH : IsClosed H) :
    cosupport n N (vanishingIdeal (n := n) H) 1 = N ∩ H := by
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, ?_⟩
    by_contra hxH
    have h1 : (vanishingIdeal (n := n) H).mem x (fun _ => (1 : ℂ)) :=
      ⟨holomorphicAt_const 1, by
        filter_upwards [hH.isOpen_compl.mem_nhds hxH] with y hy hyH
        exact absurd hyH hy⟩
    have h2 := (GermIdealOrder.vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hx _ h1)
    exact one_ne_zero h2
  · rintro ⟨hxN, hxH⟩
    refine ⟨hxN, fun g hg => (GermIdealOrder.vanishesToOrderOn_one_iff hxN hg.1).mpr ?_⟩
    exact hg.2.self_of_nhds hxH

/-- **The cosupport of the `ℰ`-sum**: `cosupp(𝔞 + ∑ 𝓘_H^e, e) = cosupp(𝔞, e) ∩ ⋂ H` (`e ≥ 1`, closed members). -/
theorem cosupport_excIdeal {N : Set M} (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k) {I : GermIdeal n M}
    (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosed H) {e : ℕ}
    (he : 1 ≤ e) : cosupport n N (excIdeal I S e) e = cosupport n N I e ∩ throughSet S := by
  unfold excIdeal
  rw [HironakaG8LogFiniteSumCut.cosupport_finSumIdeal
    (fun i x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
  have h0 : cosupport n N (idealPow (excBase I S 0) (excExp e 0)) e = cosupport n N I e := by
    have := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN hI (le_refl 1) e
    rw [Nat.mul_one] at this
    exact this
  have hs : ∀ i < S.length, cosupport n N (idealPow (excBase I S (i + 1)) (excExp e (i + 1))) e =
      N ∩ S.getD i ∅ := by
    intro i hi
    have := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN
      (fun x g hg => (show (vanishingIdeal (n := n) (S.getD i ∅)).mem x g from hg).1) he 1
    rw [Nat.one_mul] at this
    show cosupport n N (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e) e = _
    rw [this, cosupport_vanishingIdeal_one (hS _ (getD_mem hi))]
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨h0 ▸ hx 0 (Nat.succ_pos _), forall_getD_iff.mp fun i hi => ?_⟩
    have := hx (i + 1) (by omega)
    rw [hs i hi] at this
    exact this.2
  · rintro ⟨hx, hxS⟩
    refine ⟨hx.1, fun i hi => ?_⟩
    rcases i with _ | i
    · rw [h0]
      exact hx
    · rw [hs i (by omega)]
      exact ⟨hx.1, forall_getD_iff.mpr hxS i (by omega)⟩

end Basic

/-! ### One admissible blowup -/

section Transform

variable {n : ℕ} {X Z : CMfd.{u} n} {C : Set X} {π : Z → X}

/-- **The transform of `(𝓘_H, 1)` along the carrier is `𝓘_{H'}`** on the strict transform of the carrier, for an admissible
centre `C ⊆ H` of a well-formed `A` (controlled transform with mark one). -/
theorem geoTransform_member (A : MarkedIdeal n X) (hA : A.IsWellFormed) (hC : A.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) {H : Set X} (hH : IsClosedSubmanifold n H) (hCH : C ⊆ H) :
    RestrictLe (geoStrictTransform π C A.N)
        (colonAlong n (geoStrictTransform π C A.N) (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1))
        (vanishingIdeal (n := n) (geoStrictTransform π C H)) ∧
      RestrictLe (geoStrictTransform π C A.N) (vanishingIdeal (n := n) (geoStrictTransform π C H))
        (colonAlong n (geoStrictTransform π C A.N) (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1)) := by
  set 𝔪H : MarkedIdeal n X := ⟨A.N, A.E, vanishingIdeal (n := n) H, 1⟩ with h𝔪H
  have hwf : 𝔪H.IsWellFormed := ⟨hA.isClosedSubmanifold_N, VanishingIdealCoherent.isCoherent_vanishingIdeal hH,
    hA.isSNCDivisor, hA.isTransverse⟩
  have hCadm : 𝔪H.IsAdmissibleCentre C := by
    refine ⟨hC.1, fun x hx => ?_, hC.2.2⟩
    show x ∈ cosupport n A.N (vanishingIdeal (n := n) H) 1
    rw [cosupport_vanishingIdeal_one hH.1]
    exact ⟨hC.subset_N hx, hCH hx⟩
  have hT : IsGeoTestTower 𝔪H (.step .refl C π hπ) := ⟨trivial, hCadm⟩
  obtain ⟨-, -, -, h1, h2, -⟩ := HironakaControlledTransform.controlled_transform 𝔪H hwf rfl (.step .refl C π hπ) hT
  have hct : HironakaControlledTransform.controlledTransformAlong (vanishingIdeal (n := n) H) (.step .refl C π hπ) =
      vanishingIdeal (n := n) (geoStrictTransform π C H) := by
    rw [← BlowupStrictIdeal.controlledTransform_vanishingIdeal hπ hH hCH]
    unfold BlowupControlledTransform.controlledTransform
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
    rfl
  rw [hct] at h1 h2
  exact ⟨h2, h1⟩

/-- **The transform of the `ℰ`-sum is the `ℰ`-sum of the transform** (on the strict transform of the carrier; the
members are replaced by their strict transforms): for an admissible centre `C` of a well-formed `A` lying in every member. -/
theorem geoTransform_excIdeal (A : MarkedIdeal n X) (hA : A.IsWellFormed) (hC : A.IsAdmissibleCentre C)
    (hπ : IsBlowupAlong n C π) {S : List (Set X)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hCS : ∀ H ∈ S, C ⊆ H) :
    RestrictLe (geoStrictTransform π C A.N)
        (colonAlong n (geoStrictTransform π C A.N) (GermIdeal.pullback (m := n) π (excIdeal A.ideal S A.d))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) A.d))
        (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) A.d) ∧
      RestrictLe (geoStrictTransform π C A.N)
        (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) A.d)
        (colonAlong n (geoStrictTransform π C A.N) (GermIdeal.pullback (m := n) π (excIdeal A.ideal S A.d))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) A.d)) := by
  have hNc := hA.isClosedSubmanifold_N.1
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isCoherent
  have hbase := excBase_hol hIhol S
  have hle : ∀ i < S.length + 1, RestrictLe A.N (excBase A.ideal S i)
      (idealPow (vanishingIdeal (n := n) C) (excMark A.d i)) := by
    intro i hi
    rcases i with _ | i
    · exact HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport hA.isCoherent
        hA.isClosedSubmanifold_N hC.1 hC.subset_N hC.2.1
    · have hCH := hCS _ (getD_mem (show i < S.length by omega))
      intro x _ g hg
      have hg' : (vanishingIdeal (n := n) (S.getD i ∅)).mem x g := hg
      refine IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ?_ hg'.1)
      show (idealPow (vanishingIdeal (n := n) C) 1).mem x g
      rw [FactorizationFromResolution.idealPow_one_of_isCoherent
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hC.1)]
      exact ⟨hg'.1, hg'.2.mono fun y hy hyC => hy (hCH hyC)⟩
  have hdk : ∀ i < S.length + 1, excMark A.d i * excExp A.d i = A.d := fun i _ => excMark_mul_excExp A.d i
  have h1 := restrictLe_colonAlong_finSum_le hπ hNc (A := excBase A.ideal S) (d := excMark A.d) (k := excExp A.d)
    (m := S.length + 1) (L := A.d) (fun i _ => hbase i) hle hdk
  have h2 := restrictLe_finSum_le_colonAlong hπ (N := A.N) (A := excBase A.ideal S) (d := excMark A.d)
    (k := excExp A.d) (m := S.length + 1) (L := A.d) (fun i _ => hbase i) hdk
  have hpowhol : ∀ {J : GermIdeal n Z} {k : ℕ}, ∀ x g, (idealPow J k).mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg
  have hm1 : RestrictLe (geoStrictTransform π C A.N)
      (finSumIdeal (fun i => idealPow (colonAlong n (geoStrictTransform π C A.N)
        (GermIdeal.pullback (m := n) π (excBase A.ideal S i))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (excMark A.d i))) (excExp A.d i))
        (S.length + 1))
      (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) A.d) := by
    unfold excIdeal
    rw [List.length_map]
    refine restrictLe_finSumIdeal (fun i _ => hpowhol) fun i hi => ?_
    rcases i with _ | i
    · exact DerivativeIdealAlongTransform.restrictLe_refl hpowhol
    · have hi' : i < S.length := by omega
      have hm := (geoTransform_member A hA hC hπ (hS _ (getD_mem hi')) (hCS _ (getD_mem hi'))).1
      show RestrictLe (geoStrictTransform π C A.N)
        (idealPow (colonAlong n (geoStrictTransform π C A.N)
          (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (S.getD i ∅)))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1)) A.d)
        (idealPow (vanishingIdeal (n := n) ((S.map (geoStrictTransform π C)).getD i ∅)) A.d)
      rw [getD_map_of_lt _ S ∅ hi']
      exact MarkedIdealOperationsAlong.restrictLe_idealPow
        (𝔟 := vanishingIdeal (n := n) (geoStrictTransform π C (S.getD i ∅))) (fun _ _ hg => hg.1) hm A.d
  have hm2 : RestrictLe (geoStrictTransform π C A.N)
      (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) A.d)
      (finSumIdeal (fun i => idealPow (colonAlong n (geoStrictTransform π C A.N)
        (GermIdeal.pullback (m := n) π (excBase A.ideal S i))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (excMark A.d i))) (excExp A.d i))
        (S.length + 1)) := by
    unfold excIdeal
    rw [List.length_map]
    refine restrictLe_finSumIdeal (fun i _ => hpowhol) fun i hi => ?_
    rcases i with _ | i
    · exact DerivativeIdealAlongTransform.restrictLe_refl hpowhol
    · have hi' : i < S.length := by omega
      have hm := (geoTransform_member A hA hC hπ (hS _ (getD_mem hi')) (hCS _ (getD_mem hi'))).2
      show RestrictLe (geoStrictTransform π C A.N)
        (idealPow (vanishingIdeal (n := n) ((S.map (geoStrictTransform π C)).getD i ∅)) A.d)
        (idealPow (colonAlong n (geoStrictTransform π C A.N)
          (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (S.getD i ∅)))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1)) A.d)
      rw [getD_map_of_lt _ S ∅ hi']
      exact MarkedIdealOperationsAlong.restrictLe_idealPow
        (𝔟 := colonAlong n (geoStrictTransform π C A.N)
          (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (S.getD i ∅)))
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 1)) (fun _ _ hg => hg.1) hm A.d
  exact ⟨DerivativeIdealAlongTransform.restrictLe_trans h1 hm1, DerivativeIdealAlongTransform.restrictLe_trans hm2 h2⟩

end Transform

/-! ### Pullbacks -/

section Pullback

variable {n p : ℕ} {M M' : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace M'] [ChartedSpace (ComplexModel p) M'] [IsComplexManifold p M'] {φ : M' → M}

/-- **The pullback of an `ℰ`-sum lies in the `ℰ`-sum of the pullback** (for a map pulling the ideals of the members back to
the ideals of their preimages). -/
theorem pullback_excIdeal_le (hφ : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ φ) {I : GermIdeal n M}
    (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) {S : List (Set M)}
    (hvan : ∀ i < S.length, GermIdeal.pullback (m := p) φ (vanishingIdeal (n := n) (S.getD i ∅)) =
      vanishingIdeal (n := p) (φ ⁻¹' S.getD i ∅)) (e : ℕ) (W' : Set M') :
    RestrictLe W' (GermIdeal.pullback (m := p) φ (excIdeal I S e))
      (excIdeal (GermIdeal.pullback (m := p) φ I) (S.map (φ ⁻¹' ·)) e) := by
  intro z _ g hg
  have h1 := HironakaG8LogClosureHistory.pullback_finSumIdeal_le hφ (A := excBase I S) (excBase_hol hI S)
    (k := excExp e) (m := S.length + 1) hg
  have heq : finSumIdeal (fun i => idealPow (GermIdeal.pullback (m := p) φ (excBase I S i)) (excExp e i))
      (S.length + 1) = excIdeal (GermIdeal.pullback (m := p) φ I) (S.map (φ ⁻¹' ·)) e := by
    unfold excIdeal
    rw [List.length_map]
    refine finSumIdeal_congr fun i hi => ?_
    rcases i with _ | i
    · rfl
    · show idealPow (GermIdeal.pullback (m := p) φ (vanishingIdeal (n := n) (S.getD i ∅))) e =
        idealPow (vanishingIdeal (n := p) ((S.map (φ ⁻¹' ·)).getD i ∅)) e
      rw [hvan i (by omega), getD_map_of_lt _ S ∅ (show i < S.length by omega)]
  rw [heq] at h1
  exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self h1 h1.1)

/-- **The `ℰ`-sum of the pullback lies in the pullback of the `ℰ`-sum.** -/
theorem excIdeal_pullback_le (hφ : ContMDiff 𝓘(ℂ, ComplexModel p) 𝓘(ℂ, ComplexModel n) ∞ φ) {I : GermIdeal n M}
    (hI : ∀ x g, I.mem x g → HolomorphicAt n g x) {S : List (Set M)}
    (hvan : ∀ i < S.length, GermIdeal.pullback (m := p) φ (vanishingIdeal (n := n) (S.getD i ∅)) =
      vanishingIdeal (n := p) (φ ⁻¹' S.getD i ∅)) (e : ℕ) (W' : Set M') :
    RestrictLe W' (excIdeal (GermIdeal.pullback (m := p) φ I) (S.map (φ ⁻¹' ·)) e)
      (GermIdeal.pullback (m := p) φ (excIdeal I S e)) := by
  intro z _ g hg
  have hg' : IsInSpanAt (n := p) (fun s => ∃ i, i < S.length + 1 ∧
      (idealPow (excBase (GermIdeal.pullback (m := p) φ I) (S.map (φ ⁻¹' ·)) i) (excExp e i)).mem z s) z g := by
    have := hg
    unfold excIdeal at this
    rw [List.length_map] at this
    exact this
  have hmem : (GermIdeal.pullback (m := p) φ (excIdeal I S e)).mem z g := by
    show IsInSpanAt (n := p) (fun t => ∃ a, (excIdeal I S e).mem (φ z) a ∧ t = a ∘ φ) z g
    refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) hg'
    obtain ⟨i, hi, hs⟩ := hs
    have hbase : excBase (GermIdeal.pullback (m := p) φ I) (S.map (φ ⁻¹' ·)) i =
        GermIdeal.pullback (m := p) φ (excBase I S i) := by
      rcases i with _ | i
      · rfl
      · show vanishingIdeal (n := p) ((S.map (φ ⁻¹' ·)).getD i ∅) =
          GermIdeal.pullback (m := p) φ (vanishingIdeal (n := n) (S.getD i ∅))
        rw [hvan i (by omega), getD_map_of_lt _ S ∅ (show i < S.length by omega)]
    rw [hbase, ← HironakaActualNonregularCoefficientNaturality.pullback_idealPow hφ
      (fun hg => excBase_hol hI S i _ _ hg)] at hs
    have hs' : IsInSpanAt (n := p) (fun t => ∃ a, (idealPow (excBase I S i) (excExp e i)).mem (φ z) a ∧ t = a ∘ φ)
        z s := hs
    refine hs'.mono ?_
    rintro t ⟨a, ha, rfl⟩
    exact ⟨a, mem_finSumIdeal_of_mem (J := fun i => idealPow (excBase I S i) (excExp e i)) hi ha
      (GermIdealOrder.holomorphicAt_of_mem_idealPow ha), rfl⟩
  exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem hmem.1)

end Pullback

/-! ### The relation and its stability -/

section Rel

variable {n : ℕ}

/-- **`P` is restricted-equivalent to the `ℰ`-sum `A ⊕ ℰ_S`.** -/
structure ExcRel {Y : CMfd.{u} n} (P A : MarkedIdeal n Y) (S : List (Set Y)) : Prop where
  N_eq : P.N = A.N
  E_eq : P.E = A.E
  d_eq : P.d = A.d
  hol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x
  le : RestrictLe A.N P.ideal (excIdeal A.ideal S A.d)
  ge : RestrictLe A.N (excIdeal A.ideal S A.d) P.ideal

variable {Y : CMfd.{u} n} {P A : MarkedIdeal n Y} {S : List (Set Y)}

theorem excRel_addExc (A : MarkedIdeal n Y) (S : List (Set Y)) : ExcRel (addExc A S) A S :=
  ⟨rfl, rfl, rfl, excIdeal_hol _ _ _, DerivativeIdealAlongTransform.restrictLe_refl (excIdeal_hol _ _ _),
    DerivativeIdealAlongTransform.restrictLe_refl (excIdeal_hol _ _ _)⟩

/-- **The cosupport**: `cosupp P = cosupp A ∩ ⋂_{H ∈ S} H`. -/
theorem ExcRel.cosupp_eq {r : ℕ} (h : ExcRel P A S) (hA : IsInvDomain r A) (hS : ∀ H ∈ S, IsClosed H) :
    P.cosupp = A.cosupp ∩ throughSet S := by
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent
  show cosupport n P.N P.ideal P.d = cosupport n A.N A.ideal A.d ∩ throughSet S
  rw [h.N_eq, h.d_eq, ← cosupport_excIdeal hA.isWellFormed.isClosedSubmanifold_N.2 hIhol hS hA.one_le_d]
  exact Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.ge _)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.le _)

/-- **The form of `HironakaG11InvBMLower.lowerIdealBM`** (`𝔞 + exceptionalTermBM S d` as a binary sum) is
restricted-equivalent to `A ⊕ ℰ_S` (coherent `𝔞`). -/
theorem excRel_sumIdeal (A : MarkedIdeal n Y) (hA : A.ideal.IsCoherent) (S : List (Set Y)) :
    ExcRel (⟨A.N, A.E, RestrictedIdealExtension.sumIdeal A.ideal
      (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) S.length), A.d⟩ :
        MarkedIdeal n Y) A S := by
  have hpow1 : idealPow A.ideal 1 = A.ideal := FactorizationFromResolution.idealPow_one_of_isCoherent hA
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA
  have hiff : ∀ x g, (RestrictedIdealExtension.sumIdeal A.ideal
      (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) S.length)).mem x g ↔
        (excIdeal A.ideal S A.d).mem x g := by
    intro x g
    constructor
    · intro hg
      have hg' : IsInSpanAt (n := n) (fun s => A.ideal.mem x s ∨
          (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) S.length).mem x s) x g := hg
      show IsInSpanAt (n := n) (fun s => ∃ i, i < S.length + 1 ∧
        (idealPow (excBase A.ideal S i) (excExp A.d i)).mem x s) x g
      refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) hg'
      rcases hs with hs | hs
      · refine InvertibleIdealQuotient.isInSpanAt_self ⟨0, Nat.succ_pos _, ?_⟩ (hIhol x s hs)
        show (idealPow A.ideal 1).mem x s
        rw [hpow1]
        exact hs
      · have hs' : IsInSpanAt (n := n) (fun t => ∃ i, i < S.length ∧
            (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d).mem x t) x s := hs
        exact hs'.mono fun t ⟨i, hi, ht⟩ => ⟨i + 1, by omega, ht⟩
    · intro hg
      have hg' : IsInSpanAt (n := n) (fun s => ∃ i, i < S.length + 1 ∧
          (idealPow (excBase A.ideal S i) (excExp A.d i)).mem x s) x g := hg
      show IsInSpanAt (n := n) (fun s => A.ideal.mem x s ∨
        (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) S.length).mem x s) x g
      refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) hg'
      obtain ⟨i, hi, hs⟩ := hs
      rcases i with _ | i
      · have hs' : (idealPow A.ideal 1).mem x s := hs
        rw [hpow1] at hs'
        exact InvertibleIdealQuotient.isInSpanAt_self (Or.inl hs') (hIhol x s hs')
      · have hs' : (idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d).mem x s := hs
        have hhol := GermIdealOrder.holomorphicAt_of_mem_idealPow hs'
        exact InvertibleIdealQuotient.isInSpanAt_self (Or.inr (mem_finSumIdeal_of_mem
          (J := fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) (by omega) hs' hhol)) hhol
  refine ⟨rfl, rfl, rfl, fun _ _ hg => hg.1, fun x _ g hg => ?_, fun x _ g hg => ?_⟩
  · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ((hiff x g).mp hg) hg.1)
  · exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self ((hiff x g).mpr hg) hg.1)

/-- **One admissible blowup.** -/
theorem ExcRel.geoTransform {Z : CMfd.{u} n} {C : Set Y} {π : Z → Y} (h : ExcRel P A S) (hA : A.IsWellFormed)
    (hC : A.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) (hS : ∀ H ∈ S, IsClosedSubmanifold n H)
    (hCS : ∀ H ∈ S, C ⊆ H) :
    ExcRel (P.geoTransform C π) (A.geoTransform C π) (S.map (geoStrictTransform π C)) := by
  have hNc := hA.isClosedSubmanifold_N.1
  have hsub : ∀ q ∈ geoStrictTransform π C A.N, π q ∈ A.N := fun q hq =>
    BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hq
  obtain ⟨t1, t2⟩ := geoTransform_excIdeal A hA hC hπ hS hCS
  refine ⟨?_, ?_, h.d_eq, fun _ _ hg => hg.1, ?_, ?_⟩
  · show geoStrictTransform π C P.N = geoStrictTransform π C A.N
    rw [h.N_eq]
  · show P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] = A.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    rw [h.E_eq]
  · show RestrictLe (geoStrictTransform π C A.N)
      (colonAlong n (geoStrictTransform π C P.N) (GermIdeal.pullback (m := n) π P.ideal)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) P.d))
      (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) (A.geoTransform C π).d)
    rw [h.N_eq, h.d_eq]
    exact DerivativeIdealAlongTransform.restrictLe_trans (restrictLe_colonAlong_of_restrictLe
      (restrictLe_pullback_of_restrictLe hπ.contMDiff hsub (excIdeal_hol _ _ _) h.le)) t1
  · show RestrictLe (geoStrictTransform π C A.N)
      (excIdeal (A.geoTransform C π).ideal (S.map (geoStrictTransform π C)) (A.geoTransform C π).d)
      (colonAlong n (geoStrictTransform π C P.N) (GermIdeal.pullback (m := n) π P.ideal)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) P.d))
    rw [h.N_eq, h.d_eq]
    exact DerivativeIdealAlongTransform.restrictLe_trans t2 (restrictLe_colonAlong_of_restrictLe
      (restrictLe_pullback_of_restrictLe hπ.contMDiff hsub h.hol h.ge))

open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal
  projection_test_isInvDomain) in
/-- **One product with a line.** -/
theorem ExcRel.projectionTest {r : ℕ} (h : ExcRel P A S) (hA : IsInvDomain r A)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    ExcRel (projectionTest P) (projectionTest A) (S.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·)) := by
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent
  have hφ := ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hsubm := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hvan : ∀ i < S.length, GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient Y → Y)
      (vanishingIdeal (n := n) (S.getD i ∅)) =
        vanishingIdeal (n := n + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' S.getD i ∅) := fun i hi =>
    HironakaSmoothSubmersionRelativeRestriction.pullback_vanishingIdeal_submersion hsubm (hS _ (getD_mem hi))
  refine ⟨?_, ?_, h.d_eq, fun _ _ hg => hg.1, ?_, ?_⟩
  · show (Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N = (Prod.fst : projectionAmbient Y → Y) ⁻¹' A.N
    rw [h.N_eq]
  · show P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
      A.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]
    rw [h.E_eq]
  · exact DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) (excIdeal_hol _ _ _) h.le)
      (pullback_excIdeal_le hφ hIhol hvan A.d _)
  · exact DerivativeIdealAlongTransform.restrictLe_trans (excIdeal_pullback_le hφ hIhol hvan A.d _)
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) h.hol h.ge)

/-- **One restriction to an open subset.** -/
theorem ExcRel.pullback_val {r : ℕ} (h : ExcRel P A S) (hA : IsInvDomain r A) (U : Opens Y) :
    ExcRel (Y := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
      (MarkedIdeal.pullback (Subtype.val : U → Y) A) (S.map ((Subtype.val : U → Y) ⁻¹' ·)) := by
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent
  have hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → Y) := contMDiff_subtype_val
  have hvan : ∀ i < S.length, GermIdeal.pullback (m := n) (Subtype.val : U → Y)
      (vanishingIdeal (n := n) (S.getD i ∅)) = vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' S.getD i ∅) :=
    fun i _ => SmoothCentreHomogeneity.pullback_val_vanishingIdeal U _
  refine ⟨?_, ?_, h.d_eq, fun _ _ hg => hg.1, ?_, ?_⟩
  · show (Subtype.val : U → Y) ⁻¹' P.N = (Subtype.val : U → Y) ⁻¹' A.N
    rw [h.N_eq]
  · show P.E.map ((Subtype.val : U → Y) ⁻¹' ·) = A.E.map ((Subtype.val : U → Y) ⁻¹' ·)
    rw [h.E_eq]
  · exact DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) (excIdeal_hol _ _ _) h.le)
      (pullback_excIdeal_le hφ hIhol hvan A.d _)
  · exact DerivativeIdealAlongTransform.restrictLe_trans (excIdeal_pullback_le hφ hIhol hvan A.d _)
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) h.hol h.ge)

end Rel

section Stable

/-- **The relation of the `ℰ`-sums**: `P ≅ A ⊕ ℰ_S` and `Q ≅ B ⊕ ℰ_S` for locally equivalent `A ≈ B` of the native domain
with the same mark (carriers may differ) and closed submanifolds `S`. -/
def ExcPair (κ : Kinds) {n : ℕ} {Y : CMfd.{u} n} (P Q : MarkedIdeal n Y) : Prop :=
  ∃ (A B : MarkedIdeal n Y) (S : List (Set Y)) (r r' : ℕ), LocEquiv κ A B ∧ IsInvDomain r A ∧ IsInvDomain r' B ∧
    B.d = A.d ∧ (∀ H ∈ S, IsClosedSubmanifold n H) ∧ ExcRel P A S ∧ ExcRel Q B S

open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient
  projection_test_isInvDomain) in
/-- **The relation of the `ℰ`-sums is stable under the local test actions.** -/
theorem isLocStable_excPair (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => ExcPair κ (n := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩
    rw [hQ.E_eq, hP.E_eq]
    exact h.E_eq
  cosupp_eq := by
    rintro m Y P Q ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩
    rw [hP.cosupp_eq hA (fun H hH => (hS H hH).1), hQ.cosupp_eq hB (fun H hH => (hS H hH).1), h.cosupp_eq_base]
  controlled := by
    rintro m Y P Q ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩ C Z π hπ hC
    have hcos := hP.cosupp_eq hA (fun H hH => (hS H hH).1)
    have hCsub : C ⊆ A.cosupp ∩ throughSet S := hcos ▸ hC.2.1
    have hCA : A.IsAdmissibleCentre C := ⟨hC.1, fun x hx => (hCsub hx).1, hP.E_eq ▸ hC.2.2⟩
    have hCB : B.IsAdmissibleCentre C := ⟨hC.1, fun x hx => h.cosupp_eq_base ▸ (hCsub hx).1, by
      rw [h.E_eq]
      exact hCA.2.2⟩
    have hCS : ∀ H ∈ S, C ⊆ H := fun H hH x hx => (hCsub hx).2 H hH
    refine ⟨A.geoTransform C π, B.geoTransform C π, S.map (geoStrictTransform π C), r, r',
      (isLocStable_locEquiv κ).controlled h C π hπ hCA,
      InvDomainTowerAlong.isInvDomain_geoTransformAlong hA (.step .refl C π hπ) ⟨trivial, hCA⟩,
      InvDomainTowerAlong.isInvDomain_geoTransformAlong hB (.step .refl C π hπ) ⟨trivial, hCB⟩, hd, ?_,
      hP.geoTransform hA.isWellFormed hCA hπ hS hCS, hQ.geoTransform hB.isWellFormed hCB hπ hS hCS⟩
    intro H' hH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ (hS H hH) (hCS H hH)
  projection := by
    rintro hp m Y P Q ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩
    refine ⟨projectionTest A, projectionTest B, S.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·), r + 1, r' + 1,
      (isLocStable_locEquiv κ).projection hp h, projection_test_isInvDomain A hA, projection_test_isInvDomain B hB,
      hd, ?_, hP.projectionTest hA hS, hQ.projectionTest hB hS⟩
    intro H' hH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    exact HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion
      (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)) (hS H hH)
  restrict := by
    rintro m Y P Q ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩ U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) A, MarkedIdeal.pullback (Subtype.val : U → Y) B,
      S.map ((Subtype.val : U → Y) ⁻¹' ·), r, r', (isLocStable_locEquiv κ).restrict h U,
      InvDomainTowerAlong.isInvDomain_pullback_val U hA, InvDomainTowerAlong.isInvDomain_pullback_val U hB, hd, ?_,
      hP.pullback_val hA U, hQ.pullback_val hB U⟩
    intro H' hH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hS H hH) U

variable {n : ℕ} {X : CMfd.{u} n} {κ : Kinds}

/-- **P5, the `ℰ`-sum (BM08 §5 Step I.B, Lemma 3.8 for equal marks)**: if `A ≈ B` (local equivalence of kinds without
exceptional blowups, both of the native domain, the same mark; the carriers may differ) and `S` is a list of closed
submanifolds, then `P ≈ Q` for all marked ideals restricted-equivalent to `A ⊕ ℰ_S` and `B ⊕ ℰ_S`. -/
theorem locEquiv_of_excRel (hexc : κ.exc = false) {A B P Q : MarkedIdeal n X} {S : List (Set X)} {r r' : ℕ}
    (h : LocEquiv κ A B) (hA : IsInvDomain r A) (hB : IsInvDomain r' B) (hd : B.d = A.d)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hP : ExcRel P A S) (hQ : ExcRel Q B S) : LocEquiv κ P Q :=
  LocEquiv.of_isLocStable (isLocStable_excPair κ) hexc ⟨A, B, S, r, r', h, hA, hB, hd, hS, hP, hQ⟩

/-- **The `ℰ`-sums of locally equivalent marked ideals are locally equivalent.** -/
theorem locEquiv_addExc (hexc : κ.exc = false) {A B : MarkedIdeal n X} {S : List (Set X)} {r r' : ℕ}
    (h : LocEquiv κ A B) (hA : IsInvDomain r A) (hB : IsInvDomain r' B) (hd : B.d = A.d)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) : LocEquiv κ (addExc A S) (addExc B S) :=
  locEquiv_of_excRel hexc h hA hB hd hS (excRel_addExc A S) (excRel_addExc B S)

/-- **In the binary-sum form of `HironakaG11InvBMLower.lowerIdealBM`**: `(N, E, 𝔞 + ∑ 𝓘_H^d, d)` for `A` and for `B`. -/
theorem locEquiv_sumIdeal (hexc : κ.exc = false) {A B : MarkedIdeal n X} {S : List (Set X)} {r r' : ℕ}
    (h : LocEquiv κ A B) (hA : IsInvDomain r A) (hB : IsInvDomain r' B) (hd : B.d = A.d)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    LocEquiv κ (⟨A.N, A.E, RestrictedIdealExtension.sumIdeal A.ideal
        (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) A.d) S.length), A.d⟩ : MarkedIdeal n X)
      ⟨B.N, B.E, RestrictedIdealExtension.sumIdeal B.ideal
        (finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) B.d) S.length), B.d⟩ :=
  locEquiv_of_excRel hexc h hA hB hd hS (excRel_sumIdeal A hA.isWellFormed.isCoherent S)
    (excRel_sumIdeal B hB.isWellFormed.isCoherent S)

/-- **The `LocWPEquiv` form.** -/
theorem locWPEquiv_addExc {A B : MarkedIdeal n X} {S : List (Set X)} {r r' : ℕ} (h : LocWPEquiv A B)
    (hA : IsInvDomain r A) (hB : IsInvDomain r' B) (hd : B.d = A.d) (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    LocWPEquiv (addExc A S) (addExc B S) :=
  locEquiv_addExc rfl h hA hB hd hS

end Stable

end

end Hironaka.HironakaG8LocalExcSum
