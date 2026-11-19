import Hironaka.Resolution.HironakaG8LocalHistory
import Hironaka.Resolution.HironakaG8CompanionEquiv
import Hironaka.Invariant.MonomialInvariantFunctorialAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Class data at restricted stages; companions on mask intersections (G8 lane, run 0080, round 3; (B') ports P0/P5, E4b)

Blueprint: `hironaka-g8-resume-local-companion.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P5:
"`compAt A o T₀ ≈ compAt B o T₀` on the intersection of the masks").

The (B') induction compares two marked ideals `A ≈ B` (same mark, same boundary, same carrier here, agreeing boundary
exponents) through objects formed on OPEN subsets of later stages: the companion ideal of the general value is formed at
the stage `T₀` on the mask `{ν ≤ o}` (`GeneralValue.compAt`), and the masks of `A` and `B` may differ off the cosupport.
With the local relation `LocWPEquiv` (`HironakaG8LocalHistory`) everything restricts:

* `expAgree_pullback_val`: agreement of boundary exponents restricts to open subsets (exponents along `N` are local,
  `MonomialInvariantFunctorialAlong.divExpAlong_pullback`);
* **`locWPEquiv_stage_restrict`**: for `A ≈ B` (`LocWPEquiv`, native domain, same carrier, same mark, `ExpAgree`), a common
  test tower `T₀` and an open `W` of its last stage, the restrictions `P = (A_{T₀})|_W`, `Q = (B_{T₀})|_W` are again
  `LocWPEquiv`, in the native domain, with the same carrier and mark and agreeing exponents — the full class data, so
  every G8 result (E1–E3 of `HironakaG8ProjEquiv`) applies to `P`, `Q`;
* **`locWPEquiv_nmOrd_stage_restrict_eq`** (E1 at restricted stages): the orders of the nonmonomial parts agree along every
  common test tower of `P`;
* **`locWPEquiv_wEquiv_companionOf_stage_restrict`** (E4b): if `W` lies in the mask `{ν_{A_{T₀}} ≤ o}` (e.g. the
  intersection of the two masks), the companions `𝓞(P, o)`, `𝓞(Q, o)` are Włodarczyk-equivalent on `W`;
  `locWPEquiv_wEquiv_companionOf_maskInter` for `W = ordMask A_{T₀} o ⊓ ordMask B_{T₀} o`.

Not here: the companions in the full relation `LocWPEquiv` (products with a line and restrictions for the companion,
E4c), and the comparison of `compAt` with the companion on `W` (a nested-open biholomorphism; field (5) of the lower value).
Sorry-free.  Universe `0`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LocalCompanion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.NonmonomialOrderLocal (nmOrd ordGe)
open Hironaka.NonmonomialOrderTail (ordMask mem_ordMask_iff)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree carrier_geoTransformAlong_eq)
open Hironaka.HironakaG8ProjEquiv
open Hironaka.HironakaG8CompanionEquiv (projEquiv_wEquiv_companionOf)
open Hironaka.HironakaG8LocalHistory

noncomputable section

variable {n : ℕ}

/-! ### Exponents restrict -/

section Restrict

variable {X : CMfd.{0} n}

/-- **Agreement of boundary exponents restricts to open subsets.** -/
theorem expAgree_pullback_val {P Q : MarkedIdeal n X} (hP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x)
    (hQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x) (h : ExpAgree P Q) (U : Opens X) :
    ExpAgree (Y := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) P)
      (MarkedIdeal.pullback (Subtype.val : U → X) Q) := by
  intro H' hH' y hy hyH'
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
  have hcosP : ∀ e, cosupport n ((Subtype.val : U → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) P.ideal) e = (Subtype.val : U → X) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n X) hP U
  have hcosQ : ∀ e, cosupport n ((Subtype.val : U → X) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) Q.ideal) e = (Subtype.val : U → X) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n X) hQ U
  have hmap : Filter.map (Subtype.val : U → X) (𝓝 y) = 𝓝 (y : X) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set X)) y.2 (U.isOpen.mem_nhds y.2)
  have hy' : (y : X) ∈ P.cosupp := by
    have h1 := MarkedIdealRestrictOpen.cosupp_pullback_val P hP U
    have h2 : y ∈ (MarkedIdeal.pullback (Subtype.val : U → X) P).cosupp := hy
    rw [h1] at h2
    exact h2
  show divExpAlong n ((Subtype.val : U → X) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) P.ideal)
      ((Subtype.val : U → X) ⁻¹' H) y =
    divExpAlong n ((Subtype.val : U → X) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) Q.ideal)
      ((Subtype.val : U → X) ⁻¹' H) y
  rw [MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosP hmap H,
    MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosQ hmap H]
  exact h H hH y hy' hyH'

end Restrict

/-! ### Class data at restricted stages -/

section Stage

variable {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **The class data restrict to every open subset of every common test stage**: `P = (A_{T₀})|_W` and
`Q = (B_{T₀})|_W` are `LocWPEquiv`, in the native domain, with the same carrier, the same mark and agreeing exponents. -/
theorem locWPEquiv_stage_restrict (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower A T₀) (W : Opens Y₀) :
    LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀))
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) ∧
      IsInvDomain kA (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) ∧
      IsInvDomain kB (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) ∧
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)).N =
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)).N ∧
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)).d =
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)).d ∧
      ExpAgree (Y := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀))
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) := by
  have hP := h.projEquiv
  have hTB : IsGeoTestTower B T₀ := (hP.wEquiv.2 T₀).1.mp hT₀
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T₀ hT₀
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T₀ hTB
  have hexp : ExpAgree (geoTransformAlong A T₀) (geoTransformAlong B T₀) :=
    expAgree_geoTransformAlong_of_ordAgree hP.wEquiv (projEquiv_towerOrdAgree hP hA hB hN hd) hA hB hN hd h0 T₀ hT₀
  refine ⟨(h.geoTransformAlong T₀ hT₀).restrict W, InvDomainTowerAlong.isInvDomain_pullback_val W hdA,
    InvDomainTowerAlong.isInvDomain_pullback_val W hdB, ?_, ?_, ?_⟩
  · show (Subtype.val : W → Y₀) ⁻¹' (geoTransformAlong B T₀).N = (Subtype.val : W → Y₀) ⁻¹' (geoTransformAlong A T₀).N
    rw [carrier_geoTransformAlong_eq hN T₀]
  · show (geoTransformAlong B T₀).d = (geoTransformAlong A T₀).d
    rw [d_geoTransformAlong, d_geoTransformAlong, hd]
  · exact expAgree_pullback_val
      (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hdA.isWellFormed.isCoherent hg)
      (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hdB.isWellFormed.isCoherent hg) hexp W

/-- **E1 at restricted stages**: along every common test tower `T₁` of `P = (A_{T₀})|_W`, the orders of the nonmonomial
parts of `P_{T₁}` and `Q_{T₁}` agree on the cosupport. -/
theorem locWPEquiv_nmOrd_stage_restrict_eq (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower A T₀) (W : Opens Y₀) {Y : CMfd.{0} n} (T₁ : BlowupTower (CMfd.of (n := n) W) Y)
    (hT₁ : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) T₁) {y : Y}
    (hy : y ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) T₁).cosupp) :
    nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) T₁) y =
      nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) T₁) y := by
  obtain ⟨hL, hdP, hdQ, hNPQ, hdPQ, hexp⟩ := locWPEquiv_stage_restrict h hA hB hN hd h0 T₀ hT₀ W
  exact projEquiv_nmOrd_geoTransformAlong_eq hL.projEquiv hdP hdQ hNPQ hdPQ hexp T₁ hT₁ hy

/-- **E4b: companions on an open subset of the mask.**  If `W` lies in the mask `{ν_{A_{T₀}} ≤ o}`, the companion ideals
of `(A_{T₀})|_W` and `(B_{T₀})|_W` are Włodarczyk-equivalent. -/
theorem locWPEquiv_wEquiv_companionOf_stage_restrict (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) {o : ℕ} (ho : 1 ≤ o)
    {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (W : Opens Y₀)
    (hW : (W : Set Y₀) ⊆ ordMask (geoTransformAlong A T₀) o) :
    WEquiv (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o)
      (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o) := by
  obtain ⟨hL, hdP, hdQ, hNPQ, hdPQ, hexp⟩ := locWPEquiv_stage_restrict h hA hB hN hd h0 T₀ hT₀ W
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T₀ hT₀
  refine projEquiv_wEquiv_companionOf hL.projEquiv hdP hdQ hNPQ hdPQ hexp hn ho ?_
  intro x _ hxo
  have hx : (x : Y₀) ∈ ordGe (geoTransformAlong A T₀) (o + 1) :=
    (NonmonomialOrderLocal.mem_ordGe_pullback_val_iff hn hdA.isWellFormed hdA.isNonzeroAlongAt W (o + 1) x).mp hxo
  exact (mem_ordMask_iff hn hdA.isWellFormed hdA.isNonzeroAlongAt o (x : Y₀)).mp (hW x.2) hx

/-- **E4b on the intersection of the two masks.** -/
theorem locWPEquiv_wEquiv_companionOf_maskInter (h : LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) {o : ℕ} (ho : 1 ≤ o)
    {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) :
    let W : Opens Y₀ := ordMask (geoTransformAlong A T₀) o ⊓ ordMask (geoTransformAlong B T₀) o
    WEquiv (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o)
      (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o) :=
  locWPEquiv_wEquiv_companionOf_stage_restrict h hA hB hN hd h0 hn ho T₀ hT₀ _ fun _ hx => hx.1

end Stage

end

end Hironaka.HironakaG8LocalCompanion
