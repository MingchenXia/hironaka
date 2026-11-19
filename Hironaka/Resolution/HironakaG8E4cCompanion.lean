import Hironaka.Resolution.HironakaG8E4cMonomialStep
import Hironaka.Resolution.HironakaG8E4cProduct
import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaG8LocalCompanion
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Resolution.HironakaG11InvBMClass

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# E4c: the companion ideals of equivalent marked ideals are locally `s(i,ii)`-equivalent (G8C lane, run 0080; (B') P5)

Blueprint: `hironaka-g8-e4c-companion.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P5: "`A ≈ B`, same
mark, `ExpAgree` ⇒ `compAt A o T₀ ≈ compAt B o T₀` on the intersection of the masks, with `ExpAgree` (both exponents `0`)");
lane G8 `REPORT-r4.md` ("P5 E4c": the coinduction relation).  Source: Bierstone--Milman 2008, Corollary 5.3 and §5 Step II.B
(the companion ideal is determined by the equivalence class), Definition 2.4/2.5 (test transformations).

Lane G8 proved E4a/E4b: the companions `𝓞(A, o)`, `𝓞(B, o)` of `s(i,ii)`-equivalent `A`, `B` (native domain, same carrier
and mark, agreeing boundary exponents, `ord(𝓝_A) ≤ o` on the cosupport) are Włodarczyk-equivalent (`WEquiv`), also on
open subsets of the mask.  Class functoriality of the general value (G11B, BPRIME-PLAN modules 10--12) evaluates a lower
invariant on the companions and needs them in the LOCAL relation `LocWPEquiv` (blowups, products with a line, open
restrictions of every stage) with the class data of `HironakaG11InvBMClass.ClassFunctorialFor`.  This module proves it.

* `CompData o A B`: the class data (locally `s(i,ii)`-equivalent, native domain, same carrier and mark, agreeing exponents,
  positive dimension, `o ≥ 1`, `ord(𝓝) ≤ o` on both cosupports); `CompRel o P Q`: `P ≃ 𝓞(A, o)`, `Q ≃ 𝓞(B, o)` (restricted
  equivalence, coherent ideals) for class data `A`, `B`;
* `CompData.geoTransform`, `CompData.projectionTest`, `CompData.pullback_val`: the class data are stable under one test
  blowup of the companion (`HironakaG8E4cMonomialStep`), one product with a line (`HironakaG8E4cProduct`) and one open
  restriction (`HironakaG8LocalCompanion.locWPEquiv_stage_restrict`);
* **`isLocStable_compRel`**: `CompRel o` is stable under the local test actions of `s(i,ii)` (the one-step identities
  `𝓞(A, o)' ≃ 𝓞(A', o)`, `𝓞(A×ℂ, o) = 𝓞(A, o)×ℂ`, `𝓞(A, o)|_U = 𝓞(A|_U, o)`), with equal cosupports by E4a;
* **`locWPEquiv_companionOf`** (E4c): `LocWPEquiv 𝓞(A, o) 𝓞(B, o)` (by `LocEquiv.of_isLocStable`);
* `divExpAlong_eq_zero_of_frequently`, `divExpAlong_companionOf_eq_zero`, **`expAgree_companionOf`**: the boundary exponents
  of a companion vanish (its nonmonomial factor lies in no member ideal), so any two companions with the same carrier and
  boundary have agreeing exponents (both `0`);
* **`companionOf_classData`**: E4c with all the class data `ClassFunctorialFor` consumes (`LocWPEquiv`, native domain of the
  same dimension bounds, same mark, same boundary, `SameCarrierDim`, `ExpAgree` in G11B's form);
* **`companionOf_classData_stage_restrict`**, **`companionOf_classData_maskInter`**: the same for the companions formed at a
  common test stage `T₀` on an open subset of the mask `{ν_{A_{T₀}} ≤ o}`, in particular on the intersection of the masks of
  `A_{T₀}` and `B_{T₀}` (the objects `compAt A o T₀`, `compAt B o T₀` of `GeneralValue`, restricted to the common open).

Same carrier only (different carriers additionally need port P1, lane G8B).  Sorry-free.  Universe `0` (the library's log
families and G8's exponent calculus are `CMfd.{0}`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8E4cCompanion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.GermIdealOrder
  Hironaka.IdealWeightPowers Hironaka.DivisorExponentAlong
  Hironaka.MonomialPartAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealWeight
  Hironaka.RestrictedIdealExtension MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.CompanionReductionAlong (companionAlong companionAlong_N companionAlong_E)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient
  projection_test_isInvDomain)
open Hironaka.NonmonomialOrderLocal (ordGe)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform)
open Hironaka.NonmonomialOrderTail (ordMask mem_ordMask_iff)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8ProjEquiv
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open Hironaka.HironakaG8E4cMonomialStep (companion_step_facts
  restrictEquiv_nonmonomial_geoTransform restrictEquiv_companionOf_geoTransform)
open Hironaka.HironakaG8E4cProduct (companionOf_projectionTest bound_projectionTest
  expAgree_projectionTest divExpAlong_eq_zero_of_not)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-! ### Boundary exponents of a companion vanish -/

section Exponent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The exponent vanishes at a point where some germ of the (coherent) ideal does not vanish on `N ∩ H`.** -/
theorem divExpAlong_eq_zero_of_frequently {N H : Set M} {I : GermIdeal n M} (hI : I.IsCoherent) {y : M}
    {b : M → ℂ} (hb : I.mem y b) (hfreq : ∃ᶠ z in 𝓝 y, z ∈ N ∧ z ∈ H ∧ b z ≠ 0) : divExpAlong n N I H y = 0 := by
  refine divExpAlong_eq_zero_of_not fun hdiv => ?_
  obtain ⟨z, ⟨hzN, hzH, hbz⟩, hz1, hz2⟩ :=
    (hfreq.and_eventually (hdiv.and (HadamardBridge.eventually_mem_of_isCoherent hI hb))).exists
  have hc := hz1 hzN hzH
  exact hbz ((vanishesToOrderOn_one_iff hzN (GermIdeal.IsCoherent.holomorphicAt_mem hI hz2)).mp (hc.2 b hz2))

variable {X : CMfd.{u} n}

/-- **The boundary exponents of a companion ideal vanish** along its carrier: the nonmonomial part (a power of which
lies in the companion ideal) lies, at every point of `N ∩ E_i`, in the ideal of no member on `N`, so some germ of it does
not vanish identically on `N ∩ E_i` near the point. -/
theorem divExpAlong_companionOf_eq_zero (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (o : ℕ) {y : X} (hyN : y ∈ 𝔪.N) {H : Set X}
    (hH : H ∈ 𝔪.E) (hyH : y ∈ H) : divExpAlong n 𝔪.N (companionOf n 𝔪 o).ideal H y = 0 := by
  obtain ⟨h𝓝, h𝓜, -, -, hnd, -, -⟩ := NonmonomialTransformAlong.parts_hypotheses hn 𝔪 h𝔪 hne
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  obtain ⟨a, ha, hna⟩ := hnd y hyN i hyH
  have hahol : HolomorphicAt n a y := GermIdeal.IsCoherent.holomorphicAt_mem h𝓝 ha
  rw [MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem h𝔪.isSNCDivisor h𝔪.isTransverse hyN i hahol]
    at hna
  have hfreq : ∃ᶠ z in 𝓝 y, z ∈ 𝔪.N ∧ z ∈ 𝔪.E.get i ∧ a z ≠ 0 := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    refine hna ⟨hahol, hcon.mono fun z hz hzNE => ?_⟩
    by_contra h
    exact hz ⟨hzNE.1, hzNE.2, h⟩
  have hcoh : (companionOf n 𝔪 o).ideal.IsCoherent := by
    show (companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)
      (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d).ideal.IsCoherent
    rw [CompanionRebase.companionAlong_ideal]
    split_ifs
    · exact isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow h𝓝 _)
        (GermIdealPullbackCalculus.isCoherent_idealPow h𝓜 _)
    · exact h𝓝
  by_cases hod : o < 𝔪.d
  · refine divExpAlong_eq_zero_of_frequently hcoh (b := fun z => a z ^ (𝔪.d - o)) ?_
      (hfreq.mono fun z ⟨h1, h2, h3⟩ => ⟨h1, h2, pow_ne_zero _ h3⟩)
    show (companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)
      (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d).ideal.mem y fun z => a z ^ (𝔪.d - o)
    rw [CompanionRebase.companionAlong_ideal, if_pos hod]
    exact IdealOrderArithmetic.le_sumIdeal_left' (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) y _
      (MonomialPart.pow_mem_idealPow ha hahol _)
  · refine divExpAlong_eq_zero_of_frequently hcoh (b := a) ?_ hfreq
    show (companionAlong 𝔪.N 𝔪.E (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E)
      (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) o 𝔪.d).ideal.mem y a
    rw [CompanionRebase.companionAlong_ideal, if_neg hod]
    exact ha

end Exponent

/-! ### The class data and the coinduction relation -/

section Rel

/-- **The class data of the companion comparison**: locally `s(i,ii)`-equivalent, native domain, same carrier and mark,
agreeing boundary exponents, positive dimension, `o ≥ 1`, and `ord(𝓝) ≤ o` on both cosupports. -/
structure CompData {m : ℕ} {Y : CMfd.{0} m} (o : ℕ) (A B : MarkedIdeal m Y) : Prop where
  equiv : LocWPEquiv A B
  invA : ∃ k, IsInvDomain k A
  invB : ∃ k, IsInvDomain k B
  N_eq : B.N = A.N
  d_eq : B.d = A.d
  exp : ExpAgree A B
  pos : 0 < m
  one_le : 1 ≤ o
  boundA : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)
  boundB : ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1)

/-- **The coinduction relation of E4c**: `P ≃ 𝓞(A, o)` and `Q ≃ 𝓞(B, o)` (restricted equivalence, coherent ideals) for
class data `A`, `B`. -/
def CompRel (o : ℕ) {m : ℕ} {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ A B : MarkedIdeal m Y, CompData o A B ∧ RestrictEquiv P (companionOf m A o) ∧
    RestrictEquiv Q (companionOf m B o) ∧ P.ideal.IsCoherent ∧ Q.ideal.IsCoherent

variable {m : ℕ} {Y : CMfd.{0} m} {o : ℕ} {A B : MarkedIdeal m Y}

/-- The companion of a marked ideal of the native domain is coherent with a closed submanifold as carrier. -/
theorem companion_wf {k : ℕ} (hA : IsInvDomain k A) (hn : 0 < m) (ho : 1 ≤ o) :
    (companionOf m A o).IsWellFormed :=
  (InvDomainCompanion.isInvDomain_companionAlong hn hA ho).isWellFormed

/-- **The companions of class data have the same cosupport** (E4a). -/
theorem CompData.cosupp_eq (hD : CompData o A B) : (companionOf m A o).cosupp = (companionOf m B o).cosupp := by
  obtain ⟨kA, hA⟩ := hD.invA
  obtain ⟨kB, hB⟩ := hD.invB
  exact (HironakaG8CompanionEquiv.projEquiv_wEquiv_companionOf hD.equiv.projEquiv hA hB hD.N_eq hD.d_eq hD.exp
    hD.pos hD.one_le hD.boundA).cosupp_eq

/-- The companions of class data have the same boundary. -/
theorem CompData.E_eq (hD : CompData o A B) : (companionOf m B o).E = (companionOf m A o).E := by
  simp only [companionOf, companionAlong_E]
  exact hD.equiv.E_eq

/-- **The class data are stable under one test blowup of the companion.** -/
theorem CompData.geoTransform (hD : CompData o A B) {C : Set Y} {Z : CMfd.{0} m} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hC : (companionOf m A o).IsAdmissibleCentre C) :
    (companionOf m B o).IsAdmissibleCentre C ∧ CompData o (A.geoTransform C π) (B.geoTransform C π) := by
  obtain ⟨kA, hA⟩ := hD.invA
  obtain ⟨kB, hB⟩ := hD.invB
  have hCB : (companionOf m B o).IsAdmissibleCentre C :=
    (isAdmissibleCentre_congr hD.E_eq.symm hD.cosupp_eq C).mp hC
  have hCA' := (companion_step_facts hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.one_le hD.boundA hπ hC).1
  have hCB' := (companion_step_facts hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.one_le hD.boundB hπ hCB).1
  have hTA : IsGeoTestTower A (.step .refl C π hπ) := ⟨trivial, hCA'⟩
  have hTB : IsGeoTestTower B (.step .refl C π hπ) := ⟨trivial, hCB'⟩
  refine ⟨hCB, (isLocStable_locEquiv Kinds.wp).controlled hD.equiv C π hπ hCA',
    ⟨kA, InvDomainTowerAlong.isInvDomain_geoTransformAlong hA _ hTA⟩,
    ⟨kB, InvDomainTowerAlong.isInvDomain_geoTransformAlong hB _ hTB⟩, ?_, hD.d_eq, ?_, hD.pos, hD.one_le,
    (restrictEquiv_nonmonomial_geoTransform hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.one_le hD.boundA hπ hC).2,
    (restrictEquiv_nonmonomial_geoTransform hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.one_le hD.boundB hπ hCB).2⟩
  · show geoStrictTransform π C B.N = geoStrictTransform π C A.N
    rw [hD.N_eq]
  · exact expAgree_geoTransformAlong_of_ordAgree hD.equiv.projEquiv.wEquiv
      (projEquiv_towerOrdAgree hD.equiv.projEquiv hA hB hD.N_eq hD.d_eq) hA hB hD.N_eq hD.d_eq hD.exp _ hTA

/-- **The class data are stable under one product with a line.** -/
theorem CompData.projectionTest (hD : CompData o A B) : CompData o (projectionTest A) (projectionTest B) := by
  obtain ⟨kA, hA⟩ := hD.invA
  obtain ⟨kB, hB⟩ := hD.invB
  refine ⟨(isLocStable_locEquiv Kinds.wp).projection rfl hD.equiv, ⟨kA + 1, projection_test_isInvDomain A hA⟩,
    ⟨kB + 1, projection_test_isInvDomain B hB⟩, ?_, hD.d_eq,
    expAgree_projectionTest hA.isWellFormed.isCoherent hB.isWellFormed.isCoherent hA.isNonzeroAlongAt
      hB.isNonzeroAlongAt hD.N_eq hD.exp, Nat.succ_pos m, hD.one_le,
    bound_projectionTest hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.boundA,
    bound_projectionTest hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.boundB⟩
  show (Prod.fst : projectionAmbient Y → Y) ⁻¹' B.N = (Prod.fst : projectionAmbient Y → Y) ⁻¹' A.N
  rw [hD.N_eq]

/-- **The class data are stable under restriction to an open subset.** -/
theorem CompData.pullback_val (hD : CompData o A B) (U : Opens Y) :
    CompData (Y := CMfd.of (n := m) U) o (MarkedIdeal.pullback (Subtype.val : U → Y) A)
      (MarkedIdeal.pullback (Subtype.val : U → Y) B) := by
  obtain ⟨kA, hA⟩ := hD.invA
  obtain ⟨kB, hB⟩ := hD.invB
  obtain ⟨hL, hdA, hdB, hNU, hdU, hexpU⟩ :=
    HironakaG8LocalCompanion.locWPEquiv_stage_restrict hD.equiv hA hB hD.N_eq hD.d_eq hD.exp
      (.refl : BlowupTower Y Y) trivial U
  exact ⟨hL, ⟨kA, hdA⟩, ⟨kB, hdB⟩, hNU, hdU, hexpU, hD.pos, hD.one_le,
    CompanionOpen.bound_pullback_val hD.pos hA.isWellFormed hA.isNonzeroAlongAt U fun x hx _ => hD.boundA x hx,
    CompanionOpen.bound_pullback_val hD.pos hB.isWellFormed hB.isNonzeroAlongAt U fun x hx _ => hD.boundB x hx⟩

/-- One step of the relation for a single companion: a blowup. -/
theorem restrictEquiv_geoTransform_companion {P : MarkedIdeal m Y} {k : ℕ} (hA : IsInvDomain k A) (hn : 0 < m) (ho : 1 ≤ o)
    (hb : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) (hP : RestrictEquiv P (companionOf m A o))
    (hPc : P.ideal.IsCoherent) {C : Set Y} {Z : CMfd.{0} m} {π : Z → Y} (hπ : IsBlowupAlong m C π)
    (hC : (companionOf m A o).IsAdmissibleCentre C) :
    RestrictEquiv (P.geoTransform C π) (companionOf m (A.geoTransform C π) o) ∧
      (P.geoTransform C π).ideal.IsCoherent := by
  have hwf := companion_wf hA hn ho
  have hPN : IsClosed P.N := by
    rw [hP.N_eq]
    exact hwf.isClosedSubmanifold_N.1
  rw [hP.geoTransform_eq hPN hPc hwf.isCoherent hπ.contMDiff]
  exact ⟨restrictEquiv_companionOf_geoTransform hn hA.isWellFormed hA.isNonzeroAlongAt ho hb hπ hC,
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hwf.isClosedSubmanifold_N
      hwf.isCoherent hC hπ⟩

/-- One step of the relation for a single companion: a product with a line. -/
theorem restrictEquiv_projectionTest_companion {P : MarkedIdeal m Y} {k : ℕ} (hA : IsInvDomain k A) (hn : 0 < m)
    (ho : 1 ≤ o) (hP : RestrictEquiv P (companionOf m A o)) (hPc : P.ideal.IsCoherent) :
    RestrictEquiv (projectionTest P) (companionOf (m + 1) (projectionTest A) o) ∧
      (projectionTest P).ideal.IsCoherent := by
  have hwf := companion_wf hA hn ho
  rw [companionOf_projectionTest hn hA.isWellFormed hA.isNonzeroAlongAt o]
  exact ⟨HironakaG8E4cProduct.RestrictEquiv.projectionTest hP hPc hwf.isCoherent,
    GermIdealPullbackCalculus.isCoherent_pullback
      (Hironaka.ProductComplexManifold.contMDiff_fst (n := m) (m := 1) (X := Y)
        (Y := ComplexModel 1)) hPc⟩

/-- One step of the relation for a single companion: an open restriction. -/
theorem restrictEquiv_pullback_val_companion {P : MarkedIdeal m Y} {k : ℕ} (hA : IsInvDomain k A) (hn : 0 < m)
    (ho : 1 ≤ o) (hP : RestrictEquiv P (companionOf m A o)) (hPc : P.ideal.IsCoherent) (U : Opens Y) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : U → Y) P)
        (companionOf m (M := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) A) o) ∧
      (MarkedIdeal.pullback (Subtype.val : U → Y) P).ideal.IsCoherent := by
  have hwf := companion_wf hA hn ho
  rw [← CompanionRebase.pullback_val_companionOf hn hA.isWellFormed hA.isNonzeroAlongAt U o]
  exact ⟨ContactRepresentative.restrictEquiv_pullback_val U hP hPc hwf.isCoherent,
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hPc⟩

/-- **The coinduction relation of E4c is stable under the local test actions of `s(i,ii)`.** -/
theorem isLocStable_compRel (o : ℕ) : IsLocStable.{0} Kinds.wp (fun {m} {Y} P Q => CompRel o (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A, B, hD, hP, hQ, -, -⟩
    rw [hQ.E_eq, hP.E_eq]
    exact hD.E_eq
  cosupp_eq := by
    rintro m Y P Q ⟨A, B, hD, hP, hQ, -, -⟩
    rw [hP.cosupp_eq, hQ.cosupp_eq]
    exact hD.cosupp_eq
  controlled := by
    rintro m Y P Q ⟨A, B, hD, hP, hQ, hPc, hQc⟩ C Z π hπ hC
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    have hCA : (companionOf m A o).IsAdmissibleCentre C := hP.isAdmissibleCentre_iff.mp hC
    obtain ⟨hCB, hD'⟩ := hD.geoTransform hπ hCA
    obtain ⟨hP', hPc'⟩ := restrictEquiv_geoTransform_companion hA hD.pos hD.one_le hD.boundA hP hPc hπ hCA
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_geoTransform_companion hB hD.pos hD.one_le hD.boundB hQ hQc hπ hCB
    exact ⟨_, _, hD', hP', hQ', hPc', hQc'⟩
  projection := by
    rintro - m Y P Q ⟨A, B, hD, hP, hQ, hPc, hQc⟩
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    obtain ⟨hP', hPc'⟩ := restrictEquiv_projectionTest_companion hA hD.pos hD.one_le hP hPc
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_projectionTest_companion hB hD.pos hD.one_le hQ hQc
    exact ⟨_, _, hD.projectionTest, hP', hQ', hPc', hQc'⟩
  restrict := by
    rintro m Y P Q ⟨A, B, hD, hP, hQ, hPc, hQc⟩ U
    obtain ⟨kA, hA⟩ := hD.invA
    obtain ⟨kB, hB⟩ := hD.invB
    obtain ⟨hP', hPc'⟩ := restrictEquiv_pullback_val_companion hA hD.pos hD.one_le hP hPc U
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_pullback_val_companion hB hD.pos hD.one_le hQ hQc U
    exact ⟨_, _, hD.pullback_val U, hP', hQ', hPc', hQc'⟩

end Rel

/-! ### E4c -/

section Main

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X} {o : ℕ}

/-- **The bound passes to an equivalent marked ideal** (E1 at the base: equal orders of the nonmonomial parts on the common
cosupport). -/
theorem bound_of_locWPEquiv (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N)
    (hd : B.d = A.d) (h0 : ExpAgree A B) (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) :
    ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1) := by
  intro x hx hxo
  have hxA : x ∈ A.cosupp := h.cosupp_eq_base ▸ hx
  have hν := projEquiv_nmOrd_geoTransformAlong_eq h.projEquiv hA hB hN hd h0 (.refl : BlowupTower X X) trivial hxA
  refine hbound x hxA ((NonmonomialOrderLocal.mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt
    (A.cosupp_subset_N hxA) (o + 1)).mpr ?_)
  have h1 := (NonmonomialOrderLocal.mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hx) (o + 1)).mp
    hxo
  exact h1.trans_eq hν.symm

/-- The class data of `A`, `B`. -/
theorem compData_of (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N)
    (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : CompData o A B :=
  ⟨h, ⟨kA, hA⟩, ⟨kB, hB⟩, hN, hd, h0, hn, ho, hbound, bound_of_locWPEquiv h hA hB hN hd h0 hbound⟩

/-- **E4c: the companion ideals of locally `s(i,ii)`-equivalent marked ideals are locally `s(i,ii)`-equivalent** (native
domain, same carrier and mark, agreeing boundary exponents, `n > 0`, `o ≥ 1`, `ord(𝓝_A) ≤ o` on the cosupport). -/
theorem locWPEquiv_companionOf (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) : LocWPEquiv (companionOf n A o) (companionOf n B o) :=
  LocEquiv.of_isLocStable (isLocStable_compRel o) rfl
    ⟨A, B, compData_of h hA hB hN hd h0 hn ho hbound,
      RestrictEquiv.refl (companion_wf hA hn ho).isCoherent, RestrictEquiv.refl (companion_wf hB hn ho).isCoherent,
      (companion_wf hA hn ho).isCoherent, (companion_wf hB hn ho).isCoherent⟩

/-- **Any two companions with the same carrier and boundary have agreeing boundary exponents** (both `0`). -/
theorem expAgree_companionOf (hn : 0 < n) (hA : A.IsWellFormed) (hneA : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y)
    (hB : B.IsWellFormed) (hneB : ∀ y ∈ B.N, IsNonzeroAlongAt B.N B.ideal y) (hN : B.N = A.N) (hE : B.E = A.E)
    (o : ℕ) : ExpAgree (companionOf n A o) (companionOf n B o) := by
  intro H hH y hy hyH
  have hH' : H ∈ A.E := by simpa only [companionOf, companionAlong_E] using hH
  have hyN : y ∈ A.N := by
    have := (companionOf n A o).cosupp_subset_N hy
    simpa only [companionOf, companionAlong_N] using this
  show divExpAlong n (companionOf n A o).N (companionOf n A o).ideal H y =
    divExpAlong n (companionOf n B o).N (companionOf n B o).ideal H y
  simp only [companionOf, companionAlong_N]
  rw [divExpAlong_companionOf_eq_zero hn hA hneA o hyN hH' hyH,
    divExpAlong_companionOf_eq_zero hn hB hneB o (hN ▸ hyN) (hE ▸ hH') hyH]

open Hironaka.HironakaG11InvBMClass (SameCarrierDim) in
/-- **E4c with the class data of `ClassFunctorialFor`**: the companions `P = 𝓞(A, o)`, `Q = 𝓞(B, o)` are locally
`s(i,ii)`-equivalent, in the native domain (dimension bounds of `A`, `B`), with the same mark, the same boundary, the same
carrier (`SameCarrierDim`) and agreeing boundary exponents (G11B's `ExpAgree`) -- the hypotheses of
`HironakaG11InvBMClass.ClassFunctorialFor.inv_eq` for `Eqv = LocWPEquiv`. -/
theorem companionOf_classData (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) :
    LocWPEquiv (companionOf n A o) (companionOf n B o) ∧ IsInvDomain kA (companionOf n A o) ∧
      IsInvDomain kB (companionOf n B o) ∧ (companionOf n A o).d = (companionOf n B o).d ∧
      (companionOf n A o).E = (companionOf n B o).E ∧ SameCarrierDim (companionOf n A o) (companionOf n B o) ∧
      HironakaG11InvBMClass.ExpAgree (companionOf n A o) (companionOf n B o) := by
  refine ⟨locWPEquiv_companionOf h hA hB hN hd h0 hn ho hbound,
    InvDomainCompanion.isInvDomain_companionAlong hn hA ho, InvDomainCompanion.isInvDomain_companionAlong hn hB ho,
    ?_, ?_, HironakaG11InvBMClass.SameCarrierDim.of_N_eq ?_,
    expAgree_companionOf hn hA.isWellFormed hA.isNonzeroAlongAt hB.isWellFormed hB.isNonzeroAlongAt hN h.E_eq o⟩
  · simp only [companionOf, CompanionRebase.companionAlong_d, hd]
  · simp only [companionOf, companionAlong_E]
    exact h.E_eq.symm
  · simp only [companionOf, companionAlong_N]
    exact hN.symm

open Hironaka.HironakaG11InvBMClass (SameCarrierDim) in
/-- **E4c at a common test stage, on an open subset of the mask**: for `A ≈ B` (class data), a common test tower `T₀` and
an open `W ⊆ {ν_{A_{T₀}} ≤ o}` of its last stage, the companions `P = 𝓞((A_{T₀})|_W, o)` and `Q = 𝓞((B_{T₀})|_W, o)` carry
the class data of `ClassFunctorialFor` (`n > 0`, `o ≥ 1`). -/
theorem companionOf_classData_stage_restrict (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o) {Y₀ : CMfd.{0} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (W : Opens Y₀)
    (hW : (W : Set Y₀) ⊆ ordMask (geoTransformAlong A T₀) o) :
    let P := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o
    let Q := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o
    LocWPEquiv P Q ∧ IsInvDomain kA P ∧ IsInvDomain kB Q ∧ P.d = Q.d ∧ P.E = Q.E ∧ SameCarrierDim P Q ∧
      HironakaG11InvBMClass.ExpAgree P Q := by
  obtain ⟨hL, hdP, hdQ, hNPQ, hdPQ, hexp⟩ :=
    HironakaG8LocalCompanion.locWPEquiv_stage_restrict h hA hB hN hd h0 T₀ hT₀ W
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T₀ hT₀
  refine companionOf_classData (X := CMfd.of (n := n) W) hL hdP hdQ hNPQ hdPQ hexp hn ho ?_
  intro x _ hxo
  have hx : (x : Y₀) ∈ ordGe (geoTransformAlong A T₀) (o + 1) :=
    (NonmonomialOrderLocal.mem_ordGe_pullback_val_iff hn hdA.isWellFormed hdA.isNonzeroAlongAt W (o + 1) x).mp hxo
  exact (mem_ordMask_iff hn hdA.isWellFormed hdA.isNonzeroAlongAt o (x : Y₀)).mp (hW x.2) hx

open Hironaka.HironakaG11InvBMClass (SameCarrierDim) in
/-- **E4c on the intersection of the two masks** `W = {ν_{A_{T₀}} ≤ o} ∩ {ν_{B_{T₀}} ≤ o}`: the restrictions of
`compAt A o T₀` and `compAt B o T₀` to the common open carry the class data of `ClassFunctorialFor`. -/
theorem companionOf_classData_maskInter (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (hn : 0 < n) (ho : 1 ≤ o) {Y₀ : CMfd.{0} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) :
    let W : Opens Y₀ := ordMask (geoTransformAlong A T₀) o ⊓ ordMask (geoTransformAlong B T₀) o
    let P := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) o
    let Q := companionOf n (M := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) o
    LocWPEquiv P Q ∧ IsInvDomain kA P ∧ IsInvDomain kB Q ∧ P.d = Q.d ∧ P.E = Q.E ∧ SameCarrierDim P Q ∧
      HironakaG11InvBMClass.ExpAgree P Q :=
  companionOf_classData_stage_restrict h hA hB hN hd h0 hn ho T₀ hT₀ _ fun _ hx => hx.1

end Main

end

end Hironaka.HironakaG8E4cCompanion
