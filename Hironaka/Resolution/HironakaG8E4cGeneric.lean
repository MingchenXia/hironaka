import Hironaka.Resolution.HironakaG8E4cCompanion

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# E4c for an abstract class relation: the coinduction principle of the companion comparison (G8C lane, run 0080; (B') P5)

Blueprint: `hironaka-g8-e4c-generic.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §0 D2 (the carriers of
class-equivalent marked ideals may differ), §2 P1, P5, P6.

`HironakaG8E4cCompanion` proves E4c for the SAME carrier.  Its coinduction uses the class data `CompData` only through six
facts: the domain and the bound `ord(𝓝) ≤ o` for both ideals, equal boundaries, equal cosupports of the companions, and
stability of the data under one test blowup of the companion, one product with a line and one open restriction.  This
module isolates them:

* `CompClass o D`: the six facts for a family `D` of relations between marked ideals (all dimensions, universe `0`);
* `CompRelOf D o P Q`: `P ≃ 𝓞(A, o)`, `Q ≃ 𝓞(B, o)` (restricted equivalence, coherent ideals) with `D A B`;
* **`isLocStable_compRelOf`**, **`locWPEquiv_companionOf_of`**: for `D` with `CompClass o D`, `D A B` gives
  `LocWPEquiv 𝓞(A, o) 𝓞(B, o)`;
* `compClass_compData`: the same-carrier class data are an instance (so `HironakaG8E4cCompanion.locWPEquiv_companionOf`
  is the special case `D = CompData o`);
* `expAgree_companionOf_of_mem`: the exponent agreement of two companions only needs the second carrier to contain the
  first cosupport (both exponents are `0`), so it holds for different carriers too.

For carriers that differ (`SameCarrierDim`, D2 of the plan) E4c follows once a family `D` with `CompClass o D` is
available; the missing inputs are then exactly: equal orders of the nonmonomial parts on the common cosupport (E1 across
carriers, from lane G8B's P1 and agreeing exponents) and agreeing exponents after one blowup (P6).  Sorry-free.
Universe `0`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8E4cGeneric

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.DivisorExponentAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.CompanionRebase (companionOf)
open Hironaka.CompanionReductionAlong (companionAlong companionAlong_N companionAlong_E)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest)
open Hironaka.NonmonomialOrderLocal (ordGe)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable
open Hironaka.HironakaG8E4cCompanion (CompData restrictEquiv_geoTransform_companion
  restrictEquiv_projectionTest_companion restrictEquiv_pullback_val_companion companion_wf divExpAlong_companionOf_eq_zero)

noncomputable section

/-- **The facts of a class relation that the companion comparison uses**: for `D A B`, both ideals lie in the domain with
`ord(𝓝) ≤ o` on their cosupports (`n > 0`, `o ≥ 1`), the boundaries agree, the companions have equal cosupports, and `D`
is stable under one test blowup of the companion of the first ideal, one product with a line and one open restriction. -/
structure CompClass (o : ℕ) (D : ∀ {m : ℕ} {Y : CMfd.{0} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop) : Prop where
  /-- the domain, positivity and the bounds -/
  data : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B →
    (∃ k, IsInvDomain k A) ∧ (∃ k, IsInvDomain k B) ∧ 0 < m ∧ 1 ≤ o ∧
      (∀ x ∈ A.cosupp, x ∉ ordGe A (o + 1)) ∧ ∀ x ∈ B.cosupp, x ∉ ordGe B (o + 1)
  /-- the same boundary -/
  E_eq : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B → B.E = A.E
  /-- the companions have the same cosupport -/
  cosupp_eq : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B →
    (companionOf m A o).cosupp = (companionOf m B o).cosupp
  /-- stable under one test blowup of the companion -/
  geoTransform : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B → ∀ (C : Set Y) {Z : CMfd.{0} m}
    (π : Z → Y), IsBlowupAlong m C π → (companionOf m A o).IsAdmissibleCentre C →
      D (A.geoTransform C π) (B.geoTransform C π)
  /-- stable under one product with a line -/
  projectionTest : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B → D (projectionTest A) (projectionTest B)
  /-- stable under restriction to an open subset -/
  restrict : ∀ {m : ℕ} {Y : CMfd.{0} m} {A B : MarkedIdeal m Y}, D A B → ∀ U : Opens Y,
    D (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) A)
      (MarkedIdeal.pullback (Subtype.val : U → Y) B)

/-- **The coinduction relation for a class relation `D`**: `P ≃ 𝓞(A, o)`, `Q ≃ 𝓞(B, o)` with `D A B`. -/
def CompRelOf (D : ∀ {m : ℕ} {Y : CMfd.{0} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop) (o : ℕ) {m : ℕ}
    {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ A B : MarkedIdeal m Y, D A B ∧ RestrictEquiv P (companionOf m A o) ∧
    RestrictEquiv Q (companionOf m B o) ∧ P.ideal.IsCoherent ∧ Q.ideal.IsCoherent

variable {o : ℕ} {D : ∀ {m : ℕ} {Y : CMfd.{0} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop}

/-- **The coinduction relation of a class relation with the six facts is stable under the local test actions of
`s(i,ii)`.** -/
theorem isLocStable_compRelOf (hD : CompClass o D) :
    IsLocStable.{0} Kinds.wp (fun {m} {Y} P Q => CompRelOf D o (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A, B, hAB, hP, hQ, -, -⟩
    rw [hQ.E_eq, hP.E_eq]
    simp only [companionOf, companionAlong_E]
    exact hD.E_eq hAB
  cosupp_eq := by
    rintro m Y P Q ⟨A, B, hAB, hP, hQ, -, -⟩
    rw [hP.cosupp_eq, hQ.cosupp_eq]
    exact hD.cosupp_eq hAB
  controlled := by
    rintro m Y P Q ⟨A, B, hAB, hP, hQ, hPc, hQc⟩ C Z π hπ hC
    obtain ⟨⟨kA, hA⟩, ⟨kB, hB⟩, hn, ho, hbA, hbB⟩ := hD.data hAB
    have hCA : (companionOf m A o).IsAdmissibleCentre C := hP.isAdmissibleCentre_iff.mp hC
    have hEc : (companionOf m A o).E = (companionOf m B o).E := by
      simp only [companionOf, companionAlong_E]
      exact (hD.E_eq hAB).symm
    have hCB : (companionOf m B o).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hEc (hD.cosupp_eq hAB) C).mp hCA
    obtain ⟨hP', hPc'⟩ := restrictEquiv_geoTransform_companion hA hn ho hbA hP hPc hπ hCA
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_geoTransform_companion hB hn ho hbB hQ hQc hπ hCB
    exact ⟨_, _, hD.geoTransform hAB C π hπ hCA, hP', hQ', hPc', hQc'⟩
  projection := by
    rintro - m Y P Q ⟨A, B, hAB, hP, hQ, hPc, hQc⟩
    obtain ⟨⟨kA, hA⟩, ⟨kB, hB⟩, hn, ho, -, -⟩ := hD.data hAB
    obtain ⟨hP', hPc'⟩ := restrictEquiv_projectionTest_companion hA hn ho hP hPc
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_projectionTest_companion hB hn ho hQ hQc
    exact ⟨_, _, hD.projectionTest hAB, hP', hQ', hPc', hQc'⟩
  restrict := by
    rintro m Y P Q ⟨A, B, hAB, hP, hQ, hPc, hQc⟩ U
    obtain ⟨⟨kA, hA⟩, ⟨kB, hB⟩, hn, ho, -, -⟩ := hD.data hAB
    obtain ⟨hP', hPc'⟩ := restrictEquiv_pullback_val_companion hA hn ho hP hPc U
    obtain ⟨hQ', hQc'⟩ := restrictEquiv_pullback_val_companion hB hn ho hQ hQc U
    exact ⟨_, _, hD.restrict hAB U, hP', hQ', hPc', hQc'⟩

/-- **E4c for a class relation**: `D A B` with the six facts gives `LocWPEquiv 𝓞(A, o) 𝓞(B, o)`. -/
theorem locWPEquiv_companionOf_of (hD : CompClass o D) {n : ℕ} {X : CMfd.{0} n} {A B : MarkedIdeal n X}
    (h : D A B) : LocWPEquiv (companionOf n A o) (companionOf n B o) := by
  obtain ⟨⟨kA, hA⟩, ⟨kB, hB⟩, hn, ho, -, -⟩ := hD.data h
  exact LocEquiv.of_isLocStable (isLocStable_compRelOf hD) rfl
    ⟨A, B, h, RestrictEquiv.refl (companion_wf hA hn ho).isCoherent, RestrictEquiv.refl (companion_wf hB hn ho).isCoherent,
      (companion_wf hA hn ho).isCoherent, (companion_wf hB hn ho).isCoherent⟩

/-- **The same-carrier class data are an instance.** -/
theorem compClass_compData (o : ℕ) : CompClass o (fun {m} {Y} A B => CompData (m := m) (Y := Y) o A B) where
  data hD := ⟨hD.invA, hD.invB, hD.pos, hD.one_le, hD.boundA, hD.boundB⟩
  E_eq hD := hD.equiv.E_eq
  cosupp_eq hD := hD.cosupp_eq
  geoTransform hD _ _ _ hπ hC := (hD.geoTransform hπ hC).2
  projectionTest hD := hD.projectionTest
  restrict hD U := hD.pullback_val U

/-- **The exponents of two companions agree as soon as the second carrier contains the first cosupport** (same boundary;
both exponents are `0`), in particular for different carriers with equal cosupports. -/
theorem expAgree_companionOf_of_mem {n : ℕ} {X : CMfd.{0} n} {A B : MarkedIdeal n X} (hn : 0 < n)
    (hA : A.IsWellFormed) (hneA : ∀ y ∈ A.N, IsNonzeroAlongAt A.N A.ideal y) (hB : B.IsWellFormed)
    (hneB : ∀ y ∈ B.N, IsNonzeroAlongAt B.N B.ideal y) (hNB : ∀ y ∈ (companionOf n A o).cosupp, y ∈ B.N)
    (hE : B.E = A.E) : ExpAgree (companionOf n A o) (companionOf n B o) := by
  intro H hH y hy hyH
  have hH' : H ∈ A.E := by simpa only [companionOf, companionAlong_E] using hH
  have hyN : y ∈ A.N := by
    have := (companionOf n A o).cosupp_subset_N hy
    simpa only [companionOf, companionAlong_N] using this
  show divExpAlong n (companionOf n A o).N (companionOf n A o).ideal H y =
    divExpAlong n (companionOf n B o).N (companionOf n B o).ideal H y
  simp only [companionOf, companionAlong_N]
  rw [divExpAlong_companionOf_eq_zero hn hA hneA o hyN hH' hyH,
    divExpAlong_companionOf_eq_zero hn hB hneB o (hNB y hy) (hE ▸ hH') hyH]

end

end Hironaka.HironakaG8E4cGeneric
