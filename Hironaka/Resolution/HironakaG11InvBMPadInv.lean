import Hironaka.Resolution.HironakaG11InvBMPadCalc

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The padded lower invariants (repair (B'), plan modules 8 and 12; decision G11B r7)

Blueprint: `hironaka-g11-inv-bm-max-order.tex` (node `g11-inv:bm-pad-inv`).  Plan: `work/hironaka-resume-20261111/G11B/
BPRIME-PLAN.md` §6d.

Bierstone--Milman's lower invariant is evaluated on PADDED lower ideals: the divisor of the lower ideal of `𝔍` is preceded by
one empty placeholder per member of `𝔍`, so that the lower ideals compared in property (4') of the Step 1 value have literally
equal divisors.  In Lean the padding is put into the lower invariant: for a value function `inv` and `m : ℕ`,
`padInvFn inv m L T y = inv (padE L m) T y`.  Every property of resolution invariants and their class functoriality passes
from `inv` to `padInvFn inv m` (the calculus of `HironakaG11InvBMPadCalc`), so a lower invariant `R` gives the FAMILY
`padInvSeq R : ℕ → ResolutionInvariant` with `(padInvSeq R (m + m')).inv L = (padInvSeq R m).inv (padE L m')` (the hypothesis
`hfam` of plan module 8, `padInvSeq_add`), class functorial for `LocWPEquiv` whenever `R` is (`classFunctorial_padInv`).

* `padInvFn`, `padInvFn_add`, `padInvFn_zero`;
* **`isInvValue_padInvFn`** (properties (1)--(7), (4')), **`seqLocallyFinite_padInvFn`** (property (8'));
* **`padInvSeq R m`** (`ResolutionInvariantSeq.ResolutionInvariant`, built with the structure's constructor), `padInvSeq_inv`,
  **`padInvSeq_add`** (the family identity), `padInvSeq_zero`;
* `padInv R m` (`ResolutionInvariantExt.ResolutionInvariant`, uniform (8)), `padInv_add`, `ofExt_padInv`;
* **`classFunctorialFor_padInvFn`** (any equivalence passing to paddings), **`classFunctorial_padInv`** (for `LocWPEquiv`, by
  `HironakaG11InvBMPadCalc.locWPEquiv_padE`), `BMInvariant.pad`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMPadInv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMPad Hironaka.HironakaG11InvBMPadCalc
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantSeq (IsInvValue SeqLocallyFinite)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (ClassFunctorialFor BMInvariant)

noncomputable section

variable {n : ℕ} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-! ### The padded value function -/

section Fn

/-- **The padded value function**: the value of `inv` on the marked ideal with `m` empty members in front of its divisor. -/
def padInvFn (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (m : ℕ) :
    ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ :=
  fun {_} L {_} T y => inv (padE L m) T y

variable (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

theorem padInvFn_apply (m : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    padInvFn inv m L T y = inv (padE L m) T y :=
  rfl

/-- **The family identity**: padding by `m + m'` is padding by `m'` and then by `m`. -/
theorem padInvFn_add (m m' : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    padInvFn inv (m + m') L T y = padInvFn inv m (padE L m') T y := by
  show inv (padE L (m + m')) T y = inv (padE (padE L m') m) T y
  rw [padE_padE]

theorem padInvFn_zero {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    padInvFn inv 0 L T y = inv L T y :=
  rfl

variable {inv}

/-- **Properties (1)--(7), (4') pass to the padded value function.** -/
theorem isInvValue_padInvFn (h : IsInvValue n k inv) (m : ℕ) : IsInvValue n k (padInvFn inv m) where
  admissible := by
    intro X 𝔪 hD Y T hcan W l hle
    have hle' : ∀ y ∈ (geoTransformAlong (padE 𝔪 m) T).cosupp, y ∈ W → inv (padE 𝔪 m) T y ≤ l := by
      rw [cosupp_geoTransformAlong_padE]
      exact hle
    have h1 := h.admissible (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T
      ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) W l hle'
    rw [geoTransformAlong_padE, pullback_padE, isAdmissibleCentre_padE_iff, cosupp_padE] at h1
    exact h1
  usc := by
    intro X 𝔪 hD Y T hcan
    have h1 := h.usc (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan)
    rw [cosupp_geoTransformAlong_padE] at h1
    exact h1
  decrease := by
    intro X 𝔪 hD Y Z T C π hπ hcan hC hmax z hz
    exact h.decrease (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T C π hπ ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) hC
      (by rw [cosupp_geoTransformAlong_padE]; exact hmax) z (by rw [cosupp_geoTransformAlong_padE]; exact hz)
  emptyStep := by
    intro X 𝔪 hD Y Z T C π hπ hC hcan z hz
    exact h.emptyStep (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T C π hπ hC
      ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) z (by rw [cosupp_geoTransformAlong_padE]; exact hz)
  emptyPrefix := by
    intro X 𝔪 hD Y₀ Y T₀ T₁ h₀ hcan z hz
    have h1 := h.emptyPrefix (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T₀ T₁ h₀
      ((isCanonical_padE_iff 𝔪 m _ _).mpr hcan) z (by rw [cosupp_geoTransformAlong_padE]; exact hz)
    rw [geoTransformAlong_padE] at h1
    exact h1
  restrictOpen := by
    intro X 𝔪 hD U Y T hcan p hp
    have h1 := h.restrictOpen (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) U T
      ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) p (by rw [cosupp_geoTransformAlong_padE]; exact hp)
    rw [pullback_padE] at h1
    exact h1
  towerIso := by
    intro X X' Φ 𝔪 hD Y' Y T' T χ hiso hcan p hp
    have h1 := h.towerIso Φ (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) T' T χ hiso
      ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) p (by rw [cosupp_geoTransformAlong_padE]; exact hp)
    rw [pullback_padE] at h1
    exact h1
  representative := by
    intro X 𝔪 𝔫 hD𝔪 hD𝔫 hEq Y T hcan y hy
    exact h.representative (padE 𝔪 m) (padE 𝔫 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD𝔪)
      ((isInvDomain_padE_iff 𝔫 m).mpr hD𝔫) (restrictEquiv_padE hEq m) T ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan) y
      (by rw [cosupp_geoTransformAlong_padE]; exact hy)

/-- **Property (8'), per-sequence local finiteness, passes to the padded value function.** -/
theorem seqLocallyFinite_padInvFn (h : SeqLocallyFinite n k inv) (m : ℕ) : SeqLocallyFinite n k (padInvFn inv m) := by
  intro X 𝔪 hD K hK s hcan
  exact h (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) K hK s fun i => (isCanonical_padE_iff 𝔪 m _ _).mpr (hcan i)

/-- **Class functoriality passes to the padded value function**, for every equivalence of marked ideals that passes to
paddings. -/
theorem classFunctorialFor_padInvFn {Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop} (m : ℕ)
    (hEqv : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), Eqv A B → Eqv (padE A m) (padE B m))
    (h : ClassFunctorialFor Eqv k inv) : ClassFunctorialFor Eqv k (padInvFn inv m) where
  canonical_iff := by
    intro X A B hA hB hAB hd hE hdim hexp Y T
    exact (isCanonical_padE_iff A m _ T).symm.trans
      ((h.canonical_iff (padE A m) (padE B m) ((isInvDomain_padE_iff A m).mpr hA) ((isInvDomain_padE_iff B m).mpr hB)
        (hEqv A B hAB) hd (by rw [padE_E, padE_E, hE]) (sameCarrierDim_padE hdim m) (expAgree_padE hexp m) T).trans
        (isCanonical_padE_iff B m _ T))
  inv_eq := by
    intro X A B hA hB hAB hd hE hdim hexp Y T hcan y hy
    exact h.inv_eq (padE A m) (padE B m) ((isInvDomain_padE_iff A m).mpr hA) ((isInvDomain_padE_iff B m).mpr hB)
      (hEqv A B hAB) hd (by rw [padE_E, padE_E, hE]) (sameCarrierDim_padE hdim m) (expAgree_padE hexp m) T
      ((isCanonical_padE_iff A m _ T).mpr hcan) y (by rw [cosupp_geoTransformAlong_padE]; exact hy)

end Fn

/-! ### The padded invariants -/

section Inv

/-- **The padded lower invariant** (structure `ResolutionInvariantSeq.ResolutionInvariant`, built with its constructor):
`(padInvSeq R m).inv L = R.inv (padE L m)`. -/
def padInvSeq (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ) (m : ℕ) :
    ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ :=
  ⟨padInvFn R.inv m, isInvValue_padInvFn R.isInvValue m, seqLocallyFinite_padInvFn R.seqLocallyFinite m⟩

variable (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)

theorem padInvSeq_inv (m : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (padInvSeq R m).inv L T y = R.inv (padE L m) T y :=
  rfl

/-- **The family identity of the padded invariants** (the hypothesis `hfam` of plan module 8). -/
theorem padInvSeq_add (m m' : ℕ) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (y : Y) : (padInvSeq R (m + m')).inv L T y = (padInvSeq R m).inv (padE L m') T y :=
  padInvFn_add R.inv m m' L T y

theorem padInvSeq_zero (m : ℕ) (hm : m = 0) {X : CMfd.{u} n} (L : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (y : Y) : (padInvSeq R m).inv L T y = R.inv L T y := by
  subst hm
  rfl

/-- **The padded lower invariant is class functorial for `LocWPEquiv` if `R` is.** -/
theorem classFunctorial_padInv (m : ℕ) (h : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv) :
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k (padInvSeq R m).inv :=
  classFunctorialFor_padInvFn m (fun _ _ hAB => locWPEquiv_padE hAB m) h

/-- **The padded class-functorial invariant.** -/
def _root_.Hironaka.HironakaG11InvBMClass.BMInvariant.pad
    (R : BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ) (m : ℕ) :
    BMInvariant n (fun {Y} A B => LocWPEquiv (X := Y) A B) k Λ :=
  ⟨padInvSeq R.toResolutionInvariant m, classFunctorial_padInv R.toResolutionInvariant m R.classFunctorial⟩

/-- **The padded lower invariant, uniform form of (8)** (structure `ResolutionInvariantExt.ResolutionInvariant`). -/
def padInv (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (m : ℕ) :
    ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ where
  inv := padInvFn R.inv m
  admissible := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).admissible
  usc := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).usc
  decrease := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).decrease
  emptyStep := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).emptyStep
  emptyPrefix := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).emptyPrefix
  restrictOpen := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).restrictOpen
  towerIso := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).towerIso
  representative := (isInvValue_padInvFn (ResolutionInvariantSeq.isInvValue_ext R) m).representative
  locallyFinite := by
    intro X 𝔪 hD K hK
    obtain ⟨b, hb⟩ := R.locallyFinite (padE 𝔪 m) ((isInvDomain_padE_iff 𝔪 m).mpr hD) K hK
    exact ⟨b, fun T hcan => hb T ((isCanonical_padE_iff 𝔪 m _ T).mpr hcan)⟩

/-- The family identity, uniform form. -/
theorem padInv_add (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (m m' : ℕ) {X : CMfd.{u} n}
    (L : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (padInv R (m + m')).inv L T y = (padInv R m).inv (padE L m') T y :=
  padInvFn_add R.inv m m' L T y

/-- The two padded invariants agree. -/
theorem ofExt_padInv (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (m : ℕ) :
    ResolutionInvariantSeq.ResolutionInvariant.ofExt (padInv R m) =
      padInvSeq (ResolutionInvariantSeq.ResolutionInvariant.ofExt R) m :=
  rfl

end Inv

end

end Hironaka.HironakaG11InvBMPadInv
