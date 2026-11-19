import Hironaka.Resolution.HironakaG11InvBMPadInv
import Hironaka.Resolution.HironakaG8P1GenInv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Families of Step 1 values indexed by the length of the divisor (repair (B'), padded lower family; plan modules 10, 12)

Blueprint: `hironaka-g11-inv-bm-max-order.tex` (node `g11-inv:bm-pad-family`).  Plan: `work/hironaka-resume-20261111/G11B/
BPRIME-PLAN.md` §6d.

With padded lower divisors the Step 1 value of `𝔍` is `stepOneInvBM (R_{|𝔍.E|}) 𝔍`: the lower invariant depends on the number
of members of the divisor of `𝔍`.  Class functoriality only compares marked ideals with the SAME divisor, so it passes from the
fixed members of the family to the family:

* **`classFunctorialMaxOrder_lengthFamily`**: if every `F m` is class functorial on the marked ideals of maximal order, so is
  `𝔍 ↦ F |𝔍.E| 𝔍`; `classFunctorialFor_lengthFamily` (all marked ideals of the domain);
* `classFunctorial_padInv_lengthFamily`: the padded lower invariants `𝔍 ↦ (padInvSeq R |𝔍.E|).inv 𝔍` of a class-functorial `R`
  are class functorial.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMPadFamily

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HironakaG11InvBMPadInv
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)

noncomputable section

variable {n : ℕ} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop}

/-- **A family indexed by the length of the divisor is class functorial on the marked ideals of maximal order** if each member
is (class-equivalent marked ideals have the same divisor). -/
theorem classFunctorialMaxOrder_lengthFamily
    (F : ℕ → ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (h : ∀ m, ClassFunctorialMaxOrderFor Eqv k (F m)) :
    ClassFunctorialMaxOrderFor Eqv k (fun {X} 𝔍 {Y} T y => F 𝔍.E.length (X := X) 𝔍 (Y := Y) T y) where
  canonical_iff := by
    intro X A B hA hB hmA hmB hAB hd hE hdim hexp Y T
    have hl : B.E.length = A.E.length := by rw [hE]
    show IsCanonical A (F A.E.length A) T ↔ IsCanonical B (F B.E.length B) T
    rw [hl]
    exact (h A.E.length).canonical_iff A B hA hB hmA hmB hAB hd hE hdim hexp T
  inv_eq := by
    intro X A B hA hB hmA hmB hAB hd hE hdim hexp Y T hcan y hy
    have hl : B.E.length = A.E.length := by rw [hE]
    show F A.E.length A T y = F B.E.length B T y
    rw [hl]
    exact (h A.E.length).inv_eq A B hA hB hmA hmB hAB hd hE hdim hexp T hcan y hy

/-- **A family indexed by the length of the divisor is class functorial** (all marked ideals of the domain) if each member
is. -/
theorem classFunctorialFor_lengthFamily
    (F : ℕ → ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (h : ∀ m, ClassFunctorialFor Eqv k (F m)) :
    ClassFunctorialFor Eqv k (fun {X} 𝔍 {Y} T y => F 𝔍.E.length (X := X) 𝔍 (Y := Y) T y) where
  canonical_iff := by
    intro X A B hA hB hAB hd hE hdim hexp Y T
    have hl : B.E.length = A.E.length := by rw [hE]
    show IsCanonical A (F A.E.length A) T ↔ IsCanonical B (F B.E.length B) T
    rw [hl]
    exact (h A.E.length).canonical_iff A B hA hB hAB hd hE hdim hexp T
  inv_eq := by
    intro X A B hA hB hAB hd hE hdim hexp Y T hcan y hy
    have hl : B.E.length = A.E.length := by rw [hE]
    show F A.E.length A T y = F B.E.length B T y
    rw [hl]
    exact (h A.E.length).inv_eq A B hA hB hAB hd hE hdim hexp T hcan y hy

/-- **The padded lower invariants of a class-functorial invariant, as a family indexed by the length of the divisor, are
class functorial.** -/
theorem classFunctorial_padInv_lengthFamily (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (h : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k R.inv) :
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => (padInvSeq R 𝔍.E.length).inv (X := X) 𝔍 (Y := Y) T y) :=
  classFunctorialFor_lengthFamily (fun m {X} 𝔍 {Y} T y => (padInvSeq R m).inv (X := X) 𝔍 (Y := Y) T y)
    fun m => classFunctorial_padInv R m h

end

end Hironaka.HironakaG11InvBMPadFamily
