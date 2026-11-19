import Hironaka.Resolution.HironakaG11InvBMClass

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Empty members of the divisor (repair (B'), plan module 8, property (4'))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d.

Bierstone--Milman's lower ideals carry as divisor the members BORN along the tower from the base of the marked ideal.  Along
a tower `P T₁` whose prefix `P` has only empty centres, the lower ideal of `𝔍` formed at the stage `P H₀` carries the `|P|`
(empty) members born along `P` in front of those born along `H₀`, while the lower ideal of `𝔍_P` formed at `H₀` carries only the
latter.  Property (4') of the Step 1 value (`MaxOrderValue.IsMaxOrderValue.emptyPrefix`) therefore needs the lower invariant
not to see EMPTY members of the divisor.  This is not a consequence of properties (1)--(7), (4') of a resolution invariant
(those never compare marked ideals on one space with divisors of different lengths; inserting an isomorphism at the FRONT of a
tower is not among them), but it holds for the dimension-0 invariant and is the natural invariance of Bierstone--Milman's
invariant (which reads the divisor only through the members passing through a point and their years of birth).

* `SameUpToEmptyMembers A B`: same carrier, ideal and mark, and the same NONEMPTY members of the divisor in the same order;
* **`EmptyMemberIndep k inv`**: two such marked ideals of the domain have the same canonical segments and the same values on
  the cosupport along them (a property of a value function, like `HironakaG11InvBMClass.ClassFunctorialFor`);
* `SameUpToEmptyMembers.refl/symm/trans`, `emptyMemberIndep_ofDimZero` (the base of the induction).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMEmptyMember

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HironakaG11InvBMClass (isCanonical_iff_isEmptyTower_of_dimZero)

noncomputable section

variable {n : ℕ}

section Defs

variable {X : CMfd.{u} n}

open Classical in
/-- **Marked ideals that differ only by empty members of the divisor**: the same carrier, ideal and mark, and the same
nonempty members of the divisor in the same order. -/
def SameUpToEmptyMembers (A B : MarkedIdeal n X) : Prop :=
  A.N = B.N ∧ A.ideal = B.ideal ∧ A.d = B.d ∧
    A.E.filter (fun H => decide H.Nonempty) = B.E.filter (fun H => decide H.Nonempty)

theorem SameUpToEmptyMembers.refl (A : MarkedIdeal n X) : SameUpToEmptyMembers A A :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem SameUpToEmptyMembers.symm {A B : MarkedIdeal n X} (h : SameUpToEmptyMembers A B) : SameUpToEmptyMembers B A :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem SameUpToEmptyMembers.trans {A B C : MarkedIdeal n X} (h₁ : SameUpToEmptyMembers A B)
    (h₂ : SameUpToEmptyMembers B C) : SameUpToEmptyMembers A C :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

/-- Marked ideals with the same divisor differ by no member. -/
theorem sameUpToEmptyMembers_of_E_eq {A B : MarkedIdeal n X} (hN : A.N = B.N) (hI : A.ideal = B.ideal)
    (hd : A.d = B.d) (hE : A.E = B.E) : SameUpToEmptyMembers A B :=
  ⟨hN, hI, hd, by rw [hE]⟩

end Defs

section Indep

variable {Λ : Type v} [LinearOrder Λ]

/-- **Values that do not see empty members of the divisor** (a property of a value function in dimension `≤ k`): two
marked ideals of the domain differing only by empty members of the divisor have the same canonical segments and, along them,
the same values on the cosupport. -/
def EmptyMemberIndep (k : ℕ) (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    Prop :=
  ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B → SameUpToEmptyMembers A B →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A (inv A) T →
      IsCanonical B (inv B) T ∧ ∀ y ∈ (geoTransformAlong A T).cosupp, inv A T y = inv B T y

/-- **The base of the induction**: in dimension `0` every constant value function does not see empty members (canonical
segments are the towers with empty centres, `HironakaG11InvBMClass.isCanonical_iff_isEmptyTower_of_dimZero`). -/
theorem emptyMemberIndep_ofDimZero (l₀ : Λ) :
    EmptyMemberIndep 0 (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero.{u, v} (n := n) Λ l₀).inv := by
  intro X A B hA hB _ Y T hcan
  exact ⟨(isCanonical_iff_isEmptyTower_of_dimZero hB _ T).mpr ((isCanonical_iff_isEmptyTower_of_dimZero hA _ T).mp hcan),
    fun _ _ => rfl⟩

end Indep

end

end Hironaka.HironakaG11InvBMEmptyMember
