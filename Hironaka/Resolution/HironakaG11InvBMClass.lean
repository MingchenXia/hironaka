import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Class functoriality of resolution invariants: the induction predicate of repair (B')

Blueprint: `hironaka-g11-inv-bm-class.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 1, design
decisions D1, D2).  Human decision on I-1304: repair (B') -- a Bierstone--Milman lower family on the generic Step 1
skeleton, with class functoriality carried through the induction on the dimension (Bierstone--Milman 2008, Theorem 7.1(4);
§5 Step I.A: "the coefficient ideals in overlapping charts are equivalent ... by functoriality in dimension `n − 1`").

A value function `inv` (on the marked ideals of the domain in dimension `≤ k`) is **class functorial** for an equivalence
`Eqv` of marked ideals if two marked ideals `A`, `B` on the same manifold that are `Eqv`-equivalent, have the same mark, the
same divisor, carriers of the same local dimension at the points of the cosupport (`SameCarrierDim`; the carriers may
differ, as the maximal-contact hypersurfaces of two equivalent marked ideals do) and the same boundary exponents on the
cosupport (`ExpAgree`) have the same canonical segments and, along them, the same values on the cosupport.

* `ExpAgree` (universe-polymorphic form of lane G8's `HironakaG8MixedBoundaryExponents.ExpAgree`, which is the same
  predicate in universe `0`: `expAgree_iff_g8`), `ExpAgree.refl`, `expAgree_of_nil`;
* `SameCarrierDim`, `SameCarrierDim.refl`, `SameCarrierDim.of_N_eq`;
* **`ClassFunctorialFor Eqv k inv`** (fields `canonical_iff`, `inv_eq`), `ClassFunctorialFor.mono` (a finer equivalence);
* **`BMInvariant Eqv k Λ`**: a resolution invariant (`ResolutionInvariantSeq.ResolutionInvariant`) with class functoriality;
* the base case: `isCanonical_iff_isEmptyTower_of_dimZero` (in dimension `0` the canonical segments of every value function
  are the towers with empty centres), `classFunctorialFor_ofDimZero`, **`BMInvariant.ofDimZero`**.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMClass

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting_eq_zero_of_dimLE_zero
  cosupp_geoTransformAlong_eq_empty_of_dimLE_zero)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Boundary exponents and carrier dimensions -/

section Data

variable {X : CMfd.{u} n}

/-- **Agreement of the boundary exponents on the cosupport**: at every point of the cosupport of `P` on a member `H` of the
divisor of `P`, the exponents of `P` and `Q` along `H` (on their carriers) agree. -/
def ExpAgree (P Q : MarkedIdeal n X) : Prop :=
  ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H → divExpAlong n P.N P.ideal H y = divExpAlong n Q.N Q.ideal H y

theorem ExpAgree.refl (P : MarkedIdeal n X) : ExpAgree P P := fun _ _ _ _ _ => rfl

/-- With empty divisor, exponent agreement is vacuous. -/
theorem expAgree_of_nil {P Q : MarkedIdeal n X} (hE : P.E = []) : ExpAgree P Q := by
  intro H hH
  rw [hE] at hH
  exact absurd hH List.not_mem_nil

/-- In universe `0` this is lane G8's predicate. -/
theorem expAgree_iff_g8 {X : CMfd.{0} n} (P Q : MarkedIdeal n X) :
    ExpAgree P Q ↔ HironakaG8MixedBoundaryExponents.ExpAgree P Q :=
  Iff.rfl

/-- **Carriers of the same local dimension on the cosupport.** -/
def SameCarrierDim (A B : MarkedIdeal n X) : Prop :=
  ∀ x ∈ A.cosupp, ∀ j : ℕ, RegularAtDim (n := n) A.N x j ↔ RegularAtDim (n := n) B.N x j

theorem SameCarrierDim.refl (A : MarkedIdeal n X) : SameCarrierDim A A := fun _ _ _ => Iff.rfl

theorem SameCarrierDim.of_N_eq {A B : MarkedIdeal n X} (h : A.N = B.N) : SameCarrierDim A B := by
  intro x _ j
  rw [h]

end Data

/-! ### Class functoriality -/

section ClassFunctorial

variable {Λ : Type v} [LinearOrder Λ]

/-- **Class functoriality** of a value function `inv` in dimension `≤ k` for an equivalence `Eqv` of marked ideals: two
`Eqv`-equivalent marked ideals of the domain with the same mark, the same divisor, carriers of the same dimension and the
same boundary exponents have the same canonical segments and, along them, the same values on the cosupport. -/
structure ClassFunctorialFor (Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop) (k : ℕ)
    (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop where
  /-- The same canonical segments. -/
  canonical_iff : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B → Eqv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A (inv A) T ↔ IsCanonical B (inv B) T
  /-- The same values along them, on the cosupport. -/
  inv_eq : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B → Eqv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A (inv A) T →
      ∀ y ∈ (geoTransformAlong A T).cosupp, inv A T y = inv B T y

/-- **A finer equivalence keeps class functoriality.** -/
theorem ClassFunctorialFor.mono {Eqv Eqv' : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop} {k : ℕ}
    {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (h : ClassFunctorialFor Eqv k inv) (hle : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), Eqv' A B → Eqv A B) :
    ClassFunctorialFor Eqv' k inv where
  canonical_iff A B hA hB hAB := h.canonical_iff A B hA hB (hle A B hAB)
  inv_eq A B hA hB hAB := h.inv_eq A B hA hB (hle A B hAB)

variable (n) in
/-- **A class-functorial resolution invariant** in dimension `≤ k`: a resolution invariant in the sense of
`ResolutionInvariantSeq` whose value function is class functorial for `Eqv`. -/
structure BMInvariant (Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop) (k : ℕ) (Λ : Type v)
    [LinearOrder Λ] where
  /-- The resolution invariant. -/
  toResolutionInvariant : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ
  /-- Its class functoriality. -/
  classFunctorial : ClassFunctorialFor Eqv k toResolutionInvariant.inv

end ClassFunctorial

/-! ### Dimension zero -/

section DimZero

variable {Λ : Type v} [LinearOrder Λ]

/-- **In dimension `0` the canonical segments of every value function are the towers with empty centres** (the cosupports
along test towers are empty, `ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero`). -/
theorem isCanonical_iff_isEmptyTower_of_dimZero {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (h : IsInvDomain 0 𝔪)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T ↔ IsEmptyTower T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      have ih := isCanonical_iff_isEmptyTower_of_dimZero h inv T
      constructor
      · rintro ⟨hT, hC⟩
        refine ⟨ih.mp hT, ?_⟩
        rcases hC with hC | hC
        · exact hC
        · have hempty := cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T
            (countCentresMeeting_eq_zero_of_dimLE_zero h inv ∅ T hT).1
          rw [hC, hempty]
          exact eq_empty_iff_forall_notMem.mpr fun y hy => hy.1
      · rintro ⟨hT, hC⟩
        exact ⟨ih.mpr hT, Or.inl hC⟩

/-- **The constant invariant of dimension `0` is class functorial** for every equivalence. -/
theorem classFunctorialFor_ofDimZero (Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop)
    (l₀ : Λ) : ClassFunctorialFor Eqv 0 (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero.{u, v} (n := n) Λ l₀).inv where
  canonical_iff := by
    intro _ A B hA hB _ _ _ _ _ _ T
    exact (isCanonical_iff_isEmptyTower_of_dimZero hA _ T).trans
      (isCanonical_iff_isEmptyTower_of_dimZero hB _ T).symm
  inv_eq := by
    intros
    rfl

/-- **The base case of the class-functorial induction**: the constant invariant of dimension `0`. -/
def BMInvariant.ofDimZero (Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop) (l₀ : Λ) :
    BMInvariant n Eqv 0 Λ :=
  ⟨ResolutionInvariantSeq.ResolutionInvariant.ofDimZero Λ l₀, classFunctorialFor_ofDimZero Eqv l₀⟩

end DimZero

end

end Hironaka.HironakaG11InvBMClass
