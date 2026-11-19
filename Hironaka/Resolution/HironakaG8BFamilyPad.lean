import Hironaka.Resolution.HironakaG11InvBMPad
import Hironaka.Invariant.MonomialInvariantEmptyMember
import Hironaka.Resolution.HironakaG8LocalStable

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Padded divisors: empty members in front are harmless (repair (B'), padded lower family; plan modules 6, 8, 12)

Blueprint: `hironaka-g8b-family-pad.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d (decision of lane G11B,
round 7: the lower invariant is evaluated on the lower ideal with the divisor preceded by one empty placeholder per member of the
marked ideal, `HironakaG11InvBMPad.padE L m`).

Empty members of the divisor carry no geometry: no point lies on them, they impose no normal-crossings condition, their strict
transforms and preimages are empty.  This module proves that `padE L m` (the divisor of `L` preceded by `m` empty members) is
indistinguishable from `L` for everything the resolution invariants see except the absolute POSITIONS of the members:

* reindexing of coordinate families (`isCoordinateFamilyAt_reindex`); **`isSNCDivisor_padE_iff`**, **`isTransverse_padE_iff`**,
  **`hasNormalCrossings_padE_iff`** (and the one-member versions `*_cons_empty_iff`);
* **`isWellFormed_padE_iff`**, **`isInvDomain_padE_iff`**, **`isAdmissibleCentre_padE_iff`**;
* transforms: **`geoTransform_padE`**, **`geoTransformAlong_padE`** (`(padE L m)_T = padE L_T m`), `cosupp_geoTransformAlong_padE`,
  **`isGeoTestTower_padE_iff`**, **`isCanonical_padE_iff`** (canonical segments of a value function only see cosupports);
* the class data: `sameCarrierDim_padE_iff`, `expAgree_padE`, `restrictEquiv_padE`, `projectionTest_padE`, and
  **`locEquiv_padE`** (`LocEquiv κ A B → LocEquiv κ (padE A m) (padE B m)` for kinds without exceptional blowups, by the
  coinduction principle `HironakaG8LocalStable.LocEquiv.of_isLocStable`), in particular for `LocWPEquiv`.

`padE L 1` is `MonomialInvariantEmptyMember.insertEmpty 0 L` (`padE_one_eq_insertEmpty`).

Note: lane G11B's `HironakaG11InvBMPadCalc` (landed a few minutes later, independently) proves the same calculus; both are kept
(never delete).  The padded invariants `padInvSeq` and their class functoriality are lane G11B's `HironakaG11InvBMPadInv`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open scoped Hironaka.ProductComplexManifold

universe u v

namespace Hironaka.HironakaG8BFamilyPad

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.BlowupStrictSubmanifold
open Hironaka.HironakaG11InvBMPad (padE padE_padE pullback_padE cosupp_padE)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.MonomialInvariantEmptyMember (insertEmpty)
open Hironaka.HironakaG8LocalHistory (LocEquiv LocWPEquiv Kinds)
open Hironaka.HironakaG8LocalStable (IsLocStable isLocStable_locEquiv)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)

noncomputable section

variable {n : ℕ}

/-! ### Reindexing coordinate families -/

section Reindex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Coordinate families can be reindexed**: every member of the new family through `x` (with its coordinate set) occurs in
the old one. -/
theorem isCoordinateFamilyAt_reindex {ι ι' : Type*} {A : ι → Set M} {S : ι → Finset (Fin n)} {A' : ι' → Set M}
    {S' : ι' → Finset (Fin n)} {x : M} (h : IsCoordinateFamilyAt n A S x)
    (hmatch : ∀ i', x ∈ A' i' → ∃ i, A i = A' i' ∧ S i = S' i') : IsCoordinateFamilyAt n A' S' x := by
  obtain ⟨Φ, hsrc, h0, hfam⟩ := h
  refine ⟨Φ, hsrc, h0, fun i' hxi' y hy hyΦ => ?_⟩
  obtain ⟨i, hA, hS⟩ := hmatch i' hxi'
  rw [← hA, ← hS]
  exact hfam i (by rw [hA]; exact hxi') hy hyΦ

end Reindex

/-! ### One empty member in front -/

section Cons

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **An empty member in front does not change simple normal crossings.** -/
theorem isSNCDivisor_cons_empty_iff {E : List (Set M)} : IsSNCDivisor n ((∅ : Set M) :: E) ↔ IsSNCDivisor n E := by
  constructor
  · rintro ⟨hcl, h⟩
    refine ⟨fun H hH => hcl H (List.mem_cons_of_mem _ hH), fun x => ?_⟩
    obtain ⟨S', hcoord, hcard, hinj⟩ := h x
    exact ⟨fun i => S' i.succ, isCoordinateFamilyAt_reindex hcoord fun i _ => ⟨i.succ, rfl, rfl⟩,
      fun i hi => hcard i.succ hi, fun i hi j hj hij => Fin.succ_injective _ (hinj hi hj hij)⟩
  · rintro ⟨hcl, h⟩
    refine ⟨fun H hH => ?_, fun x => ?_⟩
    · rcases List.mem_cons.mp hH with rfl | hH
      · exact isClosed_empty
      · exact hcl H hH
    obtain ⟨S, hcoord, hcard, hinj⟩ := h x
    refine ⟨Fin.cons (α := fun _ => Finset (Fin n)) ∅ S, isCoordinateFamilyAt_reindex hcoord fun i' hi' => ?_,
      fun i' hi' => ?_, fun i' hi' j' hj' hij => ?_⟩
    · cases i' using Fin.cases with
      | zero => exact (notMem_empty x hi').elim
      | succ i => exact ⟨i, rfl, by simp⟩
    · cases i' using Fin.cases with
      | zero => exact (notMem_empty x hi').elim
      | succ i => rw [Fin.cons_succ]; exact hcard i hi'
    · cases i' using Fin.cases with
      | zero => exact (notMem_empty x hi').elim
      | succ i =>
        cases j' using Fin.cases with
        | zero => exact (notMem_empty x hj').elim
        | succ j =>
          rw [Fin.cons_succ, Fin.cons_succ] at hij
          exact congrArg Fin.succ (hinj (show x ∈ E.get i from hi') (show x ∈ E.get j from hj') hij)

/-- **An empty member in front does not change normal crossings with a set.** -/
theorem hasNormalCrossings_cons_empty_iff {C : Set M} {E : List (Set M)} :
    HasNormalCrossings n C ((∅ : Set M) :: E) ↔ HasNormalCrossings n C E := by
  constructor
  · intro h x hx
    obtain ⟨S₀, S', hcoord, hcard⟩ := h x hx
    refine ⟨S₀, fun i => S' i.succ, isCoordinateFamilyAt_reindex hcoord fun o _ => ?_, fun i hi => hcard i.succ hi⟩
    cases o with
    | none => exact ⟨none, rfl, rfl⟩
    | some i => exact ⟨some i.succ, rfl, rfl⟩
  · intro h x hx
    obtain ⟨S₀, S, hcoord, hcard⟩ := h x hx
    refine ⟨S₀, Fin.cons (α := fun _ => Finset (Fin n)) ∅ S, isCoordinateFamilyAt_reindex hcoord fun o ho => ?_,
      fun i' hi' => ?_⟩
    · cases o with
      | none => exact ⟨none, rfl, rfl⟩
      | some i' =>
        cases i' using Fin.cases with
        | zero => exact (notMem_empty x ho).elim
        | succ i => exact ⟨some i, rfl, by simp⟩
    · cases i' using Fin.cases with
      | zero => exact (notMem_empty x hi').elim
      | succ i => rw [Fin.cons_succ]; exact hcard i hi'

/-- **An empty member in front does not change transversality.** -/
theorem isTransverse_cons_empty_iff {N : Set M} {E : List (Set M)} :
    IsTransverse n N ((∅ : Set M) :: E) ↔ IsTransverse n N E := by
  constructor
  · intro h x hx
    obtain ⟨S₀, S', hcoord, hcard⟩ := h x hx
    refine ⟨S₀, fun i => S' i.succ, isCoordinateFamilyAt_reindex hcoord fun o _ => ?_, fun i hi => hcard i.succ hi⟩
    cases o with
    | none => exact ⟨none, rfl, rfl⟩
    | some i => exact ⟨some i.succ, rfl, rfl⟩
  · intro h x hx
    obtain ⟨S₀, S, hcoord, hcard⟩ := h x hx
    refine ⟨S₀, Fin.cons (α := fun _ => Finset (Fin n)) ∅ S, isCoordinateFamilyAt_reindex hcoord fun o ho => ?_,
      fun i' hi' => ?_⟩
    · cases o with
      | none => exact ⟨none, rfl, rfl⟩
      | some i' =>
        cases i' using Fin.cases with
        | zero => exact (notMem_empty x ho).elim
        | succ i => exact ⟨some i, rfl, by simp⟩
    · cases i' using Fin.cases with
      | zero => exact (notMem_empty x hi').elim
      | succ i => rw [Fin.cons_succ]; exact hcard i hi'

/-! ### `m` empty members in front -/

theorem isSNCDivisor_replicate_empty_append_iff (m : ℕ) {E : List (Set M)} :
    IsSNCDivisor n (List.replicate m (∅ : Set M) ++ E) ↔ IsSNCDivisor n E := by
  induction m with
  | zero => exact Iff.rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    exact isSNCDivisor_cons_empty_iff.trans ih

theorem hasNormalCrossings_replicate_empty_append_iff (m : ℕ) {C : Set M} {E : List (Set M)} :
    HasNormalCrossings n C (List.replicate m (∅ : Set M) ++ E) ↔ HasNormalCrossings n C E := by
  induction m with
  | zero => exact Iff.rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    exact hasNormalCrossings_cons_empty_iff.trans ih

theorem isTransverse_replicate_empty_append_iff (m : ℕ) {N : Set M} {E : List (Set M)} :
    IsTransverse n N (List.replicate m (∅ : Set M) ++ E) ↔ IsTransverse n N E := by
  induction m with
  | zero => exact Iff.rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    exact isTransverse_cons_empty_iff.trans ih

end Cons

/-! ### Padded marked ideals on one space -/

section OneSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem padE_one_eq_insertEmpty (L : MarkedIdeal n M) : padE L 1 = insertEmpty 0 L := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show List.replicate 1 ∅ ++ L.E = L.E.insertIdx 0 ∅
  simp

theorem isSNCDivisor_padE_iff (L : MarkedIdeal n M) (m : ℕ) : IsSNCDivisor n (padE L m).E ↔ IsSNCDivisor n L.E :=
  isSNCDivisor_replicate_empty_append_iff m

theorem isTransverse_padE_iff (L : MarkedIdeal n M) (m : ℕ) :
    IsTransverse n (padE L m).N (padE L m).E ↔ IsTransverse n L.N L.E :=
  isTransverse_replicate_empty_append_iff m

theorem hasNormalCrossings_padE_iff (L : MarkedIdeal n M) (m : ℕ) (C : Set M) :
    HasNormalCrossings n C (padE L m).E ↔ HasNormalCrossings n C L.E :=
  hasNormalCrossings_replicate_empty_append_iff m

/-- **Padding keeps well-formedness** (and conversely). -/
theorem isWellFormed_padE_iff (L : MarkedIdeal n M) (m : ℕ) : (padE L m).IsWellFormed ↔ L.IsWellFormed := by
  constructor
  · intro h
    exact ⟨h.isClosedSubmanifold_N, h.isCoherent, (isSNCDivisor_padE_iff L m).mp h.isSNCDivisor,
      (isTransverse_padE_iff L m).mp h.isTransverse⟩
  · intro h
    exact ⟨h.isClosedSubmanifold_N, h.isCoherent, (isSNCDivisor_padE_iff L m).mpr h.isSNCDivisor,
      (isTransverse_padE_iff L m).mpr h.isTransverse⟩

/-- **Padding keeps the domain of the invariants** (and conversely). -/
theorem isInvDomain_padE_iff (k : ℕ) (L : MarkedIdeal n M) (m : ℕ) : IsInvDomain k (padE L m) ↔ IsInvDomain k L := by
  constructor
  · intro h
    exact ⟨(isWellFormed_padE_iff L m).mp h.isWellFormed, h.dimLE, h.one_le_d, h.isNonzeroAlongAt⟩
  · intro h
    exact ⟨(isWellFormed_padE_iff L m).mpr h.isWellFormed, h.dimLE, h.one_le_d, h.isNonzeroAlongAt⟩

/-- **Padding keeps the admissible centres.** -/
theorem isAdmissibleCentre_padE_iff (L : MarkedIdeal n M) (m : ℕ) (C : Set M) :
    (padE L m).IsAdmissibleCentre C ↔ L.IsAdmissibleCentre C := by
  show (IsClosedSubmanifold n C ∧ C ⊆ L.cosupp ∧ HasNormalCrossings n C (padE L m).E) ↔
    (IsClosedSubmanifold n C ∧ C ⊆ L.cosupp ∧ HasNormalCrossings n C L.E)
  rw [hasNormalCrossings_padE_iff]

/-- **Padding keeps restricted equivalence.** -/
theorem restrictEquiv_padE {A B : MarkedIdeal n M} (h : RestrictEquiv A B) (m : ℕ) :
    RestrictEquiv (padE A m) (padE B m) :=
  ⟨h.N_eq, by show List.replicate m ∅ ++ A.E = List.replicate m ∅ ++ B.E; rw [h.E_eq], h.d_eq, h.le, h.ge⟩

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Padding commutes with one transform** (the strict transform of `∅` is `∅`). -/
theorem geoTransform_padE (L : MarkedIdeal n M) (m : ℕ) (C : Set M) (π : M' → M) :
    (padE L m).geoTransform C π = padE (L.geoTransform C π) m := by
  have hst : geoStrictTransform π C (∅ : Set M) = ∅ := geoStrictTransform_eq_empty_of_subset (empty_subset C)
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate m ∅ ++ L.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] =
    List.replicate m ∅ ++ (L.E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
  rw [List.map_append, List.map_replicate, hst, List.append_assoc]

end OneSpace

/-! ### Along towers -/

section Tower

variable {X : CMfd.{u} n} (L : MarkedIdeal n X) (m : ℕ)

/-- **Padding commutes with the transforms along every tower.** -/
theorem geoTransformAlong_padE :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), geoTransformAlong (padE L m) T = padE (geoTransformAlong L T) m
  | _, .refl => rfl
  | _, .step T C π _ => by
    rw [geoTransformAlong_step, geoTransformAlong_step, geoTransformAlong_padE T]
    exact geoTransform_padE _ m C π

theorem cosupp_geoTransformAlong_padE {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (padE L m) T).cosupp = (geoTransformAlong L T).cosupp := by
  rw [geoTransformAlong_padE]
  rfl

/-- **Padding keeps the multiple test blow-ups.** -/
theorem isGeoTestTower_padE_iff :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (padE L m) T ↔ IsGeoTestTower L T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff, isGeoTestTower_padE_iff T, geoTransformAlong_padE,
      isAdmissibleCentre_padE_iff]

/-- **Canonical segments of a value function only see the cosupports**: padding does not change them. -/
theorem isCanonical_padE_iff {Λ : Type v} [LinearOrder Λ] (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (padE L m) f T ↔ IsCanonical L f T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    show (IsCanonical (padE L m) f T ∧
        (C = ∅ ∨ C = ResolutionDriver.maxLocus (f T) (geoTransformAlong (padE L m) T).cosupp)) ↔
      (IsCanonical L f T ∧ (C = ∅ ∨ C = ResolutionDriver.maxLocus (f T) (geoTransformAlong L T).cosupp))
    rw [isCanonical_padE_iff f T, cosupp_geoTransformAlong_padE]

theorem sameCarrierDim_padE_iff {A B : MarkedIdeal n X} (m : ℕ) :
    SameCarrierDim (padE A m) (padE B m) ↔ SameCarrierDim A B :=
  Iff.rfl

/-- **Padding keeps the agreement of boundary exponents** (no point lies on an empty member). -/
theorem expAgree_padE {A B : MarkedIdeal n X} (h : ExpAgree A B) (m : ℕ) : ExpAgree (padE A m) (padE B m) := by
  intro H hH y hy hyH
  rcases List.mem_append.mp hH with hH | hH
  · rw [(List.eq_of_mem_replicate hH)] at hyH
    exact (notMem_empty y hyH).elim
  · exact h H hH y hy hyH

end Tower

/-! ### The local equivalences -/

section Local

/-- **Padding commutes with the product with a line** (the preimage of `∅` is empty). -/
theorem projectionTest_padE {X : CMfd.{u} n} (A : MarkedIdeal n X) (m : ℕ) :
    projectionTest (padE A m) = padE (projectionTest A) m := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate m ∅ ++ A.E).map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] =
    List.replicate m ∅ ++ (A.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X])
  rw [List.map_append, List.map_replicate, preimage_empty, List.append_assoc]

/-- The relation "padded locally equivalent marked ideals". -/
def PadRel (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ (A B : MarkedIdeal m Y) (j : ℕ), LocEquiv κ A B ∧ P = padE A j ∧ Q = padE B j

theorem isLocStable_padRel (κ : Kinds) : IsLocStable.{u} κ (fun {m} {Y} P Q => PadRel.{u} κ (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A, B, j, h, rfl, rfl⟩
    show List.replicate j ∅ ++ B.E = List.replicate j ∅ ++ A.E
    rw [h.E_eq]
  cosupp_eq := by
    rintro m Y P Q ⟨A, B, j, h, rfl, rfl⟩
    exact h.cosupp_eq_base
  controlled := by
    rintro m Y P Q ⟨A, B, j, h, rfl, rfl⟩ C Z π hπ hC
    refine ⟨A.geoTransform C π, B.geoTransform C π, j, ?_, geoTransform_padE A j C π, geoTransform_padE B j C π⟩
    exact (isLocStable_locEquiv κ).controlled h C π hπ ((isAdmissibleCentre_padE_iff A j C).mp hC)
  projection := by
    rintro hp m Y P Q ⟨A, B, j, h, rfl, rfl⟩
    exact ⟨projectionTest A, projectionTest B, j, (isLocStable_locEquiv κ).projection hp h, projectionTest_padE A j,
      projectionTest_padE B j⟩
  restrict := by
    rintro m Y P Q ⟨A, B, j, h, rfl, rfl⟩ U
    exact ⟨_, _, j, (isLocStable_locEquiv κ).restrict h U, pullback_padE _ A j, pullback_padE _ B j⟩

/-- **Padding keeps the local equivalences** of kinds without exceptional blowups (coinduction). -/
theorem locEquiv_padE {κ : Kinds} (hexc : κ.exc = false) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (h : LocEquiv κ A B) (m : ℕ) : LocEquiv κ (padE A m) (padE B m) :=
  HironakaG8LocalStable.LocEquiv.of_isLocStable (isLocStable_padRel κ) hexc ⟨A, B, m, h, rfl, rfl⟩

/-- **Padding keeps `LocWPEquiv`.** -/
theorem locWPEquiv_padE {X : CMfd.{u} n} {A B : MarkedIdeal n X} (h : LocWPEquiv A B) (m : ℕ) :
    LocWPEquiv (padE A m) (padE B m) :=
  locEquiv_padE rfl h m

end Local

end

end Hironaka.HironakaG8BFamilyPad
