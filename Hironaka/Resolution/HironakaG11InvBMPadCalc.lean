import Hironaka.Resolution.HironakaG11InvBMPad
import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Invariant.ContactStageInvDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Padded divisors: the calculus of `padE` (repair (B'), plan module 8 property (4') and module 12; decision G11B r7)

Blueprint: `hironaka-g11-inv-bm-max-order.tex` (node `g11-inv:bm-pad-calc`).  Plan: `work/hironaka-resume-20261111/G11B/
BPRIME-PLAN.md` §6d.

`HironakaG11InvBMPad.padE L m` is the marked ideal `L` with its divisor preceded by `m` empty members.  Empty members are
harmless: no point lies on them, their strict transforms and preimages are empty.  This module proves that every notion the
resolution invariants and their class functoriality see is unchanged (or commutes) under `padE`:

* normal crossings with `∅^m ++ E` (`hasNormalCrossings_replicate_append_iff`, `isSNCDivisor_replicate_append_iff`,
  `isTransverse_replicate_append_iff`; the general `hasNormalCrossings_of_through`: only the members through a point count);
* **`isAdmissibleCentre_padE_iff`**, `isWellFormed_padE_iff`, **`isInvDomain_padE_iff`**;
* **transforms commute with padding**: `geoTransform_padE`, **`geoTransformAlong_padE`**, `cosupp_geoTransformAlong_padE`,
  `N_geoTransformAlong_padE`, `isGeoTestTower_padE_iff`, `projectionTest_padE` (and `pullback_padE` of `HironakaG11InvBMPad`);
* **canonical segments only see cosupports**: `isCanonical_padE_iff` (any value function);
* `restrictEquiv_padE` (restricted equivalence), `withE_append_eq_padE` (a divisor `Z ++ E` with `Z` empty is a padding);
* class data: `expAgree_padE`, `sameCarrierDim_padE`;
* **the local equivalences pass to paddings**: `PadRel`, `isLocStable_padRel` (lane G8's coinduction principle
  `HironakaG8LocalStable.LocEquiv.of_isLocStable`), **`locEquiv_padE`** (kinds without exceptional blowups),
  **`locWPEquiv_padE`**.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMPadCalc

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings
  Hironaka.BlowupStrictSubmanifold Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMPad Hironaka.HironakaG8LocalHistory
  Hironaka.HironakaG8LocalStable
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open Hironaka.HironakaG11InvBMClass (ExpAgree SameCarrierDim)
open scoped ProductComplexManifold

noncomputable section

variable {n : ℕ}

/-! ### Normal crossings with empty members in front -/

section Crossings

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Normal crossings only see the members through the point**: if `C` has only normal crossings with `E` and every member
of `F` through a point of `C` is a member of `E`, then `C` has only normal crossings with `F`. -/
theorem hasNormalCrossings_of_through {C : Set M} {E F : List (Set M)} (hE : HasNormalCrossings n C E)
    (hFE : ∀ x ∈ C, ∀ i : Fin F.length, x ∈ F.get i → ∃ j : Fin E.length, E.get j = F.get i) :
    HasNormalCrossings n C F := by
  classical
  intro x hx
  obtain ⟨S₀, S, hcoord, hcard⟩ := hE x hx
  let idx (i : Fin F.length) (hi : x ∈ F.get i) : Fin E.length := (hFE x hx i hi).choose
  have hidx (i : Fin F.length) (hi : x ∈ F.get i) : E.get (idx i hi) = F.get i := (hFE x hx i hi).choose_spec
  let V (i : Fin F.length) : Finset (Fin n) := if hi : x ∈ F.get i then S (idx i hi) else ∅
  refine ⟨S₀, V, ?_, ?_⟩
  · obtain ⟨Φ, hsrc, h0, hΦ⟩ := hcoord
    refine ⟨Φ, hsrc, h0, ?_⟩
    intro o
    cases o with
    | none => exact hΦ none
    | some i =>
      intro hi y hy hyΦ
      change x ∈ F.get i at hi
      change (y ∈ F.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (V i))
      simp only [V, dif_pos hi]
      have hxj : x ∈ E.get (idx i hi) := (hidx i hi).symm ▸ hi
      have he := hΦ (some (idx i hi)) hxj hy hyΦ
      change (y ∈ E.get (idx i hi) ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S (idx i hi))) at he
      rw [hidx i hi] at he
      exact he
  · intro i hi
    simp only [V, dif_pos hi]
    exact hcard (idx i hi) ((hidx i hi).symm ▸ hi)

/-- **Normal crossings with empty members in front.** -/
theorem hasNormalCrossings_replicate_append_iff (C : Set M) (E : List (Set M)) (m : ℕ) :
    HasNormalCrossings n C (List.replicate m ∅ ++ E) ↔ HasNormalCrossings n C E := by
  constructor
  · intro h
    exact NormalCrossingsComparison.hasNormalCrossings_of_forall_mem h fun H hH => List.mem_append_right _ hH
  · intro h
    refine hasNormalCrossings_of_through h fun x _ i hi => ?_
    rcases List.mem_append.mp (List.get_mem _ i) with h1 | h1
    · rw [List.eq_of_mem_replicate h1] at hi
      exact absurd hi (notMem_empty x)
    · exact List.mem_iff_get.mp h1

/-- An empty member in front of a simple normal crossings divisor. -/
theorem isSNCDivisor_empty_cons {E : List (Set M)} (hE : IsSNCDivisor n E) : IsSNCDivisor n (∅ :: E) := by
  classical
  refine ⟨fun A hA => ?_, fun x => ?_⟩
  · rcases List.mem_cons.mp hA with rfl | hA
    · exact isClosed_empty
    · exact hE.1 A hA
  · obtain ⟨S, ⟨Φ, ht, h0, hcoords⟩, hcard, hinj⟩ := hE.2 x
    let S' : Fin (∅ :: E).length → Finset (Fin n) := Fin.cases ∅ S
    refine ⟨S', ⟨Φ, ht, h0, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa [S'] using hcoords j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa [S'] using hcard j
    · intro i hi j hj heq
      refine Fin.cases ?_ (fun a => ?_) i hi heq
      · simp
      · intro ha hea
        refine Fin.cases ?_ (fun b => ?_) j hj hea
        · simp
        · intro hb hab
          exact congrArg Fin.succ (hinj (by simpa using ha) (by simpa using hb) (by simpa [S'] using hab))

/-- **Simple normal crossings with empty members in front.** -/
theorem isSNCDivisor_replicate_append_iff (E : List (Set M)) (m : ℕ) :
    IsSNCDivisor n (List.replicate m ∅ ++ E) ↔ IsSNCDivisor n E := by
  refine ⟨fun h => NormalCrossingsComparison.isSNCDivisor_of_sublist h (List.sublist_append_right _ _), fun h => ?_⟩
  induction m with
  | zero => simpa using h
  | succ m ih => simpa [List.replicate_succ] using isSNCDivisor_empty_cons ih

/-- **Transversality with empty members in front.** -/
theorem isTransverse_replicate_append_iff (N : Set M) (E : List (Set M)) (m : ℕ) :
    IsTransverse n N (List.replicate m ∅ ++ E) ↔ IsTransverse n N E :=
  ⟨fun h => NormalCrossingsComparison.isTransverse_of_forall_mem h fun H hH => List.mem_append_right _ hH,
    fun h => ContactStageInvDomain.isTransverse_append_of_forall_notMem h fun H hH x _ => by
      rw [List.eq_of_mem_replicate hH]
      exact notMem_empty x⟩

end Crossings

/-! ### Padded marked ideals on one manifold -/

section OneSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Admissible centres do not see the padding.** -/
theorem isAdmissibleCentre_padE_iff (L : MarkedIdeal n M) (m : ℕ) (C : Set M) :
    (padE L m).IsAdmissibleCentre C ↔ L.IsAdmissibleCentre C :=
  Iff.and Iff.rfl (Iff.and Iff.rfl (hasNormalCrossings_replicate_append_iff C L.E m))

/-- **Well-formedness does not see the padding.** -/
theorem isWellFormed_padE_iff (L : MarkedIdeal n M) (m : ℕ) : (padE L m).IsWellFormed ↔ L.IsWellFormed :=
  ⟨fun h => ⟨h.isClosedSubmanifold_N, h.isCoherent, (isSNCDivisor_replicate_append_iff L.E m).mp h.isSNCDivisor,
      (isTransverse_replicate_append_iff L.N L.E m).mp h.isTransverse⟩,
    fun h => ⟨h.isClosedSubmanifold_N, h.isCoherent, (isSNCDivisor_replicate_append_iff L.E m).mpr h.isSNCDivisor,
      (isTransverse_replicate_append_iff L.N L.E m).mpr h.isTransverse⟩⟩

/-- **The domain of the resolution invariants does not see the padding.** -/
theorem isInvDomain_padE_iff {k : ℕ} (L : MarkedIdeal n M) (m : ℕ) : IsInvDomain k (padE L m) ↔ IsInvDomain k L :=
  ⟨fun h => ⟨(isWellFormed_padE_iff L m).mp h.isWellFormed, h.dimLE, h.one_le_d, h.isNonzeroAlongAt⟩,
    fun h => ⟨(isWellFormed_padE_iff L m).mpr h.isWellFormed, h.dimLE, h.one_le_d, h.isNonzeroAlongAt⟩⟩

/-- **Restricted equivalence passes to paddings.** -/
theorem restrictEquiv_padE {L L' : MarkedIdeal n M} (h : RestrictEquiv L L') (m : ℕ) :
    RestrictEquiv (padE L m) (padE L' m) :=
  ⟨h.N_eq, by rw [padE_E, padE_E, h.E_eq], h.d_eq, h.le, h.ge⟩

/-- **A divisor with empty members in front is a padding.** -/
theorem withE_append_eq_padE (L : MarkedIdeal n M) {Z : List (Set M)} (hZ : ∀ H ∈ Z, H = ∅) :
    ({ L with E := Z ++ L.E } : MarkedIdeal n M) = padE L Z.length := by
  obtain ⟨j, rfl⟩ : ∃ j, Z = List.replicate j ∅ := ⟨Z.length, List.eq_replicate_iff.mpr ⟨rfl, hZ⟩⟩
  rw [List.length_replicate]
  rfl

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **One transform commutes with padding** (the strict transform of `∅` is `∅`; the exceptional member is appended at the
end). -/
theorem geoTransform_padE (L : MarkedIdeal n M) (m : ℕ) (C : Set M) (π : M' → M) :
    (padE L m).geoTransform C π = padE (L.geoTransform C π) m := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate m ∅ ++ L.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] =
    List.replicate m ∅ ++ (L.E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
  rw [List.map_append, List.map_replicate, geoStrictTransform_eq_empty_of_subset (empty_subset C), List.append_assoc]

end OneSpace

/-! ### Along towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **The transforms along every tower commute with padding.** -/
theorem geoTransformAlong_padE (L : MarkedIdeal n X) (m : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), geoTransformAlong (padE L m) T = padE (geoTransformAlong L T) m
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransformAlong_padE L m T]
      exact geoTransform_padE _ m C π

/-- Along every tower the cosupport does not see the padding. -/
theorem cosupp_geoTransformAlong_padE (L : MarkedIdeal n X) (m : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (padE L m) T).cosupp = (geoTransformAlong L T).cosupp := by
  rw [geoTransformAlong_padE]
  rfl

/-- Along every tower the carrier does not see the padding. -/
theorem N_geoTransformAlong_padE (L : MarkedIdeal n X) (m : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (padE L m) T).N = (geoTransformAlong L T).N := by
  rw [geoTransformAlong_padE]
  rfl

/-- **Multiple test blow-ups do not see the padding.** -/
theorem isGeoTestTower_padE_iff (L : MarkedIdeal n X) (m : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (padE L m) T ↔ IsGeoTestTower L T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff, isGeoTestTower_padE_iff L m T, geoTransformAlong_padE,
        isAdmissibleCentre_padE_iff]

/-- **Canonical segments do not see the padding** (for any value function: a canonical segment only sees the values and the
cosupports). -/
theorem isCanonical_padE_iff {Λ : Type v} [LinearOrder Λ] (L : MarkedIdeal n X) (m : ℕ)
    (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (padE L m) f T ↔ IsCanonical L f T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      show (IsCanonical (padE L m) f T ∧ (C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong (padE L m) T).cosupp)) ↔
        (IsCanonical L f T ∧ (C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong L T).cosupp))
      rw [isCanonical_padE_iff L m f T, cosupp_geoTransformAlong_padE]

/-- **Boundary exponents of paddings** (no point lies on an empty member). -/
theorem expAgree_padE {A B : MarkedIdeal n X} (h : ExpAgree A B) (m : ℕ) : ExpAgree (padE A m) (padE B m) := by
  intro H hH y hy hyH
  rcases List.mem_append.mp hH with h1 | h1
  · rw [List.eq_of_mem_replicate h1] at hyH
    exact absurd hyH (notMem_empty y)
  · exact h H h1 y hy hyH

/-- Carrier dimensions of paddings. -/
theorem sameCarrierDim_padE {A B : MarkedIdeal n X} (h : SameCarrierDim A B) (m : ℕ) :
    SameCarrierDim (padE A m) (padE B m) :=
  h

end Tower

/-! ### The local equivalences pass to paddings -/

section Local

/-- **Products with a line commute with padding.** -/
theorem projectionTest_padE {m : ℕ} {Y : CMfd.{u} m} (P : MarkedIdeal m Y) (j : ℕ) :
    projectionTest (padE P j) = padE (projectionTest P) j := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate j ∅ ++ P.E).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
    List.replicate j ∅ ++ (P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y])
  rw [List.map_append, List.map_replicate, preimage_empty, List.append_assoc]

/-- **The relation of the coinduction**: `P'`, `Q'` are the paddings by `j` empty members of a locally equivalent pair. -/
def PadRel (κ : Kinds) (j : ℕ) {m : ℕ} {Y : CMfd.{u} m} (P' Q' : MarkedIdeal m Y) : Prop :=
  ∃ P Q : MarkedIdeal m Y, LocEquiv κ P Q ∧ P' = padE P j ∧ Q' = padE Q j

/-- **Padding is stable under the local test actions.** -/
theorem isLocStable_padRel (κ : Kinds) (j : ℕ) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => PadRel κ j (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P' Q' ⟨P, Q, h, rfl, rfl⟩
    show List.replicate j ∅ ++ Q.E = List.replicate j ∅ ++ P.E
    rw [h.E_eq]
  cosupp_eq := by
    rintro m Y P' Q' ⟨P, Q, h, rfl, rfl⟩
    exact h.cosupp_eq_base
  controlled := by
    rintro m Y P' Q' ⟨P, Q, h, rfl, rfl⟩ C Z π hπ hC
    exact ⟨P.geoTransform C π, Q.geoTransform C π,
      (isLocStable_locEquiv κ).controlled h C π hπ ((isAdmissibleCentre_padE_iff P j C).mp hC),
      geoTransform_padE P j C π, geoTransform_padE Q j C π⟩
  projection := by
    rintro hp m Y P' Q' ⟨P, Q, h, rfl, rfl⟩
    exact ⟨projectionTest P, projectionTest Q, (isLocStable_locEquiv κ).projection hp h, projectionTest_padE P j,
      projectionTest_padE Q j⟩
  restrict := by
    rintro m Y P' Q' ⟨P, Q, h, rfl, rfl⟩ U
    exact ⟨MarkedIdeal.pullback (Subtype.val : U → Y) P, MarkedIdeal.pullback (Subtype.val : U → Y) Q,
      (isLocStable_locEquiv κ).restrict h U, pullback_padE _ P j, pullback_padE _ Q j⟩

/-- **Local equivalence passes to paddings** (kinds without exceptional blowups). -/
theorem locEquiv_padE {κ : Kinds} (hexc : κ.exc = false) {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : LocEquiv κ P Q) (j : ℕ) : LocEquiv κ (padE P j) (padE Q j) :=
  LocEquiv.of_isLocStable (isLocStable_padRel κ j) hexc ⟨P, Q, h, rfl, rfl⟩

/-- **`LocWPEquiv` passes to paddings** (Bierstone--Milman's `s(i, ii)`-equivalence, local form). -/
theorem locWPEquiv_padE {X : CMfd.{u} n} {P Q : MarkedIdeal n X} (h : LocWPEquiv P Q) (j : ℕ) :
    LocWPEquiv (padE P j) (padE Q j) :=
  locEquiv_padE rfl h j

end Local

end

end Hironaka.HironakaG11InvBMPadCalc
