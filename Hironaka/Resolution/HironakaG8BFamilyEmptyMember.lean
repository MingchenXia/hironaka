import Hironaka.Resolution.HironakaG8BFamilyPad
import Hironaka.Resolution.HironakaG8BFamilyGeneric
import Hironaka.Resolution.HironakaG11InvBMEmptyMember
import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Coherence.VanishingIdealCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value sees empty members of the divisor: `EmptyMemberIndep` fails in every dimension `≥ 1`

Blueprint: `hironaka-g8b-family-empty-member.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d.  Inbox I-1370
(C-0002: the claim; C-0003: lane G11B's confirmation and the decision for padded lower divisors).

Lane G11B's round-7 proposal for property (4') of Bierstone--Milman's Step 1 value was to carry the hypothesis
`HironakaG11InvBMEmptyMember.EmptyMemberIndep (k - 1) R.inv` ("the lower invariant does not see empty members of the divisor")
through the induction on the dimension.  The induction produces the lower invariants as GENERAL VALUES `genInv M` (TN-CLASSICAL's
general step), and the general value at a point of order `0` is `(0, γ)`, where the monomial invariant `γ` records the members
through the point by their ABSOLUTE positions in the divisor (`MonomialInvariantEmptyMember`).  This module turns that
observation into a theorem with an explicit counterexample:

* the marked ideal `exMarked n = (ℂ^{n+1}, ℂ × 0, [{z₀ = 0}], 𝓘_{z₀ = 0}, 1)` (carrier the first coordinate line, one member,
  the ideal of the member, mark `1`) lies in the domain in every dimension `k ≥ 1` (`isInvDomain_exMarked`), and so does the
  same marked ideal with an empty member in front (`insertEmpty 0`, by `HironakaG8BFamilyPad`);
* at the origin the nonmonomial part has order `0` (`nmOrd_exMarked_zero`) and the monomial invariant is a value whose set of
  members is nonempty (`exists_towerInvAlong_exMarked`);
* **`not_emptyMemberIndep_of_eq_genInv`**, **`not_emptyMemberIndep_genInv`**: for EVERY Step 1 value `M` and every `k ≥ 1`,
  `¬ EmptyMemberIndep k (genInv M)` (in dimension `n + 1`, universe `0`); **`not_emptyMemberIndep_genInv_of_pos`** (`0 < n`);
* **`not_emptyMemberIndep_invFamilyQ`**, **`not_emptyMemberIndep_invFamilyBM`**: the invariants of the class-functorial
  induction (`HironakaG8BFamilyGeneric`, `HironakaG8BFamily`) of index `≥ 1` do not satisfy it, whatever the Step 1 operator.

Consequently a hypothesis `EmptyMemberIndep (k - 1) R.inv` on the lower invariant can be discharged only for `k = 1` along the
induction; lane G11B dropped it (I-1370 C-0003) in favour of padded lower divisors (`HironakaG11InvBMPad`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8BFamilyEmptyMember

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings
  Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong
  Hironaka.MonomialInvariant Hironaka.MonomialCase
  Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong
  Hironaka.MonomialPartAlong Hironaka.NonmonomialOrderLocal
  Hironaka.IdealWeightPowers Hironaka.MonomialInvariantEmptyMember
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HironakaG11InvBMEmptyMember (SameUpToEmptyMembers EmptyMemberIndep)
open Hironaka.HironakaG11InvBMPad (padE)
open Hironaka.HironakaG8BFamilyPad (padE_one_eq_insertEmpty isInvDomain_padE_iff)
open Hironaka.GeneralValue (genInv)

noncomputable section

/-! ### Coordinate subspaces of `ℂ^m` -/

section Coord

variable {m : ℕ}

/-- The translation `z ↦ z - w`, as centred holomorphic coordinates at `w`. -/
def translationAt (w : ComplexModel m) : LocalHolomorphicEquivAt (n := m) w where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := fun z => z - w
  invFun := fun z => z + w
  toFun_holomorphic := (differentiable_id.sub_const w).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const w).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

theorem sub_mem_coordSubspace_iff {S : Finset (Fin m)} {x y : ComplexModel m} (hx : x ∈ coordSubspace S) :
    y - x ∈ coordSubspace S ↔ y ∈ coordSubspace S := by
  simp only [coordSubspace, mem_ofPred_eq] at hx ⊢
  constructor
  · intro h j hj
    have h1 := h j hj
    rw [PiLp.sub_apply, hx j hj, sub_zero] at h1
    exact h1
  · intro h j hj
    rw [PiLp.sub_apply, hx j hj, h j hj, sub_zero]

/-- **A family of coordinate subspaces of `ℂ^m` is a coordinate family at every point** (translate the point to `0`). -/
theorem isCoordinateFamilyAt_coordSubspace {ι : Type*} (A : ι → Set (ComplexModel m)) (S : ι → Finset (Fin m))
    (hA : ∀ i, A i = coordSubspace (S i)) (x : ComplexModel m) : IsCoordinateFamilyAt m A S x := by
  refine ⟨translationAt x, fun _ _ => mem_univ _, sub_self x, fun i hxi y _ _ => ?_⟩
  rw [hA i] at hxi ⊢
  exact (sub_mem_coordSubspace_iff hxi).symm

theorem isClosed_coordSubspace (S : Finset (Fin m)) : IsClosed (coordSubspace S) := by
  have h : coordSubspace S = ⋂ j ∈ S, {z : ComplexModel m | z j = 0} := by
    ext z
    simp [coordSubspace]
  rw [h]
  exact isClosed_biInter fun j _ =>
    isClosed_eq (EuclideanSpace.proj j : ComplexModel m →L[ℂ] ℂ).continuous continuous_const

theorem regularAtDim_coordSubspace (S : Finset (Fin m)) {x : ComplexModel m} (hx : x ∈ coordSubspace S) :
    RegularAtDim (n := m) (coordSubspace S) x (m - S.card) :=
  HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace (translationAt x) (fun _ _ => mem_univ _) (sub_self x)
    (fun _ _ => (sub_mem_coordSubspace_iff hx).symm)

theorem isClosedSubmanifold_coordSubspace (S : Finset (Fin m)) : IsClosedSubmanifold m (coordSubspace S) :=
  ⟨isClosed_coordSubspace S, fun _ hx => ⟨_, regularAtDim_coordSubspace S hx⟩⟩

end Coord

/-! ### The counterexample -/

section Example

variable {n : ℕ}

variable (n) in
/-- The coordinates `1, …, n` of `ℂ^{n+1}`. -/
def tailCoords : Finset (Fin (n + 1)) := Finset.univ.map (Fin.succEmb n)

theorem card_tailCoords : (tailCoords n).card = n := by
  simp [tailCoords]

theorem zero_notMem_tailCoords : (0 : Fin (n + 1)) ∉ tailCoords n := by
  simp [tailCoords, Fin.succ_ne_zero]

variable (n) in
/-- The carrier: the first coordinate line `ℂ × 0`. -/
def lineN : Set (ComplexModel (n + 1)) := coordSubspace (tailCoords n)

variable (n) in
/-- The member: the hyperplane `{z₀ = 0}`. -/
def hypH : Set (ComplexModel (n + 1)) := coordSubspace {0}

variable (n) in
/-- `ℂ^{n+1}` as a complex manifold. -/
abbrev Model : CMfd.{0} (n + 1) := CMfd.of (ComplexModel (n + 1))

variable (n) in
/-- **The marked ideal** `(ℂ^{n+1}, ℂ × 0, [{z₀ = 0}], 𝓘_{z₀ = 0}, 1)`. -/
def exMarked : MarkedIdeal (n + 1) (Model n) :=
  ⟨lineN n, [hypH n], vanishingIdeal (n := n + 1) (hypH n), 1⟩

theorem zero_mem_lineN : (0 : ComplexModel (n + 1)) ∈ lineN n := fun _ _ => rfl

theorem zero_mem_hypH : (0 : ComplexModel (n + 1)) ∈ hypH n := fun _ _ => rfl

theorem get_hypH (i : Fin [hypH n].length) : [hypH n].get i = coordSubspace {0} := by
  obtain ⟨_ | j, hj⟩ := i
  · rfl
  · simp at hj

theorem isSNCDivisor_hypH : IsSNCDivisor (n + 1) [hypH n] := by
  refine ⟨fun H hH => ?_, fun x => ⟨fun _ => {0}, isCoordinateFamilyAt_coordSubspace _ _ get_hypH x,
    fun _ _ => Finset.card_singleton _, fun i _ j _ _ => ?_⟩⟩
  · rw [List.mem_singleton.mp hH]
    exact isClosed_coordSubspace _
  · have hi := i.isLt
    have hj := j.isLt
    simp only [List.length_singleton] at hi hj
    exact Fin.ext (by omega)

theorem isTransverse_lineN_hypH : IsTransverse (n + 1) (lineN n) [hypH n] := by
  intro x _
  refine ⟨tailCoords n, fun _ => {0}, isCoordinateFamilyAt_coordSubspace _ _ (fun o => ?_) x,
    fun _ _ => ⟨Finset.card_singleton _, Finset.disjoint_singleton_left.mpr zero_notMem_tailCoords⟩⟩
  cases o with
  | none => rfl
  | some i => exact get_hypH i

/-- The first coordinate. -/
def coord0 : ComplexModel (n + 1) → ℂ := fun z => z 0

theorem holomorphicAt_coord0 (y : ComplexModel (n + 1)) : HolomorphicAt (n + 1) (coord0 (n := n)) y :=
  Eventually.of_forall fun _ =>
    (EuclideanSpace.proj (0 : Fin (n + 1)) : ComplexModel (n + 1) →L[ℂ] ℂ).differentiableAt.mdifferentiableAt

theorem coord0_mem (y : ComplexModel (n + 1)) : (vanishingIdeal (n := n + 1) (hypH n)).mem y (coord0 (n := n)) :=
  ⟨holomorphicAt_coord0 y, Eventually.of_forall fun _ hz => hz 0 (Finset.mem_singleton_self 0)⟩

/-- **The ideal does not vanish identically on the carrier near any of its points**: the first coordinate is nonzero at
points of the line arbitrarily close to any point of it. -/
theorem isNonzeroAlongAt_lineN {y : ComplexModel (n + 1)} (hy : y ∈ lineN n) :
    IsNonzeroAlongAt (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) y := by
  refine ⟨coord0, coord0_mem y, fun hev => ?_⟩
  let c : ℂ → ComplexModel (n + 1) := fun t => y + t • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℂ)
  have hc : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
  have hcy : c 0 = y := by simp [c]
  have hline : ∀ t, c t ∈ lineN n := by
    intro t j hj
    have hj0 : j ≠ 0 := fun h => zero_notMem_tailCoords (h ▸ hj)
    simp [c, hy j hj, hj0]
  have hcoord : ∀ t, coord0 (c t) = y 0 + t := by
    intro t
    simp [c, coord0]
  have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), ¬ (c t ∈ lineN n ∧ coord0 (c t) ≠ 0) := by
    have := hc.tendsto 0
    rw [hcy] at this
    exact this.eventually hev
  have h3 : ∀ᶠ t in 𝓝 (0 : ℂ), y 0 + t = 0 := h2.mono fun t ht => by
    by_contra hne
    exact ht ⟨hline t, by rw [hcoord]; exact hne⟩
  have hy0 : y 0 + 0 = 0 := h3.self_of_nhds
  have h4 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), y 0 + t = 0 := h3.filter_mono nhdsWithin_le_nhds
  have h5 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ht1, ht2⟩ := (h4.and h5).exists
  exact ht2 (by linear_combination ht1 - hy0)

variable (n) in
/-- **The counterexample lies in the domain** in every dimension `k ≥ 1`. -/
theorem isInvDomain_exMarked {k : ℕ} (hk : 1 ≤ k) : IsInvDomain k (exMarked n) where
  isWellFormed := ⟨isClosedSubmanifold_coordSubspace _,
    VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_coordSubspace _), isSNCDivisor_hypH,
    isTransverse_lineN_hypH⟩
  dimLE := fun _ hx => ⟨1, hk, by
    have h := regularAtDim_coordSubspace (tailCoords n) hx
    rwa [card_tailCoords, Nat.add_sub_cancel_left] at h⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun _ hy => isNonzeroAlongAt_lineN hy

theorem mem_cosupport_of_mem {z : ComplexModel (n + 1)} (hzN : z ∈ lineN n) (hzH : z ∈ hypH n) :
    z ∈ cosupport (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) 1 :=
  ⟨hzN, fun _ hg => (vanishesToOrderOn_one_iff hzN hg.1).mpr (hg.2.self_of_nhds hzH)⟩

theorem zero_mem_cosupp : (0 : ComplexModel (n + 1)) ∈ (exMarked n).cosupp :=
  mem_cosupport_of_mem zero_mem_lineN zero_mem_hypH

/-- **The exponent of the ideal along the member at the origin is at least `1`.** -/
theorem one_le_divExpAlong :
    1 ≤ divExpAlong (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) (hypH n) 0 := by
  obtain ⟨r, hr⟩ := exists_isLocalRetraction (regularAtDim_coordSubspace (tailCoords n) (zero_mem_lineN (n := n)))
  exact (isDivNearAlong_iff_le_divExpAlong hr zero_mem_hypH (isNonzeroAlongAt_lineN zero_mem_lineN)
    (fun _ _ hg => hg.1)).mp (Eventually.of_forall fun _ hzN hzH => mem_cosupport_of_mem hzN hzH)

/-- **At the origin the nonmonomial part has order `0`**: the constant `1` lies in it (the monomial part is contained in the
ideal along the carrier, as the exponent along the member is `≥ 1`). -/
theorem nmOrd_exMarked_zero : nmOrd (exMarked n) 0 = 0 := by
  refine Nat.le_zero.mp (nmOrd_le_of_notMem fun hmem => ?_)
  have hcoh : (vanishingIdeal (n := n + 1) (hypH n)).IsCoherent :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_coordSubspace _)
  have h1 : (nmPart (exMarked n)).mem 0 (fun _ => 1) := by
    refine ⟨holomorphicAt_const 1, fun g hg => ?_⟩
    obtain ⟨hgh, hgm⟩ := hg
    have hspan := hgm ⟨0, by simp [exMarked]⟩ zero_mem_lineN zero_mem_hypH
    have hspan' : IsInSpanOnAt (n := n + 1) (lineN n) ((vanishingIdeal (n := n + 1) (hypH n)).mem 0) 0 g := by
      refine RelativePrincipalizationSpan.IsInSpanOnAt.mono (fun s hs => ?_) hspan
      have hs1 := idealPow_le_of_le (𝔞 := vanishingIdeal (n := n + 1) (hypH n)) (fun _ _ hg => hg.1)
        one_le_divExpAlong 0 s hs
      rwa [idealPow_succ, idealPow_zero, BlowupControlledTransform.unitIdeal_mul hcoh] at hs1
    have hfun : (fun y => g y * 1) = g := funext fun _ => mul_one _
    rw [hfun]
    exact ⟨hgh, hspan'⟩
  exact one_ne_zero ((vanishesToOrderOn_one_iff hmem.1 (holomorphicAt_const 1)).mp (hmem.2 _ h1))

/-- **The monomial invariant at the origin** is a value whose set of members is nonempty. -/
theorem exists_towerInvAlong_exMarked :
    ∃ v : Val, towerInvAlong (exMarked n) (BlowupTower.refl : BlowupTower (Model n) (Model n)) 0 = v ∧
      ∃ i ∈ ofColex (ofLex (ofLex v).2).2, 0 ≤ i := by
  have hmem : (0 : ℕ) ∈ memberIdx [hypH n] (0 : ComplexModel (n + 1)) :=
    (mem_memberIdx [hypH n]).mpr ⟨by simp, zero_mem_hypH⟩
  have hexp : expDataAlong (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) [hypH n] 0 0 =
      divExpAlong (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) (hypH n) 0 := by
    simp [expDataAlong]
  have hsum : 1 ≤ ∑ i ∈ memberIdx [hypH n] (0 : ComplexModel (n + 1)),
      expDataAlong (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) [hypH n] 0 i := by
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem)
    rw [hexp]
    exact one_le_divExpAlong
  obtain ⟨I, hI, hinv, -⟩ := exists_top hsum
  refine ⟨key (n + 1) (expDataAlong (n + 1) (lineN n) (vanishingIdeal (n := n + 1) (hypH n)) [hypH n] 0) I, hinv, ?_⟩
  obtain ⟨-, hId⟩ := mem_feasible.mp hI
  obtain ⟨i, hi⟩ : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hId
    exact absurd hId (by norm_num)
  exact ⟨i, hi, Nat.zero_le i⟩

end Example

/-! ### `EmptyMemberIndep` fails for the general value -/

section Fails

variable {n : ℕ} {Λ : Type v} [LinearOrder Λ]

open Classical in
/-- **The marked ideal with an empty member in front and the marked ideal itself differ only by an empty member.** -/
theorem sameUpToEmptyMembers_insertEmpty_exMarked : SameUpToEmptyMembers (insertEmpty 0 (exMarked n)) (exMarked n) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (((exMarked n).E.insertIdx 0 ∅).filter fun H => decide H.Nonempty) = _
  rw [List.insertIdx_zero, List.filter_cons_of_neg (by simp)]

/-- **The general value sees the empty member in front**: at the origin the general values of `insertEmpty 0 (exMarked n)`
and of `exMarked n` (along the empty tower) differ, for every Step 1 value `M`. -/
theorem genInv_insertEmpty_exMarked_ne
    (M : ∀ {X : CMfd.{0} (n + 1)}, MarkedIdeal (n + 1) X → ∀ {Y : CMfd.{0} (n + 1)}, BlowupTower X Y → Y → Λ) :
    genInv M (insertEmpty 0 (exMarked n)) (BlowupTower.refl : BlowupTower (Model n) (Model n)) 0 ≠
      genInv M (exMarked n) (BlowupTower.refl : BlowupTower (Model n) (Model n)) 0 := by
  intro h
  rw [genInv_insertEmpty_of_nmOrd_eq_zero M (exMarked n) (Nat.zero_le _) BlowupTower.refl nmOrd_exMarked_zero,
    GeneralValueOrderZero.genInv_eq_towerInvAlong M (exMarked n) BlowupTower.refl nmOrd_exMarked_zero] at h
  obtain ⟨v, hv, hpos⟩ := exists_towerInvAlong_exMarked (n := n)
  rw [hv] at h
  have h' := congrArg (fun p : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ) => (ofLex p).2) h
  simp only [ofLex_toLex] at h'
  exact shiftVal_ne_self hpos (Sum.inl_injective (toLex.injective h'))

/-- **`EmptyMemberIndep` fails for every value function equal to a general value**, in every dimension `k ≥ 1`. -/
theorem not_emptyMemberIndep_of_eq_genInv {k : ℕ} (hk : 1 ≤ k)
    (M : ∀ {X : CMfd.{0} (n + 1)}, MarkedIdeal (n + 1) X → ∀ {Y : CMfd.{0} (n + 1)}, BlowupTower X Y → Y → Λ)
    (inv : ∀ {X : CMfd.{0} (n + 1)}, MarkedIdeal (n + 1) X → ∀ {Y : CMfd.{0} (n + 1)}, BlowupTower X Y → Y →
      ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ))
    (hinv : ∀ {X : CMfd.{0} (n + 1)} (𝔪 : MarkedIdeal (n + 1) X) {Y : CMfd.{0} (n + 1)} (T : BlowupTower X Y) (y : Y),
      inv 𝔪 T y = genInv M 𝔪 T y) :
    ¬ EmptyMemberIndep (n := n + 1) k inv := by
  intro hEI
  have hB := isInvDomain_exMarked n hk
  have hA : IsInvDomain k (insertEmpty 0 (exMarked n)) := by
    rw [← padE_one_eq_insertEmpty]
    exact (isInvDomain_padE_iff k _ 1).mpr hB
  obtain ⟨-, hval⟩ := hEI _ _ hA hB sameUpToEmptyMembers_insertEmpty_exMarked
    (BlowupTower.refl : BlowupTower (Model n) (Model n)) trivial
  have h : inv (insertEmpty 0 (exMarked n)) (BlowupTower.refl : BlowupTower (Model n) (Model n)) 0 =
      inv (exMarked n) (BlowupTower.refl : BlowupTower (Model n) (Model n)) 0 := hval 0 zero_mem_cosupp
  rw [hinv, hinv] at h
  exact genInv_insertEmpty_exMarked_ne M h

/-- **`EmptyMemberIndep` fails for the general value of every Step 1 value**, in every dimension `k ≥ 1`. -/
theorem not_emptyMemberIndep_genInv {k : ℕ} (hk : 1 ≤ k)
    (M : ∀ {X : CMfd.{0} (n + 1)}, MarkedIdeal (n + 1) X → ∀ {Y : CMfd.{0} (n + 1)}, BlowupTower X Y → Y → Λ) :
    ¬ EmptyMemberIndep (n := n + 1) k (genInv M) :=
  not_emptyMemberIndep_of_eq_genInv hk M (genInv M) fun _ _ _ _ => rfl

/-- The same for an ambient dimension `n > 0`. -/
theorem not_emptyMemberIndep_genInv_of_pos {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 1 ≤ k)
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) :
    ¬ EmptyMemberIndep (n := n) k (genInv M) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact not_emptyMemberIndep_genInv hk M

end Fails

/-! ### The invariants of the induction -/

section Family

open Hironaka.HironakaG8BFamilyGeneric

/-- **The invariants of index `≥ 1` of the class-functorial induction do not satisfy `EmptyMemberIndep`**, whatever the Step 1
operator and the carried property. -/
theorem not_emptyMemberIndep_invFamilyQ {n : ℕ} (hn : 0 < n) (S : StepOneOp n) (Q : InvProp n)
    (h0 : Q 0 (ResolutionInvariantSeq.ResolutionInvariant.ofDimZero.{0, 0} (n := n) (CanonicalCentres.ValTy 0)
      (0 : ℕ)).inv)
    (h : ∀ k, k < n → StepGood S Q k) (k : ℕ) (hk : k + 1 ≤ n) :
    ¬ EmptyMemberIndep (n := n) (k + 1)
      (invFamilyQ hn S Q h0 h (k + 1) hk).toBMInvariant.toResolutionInvariant.inv :=
  not_emptyMemberIndep_genInv_of_pos hn (Nat.le_add_left 1 k) _

/-- **The same for the family of `HironakaG8BFamily`** (Step 1 value `stepOneInvBM` of the unpadded lower family). -/
theorem not_emptyMemberIndep_invFamilyBM {n : ℕ} (hn : 0 < n)
    (h : ∀ k, k < n → HironakaG8BFamily.StepInputsBM n (k + 1)) (k : ℕ) (hk : k + 1 ≤ n) :
    ¬ EmptyMemberIndep (n := n) (k + 1) (HironakaG8BFamily.invFamilyBM hn h (k + 1) hk).toResolutionInvariant.inv :=
  not_emptyMemberIndep_genInv_of_pos hn (Nat.le_add_left 1 k) _

end Family

end

end Hironaka.HironakaG8BFamilyEmptyMember
