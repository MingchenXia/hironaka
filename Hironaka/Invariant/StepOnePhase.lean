import Hironaka.Invariant.StepOneWellFounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The values of the nonempty centres of a canonical segment; the phases of the Step 1 value

Blueprint `hir:step-one-phase` (`blueprint/src/hironaka.tex`, Hironaka phase H4, a piece of `hir:maximal-order-step`, toward
property (8)).  Sources: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1 (Step 1a lowers the number
`s` of original members through the points of the cosupport, one phase per value of `s`; Step 1aa and Step 1ba blow up the points
of value `(s, ∞)`); Bierstone--Milman 2008 §7.

Along a tower `T` and for a value function `inv`, `centreValues inv T` lists, in order, the value of `inv` at (a point of) each
nonempty centre of `T`; on a canonical segment such a centre is the maximum locus, so the entry is the maximum of the value on
the cosupport at that stage.  If one step of a canonical segment never raises a value and lowers the values over its centre
(`StepOneWellFounded.StepDrop`, properties (3) and (4) of `hir:centre-function`), then **the values of the nonempty centres
strictly decrease, and every value on the last cosupport lies below all of them** (`pairwise_centreValues`,
`lt_of_mem_centreValues`).  The list of a prefix is a prefix of the list (`centreValues_append`), so along a growing sequence of
canonical segments the values of all nonempty centres form one strictly decreasing sequence.

For the masked Step 1 value `stepOneInvM R 𝔍` (marked ideals of the domain of maximal order) this is the **phase bookkeeping**
of property (8), which does not depend on the form chosen for (8) (inbox I-1139): the first entries (the levels `s`) of the
values of the nonempty centres do not increase and are at most `#E` (`level_le_length_E`); each special value `(s, ∞)` occurs at
most once, so at most `#E + 1` nonempty centres have a special value (`length_filter_special_centreValues_le`); the number of
nonempty centres is the sum over the phases `s = 0, …, #E` (`length_centreValues_eq_sum_phases`), and inside the phase `s` the
lower values of the non-special centres strictly decrease (`pairwise_snd_filter_fst_eq`).  What is left for (8) is a bound, in
each phase, on such decreasing sequences of lower values: that is where the lower-dimensional invariant's own (8) enters.

## Main results

* `centreValues`, `centreValues_step_of_nonempty`, `centreValues_step_of_eq_empty`, `centreValues_append`,
  `centreValues_isPrefix_append`, `exists_eq_of_mem_centreValues`;
* `length_centreValues`, `countCentresMeeting_le_length_centreValues`: the length is the number of nonempty centres;
* **`pairwise_centreValues`**, **`lt_of_mem_centreValues`**, `nodup_centreValues`: under `StepDrop`, along canonical segments;
* `level_le_length_E`, `fst_le_of_mem_centreValues_stepOneInvM`, **`pairwise_fst_centreValues_stepOneInvM`**,
  **`length_filter_special_centreValues_le`**, `length_eq_sum_filter_fst`, **`length_centreValues_eq_sum_phases`**,
  `pairwise_snd_filter_fst_eq`: the phases of the Step 1 value.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOnePhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.StepOneValueMasked
  Hironaka.StepOneWellFounded Hironaka.BoundaryCount
  Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### The values of the nonempty centres -/

section Generic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

variable (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) in
open Classical in
/-- **The values of the nonempty centres of a tower**, in order: for each step along a nonempty centre `C` after `T`, the value
of `inv T` at a point of `C` (on a canonical segment `C` is then the maximum locus, and the entry is the maximum). -/
def centreValues : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → List Λ
  | _, .refl => []
  | _, .step T C _ _ => centreValues T ++ if h : C.Nonempty then [inv T h.some] else []

variable (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

@[simp] theorem centreValues_refl : centreValues inv (BlowupTower.refl : BlowupTower X X) = [] := rfl

theorem centreValues_step_of_nonempty {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (h : C.Nonempty) :
    centreValues inv (.step T C π hπ) = centreValues inv T ++ [inv T h.some] := by
  classical
  show (centreValues inv T ++ if h : C.Nonempty then [inv T h.some] else []) = _
  rw [dif_pos h]

theorem centreValues_step_of_eq_empty {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (h : C = ∅) : centreValues inv (.step T C π hπ) = centreValues inv T := by
  classical
  show (centreValues inv T ++ if h : C.Nonempty then [inv T h.some] else []) = _
  rw [dif_neg (by rw [h]; exact not_nonempty_empty), List.append_nil]

/-- **The list of an extension starts with the list of the prefix**: the rest is the list of the extension `S` for the value
function `S' ↦ inv (T S')`. -/
theorem centreValues_append {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),
      centreValues inv (T.append S) = centreValues inv T ++ centreValues (fun {W} S' => inv (Y := W) (T.append S')) S
  | _, .refl => by simp
  | _, .step S C π hπ => by
      classical
      show (centreValues inv (T.append S) ++ if h : C.Nonempty then [inv (T.append S) h.some] else []) =
        centreValues inv T ++ (centreValues (fun {W} S' => inv (Y := W) (T.append S')) S ++
          if h : C.Nonempty then [inv (T.append S) h.some] else [])
      rw [centreValues_append T S, List.append_assoc]

/-- Along a growing sequence the lists grow: the list of a prefix is a prefix of the list. -/
theorem centreValues_isPrefix_append {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    centreValues inv T <+: centreValues inv (T.append S) := by
  rw [centreValues_append]
  exact List.prefix_append _ _

/-- Every entry is a value of `inv` at some stage of the tower. -/
theorem exists_eq_of_mem_centreValues :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) {a : Λ}, a ∈ centreValues inv T →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (x : Y'), a = inv T' x
  | _, .refl, a, ha => by simp at ha
  | _, .step T C π hπ, a, ha => by
      by_cases h : C.Nonempty
      · rw [centreValues_step_of_nonempty inv T C π hπ h, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | ha
        · exact exists_eq_of_mem_centreValues T ha
        · exact ⟨_, T, h.some, ha⟩
      · rw [centreValues_step_of_eq_empty inv T C π hπ (not_nonempty_iff_eq_empty.mp h)] at ha
        exact exists_eq_of_mem_centreValues T ha

/-- **The length of the list is the number of nonempty centres.** -/
theorem length_centreValues :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (centreValues inv T).length = countCentresMeeting (univ : Set X) T
  | _, .refl => rfl
  | _, .step T C π hπ => by
      classical
      show (centreValues inv (.step T C π hπ)).length =
        countCentresMeeting (univ : Set X) T + if (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty then 1 else 0
      rw [preimage_univ, inter_univ]
      by_cases h : C.Nonempty
      · rw [centreValues_step_of_nonempty inv T C π hπ h, List.length_append, length_centreValues T, if_pos h]
        rfl
      · rw [centreValues_step_of_eq_empty inv T C π hπ (not_nonempty_iff_eq_empty.mp h), length_centreValues T,
          if_neg h]
        rfl

/-- The nonempty centres meeting the preimage of `K` are at most the nonempty centres. -/
theorem countCentresMeeting_le_countCentresMeeting_univ (K : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), countCentresMeeting K T ≤ countCentresMeeting (univ : Set X) T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      classical
      show countCentresMeeting K T + (if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0) ≤
        countCentresMeeting (univ : Set X) T + if (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty then 1 else 0
      have ih := countCentresMeeting_le_countCentresMeeting_univ K T
      by_cases h : (C ∩ T.proj ⁻¹' K).Nonempty
      · have h' : (C ∩ T.proj ⁻¹' (univ : Set X)).Nonempty := h.mono (inter_subset_inter_right _ (preimage_mono
          (subset_univ K)))
        rw [if_pos h, if_pos h']
        omega
      · rw [if_neg h]
        split_ifs <;> omega

/-- The nonempty centres meeting the preimage of `K` are at most the length of the list. -/
theorem countCentresMeeting_le_length_centreValues (K : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    countCentresMeeting K T ≤ (centreValues inv T).length := by
  rw [length_centreValues]
  exact countCentresMeeting_le_countCentresMeeting_univ K T

variable {𝔪 : MarkedIdeal n X} {inv}

/-- The two halves of the induction: strictly decreasing, and above every value on the last cosupport. -/
theorem pairwise_and_lt_centreValues (hdrop : StepDrop 𝔪 inv) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T →
      (centreValues inv T).Pairwise (fun a b => b < a) ∧
        ∀ a ∈ centreValues inv T, ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, inv T z < a
  | _, .refl, _ => ⟨List.Pairwise.nil, fun a ha => by simp at ha⟩
  | _, .step T C π hπ, hcan => by
      have hT : IsCanonical 𝔪 inv T := hcan.1
      have hC : C = ∅ ∨ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
      have ih := pairwise_and_lt_centreValues hdrop T hT
      -- one step: a point of the new cosupport lies over the old one, with a value at most that of its image
      have hstep : ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
          π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv (.step T C π hπ) z ≤ inv T (π z) := by
        intro z hz
        obtain ⟨hpz, h1, h2⟩ := hdrop T C π hπ hcan z hz
        refine ⟨hpz, ?_⟩
        by_cases hzC : π z ∈ C
        · exact (h1 hzC).le
        · exact (h2 hzC).le
      have hold : ∀ a ∈ centreValues inv T, ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
          inv (.step T C π hπ) z < a := fun a ha z hz =>
        (hstep z hz).2.trans_lt (ih.2 a ha _ (hstep z hz).1)
      by_cases hne : C.Nonempty
      · have hCm : C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hC.resolve_left hne.ne_empty
        have hsome : hne.some ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp := hCm ▸ hne.some_mem
        rw [centreValues_step_of_nonempty inv T C π hπ hne]
        refine ⟨List.pairwise_append.mpr ⟨ih.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩, ?_⟩
        · rw [List.mem_singleton] at hb
          rw [hb]
          exact ih.2 a ha _ hsome.1
        · intro a ha z hz
          rcases List.mem_append.mp ha with ha | ha
          · exact hold a ha z hz
          · rw [List.mem_singleton] at ha
            rw [ha]
            obtain ⟨hpz, h1, h2⟩ := hdrop T C π hπ hcan z hz
            exact lt_of_mem_maxLocus hsome hpz
              ⟨fun hm => h1 (by rw [hCm]; exact hm), fun hm => h2 fun hc => hm (by rw [← hCm]; exact hc)⟩
      · rw [centreValues_step_of_eq_empty inv T C π hπ (not_nonempty_iff_eq_empty.mp hne)]
        exact ⟨ih.1, hold⟩

/-- **The values of the nonempty centres of a canonical segment strictly decrease** (under `StepDrop`). -/
theorem pairwise_centreValues (hdrop : StepDrop 𝔪 inv) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 inv T) : (centreValues inv T).Pairwise (fun a b => b < a) :=
  (pairwise_and_lt_centreValues hdrop T hcan).1

/-- **Every value on the last cosupport lies below the value of every nonempty centre** (under `StepDrop`). -/
theorem lt_of_mem_centreValues (hdrop : StepDrop 𝔪 inv) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 inv T) {a : Λ} (ha : a ∈ centreValues inv T) {z : Y}
    (hz : z ∈ (geoTransformAlong 𝔪 T).cosupp) : inv T z < a :=
  (pairwise_and_lt_centreValues hdrop T hcan).2 a ha z hz

/-- The values of the nonempty centres of a canonical segment are pairwise distinct. -/
theorem nodup_centreValues (hdrop : StepDrop 𝔪 inv) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 inv T) : (centreValues inv T).Nodup :=
  (pairwise_centreValues hdrop T hcan).imp fun h => ne_of_gt h

end Generic

/-! ### Lists of lexicographic pairs -/

section Lex

variable {β : Type*} [LinearOrder β]

/-- In a strictly decreasing list of lexicographic pairs the first entries do not increase. -/
theorem pairwise_fst_of_pairwise {l : List (ℕ ×ₗ β)} (hl : l.Pairwise (fun a b => b < a)) :
    (l.map fun a => (ofLex a).1).Pairwise (fun s t => t ≤ s) := by
  rw [List.pairwise_map]
  refine hl.imp fun {a b} h => ?_
  rcases Prod.Lex.lt_iff.mp h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- **Inside a phase** (first entry `s`) the second entries of a strictly decreasing list of lexicographic pairs strictly
decrease. -/
theorem pairwise_snd_filter_fst_eq {l : List (ℕ ×ₗ β)} (hl : l.Pairwise (fun a b => b < a)) (s : ℕ) :
    ((l.filter fun a => (ofLex a).1 = s).map fun a => (ofLex a).2).Pairwise (fun c d => d < c) := by
  rw [List.pairwise_map]
  refine (hl.filter _).imp_of_mem fun {a b} ha hb h => ?_
  have hsa : (ofLex a).1 = s := by simpa using (List.mem_filter.mp ha).2
  have hsb : (ofLex b).1 = s := by simpa using (List.mem_filter.mp hb).2
  rcases Prod.Lex.lt_iff.mp h with h | ⟨-, h⟩
  · exact absurd h (by rw [hsa, hsb]; exact lt_irrefl s)
  · exact h

/-- **A list of numbers below `m` is the sum of its fibres** over `0, …, m - 1`. -/
theorem length_eq_sum_filter_fst {α : Type*} (f : α → ℕ) (m : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, f a < m) → l.length = ∑ s ∈ Finset.range m, (l.filter fun a => f a = s).length
  | [], _ => by simp
  | a :: l, h => by
      have ih := length_eq_sum_filter_fst f m l fun b hb => h b (List.mem_cons_of_mem a hb)
      have ha : f a ∈ Finset.range m := Finset.mem_range.mpr (h a List.mem_cons_self)
      have hsplit : ∀ s, ((a :: l).filter fun b => f b = s).length =
          (if f a = s then 1 else 0) + (l.filter fun b => f b = s).length := by
        intro s
        by_cases has : f a = s
        · simp [has, add_comm]
        · simp [has]
      have hone : (∑ s ∈ Finset.range m, if f a = s then 1 else 0) = 1 := by
        rw [Finset.sum_ite_eq, if_pos ha]
      rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib, hone, ← ih, List.length_cons]
      omega

end Lex

/-! ### The phases of the masked Step 1 value -/

section StepOne

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
variable (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **The level is at most the number of original members.** -/
theorem level_le_length_E {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : level 𝔍 T y ≤ 𝔍.E.length := by
  classical
  show (Finset.univ.filter fun i : Fin (origMembers 𝔍 T).length => y ∈ (origMembers 𝔍 T).get i).card ≤ _
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact List.length_take_le _ _

/-- The first entry of every value of the masked Step 1 value is at most `#E`. -/
theorem fst_stepOneInvM_le {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (stepOneInvM R 𝔍 T y)).1 ≤ 𝔍.E.length := by
  rw [stepOneInvL_fst]
  exact level_le_length_E 𝔍 T y

/-- The first entry of the value of every nonempty centre is at most `#E`. -/
theorem fst_le_of_mem_centreValues_stepOneInvM {Y : CMfd.{u} n} (T : BlowupTower X Y)
    {a : ℕ ×ₗ WithTop Λ} (ha : a ∈ centreValues (stepOneInvM R 𝔍) T) : (ofLex a).1 ≤ 𝔍.E.length := by
  obtain ⟨Y', T', x, rfl⟩ := exists_eq_of_mem_centreValues _ T ha
  exact fst_stepOneInvM_le R 𝔍 T' x

variable {R 𝔍}

/-- **Along a canonical segment of the masked Step 1 value the values of the nonempty centres strictly decrease** (`𝔍` in the
domain, of maximal order, `0 < n`). -/
theorem pairwise_centreValues_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    (centreValues (stepOneInvM R 𝔍) T).Pairwise (fun a b => b < a) :=
  pairwise_centreValues (stepDrop_stepOneInvM R 𝔍 h hmax hn) T hcan

/-- **The phases: the levels of the nonempty centres do not increase.** -/
theorem pairwise_fst_centreValues_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    ((centreValues (stepOneInvM R 𝔍) T).map fun a => (ofLex a).1).Pairwise (fun s t => t ≤ s) :=
  pairwise_fst_of_pairwise (pairwise_centreValues_stepOneInvM h hmax hn T hcan)

/-- **Each special value occurs at most once, so at most `#E + 1` nonempty centres of a canonical segment have a special value
`(s, ∞)`.** -/
theorem length_filter_special_centreValues_le (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    ((centreValues (stepOneInvM R 𝔍) T).filter fun a => (ofLex a).2 = ⊤).length ≤ 𝔍.E.length + 1 := by
  classical
  set L := (centreValues (stepOneInvM R 𝔍) T).filter fun a => (ofLex a).2 = ⊤ with hL
  have hnd : L.Nodup := (nodup_centreValues (stepDrop_stepOneInvM R 𝔍 h hmax hn) T hcan).filter _
  have hinj : ∀ a ∈ L, ∀ b ∈ L, (ofLex a).1 = (ofLex b).1 → a = b := by
    intro a ha b hb hab
    have ha2 : (ofLex a).2 = ⊤ := by simpa using (List.mem_filter.mp ha).2
    have hb2 : (ofLex b).2 = ⊤ := by simpa using (List.mem_filter.mp hb).2
    have : ofLex a = ofLex b := Prod.ext hab (ha2.trans hb2.symm)
    simpa using congrArg toLex this
  have hnd' : (L.map fun a => (ofLex a).1).Nodup := hnd.map_on fun a ha b hb hab => hinj a ha b hb hab
  have hsub : (L.map fun a => (ofLex a).1).toFinset ⊆ Finset.range (𝔍.E.length + 1) := by
    intro s hs
    rw [List.mem_toFinset, List.mem_map] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (fst_le_of_mem_centreValues_stepOneInvM R 𝔍 T (List.mem_filter.mp ha).1))
  calc L.length = (L.map fun a => (ofLex a).1).length := (List.length_map _).symm
    _ = (L.map fun a => (ofLex a).1).toFinset.card := (List.toFinset_card_of_nodup hnd').symm
    _ ≤ (Finset.range (𝔍.E.length + 1)).card := Finset.card_le_card hsub
    _ = 𝔍.E.length + 1 := Finset.card_range _

variable (R 𝔍) in
/-- **The number of nonempty centres is the sum over the phases** `s = 0, …, #E` of the numbers of nonempty centres whose value
has level `s` (for every tower). -/
theorem length_centreValues_eq_sum_phases {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (centreValues (stepOneInvM R 𝔍) T).length =
      ∑ s ∈ Finset.range (𝔍.E.length + 1),
        ((centreValues (stepOneInvM R 𝔍) T).filter fun a => (ofLex a).1 = s).length :=
  length_eq_sum_filter_fst (fun a => (ofLex a).1) _ _ fun _a ha =>
    Nat.lt_succ_of_le (fst_le_of_mem_centreValues_stepOneInvM R 𝔍 T ha)

/-- **Inside the phase `s` the second entries of the values of the nonempty centres strictly decrease** (those of the
non-special centres are the lower values `(s, λ)`, `λ` from the lower-dimensional invariant). -/
theorem pairwise_snd_phase_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) (s : ℕ) :
    (((centreValues (stepOneInvM R 𝔍) T).filter fun a => (ofLex a).1 = s).map fun a => (ofLex a).2).Pairwise
      (fun c d => d < c) :=
  pairwise_snd_filter_fst_eq (pairwise_centreValues_stepOneInvM h hmax hn T hcan) s

end StepOne

end

end Hironaka.StepOnePhase
