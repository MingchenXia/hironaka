import Hironaka.Invariant.GeneralCompanionPhase
import Hironaka.Invariant.GeneralStepValue

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general step: property (8') of the general value, and the general value as a resolution invariant

Blueprint `hir:general-seq-finite` (`blueprint/src/hironaka.tex`, Hironaka phase H4, the last piece of `hir:general-step`).
Human decision I-1139 C-0001 (option (b)): property (8) of a resolution invariant is its per-sequence form
`ResolutionInvariantSeq.SeqLocallyFinite`.  Sources: Włodarczyk 2005 (`hiron.tex`), proof of Proposition `pr:resol`, Step 2
("then we repeat the procedure", the orders of the nonmonomial part dropping); Bierstone--Milman 2008, Step II.

**Main results.**

* `SeqLocallyFiniteMaxOrder n k M`: property (8') of a value function `M` for the marked ideals of the domain of maximal order
  along their submanifold -- along every growing sequence of canonical segments of `M 𝔍` only finitely many nonempty centres
  meet a compact set (the hypothesis `hM8` of TN3's `GeneralCompanionPhase.exists_bound_countPhase`, binder for binder);
* **`seqLocallyFinite_genInv`**: if `M` is a value function for the marked ideals of maximal order (`IsMaxOrderValue`) with
  (8') for them, the general value `genInv M` has (8') for every marked ideal of the domain (`0 < n`).  Along a growing sequence
  of canonical segments the nonempty centres meeting the preimage of a compact `K` have order `≤ q` for one `q`
  (`NonmonomialOrderGlobalPhase.exists_centre_nmOrd_le_of_isCompact`), so their number is at most the sum over the phases
  `o = 0, …, q` of the phase counts (`GeneralCompanionPhase.countCentresMeeting_le_sum_countPhase`); the monomial phase is
  bounded by its strictly decreasing well-founded values (`GeneralCompanionPhase.countPhase_le_filter`,
  `GeneralPhaseCount.exists_bound_phase_zero`), each phase `o ≥ 1` by (8') of `M` for one companion ideal
  (`GeneralCompanionPhase.exists_bound_countPhase`);
* **`ofMaxOrder`** (`hir:general-step`): such an `M` gives a resolution invariant in dimension `≤ k` in the sense of
  `ResolutionInvariantSeq.ResolutionInvariant`, with the general value as invariant (properties (1)--(7), (4') are
  `GeneralStepValue.isInvValue_genInv`).

**Off the route, kept** (correct and proved): the orchestrator's independent review of 3 October 2026 (finding F2) showed that
(8') holds for every value function with properties (1)--(7), (4') and well-ordered values
(`CanonicalCentres.seqLocallyFinite_of_wellFoundedLT`, `hir:invariant-well-founded`), and the route's general step
(`CanonicalCentres.generalStep`, `hir:general-step-wf`) uses that.  No declaration of this module lies in the constant cone of the
main theorem.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralSeqFinite

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MaxOrderValue Hironaka.GeneralValue
  Hironaka.GeneralCompanionPhase Hironaka.ResolutionInvariantSeq
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n : ℕ}

variable (n) in
/-- **Property (8') for the marked ideals of maximal order**: for every marked ideal `𝔍` of the domain `IsInvDomain k` of
maximal order along its submanifold and every compact `K`, along every growing sequence of canonical segments of `M 𝔍` the
numbers of centres meeting `K` are bounded (the hypothesis `hM8` of `GeneralCompanionPhase.exists_bound_countPhase`). -/
def SeqLocallyFiniteMaxOrder (k : ℕ) {Λ : Type v} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ K : Set X, IsCompact K → ∀ s : GrowingSeq X, (∀ i, IsCanonical 𝔍 (M 𝔍) (s.stage i).2) →
      ∃ m, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Property (8') of the general value** (`hir:general-seq-finite`): for a value function `M` for the marked ideals of
maximal order in dimension `≤ k` with property (8') for them, and `0 < n`, along every growing sequence of canonical segments
of the general value `genInv M 𝔪` (`𝔪` in the domain) only finitely many nonempty centres meet a compact set. -/
theorem seqLocallyFinite_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n) (hM8 : SeqLocallyFiniteMaxOrder n k M) :
    SeqLocallyFinite n k (genInv M) := by
  intro X 𝔪 h K hK s hs
  classical
  obtain ⟨q, hq⟩ := NonmonomialOrderGlobalPhase.exists_centre_nmOrd_le_of_isCompact hn h (ordMonotone_genInv M 𝔪) hK
  have hall : ∀ o ∈ Finset.range (q + 1), ∃ m : ℕ, ∀ i, countPhase 𝔪 K o (s.stage i).2 ≤ m := by
    intro o _
    rcases Nat.eq_zero_or_pos o with rfl | ho
    · obtain ⟨m, hm⟩ := GeneralPhaseCount.exists_bound_phase_zero hM hn h s hs
      exact ⟨m, fun i => (countPhase_le_filter hM hn h K 0 _ (hs i)).trans (hm i)⟩
    · exact exists_bound_countPhase hM hn h ho hK (fun 𝔍 h𝔍 hmax K hK s hs => hM8 𝔍 h𝔍 hmax K hK s hs) s hs
  choose! m hm using hall
  refine ⟨∑ o ∈ Finset.range (q + 1), m o, fun i => ?_⟩
  exact (countCentresMeeting_le_sum_countPhase hM hn h hq _ (hs i)).trans
    (Finset.sum_le_sum fun o ho => hm o ho i)

variable (n k) in
/-- **The general step** (`hir:general-step`): a value function `M` for the marked ideals of maximal order in dimension
`≤ k` with property (8') for them gives a resolution invariant in dimension `≤ k` (`0 < n`), the general value `genInv M`. -/
def ofMaxOrder (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hM : IsMaxOrderValue n k M) (hM8 : SeqLocallyFiniteMaxOrder n k M) (hn : 0 < n) :
    ResolutionInvariant.{u, v} n k (ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ)) where
  inv := genInv M
  isInvValue := GeneralStepValue.isInvValue_genInv hM hn
  seqLocallyFinite := seqLocallyFinite_genInv hM hn hM8

/-- The invariant of `ofMaxOrder` is the general value. -/
theorem ofMaxOrder_inv (hM : IsMaxOrderValue n k M) (hM8 : SeqLocallyFiniteMaxOrder n k M) (hn : 0 < n)
    {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofMaxOrder n k M hM hM8 hn).inv 𝔪 T y = genInv M 𝔪 T y := rfl

end

end Hironaka.GeneralSeqFinite
