import Hironaka.Resolution.HironakaG4CompactWindowTasks
import Hironaka.Resolution.HironakaG4SharpCountStability
import Hironaka.Resolution.HironakaExhaustionBlockLocalFiniteness
import Mathlib.Topology.Compactness.SigmaCompact

/-! Constructing successive actual compact-task service blocks from compact bad windows. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4WindowServiceBlocks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterTowerAlong MemberInterLocusAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4SharpBadFootprint HironakaG4CompactWindowTasks HironakaG4SharpCountStability
variable {n : ℕ} {X : CMfd.{u} n}

/-- An actual sharp prefix together with its served compact tasks. -/
structure BlockState (W : Set X) (E : List (Set X)) (K : CompactExhaustion X) (j : ℕ) where
  Y : CMfd.{u} n
  T : BlowupTower X Y
  test : IsGeoTestTower (geometricTemplate W []) T
  full : IsGeoTestTower (geometricTemplate (univ : Set X) E) T
  sharp : CurrentSharpCentres W E T
  good : ∀ a < j, ∀ z ∈ strictAlong T W, T.proj z ∈ K a →
    normalCrossingsAt (n := n) (strictAlong T W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z

/-- The actual finite block selected at one stage. -/
structure BlockChoice (W : Set X) (E : List (Set X)) (K : CompactExhaustion X)
    {j : ℕ} (p : BlockState W E K j) where
  U : Opens X
  cover : (K j : Set X) ⊆ U
  Z : CMfd.{u} n
  S : BlowupTower p.Y Z
  test : IsGeoTestTower (geometricTemplate W []) (p.T.append S)
  full : IsGeoTestTower (geometricTemplate (univ : Set X) E) (p.T.append S)
  sharp : CurrentSharpCentres W E (p.T.append S)
  good : ∀ z ∈ strictAlong (p.T.append S) W, (p.T.append S).proj z ∈ U →
    normalCrossingsAt (n := n) (strictAlong (p.T.append S) W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) (p.T.append S)).E z

section FullBoundary

variable {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X)

def chooseBlockFullBoundary {j : ℕ} (p : BlockState W E K j) : BlockChoice W E K p := by
  apply Classical.choice
  obtain ⟨_V,U,hKU,_hK,Z,S,hS,hSF,hSS,_hOver,hNC⟩ :=
    compact_window_full_boundary_service_after_prefix hW hE hLocal (K j) (K.isCompact j)
      p.T p.test p.full p.sharp
  exact ⟨⟨U,hKU,Z,S,hS,hSF,hSS,hNC⟩⟩

include hW hE in
/-- A sharp append preserves every base region that was already resolved. -/
theorem good_after_sharp_append {j : ℕ} (p : BlockState W E K j) (q : BlockChoice W E K p)
    (a : ℕ) (ha : a < j) :
    ∀ z ∈ strictAlong (p.T.append q.S) W, (p.T.append q.S).proj z ∈ K a →
      normalCrossingsAt (n := n) (strictAlong (p.T.append q.S) W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (p.T.append q.S)).E z := by
  let N := strictAlong p.T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) p.T).E
  have hN : IsClosed N := isClosed_strictAlong p.T hW.1
  have hF : ∀ H ∈ F, IsClosed H :=
    HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong
      (geometricTemplate (univ : Set X) E) hE.1 p.T
  have hSharpS := sharp_tail_of_append W E p.T q.S q.sharp
  obtain ⟨hFoot,_⟩ := currentSharpCentres_original_footprint hN hF q.S hSharpS
  intro z hz hza
  rw [strictAlong_append] at hz
  rw [strictAlong_append,geoTransformAlong_append,
    template_current (univ : Set X) E p.T,strict_univ p.T]
  rw [BlowupTower.proj_append] at hza
  by_contra hnc
  obtain ⟨hzN,hbad⟩ := hFoot ⟨hz,hnc⟩
  exact hbad (p.good a ha (q.S.proj z) hzN hza)

/-- Recursive blocks actually serve their scheduled compact exhaustion tasks. -/
def fullBoundaryStates : (j : ℕ) → BlockState W E K j
  | 0 => ⟨X,.refl,trivial,trivial,trivial,by intro a ha; omega⟩
  | j+1 => by
    let p := fullBoundaryStates j
    let q := chooseBlockFullBoundary hW hE hLocal K p
    refine ⟨q.Z,p.T.append q.S,q.test,q.full,q.sharp,?_⟩
    intro a ha
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ ha) with hlt | heq
    · exact good_after_sharp_append hW hE K p q a hlt
    · subst a
      intro z hz hzK
      exact q.good z hz (q.cover hzK)

/-- The selected endpoints form a nested chain of literal finite towers. -/
theorem fullBoundaryStates_extend (j : ℕ) :
    ∃ Q : BlowupTower (fullBoundaryStates hW hE hLocal K j).Y
        (fullBoundaryStates hW hE hLocal K (j+1)).Y,
      (fullBoundaryStates hW hE hLocal K (j+1)).T =
        (fullBoundaryStates hW hE hLocal K j).T.append Q := by
  refine ⟨(chooseBlockFullBoundary hW hE hLocal K
    (fullBoundaryStates hW hE hLocal K j)).S, rfl⟩

end FullBoundary

section Compatibility
variable (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X)

set_option linter.unusedVariables false in
def chooseBlock (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X) {j : ℕ} (p : BlockState W E K j) : BlockChoice W E K p :=
  chooseBlockFullBoundary hW hE hLocal K p

set_option linter.unusedVariables false in
def states (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X) (j : ℕ) : BlockState W E K j :=
  fullBoundaryStates hW hE hLocal K j

set_option linter.unusedVariables false in
theorem states_extend (j : ℕ) :
    ∃ Q : BlowupTower (states hn hW hE hdense hLocal K j).Y
        (states hn hW hE hdense hLocal K (j+1)).Y,
      (states hn hW hE hdense hLocal K (j+1)).T =
        (states hn hW hE hdense hLocal K j).T.append Q :=
  fullBoundaryStates_extend hW hE hLocal K j

end Compatibility

end
end Hironaka.HironakaG4WindowServiceBlocks
