import Hironaka.Resolution.HironakaG4CompactComponentTasks
import Hironaka.Resolution.HironakaG4WindowServiceBlocks
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! Successive sharp blocks supported on compact original bad components. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactComponentBlocks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GlobalComponents HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4CompactComponentTasks HironakaEmbeddedBoundary RestrictEmptyTower
variable {n : ℕ} {X : CMfd.{u} n}

/-- A literal sharp prefix serving compact tasks only on compact bad components. -/
structure ComponentBlockState (W : Set X) (E : List (Set X)) (K : CompactExhaustion X) (j : ℕ) where
  Y : CMfd.{u} n
  T : BlowupTower X Y
  test : IsGeoTestTower (geometricTemplate W []) T
  full : IsGeoTestTower (geometricTemplate (univ : Set X) E) T
  sharp : CurrentSharpCentres W E T
  support : CentresOver (compactComponentUnion (originalSharpBadLocus (n := n) W E)) T
  good : ∀ a < j, ∀ z ∈ strictAlong T W,
    T.proj z ∈ (K a : Set X) ∩ compactComponentUnion (originalSharpBadLocus (n := n) W E) →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z

/-- The next finite block, with its full support and served task retained. -/
structure ComponentBlockChoice (W : Set X) (E : List (Set X)) (K : CompactExhaustion X)
    {j : ℕ} (p : ComponentBlockState W E K j) where
  Z : CMfd.{u} n
  S : BlowupTower p.Y Z
  test : IsGeoTestTower (geometricTemplate W []) (p.T.append S)
  full : IsGeoTestTower (geometricTemplate (univ : Set X) E) (p.T.append S)
  sharp : CurrentSharpCentres W E (p.T.append S)
  support : CentresOver (p.T.proj ⁻¹' compactComponentUnion (originalSharpBadLocus (n := n) W E)) S
  good : ∀ z ∈ strictAlong (p.T.append S) W,
    (p.T.append S).proj z ∈ (K j : Set X) ∩ compactComponentUnion (originalSharpBadLocus (n := n) W E) →
      normalCrossingsAt (n := n) (strictAlong (p.T.append S) W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (p.T.append S)).E z

variable (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
  (hdisj : Pairwise (fun C D : globalComponents (n := n) (originalSharpBadLocus (n := n) W E) =>
    Disjoint C.val D.val))
  (K : CompactExhaustion X)

/-- The actual task service supplies a block whose centres remain over the
union of compact bad components. -/
def chooseComponentBlock {j : ℕ} (p : ComponentBlockState W E K j) : ComponentBlockChoice W E K p := by
  apply Classical.choice
  obtain ⟨V,_hCompact,hSub,Z,S,hS,hSF,hSS,hOver,hGood⟩ :=
    exists_compact_component_task_after_prefix hn hW hE hdense hdisj (K j) (K.isCompact j)
      p.T p.test p.full p.sharp
  have hOverA : CentresOver
      (p.T.proj ⁻¹' compactComponentUnion (originalSharpBadLocus (n := n) W E)) S := by
    apply centresOver_of_inter_subset (T := S) ?_ hOver hOver
    intro z hz
    exact hSub hz.1
  exact ⟨⟨Z,S,hS,hSF,hSS,hOverA,hGood⟩⟩

/-- The successive actual finite histories serve the compact-component part
of every earlier compact task and have no centres over noncompact components. -/
def componentStates : (j : ℕ) → ComponentBlockState W E K j
  | 0 => ⟨X,.refl,trivial,trivial,trivial,trivial,by intro a ha; omega⟩
  | j+1 => by
    let p := componentStates j
    let q := chooseComponentBlock hn hW hE hdense hdisj K p
    refine ⟨q.Z,p.T.append q.S,q.test,q.full,q.sharp,?_,?_⟩
    · exact (centresOver_append_iff _ p.T q.S).mpr ⟨p.support,q.support⟩
    · intro a ha z hz hza
      exact q.good z hz ⟨K.subset (Nat.le_of_lt_succ ha) hza.1,hza.2⟩

/-- The selected endpoints are nested by the actual chosen sharp blocks. -/
theorem componentStates_extend (j : ℕ) :
    ∃ S : BlowupTower (componentStates hn hW hE hdense hdisj K j).Y
        (componentStates hn hW hE hdense hdisj K (j+1)).Y,
      (componentStates hn hW hE hdense hdisj K (j+1)).T =
        (componentStates hn hW hE hdense hdisj K j).T.append S := by
  refine ⟨(chooseComponentBlock hn hW hE hdense hdisj K
    (componentStates hn hW hE hdense hdisj K j)).S,rfl⟩
end
end Hironaka.HironakaG4CompactComponentBlocks
