import Hironaka.Resolution.HironakaG4ActualMonomialPairWindows
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ExactMatrixWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HomogenizedGlueingTower BoundaryCount
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4ActualMonomialPairWindows HironakaG4MonomialTopStratum DivisorExponentAlong
variable {n : ℕ} {X : CMfd.{u} n}

def nonzeroColumns {r b : ℕ} (A : Fin r → Fin b → ℕ) : Finset (Fin b) :=
  Finset.univ.filter (fun j => ∃ i,A i j ≠ 0)

/-- The exact source-matrix fibre has the local germ of the born intersection
for precisely the columns containing a nonzero source entry. -/
theorem exact_matrix_window (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    {x : X} (hx : x ∈ N) :
    let A : X → Fin old.length → Fin born.length → ℕ := fun y i j =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) y
    ∃ U : Opens X,x ∈ U ∧ ∀ y ∈ N,y ∈ U →
      (A y=A x ↔ y ∈ memberInter born (nonzeroColumns (A x))) := by
  let A : X → Fin old.length → Fin born.length → ℕ := fun y i j =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) y
  let K : X → Finset (Fin born.length) := fun y => Finset.univ.filter fun j => y ∈ born.get j
  change ∃ U : Opens X,x ∈ U ∧ ∀ y ∈ N,y ∈ U → _
  obtain ⟨U,hxU,hMat,_hFinite,_hPair,_hAnalytic⟩ :=
    (exists_actual_old_monomial_pair_window hn hN hE hTr hdense).2 x hx
  refine ⟨U,hxU,?_⟩
  intro y hyN hyU
  have hA : A y=restrictIncidence (A x) (K y) := (hMat y hyN hyU).2
  change (A y=A x ↔ y ∈ memberInter born (nonzeroColumns (A x)))
  constructor
  · intro hEq j hj
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hj).2
    by_contra hNot
    have hjK : j ∉ K y := fun hh => hNot (Finset.mem_filter.mp hh).2
    have hval := congrFun (congrFun hA i) j
    rw [hEq] at hval
    simp [restrictIncidence,hjK] at hval
    exact hi hval
  · intro hMem
    rw [hA]
    funext i j
    by_cases hjK : j ∈ K y
    · simp [restrictIncidence,hjK]
    · have hj0 : A x i j=0 := by
        by_contra hne
        have hjS : j ∈ nonzeroColumns (A x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i,hne⟩⟩
        have hjY := hMem j hjS
        exact hjK (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjY⟩)
      simp [restrictIncidence,hjK,hj0]
end
end Hironaka.HironakaG4ExactMatrixWindow
