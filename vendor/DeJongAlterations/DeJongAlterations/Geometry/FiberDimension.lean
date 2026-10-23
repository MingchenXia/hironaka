import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.KrullDimension

/-!
# Native scheme fiber dimension

We formulate the fiber-dimension upper-semicontinuity and componentwise generic lower-bound
statements using actual scheme-theoretic fibers and topological Krull dimension. The zeroth
closed level is proved for every universally closed morphism. Positive levels are empty for
locally quasi-finite morphisms; full upper semicontinuity additionally requires universal
closedness. The componentwise bound is proved for locally quasi-finite morphisms.
Positive-dimensional semicontinuity is not assumed or asserted as a theorem here.
-/

open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.FiberDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Dimension of the actual scheme-theoretic fiber; an empty fiber has dimension bottom. -/
def fiberDimension {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : WithBot ℕ∞ :=
  topologicalKrullDim (f.fiber s)

/-- The actual upper level set of the fiber dimension at a natural-number threshold. -/
def fiberDimensionGE {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) : Set S :=
  {s | (d : WithBot ℕ∞) ≤ fiberDimension f s}

/-- The native assertion in Section 2.7(b), without a caller-supplied certificate. -/
def FiberDimensionUpperSemicontinuous {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ d : ℕ, IsClosed (fiberDimensionGE f d)

/-- The componentwise assertion of Section 2.7(c), retaining every component of every fiber. -/
def EveryFiberComponentDimensionGEGeneric {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral S] : Prop :=
  ∀ (s : S) (Z : Set (f.fiber s)), Z ∈ irreducibleComponents (f.fiber s) →
    fiberDimension f (genericPoint S) ≤ topologicalKrullDim Z

/-- Nonnegative topological Krull dimension is equivalent to existence of a point. -/
theorem topologicalKrullDim_nonneg_iff (T : Type u) [TopologicalSpace T] :
    0 ≤ topologicalKrullDim T ↔ Nonempty T := by
  rw [topologicalKrullDim, Order.krullDim_nonneg_iff]
  constructor
  · rintro ⟨Z⟩
    exact Z.isIrreducible.nonempty.to_subtype.map Subtype.val
  · rintro ⟨x⟩
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

/-- A fiber has nonnegative dimension precisely at a point of the actual image. -/
theorem fiberDimension_nonneg_iff_mem_range {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    0 ≤ fiberDimension f s ↔ s ∈ Set.range f := by
  rw [fiberDimension, topologicalKrullDim_nonneg_iff]
  constructor
  · rintro ⟨x⟩
    exact ⟨(f.fiberHomeo s x).1, (f.fiberHomeo s x).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨(f.fiberHomeo s).symm ⟨x, hx⟩⟩

/-- The zeroth upper level is the actual image, including the empty-fiber convention. -/
theorem fiberDimensionGE_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    fiberDimensionGE f 0 = Set.range f := by
  ext s
  exact fiberDimension_nonneg_iff_mem_range f s

/-- The zeroth fiber-dimension level is closed for any universally closed morphism. -/
theorem isClosed_fiberDimensionGE_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyClosed f] : IsClosed (fiberDimensionGE f 0) := by
  rw [fiberDimensionGE_zero]
  exact f.isClosedMap.isClosed_range

/-- Actual fibers of a locally quasi-finite morphism have dimension at most zero. -/
theorem fiberDimension_le_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] (s : S) : fiberDimension f s ≤ 0 :=
  topologicalKrullDim_zero_of_discreteTopology (f.fiber s)

/-- Every strictly positive level is empty for a locally quasi-finite morphism. -/
theorem fiberDimensionGE_succ_eq_empty {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] (d : ℕ) : fiberDimensionGE f (d + 1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have h := hs.trans (fiberDimension_le_zero f s)
  have hpos : (0 : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.succ_pos d
  exact hpos.not_ge h

/-- Full fiber-dimension upper semicontinuity in the locally quasi-finite universally closed case. -/
theorem fiberDimensionUpperSemicontinuous_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyQuasiFinite f] [UniversallyClosed f] :
    FiberDimensionUpperSemicontinuous f := by
  intro d
  cases d with
  | zero => exact isClosed_fiberDimensionGE_zero f
  | succ d => rw [fiberDimensionGE_succ_eq_empty]; exact isClosed_empty

/-- Each actual irreducible component of a fiber has nonnegative dimension. -/
theorem fiberComponentDimension_nonneg {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (Z : Set (f.fiber s)) (hZ : Z ∈ irreducibleComponents (f.fiber s)) :
    0 ≤ topologicalKrullDim Z :=
  (topologicalKrullDim_nonneg_iff Z).mpr hZ.1.nonempty.to_subtype

/-- The generic lower bound holds component by component in relative dimension zero. -/
theorem everyFiberComponentDimensionGEGeneric_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [IsIntegral S] [LocallyQuasiFinite f] :
    EveryFiberComponentDimensionGEGeneric f := by
  intro s Z hZ
  exact (fiberDimension_le_zero f (genericPoint S)).trans (fiberComponentDimension_nonneg f s Z hZ)

end DeJongAlterations.Geometry.FiberDimension
