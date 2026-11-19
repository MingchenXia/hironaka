import Hironaka.Resolution.HironakaG8P1ArcTower
import Hironaka.Invariant.RestrictEmptyTower

/-!
# The arc test away from the original horizontal divisor

Every centre of the actual arc family lies over the original horizontal
divisor. The product of any initial set with the line is the closure of its
part away from that divisor. These are the two arc-specific inputs to the
strict-transform closure calculation in the first-order arc-chart argument.

Source: Bierstone--Milman 2008, proof of Theorem 6.1; the arc centres are the
successive lifts of the point at parameter zero.

These are prerequisites for the first-order arc-chart argument. Its tangent
comparison and the original Hironaka goals require further work.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open scoped Hironaka.ProductComplexManifold

universe u

namespace Hironaka.HironakaG8P1ArcOffHorizontal

open Hironaka.BlowupSequences BlowupTowers BlowupConstruction
  HironakaActualProjectionTestRecord HironakaG8P1ArcTower RestrictEmptyTower

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- The original open part of the product on which the line parameter is nonzero. -/
def offHorizontal (X : CMfd.{u} n) : Opens (projectionAmbient X) :=
  ⟨{p | p.2 0 ≠ 0},
    isOpen_ne_fun ((PiLp.continuous_apply 2 _ 0).comp continuous_snd) continuous_const⟩

private theorem model_one_ne_zero_iff (v : ComplexModel 1) :
    v ≠ 0 ↔ v 0 ≠ 0 := by
  constructor
  · intro hv hz
    apply hv
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    exact hz
  · intro hv hz
    apply hv
    rw [hz]
    rfl

/-- An initial product set is dense in itself away from the horizontal divisor.
No regularity or nonemptiness assumption on the initial set is needed. -/
theorem product_subset_closure_offHorizontal (A : Set X) :
    (Prod.fst : projectionAmbient X → X) ⁻¹' A ⊆
      closure (((Prod.fst : projectionAmbient X → X) ⁻¹' A) ∩
        (offHorizontal X : Set (projectionAmbient X))) := by
  have hpart : ((Prod.fst : projectionAmbient X → X) ⁻¹' A) ∩
      (offHorizontal X : Set (projectionAmbient X)) =
      A ×ˢ ({0}ᶜ : Set (ComplexModel 1)) := by
    ext p
    change (p.1 ∈ A ∧ p.2 0 ≠ 0) ↔ (p.1 ∈ A ∧ p.2 ∉ ({0} : Set (ComplexModel 1)))
    simpa only [mem_singleton_iff] using
      and_congr_right (fun _ => (model_one_ne_zero_iff p.2).symm)
  rw [hpart, closure_prod_eq, closure_compl_singleton]
  intro p hp
  exact ⟨subset_closure hp, mem_univ _⟩

/-- A point blowup above line parameter zero preserves avoidance of the
original nonzero-parameter open. -/
theorem centresAvoid_offHorizontal_step {Y Z : CMfd.{u} (n+1)}
    (T : BlowupTower (projectionAmbient X) Y)
    (hT : CentresAvoid (offHorizontal X) T) {z : Y}
    (hz : (T.proj z).2 0 = 0) {π : Z → Y}
    (hπ : IsBlowupAlong (n+1) ({z} : Set Y) π) :
    CentresAvoid (offHorizontal X) (T.step ({z} : Set Y) π hπ) := by
  refine ⟨hT, Set.disjoint_left.mpr ?_⟩
  intro y hy hyO
  have hyz : y = z := mem_singleton_iff.mp hy
  subst hyz
  exact hyO hz

/-- Every centre of the canonical arc test lies over the original horizontal
divisor, including the initial point blowup and all subsequent arc points. -/
theorem centresAvoid_offHorizontal_arcFamily {x : X}
    {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))}
    {S : ℕ → ArcStage n (arcY1 x)} (hS : IsArcFamily x hπ1 S) :
    ∀ r, CentresAvoid (offHorizontal X) ((arcA1 x hπ1).append (S r).R) := by
  have hbase : CentresAvoid (offHorizontal X) (arcA1 x hπ1) :=
    centresAvoid_offHorizontal_step (X := X) BlowupTower.refl trivial (by rfl) hπ1
  intro r
  induction r with
  | zero =>
    have hZ := hS.zero_Z
    have hR := hS.zero_R
    generalize S 0 = s at hZ hR ⊢
    obtain ⟨Zs, Rs, es, zs⟩ := s
    dsimp only at hZ hR ⊢
    subst hZ
    obtain rfl := eq_of_heq hR
    exact hbase
  | succ r ih =>
    have hz := (hS.arc r).proj_eq.2
    obtain ⟨hπ, hZt, hRt⟩ := hS.succ r
    generalize S (r + 1) = t at hZt hRt ⊢
    generalize S r = s at ih hz hπ hZt hRt
    obtain ⟨Zs, Rs, es, zs⟩ := s
    obtain ⟨Zt, Rt, et, zt⟩ := t
    dsimp only at ih hz hπ hZt hRt ⊢
    subst hZt
    obtain rfl := eq_of_heq hRt
    exact centresAvoid_offHorizontal_step ((arcA1 x hπ1).append Rs) ih hz hπ

end

end Hironaka.HironakaG8P1ArcOffHorizontal
