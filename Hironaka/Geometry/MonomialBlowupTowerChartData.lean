import Hironaka.Geometry.MonomialBlowupTower
import Hironaka.Geometry.MonomialBlowupTowerCover
import Hironaka.Geometry.MonomialBlowupTowerAlgebra

/-!
# Genuine chart data for the actual global prefix blowup tower

The chart data are an internal induction invariant. The final producer
constructs them from the given coefficient list and its actual native tower.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerCharts

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration
open MonomialBlowupTower MonomialBlowupTowerBase BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- Actual spectrum chart maps and coordinate formulas, used only as an internally constructed invariant. -/
structure ChartData (l : List A) (n : ℕ) (P q : A) where
  I : Type
  factor : I → A
  factor_mem : ∀ i, factor i ∈ l
  factor_ne_zero : ∀ i, factor i ≠ 0
  scale : I → A
  scale_ne_zero : ∀ i, scale i ≠ 0
  divides_prefix : ∀ i, scale i * factor i ∣ P
  ringMap : ∀ i, Node A l.prod →ₐ[A] Node A (factor i)
  ringMap_u : ∀ i, ringMap i (coordinate l.prod 0) =
    algebraMap A (Node A (factor i)) (scale i) * coordinate (factor i) 0
  inclusion : ∀ i, Spec (CommRingCat.of (Node A (factor i))) ⟶ (tower l n).left
  inclusion_open : ∀ i, IsOpenImmersion (inclusion i)
  inclusion_structure : ∀ i, inclusion i ≫ (tower l n).hom =
    Spec.map (CommRingCat.ofHom (ringMap i).toRingHom)
  prefix_ne_zero : P ≠ 0
  remaining_ne_zero : q ≠ 0
  continuationRingMap : Node A l.prod →ₐ[A] Node A q
  continuationRingMap_u : continuationRingMap (coordinate l.prod 0) =
    algebraMap A (Node A q) P * coordinate q 0
  continuationInclusion : Spec (CommRingCat.of (Node A q)) ⟶ (tower l n).left
  continuation_open : IsOpenImmersion continuationInclusion
  continuation_structure : continuationInclusion ≫ (tower l n).hom =
    Spec.map (CommRingCat.ofHom continuationRingMap.toRingHom)
  covers : ∀ x : (tower l n).left,
    (∃ i, x ∈ (inclusion i).opensRange) ∨ x ∈ continuationInclusion.opensRange

namespace ChartData

variable {l : List A} {n : ℕ} {P q : A} (S : ChartData l n P q)

def source : Option S.I → Scheme.{u}
  | none => Spec (CommRingCat.of (Node A q))
  | some i => Spec (CommRingCat.of (Node A (S.factor i)))

def map : (i : Option S.I) → S.source i ⟶ (tower l n).left
  | none => S.continuationInclusion
  | some i => S.inclusion i

instance map_isOpenImmersion (i : Option S.I) : IsOpenImmersion (S.map i) := by
  cases i with
  | none => exact S.continuation_open
  | some i => exact S.inclusion_open i

/-- The invariant supplies a genuine native open cover of the actual global stage. -/
def openCover : (tower l n).left.OpenCover.{0} :=
  Scheme.Cover.mkOfCovers (Option S.I) S.source S.map (by
    intro x
    rcases S.covers x with ⟨i, hi⟩ | h
    · exact ⟨some i, hi⟩
    · exact ⟨none, h⟩)

@[simp]
theorem openCover_source_none : S.openCover.X none = Spec (CommRingCat.of (Node A q)) := rfl

@[simp]
theorem openCover_source_some (i : S.I) :
    S.openCover.X (some i) = Spec (CommRingCat.of (Node A (S.factor i))) := rfl

end ChartData

/-- The actual initial node has its genuine identity continuation chart and no finished charts. -/
def initialCharts [Nontrivial A] (l : List A) (hl : l.prod ≠ 0) : ChartData l 0 1 l.prod where
  I := Empty
  factor := Empty.elim
  factor_mem i := Empty.elim i
  factor_ne_zero i := Empty.elim i
  scale := Empty.elim
  scale_ne_zero i := Empty.elim i
  divides_prefix i := Empty.elim i
  ringMap i := Empty.elim i
  ringMap_u i := Empty.elim i
  inclusion i := Empty.elim i
  inclusion_open i := Empty.elim i
  inclusion_structure i := Empty.elim i
  prefix_ne_zero := one_ne_zero
  remaining_ne_zero := hl
  continuationRingMap := AlgHom.id A _
  continuationRingMap_u := by simp
  continuationInclusion := 𝟙 _
  continuation_open := inferInstance
  continuation_structure := by simp
  covers x := Or.inr ⟨x, rfl⟩

/-- Full ideal-sheaf pullback on an actual stage chart is the actual image of the original prefix ideal. -/
theorem stageCenter_comap_chart {l : List A} {n : ℕ} {q : A}
    (F : Node A l.prod →ₐ[A] Node A q)
    (f : Spec (CommRingCat.of (Node A q)) ⟶ (tower l n).left)
    (hf : f ≫ (tower l n).hom = Spec.map (CommRingCat.ofHom F.toRingHom)) :
    (stageCenter (originalCenter l) n).comap f =
      SpecIdealSheaf.specIdealSheaf (Node A q)
        ((prefixCenter l.prod (l.take (n + 1)).prod).map F.toRingHom) := by
  rw [stageCenter, ← Scheme.IdealSheafData.comap_comp, hf, originalCenter,
    SpecIdealSheaf.specIdealSheaf_comap]

end Hironaka.Geometry.MonomialBlowupTowerCharts
