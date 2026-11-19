import Hironaka.Geometry.MonomialBlowupTowerBoundaryLastChart

/-! A genuine finished-node-only cover of the final nonempty finite tower. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerBoundaryCover

open Algebra.NodeBlowupChart MonomialBlowupTower MonomialBlowupTowerBase
open MonomialBlowupTowerCharts MonomialBlowupTowerRegular BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The literal coefficient morphism of an actual node. -/
def nodeToBase (c : A) : Spec (CommRingCat.of (Node A c)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Node A c)))

/-- Actual node algebra maps preserve the literal coefficient morphisms. -/
theorem coefficient_triangle {l : List A} {n : ℕ} {q : A}
    (F : Node A l.prod →ₐ[A] Node A q)
    (f : Spec (CommRingCat.of (Node A q)) ⟶ (tower l n).left)
    (hf : f ≫ (tower l n).hom = Spec.map (CommRingCat.ofHom F.toRingHom)) :
    f ≫ (tower l n).hom ≫ nodeToBase l.prod = nodeToBase q := by
  rw [← Category.assoc, hf]
  dsimp only [nodeToBase]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext F.commutes

/-- Internal data for a genuine global open cover consisting only of finished nodes. -/
structure FinishedCoverData (l : List A) (n : ℕ) where
  I : Type
  factor : I → A
  factor_mem : ∀ i, factor i ∈ l
  inclusion : ∀ i, Spec (CommRingCat.of (Node A (factor i))) ⟶ (tower l n).left
  inclusion_open : ∀ i, IsOpenImmersion (inclusion i)
  toBase : ∀ i, inclusion i ≫ (tower l n).hom ≫ nodeToBase l.prod = nodeToBase (factor i)
  covers : ∀ x : (tower l n).left, ∃ i, x ∈ (inclusion i).opensRange

namespace FinishedCoverData

variable {l : List A} {n : ℕ} (S : FinishedCoverData l n)

instance inclusion_isOpenImmersion (i : S.I) : IsOpenImmersion (S.inclusion i) := S.inclusion_open i

/-- The actual native cover constructed from these internally produced finished charts. -/
def openCover : (tower l n).left.OpenCover.{0} :=
  Scheme.Cover.mkOfCovers S.I (fun i ↦ Spec (CommRingCat.of (Node A (S.factor i))))
    S.inclusion S.covers

end FinishedCoverData

variable [IsDomain A]

namespace LastStep

variable {l : List A} {n : ℕ} {P t : A}
    (S : ChartData l n P (t * ([] : List A).prod)) [Fact (t ≠ 0)]

local instance : Fact ((1 : A) ≠ 0) := ⟨one_ne_zero⟩
local instance : Fact (([] : List A).prod ≠ 0) := ⟨one_ne_zero⟩
local instance (i : S.I) : IsOpenImmersion (S.inclusion i) := S.inclusion_open i
local instance : IsOpenImmersion S.continuationInclusion := S.continuation_open

/-- The new finished node covers the whole inverse image of the old continuation chart. -/
theorem fresh_opensRange (hprefix : (l.take (n + 1)).prod = P * t) :
    (StepContext.freshInclusion S hprefix).opensRange =
      blowupStructure (StepContext.center (l := l) (n := n)) ⁻¹ᵁ
        S.continuationInclusion.opensRange := by
  change (uChartInclusion t 1 ≫
    ((StepContext.continuationIso S).inv ≫ StepContext.continuationGlobalMap S hprefix)).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    StepContext.continuationGlobalMap_opensRange]

/-- Exact range coverage by old finished nodes and the new last finished node. -/
theorem covers (hprefix : (l.take (n + 1)).prod = P * t) :
    ∀ y : blowup (StepContext.center (l := l) (n := n)),
      (∃ i, y ∈ (StepContext.oldInclusion S hprefix i).opensRange) ∨
        y ∈ (StepContext.freshInclusion S hprefix).opensRange := by
  intro y
  rcases S.covers (blowupStructure (StepContext.center (l := l) (n := n)) y) with ⟨i, hi⟩ | hc
  · left
    exact ⟨i, by rw [StepContext.oldInclusion_opensRange]; exact hi⟩
  · right
    rw [fresh_opensRange]
    exact hc

include S in
/-- The last actual global successor admits a finished-only cover. -/
theorem nonempty_finished (hprefix : (l.take (n + 1)).prod = P * t) (htmem : t ∈ l) :
    Nonempty (FinishedCoverData l (n + 1)) := by
  have hcov := covers S hprefix
  let fresh := StepContext.freshInclusion S hprefix
  let old := StepContext.oldInclusion S hprefix
  refine ⟨{
    I := Option S.I
    factor := fun i ↦ i.elim t S.factor
    factor_mem := ?_
    inclusion := fun i ↦ by
      cases i with
      | none => exact fresh
      | some i => exact old i
    inclusion_open := ?_
    toBase := ?_
    covers := ?_ }⟩
  · intro i
    cases i with
    | none => exact htmem
    | some i => exact S.factor_mem i
  · intro i
    cases i <;> dsimp only [fresh, old] <;> infer_instance
  · intro i
    cases i with
    | none =>
      apply coefficient_triangle ((uChartOriginalMap t 1).comp S.continuationRingMap)
      change StepContext.freshInclusion S hprefix ≫
        (blowupStructure (StepContext.center (l := l) (n := n)) ≫ (tower l n).hom) = _
      rw [← Category.assoc, StepContext.freshInclusion_structure, Category.assoc,
        S.continuation_structure, ← Spec.map_comp]
      rfl
    | some i =>
      apply coefficient_triangle (S.ringMap i)
      change StepContext.oldInclusion S hprefix i ≫
        (blowupStructure (StepContext.center (l := l) (n := n)) ≫ (tower l n).hom) = _
      rw [← Category.assoc, StepContext.oldInclusion_structure, S.inclusion_structure]
  · intro y
    rcases hcov y with ⟨i, hi⟩ | hf
    · exact ⟨some i, hi⟩
    · exact ⟨none, hf⟩

end LastStep

/-- Every nonempty actual finite prefix tower has its internally constructed finished-only cover. -/
theorem nonempty_finishedCover (l : List A) (hl : (0 : A) ∉ l) (hne : l ≠ []) :
    Nonempty (FinishedCoverData l l.length) := by
  induction l using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton a t ih =>
    have htmem : t ∈ a ++ [t] := by simp
    have ht : t ≠ 0 := by
      intro h
      exact hl (h ▸ htmem)
    let : Fact (t ≠ 0) := ⟨ht⟩
    obtain ⟨S⟩ : Nonempty (ChartData (a ++ [t]) a.length a.prod (t * ([] : List A).prod)) := by
      simpa using nonempty_charts (a ++ [t]) hl a [t] rfl
    have hprefix : ((a ++ [t]).take (a.length + 1)).prod = a.prod * t :=
      nextPrefix_prod a t []
    simpa only [List.length_append, List.length_singleton] using
      LastStep.nonempty_finished S hprefix htmem

end Hironaka.Geometry.MonomialBlowupTowerBoundaryCover
