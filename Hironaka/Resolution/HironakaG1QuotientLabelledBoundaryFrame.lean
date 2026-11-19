import Hironaka.Resolution.HironakaActualIntrinsicWeightedBoundaryDerivations

/-!
# Whole original boundary image frames on arbitrary native head quotients

One actual ambient SNC reader is internally chosen before all head subsets,
native points, original labels, powers and literal old/born words. The actual
Cartier IMAGE ideals are retained, including nonradical, zero and unit cases.
No transverse/smooth head, common independent frame or history is assumed.

Blueprint FIRST: `hironaka-g1-quotient-labelled-boundary-frame.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1QuotientLabelledBoundaryFrame

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings SimultaneousNormalCrossings BlowupFlatCoordinates HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualIntrinsicCarrierDerivationTransport
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaActualIntrinsicWeightedBoundaryDerivations

variable {n : ℕ} {X : CMfd.{0} n}

/-- The full original label selects its ACTUAL native inclusion-stalk image,
or the retained unit slot. No reduced-support ideal is substituted. -/
def quotientBoundaryGerm (C : Set X) {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    {l : ℕ} (κ : Fin l → Option (Fin n)) (p : C) (hp : p.val ∈ flatDomain Φ)
    (i : Fin l) : ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier :=
  match κ i with
  | none => 1
  | some j => (actualSubspaceInclusion (n := n) C).stalkMap p
      (actualOriginalFunctionGerm p.val (flatCoord Φ j) (holomorphicAt_flatCoord Φ j hp))

private theorem originalGerm_isUnit_iff (p : X) (f : X → ℂ) (hf : HolomorphicAt n f p) :
    IsUnit (actualOriginalFunctionGerm p f hf) ↔ f p ≠ 0 := by
  rw [← isUnit_map_iff (actualStalkChartEquiv (n := n) p), actualOriginalFunctionGerm_chart,
    HolGerm.isUnit_iff_eval_ne_zero]
  change f ((chartAt (ComplexModel n) p).symm (0 + chartAt (ComplexModel n) p p)) ≠ 0 ↔ _
  rw [zero_add, (chartAt (ComplexModel n) p).left_inv (mem_chart_source _ p)]

/-- ONE reader/selector is internally chosen BEFORE ALL native head points
and full labels. Even singular, tangent or contained heads retain the entire
Cartier ideal IMAGE, with no radical or regular-generator conclusion. -/
theorem exists_quotient_labelled_boundary_frame {E : List (Set X)}
    (hE : IsSNCDivisor n E) (x : X) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n))
      (_hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ y ∈ flatDomain Φ, ∀ i : Fin E.length,
        y ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j y = 0) ∧
      ∀ (C : Set X) (p : C) (hp : p.val ∈ flatDomain Φ) (i : Fin E.length),
        actualLabelledBoundaryTraceIdeal C E i p =
            Ideal.span {quotientBoundaryGerm C Φ κ p hp i} ∧
          (IsUnit (quotientBoundaryGerm C Φ κ p hp i) ↔ p.val ∉ E.get i) ∧
          (C ⊆ E.get i → quotientBoundaryGerm C Φ κ p hp i = 0) := by
  obtain ⟨k, _hk, Φ, κ, hsrc, _τ, h0, _hκ, hinj, _hslots, _hzero, hcharts, _hpoint, _hall⟩ :=
    exists_actual_intrinsic_labelled_boundary_ideal_dictionary
      (N := (univ : Set X)) hE (isTransverse_univ_of_isSNCDivisor hE) x (mem_univ x)
  have hEq : ∀ y ∈ flatDomain Φ, ∀ i : Fin E.length,
      y ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j y = 0 :=
    fun y hy => (hcharts y hy).2
  refine ⟨Φ, κ, hsrc, h0, hinj, hEq, ?_⟩
  intro C p hp i
  cases hslot : κ i with
  | none =>
    have habs : ∀ y ∈ flatDomain Φ, y ∉ E.get i := by
      intro y hy hyE
      obtain ⟨j, hj, _⟩ := (hEq y hy i).mp hyE
      simp [hslot] at hj
    have hf : HolomorphicAt n (fun _ : X => (1 : ℂ)) p.val := holomorphicAt_const 1
    have hmem : (vanishingIdeal (n := n) (E.get i)).mem p.val (fun _ => (1 : ℂ)) := by
      refine ⟨hf, ?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp] with y hy hyE
      exact (habs y hy hyE).elim
    have hone : actualOriginalFunctionGerm p.val (fun _ : X => (1 : ℂ)) hf = 1 := by
      rw [← actual_ambient_structural_constant_original]
      simp
    have htop : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val = ⊤ := by
      apply (Ideal.eq_top_iff_one _).mpr
      rw [← hone]
      exact Ideal.subset_span ⟨fun _ => (1 : ℂ), hf, hmem, rfl⟩
    constructor
    · rw [actualLabelledBoundaryTraceIdeal, htop, Ideal.map_top]
      simp [quotientBoundaryGerm, hslot]
    · constructor
      · constructor
        · intro _
          exact habs p.val hp
        · intro _
          simp [quotientBoundaryGerm, hslot]
      · intro hCE
        exact (habs p.val hp (hCE p.property)).elim
  | some j =>
    have hflat : ∀ y ∈ flatDomain Φ, y ∈ E.get i ↔ flatCoord Φ j y = 0 := by
      intro y hy
      rw [hEq y hy i]
      constructor
      · rintro ⟨j', hj', hz⟩
        have he : j' = j := Option.some.inj (hj'.symm.trans hslot)
        simpa only [he] using hz
      · intro hz
        exact ⟨j, hslot, hz⟩
    constructor
    · rw [actualLabelledBoundaryTraceIdeal,
        actualWholeHyperplaneStalkIdeal_eq_span Φ hflat p.val hp, Ideal.map_span]
      simp only [Set.image_singleton, quotientBoundaryGerm, hslot]
      rfl
    · constructor
      · simp only [quotientBoundaryGerm, hslot]
        rw [isUnit_map_iff ((actualSubspaceInclusion (n := n) C).stalkMap p).hom,
          originalGerm_isUnit_iff]
        exact (not_congr (hflat p.val hp)).symm
      · intro hCE
        simp only [quotientBoundaryGerm, hslot]
        change actualOriginalFunctionGerm p.val (flatCoord Φ j)
          (holomorphicAt_flatCoord Φ j hp) ∈
            RingHom.ker ((actualSubspaceInclusion (n := n) C).stalkMap p).hom
        rw [actualSubspaceInclusion_stalk_kernel]
        apply Ideal.subset_span
        refine ⟨flatCoord Φ j, holomorphicAt_flatCoord Φ j hp, ?_, rfl⟩
        refine ⟨holomorphicAt_flatCoord Φ j hp, ?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp] with y hy hyC
        exact (hflat y hy).mp (hCE hyC)

/-- The SAME internally chosen reader precedes ALL original weight families
and literal old/born words. Whole image ideals retain zero and unit slots. -/
theorem exists_quotient_weighted_boundary_frame {E : List (Set X)}
    (hE : IsSNCDivisor n E) (x : X) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (κ : Fin E.length → Option (Fin n))
      (_hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target),
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Set.InjOn κ {i | x ∈ E.get i} ∧
      (∀ y ∈ flatDomain Φ, ∀ i : Fin E.length,
        y ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j y = 0) ∧
      ∀ (C : Set X) (p : C) (hp : p.val ∈ flatDomain Φ),
        (∀ i : Fin E.length,
          actualLabelledBoundaryTraceIdeal C E i p = Ideal.span {quotientBoundaryGerm C Φ κ p hp i} ∧
            (IsUnit (quotientBoundaryGerm C Φ κ p hp i) ↔ p.val ∉ E.get i) ∧
            (C ⊆ E.get i → quotientBoundaryGerm C Φ κ p hp i = 0)) ∧
        (∀ m : Fin E.length → ℕ,
          actualWeightedBoundaryTraceIdeal C E m p =
            Ideal.span {∏ i : Fin E.length, (quotientBoundaryGerm C Φ κ p hp i) ^ (m i)}) ∧
        (∀ w : List (Fin E.length),
          Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap p).hom
              ((w.map (fun i => actualWholeSheafStalkIdeal
                (vanishingIdeal (n := n) (E.get i)) p.val)).prod) =
              (w.map (fun i => actualLabelledBoundaryTraceIdeal C E i p)).prod ∧
            (w.map (fun i => actualLabelledBoundaryTraceIdeal C E i p)).prod =
            Ideal.span {(w.map (quotientBoundaryGerm C Φ κ p hp)).prod}) := by
  obtain ⟨Φ, κ, hsrc, h0, hinj, hEq, hall⟩ := exists_quotient_labelled_boundary_frame hE x
  refine ⟨Φ, κ, hsrc, h0, hinj, hEq, ?_⟩
  intro C p hp
  have hspan := hall C p hp
  refine ⟨hspan, ?_, ?_⟩
  · intro m
    rw [weightedBoundaryTraceIdeal_eq_prod]
    calc
      _ = ∏ i : Fin E.length, Ideal.span {(quotientBoundaryGerm C Φ κ p hp i) ^ (m i)} := by
        apply Finset.prod_congr rfl
        intro i _
        rw [(hspan i).1, Ideal.span_singleton_pow]
      _ = _ := Ideal.prod_span_singleton Finset.univ _
  · intro w
    constructor
    · change (Ideal.mapHom ((actualSubspaceInclusion (n := n) C).stalkMap p).hom)
        ((w.map (fun i => actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val)).prod) = _
      rw [map_list_prod]
      simp only [List.map_map, Function.comp_def, Ideal.mapHom_apply, actualLabelledBoundaryTraceIdeal]
    · induction w with
      | nil => simp
      | cons i w ih =>
        simp only [List.map_cons, List.prod_cons, (hspan i).1, ih, Ideal.span_singleton_mul_span_singleton]

end
end Hironaka.HironakaG1QuotientLabelledBoundaryFrame
