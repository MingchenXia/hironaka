import Hironaka.Resolution.HironakaG11NoncontainingAbstractBlowup
import Hironaka.Resolution.HironakaG11NoncontainingOpen
import Hironaka.Resolution.HironakaG11HistoryDenseEscape

set_option autoImplicit false

/-!
# Local noncontaining-germ history at an arbitrary blowup

A noncontaining normal-crossings centre germ produces actual source and
inverse-blowup opens with dense trace escape; that escape propagates along
any identified avoiding test history.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11NoncontainingAbstractLocalHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupSpaceTangent BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong HironakaG11InvBMLower
  HironakaG11NoncontainingOpen HironakaG11HistoryDenseEscape

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- Local noncontaining-germ density on an actual arbitrary blowup. -/
theorem exists_local_trace_dense_of_noncontaining_germ
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) {p : Y} (hpC : π p ∈ C) (hpH : π p ∈ E.get i)
    (hnot : ¬ ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ E.get i) :
    ∃ (W : Opens X) (V : Opens Y), π p ∈ W ∧ (V : Set Y) = π ⁻¹' W ∧ p ∈ V ∧
      ((Subtype.val : V → Y) ⁻¹' (geoStrictTransform π C P ∩ (π ⁻¹' C))) ⊆
        closure (((Subtype.val : V → Y) ⁻¹' (geoStrictTransform π C P ∩ (π ⁻¹' C))) \
          ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i))) := by
  have hnear := eventually_noncontaining_germ_of_normalCrossings (Fact.out : IsClosedSubmanifold n C)
    hcross hpC i hpH hnot
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hnear
  let W' : Opens X := ⟨W, hWopen⟩
  let V : Opens Y := ⟨π ⁻¹' W, hWopen.preimage hπ.contMDiff.continuous⟩
  refine ⟨W', V, hpW, rfl, hpW, ?_⟩
  intro q hq
  have hqC : π (q : Y) ∈ C := hq.2
  have hqW : π (q : Y) ∈ W := q.2
  have hqcl : (q : Y) ∈ closure ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C (E.get i)) := by
    by_cases hqH : π (q : Y) ∈ E.get i
    · have hf := HironakaG11NoncontainingAbstractBlowup.frequently_strict_not_boundary_of_noncontaining_germ
        hπ hCint hP hCP hE hcross i hq.1 hqC hqH (hWsub hqW hqC)
      rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨r, ⟨hrC, hrP, hrH⟩, hrO⟩ := (hf.and_eventually hO).exists
      exact ⟨r, hrO, ⟨⟨hrP, hrC⟩, hrH⟩⟩
    · apply subset_closure
      refine ⟨hq, ?_⟩
      intro hqHst
      exact hqH (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (hE.1 _ (List.get_mem E i)) hqHst)
  have hEq : (Subtype.val : V → Y) ⁻¹' closure
      ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C (E.get i)) =
      closure ((Subtype.val : V → Y) ⁻¹'
        ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C (E.get i))) :=
    V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
  have hpre : q ∈ (Subtype.val : V → Y) ⁻¹'
      closure ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C (E.get i)) := hqcl
  rw [hEq] at hpre
  simpa only [preimage_sdiff] using hpre

/-- The local source and inverse-blowup opens give the actual trace-density
input to every identified later avoiding test history. -/
theorem exists_local_avoiding_history_nondiv
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) {p : Y} (hpC : π p ∈ C) (hpH : π p ∈ E.get i)
    (hnot : ¬ ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ E.get i) :
    ∃ (W : Opens X) (V : Opens Y), π p ∈ W ∧ (V : Set Y) = π ⁻¹' W ∧ p ∈ V ∧
      ∀ (M : MarkedIdeal n (CMfd.of (n := n) V)), M.IsWellFormed →
        ∀ (j : Fin M.E.length), M.N = (Subtype.val : V → Y) ⁻¹' geoStrictTransform π C P →
          M.E.get j = (Subtype.val : V → Y) ⁻¹' (π ⁻¹' C) →
          ∀ {Z : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) V) Z), IsGeoTestTower M T →
            RestrictEmptyTower.CentresAvoid
              ⟨((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i))ᶜ,
                (isClosed_closure.preimage continuous_subtype_val).isOpen_compl⟩ T →
            ∀ {S : List (Set Z)}, (∀ K ∈ S, IsClosed K) →
              strictAlong T ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i)) ∈ S →
              ∀ (e : ℕ) {z : Z}, z ∈ (geoTransformAlong M T).N ∩ strictAlong T (M.E.get j) →
                ¬ IsDivNearAlong n (geoTransformAlong M T).N (exceptionalTermBM (n := n) S e)
                  (strictAlong T (M.E.get j)) 1 z := by
  obtain ⟨W, V, hpW, hV, hpV, hdense⟩ :=
    exists_local_trace_dense_of_noncontaining_germ hπ hCint hP hCP hE hcross i hpC hpH hnot
  refine ⟨W, V, hpW, hV, hpV, ?_⟩
  intro M hM j hN hD Z T hT hAvoid S hS hmem e z hz
  have hHclosed : IsClosed ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i)) :=
    isClosed_closure.preimage continuous_subtype_val
  have hDense' : M.N ∩ M.E.get j ⊆ closure ((M.N ∩ M.E.get j) \
      ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C (E.get i))) := by
    rw [hN, hD, ← preimage_inter]
    exact hdense
  exact not_isDivNearAlong_exceptionalTerm_of_avoiding_history M hM j _ hHclosed hDense'
    T hT hAvoid hS hmem e hz

end

end Hironaka.HironakaG11NoncontainingAbstractLocalHistory
