import Hironaka.Resolution.HironakaG11ContainingGermAbstractBlowup
import Hironaka.Resolution.HironakaG11TangentNoncontainmentOpen
import Hironaka.Resolution.HironakaG11HistoryDenseEscape

set_option autoImplicit false

/-!
# Local containing-germ history at an arbitrary blowup

A tangent noncontainment and centre containment as germs at one birth point
give an actual source open and its inverse blowup open. On that open the
arbitrary blowup's strict-carrier trace has dense complement of the old
strict member; the density propagates through any avoiding test history.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11ContainingAbstractLocalHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupSpaceTangent BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong HironakaG11InvBMLower
  HironakaG11TangentNoncontainmentOpen HironakaG11HistoryDenseEscape

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- Local containing-germ density on an actual arbitrary blowup, with the
native construction's empty-interior condition kept explicit. -/
theorem exists_local_trace_dense_of_containing_germ
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y} (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (hnt : ¬ tangentSpace n P (π p) ≤ tangentSpace n H (π p)) :
    ∃ (W : Opens X) (V : Opens Y), π p ∈ W ∧ (V : Set Y) = π ⁻¹' W ∧ p ∈ V ∧
      ((Subtype.val : V → Y) ⁻¹' (geoStrictTransform π C P ∩ (π ⁻¹' C))) ⊆
        closure (((Subtype.val : V → Y) ⁻¹' (geoStrictTransform π C P ∩ (π ⁻¹' C))) \
          ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H)) := by
  have hnear := (eventually_tangent_noncontainment hP (hCP hpC) hnt).and hCH.eventually_nhds
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hnear
  let W' : Opens X := ⟨W, hWopen⟩
  let V : Opens Y := ⟨π ⁻¹' W, hWopen.preimage hπ.contMDiff.continuous⟩
  refine ⟨W', V, hpW, rfl, hpW, ?_⟩
  intro q hq
  have hqC : π (q : Y) ∈ C := hq.2
  have hqW : π (q : Y) ∈ W := q.2
  have hqnt := (hWsub hqW).1 (hCP hqC)
  have hqCH := (hWsub hqW).2
  have hf := HironakaG11ContainingGermAbstractBlowup.frequently_strict_not_boundary_of_containing_germ
    hπ hCint hP hCP hq.1 hqC hqCH hqnt
  have hqcl : (q : Y) ∈ closure ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C H) := by
    rw [mem_closure_iff_nhds]
    intro O hO
    obtain ⟨r, ⟨hrbase, hrP, hrH⟩, hrO⟩ := (hf.and_eventually hO).exists
    have hrC : π r ∈ C := hrbase ▸ hqC
    exact ⟨r, hrO, ⟨⟨hrP, hrC⟩, hrH⟩⟩
  have hEq : (Subtype.val : V → Y) ⁻¹' closure ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C H) =
      closure ((Subtype.val : V → Y) ⁻¹' ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C H)) :=
    V.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
  have hpre : q ∈ (Subtype.val : V → Y) ⁻¹'
      closure ((geoStrictTransform π C P ∩ (π ⁻¹' C)) \ geoStrictTransform π C H) := hqcl
  rw [hEq] at hpre
  simpa only [preimage_sdiff] using hpre

/-- The local source and inverse blowup opens give a dense-escape input to
every later well-formed avoiding test history with the actual restricted
carrier and born divisor. -/
theorem exists_local_avoiding_history_nondiv
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y} (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (hnt : ¬ tangentSpace n P (π p) ≤ tangentSpace n H (π p)) :
    ∃ (W : Opens X) (V : Opens Y), π p ∈ W ∧ (V : Set Y) = π ⁻¹' W ∧ p ∈ V ∧
      ∀ (M : MarkedIdeal n (CMfd.of (n := n) V)), M.IsWellFormed →
        ∀ (j : Fin M.E.length), M.N = (Subtype.val : V → Y) ⁻¹' geoStrictTransform π C P →
          M.E.get j = (Subtype.val : V → Y) ⁻¹' (π ⁻¹' C) →
          ∀ {Z : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) V) Z), IsGeoTestTower M T →
            RestrictEmptyTower.CentresAvoid
              ⟨((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H)ᶜ,
                (isClosed_closure.preimage continuous_subtype_val).isOpen_compl⟩ T →
            ∀ {S : List (Set Z)}, (∀ K ∈ S, IsClosed K) →
              strictAlong T ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H) ∈ S →
              ∀ (e : ℕ) {z : Z}, z ∈ (geoTransformAlong M T).N ∩ strictAlong T (M.E.get j) →
                ¬ IsDivNearAlong n (geoTransformAlong M T).N (exceptionalTermBM (n := n) S e)
                  (strictAlong T (M.E.get j)) 1 z := by
  obtain ⟨W, V, hpW, hV, hpV, hdense⟩ :=
    exists_local_trace_dense_of_containing_germ hπ hCint hP hCP hpC hCH hnt
  refine ⟨W, V, hpW, hV, hpV, ?_⟩
  intro M hM j hN hD Z T hT hAvoid S hS hmem e z hz
  have hHclosed : IsClosed ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H) :=
    isClosed_closure.preimage continuous_subtype_val
  have hDense' : M.N ∩ M.E.get j ⊆ closure ((M.N ∩ M.E.get j) \
      ((Subtype.val : V → Y) ⁻¹' geoStrictTransform π C H)) := by
    rw [hN, hD, ← preimage_inter]
    exact hdense
  exact not_isDivNearAlong_exceptionalTerm_of_avoiding_history M hM j _ hHclosed hDense'
    T hT hAvoid hS hmem e hz

end

end Hironaka.HironakaG11ContainingAbstractLocalHistory
