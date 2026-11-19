import Hironaka.Resolution.HironakaG1SNCReaderNormalization
import Hironaka.Resolution.HironakaG1RelativeBoundaryUnitsOnGraph

/-! Unit comparisons for the exact coordinates of any fixed relative SNC reader. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1FixedReaderBoundaryUnits
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaActualIntrinsicCarrierDerivationTransport
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1QuotientLabelledBoundaryFrame
  HironakaG1RelativeBoundaryUnitLifts HironakaG1RelativeBoundaryUnitsOnGraph
  HironakaG1SNCReaderNormalization

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}

private abbrev ambient (p : M) := actualComplexStructureStalk (n := n) p
private abbrev native (C : Set M) (p : C) := ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier

/-- The boundary dictionary suffices to identify the whole trace ideal
for a fixed chart and selector, including absent labels. -/
theorem labelled_span_of_member
    (C : Set M) (p : C) {E : List (Set M)} (i : Fin E.length)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.val p.val))
    {k : ℕ} (κ : Fin k → Option (Fin n)) (l : Fin k)
    (hmem : ∀ x ∈ flatDomain Φ, x ∈ E.get i ↔ ∃ j, κ l = some j ∧ flatCoord Φ j x = 0) :
    actualLabelledBoundaryTraceIdeal C E i p =
      Ideal.span {quotientBoundaryGerm C Φ κ p (mem_flatDomain_self Φ) l} := by
  cases hs : κ l with
  | none =>
    have hmiss : ∀ x ∈ flatDomain Φ, x ∉ E.get i := by
      intro x hx he
      obtain ⟨j, hj, _⟩ := (hmem x hx).mp he
      rw [hs] at hj
      cases hj
    have hhol : HolomorphicAt n (fun _ : M => (1 : ℂ)) p.val := holomorphicAt_const 1
    have hvan : (vanishingIdeal (n := n) (E.get i)).mem p.val (fun _ : M => (1 : ℂ)) := by
      refine ⟨hhol, ?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with x hx he
      exact (hmiss x hx he).elim
    have hone : actualOriginalFunctionGerm p.val (fun _ : M => (1 : ℂ)) hhol = 1 := by
      rw [← actual_ambient_structural_constant_original]
      rw [map_one]
      exact map_one ((ambientPointMap n M).stalkMap p.val).hom
    have htop : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr (hone ▸ Ideal.subset_span
        ⟨fun _ : M => (1 : ℂ), hhol, hvan, rfl⟩)
    rw [actualLabelledBoundaryTraceIdeal, htop, Ideal.map_top]
    simp [quotientBoundaryGerm, hs]
  | some j =>
    have hh : ∀ x ∈ flatDomain Φ, x ∈ E.get i ↔ flatCoord Φ j x = 0 := by
      intro x hx
      rw [hmem x hx]
      constructor
      · rintro ⟨q, hq, hz⟩
        rw [hs] at hq
        simpa only [← Option.some.inj hq] using hz
      · exact fun hz => ⟨j, hs, hz⟩
    rw [actualLabelledBoundaryTraceIdeal, actualWholeHyperplaneStalkIdeal_eq_span Φ hh p.val
      (mem_flatDomain_self Φ), Ideal.map_span]
    simp only [Set.image_singleton, quotientBoundaryGerm, hs]

variable {C : Set M} {D : Set N}
  (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
  (p : C) {E : List (Set M)} {F : List (Set N)} {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p.val (e.hom.base p).val E F τ)

/-- Original source selector of this exact normalized reader. -/
def sourceSelector (i : Fin E.length) : Option (Fin n) :=
  (R.slot i).map (fun j => R.σ₁ (j.castAdd R.a))

/-- Original target selector, indexed by the same paired original labels. -/
def targetSelector (i : Fin E.length) : Option (Fin m) :=
  (R.slot i).map (fun j => R.σ₂ (j.castAdd R.b))

private theorem option_member {r d : ℕ} {s : Option (Fin r)} (α : Fin r → Fin d) (f : Fin d → ℂ) :
    (∃ j, s = some j ∧ f (α j) = 0) ↔
      ∃ j, s.map α = some j ∧ f j = 0 := by
  cases s with
  | none => simp
  | some j => simp

/-- The exact source slot of the fixed reader generates the actual trace ideal. -/
theorem source_labelled_trace_span (i : Fin E.length) :
    actualLabelledBoundaryTraceIdeal C E i p =
      Ideal.span {quotientBoundaryGerm C R.Φ₁ (sourceSelector e p R) p
        (mem_flatDomain_self R.Φ₁) i} := by
  apply labelled_span_of_member
  intro x hx
  exact (R.member₁ x hx i).trans (option_member _ _)

/-- The exact target slot of the fixed reader generates the paired actual trace ideal. -/
theorem target_labelled_trace_span (i : Fin E.length) :
    actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p) =
      Ideal.span {quotientBoundaryGerm D R.Φ₂ (targetSelector e p R) (e.hom.base p)
        (mem_flatDomain_self R.Φ₂) i} := by
  apply labelled_span_of_member
  intro x hx
  exact (R.member₂ x hx i).trans (option_member _ _)

set_option maxHeartbeats 700000 in
/-- The actual ratio law holds for the exact normalized coordinates of a
fixed reader. Every original label keeps a nonvanishing ambient unit on
both sides, and both values agree along the paired native graph. -/
theorem fixed_reader_units_on_graph
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hI : ∀ i : Fin E.length, Ideal.map (e.hom.stalkMap p).hom
      (actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p)) =
        actualLabelledBoundaryTraceIdeal C E i p) :
    ∃ (U : Opens M) (V : Opens N) (a : Fin E.length → M → ℂ) (b : Fin E.length → N → ℂ),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧
      (U : Set M) ⊆ flatDomain R.Φ₁ ∧ (V : Set N) ⊆ flatDomain R.Φ₂ ∧
      (∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x ∧ a i x ≠ 0) ∧
      (∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y ∧ b i y ≠ 0) ∧
      ∀ x : C, x.val ∈ U → (e.hom.base x).val ∈ V ∧
        ∀ i, a i x.val = b i (e.hom.base x).val ∧
          labelledFunction R.Φ₂ (targetSelector e p R) i (e.hom.base x).val =
            a i x.val * labelledFunction R.Φ₁ (sourceSelector e p R) i x.val := by
  classical
  let p' := e.hom.base p
  let ε := (asIso (e.hom.stalkMap p)).commRingCatIsoToRingEquiv
  let : IsLocalRing (native C p) := actualSubspaceStalk_isLocalRing (n := n) C p
  let f := labelledFunction R.Φ₁ (sourceSelector e p R)
  let g := labelledFunction R.Φ₂ (targetSelector e p R)
  have hf (i : Fin E.length) := labelledFunction_holomorphicAt R.Φ₁ (sourceSelector e p R) i
    (mem_flatDomain_self R.Φ₁)
  have hg (i : Fin E.length) := labelledFunction_holomorphicAt R.Φ₂ (targetSelector e p R) i
    (mem_flatDomain_self R.Φ₂)
  let f₀ i := quotientBoundaryGerm C R.Φ₁ (sourceSelector e p R) p (mem_flatDomain_self R.Φ₁) i
  let g₀ i := quotientBoundaryGerm D R.Φ₂ (targetSelector e p R) p' (mem_flatDomain_self R.Φ₂) i
  have hSpan (i : Fin E.length) : Ideal.span {f₀ i} = Ideal.span {ε (g₀ i)} := by
    have h := hI i
    rw [source_labelled_trace_span e p R, target_labelled_trace_span e p R, Ideal.map_span,
      Set.image_singleton] at h
    exact h.symm
  choose r hr using fun i => exists_unit_mul_of_span_eq (f₀ i) (ε (g₀ i)) (hSpan i)
  choose v hv using fun i => exists_actual_ambient_unit_lift C p (r i)
  choose w hw using fun i => exists_actual_ambient_unit_lift D p' (Units.map ε.symm.toMonoidHom (r i))
  have hUnit (i : Fin E.length) :
      e.hom.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap p' (w i : ambient p'.val)) =
        (actualSubspaceInclusion (n := n) C).stalkMap p (v i : ambient p.val) := by
    have hleft := congrArg (fun z : (native C p)ˣ => (z : native C p)) (hv i)
    have hright := congrArg (fun z : (native D p')ˣ => (z : native D p')) (hw i)
    change (actualSubspaceInclusion (n := n) C).stalkMap p (v i : ambient p.val) = _ at hleft
    change (actualSubspaceInclusion (n := m) D).stalkMap p' (w i : ambient p'.val) =
      ε.symm (r i : native C p) at hright
    rw [hright, hleft]
    exact ε.apply_symm_apply _
  have hRatio (i : Fin E.length) :
      e.hom.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap p'
          (actualOriginalFunctionGerm p'.val (g i) (hg i))) =
        (actualSubspaceInclusion (n := n) C).stalkMap p
          ((v i : ambient p.val) * actualOriginalFunctionGerm p.val (f i) (hf i)) := by
    change _ = ((actualSubspaceInclusion (n := n) C).stalkMap p).hom _
    rw [map_mul, labelledFunction_quotient D p' R.Φ₂ (targetSelector e p R) i (mem_flatDomain_self R.Φ₂),
      labelledFunction_quotient C p R.Φ₁ (sourceSelector e p R) i (mem_flatDomain_self R.Φ₁)]
    have hleft := congrArg (fun z : (native C p)ˣ => (z : native C p)) (hv i)
    change ((actualSubspaceInclusion (n := n) C).stalkMap p).hom (v i : ambient p.val) = _ at hleft
    rw [hleft]
    exact hr i
  obtain ⟨a, b, _, _, U₀, V₀, hpU, hpV, _, _, ha, hb, hG⟩ :=
    simultaneous_unit_representatives e.hom he p f g hf hg v w hUnit hRatio
  let V : Opens N := ⟨(V₀ : Set N) ∩ flatDomain R.Φ₂, V₀.isOpen.inter (isOpen_flatDomain R.Φ₂)⟩
  have hpV' : p'.val ∈ V := ⟨hpV, mem_flatDomain_self R.Φ₂⟩
  have hNear : ∀ᶠ x : C in 𝓝 p, (e.hom.base x).val ∈ V :=
    (continuous_subtype_val.comp e.hom.base.hom.continuous).continuousAt.eventually
      (V.isOpen.mem_nhds hpV')
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at hNear
  obtain ⟨S, hS, hSo, hpS⟩ := mem_nhds_iff.mp hNear
  let U : Opens M := ⟨(U₀ : Set M) ∩ (flatDomain R.Φ₁ ∩ S),
    U₀.isOpen.inter ((isOpen_flatDomain R.Φ₁).inter hSo)⟩
  exact ⟨U, V, a, b, ⟨hpU, mem_flatDomain_self R.Φ₁, hpS⟩, hpV',
    (fun _ h => h.2.1), (fun _ h => h.2), (fun x hx => ha x hx.1),
    (fun y hy => hb y hy.1), fun x hx => ⟨hS hx.2.2 x rfl, (hG x hx.1).2⟩⟩

/-- The source label reads exactly the active coordinate of this fixed reader. -/
theorem source_labelledFunction_eq_normalized (x : readerSource R.Φ₁)
    {i : Fin E.length} {j : Fin R.r} (hj : R.slot i = some j) :
    labelledFunction R.Φ₁ (sourceSelector e p R) i x.val =
      (R.sourceDiffeomorph x).val (j.castAdd R.a) := by
  change labelledFunction R.Φ₁ (sourceSelector e p R) i x.val =
    flatCoord R.Φ₁ (R.σ₁ (j.castAdd R.a)) x.val
  simp [labelledFunction, sourceSelector, hj]

/-- The target label reads exactly the paired active coordinate. -/
theorem target_labelledFunction_eq_normalized (y : readerSource R.Φ₂)
    {i : Fin E.length} {j : Fin R.r} (hj : R.slot i = some j) :
    labelledFunction R.Φ₂ (targetSelector e p R) i y.val =
      (R.targetDiffeomorph y).val (j.castAdd R.b) := by
  change labelledFunction R.Φ₂ (targetSelector e p R) i y.val =
    flatCoord R.Φ₂ (R.σ₂ (j.castAdd R.b)) y.val
  simp [labelledFunction, targetSelector, hj]

/-- Simultaneous unit comparison for every active normalized coordinate of
the fixed relative reader, with the original paired graph as base. -/
theorem active_reader_units_on_graph
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hI : ∀ i : Fin E.length, Ideal.map (e.hom.stalkMap p).hom
      (actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p)) =
        actualLabelledBoundaryTraceIdeal C E i p) :
    ∃ (U : Opens M) (V : Opens N) (a : Fin R.r → M → ℂ) (b : Fin R.r → N → ℂ),
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧
      (U : Set M) ⊆ flatDomain R.Φ₁ ∧ (V : Set N) ⊆ flatDomain R.Φ₂ ∧
      (∀ x ∈ U, ∀ j, HolomorphicAt n (a j) x ∧ a j x ≠ 0) ∧
      (∀ y ∈ V, ∀ j, HolomorphicAt m (b j) y ∧ b j y ≠ 0) ∧
      ∀ x : C, x.val ∈ U →
        ∃ (hx : x.val ∈ flatDomain R.Φ₁) (hy : (e.hom.base x).val ∈ flatDomain R.Φ₂),
          (e.hom.base x).val ∈ V ∧
          ∀ j : Fin R.r, a j x.val = b j (e.hom.base x).val ∧
            (R.targetDiffeomorph ⟨(e.hom.base x).val, hy⟩).val (j.castAdd R.b) =
              a j x.val * (R.sourceDiffeomorph ⟨x.val, hx⟩).val (j.castAdd R.a) := by
  obtain ⟨U, V, a, b, hp, hp', hU, hV, ha, hb, hG⟩ := fixed_reader_units_on_graph e p R he hI
  classical
  choose i hi using R.slot_surjective
  refine ⟨U, V, a ∘ i, b ∘ i, hp, hp', hU, hV, (fun x hx j => ha x hx (i j)),
    (fun y hy j => hb y hy (i j)), ?_⟩
  intro x hx
  obtain ⟨hy, h⟩ := hG x hx
  refine ⟨hU hx, hV hy, hy, fun j => ⟨(h (i j)).1, ?_⟩⟩
  have hh := (h (i j)).2
  rw [source_labelledFunction_eq_normalized e p R ⟨x.val, hU hx⟩ (hi j),
    target_labelledFunction_eq_normalized e p R ⟨(e.hom.base x).val, hV hy⟩ (hi j)] at hh
  exact hh

end
end Hironaka.HironakaG1FixedReaderBoundaryUnits
