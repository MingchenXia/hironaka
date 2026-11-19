import Hironaka.Resolution.HironakaG8GeneralCentreTransverseTrace
import Hironaka.Blowup.BlowupSpaceUniversal
import Hironaka.Blowup.BlowupUniqueness
/-! # Local sections of the exceptional strict trace -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8TraceLocalSection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates
  BlowupMonomialCharts NestedFlattening RegularAtDimTransport HironakaG8GeneralCentreStrictTangent HironakaG8GeneralCentreFibreCriterion

/-- On a simultaneous centre/carrier chart, every neighbourhood of a
point of the exceptional strict trace projects onto a neighbourhood of its
base point in the centre. -/
theorem trace_projects_near_base_of_nested_chart
    {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {C P : Set X} [Fact (IsClosedSubmanifold n C)]
    (c : FlatChart n C) (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) {kP : ℕ}
    (hflatP : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) c.y₀).source →
      chartAt (ComplexModel n) c.y₀ x ∈ c.Φ.source →
        (x ∈ P ↔ c.Φ.toFun (chartAt (ComplexModel n) c.y₀ x) ∈ complexCoordinatePlane n kP))
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hps : p ∈ c.source) (hpC : p.base ∈ C) :
    ∀ O ∈ 𝓝 p, ∀ᶠ x in 𝓝 p.base, x ∈ C →
      ∃ q ∈ O, q.base = x ∧ q ∈ geoStrictTransform (blowupProj n C) C P := by
  let w₀ := c.toFun p
  let w : X → ComplexModel n := fun x => WithLp.toLp 2 fun i =>
    if i.val < c.k then flatCoord c.Φ i x else w₀ i
  have hw₀ : w₀ ∈ c.target := c.map_source hps
  have hpivot : w₀ c.j = 0 := (c.toFun_j_eq_zero_iff hps).mpr hpC
  have hwBase : w p.base = w₀ := by
    ext i
    change (if i.val < c.k then flatCoord c.Φ i p.base else w₀ i) = w₀ i
    by_cases hi : i.val < c.k
    · rw [if_pos hi]
      have hm := congrArg (fun z : ComplexModel n => z i) (c.monomial_toFun hps)
      change monomial c.k c.j w₀ i = flatCoord c.Φ i p.base at hm
      rw [monomial_apply, if_neg (by omega)] at hm
      exact hm.symm
    · simp [hi]
  have hwCont : ContinuousAt w p.base := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    change ContinuousAt (fun x : X => if i.val < c.k then flatCoord c.Φ i x else w₀ i) p.base
    split_ifs
    · exact (holomorphicAt_flatCoord c.Φ i hps.1).continuousAt
    · exact continuousAt_const
  have hwLim : Tendsto w (𝓝 p.base) (𝓝 w₀) := by simpa only [hwBase] using hwCont.tendsto
  have hqLim : Tendsto (fun x => c.invFun (w x)) (𝓝 p.base) (𝓝 p) := by
    have h := (c.homeo.continuousAt_symm hw₀).tendsto.comp hwLim
    change Tendsto (fun x => c.invFun (w x)) (𝓝 p.base) (𝓝 (c.invFun w₀)) at h
    simpa only [w₀, c.left_inv hps] using h
  have hnormal : ∀ x, c.normalVec (w x) = c.normalVec w₀ := by
    intro x
    ext i
    by_cases hij : i = c.j
    · simp [FlatChart.normalVec_apply, hij]
    · by_cases hci : c.k ≤ i.val
      · simp [FlatChart.normalVec_apply, hij, hci, w, Nat.not_lt_of_ge hci]
      · simp [FlatChart.normalVec_apply, hij, hci]
  have hnormalP : ∀ i : Fin n, kP ≤ i.val → c.normalVec w₀ i = 0 := by
    have hξP := normal_direction_mem_tangentSpace_of_mem_geoStrictTransform c hCP hp hps hpC
    intro i hi
    have hz := (mem_tangentSpace_iff c.hsrc hflatP hps.1 (hCP hpC)).mp hξP i hi
    exact (germDiff_flatCoord_flatVec c.hsrc hps.1 i (c.normalVec w₀)).symm.trans hz
  have hTCP : ∀ x, tangentSpace n C x ≤ tangentSpace n P x := by
    intro x ξ hξ
    apply mem_tangentSpace.mpr
    intro f hfP
    apply germDiff_eq_zero_of_mem_tangentSpace hξ
    refine ⟨hfP.1, ?_⟩
    filter_upwards [hfP.2] with y hy hyC
    exact hy (hCP hyC)
  intro O hO
  filter_upwards [hwLim (c.isOpen_target.mem_nhds hw₀), hqLim hO,
    (isOpen_flatDomain c.Φ).mem_nhds hps.1] with x hxTarget hxO hxdom hxC
  let q := c.invFun (w x)
  have hqsource : q ∈ c.source := c.map_target hxTarget
  have hpivx : w x c.j = 0 := by
    simp [w, Nat.not_lt_of_ge c.hj, hpivot]
  have hmon : monomial c.k c.j (w x) = c.Φ.toFun (chartAt (ComplexModel n) c.y₀ x) := by
    ext i
    change monomial c.k c.j (w x) i = flatCoord c.Φ i x
    by_cases hi : c.k ≤ i.val ∧ i ≠ c.j
    · rw [monomial_apply, if_pos hi, hpivx, mul_zero]
      exact (flatCoord_eq_zero c.hsrc c.hflat hxdom hxC hi.1).symm
    · rw [monomial_apply, if_neg hi]
      by_cases hik : i.val < c.k
      · simp [w, hik]
      · have hij : i = c.j := by
          by_contra hne
          exact hi ⟨by omega, hne⟩
        subst i
        simp [w, Nat.not_lt_of_ge c.hj, hpivot,
          flatCoord_eq_zero c.hsrc c.hflat hxdom hxC c.hj]
  have hqbase : q.base = x := by
    rw [c.base_invFun hxTarget]
    change (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun (monomial c.k c.j (w x))) = x
    rw [hmon]
    exact flatInverse_flat c.Φ hxdom
  have hqC : q.base ∈ C := hqbase ▸ hxC
  have hqnormalP : flatVec c.Φ q.base (c.normalVec (c.toFun q)) ∈ tangentSpace n P q.base := by
    apply (mem_tangentSpace_iff c.hsrc hflatP hqsource.1 (hCP hqC)).mpr
    intro i hi
    rw [germDiff_flatCoord_flatVec c.hsrc hqsource.1]
    rw [c.right_inv hxTarget, hnormal x]
    exact hnormalP i hi
  have hqdirP : q.dir ≤ tangentSpace n P q.base := by
    rw [dir_eq_tangentCentre_sup_normal_direction c hqsource hqC]
    exact sup_le (hTCP q.base) ((Submodule.span_singleton_le_iff_mem _ _).mpr hqnormalP)
  exact ⟨q, hxO, hqbase, mem_geoStrictTransform_of_dir_le_tangentSpace hP hCP hqC hqdirP⟩


/-- The native exceptional strict trace locally surjects onto the centre,
without a chosen chart. -/
theorem trace_projects_near_base
    {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {C P : Set X} [Fact (IsClosedSubmanifold n C)]
    (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) :
    ∀ O ∈ 𝓝 p, ∀ᶠ x in 𝓝 p.base, x ∈ C →
      ∃ q ∈ O, q.base = x ∧ q ∈ geoStrictTransform (blowupProj n C) C P := by
  obtain ⟨kC,hkC⟩ := (Fact.out : IsClosedSubmanifold n C).2 p.base hpC
  obtain ⟨kP,hkP⟩ := hP.2 p.base (hCP hpC)
  have hle : kC ≤ kP := le_of_regularAtDim_subset hkC hkP hCP
  obtain ⟨Φ,hΦsrc,_,hflat⟩ := exists_nested_flattening hle hkC hkP hCP
  have hflatC : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) p.base).source →
      chartAt (ComplexModel n) p.base x ∈ Φ.source →
        (x ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) p.base x) ∈ complexCoordinatePlane n kC) :=
    fun hx hΦx => (hflat hx hΦx).1
  have hnot := p.dirVec_not_mem hpC
  rw [mem_tangentSpace_iff hΦsrc hflatC (mem_flatDomain_self Φ) hpC] at hnot
  push Not at hnot
  obtain ⟨j,hj,hne⟩ := hnot
  let c : FlatChart n C := ⟨p.base,kC,Φ,hΦsrc,hflatC,j,hj⟩
  have hps : p ∈ c.source := by
    refine ⟨mem_flatDomain_self Φ, ?_⟩
    change BlowupConstruction.extVal (flatCoord Φ j) p ≠ 0
    rw [BlowupConstruction.extVal_of_mem hpC]
    exact hne
  exact trace_projects_near_base_of_nested_chart c hP hCP
    (fun hx hΦx => (hflat hx hΦx).2) hp hps hpC


/-- The exceptional strict trace of an arbitrary actual blowup locally
surjects onto its smooth centre at every trace point. -/
theorem actual_trace_projects_near_base
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {C P : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y} (hp : p ∈ geoStrictTransform π C P) (hpC : π p ∈ C) :
    ∀ O ∈ 𝓝 p, ∀ᶠ x in 𝓝 (π p), x ∈ C →
      ∃ q ∈ O, π q = x ∧ q ∈ geoStrictTransform π C P := by
  let : Fact (IsClosedSubmanifold n C) := ⟨hπ.1⟩
  obtain ⟨e,f,he,hf,hπe,_,hfe,hef⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hπ (isBlowupAlong_blowupProj hπ.2.1)
  let φ : Y ≃ₜ BlowupSpace n C :=
    { toFun := e, invFun := f, left_inv := congrFun hfe, right_inv := congrFun hef,
      continuous_toFun := he.continuous, continuous_invFun := hf.continuous }
  have heProj : ∀ y : Y, (blowupProj n C) (e y) = π y := fun y => congrFun hπe y
  have heStrict (A : Set X) : geoStrictTransform π C A =
      e ⁻¹' geoStrictTransform (blowupProj n C) C A := by
    symm
    change (φ : Y → BlowupSpace n C) ⁻¹' closure ((blowupProj n C) ⁻¹' (A \ C)) =
      closure (π ⁻¹' (A \ C))
    rw [φ.isOpenMap.preimage_closure_eq_closure_preimage φ.continuous_toFun]
    congr 1
    ext y
    change (blowupProj n C) (e y) ∈ A \ C ↔ π y ∈ A \ C
    rw [heProj y]
  have hpP : e p ∈ geoStrictTransform (blowupProj n C) C P := by
    have hp' : p ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C P := (heStrict P) ▸ hp
    exact hp'
  have hpbase : (e p).base = π p := heProj p
  have hpC' : (e p).base ∈ C := hpbase ▸ hpC
  intro O hO
  have hO' : φ '' O ∈ 𝓝 (e p) := by
    change φ '' O ∈ 𝓝 (φ p)
    rw [← φ.map_nhds_eq]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hO (fun y hy => ⟨y,hy,rfl⟩))
  have hn := trace_projects_near_base hP hCP hpP hpC' (φ '' O) hO'
  rw [hpbase] at hn
  filter_upwards [hn] with x hx hxC
  obtain ⟨q,hqO,hqbase,hqP⟩ := hx hxC
  obtain ⟨r,hrO,rfl⟩ := hqO
  refine ⟨r,hrO,?_,?_⟩
  · change (blowupProj n C) (e r) = x at hqbase
    rwa [heProj r] at hqbase
  · change r ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C P at hqP
    rwa [← heStrict P] at hqP

end
end Hironaka.HironakaG8TraceLocalSection
