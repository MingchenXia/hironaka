import Hironaka.Resolution.HironakaG8GeneralCentreTransverseTrace

set_option autoImplicit false

/-!
# Varying a normal direction in a containing-centre exceptional fibre

In a native chart, a normal variation with zero pivot and zero centre
coordinates preserves the base and varies the exceptional normal vector
affinely. A variation tangent to the carrier and not tangent to the old
member gives arbitrarily near exceptional strict-carrier points outside that
member. Extraction of the normalized variation from tangent noncontainment
is separate.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11ContainingFibreVariation

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates
  BlowupMonomialCharts HironakaG8GeneralCentreStrictTangent HironakaG8GeneralCentreFibreCriterion

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- An actual normalized normal variation tangent to the carrier but not
to the old member gives local escape in the fixed exceptional fibre. -/
theorem frequently_strict_not_boundary_of_normal_variation (c : FlatChart n C)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hCH : C ⊆ H)
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hps : p ∈ c.source) (hpC : p.base ∈ C)
    (v : ComplexModel n) (hvj : v c.j = 0) (hvC : ∀ i : Fin n, i.val < c.k → v i = 0)
    (hvP : flatVec c.Φ p.base v ∈ tangentSpace n P p.base)
    (hvH : flatVec c.Φ p.base v ∉ tangentSpace n H p.base) :
    ∃ᶠ q in 𝓝 p, q.base = p.base ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C H := by
  by_cases hpH : p ∈ geoStrictTransform (blowupProj n C) C H
  swap
  · apply Filter.frequently_iff.mpr
    intro U hU
    exact ⟨p, mem_of_mem_nhds hU, rfl, hp, hpH⟩
  let w₀ := c.toFun p
  let curve : ℂ → ComplexModel n := fun t => w₀ + t • v
  have hw₀ : w₀ ∈ c.target := c.map_source hps
  have hj₀ : w₀ c.j = 0 := (c.toFun_j_eq_zero_iff hps).mpr hpC
  have hmon : ∀ t, monomial c.k c.j (curve t) = monomial c.k c.j w₀ := by
    intro t
    ext i
    rw [monomial_apply, monomial_apply]
    by_cases hi : c.k ≤ i.val ∧ i ≠ c.j
    · simp [hi, curve, hj₀, hvj]
    · have hvi : v i = 0 := by
        by_cases hij : i = c.j
        · simpa [hij] using hvj
        · exact hvC i (by omega)
      simp [hi, curve, hvi]
  have hpt : ∀ t, c.pt (curve t) = p.base := by
    intro t
    rw [← c.pt_toFun hps]
    change (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun (monomial c.k c.j (curve t))) =
      (chartAt (ComplexModel n) c.y₀).symm (c.Φ.invFun (monomial c.k c.j w₀))
    rw [hmon t]
  have hnormal : ∀ t, c.normalVec (curve t) = c.normalVec w₀ + t • v := by
    intro t
    ext i
    by_cases hij : i = c.j
    · subst i
      simp [c.normalVec_apply, curve, hvj]
    · by_cases hi : c.k ≤ i.val
      · simp [c.normalVec_apply, hij, hi, curve]
      · have hvi := hvC i (by omega)
        simp [c.normalVec_apply, hij, hi, curve, hvi]
  have hTCP : ∀ x, tangentSpace n C x ≤ tangentSpace n P x := by
    intro x ξ hξ
    apply mem_tangentSpace.mpr
    intro f hfP
    apply germDiff_eq_zero_of_mem_tangentSpace hξ
    refine ⟨hfP.1, ?_⟩
    filter_upwards [hfP.2] with y hy hyC
    exact hy (hCP hyC)
  have hpdirP := dir_le_tangentSpace_of_mem_geoStrictTransform hCP hp hpC
  have hpdirH := dir_le_tangentSpace_of_mem_geoStrictTransform hCH hpH hpC
  have hnormalP : flatVec c.Φ p.base (c.normalVec w₀) ∈ tangentSpace n P p.base := by
    apply hpdirP
    rw [dir_eq_tangentCentre_sup_normal_direction c hps hpC]
    exact (show ℂ ∙ flatVec c.Φ p.base (c.normalVec w₀) ≤ _ from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have hnormalH : flatVec c.Φ p.base (c.normalVec w₀) ∈ tangentSpace n H p.base := by
    apply hpdirH
    rw [dir_eq_tangentCentre_sup_normal_direction c hps hpC]
    exact (show ℂ ∙ flatVec c.Φ p.base (c.normalVec w₀) ≤ _ from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have hcurve : Tendsto curve (𝓝 (0 : ℂ)) (𝓝 w₀) := by
    have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [curve, zero_smul, add_zero] using hc.tendsto 0
  have hinverse : Tendsto (fun t => c.invFun (curve t)) (𝓝 (0 : ℂ)) (𝓝 p) := by
    have hlim := (c.homeo.continuousAt_symm hw₀).tendsto.comp hcurve
    change Tendsto (fun t => c.invFun (curve t)) (𝓝 (0 : ℂ)) (𝓝 (c.invFun w₀)) at hlim
    simpa only [w₀, c.left_inv hps] using hlim
  have htarget : ∀ᶠ t in 𝓝 (0 : ℂ), curve t ∈ c.target :=
    hcurve (c.isOpen_target.mem_nhds hw₀)
  apply Filter.frequently_iff.mpr
  intro U hU
  have hUevent : ∀ᶠ t in 𝓝 (0 : ℂ), c.invFun (curve t) ∈ U := hinverse hU
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), curve t ∈ c.target ∧ c.invFun (curve t) ∈ U :=
    nhdsWithin_le_nhds (htarget.and hUevent)
  obtain ⟨t, ⟨ht, htU⟩, htne⟩ := (hnear.and self_mem_nhdsWithin).exists
  let q : BlowupSpace n C := c.invFun (curve t)
  have hqs : q ∈ c.source := c.map_target ht
  have hqcoords : c.toFun q = curve t := c.right_inv ht
  have hqbase : q.base = p.base := by rw [c.base_invFun ht, hpt t]
  have hqC : q.base ∈ C := hqbase ▸ hpC
  have hnormalflat : flatVec c.Φ q.base (c.normalVec (c.toFun q)) =
      flatVec c.Φ p.base (c.normalVec w₀) + t • flatVec c.Φ p.base v := by
    rw [hqbase, hqcoords, hnormal]
    simp [flatVec]
  have hqnormalP : flatVec c.Φ q.base (c.normalVec (c.toFun q)) ∈ tangentSpace n P q.base := by
    rw [hnormalflat, hqbase]
    exact (tangentSpace n P p.base).add_mem hnormalP ((tangentSpace n P p.base).smul_mem t hvP)
  have hqdirP : q.dir ≤ tangentSpace n P q.base := by
    rw [dir_eq_tangentCentre_sup_normal_direction c hqs hqC]
    exact sup_le (hTCP q.base) ((Submodule.span_singleton_le_iff_mem _ _).mpr hqnormalP)
  have hqP := mem_geoStrictTransform_of_dir_le_tangentSpace hP hCP hqC hqdirP
  have hqNotH : q ∉ geoStrictTransform (blowupProj n C) C H := by
    intro hqH
    have hqdirH := dir_le_tangentSpace_of_mem_geoStrictTransform hCH hqH hqC
    have hqnormalH : flatVec c.Φ q.base (c.normalVec (c.toFun q)) ∈ tangentSpace n H q.base := by
      apply hqdirH
      rw [dir_eq_tangentCentre_sup_normal_direction c hqs hqC]
      exact (show ℂ ∙ flatVec c.Φ q.base (c.normalVec (c.toFun q)) ≤ _ from le_sup_right)
        (Submodule.mem_span_singleton_self _)
    rw [hnormalflat, hqbase] at hqnormalH
    have htv : t • flatVec c.Φ p.base v ∈ tangentSpace n H p.base := by
      have hh := (tangentSpace n H p.base).sub_mem hqnormalH hnormalH
      simpa using hh
    have hv := (tangentSpace n H p.base).smul_mem t⁻¹ htv
    apply hvH
    simpa [smul_smul, inv_mul_cancel₀ htne] using hv
  exact ⟨q, htU, hqbase, hqP, hqNotH⟩


/-- Tangent-space noncontainment produces a normalized variation and hence
local escape in the fixed exceptional fibre. -/
theorem frequently_strict_not_boundary_of_tangent_noncontainment (c : FlatChart n C)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hCH : C ⊆ H)
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hps : p ∈ c.source) (hpC : p.base ∈ C)
    (hnt : ¬ tangentSpace n P p.base ≤ tangentSpace n H p.base) :
    ∃ᶠ q in 𝓝 p, q.base = p.base ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C H := by
  by_cases hpH : p ∈ geoStrictTransform (blowupProj n C) C H
  swap
  · apply Filter.frequently_iff.mpr
    intro U hU
    exact ⟨p, mem_of_mem_nhds hU, rfl, hp, hpH⟩
  obtain ⟨ξ, hξP, hξH⟩ : ∃ ξ ∈ tangentSpace n P p.base, ξ ∉ tangentSpace n H p.base := by
    by_contra h
    apply hnt
    intro ξ hξ
    by_contra hξH
    exact h ⟨ξ, hξ, hξH⟩
  let A := fderiv ℂ (flatMap c.Φ p.base) (chartAt (ComplexModel n) p.base p.base)
  have hAsurj : Function.Surjective A := fun z =>
    ⟨flatVec c.Φ p.base z, fderiv_flatMap_flatVec c.hsrc hps.1 z⟩
  have hAinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective (f := (A : ComplexModel n →ₗ[ℂ] ComplexModel n))).mpr hAsurj
  have hξflat : flatVec c.Φ p.base (A ξ) = ξ := by
    apply hAinj
    exact fderiv_flatMap_flatVec c.hsrc hps.1 (A ξ)
  let u := c.normalVec (c.toFun p)
  let z := A ξ - (A ξ c.j) • u
  let zC : ComplexModel n := WithLp.toLp 2 fun i => if i.val < c.k then z i else 0
  let v := z - zC
  have hvj : v c.j = 0 := by
    simp [v, z, zC, u, c.normalVec_j, Nat.not_lt.mpr c.hj]
  have hvC : ∀ i : Fin n, i.val < c.k → v i = 0 := by
    intro i hi
    simp [v, zC, hi]
  have hTCP : tangentSpace n C p.base ≤ tangentSpace n P p.base := by
    intro η hη
    apply mem_tangentSpace.mpr
    intro f hfP
    apply germDiff_eq_zero_of_mem_tangentSpace hη
    refine ⟨hfP.1, ?_⟩
    filter_upwards [hfP.2] with y hy hyC
    exact hy (hCP hyC)
  have hTCH : tangentSpace n C p.base ≤ tangentSpace n H p.base := by
    intro η hη
    apply mem_tangentSpace.mpr
    intro f hfH
    apply germDiff_eq_zero_of_mem_tangentSpace hη
    refine ⟨hfH.1, ?_⟩
    filter_upwards [hfH.2] with y hy hyC
    exact hy (hCH hyC)
  have hzC : flatVec c.Φ p.base zC ∈ tangentSpace n C p.base := by
    apply (mem_tangentSpace_iff c.hsrc c.hflat hps.1 hpC).mpr
    intro i hi
    rw [germDiff_flatCoord_flatVec c.hsrc hps.1]
    simp [zC, Nat.not_lt.mpr hi]
  have huDir : flatVec c.Φ p.base u ∈ p.dir := by
    rw [dir_eq_tangentCentre_sup_normal_direction c hps hpC]
    exact (show ℂ ∙ flatVec c.Φ p.base u ≤ _ from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have huP : flatVec c.Φ p.base u ∈ tangentSpace n P p.base :=
    dir_le_tangentSpace_of_mem_geoStrictTransform hCP hp hpC huDir
  have huH : flatVec c.Φ p.base u ∈ tangentSpace n H p.base :=
    dir_le_tangentSpace_of_mem_geoStrictTransform hCH hpH hpC huDir
  have hvflat : flatVec c.Φ p.base v = ξ - (A ξ c.j) • flatVec c.Φ p.base u -
      flatVec c.Φ p.base zC := by
    dsimp [v, z, flatVec]
    rw [map_sub, map_sub, map_smul]
    change flatVec c.Φ p.base (A ξ) - (A ξ c.j) • flatVec c.Φ p.base u -
      flatVec c.Φ p.base zC = _
    rw [hξflat]
    rfl
  have hvP : flatVec c.Φ p.base v ∈ tangentSpace n P p.base := by
    rw [hvflat]
    exact (tangentSpace n P p.base).sub_mem
      ((tangentSpace n P p.base).sub_mem hξP ((tangentSpace n P p.base).smul_mem _ huP)) (hTCP hzC)
  have hvH : flatVec c.Φ p.base v ∉ tangentSpace n H p.base := by
    intro hvH
    apply hξH
    have h := (tangentSpace n H p.base).add_mem
      ((tangentSpace n H p.base).add_mem hvH ((tangentSpace n H p.base).smul_mem (A ξ c.j) huH)) (hTCH hzC)
    rw [hvflat] at h
    convert h using 1; abel
  exact frequently_strict_not_boundary_of_normal_variation c hP hCP hCH hp hps hpC v hvj hvC hvP hvH


/-- At any native exceptional strict-carrier point, noncontainment of its
carrier tangent in the old boundary tangent forces nearby escape in that
same fixed exceptional fibre. -/
theorem frequently_strict_not_boundary_of_tangent_noncontainment_native
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hCH : C ⊆ H)
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) (hnt : ¬ tangentSpace n P p.base ≤ tangentSpace n H p.base) :
    ∃ᶠ q in 𝓝 p, q.base = p.base ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C H := by
  obtain ⟨j, hj, hps⟩ := exists_mem_flatSource hpC
    (mem_flatDomain_self (flatΦ n hpC)) hpC
  let c : FlatChart n C := mkFlat hpC j hj
  exact frequently_strict_not_boundary_of_tangent_noncontainment c hP hCP hCH hp hps hpC hnt


/-- On a fixed exceptional fibre, carrier tangent noncontainment makes the
complement of the old strict member dense in the strict-carrier fibre. -/
theorem strict_fibre_subset_closure_diff_of_tangent_noncontainment
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hCH : C ⊆ H)
    {x : X} (hxC : x ∈ C) (hnt : ¬ tangentSpace n P x ≤ tangentSpace n H x) :
    (geoStrictTransform (blowupProj n C) C P ∩ (blowupProj n C ⁻¹' {x})) ⊆
      closure ((geoStrictTransform (blowupProj n C) C P ∩ (blowupProj n C ⁻¹' {x})) \
        geoStrictTransform (blowupProj n C) C H) := by
  intro p ⟨hpP, hpx⟩
  have hpbase : p.base = x := hpx
  have hpC : p.base ∈ C := hpbase ▸ hxC
  have hnt' : ¬ tangentSpace n P p.base ≤ tangentSpace n H p.base := hpbase ▸ hnt
  have hf := frequently_strict_not_boundary_of_tangent_noncontainment_native hP hCP hCH hpP hpC hnt'
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨q, ⟨hqbase, hqP, hqH⟩, hqU⟩ := (hf.and_eventually hU).exists
  exact ⟨q, hqU, ⟨⟨hqP, hqbase.trans hpbase⟩, hqH⟩⟩

/-- If tangent noncontainment holds at every centre point, the complement of
the old strict member is dense in the total exceptional strict-carrier trace. -/
theorem exceptional_trace_subset_closure_diff_of_tangent_noncontainment
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P) (hCH : C ⊆ H)
    (hnt : ∀ x ∈ C, ¬ tangentSpace n P x ≤ tangentSpace n H x) :
    (geoStrictTransform (blowupProj n C) C P ∩ (blowupProj n C ⁻¹' C)) ⊆
      closure ((geoStrictTransform (blowupProj n C) C P ∩ (blowupProj n C ⁻¹' C)) \
        geoStrictTransform (blowupProj n C) C H) := by
  intro p ⟨hpP, hpC⟩
  have hf := frequently_strict_not_boundary_of_tangent_noncontainment_native hP hCP hCH hpP hpC
    (hnt p.base hpC)
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨q, ⟨hqbase, hqP, hqH⟩, hqU⟩ := (hf.and_eventually hU).exists
  have hqC : q.base ∈ C := hqbase ▸ hpC
  exact ⟨q, hqU, ⟨⟨hqP, hqC⟩, hqH⟩⟩

end

end Hironaka.HironakaG11ContainingFibreVariation
