import Hironaka.Resolution.HironakaG8GeneralCentreFibreCriterion

set_option autoImplicit false

/-!
# Local noncontainment of the total exceptional trace in a transverse member

The actual native chart flattens the smooth carrier, while the boundary is
one of its centre coordinates. Varying that base coordinate preserves the
native normal direction and the exceptional strict carrier, but leaves the
boundary. This concerns the local total trace, not a fixed exceptional fibre.

The qualified simultaneous chart is explicit ordinary geometric input here;
constructing it from the source SNC hypotheses is a separate remaining step.
No residual successor or original Hironaka goal is closed by this theorem.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8GeneralCentreTransverseTrace

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupFlatCoordinates
  BlowupMonomialCharts HironakaG8GeneralCentreStrictTangent HironakaG8GeneralCentreFibreCriterion

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- A genuine centre-coordinate variation gives nearby exceptional strict
carrier points off a qualified transverse original boundary. -/
theorem frequently_exceptional_strict_not_boundary (c : FlatChart n C)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {kP : ℕ}
    (hflatP : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) c.y₀).source →
      chartAt (ComplexModel n) c.y₀ x ∈ c.Φ.source →
        (x ∈ P ↔ c.Φ.toFun (chartAt (ComplexModel n) c.y₀ x) ∈ complexCoordinatePlane n kP))
    (h : Fin n) (hh : h.val < c.k) (hH : IsClosed H)
    (hflatH : ∀ {x : X}, x ∈ (chartAt (ComplexModel n) c.y₀).source →
      chartAt (ComplexModel n) c.y₀ x ∈ c.Φ.source →
        (x ∈ H ↔ flatCoord c.Φ h x = 0))
    {p : BlowupSpace n C}
    (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hps : p ∈ c.source) (hpC : p.base ∈ C) (hpH : p.base ∈ H) :
    ∃ᶠ q in 𝓝 p, q.base ∈ C ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C H := by
  let w₀ := c.toFun p
  let eₕ : ComplexModel n := EuclideanSpace.single h (1 : ℂ)
  let curve : ℂ → ComplexModel n := fun t => w₀ + t • eₕ
  have hw₀ : w₀ ∈ c.target := c.map_source hps
  have hPivot : w₀ c.j = 0 := (c.toFun_j_eq_zero_iff hps).mpr hpC
  have hhj : h ≠ c.j := by
    intro heq
    have hj := c.hj
    rw [← heq] at hj
    omega
  have hnotNormal : ¬ (c.k ≤ h.val ∧ h ≠ c.j) := fun hn => (Nat.not_le_of_lt hh) hn.1
  have hh₀ : w₀ h = 0 := by
    have hflat₀ : flatCoord c.Φ h p.base = 0 := (hflatH hps.1.1 hps.1.2).mp hpH
    have hm := congrArg (fun w : ComplexModel n => w h) (c.monomial_toFun hps)
    change monomial c.k c.j (c.toFun p) h = flatCoord c.Φ h p.base at hm
    rw [monomial_apply, if_neg hnotNormal] at hm
    exact hm.trans hflat₀
  have hnormal : ∀ t, c.normalVec (curve t) = c.normalVec w₀ := by
    intro t
    ext i
    by_cases hij : i = c.j
    · simp only [c.normalVec_apply, if_pos hij]
    · by_cases hci : c.k ≤ i.val
      · rw [c.normalVec_apply, c.normalVec_apply, if_neg hij, if_pos hci]
        have hih : i ≠ h := by
          intro heq
          subst heq
          omega
        simp [curve, eₕ, hih, hij, hci]
      · simp only [c.normalVec_apply, if_neg hij, if_neg hci]
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
  have hqj : c.toFun q c.j = 0 := by
    rw [hqcoords]
    simp [curve, eₕ, Ne.symm hhj, hPivot]
  have hqC : q.base ∈ C := (c.toFun_j_eq_zero_iff hqs).mp hqj
  have hqNormalP : flatVec c.Φ q.base (c.normalVec (c.toFun q)) ∈ tangentSpace n P q.base := by
    apply (mem_tangentSpace_iff c.hsrc hflatP hqs.1 (hCP hqC)).mpr
    intro i hi
    rw [germDiff_flatCoord_flatVec c.hsrc hqs.1]
    rw [hqcoords, hnormal t]
    exact hnormalP i hi
  have hqdirP : q.dir ≤ tangentSpace n P q.base := by
    rw [dir_eq_tangentCentre_sup_normal_direction c hqs hqC]
    exact sup_le (hTCP q.base) ((Submodule.span_singleton_le_iff_mem _ _).mpr hqNormalP)
  have hqP := mem_geoStrictTransform_of_dir_le_tangentSpace hP hCP hqC hqdirP
  have hqNotH : q.base ∉ H := by
    intro hqH
    have hflatq : flatCoord c.Φ h q.base = 0 := (hflatH hqs.1.1 hqs.1.2).mp hqH
    have hm := congrArg (fun w : ComplexModel n => w h) (c.monomial_toFun hqs)
    change monomial c.k c.j (c.toFun q) h = flatCoord c.Φ h q.base at hm
    rw [monomial_apply, if_neg hnotNormal, hqcoords] at hm
    have hth : curve t h = t := by simp [curve, eₕ, hh₀]
    exact htne ((hth.symm.trans hm).trans hflatq)
  have hqNotStrictH : q ∉ geoStrictTransform (blowupProj n C) C H := fun hqH =>
    hqNotH (geoStrictTransform_subset_preimage (continuous_blowupProj (n := n) (C := C)) hH hqH)
  exact ⟨q, htU, hqC, hqP, hqNotStrictH⟩

end

end Hironaka.HironakaG8GeneralCentreTransverseTrace
