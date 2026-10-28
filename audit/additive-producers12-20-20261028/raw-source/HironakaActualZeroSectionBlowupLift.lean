import TranscendentalNakamaye.Pending.HironakaActualZeroSectionCentreSheaf
import TranscendentalNakamaye.Pending.HironakaSmoothSubmersionOrderedChoiceImageTrace
import TranscendentalNakamaye.Pending.BlowupSpaceUniversal
import TranscendentalNakamaye.Pending.BlowupStrictSubmanifold

/-!
# Actual zero-section carrier and the genuine universal blowup lift

The original data are two prescribed genuine blowups, along C and its literal
zero-section image. The whole sheaf centre dictionary produces the actual
lift; true exceptional nonvanishing produces its range in the WHOLE geometric
strict carrier. No origin-ideal replacement or strict-carrier certificate.
Blueprint: hironaka-actual-zero-section-blowup-comparison-extension.tex.
Source-only; no kernel acceptance is claimed.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupLift

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualZeroSectionCentreSheaf
  HironakaSmoothSubmersionOrderedChoiceImageTrace BlowupStrictSubmanifold

/-- The actual entire coordinate plane is closed, with no positive block bound. -/
theorem actual_zeroSection_plane_closed (d t : ℕ) :
    IsClosed (complexCoordinatePlane (d+t) d) := by
  have he : complexCoordinatePlane (d+t) d =
      ⋂ i : Fin (d+t), ⋂ (_ : d ≤ i.val), {z : ComplexModel (d+t) | z i = 0} := by
    ext z
    simp only [complexCoordinatePlane, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).continuous continuous_const

/-- At EVERY point the actual plane has a true translation flattening. -/
theorem actual_zeroSection_plane_regular (d t : ℕ) (z : ComplexModel (d+t))
    (hz : z ∈ complexCoordinatePlane (d+t) d) :
    RegularAtDim (n := d+t) (complexCoordinatePlane (d+t) d) z d := by
  let e := (complexChartAt (n := d+t) z).val
  let p := e z
  have he (w : ComplexModel (d+t)) : e w = w := by
    simp [e, complexChartAt, chartAt_self_eq]
  have hp : p = z := he z
  let Φ : LocalHolomorphicEquivAt (n := d+t) p :=
    { source := e.target
      target := (fun w => w + p) ⁻¹' e.target
      isOpen_source := e.open_target
      isOpen_target := e.open_target.preimage (continuous_id.add continuous_const)
      center_mem_source := e.map_source (mem_complexChartAt_source z)
      toFun := fun w => w - p
      invFun := fun w => w + p
      toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
      invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
      mapsTo_toFun := fun w hw => by simpa using hw
      mapsTo_invFun := fun w hw => hw
      left_inv := fun w _ => by simp
      right_inv := fun w _ => by simp }
  refine ⟨by omega, hz, Φ, subset_rfl, sub_self p, ?_⟩
  intro w _hw _hwΦ
  change w ∈ complexCoordinatePlane (d+t) d ↔ e w - p ∈ complexCoordinatePlane (d+t) d
  rw [he w, hp]
  exact (sub_mem_plane_iff hz).symm

/-- The actual whole range equals the original coordinate plane. -/
theorem actual_zeroSection_range (d t : ℕ) :
    Set.range (tangentInclusion d t) = complexCoordinatePlane (d+t) d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact tangentInclusion_mem_plane d t x
  · intro hz
    exact ⟨tangentProjection d t z, tangentInclusion_projection_eq_of_mem_plane d t hz⟩

section ActualBlowups

variable {d t : ℕ} {B Y : Type}
  [TopologicalSpace B] [ChartedSpace (ComplexModel d) B] [IsComplexManifold d B]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
  {C : Set (ComplexModel d)} {p : B → ComplexModel d} {π : Y → ComplexModel (d+t)}

set_option linter.unusedSectionVars false in
/-- ONLY original genuine blowups supply the unique actual holomorphic lift.
The original universal property really permits the smaller source dimension. -/
theorem existsUnique_actual_zeroSection_blowup_lift
    (hp : IsBlowupAlong d C p)
    (hπ : IsBlowupAlong (d+t) ((tangentInclusion d t) '' C) π) :
    ∃! f : B → Y,
      ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞ f ∧
        π ∘ f = (tangentInclusion d t) ∘ p := by
  have hi : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞
      (tangentInclusion d t) := (tangentInclusion d t).contDiff.contMDiff
  have hinv : (GermIdeal.pullback (m := d) ((tangentInclusion d t) ∘ p)
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))).IsInvertible := by
    rw [whole_pullback_comp hi hp.contMDiff
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) (fun _ _ ha => ha.1),
      actual_zeroSection_centre_sheaf d t C]
    exact hp.2.2.2.1
  exact hπ.2.2.2.2 d B ((tangentInclusion d t) ∘ p) (hi.comp hp.contMDiff) hinv

/-- The ENTIRE actual exceptional sheaf of the same lift is the base one.
No origin germ, Taylor ideal or finite jet replaces either side. -/
theorem actual_zeroSection_lift_exceptional_ideal
    (hp : IsBlowupAlong d C p)
    (hπ : IsBlowupAlong (d+t) ((tangentInclusion d t) '' C) π)
    (f : B → Y) (hf : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞ f)
    (hcomm : π ∘ f = (tangentInclusion d t) ∘ p) :
    GermIdeal.pullback (m := d) f
        (GermIdeal.pullback (m := d+t) π
          (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))) =
      GermIdeal.pullback (m := d) p (vanishingIdeal (n := d) C) := by
  rw [← whole_pullback_comp hπ.contMDiff hf
    (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) (fun _ _ ha => ha.1), hcomm,
    whole_pullback_comp (tangentInclusion d t).contDiff.contMDiff hp.contMDiff
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))
      (fun _ _ ha => ha.1), actual_zeroSection_centre_sheaf d t C]

set_option linter.unusedSectionVars false in
/-- True invertibility on the original base blowup yields the internally dense
noncentre and therefore range in the WHOLE actual strict carrier. -/
theorem actual_zeroSection_lift_mem_geoStrictTransform
    (hp : IsBlowupAlong d C p)
    (f : B → Y) (hf : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞ f)
    (hcomm : π ∘ f = (tangentInclusion d t) ∘ p) (x : B) :
    f x ∈ geoStrictTransform π ((tangentInclusion d t) '' C)
      (complexCoordinatePlane (d+t) d) := by
  let : Fact (IsClosedSubmanifold d C) := ⟨hp.1⟩
  apply mem_closure_iff.mpr
  intro V hV hxV
  obtain ⟨y, hyV, hpy⟩ := BlowupConstruction.exists_not_mem_of_isOpen hp.contMDiff hp.2.2.2.1
    (hV.preimage hf.continuous) ⟨x, hxV⟩
  refine ⟨f y, hyV, ?_⟩
  change π (f y) ∈ complexCoordinatePlane (d+t) d ∧ π (f y) ∉ (tangentInclusion d t) '' C
  have hycomm : π (f y) = tangentInclusion d t (p y) := congrFun hcomm y
  rw [hycomm]
  constructor
  · exact tangentInclusion_mem_plane d t (p y)
  · intro h
    exact hpy (by
      have hpre : p y ∈ (tangentInclusion d t) ⁻¹' ((tangentInclusion d t) '' C) := h
      rwa [actual_zeroSection_centre_preimage d t C] at hpre)

end ActualBlowups

end
end TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupLift
