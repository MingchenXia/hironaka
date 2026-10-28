import TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupLift
import TranscendentalNakamaye.Pending.SubmanifoldCodRestrict
import TranscendentalNakamaye.Pending.SubmanifoldIdealRestriction
import TranscendentalNakamaye.Pending.MarkedIdealGeoTransform
import TranscendentalNakamaye.Pending.BlowupUniqueness

/-!
# Genuine zero-section blowup compatibility with the whole strict carrier

The strict carrier's pointwise regularity and actual flattening atlas are
constructed internally. Its real exceptional invertibility gives the reverse
universal lift. Base and ambient universal uniqueness prove the two inverses.
No strict-carrier smoothness/equivalence, desired whole ideal or algorithm
compatibility is supplied by the caller. The convention is geoStrictTransform.
Blueprint: hironaka-actual-zero-section-blowup-comparison-extension.tex.
Source-only; no kernel acceptance is claimed.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupComparison

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  HironakaRelativeNormalIdeal HironakaActualZeroSectionCentreSheaf
  HironakaActualZeroSectionBlowupLift HironakaSmoothSubmersionOrderedChoiceImageTrace
  BlowupStrictSubmanifold SubmanifoldChartedSpace SubmanifoldCodRestrict
  SubmanifoldIdealRestriction BlowupExceptionalDivisor RestrictedIdealQuotient

/-- Genuine original ambient blowup data and the actual plane geometry produce
pointwise regularity of the WHOLE strict carrier, not a caller smoothness input. -/
theorem actual_zeroSection_strict_regular {d t : ℕ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    {C : Set (ComplexModel d)} {π : Y → ComplexModel (d+t)}
    (hπ : IsBlowupAlong (d+t) ((tangentInclusion d t) '' C) π)
    (y : Y) (hy : y ∈ geoStrictTransform π ((tangentInclusion d t) '' C)
      (complexCoordinatePlane (d+t) d)) :
    RegularAtDim (n := d+t)
      (geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d)) y d := by
  apply regularAtDim_geoStrictTransform hπ (actual_zeroSection_plane_closed d t)
    (actual_zeroSection_plane_regular d t) ?_ hy
  rintro _ ⟨x, _hx, rfl⟩
  exact tangentInclusion_mem_plane d t x

/-- The explicit whole geometric output for a constructed atlas. This is only
an output predicate, never a caller comparison or smoothness certificate. -/
def actualZeroSectionComparisonFor {d t : ℕ} {B Y : Type}
    [TopologicalSpace B] [ChartedSpace (ComplexModel d) B] [IsComplexManifold d B]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    (C : Set (ComplexModel d)) (p : B → ComplexModel d) (π : Y → ComplexModel (d+t))
    (cs : ChartedSpace (ComplexModel d)
      (geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d))) : Prop :=
    let S := geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d)
    letI := cs
    ∃ E : B ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ S,
      (∀ x, π (E x).val = tangentInclusion d t (p x)) ∧
      (∀ y : S, p (E.symm y) = tangentProjection d t (π y.val)) ∧
      Set.range (fun x => (E x).val) = S ∧
      GermIdeal.pullback (m := d) (fun x => (E x).val)
          (GermIdeal.pullback (m := d+t) π
            (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))) =
        GermIdeal.pullback (m := d) p (vanishingIdeal (n := d) C)

/-- ONLY two prescribed genuine original blowups internally supply a genuine
complex manifold on the whole strict carrier and a true biholomorphism over
the zero section, with its literal full exceptional ideal equality. -/
theorem exists_actual_zeroSection_blowup_comparison {d t : ℕ} {B Y : Type}
    [TopologicalSpace B] [ChartedSpace (ComplexModel d) B] [IsComplexManifold d B]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    {C : Set (ComplexModel d)} {p : B → ComplexModel d} {π : Y → ComplexModel (d+t)}
    (hp : IsBlowupAlong d C p)
    (hπ : IsBlowupAlong (d+t) ((tangentInclusion d t) '' C) π) :
    ∃ cs : ChartedSpace (ComplexModel d)
        (geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d)),
      @IsComplexManifold d _ _ cs ∧ actualZeroSectionComparisonFor C p π cs := by
  let S := geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d)
  have hreg : ∀ y ∈ S, RegularAtDim (n := d+t) S y d :=
    actual_zeroSection_strict_regular hπ
  have hdt : d ≤ d+t := by omega
  let cs := chartedSpace hdt hreg
  let : ChartedSpace (ComplexModel d) S := cs
  have hS : IsComplexManifold d S := isComplexManifold_chartedSpace hdt hreg
  let : IsComplexManifold d S := hS
  have hval : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞
      (Subtype.val : S → Y) := contMDiff_val hdt hreg
  have hi : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d+t)) ∞
      (tangentInclusion d t) := (tangentInclusion d t).contDiff.contMDiff
  obtain ⟨f, ⟨hf, hcomm⟩, _hfunique⟩ := existsUnique_actual_zeroSection_blowup_lift hp hπ
  have hfS (x : B) : f x ∈ S := actual_zeroSection_lift_mem_geoStrictTransform hp f hf hcomm x
  let fS : B → S := fun x => ⟨f x, hfS x⟩
  have hfs : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ fS :=
    contMDiff_codRestrict hdt hreg hf hfS
  let q : S → ComplexModel d := (tangentProjection d t) ∘ (π ∘ Subtype.val)
  have hq : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ q :=
    (tangentProjection d t).contDiff.contMDiff.comp (hπ.contMDiff.comp hval)
  have hiq : (tangentInclusion d t) ∘ q = π ∘ (Subtype.val : S → Y) := by
    funext y
    exact tangentInclusion_projection_eq_of_mem_plane d t
      (geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (actual_zeroSection_plane_closed d t) y.property)
  have halong := MarkedIdeals.MarkedIdeal.isInvertibleAlong_geoStrictTransform hπ
    (complexCoordinatePlane (d+t) d) 1
  change IsInvertibleAlong (d+t) S (IdealWeightPowers.idealPow (exceptionalDivisor hπ).ideal 1) at halong
  rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at halong
  have hres := isInvertible_restrictIdeal hval halong
  change (GermIdeal.pullback (m := d) (Subtype.val : S → Y)
    (GermIdeal.pullback (m := d+t) π
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)))).IsInvertible at hres
  have hqideal : GermIdeal.pullback (m := d) q (vanishingIdeal (n := d) C) =
      GermIdeal.pullback (m := d) (Subtype.val : S → Y)
        (GermIdeal.pullback (m := d+t) π
          (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))) := by
    calc
      _ = GermIdeal.pullback (m := d) q
          (GermIdeal.pullback (m := d) (tangentInclusion d t)
            (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))) := by
        rw [actual_zeroSection_centre_sheaf d t C]
      _ = GermIdeal.pullback (m := d) ((tangentInclusion d t) ∘ q)
          (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) :=
        (whole_pullback_comp hi hq
          (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) (fun _ _ ha => ha.1)).symm
      _ = GermIdeal.pullback (m := d) (π ∘ (Subtype.val : S → Y))
          (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) := by rw [hiq]
      _ = _ := whole_pullback_comp hπ.contMDiff hval
        (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) (fun _ _ ha => ha.1)
  have hqinv : (GermIdeal.pullback (m := d) q (vanishingIdeal (n := d) C)).IsInvertible := by
    rw [hqideal]
    exact hres
  obtain ⟨g, ⟨hg, hpg⟩, _hgunique⟩ := hp.2.2.2.2 d S q hq hqinv
  have hqf : q ∘ fS = p := by
    funext x
    change tangentProjection d t (π (f x)) = p x
    have hxcomm : π (f x) = tangentInclusion d t (p x) := congrFun hcomm x
    rw [hxcomm, tangentProjection_tangentInclusion]
  have hgf : g ∘ fS = id := by
    apply BlowupUniqueness.eq_id_of_comp_eq hp (hg.comp hfs)
    calc
      p ∘ (g ∘ fS) = (p ∘ g) ∘ fS := rfl
      _ = q ∘ fS := by rw [hpg]
      _ = p := hqf
  have hiqinv : (GermIdeal.pullback (m := d) ((tangentInclusion d t) ∘ q)
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C))).IsInvertible := by
    rw [whole_pullback_comp hi hq
      (vanishingIdeal (n := d+t) ((tangentInclusion d t) '' C)) (fun _ _ ha => ha.1),
      actual_zeroSection_centre_sheaf d t C]
    exact hqinv
  obtain ⟨_u, _hu, huniq⟩ := hπ.2.2.2.2 d S ((tangentInclusion d t) ∘ q)
    (hi.comp hq) hiqinv
  have hfgval : f ∘ g = (Subtype.val : S → Y) := by
    apply ExistsUnique.unique ⟨_u, _hu, huniq⟩
    · refine ⟨hf.comp hg, ?_⟩
      calc
        π ∘ (f ∘ g) = (π ∘ f) ∘ g := rfl
        _ = ((tangentInclusion d t) ∘ p) ∘ g := by rw [hcomm]
        _ = (tangentInclusion d t) ∘ (p ∘ g) := rfl
        _ = (tangentInclusion d t) ∘ q := by rw [hpg]
    · exact ⟨hval, hiq.symm⟩
  let E : B ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ S :=
    { toEquiv :=
        { toFun := fS
          invFun := g
          left_inv := fun x => congrFun hgf x
          right_inv := fun y => Subtype.ext (congrFun hfgval y) }
      contMDiff_toFun := hfs
      contMDiff_invFun := hg }
  refine ⟨cs, hS, E, ?_, ?_, ?_, ?_⟩
  · exact fun x => congrFun hcomm x
  · exact fun y => congrFun hpg y
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (E x).property
    · intro hy
      exact ⟨E.symm ⟨y, hy⟩, congrArg Subtype.val (E.apply_symm_apply ⟨y, hy⟩)⟩
  · exact actual_zeroSection_lift_exceptional_ideal hp hπ
      (fun x => (E x).val) (hval.comp E.contMDiff) (funext fun x => congrFun hcomm x)

end
end TranscendentalNakamaye.Pending.HironakaActualZeroSectionBlowupComparison
