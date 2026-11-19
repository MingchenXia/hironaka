import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictTraceFactor

/-! Same-centre relative STRICT for an actual selected smooth subcarrier.
Source-first complete chapter: hironaka-g4-smooth-subcarrier-residual-step.tex.
No arbitrary all-row order persistence or recursive history is inferred. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SmoothSubcarrierResidualStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings MonomialCase BlowupFlatCoordinates
  HironakaSharpOriginalFirstMemberRelativeStrict HironakaSharpActualControlledRelativeSaturation
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualFirstAmbientStrictTraceFactor
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}


/-- A genuine reduced vanishing ideal has no hidden exceptional saturation
when its actual support is dense off the actual SNC divisor. -/
theorem relativeExceptionalSaturation_vanishingIdeal_eq (hn : 0 < n) {N Z D : Set X}
    (hD : IsSNCDivisor n [D]) (hZN : Z ⊆ N) (hdense : Z ⊆ closure (Z \ D)) :
    relativeExceptionalSaturation N (vanishingIdeal (n := n) Z) D=
      vanishingIdeal (n := n) Z := by
  ext x g
  constructor
  · rintro ⟨k,hg,hcolon⟩
    by_cases hxD : x ∈ D
    · obtain ⟨Φ,σ,_hsrc,_h0,_hinj,hA⟩ := exists_snc_chart hn hD x
      have hxFlat : x ∈ flatDomain Φ := mem_flatDomain_self Φ
      have hflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
          chartAt (ComplexModel n) x y ∈ Φ.source →
          (y ∈ D ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ 0)=0) :=
        hA 0 hxD
      let a : X → ℂ := flatCoord Φ (σ 0)
      have ha : HolomorphicAt n a x := holomorphicAt_flatCoord Φ (σ 0) hxFlat
      have haD : (vanishingIdeal (n := n) D).mem x a :=
        (MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ hflat hxFlat a).mpr
          (isInSpanAt_self rfl ha)
      have htest := hcolon (fun y => a y^k) (MonomialPart.pow_mem_idealPow haD ha k)
      have hzero := MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt hZN htest.1 htest.2
      have hflatNear : ∀ᶠ y in 𝓝 x,y ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds hxFlat
      have hnear : ∀ᶠ y in 𝓝 x,y ∈ flatDomain Φ ∧ HolomorphicAt n g y ∧
          (y ∈ Z → a y^k*g y=0) := hflatNear.and (hg.eventually.and hzero.2)
      obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hnear
      have hEq : EqOn g (fun _ => (0 : ℂ)) ((Z \ D) ∩ V) := by
        intro y hy
        have hyFlat := (hVsub hy.2).1
        have hane : a y≠0 := fun h => hy.1.2 ((hflat hyFlat.1 hyFlat.2).mpr h)
        exact (mul_eq_zero.mp ((hVsub hy.2).2.2 hy.1.1)).resolve_left (pow_ne_zero _ hane)
      have hcont : ContinuousOn g (Z ∩ V) :=
        fun y hy => ((hVsub hy.2).2.1.continuousAt).continuousWithinAt
      have hclosure : Z ∩ V ⊆ closure ((Z \ D) ∩ V) :=
        fun y hy => hVo.closure_inter ⟨hdense hy.1,hy.2⟩
      have hEqAll : EqOn g (fun _ => (0 : ℂ)) (Z ∩ V) :=
        hEq.of_subset_closure hcont continuousOn_const (fun _ hy => ⟨hy.1.1,hy.2⟩) hclosure
      refine ⟨hg,?_⟩
      filter_upwards [hVo.mem_nhds hxV] with y hy hyZ
      exact hEqAll ⟨hyZ,hy⟩
    · have h1D : (vanishingIdeal (n := n) D).mem x (1 : X → ℂ) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hD.1 D (by simp)).isOpen_compl.mem_nhds hxD] with y hy hyD
        exact False.elim (hy hyD)
      have h1pow : (idealPow (vanishingIdeal (n := n) D) k).mem x (1 : X → ℂ) := by
        change (idealPow (vanishingIdeal (n := n) D) k).mem x (fun _ => 1)
        simpa using MonomialPart.pow_mem_idealPow h1D (holomorphicAt_const 1) k
      have htest := hcolon (1 : X → ℂ) h1pow
      have hvan := MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt hZN htest.1 htest.2
      convert hvan using 1
      funext y
      simp
  · intro hg
    refine ⟨0,hg.1,fun a ha => ?_⟩
    change HolomorphicAt n a x at ha
    have hprod : (vanishingIdeal (n := n) Z).mem x (a*g) := by
      refine ⟨ha.mul hg.1,?_⟩
      filter_upwards [hg.2] with y hy hyZ
      change a y*g y=0
      rw [hy hyZ,mul_zero]
    exact ⟨hprod.1,IsInSpanAt.restrict (isInSpanAt_self hprod hprod.1)⟩


/-- The SAME real centre carries a selected genuine smooth subcarrier to its
literal smooth strict transform, with the WHOLE relative STRICT ideal. -/
theorem actual_smooth_subcarrier_relative_strict (hn : 0 < n) {N Z C : Set X}
    (hN : IsClosedSubmanifold n N) (hZ : IsClosedSubmanifold n Z) (hZN : Z ⊆ N)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCZ : C ⊆ Z) :
    IsClosedSubmanifold n (geoStrictTransform π C Z) ∧
      nextRelativeStrict N (vanishingIdeal (n := n) Z) C π=
        vanishingIdeal (n := n) (geoStrictTransform π C Z) := by
  let N' := geoStrictTransform π C N
  let Z' := geoStrictTransform π C Z
  let D := π ⁻¹' C
  have hCN : C ⊆ N := hCZ.trans hZN
  have hZsmooth : IsClosedSubmanifold n Z' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hZ hCZ
  have hZsub : Z' ⊆ N' := by
    apply closure_mono
    intro y hy
    exact ⟨hZN hy.1,hy.2⟩
  have hdense : Z' ⊆ closure (Z' \ D) := by
    apply closure_mono
    intro y hy
    exact ⟨subset_closure hy,hy.2⟩
  have hD : IsSNCDivisor n [D] := BlowupSNCTransform.isSNCDivisor_preimage_centre hπ
  have hTrace := actual_first_controlled_ambient_strict_trace hN hZ hπ hCN hCZ
  have hSat := geoTransform_relativeExceptionalSaturation_eq hn
    (⟨N,[],vanishingIdeal (n := n) Z,1⟩ : MarkedIdeal n X) hπ
  change relativeExceptionalSaturation N'
    ((⟨N,[],vanishingIdeal (n := n) Z,1⟩ : MarkedIdeal n X).geoTransform C π).ideal D=
      nextRelativeStrict N (vanishingIdeal (n := n) Z) C π at hSat
  rw [hTrace] at hSat
  have hRemove : relativeExceptionalSaturation N' (restrictOn n N' (vanishingIdeal (n := n) Z')) D=
      relativeExceptionalSaturation N' (vanishingIdeal (n := n) Z') D := by
    ext y g
    exact relativeExceptionalSaturation_restrictOn_mem_iff N' (vanishingIdeal (n := n) Z') D y g
  have hReduced := relativeExceptionalSaturation_vanishingIdeal_eq hn hD hZsub hdense
  exact ⟨hZsmooth,hSat.symm.trans (hRemove.trans hReduced)⟩

end
end Hironaka.HironakaG4SmoothSubcarrierResidualStep
