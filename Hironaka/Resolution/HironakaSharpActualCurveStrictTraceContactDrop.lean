/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStrictProjectionLocalInverse

/-! Actual raw relative curve order preservation ABOVE a real discrete centre,
then true ambient strict-trace contact decreases. No chronological J substitution. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStrictTraceContactDrop
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveStrictProjectionLocalInverse HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpOriginalFirstMemberExceptionalFactor HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealOperationsAlong
  GermIdealOrder HadamardBridge IdealWeightPowers DivisorExponentAlong IdealOrderArithmetic
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings InvertibleIdealQuotient
  HironakaCoherentTransformExtension
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem actual_eventually_mdifferentiable_of_contMDiffAt {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f x) :
    ∀ᶠ y in 𝓝 x,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f y := by
  have h1 : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) 1 f x := hf.of_le (by simp)
  exact ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp h1).mono
    fun _ hy => hy.mdifferentiableAt (by simp)

private theorem actual_relative_vanishing_comp {N : Set X} {S : Set Y} {f : Y → X} {y : Y}
    (hf : ∀ᶠ z in 𝓝 y,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f z)
    (hmaps : ∀ᶠ z in 𝓝 y,z ∈ S → f z ∈ N)
    {q : ℕ} {g : X → ℂ} (hg : VanishesToOrderOn n N (f y) q g) :
    VanishesToOrderOn n S y q (g ∘ f) := by
  obtain ⟨a,ha,hga⟩ := hg
  refine ⟨a ∘ f,comp_mem_idealPow_pointIdeal hf q ha,?_⟩
  filter_upwards [hf.self_of_nhds.continuousAt.eventually hga,hmaps] with z hz hzS hS
  exact hz (hzS hS)

/-- ONLY actual curve/centre/ideal geometry internally supplies the real inverse
and BOTH whole raw relative cosupport directions, including above the centre. -/
theorem actual_curve_raw_total_cosupport_iff_above_centre
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {I : GermIdeal n X} (hcI : I.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) (q : ℕ) :
    z ∈ cosupport n (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I)) q ↔
      π z ∈ cosupport n N I q := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let P := GermIdeal.pullback (m := n) π I
  have hcP : P.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcI
  have hNorm : cosupport n N' (restrictOn n N' P) q=cosupport n N' P q :=
    Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hcP) q)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn q)
  change z ∈ cosupport n N' (restrictOn n N' P) q ↔ _
  rw [hNorm]
  obtain ⟨s,hs,hs0,hsN,_hsπ⟩ := exists_actual_curve_strict_projection_local_inverse hN hrN hrC hπ hCN hz hzC
  have hπd : ∀ᶠ y in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) π y :=
    Eventually.of_forall fun _ => hπ.contMDiff.mdifferentiableAt (by simp)
  have hπN : ∀ᶠ y in 𝓝 z,y ∈ N' → π y ∈ N := Eventually.of_forall fun _ hy =>
    BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy
  constructor
  · intro hq
    refine ⟨hπN.self_of_nhds hz,fun a ha => ?_⟩
    have hah := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcI ha
    have haP : P.mem z (a ∘ π) := GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨a,ha,rfl⟩ (holomorphicAt_comp_map hπd hah))
    have hav : VanishesToOrderOn n N' (s (π z)) q (a ∘ π) := by rw [hs0]; exact hq.2 _ haP
    have hv := actual_relative_vanishing_comp (actual_eventually_mdifferentiable_of_contMDiffAt hs)
      (hsN.mono fun _ hy hN => (hy hN).1) hav
    exact CodimOneCentreAlong.VanishesToOrderOn.congr_on hv (hsN.mono fun x hx hxN => congrArg a (hx hxN).2)
  · intro hq
    refine ⟨hz,fun g hg => ?_⟩
    apply IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact actual_relative_vanishing_comp hπd hπN (hq.2 a ha)

/-- Real zero-mark geometry supplies all finite-order premises before the BOTH
cosupport directions identify EXISTING ordinary trace orders above the centre. -/
theorem actual_curve_raw_total_order_eq_above_centre
    {N C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    {I : GermIdeal n X} (hcI : I.IsCoherent) (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N) (hzC : π z ∈ C) :
    ordinaryTraceOrder (BlowupStrictSubmanifold.geoStrictTransform π C N)
      (restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I)) z=
      ordinaryTraceOrder N I (π z) := by
  let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
  let P := restrictOn n N' (GermIdeal.pullback (m := n) π I)
  let M : MarkedIdeal n X := ⟨N,[],I,0⟩
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hcP : P.IsCoherent := isCoherent_restrictOn (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hcI)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
  have hTotal : (M.geoTransform C π).ideal=P := geoTransform_zeroMark_ideal_eq_restricted_total M rfl C π
  have hnzP : ∀ y ∈ N',IsNonzeroAlongAt N' P y := by
    rw [←hTotal]
    exact isNonzeroAlongAt_geoTransform_without_admissibility M hN hcI hπ hCN hnzI
  have hxN := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  have hq := actual_curve_raw_total_cosupport_iff_above_centre hN hrN hrC hcI hπ hCN hz hzC
  apply Nat.le_antisymm
  · apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hxN _).mp
    exact (hq _).mp ((ordinaryTraceOrder_cosupport_iff hN' hcP hnzP hz _).mpr le_rfl)
  · apply (ordinaryTraceOrder_cosupport_iff hN' hcP hnzP hz _).mp
    exact (hq _).mpr ((ordinaryTraceOrder_cosupport_iff hN hcI hnzI hxN _).mpr le_rfl)

/-- Genuine first-step strict ambient trace loses exactly one unit of curve
contact, including above the centre, from actual raw order preservation. -/
theorem actual_first_curve_ambient_strict_trace_order_drop (hn : 0 < n)
    {N H C : Set X} (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N,RegularAtDim (n := n) N x 1)
    (hrC : ∀ x ∈ C,RegularAtDim (n := n) C x 0)
    (hH : IsSNCDivisor n [H]) (hdense : N ⊆ closure (N \ H))
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N) (hCH : C ⊆ H)
    {z : Y} (hz : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C N ∩ π ⁻¹' C) :
    let N' := BlowupStrictSubmanifold.geoStrictTransform π C N
    let I' := restrictOn n N' (vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C H))
    ordinaryTraceOrder N' I' z+1=ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) ∧
      ordinaryTraceOrder N' I' z<ordinaryTraceOrder N (vanishingIdeal (n := n) H) (π z) := by
  have hHc : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHc
  have hnzH : ∀ x ∈ N,IsNonzeroAlongAt N (vanishingIdeal (n := n) H) x := fun _ hx =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hx
  have hRaw := actual_curve_raw_total_order_eq_above_centre hN hrN hrC hcH hnzH hπ hCN hz.1 hz.2
  have hNew := (actual_first_raw_total_strict_trace_exponent_shift hn hN hH hdense hπ hCN hCH z hz).1
  have hTotal : (memberTotalMarked N H C π).ideal=
      restrictOn n (BlowupStrictSubmanifold.geoStrictTransform π C N) (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) H)) :=
    geoTransform_zeroMark_ideal_eq_restricted_total (⟨N,[],vanishingIdeal (n := n) H,0⟩ : MarkedIdeal n X) rfl C π
  rw [hTotal,hRaw] at hNew
  dsimp only
  omega

end
end Hironaka.HironakaSharpActualCurveStrictTraceContactDrop
