import Hironaka.Resolution.HironakaG1RecursiveBornOrderTwoCompanionExample

/-! The actual order-two coefficient and homogenization operations on the
recursive born companion. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornOrderTwoBarExample
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec CanonicalCentres GeneralValue NonmonomialOrderTail
  StepOneValue StepOneLowerDomain StepOneValueMasked
  HomogenizedIdealAlong HomogenizedEquivalence HomogenizedGlueing
  DerivativeIdealAlong DerivativeIdealAlongCoherent RelativePrincipalizationSpan
  RestrictedIdealExtension IdealWeightPowers CoefficientIdeal GermIdealPullbackCalculus
  RestrictLeCalculus HironakaG8CoeffClass
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1InitialPositiveGeneralRead HironakaG1RecursiveBornOrderTwoCompanionExample

section MarkTwo
variable {n : ℕ} {X : CMfd.{0} n}

/-- At true mark two, homogenization sums the original ideal and the square
of its first tangential derivative ideal. -/
theorem homogenized_mark_two (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : M.d = 2) :
    (homMarkedAlong M).ideal =
      sumIdeal M.ideal (idealPow (derivIdealAlong M.N M.ideal) 2) := by
  let D := derivIdealAlong M.N M.ideal
  have hD : D.IsCoherent := isCoherent_derivIdealAlong hM.isCoherent hM.isClosedSubmanifold_N
  let F (i : ℕ) := (iterDerivIdealAlong M.N M.ideal i).mul (idealPow D i)
  have hf₀ : F 0 = M.ideal := mul_unitIdeal hM.isCoherent
  have hf₁ : F 1 = idealPow D 2 := by
    change D.mul (idealPow D 1) = idealPow D 2
    rw [idealPow_succ D 1, idealPow_one_eq hD]
  have hF (i : ℕ) (hi : i ≤ 1) : (F i).IsCoherent := by
    have hCases : i = 0 ∨ i = 1 := by omega
    rcases hCases with rfl | rfl
    · exact hf₀.symm ▸ hM.isCoherent
    · exact hf₁.symm ▸ isCoherent_idealPow hD 2
  change homogenizedIdealAlong M.N M.ideal M.d = _
  rw [hd]
  change finSumIdeal F 2 = _
  rw [finSumIdeal_succ hF, finSumIdeal_one (hF 0 (by decide)), hf₀, hf₁]

/-- At true mark two, a coefficient step keeps the same mark and adds the
square of the first tangential derivative ideal. -/
theorem coefficient_mark_two (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : M.d = 2) :
    (coeffMarkedAlong M).d = 2 ∧ (coeffMarkedAlong M).ideal =
      sumIdeal M.ideal (idealPow (derivIdealAlong M.N M.ideal) 2) := by
  let D := derivIdealAlong M.N M.ideal
  let F (i : ℕ) := idealPow (iterDerivIdealAlong M.N M.ideal i)
    (sumExp (fun j => 2 - j) 2 i)
  have hD : D.IsCoherent := isCoherent_derivIdealAlong hM.isCoherent hM.isClosedSubmanifold_N
  have hf₀ : F 0 = M.ideal := by
    change idealPow M.ideal 1 = _
    exact idealPow_one_eq hM.isCoherent
  have hf₁ : F 1 = idealPow D 2 := rfl
  have hF (i : ℕ) (hi : i ≤ 1) : (F i).IsCoherent := by
    have hCases : i = 0 ∨ i = 1 := by omega
    rcases hCases with rfl | rfl
    · exact hf₀.symm ▸ hM.isCoherent
    · exact hf₁.symm ▸ isCoherent_idealPow hD 2
  constructor
  · change ((Finset.range M.d).prod (fun j => M.d - j)) = 2
    rw [hd]
    decide
  · change finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
       (sumExp (fun j => M.d - j) M.d i)) M.d = _
    rw [hd]
    change finSumIdeal F 2 = _
    rw [finSumIdeal_succ hF, finSumIdeal_one (hF 0 (by decide)), hf₀, hf₁]

/-- The original bar and its contact coefficient stage both preserve the
actual mark two. The marked ideal still has the same cosupport after bar. -/
theorem original_bar_and_contact_mark_two (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : M.d = 2) :
    let H := homMarkedAlong M
    let P := barMarked M
    H.ideal = sumIdeal M.ideal (idealPow (derivIdealAlong M.N M.ideal) 2) ∧
    P.d = 2 ∧ P.cosupp = M.cosupp ∧
    P.ideal = sumIdeal H.ideal (idealPow (derivIdealAlong H.N H.ideal) 2) ∧
    (coeffMarkedAlong P).d = 2 ∧
    (coeffMarkedAlong P).ideal = sumIdeal P.ideal (idealPow (derivIdealAlong P.N P.ideal) 2) := by
  intro H P
  have hH : H.IsWellFormed := ⟨hM.isClosedSubmanifold_N,
    isCoherent_homogenizedIdealAlong hM.isCoherent hM.isClosedSubmanifold_N M.d,
    hM.isSNCDivisor, hM.isTransverse⟩
  have hP := isWellFormed_barMarked M hM
  have hHP := coefficient_mark_two H hH hd
  have hPP := coefficient_mark_two P hP hHP.1
  exact ⟨homogenized_mark_two M hM hd, hHP.1, cosupp_barMarked M hM (hd ▸ (by decide : 1 ≤ 2)),
    hHP.2, hPP.1, hPP.2⟩

end MarkTwo

private abbrev A := geoTransformAlong record B
private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z

/-- The actual order-two restart keeps mark two throughout bar and the
next contact coefficient operation, and retains the original anchor. -/
theorem actual_recursive_born_contact_marks :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let K : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) K 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
      ∃ hx : x ∈ U,
        let a : U := ⟨x, hx⟩
        (barMarked Q).d = 2 ∧ (coeffMarkedAlong (barMarked Q)).d = 2 ∧
        a ∈ (barMarked Q).cosupp := by
  obtain ⟨hq, hz, hx, hQeq, hQ, _, ha, _, _, _⟩ := selected_born_order_two_companion
  have hd := congrArg MarkedIdeal.d hQeq
  obtain ⟨_, hBar, hCos, _, hCoeff, _⟩ := original_bar_and_contact_mark_two _ hQ.isWellFormed hd
  exact ⟨hq, hz, hx, hBar, hCoeff, hCos.symm ▸ ha⟩

open GermIdealOrder MonomialPartAlong

set_option maxHeartbeats 700000 in
/-- On the literal section defined by the first coordinate, the doubly
weighted coefficient ideal has order at least two and contains the square
of the third coordinate in its restricted span. -/
theorem actual_recursive_born_coordinate_coefficient_bounds :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let K : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) K 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
      ∃ hx : x ∈ U,
        let a : U := ⟨x, hx⟩
        let C := Q.N ∩ {u : U | yChart.toFun u.val.val.val (0 : Fin 3) = 0}
        let J' := coeffMarkedAlong (barMarked Q)
        J'.d = 2 ∧ a ∈ cosupport 3 C J'.ideal 2 ∧
        IsInSpanOnAt (n := 3) C (J'.ideal.mem a) a
          (fun u : U => yChart.toFun u.val.val.val (2 : Fin 3) ^ 2) := by
  obtain ⟨hq, hz, hx, hC, hd, hTrace⟩ := selected_order_two_coordinate_trace
  obtain ⟨hq', hz', hx', _, hQ, _, ha, _, _, _⟩ := selected_born_order_two_companion
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let K : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) K 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
  let a : U := ⟨x, hx⟩
  let C := Q.N ∩ {u : U | yChart.toFun u.val.val.val (0 : Fin 3) = 0}
  let H := homMarkedAlong Q
  let J' := coeffMarkedAlong (barMarked Q)
  have hH : H.IsWellFormed := ⟨hQ.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homogenizedIdealAlong hQ.isWellFormed.isCoherent hQ.isWellFormed.isClosedSubmanifold_N Q.d,
    hQ.isWellFormed.isSNCDivisor, hQ.isWellFormed.isTransverse⟩
  have hB := isWellFormed_barMarked Q hQ.isWellFormed
  obtain ⟨hH', hBMark, hBCos, hBI, hJMark, hJI⟩ :=
    original_bar_and_contact_mark_two Q hQ.isWellFormed hd
  have hQH : Q.ideal.Le H.ideal := by
    rw [hH']
    exact le_sumIdeal_left hQ.isWellFormed.isCoherent
  have hHB : H.ideal.Le (barMarked Q).ideal := by
    rw [hBI]
    exact le_sumIdeal_left hH.isCoherent
  have hBJ : (barMarked Q).ideal.Le J'.ideal := by
    change (barMarked Q).ideal.Le (coeffMarkedAlong (barMarked Q)).ideal
    rw [hJI]
    exact le_sumIdeal_left hB.isCoherent
  have hIncl : Q.ideal.Le J'.ideal := fun u g hg => hBJ u g (hHB u g (hQH u g hg))
  have hBC : a ∈ (barMarked Q).cosupp := hBCos.symm ▸ ha
  have hJ : a ∈ J'.cosupp := by
    have hCos := cosupp_coeffMarkedAlong (𝔪 := barMarked Q) hB.isClosedSubmanifold_N.2
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isCoherent hg)
      (show 1 ≤ (barMarked Q).d from hBMark.symm ▸ (by decide : 1 ≤ 2))
    exact hCos.symm ▸ hBC
  have hOrd : a ∈ cosupport 3 C J'.ideal 2 := by
    refine ⟨hC, fun f hf => ?_⟩
    have hv : VanishesToOrderOn 3 J'.N a J'.d f := hJ.2 f hf
    have himp : C ⊆ J'.N := inter_subset_left
    have hdJ : J'.d = 2 := hJMark
    rw [hdJ] at hv
    exact hv.mono_set himp
  let f : U → ℂ := fun u => yChart.toFun u.val.val.val (2 : Fin 3) ^ 2
  have hRaw := (hTrace f).mpr (isInSpanOnAt_eq_iff.mpr
    ⟨fun _ => 1, holomorphicAt_const 1, Eventually.of_forall fun _ _ => (one_mul _).symm⟩)
  exact ⟨hq, hz, hx, hJMark, hOrd, IsInSpanOnAt.mono (fun g hg => hIncl a g hg) hRaw⟩

open DerivativeIdealAlongEtale MonomialPartEtale OrderTaylor CompanionReduction
  HironakaG1RecursiveBornResidualExample HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar HironakaRelativeNormalIdeal BlowupMonomialCharts
  BlowupFlatCoordinates BlowupConstruction IdealOrderArithmetic

private abbrev X₀ := CMfd.of (n := 3) (productOpen (⊤ : Opens (ComplexModel 2)))
private abbrev p₀ : X₀ := zeroSection (⊤ : Opens (ComplexModel 2)) ⟨0, mem_univ _⟩
private abbrev F : Set Y := π ⁻¹' ({p₀} : Set X₀)
private abbrev f (w : ComplexModel 3) : Y :=
  yChart.invFun (w (2 : Fin 3) • EuclideanSpace.single (2 : Fin 3) (1 : ℂ))

private theorem f_chart (w : ComplexModel 3) :
    f w ∈ F ∧ yChart.toFun (f w) (0 : Fin 3) = 0 ∧
      yChart.toFun (f w) (2 : Fin 3) = w (2 : Fin 3) := by
  let u := w (2 : Fin 3) • EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  have hs : f w ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all u)
  have hR : yChart.toFun (f w) = u := yChart.toPartialEquiv.right_inv (chart_all u)
  refine ⟨?_, by rw [hR]; simp [u], by rw [hR]; simp [u]⟩
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  have hp : p₀.val = 0 := map_zero (tangentInclusion 2 1)
  rw [chart_projection _ hs, hp, hR]
  ext i
  by_cases hi : i = 1
  · subst i
    simp [monomial_apply, u]
  · simp [monomial_apply, u, hi]

private theorem f_diff (w : ComplexModel 3) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) f w := by
  let e : ComplexChart 3 Y :=
    ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩
  have hp : DifferentiableAt ℂ (fun u : ComplexModel 3 => u (2 : Fin 3)) w :=
    (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiableAt
  have h := hp.smul (differentiableAt_const (EuclideanSpace.single (2 : Fin 3) (1 : ℂ)))
  exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) e.property
    (chart_all _)).comp w h.mdifferentiableAt

set_option maxHeartbeats 1200000 in
/-- The double-coefficient ideal on the actual coordinate section has
ordinary order exactly two at the survivor, with the true mark still two. -/
theorem actual_recursive_born_coordinate_coefficient_exact_order :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let Z := CMfd.of (n := 3) (O z)
      let x : O z := ⟨z, hz⟩
      let K : MarkedIdeal 3 Z := L z
      let U := ordMask (M := Z) K 2
      let P := CMfd.of (n := 3) U
      let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
      ∃ hx : x ∈ U,
        let a : U := ⟨x, hx⟩
        let C := Q.N ∩ {u : U | yChart.toFun u.val.val.val (0 : Fin 3) = 0}
        let J' := coeffMarkedAlong (barMarked Q)
        J'.d = 2 ∧ a ∈ cosupport 3 C J'.ideal 2 ∧ a ∉ cosupport 3 C J'.ideal 3 := by
  obtain ⟨hq, hz, hx, hD, hTwo, hSpan⟩ := actual_recursive_born_coordinate_coefficient_bounds
  obtain ⟨hq', hz', hx', hQeq, _, _, _, _, _, _⟩ := selected_born_order_two_companion
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have e₃ : hx' = hx := Subsingleton.elim _ _
  subst hx'
  obtain ⟨hq', hz', _, _, hN, _, _⟩ := selected_born_trace_gens
  have e₁ : hq' = hq := Subsingleton.elim _ _
  subst hq'
  have e₂ : hz' = hz := Subsingleton.elim _ _
  subst hz'
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let K : MarkedIdeal 3 Z := L z
  let U := ordMask (M := Z) K 2
  let P := CMfd.of (n := 3) U
  let Q : MarkedIdeal 3 P := compAt (X := Z) K 2 (BlowupTower.refl (X := Z))
  let a : U := ⟨x, hx⟩
  let C := Q.N ∩ {u : U | yChart.toFun u.val.val.val (0 : Fin 3) = 0}
  let J' := coeffMarkedAlong (barMarked Q)
  refine ⟨hq, hz, hx, hD, hTwo, fun hThree => ?_⟩
  have hNc : Q.N = (Subtype.val : U → O z) ⁻¹' K.N := by
    have h := congrArg (fun M : MarkedIdeal 3 P => M.N) hQeq
    exact h
  let g : U → ℂ := fun u => yChart.toFun u.val.val.val (2 : Fin 3) ^ 2
  obtain ⟨j, s, b, hs, hb, hEq⟩ := hSpan
  have hsOrd (i : Fin j) : VanishesToOrderOn 3 C a 3 (s i) := hThree.2 _ (hs i)
  obtain ⟨c, hc, he⟩ := vanishesToOrderOn_sum_mul hb hsOrd
  have hg : VanishesToOrderOn 3 C a 3 g := by
    refine ⟨c, hc, ?_⟩
    filter_upwards [hEq, he] with y hy₁ hy₂ hyC
    exact (hy₁ hyC).trans (hy₂ hyC)
  let ψ₁ := openInv W z
  let ψ₂ := openInv (O z) x
  let ψ₃ := openInv U a
  have h₁ := isLocalInverseAt_val (n := 3) W z
  have h₂ := isLocalInverseAt_val (n := 3) (O z) x
  have h₃ := isLocalInverseAt_val (n := 3) U a
  have hf₀ : f 0 = q := by simp [f]
  have ht : Tendsto f (𝓝 0) (𝓝 q) := hf₀ ▸ (f_diff 0).continuousAt.tendsto
  have ht₁ : Tendsto ψ₁ (𝓝 q) (𝓝 z) := h₁.tendsto
  have ht₂ : Tendsto ψ₂ (𝓝 z) (𝓝 x) := h₂.tendsto
  let θ := ψ₃ ∘ ψ₂ ∘ ψ₁ ∘ f
  have hθ₀ : θ 0 = a := by
    change ψ₃ (ψ₂ (ψ₁ (f 0))) = a
    rw [hf₀, show ψ₁ q = z from h₁.left_inv.self_of_nhds,
      show ψ₂ z = x from h₂.left_inv.self_of_nhds]
    exact h₃.left_inv.self_of_nhds
  have hθ : ∀ᶠ w : ComplexModel 3 in 𝓝 0,
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w := by
    filter_upwards [ht.eventually h₁.mdiff_inv, (ht₁.comp ht).eventually h₂.mdiff_inv,
      (ht₂.comp (ht₁.comp ht)).eventually h₃.mdiff_inv] with w hu₁ hu₂ hu₃
    exact hu₃.comp w (hu₂.comp w (hu₁.comp w (f_diff w)))
  have hNear : ∀ᶠ w : ComplexModel 3 in 𝓝 0, θ w ∈ C ∧ g (θ w) = w (2 : Fin 3) ^ 2 := by
    filter_upwards [ht.eventually h₁.right_inv, (ht₁.comp ht).eventually h₂.right_inv,
      (ht₂.comp (ht₁.comp ht)).eventually h₃.right_inv] with w hw₁ hw₂ hw₃
    have hVal : (θ w).val.val.val = f w := by
      change (ψ₃ (ψ₂ (ψ₁ (f w)))).val.val.val = f w
      change (ψ₃ (ψ₂ (ψ₁ (f w)))).val = ψ₂ (ψ₁ (f w)) at hw₃
      change (ψ₂ (ψ₁ (f w))).val = ψ₁ (f w) at hw₂
      rw [hw₃, hw₂]
      exact hw₁
    obtain ⟨hF, h0, h2⟩ := f_chart w
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hNc]
      change (θ w).val ∈ (L z).N
      rw [hN]
      change (θ w).val.val.val ∈ F
      rwa [hVal]
    · change yChart.toFun ((θ w).val.val.val) (0 : Fin 3) = 0
      rwa [hVal]
    · change yChart.toFun ((θ w).val.val.val) (2 : Fin 3) ^ 2 = _
      rw [hVal, h2]
  obtain ⟨b, hb, hbe⟩ := vanishesToOrderOn_comp (θ := θ) hθ (hθ₀.symm ▸ hg)
  have hbEq : (fun w : ComplexModel 3 => w (2 : Fin 3) ^ 2) =ᶠ[𝓝 0] b := by
    filter_upwards [hNear, hbe] with w hw hw'
    exact hw.2.symm.trans (hw' hw.1)
  let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
    BlowupExistenceOriginIdeal.idEquivAt
  have hnot := MonomialCase.flatCoord_notMem_idealPow_two Φ 2 (mem_flatDomain_self Φ)
  have hh : HolomorphicAt 3 (fun w : ComplexModel 3 => w (2 : Fin 3)) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).mdifferentiableAt
  exact pow_notMem_idealPow (o := 1) hh hnot 2 (mem_idealPow_congr hb hbEq.symm)

end
end Hironaka.HironakaG1RecursiveBornOrderTwoBarExample
