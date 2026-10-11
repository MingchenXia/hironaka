/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDivisorResidual
import Hironaka.Analytic.SNCDivisorLocalGenerator

set_option autoImplicit false

/-!
# The genuine residual unit producer for an SNC-supported divisor

Source: Włodarczyk 2005, Step 2; full mathematical proof in
`blueprint/src/hironaka-divisor-unit-extension.tex`.
The private support-containment chart helper retains the existing pure
proof of `SNCSupportedDivisorFixedChartNormalForm` without importing
that module's metric consumers. The new producer derives the residual
unit property from actual support containment and connectedness.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDivisorResidualUnit

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings InvertibleIdealQuotient HironakaDivisorResidual
  HironakaDivisorPowers DivisorExponent GermIdealOrder GermIdealTotalTransform
  IdealWeightPowers SNCDivisorLocalGenerator RelativePrincipalizationSpan

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- In each ball, a point lies on just the indicated coordinate hyperplane. -/
theorem exists_coordinate_unit_point (j : Fin n) {r : ℝ} (hr : 0 < r) :
    ∃ z : ComplexModel n, z ∈ ball 0 r ∧ z j = 0 ∧ ∀ i : Fin n, i ≠ j → z i ≠ 0 := by
  classical
  let v : ComplexModel n := WithLp.toLp 2 (fun i => if i = j then 0 else (1 : ℂ))
  let δ : ℝ := r / (‖v‖ + 1)
  let z : ComplexModel n := δ • v
  have hd : 0 < δ := div_pos hr (by positivity)
  have hdR : δ * (‖v‖ + 1) = r := by
    dsimp only [δ]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < ‖v‖ + 1))
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  · simp [z, v]
  · intro i hi
    change δ • (if i = j then (0 : ℂ) else 1) ≠ 0
    rw [if_neg hi]
    exact smul_ne_zero hd.ne' one_ne_zero

/-- Genuine invertibility and SNC geometry supply the full local generator and its monomial. -/
private theorem exists_adapted_unit_monomial_generator_subset
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ H ∈ E, H) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : M → ℂ, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ i, x ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | x ∈ E.get i} ∧
        (∀ i, x ∈ E.get i → ∀ {y : M}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j := by
  classical
  obtain ⟨U, hU, hxU, g, hg, hnon, hgen⟩ := D.isInvertible x
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 x
  let e := complexChartAt (n := n) x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  let T : ComplexModel n → M := fun z => e.val.symm (Φ.invFun z)
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_chart_source (ComplexModel n) x)]
  have hTc : ContinuousAt T 0 :=
    (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
      ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    simpa only [hT0] using hTc.tendsto
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  let G : ComplexModel n → ℂ := fun z => g (T z)
  have hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z := by
    have hchart := differentiableOn_comp_chartSymm x hg
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    filter_upwards [Φ.isOpen_target.mem_nhds h0t, hT.eventually (hU.mem_nhds hxU)] with z hz hzU
    have hcoord : DifferentiableAt ℂ (fun w => g (e.val.symm w)) (Φ.invFun z) :=
      hchart.differentiableAt (hopen.mem_nhds ⟨hsrc (Φ.mapsTo_invFun hz), hzU⟩)
    exact hcoord.comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))
  have hzero : ∀ᶠ z in 𝓝 0, G z = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t,
      hT.eventually (hU.mem_nhds hxU), hT.eventually havoid] with z hz hzU hzavoid hGz
    have hsup : T z ∈ D.support :=
      (mem_support_iff_generator_eq_zero D
        (holomorphicAt_of_mdifferentiableOn hU hg hzU) (hgen (T z) hzU)).mpr hGz
    have hmem : ∃ H ∈ E, T z ∈ H := by
      have hsup' := hsupport hsup
      obtain ⟨F, hF⟩ := mem_iUnion.mp hsup'
      obtain ⟨hFE, hzF⟩ := mem_iUnion.mp hF
      exact ⟨F, hFE, hzF⟩
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
    have hxi : x ∈ E.get i := by
      by_contra h
      exact hzavoid i h hi
    have htarget : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz)
    have hy : T z ∈ e.val.source := e.val.map_target htarget
    have hphi : e.val (T z) ∈ Φ.source := by
      dsimp only [T]
      rw [e.val.right_inv htarget]
      exact Φ.mapsTo_invFun hz
    have heq : Φ.toFun (e.val (T z)) = z := by
      dsimp only [T]
      rw [e.val.right_inv htarget, Φ.right_inv z hz]
    have hsub : z ∈ coordSubspace (S i) := by
      rw [← heq]
      exact (hflat i hxi hy hphi).mp hi
    have hpos : 0 < (S i).card := by rw [hcard i hxi]; norm_num
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, hsub j hj⟩
  obtain ⟨a, H, hH, hH0, hfactor⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hG hzero
  exact ⟨U, hU, hxU, g, hg, hnon, hgen, S, Φ, hsrc, h0, hcard, hinj, hflat,
    a, H, hH, hH0, hfactor⟩


/-- A zero of the actual generator forces one actual SNC member to lie
locally in the support. No local factor or component certificate is an input. -/
theorem exists_member_locally_in_support (R : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : R.support ⊆ ⋃ W ∈ E, W) {x : M} (hx : x ∈ R.support) :
    ∃ W ∈ E, x ∈ W ∧ ∀ᶠ y in 𝓝 x, y ∈ W → y ∈ R.support := by
  classical
  obtain ⟨U, hU, hxU, g, hg, -, hgen, S, Φ, hsrc, h0, hcard, -, hflat,
    a, H, -, hH0, hfactor⟩ :=
    exists_adapted_unit_monomial_generator_subset R E hE hsupport x
  let e := complexChartAt (n := n) x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  let T : ComplexModel n → M := fun z => e.val.symm (Φ.invFun z)
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_complexChartAt_source x)]
  have ht : Tendsto T (𝓝 0) (𝓝 x) := by
    have hTc : ContinuousAt T 0 :=
      (e.val.continuousAt_symm (hsrc (Φ.mapsTo_invFun h0t))).comp
        ((Φ.invFun_holomorphic.differentiableAt
          (Φ.isOpen_target.mem_nhds h0t)).continuousAt)
    simpa only [hT0] using hTc.tendsto
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  have hgx : g x = 0 :=
    (mem_support_iff_generator_eq_zero R
      (holomorphicAt_of_mdifferentiableOn hU hg hxU) (hgen x hxU)).mp hx
  have hpos : ∃ j : Fin n, 0 < a j := by
    by_contra! hn
    have ha0 : ∀ j, a j = 0 := fun j => Nat.eq_zero_of_le_zero (hn j)
    have heq := hfactor.self_of_nhds
    change g (T 0) = H 0 * ∏ j : Fin n, (0 : ComplexModel n) j ^ a j at heq
    rw [hT0, hgx] at heq
    simp only [ha0, pow_zero, Finset.prod_const_one, mul_one] at heq
    exact hH0 heq.symm
  obtain ⟨j, hj⟩ := hpos
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Φ.target ∧ T z ∈ U ∧
      (∀ i : Fin E.length, x ∉ E.get i → T z ∉ E.get i) ∧
      g (T z) = H z * ∏ k : Fin n, z k ^ a k := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t,
      ht.eventually (hU.mem_nhds hxU), ht.eventually havoid, hfactor]
      with z hz hzU hzavoid hzfactor
    exact ⟨hz, hzU, hzavoid, hzfactor⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  obtain ⟨z, hz, hzj, hzother⟩ := exists_coordinate_unit_point j hr
  obtain ⟨hzΦ, hzU, hzavoid, hzfactor⟩ := hball hz
  have hprod : ∏ k : Fin n, z k ^ a k = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hzj, zero_pow (Nat.ne_of_gt hj)]
  have hgz : g (T z) = 0 := by rw [hzfactor, hprod, mul_zero]
  have hsup : T z ∈ R.support :=
    (mem_support_iff_generator_eq_zero R
      (holomorphicAt_of_mdifferentiableOn hU hg hzU) (hgen (T z) hzU)).mpr hgz
  have hmem : ∃ W ∈ E, T z ∈ W := by
    obtain ⟨W, hW⟩ := mem_iUnion.mp (hsupport hsup)
    obtain ⟨hWE, hzW⟩ := mem_iUnion.mp hW
    exact ⟨W, hWE, hzW⟩
  obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp hmem
  have hxi : x ∈ E.get i := by
    by_contra h
    exact hzavoid i h hi
  have htarget : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hzΦ)
  have hzsource : T z ∈ e.val.source := e.val.map_target htarget
  have hchart : e.val (T z) = Φ.invFun z := e.val.right_inv htarget
  have hφ : e.val (T z) ∈ Φ.source := by rw [hchart]; exact Φ.mapsTo_invFun hzΦ
  have heq : Φ.toFun (e.val (T z)) = z := by rw [hchart, Φ.right_inv z hzΦ]
  have hsub : z ∈ coordSubspace (S i) := by
    rw [← heq]
    exact (hflat i hxi hzsource hφ).mp hi
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (hcard i hxi)
  have hkj : k = j := by
    by_contra h
    exact hzother k h (hsub k (by rw [hk]; exact Finset.mem_singleton_self k))
  have hSi : S i = {j} := by simpa only [hkj] using hk
  let P : M → ComplexModel n := fun y => Φ.toFun (e.val y)
  have hp : Tendsto P (𝓝 x) (𝓝 (0 : ComplexModel n)) := by
    have hc : ContinuousAt P x :=
      (Φ.toFun_holomorphic.differentiableAt
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).continuousAt.comp
          (e.val.continuousAt (mem_complexChartAt_source x))
    have hP0 : P x = 0 := h0
    simpa only [hP0] using hc.tendsto
  refine ⟨E.get i, List.get_mem _ _, hxi, ?_⟩
  filter_upwards [e.val.open_source.mem_nhds (mem_complexChartAt_source x),
    (e.val.continuousAt (mem_complexChartAt_source x)).tendsto.eventually
      (Φ.isOpen_source.mem_nhds Φ.center_mem_source),
    hU.mem_nhds hxU, hp.eventually hfactor] with y hye hyΦ hyU hyfactor hyW
  have hycoord : P y ∈ coordSubspace (S i) := (hflat i hxi hye hyΦ).mp hyW
  have hypj : P y j = 0 := hycoord j (by rw [hSi]; exact Finset.mem_singleton_self j)
  have hTP : T (P y) = y := by
    dsimp only [T, P]
    rw [Φ.left_inv _ hyΦ, e.val.left_inv hye]
  have hprodY : ∏ k : Fin n, P y k ^ a k = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hypj, zero_pow (Nat.ne_of_gt hj)]
  apply (mem_support_iff_generator_eq_zero R
    (holomorphicAt_of_mdifferentiableOn hU hg hyU) (hgen y hyU)).mpr
  change g (T (P y)) = H (P y) * ∏ k : Fin n, P y k ^ a k at hyfactor
  rw [hTP, hprodY, mul_zero] at hyfactor
  exact hyfactor

/-- Actual divisor exponents propagate a local support component on each
connected smooth member, forcing a component-free residual to have empty support. -/
theorem support_eq_empty_of_no_component (R : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hconnected : ∀ W ∈ E, ∃ d, IsClosedConnectedSubmanifold n W d)
    (hsupport : R.support ⊆ ⋃ W ∈ E, W) (hnot : ∀ W ∈ E, ¬ W ⊆ R.support) :
    R.support = ∅ := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible R.isInvertible
  have hcos : cosupport n univ R.ideal 1 = R.support := by
    rw [cosupport_one (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hcoh hf),
      univ_inter]
    rfl
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨W, hWE, hxW, hlocal⟩ := exists_member_locally_in_support R E hE hsupport hx
  obtain ⟨d, hW⟩ := hconnected W hWE
  obtain ⟨a, ha⟩ := exists_divExp_on_connected_submanifold hW hcoh
    (fun y => isNonzeroAt_of_isInvertible R.isInvertible y)
  have hxdiv : IsDivNear n R.ideal W 1 x := by
    change ∀ᶠ y in 𝓝 x, y ∈ W → y ∈ cosupport n univ R.ideal 1
    simpa only [hcos] using hlocal
  have h1a : 1 ≤ a := (ha x hxW 1).mp hxdiv
  apply hnot W hWE
  intro y hy
  have hydiv := (ha y hy 1).mpr h1a
  rw [← hcos]
  exact hydiv.self_of_nhds hy

/-- The complete actual residual germ ideal is the unit ideal. -/
theorem ideal_eq_unitIdeal_of_no_component (R : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hconnected : ∀ W ∈ E, ∃ d, IsClosedConnectedSubmanifold n W d)
    (hsupport : R.support ⊆ ⋃ W ∈ E, W) (hnot : ∀ W ∈ E, ¬ W ⊆ R.support) :
    R.ideal = unitIdeal n M :=
  BlowupTowerTransforms.eq_unitIdeal_of_zeroLocus_eq_empty
    (DivisorMetric.isCoherent_of_isInvertible R.isInvertible)
    (support_eq_empty_of_no_component R E hE hconnected hsupport hnot)

/-- Actual connected-component extraction and the residual unit producer
give a finite monomial equality of the original complete germ ideal. -/
theorem exists_componentPowerProduct_eq (D : EffectiveDivisor n M)
    (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hconnected : ∀ W ∈ E, ∃ d, IsClosedConnectedSubmanifold n W d ∧ d + 1 = n)
    (hsupport : D.support ⊆ ⋃ W ∈ E, W) :
    ∃ A : List (Set M × ℕ), A.map Prod.fst = E ∧
      D.ideal = componentPowerProduct (n := n) A := by
  obtain ⟨A, hAE, R, hD, hnot, hRD⟩ :=
    exists_residual_on_finite_connected_hypersurfaces E hconnected D
  have hR := ideal_eq_unitIdeal_of_no_component R E hE
    (fun W hW => let ⟨d, hd, _⟩ := hconnected W hW; ⟨d, hd⟩)
    (hRD.trans hsupport) hnot
  have hAcoh : (componentPowerProduct (n := n) A).IsCoherent := by
    apply isCoherent_componentPowerProduct
    intro p hp
    have hpE : p.1 ∈ E := by
      rw [← hAE]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨d, hW, -⟩ := hconnected p.1 hpE
    exact ⟨hW.1, fun y hy => ⟨d, hW.2.2 y hy⟩⟩
  refine ⟨A, hAE, ?_⟩
  rw [hD, hR, RestrictLeCalculus.mul_unitIdeal hAcoh]

end
end Hironaka.HironakaDivisorResidualUnit
