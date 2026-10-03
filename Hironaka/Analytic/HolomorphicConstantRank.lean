/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod
set_option autoImplicit false

/-!
# The constant rank theorem for holomorphic maps

Let `G: E → F` be holomorphic on an open set `U` of a finite-dimensional complex normed space, with `rank dG_z = r`
for every `z ∈ U`, and `p ∈ U`. Write `L = dG_p`, `R = range L` (dimension `r`) and `K = ker L`.

* `exists_normalForm`: there are continuous linear projections `Q : F → R` and `S : E → K`, a
  ball `B` around `Ψ p` in `R × K`, where `Ψ z = (Q (G z), S z)`, a holomorphic inverse `ψ : B → U`
  of `Ψ` (`Ψ (ψ w) = w`, `ψ (Ψ p) = p`, `ψ '' B` open), and a holomorphic `k` on the first factor
  of `B` with `Q ∘ k = id` and the normal form
  `G (ψ w) = k w.1`  for `w ∈ B`:
  in the chart `ψ`, `G` depends only on the first `r` coordinates and is the graph map `k` there.
* `exists_ne_mem_fibre`: if `r < dim E`, then `p` is an accumulation point of its fibre
  `G⁻¹(G p)`.

## Proof

`Ψ = (Q ∘ G, S)` has derivative `(Q ∘ L, S)` at `p`, which is injective (a vector killed by both
lies in `K` and is fixed by `S`), hence bijective by rank--nullity, so the inverse function theorem
gives `ψ`.  On `B`, `H = G ∘ ψ` satisfies `Q ∘ dH = fst` (first component of `dΨ`), and
`rank dH = rank dG = r = dim R`; so `Q` is injective on `range dH`, and `dH (0, v) = 0` because
`Q (dH (0, v)) = 0`.  Hence `H` is constant along the convex slices `{w'} × ball`, which is the
normal form with `k w' = H (w', c)`.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Hironaka.HolomorphicConstantRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Linear algebra of the constant rank theorem**: if `A : R × K → F` satisfies `Q ∘ A = fst`
and `dim range A = dim R`, then `A` vanishes on the second factor. -/
theorem apply_inr_eq_zero {R K : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
    [FiniteDimensional ℂ R] [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : R × K →L[ℂ] F) (Q : F →L[ℂ] R) (hQA : Q.comp A = ContinuousLinearMap.fst ℂ R K)
    (hrank : Module.finrank ℂ (LinearMap.range (A : R × K →ₗ[ℂ] F)) = Module.finrank ℂ R)
    (v : K) : A (0, v) = 0 := by
  -- `Q` restricted to `range A` is onto `R`, hence injective
  set Q' : LinearMap.range (A : R × K →ₗ[ℂ] F) →ₗ[ℂ] R :=
    (Q : F →ₗ[ℂ] R).comp (LinearMap.range (A : R × K →ₗ[ℂ] F)).subtype with hQ'
  have hsurj : Function.Surjective Q' := by
    intro w
    refine ⟨⟨A (w, 0), LinearMap.mem_range_self _ _⟩, ?_⟩
    have := congrArg (fun T : R × K →L[ℂ] R => T (w, 0)) hQA
    simpa [hQ'] using this
  have hinj : Function.Injective Q' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hsurj
  have h0 : Q' ⟨A (0, v), LinearMap.mem_range_self _ _⟩ = Q' 0 := by
    have := congrArg (fun T : R × K →L[ℂ] R => T (0, v)) hQA
    simpa [hQ'] using this
  have := hinj h0
  simpa using congrArg Subtype.val this

omit [FiniteDimensional ℂ F] in
/-- The derivative of `(Q ∘ G, S)` at `p` is injective, hence a linear equivalence. -/
theorem bijective_prod_comp {L : E →L[ℂ] F}
    (Q : F →L[ℂ] LinearMap.range (L : E →ₗ[ℂ] F)) (S : E →L[ℂ] LinearMap.ker (L : E →ₗ[ℂ] F))
    (hQ : ∀ y : LinearMap.range (L : E →ₗ[ℂ] F), Q y = y)
    (hS : ∀ x : LinearMap.ker (L : E →ₗ[ℂ] F), S x = x) :
    Function.Bijective ((Q.comp L).prod S) := by
  have hinj : Function.Injective ((Q.comp L).prod S) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : Q (L x) = 0 := congrArg Prod.fst hx
    have h2 : S x = 0 := congrArg Prod.snd hx
    have hLx : L x = 0 := by
      have := hQ ⟨L x, LinearMap.mem_range_self _ x⟩
      rw [h1] at this
      exact (congrArg Subtype.val this).symm
    have hxK : x ∈ LinearMap.ker (L : E →ₗ[ℂ] F) := hLx
    have := hS ⟨x, hxK⟩
    rw [h2] at this
    exact (congrArg Subtype.val this).symm
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℂ E =
      Module.finrank ℂ (LinearMap.range (L : E →ₗ[ℂ] F) × LinearMap.ker (L : E →ₗ[ℂ] F)) := by
    rw [Module.finrank_prod, LinearMap.finrank_range_add_finrank_ker]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (((Q.comp L).prod S : E →L[ℂ] _) : E →ₗ[ℂ] _)) hdim).1 hinj

/-- **The constant rank theorem, normal form.**  Let `G` be holomorphic on the open set `U` with
`rank dG_z = r` for all `z ∈ U`, and `p ∈ U`; let `R = range dG_p`, `K = ker dG_p`.  There are
projections `Q : F → R`, `S : E → K`, a radius `ρ > 0` and holomorphic maps `ψ` (on the ball `B` of
radius `ρ` around `Ψ p = (Q (G p), S p)`) and `k` (on the ball of radius `ρ` around `Q (G p)`) such
that `ψ` is a holomorphic inverse of `Ψ z = (Q (G z), S z)` on `B` with open image, `Q ∘ k = id`,
and `G (ψ w) = k w.1` on `B`. -/
theorem exists_normalForm {G : E → F} {U : Set E} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    {r : ℕ}
    (hr : ∀ z ∈ U, Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) = r)
    {p : E} (hp : p ∈ U) :
    ∃ (Q : F →L[ℂ] LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F))
      (S : E →L[ℂ] LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F))
      (ψ : LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) ×
          LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) → E)
      (k : LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) → F) (ρ : ℝ),
      0 < ρ ∧ IsOpen (ψ '' ball (Q (G p), S p) ρ) ∧ ψ (Q (G p), S p) = p ∧
      (∀ w ∈ ball (Q (G p), S p) ρ, ψ w ∈ U ∧ (Q (G (ψ w)), S (ψ w)) = w) ∧
      DifferentiableOn ℂ ψ (ball (Q (G p), S p) ρ) ∧
      DifferentiableOn ℂ k (ball (Q (G p)) ρ) ∧
      (∀ w ∈ ball (Q (G p)) ρ, Q (k w) = w) ∧
      ∀ w ∈ ball (Q (G p), S p) ρ, G (ψ w) = k w.1 := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  obtain ⟨R', hR'⟩ := (LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)).exists_isCompl
  obtain ⟨K', hK'⟩ := (LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)).exists_isCompl
  let Q := (Submodule.projectionOnto _ R' hR').toContinuousLinearMap
  let S := (Submodule.projectionOnto _ K' hK').toContinuousLinearMap
  have hQ : ∀ y, Q (Subtype.val y) = y := fun y => Submodule.projectionOnto_apply_left hR' y
  have hS : ∀ x, S (Subtype.val x) = x := fun x => Submodule.projectionOnto_apply_left hK' x
  have hGs : ContDiffOn ℂ ∞ G U := Hironaka.contDiffOn_of_differentiableOn_complex hG hU
  have hGstrict : HasStrictFDerivAt G (fderiv ℂ G p) p :=
    ((hGs p hp).contDiffAt (hU.mem_nhds hp)).hasStrictFDerivAt (by simp)
  have hbij := bijective_prod_comp (L := fderiv ℂ G p) Q S hQ hS
  have : CompleteSpace (LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) ×
      LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)) := FiniteDimensional.complete ℂ _
  let A : E →ₗ[ℂ] LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) ×
      LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) :=
    ((Q.comp (fderiv ℂ G p)).prod S).toLinearMap
  have hA : Function.Bijective A := hbij
  let e := (LinearEquiv.ofBijective A hA).toContinuousLinearEquiv
  have hecoe : (e : E →L[ℂ] _) = (Q.comp (fderiv ℂ G p)).prod S := rfl
  let Ψ := fun z => (Q (G z), S z)
  have hΨd : ∀ z ∈ U, HasFDerivAt Ψ ((Q.comp (fderiv ℂ G z)).prod S) z := fun z hz =>
    (Q.hasFDerivAt.comp z ((hG z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt).prodMk
      S.hasFDerivAt
  have hΨs : HasStrictFDerivAt Ψ (e : E →L[ℂ] _) p :=
    (Q.hasStrictFDerivAt.comp p hGstrict).prodMk S.hasStrictFDerivAt
  let φ := hΨs.toOpenPartialHomeomorph Ψ
  have hpφ : p ∈ φ.source := hΨs.mem_toOpenPartialHomeomorph_source
  -- the derivative of `Ψ` depends continuously on the point
  have hDc : ContinuousOn (fun z => (Q.comp (fderiv ℂ G z)).prod S) U := by
    have hfd : ContinuousOn (fderiv ℂ G) U := hGs.continuousOn_fderiv_of_isOpen hU (by simp)
    have h1 : ContinuousOn (fun z => Q.comp (fderiv ℂ G z)) U :=
      (ContinuousLinearMap.compL ℂ E F _ Q).continuous.comp_continuousOn hfd
    exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp_continuousOn (h1.prodMk continuousOn_const)
  -- the open set where `dΨ` is invertible, inside the source of `φ`
  let Ω : Set E := (U ∩ (fun z => (Q.comp (fderiv ℂ G z)).prod S) ⁻¹'
    {A | A.IsInvertible}) ∩ φ.source
  have hΩo : IsOpen Ω :=
    (hDc.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen).inter φ.open_source
  have hpΩ : p ∈ Ω := ⟨⟨hp, e, hecoe⟩, hpφ⟩
  -- a ball around `Ψ p` inside `φ.target ∩ φ.symm ⁻¹' Ω`
  have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' Ω) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hΩo
  have hΨp : Ψ p ∈ φ.target ∩ φ.symm ⁻¹' Ω := by
    refine ⟨φ.map_source hpφ, ?_⟩
    have : φ.symm (Ψ p) = p := φ.left_inv hpφ
    show φ.symm (Ψ p) ∈ Ω
    rw [this]
    exact hpΩ
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hT (Ψ p) hΨp
  have hmemΩ : ∀ w ∈ ball (Ψ p) ρ, φ.symm w ∈ Ω := fun w hw => (hball hw).2
  have hright : ∀ w ∈ ball (Ψ p) ρ, Ψ (φ.symm w) = w := fun w hw => φ.right_inv (hball hw).1
  -- the derivative of `ψ = φ.symm` and of `H = G ∘ ψ` on the ball
  have hder : ∀ w ∈ ball (Ψ p) ρ, ∃ M : E ≃L[ℂ] (LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) :
      E →ₗ[ℂ] F) × LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)),
      HasFDerivAt φ.symm (M.symm : _ →L[ℂ] E) w ∧
      HasFDerivAt (fun w => G (φ.symm w)) ((fderiv ℂ G (φ.symm w)).comp (M.symm : _ →L[ℂ] E)) w ∧
      (M : E →L[ℂ] _) = (Q.comp (fderiv ℂ G (φ.symm w))).prod S := by
    intro w hw
    obtain ⟨⟨hzU, M, hM⟩, hzs⟩ := hmemΩ w hw
    have hΨz : HasFDerivAt φ (M : E →L[ℂ] _) (φ.symm w) := by
      rw [hM]; exact hΨd _ hzU
    have hψ := φ.hasFDerivAt_symm (hball hw).1 hΨz
    refine ⟨M, hψ, ?_, hM⟩
    exact ((hG _ hzU).differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp w hψ
  have hdual : ∀ w ∈ ball (Ψ p) ρ, ∀ v,
      (fderiv ℂ (fun w => G (φ.symm w)) w) (0, v) = 0 := by
    intro w hw v
    obtain ⟨M, -, hH, hM⟩ := hder w hw
    rw [hH.fderiv]
    have hzU : φ.symm w ∈ U := (hmemΩ w hw).1.1
    refine apply_inr_eq_zero _ Q ?_ ?_ v
    · refine ContinuousLinearMap.ext fun x => ?_
      have h1 := congrArg (fun T => (T (M.symm x)).1) hM
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply] at h1
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe]
      exact h1.symm.trans (by simp)
    · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top]
      · rw [hr _ hzU, ← hr p hp]
      · exact LinearMap.range_eq_top.2 M.symm.surjective
  -- `H = G ∘ ψ` is constant along the slices `{w.1} × ball`
  have hballprod : ball (Ψ p) ρ = ball (Ψ p).1 ρ ×ˢ ball (Ψ p).2 ρ := (ball_prod_same _ _ _).symm
  have hHdiff : ∀ w ∈ ball (Ψ p) ρ, DifferentiableAt ℂ (fun w => G (φ.symm w)) w := fun w hw => by
    obtain ⟨M, -, hH, -⟩ := hder w hw
    exact hH.differentiableAt
  have hslice : ∀ w ∈ ball (Ψ p) ρ, G (φ.symm w) = G (φ.symm (w.1, (Ψ p).2)) := by
    intro w hw
    have hw' : w ∈ ball (Ψ p).1 ρ ×ˢ ball (Ψ p).2 ρ := hballprod ▸ hw
    have hmem : ∀ t ∈ ball (Ψ p).2 ρ, (w.1, t) ∈ ball (Ψ p) ρ := fun t ht =>
      hballprod ▸ (Set.mk_mem_prod hw'.1 ht)
    let f := fun t => G (φ.symm (w.1, t))
    have hfd : ∀ t ∈ ball (Ψ p).2 ρ, HasFDerivAt f
        ((fderiv ℂ (fun w => G (φ.symm w)) (w.1, t)).comp
          (ContinuousLinearMap.inr ℂ _ _)) t := fun t ht =>
      (hHdiff _ (hmem t ht)).hasFDerivAt.comp t (hasFDerivAt_prodMk_right w.1 t)
    have hf0 : ∀ t ∈ ball (Ψ p).2 ρ, fderivWithin ℂ f (ball (Ψ p).2 ρ) t = 0 := by
      intro t ht
      rw [fderivWithin_of_isOpen isOpen_ball ht, (hfd t ht).fderiv]
      refine ContinuousLinearMap.ext fun v => ?_
      simpa using hdual _ (hmem t ht) v
    have := Convex.is_const_of_fderivWithin_eq_zero (convex_ball _ _)
      (fun t ht => (hfd t ht).differentiableAt.differentiableWithinAt) hf0 hw'.2
      (mem_ball_self hρ)
    simpa [f] using this
  refine ⟨Q, S, φ.symm, fun w' => G (φ.symm (w', (Ψ p).2)), ρ, hρ, ?_, φ.left_inv hpφ,
    fun w hw => ⟨(hmemΩ w hw).1.1, hright w hw⟩, ?_, ?_, ?_, fun w hw => hslice w hw⟩
  · have hsub : ball (Ψ p) ρ ⊆ φ.target := fun w hw => (hball hw).1
    show IsOpen (φ.symm '' ball (Ψ p) ρ)
    rw [φ.symm_image_eq_source_inter_preimage hsub]
    exact φ.isOpen_inter_preimage isOpen_ball
  · intro w hw
    obtain ⟨M, hψ, -, -⟩ := hder w hw
    exact hψ.differentiableAt.differentiableWithinAt
  · intro w' hw'
    have hmem : (w', (Ψ p).2) ∈ ball (Ψ p) ρ := hballprod ▸ Set.mk_mem_prod hw' (mem_ball_self hρ)
    exact (DifferentiableAt.comp (g := fun w => G (φ.symm w)) w' (hHdiff _ hmem)
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) w' (Ψ p).2).differentiableAt).differentiableWithinAt
  · intro w' hw'
    have hmem : (w', (Ψ p).2) ∈ ball (Ψ p) ρ := hballprod ▸ Set.mk_mem_prod hw' (mem_ball_self hρ)
    exact congrArg Prod.fst (hright _ hmem)

/-- **Positive-dimensional fibres.** Under the hypotheses of `exists_normalForm`, if the rank `r`
is smaller than `dim E`, then `p` is an accumulation point of its fibre: every neighbourhood of `p`
contains a point `z ≠ p` with `G z = G p`. -/
theorem exists_ne_mem_fibre {G : E → F} {U : Set E} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    {r : ℕ}
    (hr : ∀ z ∈ U, Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) = r)
    {p : E} (hp : p ∈ U) (hlt : r < Module.finrank ℂ E) {V : Set E} (hV : V ∈ 𝓝 p) :
    ∃ z ∈ V, z ≠ p ∧ G z = G p := by
  obtain ⟨Q, S, ψ, k, ρ, hρ, -, hψp, hψ, hψd, -, -, hnf⟩ := exists_normalForm hU hG hr hp
  have hK : 0 < Module.finrank ℂ (LinearMap.ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)) := by
    have := LinearMap.finrank_range_add_finrank_ker ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)
    rw [hr p hp] at this
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hK
  set c := (Q (G p), S p) with hc
  let γ : ℂ → _ := fun s => (c.1, c.2 + s • v)
  have hγ : Continuous γ := by fun_prop
  have hγ0 : γ 0 = c := by simp [γ]
  have hψc : ContinuousAt ψ c :=
    hψd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ ball c ρ ∧ ψ (γ s) ∈ V := by
    have h1 : Tendsto γ (𝓝 0) (𝓝 c) := hγ0 ▸ hγ.tendsto 0
    have hV' : ∀ᶠ w in 𝓝 c, ψ w ∈ V := hψc.preimage_mem_nhds (hψp.symm ▸ hV)
    have hB : ∀ᶠ w in 𝓝 c, w ∈ ball c ρ := isOpen_ball.mem_nhds (mem_ball_self hρ)
    exact h1.eventually (hB.and hV')
  have hev1 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), γ s ∈ ball c ρ ∧ ψ (γ s) ∈ V := nhdsWithin_le_nhds hev
  have hev' : ∀ᶠ s in 𝓝[≠] (0 : ℂ), (γ s ∈ ball c ρ ∧ ψ (γ s) ∈ V) ∧ s ≠ 0 :=
    hev1.and self_mem_nhdsWithin
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := hev'.exists
  refine ⟨ψ (γ s), hs2, fun h => ?_, ?_⟩
  · have h1 := (hψ (γ s) hs1).2
    rw [h] at h1
    have h2 := congrArg Prod.snd h1
    simp only [γ, c, left_eq_add, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact hs0 h2
    · exact hv h2
  · have h3 := hnf c (mem_ball_self hρ)
    rw [hψp] at h3
    rw [hnf _ hs1, h3]

end Hironaka.HolomorphicConstantRank
