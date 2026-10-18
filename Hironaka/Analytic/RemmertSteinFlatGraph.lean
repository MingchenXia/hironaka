/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.RemmertSteinFlatBadSet

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The flat case of Remmert--Stein: `E` is a graph over the good base

Blueprint `rem:remmert-stein-flat`, paragraph "Canonical defining functions", first sentence
(Demailly, *Complex analytic and differential geometry*, II.8.7).  At a point `z` of `E ∩ Q` over the
good base `B'₀ = (B' \ N) \ Σ₀`, `E` is a regular point of dimension `s` at which `π|_E` has rank `s`
(`exists_badSet`).  Reading the rank through a flattening `Φ` of `E` at `z` (`rankAt_param_eq`),
the map `v ↦ π(Φ⁻¹ v)` on the `s`-plane has invertible differential at `0`; by the holomorphic
inverse function theorem it is a local biholomorphism `Θ`, and near `z` the set `E` is the graph
`w ↦ κ(Φ⁻¹ Θ⁻¹ w)` over the open set `Θ(source)` (`exists_local_graph`), in the coordinates
`(π z, κ z - κ a)` used by the covering lemma `CoveringSymmetricFunctions`.

Sorry-free.
-/

open Set Filter Topology Metric TopologicalSpace Module
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertSteinFlat

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  RemmertStatements RankDegeneracy

variable {n p t : ℕ} {Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t))}
  {a : ComplexModel n} {δ ρ : ℝ}

/-- The good base `B'₀ = (B' \ N) \ Σ₀`. -/
def goodBase (Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)))
    (a : ComplexModel n) (δ : ℝ) (Sig₀ : Set (coverTarget Λ a δ)) : Set (ComplexModel (p + t)) :=
  (ball (Λ a).1 δ \ complexCoordinatePlane (p + t) p) \ ((↑) '' Sig₀)

theorem isOpen_goodBase {Sig₀ : Set (coverTarget Λ a δ)} (hSig : IsClosed Sig₀) :
    IsOpen (goodBase Λ a δ Sig₀) := by
  have h : goodBase Λ a δ Sig₀ = (↑) '' (Sig₀ᶜ) := by
    ext w
    constructor
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hw⟩, fun h => hwS ⟨_, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rintro ⟨y', hy', hyy'⟩
      exact hy (Subtype.ext hyy' ▸ hy')
  rw [h]
  exact (coverTarget Λ a δ).isOpen.isOpenMap_subtype_val _ hSig.isOpen_compl

/-- The covering set `Ê = {(π z, κ z - κ a) : z ∈ E ∩ Q, π z ∈ B'₀}` in `ℂˢ × ℂᵈ`. -/
def coverSet (Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)))
    (a : ComplexModel n) (δ ρ : ℝ) (E : Set (ComplexModel n)) (B₀ : Set (ComplexModel (p + t))) :
    Set (ComplexModel (p + t) × ComplexModel (n - (p + t))) :=
  (fun z => ((Λ z).1, (Λ z).2 - (Λ a).2)) '' (E ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 ∈ B₀})

theorem chart_coverSource_apply (x y : coverSource Λ a δ ρ) :
    (chartAt (ComplexModel n) x) y = (y : ComplexModel n) := by
  rw [chartAt_opens_apply]
  simp [chartAt_self_eq]

theorem chart_coverTarget_apply (x y : coverTarget Λ a δ) :
    (chartAt (ComplexModel (p + t)) x) y = (y : ComplexModel (p + t)) := by
  rw [chartAt_opens_apply]
  simp [chartAt_self_eq]

/-- **`E` is locally a holomorphic graph over the good base.** -/
theorem exists_local_graph {E : Set (ComplexModel n)} (hsn : p + t ≤ n)
    {Sig₀ : Set (coverTarget Λ a δ)} (hSig : IsClosed Sig₀)
    (hgood : ∀ z : coverSource Λ a δ ρ, (z : ComplexModel n) ∈ E → coverMap Λ a δ ρ z ∉ Sig₀ →
      RegularAtDim (n := n) ((↑) ⁻¹' E : Set (coverSource Λ a δ ρ)) z (p + t) ∧
      rankAt (n := n) (n' := p + t) (coverMap Λ a δ ρ)
        ((↑) ⁻¹' E : Set (coverSource Λ a δ ρ)) z = p + t)
    {z : ComplexModel n} (hzE : z ∈ E) (hzQ : z ∈ polydisc Λ a δ ρ)
    (hzB : (Λ z).1 ∈ goodBase Λ a δ Sig₀) :
    ∃ V ∈ 𝓝 ((Λ z).1, (Λ z).2 - (Λ a).2), ∃ U : Set (ComplexModel (p + t)), IsOpen U ∧
      ∃ g : ComplexModel (p + t) → ComplexModel (n - (p + t)), DifferentiableOn ℂ g U ∧
        coverSet Λ a δ ρ E (goodBase Λ a δ Sig₀) ∩ V = (fun w => (w, g w)) '' U := by
  classical
  set X₀ := coverSource Λ a δ ρ with hX₀
  set F₀ := coverMap Λ a δ ρ with hF₀
  set E₀ : Set X₀ := (↑) ⁻¹' E with hE₀
  set B₀ := goodBase Λ a δ Sig₀ with hB₀
  have hzX : z ∈ X₀ := ⟨hzQ, hzB.1.2⟩
  set zX : X₀ := ⟨z, hzX⟩ with hzXdef
  have hzSig : F₀ zX ∉ Sig₀ := fun h => hzB.2 ⟨_, h, rfl⟩
  obtain ⟨hreg, hrank⟩ := hgood zX hzE hzSig
  set e := (complexChartAt (n := n) zX).val with he
  obtain ⟨-, -, Φ, hΦt, hΦ0, hΦE⟩ := hreg
  have he_apply : ∀ y : X₀, e y = (y : ComplexModel n) := fun y => chart_coverSource_apply zX y
  have he_symm : ∀ u ∈ e.target, ((e.symm u : X₀) : ComplexModel n) = u := by
    intro u hu
    rw [← he_apply, e.right_inv hu]
  have hez : e zX = z := he_apply zX
  -- the flattening, read in `ℂⁿ`
  have hflat : ∀ u ∈ Φ.source, (e.symm u ∈ E₀ ↔ Φ.toFun u ∈ complexCoordinatePlane n (p + t)) := by
    intro u hu
    have hut := hΦt hu
    have := hΦE (y := e.symm u) (e.map_target hut) (by rw [e.right_inv hut]; exact hu)
    rwa [e.right_inv hut] at this
  have hflat' : ∀ u ∈ Φ.source, (u ∈ E ↔ Φ.toFun u ∈ complexCoordinatePlane n (p + t)) := by
    intro u hu
    rw [← hflat u hu]
    change u ∈ E ↔ ((e.symm u : X₀) : ComplexModel n) ∈ E
    rw [he_symm u (hΦt hu)]
  have hΦz : Φ.toFun z = 0 := by rw [← hez]; exact hΦ0
  have hzΦ : z ∈ Φ.source := by rw [← hez]; exact Φ.center_mem_source
  -- the rank through the parametrization
  set G : ComplexModel (p + t) → ComplexModel (p + t) :=
    fun v => (Λ (Φ.invFun (coordinateInclusion n (p + t) v))).1 with hG
  have hN₀ : IsOpen (coordinateInclusion n (p + t) ⁻¹' Φ.target) :=
    Φ.isOpen_target.preimage (coordinateInclusion n (p + t)).continuous
  have h0N₀ : coordinateInclusion n (p + t) 0 ∈ Φ.target := by
    rw [map_zero, ← hΦz]
    exact Φ.mapsTo_toFun hzΦ
  have hΦinv0 : Φ.invFun (coordinateInclusion n (p + t) 0) = z := by
    rw [map_zero, ← hΦz, Φ.left_inv _ hzΦ]
  have hGd : DifferentiableOn ℂ G (coordinateInclusion n (p + t) ⁻¹' Φ.target) := by
    have h1 : DifferentiableOn ℂ (fun v => Φ.invFun (coordinateInclusion n (p + t) v))
        (coordinateInclusion n (p + t) ⁻¹' Φ.target) :=
      Φ.invFun_holomorphic.comp (coordinateInclusion n (p + t)).differentiable.differentiableOn
        fun v hv => hv
    exact ((ContinuousLinearMap.fst ℂ _ _).comp Λ.toContinuousLinearMap).differentiable.comp_differentiableOn
      h1
  have hrank' : finrank ℂ (LinearMap.range
      ((fderiv ℂ G 0 : ComplexModel (p + t) →L[ℂ] ComplexModel (p + t)) : ComplexModel (p + t) →ₗ[ℂ] ComplexModel (p + t)))
      = (p + t) := by
    have hFw : F₀ (e.symm (Φ.invFun (coordinateInclusion n (p + t) 0))) ∈
        (complexChartAt (n := (p + t)) (F₀ zX)).val.source := by
      simp [complexChartAt, mem_chartAt_opens_source, chartAt_self_eq]
    obtain ⟨-, hr⟩ := rankAt_param_eq (n := n) (n' := (p + t)) (A := E₀) hsn
      (complexChartAt (n := n) zX) (complexChartAt (n := (p + t)) (F₀ zX)) (F := F₀) Φ hΦt hflat
      h0N₀ hFw (contMDiff_coverMap.mdifferentiableAt (by simp))
    have hpt : e.symm (Φ.invFun (coordinateInclusion n (p + t) 0)) = zX := by
      rw [hΦinv0, ← hez, e.left_inv (mem_chart_source _ zX)]
    rw [hpt, hrank] at hr
    have heq : (fun v => (complexChartAt (n := (p + t)) (F₀ zX)).val
        (F₀ (e.symm (Φ.invFun (coordinateInclusion n (p + t) v))))) =ᶠ[𝓝 0] G := by
      filter_upwards [hN₀.mem_nhds h0N₀] with v hv
      have hvs := Φ.mapsTo_invFun hv
      exact congrArg (fun y => (Λ y).1) (he_symm _ (hΦt hvs))
    rw [← heq.fderiv_eq]
    exact hr.symm
  have hGinj : Function.Injective (fderiv ℂ G 0) := by
    have hsurj : LinearMap.range
        ((fderiv ℂ G 0 : ComplexModel (p + t) →L[ℂ] ComplexModel (p + t)) :
          ComplexModel (p + t) →ₗ[ℂ] ComplexModel (p + t)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hrank', finrank_euclideanSpace_fin]
    have := (LinearMap.injective_iff_surjective
      (f := ((fderiv ℂ G 0 : ComplexModel (p + t) →L[ℂ] ComplexModel (p + t)) :
        ComplexModel (p + t) →ₗ[ℂ] ComplexModel (p + t)))).mpr (LinearMap.range_eq_top.mp hsurj)
    exact this
  -- the inverse function theorem on a neighbourhood keeping inside `Q ∩ π⁻¹ B'₀`
  have hB₀o : IsOpen B₀ := isOpen_goodBase hSig
  set N₁ : Set (ComplexModel (p + t)) := {v | coordinateInclusion n (p + t) v ∈ Φ.target ∧
      Φ.invFun (coordinateInclusion n (p + t) v) ∈ polydisc Λ a δ ρ ∧
      (Λ (Φ.invFun (coordinateInclusion n (p + t) v))).1 ∈ B₀} with hN₁
  have hN₁o : IsOpen N₁ := by
    have hc : ContinuousOn (fun v => Φ.invFun (coordinateInclusion n (p + t) v))
        (coordinateInclusion n (p + t) ⁻¹' Φ.target) :=
      Φ.invFun_holomorphic.continuousOn.comp (coordinateInclusion n (p + t)).continuous.continuousOn
        fun v hv => hv
    have := hc.isOpen_inter_preimage hN₀
      ((isOpen_polydisc (Λ := Λ) (a := a) (δ := δ) (ρ := ρ)).inter
        (hB₀o.preimage (continuous_fst.comp Λ.continuous)))
    convert this using 1
    ext v
    simp only [hN₁, mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.comp_apply]
  have h0N₁ : (0 : ComplexModel (p + t)) ∈ N₁ := by
    refine ⟨h0N₀, ?_, ?_⟩ <;> rw [hΦinv0]
    · exact hzQ
    · exact hzB
  obtain ⟨Θ, hΘs, hΘf, -⟩ := Hironaka.exists_localHolomorphicEquivAt hN₁o h0N₁
    (hGd.mono fun v hv => hv.1) hGinj
  -- the graph
  set g : ComplexModel (p + t) → ComplexModel (n - (p + t)) := fun w =>
    (Λ (Φ.invFun (coordinateInclusion n (p + t) (Θ.invFun w)))).2 - (Λ a).2 with hg
  have hgd : DifferentiableOn ℂ g Θ.target := by
    have h1 : DifferentiableOn ℂ (fun w => Φ.invFun (coordinateInclusion n (p + t) (Θ.invFun w)))
        Θ.target :=
      Φ.invFun_holomorphic.comp
        ((coordinateInclusion n (p + t)).differentiable.comp_differentiableOn Θ.invFun_holomorphic)
        fun w hw => (hΘs (Θ.mapsTo_invFun hw)).1
    exact (((ContinuousLinearMap.snd ℂ _ _).comp Λ.toContinuousLinearMap).differentiable.comp_differentiableOn
      h1).sub_const _
  set O : Set (ComplexModel n) := {y | y ∈ Φ.source ∧
      coordinateProjection n (p + t) (Φ.toFun y) ∈ Θ.source} with hO
  have hOo : IsOpen O :=
    Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source
      (Θ.isOpen_source.preimage (coordinateProjection n (p + t)).continuous)
  set ψ : ComplexModel (p + t) × ComplexModel (n - (p + t)) → ComplexModel n :=
    fun q => Λ.symm (q + (0, (Λ a).2)) with hψ
  have hψc : Continuous ψ := Λ.symm.continuous.comp (continuous_id.add continuous_const)
  have hψΛ : ∀ y, ψ ((Λ y).1, (Λ y).2 - (Λ a).2) = y := by
    intro y
    show Λ.symm (((Λ y).1, (Λ y).2 - (Λ a).2) + (0, (Λ a).2)) = y
    rw [show ((Λ y).1, (Λ y).2 - (Λ a).2) + ((0 : ComplexModel (p + t)), (Λ a).2) = Λ y from
      Prod.ext (by simp) (by simp)]
    exact Λ.symm_apply_apply y
  refine ⟨ψ ⁻¹' O, hψc.isOpen_preimage _ hOo |>.mem_nhds ?_, Θ.target, Θ.isOpen_target, g, hgd,
    ?_⟩
  · rw [mem_preimage, hψΛ]
    refine ⟨hzΦ, ?_⟩
    rw [hΦz, map_zero]
    exact Θ.center_mem_source
  ext ⟨w, v⟩
  constructor
  · rintro ⟨⟨y, ⟨⟨hyE, hyQ⟩, hyB⟩, hyq⟩, hqO⟩
    rw [← hyq] at hqO
    rw [mem_preimage, hψΛ] at hqO
    obtain ⟨hyΦ, hyΘ⟩ := hqO
    have hyP : Φ.toFun y ∈ complexCoordinatePlane n (p + t) := (hflat' y hyΦ).mp hyE
    set u := coordinateProjection n (p + t) (Φ.toFun y) with hu
    have hyu : y = Φ.invFun (coordinateInclusion n (p + t) u) := by
      rw [hu, coordinateInclusion_coordinateProjection hyP, Φ.left_inv _ hyΦ]
    refine ⟨Θ.toFun u, Θ.mapsTo_toFun hyΘ, ?_⟩
    rw [← hyq]
    have hΘu : Θ.toFun u = (Λ y).1 := by
      rw [hΘf]
      show (Λ (Φ.invFun (coordinateInclusion n (p + t) u))).1 = (Λ y).1
      rw [← hyu]
    simp only [Prod.mk.injEq]
    refine ⟨hΘu, ?_⟩
    simp only [hg, Θ.left_inv _ hyΘ, ← hyu]
  · rintro ⟨w', hw', hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    set u := Θ.invFun w' with hu
    have huN : u ∈ N₁ := hΘs (Θ.mapsTo_invFun hw')
    set y := Φ.invFun (coordinateInclusion n (p + t) u) with hy
    have hyΦ : y ∈ Φ.source := Φ.mapsTo_invFun huN.1
    have hΦy : Φ.toFun y = coordinateInclusion n (p + t) u := Φ.right_inv _ huN.1
    have hyE : y ∈ E := (hflat' y hyΦ).mpr (by
      rw [hΦy]; exact coordinateInclusion_mem_complexCoordinatePlane u)
    have hΘu : Θ.toFun u = w' := Θ.right_inv _ hw'
    have hy1 : (Λ y).1 = w' := by rw [← hΘu, hΘf]
    refine ⟨⟨y, ⟨⟨hyE, huN.2.1⟩, huN.2.2⟩, ?_⟩, ?_⟩
    · simp only [Prod.mk.injEq, hy1, true_and]
      rfl
    · show ψ (w', g w') ∈ O
      have : (w', g w') = ((Λ y).1, (Λ y).2 - (Λ a).2) := by
        rw [hy1]
      rw [this, hψΛ]
      refine ⟨hyΦ, ?_⟩
      rw [hΦy, coordinateProjection_coordinateInclusion hsn]
      exact Θ.mapsTo_invFun hw'

end Hironaka.RemmertSteinFlat
