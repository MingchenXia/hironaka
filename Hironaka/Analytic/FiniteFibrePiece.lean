/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ConstantRankSubmanifold
import Hironaka.Analytic.HolomorphicGenericRank
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.HolomorphicZeroSetThin
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.HolomorphicConstantRank
set_option autoImplicit false

/-!
# Manifold pieces of a parametrized irreducible germ

Let `A ⊆ ℂⁿ` carry parametrization data `P` of dimension `d` (Noether position, projection `π` onto the first `d`
coordinates) with parametrizing sets `S` on the polydisc `Δ`.

* `finite_fibre_ball`: EVERY fibre of `π` on `A ∩ ball 0 rad` is finite (a
  point over `x` has its coordinates `z_k`, `k ≥ d`, among the roots of the monic `Q_k(x, ·)`).
* `exists_isOpen_constRank`: a holomorphic map on a nonempty open set has constant rank on a
  nonempty open subset (the maximal-rank set).
* `le_dim_of_injOn`: if `φ` is holomorphic and injective on a nonempty open `U ⊆ ℂᵏ` with values
  in `A ∩ ball 0 rad`, then `k ≤ d`.  (At a point of constant maximal rank `ρ` of `π ∘ φ`, `ρ < k`
  would make the point an accumulation point of its `π ∘ φ`-fibre, which `φ` maps injectively
  into a finite fibre of `π`.)
* `exists_isOpen_subset_image`: if moreover `k = d` and `φ(U) ⊆ A ∩ Δ`, then `φ(U)` contains a
  nonempty relatively open subset of `A ∩ Δ`: `π ∘ φ` is a submersion on an open set, its image
  there meets the complement of the discriminant locus, and near such a point `A` is the graph of
  a holomorphic section of `π` (`SetsData.local_graph`), which the open image of `φ` fills.
* `exists_param_of_regularAtDim`: a regular point of dimension `k` of a subset of `ℂⁿ` is the
  image of `0` under an injective holomorphic map on an open subset of `ℂᵏ`, with values in the
  subset and in any prescribed neighbourhood (the inverse of the flattening on the plane).
-/

open Set Filter Topology Metric

noncomputable section

namespace Hironaka.FiniteFibrePiece

open Hironaka.RegularLocusDense GermParametrizationData HolomorphicConstantRank HolomorphicGenericRank ConstantRankSubmanifold

variable {n : ℕ}

/-! ### Finite fibres -/

/-- The roots of a monic polynomial with function coefficients form a finite set. -/
theorem finite_setOf_monicEval_eq_zero {E : Type*} (q : ℕ) (a : ℕ → E → ℂ) (x : E) :
    {t | monicEval q a x t = 0}.Finite := by
  classical
  open Polynomial in
  set p : ℂ[X] := X ^ q + ∑ j : Fin q, C (a j x) * X ^ (j : ℕ) with hp
  have hmonic : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have heval : monicEval q a x = fun t => p.eval t := by
    funext t
    simp [p, monicEval, Polynomial.eval_finsetSum, Finset.sum_range]
  have hset : {t | monicEval q a x t = 0} = (p.roots.toFinset : Set ℂ) := by
    ext t
    simp [heval, Polynomial.mem_roots hp0]
  rw [hset]
  exact Finset.finite_toSet _

/-- The projection onto the first `d` coordinates does not increase the norm. -/
theorem norm_coordinateProjection_le {d : ℕ} (hd : d ≤ n) (z : ComplexModel n) :
    ‖coordinateProjection n d z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have h1 : ∑ a : Fin d, ‖coordinateProjection n d z a‖ ^ 2 =
      ∑ a : Fin d, ‖z (Fin.castLE hd a)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coordinateProjection_apply, dif_pos (lt_of_lt_of_le a.2 hd)]
    rfl
  rw [h1]
  have h2 : ∑ a : Fin d, ‖z (Fin.castLE hd a)‖ ^ 2 =
      ∑ i ∈ Finset.univ.map (Fin.castLEEmb hd), ‖z i‖ ^ 2 := by
    rw [Finset.sum_map]
    rfl
  rw [h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => by positivity

/-- **Every fibre of the adapted projection on `A ∩ ball 0 rad` is finite.** -/
theorem finite_fibre_ball {A : Set (ComplexModel n)} (P : ParametrizationData A)
    (x : ComplexModel P.dim) :
    (A ∩ ball 0 P.rad ∩ coordinateProjection n P.dim ⁻¹' {x}).Finite := by
  classical
  let T : Fin n → Set ℂ := fun k =>
    if h : k.1 < P.dim then {x ⟨k.1, h⟩} else {t | monicEval (P.s k) (P.e k) x t = 0}
  have hT : ∀ k, (T k).Finite := fun k => by
    by_cases h : k.1 < P.dim
    · simp only [T, dif_pos h]
      exact finite_singleton _
    · simp only [T, dif_neg h]
      exact finite_setOf_monicEval_eq_zero _ _ _
  have hfin : (Set.pi univ T).Finite := Set.Finite.pi hT
  have hinj : Function.Injective (fun z : ComplexModel n => (fun k => z k : Fin n → ℂ)) := by
    intro a b hab
    ext k
    exact congrFun hab k
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro z ⟨⟨hzA, hzb⟩, hzx⟩
  have hzx' : coordinateProjection n P.dim z = x := hzx
  intro k _
  by_cases h : k.1 < P.dim
  · simp only [T, dif_pos h, mem_singleton_iff]
    rw [← hzx', coordinateProjection_apply, dif_pos k.2]
  · simp only [T, dif_neg h, mem_ofPred_eq]
    have := P.e_eq_zero z hzA hzb k (not_lt.mp h)
    rwa [hzx'] at this

/-! ### Constant maximal rank on an open set -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- A holomorphic map on a nonempty open set has constant rank on a nonempty open subset, and
that rank is the maximal rank on the set. -/
theorem exists_isOpen_constRank {G : E → F} {U : Set E} (hU : IsOpen U) (hUne : U.Nonempty)
    (hG : DifferentiableOn ℂ G U) :
    ∃ r : ℕ, ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧ U'.Nonempty ∧
      (∀ z ∈ U', Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) = r) ∧
      ∀ z ∈ U, Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) ≤ r := by
  classical
  set rk : E → ℕ := fun z =>
    Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) with hrk
  have hbd : ∀ z, rk z ≤ Module.finrank ℂ F := fun z => Submodule.finrank_le _
  obtain ⟨z₀, hz₀⟩ := hUne
  set r := Nat.findGreatest (fun m => ∃ z ∈ U, rk z = m) (Module.finrank ℂ F) with hr
  have hspec : ∃ z ∈ U, rk z = r :=
    Nat.findGreatest_spec (P := fun m => ∃ z ∈ U, rk z = m) (hbd z₀) ⟨z₀, hz₀, rfl⟩
  have hmax : ∀ z ∈ U, rk z ≤ r := fun z hz =>
    Nat.le_findGreatest (P := fun m => ∃ z ∈ U, rk z = m) (hbd z) ⟨z, hz, rfl⟩
  obtain ⟨z₁, hz₁U, hz₁⟩ := hspec
  refine ⟨r, {z ∈ U | rk z = r}, isOpen_maxRank hU hG hmax, fun z hz => hz.1, ⟨z₁, hz₁U, hz₁⟩,
    fun z hz => hz.2, hmax⟩

/-- **A holomorphic map with finite fibres has full generic rank**: if `G` is holomorphic on a
nonempty open set `U` and the fibres `{z ∈ U | G z = y}` are finite, the maximal rank of `dG` on
`U` is `dim E`; it is attained on a nonempty open subset. -/
theorem exists_isOpen_rank_eq_finrank_of_finite_fibre {G : E → F} {U : Set E} (hU : IsOpen U)
    (hUne : U.Nonempty) (hG : DifferentiableOn ℂ G U)
    (hfib : ∀ y, {z ∈ U | G z = y}.Finite) :
    ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧ U'.Nonempty ∧
      ∀ z ∈ U', Module.finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) =
        Module.finrank ℂ E := by
  obtain ⟨r, U', hU'o, hU'U, ⟨z₁, hz₁⟩, hr, -⟩ := exists_isOpen_constRank hU hUne hG
  have hrE : r = Module.finrank ℂ E := by
    refine le_antisymm ?_ ?_
    · rw [← hr z₁ hz₁]
      exact LinearMap.finrank_range_le _
    · by_contra hlt
      push Not at hlt
      set Fib := {z ∈ U | G z = G z₁} \ {z₁} with hFib
      have hFfin : Fib.Finite := (hfib (G z₁)).sdiff
      have hV : (Fibᶜ ∩ U') ∈ 𝓝 z₁ :=
        inter_mem (hFfin.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl) (hU'o.mem_nhds hz₁)
      obtain ⟨z, hzV, hzne, hzG⟩ :=
        exists_ne_mem_fibre hU'o (hG.mono hU'U) hr hz₁ hlt hV
      exact hzV.1 ⟨⟨hU'U hzV.2, hzG⟩, hzne⟩
  exact ⟨U', hU'o, hU'U, ⟨z₁, hz₁⟩, fun z hz => (hr z hz).trans hrE⟩

/-! ### Injective holomorphic pieces of a parametrized germ -/

variable {A : Set (ComplexModel n)}

/-- Fibres of `π ∘ φ` are finite when `φ` is injective with values in `A ∩ ball 0 rad`. -/
theorem finite_fibre_comp (P : ParametrizationData A) {k : ℕ} {U : Set (ComplexModel k)}
    {φ : ComplexModel k → ComplexModel n} (hinj : InjOn φ U)
    (hφA : MapsTo φ U (A ∩ ball 0 P.rad)) (x : ComplexModel P.dim) :
    {u ∈ U | coordinateProjection n P.dim (φ u) = x}.Finite := by
  refine Set.Finite.of_finite_image ((finite_fibre_ball P x).subset ?_) (hinj.mono fun u hu => hu.1)
  rintro _ ⟨u, ⟨huU, hux⟩, rfl⟩
  exact ⟨hφA huU, hux⟩

/-- **Manifold pieces of a parametrized germ have dimension at most `d`**
(`rem:finite-fibre-piece`, first part). -/
theorem le_dim_of_injOn (P : ParametrizationData A) {k : ℕ} {U : Set (ComplexModel k)}
    (hU : IsOpen U) (hUne : U.Nonempty) {φ : ComplexModel k → ComplexModel n}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (hφA : MapsTo φ U (A ∩ ball 0 P.rad)) :
    k ≤ P.dim := by
  have hG : DifferentiableOn ℂ (fun u => coordinateProjection n P.dim (φ u)) U :=
    (coordinateProjection n P.dim).differentiable.comp_differentiableOn hφ
  obtain ⟨U', -, -, ⟨z, hz⟩, hr⟩ :=
    exists_isOpen_rank_eq_finrank_of_finite_fibre hU hUne hG (finite_fibre_comp P hinj hφA)
  have h1 := hr z hz
  rw [finrank_euclideanSpace_fin] at h1
  rw [← h1]
  exact (Submodule.finrank_le _).trans (finrank_euclideanSpace_fin).le

/-- **A `d`-dimensional injective piece contains a relatively open subset of `A ∩ Δ`**
(`rem:finite-fibre-piece`, second part). -/
theorem exists_isOpen_subset_image (P : ParametrizationData A) (S : SetsData P)
    {U : Set (ComplexModel P.dim)} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ComplexModel P.dim → ComplexModel n} (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (hφA : MapsTo φ U (A ∩ polydisc n P.dim S.r₁ S.r₂)) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ (V ∩ (A ∩ polydisc n P.dim S.r₁ S.r₂)).Nonempty ∧
      V ∩ (A ∩ polydisc n P.dim S.r₁ S.r₂) ⊆ φ '' U := by
  set π := coordinateProjection n P.dim with hπ
  set G : ComplexModel P.dim → ComplexModel P.dim := fun u => π (φ u) with hGdef
  have hG : DifferentiableOn ℂ G U := π.differentiable.comp_differentiableOn hφ
  have hφB : MapsTo φ U (A ∩ ball 0 P.rad) := fun u hu =>
    ⟨(hφA hu).1, S.polydisc_subset (hφA hu).2⟩
  obtain ⟨U', hU'o, hU'U, ⟨z, hz⟩, hr⟩ :=
    exists_isOpen_rank_eq_finrank_of_finite_fibre hU hUne hG (finite_fibre_comp P hinj hφB)
  -- `G` is open at every point of `U'`
  have hopen : ∀ w ∈ U', ∀ O ∈ 𝓝 w, G '' O ∈ 𝓝 (G w) := fun w hw O hO =>
    image_mem_nhds_of_finrank_eq hU'o (hG.mono hU'U) hw (hr w hw) hO
  -- a point of `G '' U'` off the discriminant locus
  have hGz : G z ∈ ball (0 : ComplexModel P.dim) P.rad := by
    rw [mem_ball_zero_iff]
    exact (norm_coordinateProjection_le P.dim_le _).trans_lt
      (mem_ball_zero_iff.1 (hφB (hU'U hz)).2)
  have hcl := RiemannExtension.dense_compl_zeroSet isOpen_ball
    (convex_ball (0 : ComplexModel P.dim) P.rad).isPreconnected P.differentiableOn_disc
    (mem_ball_self P.rad_pos) P.disc_not_eventually_zero hGz
  obtain ⟨x₁, hx₁G, -, hx₁d⟩ := mem_closure_iff_nhds.1 hcl _ (hopen z hz U' (hU'o.mem_nhds hz))
  obtain ⟨z₁, hz₁, rfl⟩ := hx₁G
  have hx₁d' : P.disc (G z₁) ≠ 0 := hx₁d
  set y₁ := φ z₁ with hy₁
  have hy₁A : y₁ ∈ A ∩ polydisc n P.dim S.r₁ S.r₂ := hφA (hU'U hz₁)
  obtain ⟨Ug, Vg, g, hUgo, hVgo, hy₁Ug, hy₁Vg, -, -, -, -, -, hgsec⟩ :=
    S.local_graph y₁ hy₁A hx₁d'
  -- a neighbourhood of `z₁` mapped into `Vg`, and its open image
  have hφc : ContinuousAt φ z₁ := (hφ.differentiableAt (hU.mem_nhds (hU'U hz₁))).continuousAt
  set O₁ := U' ∩ φ ⁻¹' Vg with hO₁
  have hO₁n : O₁ ∈ 𝓝 z₁ := inter_mem (hU'o.mem_nhds hz₁) (hφc.preimage_mem_nhds (hVgo.mem_nhds hy₁Vg))
  have hGO₁ : G '' O₁ ∈ 𝓝 (G z₁) := hopen z₁ hz₁ O₁ hO₁n
  set V := Vg ∩ π ⁻¹' interior (G '' O₁) with hV
  refine ⟨V, hVgo.inter (isOpen_interior.preimage π.continuous), ⟨y₁, ⟨hy₁Vg, ?_⟩, hy₁A⟩, ?_⟩
  · exact mem_interior_iff_mem_nhds.2 hGO₁
  · rintro y ⟨⟨hyVg, hyint⟩, hyA⟩
    obtain ⟨u, ⟨huU', huVg⟩, hu⟩ := interior_subset hyint
    have h1 := (hgsec y hyVg hyA.1).2
    have h2 := (hgsec (φ u) huVg (hφA (hU'U huU')).1).2
    have hπ' : π (φ u) = π y := hu
    refine ⟨u, hU'U huU', ?_⟩
    rw [← h2, ← h1, hπ']

/-! ### Injective parametrizations at regular points -/

/-- **A regular point of dimension `k` is the centre of an injective holomorphic `k`-parameter
piece**, inside the set and inside any prescribed neighbourhood. -/
theorem exists_param_of_regularAtDim {S : Set (ComplexModel n)} {y : ComplexModel n} {k : ℕ}
    (h : RegularAtDim (n := n) (M := ComplexModel n) S y k) {W : Set (ComplexModel n)}
    (hW : W ∈ 𝓝 y) :
    ∃ (U : Set (ComplexModel k)) (φ : ComplexModel k → ComplexModel n), IsOpen U ∧
      (0 : ComplexModel k) ∈ U ∧ φ 0 = y ∧ DifferentiableOn ℂ φ U ∧ InjOn φ U ∧
      MapsTo φ U (S ∩ W) := by
  obtain ⟨hk, -, Φ, -, hΦ0, hflat⟩ := h
  have hΦ0' : Φ.toFun y = 0 := hΦ0
  have hyΦ : y ∈ Φ.source := Φ.center_mem_source
  set ι := coordinateInclusion n k with hι
  set U : Set (ComplexModel k) := ι ⁻¹' (Φ.target ∩ Φ.invFun ⁻¹' interior W) with hUdef
  have hUo : IsOpen U :=
    (Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
      isOpen_interior).preimage ι.continuous
  have hy0 : Φ.invFun 0 = y := by
    rw [← hΦ0']
    exact Φ.left_inv y hyΦ
  have hι0 : ι 0 = 0 := map_zero ι
  refine ⟨U, fun u => Φ.invFun (ι u), hUo, ?_, ?_, ?_, ?_, ?_⟩
  · change ι 0 ∈ Φ.target ∧ Φ.invFun (ι 0) ∈ interior W
    rw [hι0, hy0]
    refine ⟨?_, mem_interior_iff_mem_nhds.2 hW⟩
    rw [← hΦ0']
    exact Φ.mapsTo_toFun hyΦ
  · change Φ.invFun (ι 0) = y
    rw [hι0, hy0]
  · exact Φ.invFun_holomorphic.comp ι.differentiableOn fun u hu => hu.1
  · intro u hu v hv huv
    have h1 := Φ.right_inv _ hu.1
    have h2 := Φ.right_inv _ hv.1
    have : ι u = ι v := by
      rw [← h1, ← h2]
      exact congrArg Φ.toFun huv
    have := congrArg (coordinateProjection n k) this
    simpa [hι, coordinateProjection_coordinateInclusion hk] using this
  · intro u hu
    have hsrc : Φ.invFun (ι u) ∈ Φ.source := Φ.mapsTo_invFun hu.1
    refine ⟨?_, interior_subset hu.2⟩
    have hmem := (hflat (y := Φ.invFun (ι u)) (mem_univ _) hsrc).2
    apply hmem
    change Φ.toFun (Φ.invFun (ι u)) ∈ complexCoordinatePlane n k
    rw [Φ.right_inv _ hu.1]
    exact coordinateInclusion_mem_complexCoordinatePlane u

end Hironaka.FiniteFibrePiece
