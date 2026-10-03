/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.DimensionMonotone
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Analytic.AnalyticDimensionBasics
import Hironaka.Analytic.AnalyticGermDecomposition
import Hironaka.Analytic.FiniteFibrePiece
import Hironaka.Analytic.GermComponentDimension
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.GermParametrizationDense
import Hironaka.Analytic.GermParametrizationProof
import Hironaka.Analytic.IrreducibleGermLocal
import Hironaka.Analytic.RegularPointDimension
set_option autoImplicit false

/-!
# Thin analytic subsets have smaller dimension

Let `T` be analytic in a complex manifold with `dim T ≤ a`, and `T' ⊆ T` with empty interior relative to `T`. Then
every regular point of `T'` has dimension `< a`.

* `exists_isOpen_avoid`: inside an open set `W₀`, finitely many sets `F_j` each of which is avoided
  by `G` in every open subset meeting `G` can be avoided all at once by an open subset meeting `G`.
* `exists_isOpen_subset_image_germ` (germ level): if every regular point of the analytic germ `T` has
  dimension `≤ a` and an injective holomorphic `a`-parameter piece `φ` of `T` passes through `0`, then
  `φ` fills `T` on a nonempty open set.  (The piece has an open part inside one component `A_i` of
  the germ, of dimension `d_i`; `a ≤ d_i` by `FiniteFibrePiece.le_dim_of_injOn`, `d_i ≤ a` because
  `A_i` has regular points of dimension `d_i` where `T = A_i`; with `d_i = a` the piece fills a
  relatively open subset of `A_i` (`FiniteFibrePiece.exists_isOpen_subset_image`), and off the other
  components `T = A_i` there.)
* `lt_of_regularAtDim_of_thin` (manifold level, `rem:thin-dimension-drop`).
-/

open Set Filter Topology Metric

noncomputable section

namespace Hironaka.ThinDimensionDrop

open Hironaka.RegularLocusDense AnalyticGermDecomposition GermParametrization GermParametrizationData GermComponentDimension RegularPointDimension RegularAtDimChart AnalyticDescendingChain AnalyticDimensionBasics FiniteFibrePiece DimensionMonotone

variable {n : ℕ}

/-! ### Avoiding finitely many thin sets -/

/-- **Avoiding finitely many sets at once.**  If `G` meets every open `U ⊆ W₀` that it meets outside
each `F j` (`j ∈ s`), and each `W₀ \ F j` is open, then every open `O ⊆ W₀` meeting `G` contains an
open set meeting `G` and missing every `F j`. -/
theorem exists_isOpen_avoid {X ι : Type*} [TopologicalSpace X] (s : Finset ι) {F : ι → Set X}
    {G W₀ : Set X}
    (hthin : ∀ j ∈ s, ∀ U : Set X, IsOpen U → U ⊆ W₀ → (U ∩ G).Nonempty → ∃ y ∈ U ∩ G, y ∉ F j)
    (hopen : ∀ j ∈ s, IsOpen (W₀ \ F j)) :
    ∀ {O : Set X}, IsOpen O → O ⊆ W₀ → (O ∩ G).Nonempty →
      ∃ O' : Set X, IsOpen O' ∧ O' ⊆ O ∧ (O' ∩ G).Nonempty ∧ ∀ j ∈ s, O' ∩ F j = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro O hO _ hne
    exact ⟨O, hO, subset_rfl, hne, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | insert a s ha ih =>
    intro O hO hOW hne
    obtain ⟨O₁, hO₁o, hO₁O, hO₁ne, hO₁s⟩ :=
      ih (fun j hj => hthin j (Finset.mem_insert_of_mem hj))
        (fun j hj => hopen j (Finset.mem_insert_of_mem hj)) hO hOW hne
    obtain ⟨y, ⟨hyO₁, hyG⟩, hya⟩ :=
      hthin a (Finset.mem_insert_self a s) O₁ hO₁o (hO₁O.trans hOW) hO₁ne
    refine ⟨O₁ ∩ (W₀ \ F a), hO₁o.inter (hopen a (Finset.mem_insert_self a s)),
      inter_subset_left.trans hO₁O, ⟨y, ⟨hyO₁, hOW (hO₁O hyO₁), hya⟩, hyG⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact eq_empty_iff_forall_notMem.mpr fun w hw => hw.1.2.2 hw.2
    · exact subset_empty_iff.mp ((inter_subset_inter_left _ inter_subset_left).trans
        (hO₁s j hj).subset)

/-- `exists_isOpen_subset_image` with the dimension given up to an equality. -/
theorem exists_isOpen_subset_image_of_eq {A : Set (ComplexModel n)} (P : ParametrizationData A)
    (S : SetsData P) {k : ℕ} (hk : k = P.dim) {U : Set (ComplexModel k)} (hU : IsOpen U)
    (hUne : U.Nonempty) {φ : ComplexModel k → ComplexModel n} (hφ : DifferentiableOn ℂ φ U)
    (hinj : InjOn φ U) (hφA : MapsTo φ U (A ∩ polydisc n P.dim S.r₁ S.r₂)) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ (V ∩ (A ∩ polydisc n P.dim S.r₁ S.r₂)).Nonempty ∧
      V ∩ (A ∩ polydisc n P.dim S.r₁ S.r₂) ⊆ φ '' U := by
  subst hk
  exact exists_isOpen_subset_image P S hU hUne hφ hinj hφA

/-! ### The germ-level statement -/

/-- **A top-dimensional piece fills an open set, germ level.**  If every regular point of the
analytic germ `T` has dimension `≤ a`, and `φ` is holomorphic and injective on an open `U ⊆ ℂᵃ`
with values in `T` and `φ u₀ = 0`, then inside every neighbourhood of `0` there is an open set `W`
meeting `T` with `W ∩ T ⊆ φ(U)`. -/
theorem exists_isOpen_subset_image_germ {T : Set (ComplexModel n)} (hT : IsAnalyticGerm T) {a : ℕ}
    (hdim : ∀ y j, RegularAtDim (n := n) (M := ComplexModel n) T y j → j ≤ a)
    {U : Set (ComplexModel a)} (hU : IsOpen U) {φ : ComplexModel a → ComplexModel n}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (hφT : MapsTo φ U T)
    {u₀ : ComplexModel a} (hu₀ : u₀ ∈ U) (hφ0 : φ u₀ = 0) {O : Set (ComplexModel n)}
    (hO : O ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ W ⊆ O ∧ (W ∩ T).Nonempty ∧ W ∩ T ⊆ φ '' U := by
  classical
  obtain ⟨r, A, hAirr, -, hTA, hpw⟩ := exists_irreducible_decomposition_euclidean hT
  choose L P hS using fun i => exists_parametrization (hAirr i)
  have S : ∀ i, SetsData (P i) := fun i => (hS i).some
  choose ρc hρc hρco using fun i => exists_isOpen_ball_diff (hAirr i).1
  -- thinness of the other components inside `A i`
  have hthin0 : ∀ i j, j ≠ i → ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      ∀ U' : Set (ComplexModel n), IsOpen U' → (U' ∩ (A i ∩ Ω)).Nonempty →
        ∃ y ∈ U' ∩ (A i ∩ Ω), y ∉ A j := fun i j hji =>
    IrreducibleGermLocal.exists_thin_nhds (hAirr i) (hAirr j).1 (hpw (Ne.symm hji))
  have hthin1 : ∀ i j, ∃ Ω : Set (ComplexModel n), IsOpen Ω ∧ (0 : ComplexModel n) ∈ Ω ∧
      (j ≠ i → ∀ U' : Set (ComplexModel n), IsOpen U' → (U' ∩ (A i ∩ Ω)).Nonempty →
        ∃ y ∈ U' ∩ (A i ∩ Ω), y ∉ A j) := fun i j => by
    by_cases hji : j = i
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd hji h⟩
    · obtain ⟨Ω, hΩo, hΩ0, hΩ⟩ := hthin0 i j hji
      exact ⟨Ω, hΩo, hΩ0, fun _ => hΩ⟩
  choose Ωt hΩto hΩt0 hΩt using hthin1
  -- the conditions at `0`
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (z ∈ T ↔ z ∈ ⋃ i, A i) ∧
      (∀ i, (L i).symm z ∈ polydisc n (P i).dim (S i).r₁ (S i).r₂) ∧
      (∀ i j, z ∈ Ωt i j) ∧ z ∈ O := by
    refine (Filter.eventuallyEq_set.mp hTA).and ((Filter.eventually_all.2 fun i => ?_).and
      ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        (hΩto i j).mem_nhds (hΩt0 i j)).and hO))
    have hc : Tendsto (L i).symm (𝓝 0) (𝓝 0) := tendsto_linearEquiv_nhds_zero (L i).symm
    exact hc.eventually ((isOpen_polydisc _ _ _ _).mem_nhds
      (zero_mem_polydisc (S i).r₁_pos (S i).r₂_pos))
  obtain ⟨ρ₀, hρ₀, hρ₀s⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hρev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ≤ ρ₀ ∧ ∀ i, ρ ≤ ρc i := by
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hρ₀)).and
      (Filter.eventually_all.2 fun i => eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (hρc i)))
  obtain ⟨ρ, ⟨hρρ₀, hρc'⟩, hρ⟩ := (hρev.and self_mem_nhdsWithin).exists
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hsub : ∀ z ∈ ball (0 : ComplexModel n) ρ, (z ∈ T ↔ z ∈ ⋃ i, A i) ∧
      (∀ i, (L i).symm z ∈ polydisc n (P i).dim (S i).r₁ (S i).r₂) ∧
      (∀ i j, z ∈ Ωt i j) ∧ z ∈ O :=
    fun z hz => hρ₀s z (ball_subset_ball hρρ₀ hz)
  have hopen : ∀ i, IsOpen (ball (0 : ComplexModel n) ρ \ A i) := fun i => by
    have heq : ball (0 : ComplexModel n) ρ \ A i =
        ball (0 : ComplexModel n) ρ ∩ (ball 0 (ρc i) \ A i) := by
      ext z
      constructor
      · rintro ⟨hz, hzA⟩
        exact ⟨hz, ball_subset_ball (hρc' i) hz, hzA⟩
      · rintro ⟨hz, -, hzA⟩
        exact ⟨hz, hzA⟩
    rw [heq]
    exact isOpen_ball.inter (hρco i)
  -- `T ∩ O'' = A i ∩ O''` on an open set missing the other components
  have hTeq : ∀ i {O'' : Set (ComplexModel n)}, O'' ⊆ ball 0 ρ →
      (∀ j ∈ Finset.univ.erase i, O'' ∩ A j = ∅) → T ∩ O'' = A i ∩ O'' := by
    intro i O'' hO''ρ hdisj
    ext w
    constructor
    · rintro ⟨hw, hwO⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (((hsub w (hO''ρ hwO)).1).1 hw)
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hwO⟩
      · have : w ∈ O'' ∩ A j := ⟨hwO, hj⟩
        rw [hdisj j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)] at this
        exact absurd this (notMem_empty w)
    · rintro ⟨hw, hwO⟩
      exact ⟨((hsub w (hO''ρ hwO)).1).2 (mem_iUnion.2 ⟨i, hw⟩), hwO⟩
  have havoid : ∀ i {O₀ : Set (ComplexModel n)}, IsOpen O₀ → O₀ ⊆ ball 0 ρ →
      (O₀ ∩ A i).Nonempty → ∃ O'' : Set (ComplexModel n), IsOpen O'' ∧ O'' ⊆ O₀ ∧
        (O'' ∩ A i).Nonempty ∧ ∀ j ∈ Finset.univ.erase i, O'' ∩ A j = ∅ := by
    intro i O₀ hO₀ hO₀ρ hne
    refine exists_isOpen_avoid (Finset.univ.erase i) (W₀ := ball 0 ρ) ?_
      (fun j _ => hopen j) hO₀ hO₀ρ hne
    intro j hj U' hU' hU'ρ hU'ne
    obtain ⟨w, hwU, hwA⟩ := hU'ne
    obtain ⟨y, ⟨hyU, hyA, -⟩, hyj⟩ := hΩt i j (Finset.mem_erase.mp hj).1 U' hU'
      ⟨w, hwU, hwA, (hsub w (hU'ρ hwU)).2.2.1 i j⟩
    exact ⟨y, ⟨hyU, hyA⟩, hyj⟩
  -- the piece near `u₀`
  set U₁ := U ∩ φ ⁻¹' ball (0 : ComplexModel n) ρ with hU₁
  have hU₁o : IsOpen U₁ := hφ.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hu₀U₁ : u₀ ∈ U₁ := ⟨hu₀, by rw [mem_preimage, hφ0]; exact mem_ball_self hρ0⟩
  have hcov : U₁ ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin r)), φ ⁻¹' A i := by
    intro u hu
    have := ((hsub _ hu.2).1).1 (hφT hu.1)
    obtain ⟨i, hi⟩ := mem_iUnion.mp this
    exact mem_biUnion (Finset.mem_univ i) hi
  have hrel : ∀ i ∈ (Finset.univ : Finset (Fin r)), IsOpen (U₁ \ φ ⁻¹' A i) := by
    intro i _
    have heq : U₁ \ φ ⁻¹' A i = U ∩ φ ⁻¹' (ball (0 : ComplexModel n) ρ \ A i) := by
      ext u
      simp only [hU₁, Set.mem_sdiff, mem_inter_iff, mem_preimage]
      tauto
    rw [heq]
    exact hφ.continuousOn.isOpen_inter_preimage hU (hopen i)
  obtain ⟨i, -, W', hW'o, hW'ne, hW'sub⟩ :=
    exists_isOpen_subset_inter_of_cover Finset.univ hU₁o ⟨u₀, hu₀U₁⟩ hcov hrel
  set ψ : ComplexModel a → ComplexModel n := fun u => (L i).symm (φ u) with hψ
  have hψd : DifferentiableOn ℂ ψ W' :=
    (L i).symm.differentiable.comp_differentiableOn (hφ.mono fun u hu => (hW'sub hu).1.1)
  have hψi : InjOn ψ W' := fun u hu v hv huv =>
    hinj (hW'sub hu).1.1 (hW'sub hv).1.1 ((L i).symm.injective huv)
  have hψA : MapsTo ψ W' ((L i) ⁻¹' A i ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂) := by
    intro u hu
    refine ⟨?_, (hsub _ (hW'sub hu).1.2).2.1 i⟩
    change (L i) ((L i).symm (φ u)) ∈ A i
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (hW'sub hu).2
  -- `a ≤ d_i`
  have hk : a ≤ (P i).dim :=
    le_dim_of_injOn (P i) hW'o hW'ne hψd hψi fun u hu =>
      ⟨(hψA hu).1, (S i).polydisc_subset (hψA hu).2⟩
  -- `d_i ≤ a`
  have hk' : (P i).dim ≤ a := by
    obtain ⟨Ωp, hΩpo, hΩp0, hΩp⟩ :=
      exists_pure_nhds_dim (hAirr i) fun ε hε => exists_regularAtDim_near_zero (L i) (S i) hε
    obtain ⟨O', hO'o, hO'sub, hne, hdisj⟩ :=
      exists_isOpen_disjoint_others hAirr hpw i (isOpen_ball.inter hΩpo)
        ⟨mem_ball_self hρ0, hΩp0⟩
    obtain ⟨z, hzO', hzA⟩ := hne
    obtain ⟨y, hyO', hyreg⟩ :=
      mem_closure_iff.mp ((hΩp O' hO'o (hO'sub.trans inter_subset_right)).2 ⟨hzA, hzO'⟩)
        O' hO'o hzO'
    have hcg : T ∩ O' = A i ∩ O' := hTeq i (fun w hw => (hO'sub hw).1)
      (fun j hj => hdisj j (Finset.mem_erase.mp hj).1)
    exact hdim y _ (regularAtDim_of_inter_eq hO'o hyO' (by rw [hcg, inter_assoc, inter_self])
      hyreg)
  -- the piece fills a relatively open subset of `A i`
  obtain ⟨V, hVo, ⟨y, hyV, hyA⟩, hVsub⟩ :=
    exists_isOpen_subset_image_of_eq (P i) (S i) (le_antisymm hk hk') hW'o hW'ne hψd hψi hψA
  obtain ⟨w₀, hw₀, hw₀y⟩ := hVsub ⟨hyV, hyA⟩
  set V'' : Set (ComplexModel n) :=
    (L i).symm ⁻¹' (V ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂) ∩ ball 0 ρ with hV''
  have hV''o : IsOpen V'' :=
    ((hVo.inter (isOpen_polydisc _ _ _ _)).preimage (L i).symm.continuous).inter isOpen_ball
  have hφw₀ : φ w₀ = (L i) y := by
    rw [← hw₀y]
    simp [hψ]
  have hV''ne : (V'' ∩ A i).Nonempty := by
    refine ⟨(L i) y, ⟨⟨?_, ?_⟩, ?_⟩, hyA.1⟩
    · simpa using hyV
    · simpa using hyA.2
    · rw [← hφw₀]; exact (hW'sub hw₀).1.2
  obtain ⟨O'', hO''o, hO''sub, hO''ne, hO''dis⟩ :=
    havoid i hV''o inter_subset_right hV''ne
  refine ⟨O'', hO''o, fun z hz => (hsub z (hO''sub hz).2).2.2.2, ?_, ?_⟩
  · obtain ⟨z, hzO, hzA⟩ := hO''ne
    refine ⟨z, hzO, ?_⟩
    have hTi := hTeq i (hO''sub.trans inter_subset_right) hO''dis
    have h : z ∈ A i ∩ O'' := ⟨hzA, hzO⟩
    rw [← hTi] at h
    exact h.1
  · rintro z ⟨hzO, hzT⟩
    have hTi := hTeq i (hO''sub.trans inter_subset_right) hO''dis
    have hzA : z ∈ A i := by
      have h : z ∈ T ∩ O'' := ⟨hzT, hzO⟩
      rw [hTi] at h
      exact h.1
    have hz'' := hO''sub hzO
    have hmem : (L i).symm z ∈ V ∩ ((L i) ⁻¹' A i ∩ polydisc n (P i).dim (S i).r₁ (S i).r₂) := by
      refine ⟨hz''.1.1, ?_, hz''.1.2⟩
      change (L i) ((L i).symm z) ∈ A i
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hzA
    obtain ⟨w, hw, hwz⟩ := hVsub hmem
    refine ⟨w, (hW'sub hw).1.1, ?_⟩
    have := congrArg (L i) hwz
    simpa [hψ] using this

/-! ### Thin analytic subsets on manifolds -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Thin analytic subsets have smaller dimension** (`rem:thin-dimension-drop`): if `T` is
analytic with `dim T ≤ a` and `T' ⊆ T` has empty interior relative to `T`, then every regular point
of `T'` has dimension `< a`. -/
theorem lt_of_regularAtDim_of_thin {T T' : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    (hT'T : T' ⊆ T) (hthin : ∀ O : Set M, IsOpen O → O ∩ T ⊆ T' → O ∩ T = ∅) {a : ℕ}
    (hdim : DimLE (n := n) T a) {y : M} {k : ℕ} (hy : RegularAtDim (n := n) T' y k) : k < a := by
  have hka : k ≤ a := DimLE.anti hT hT'T hdim y k hy
  rcases hka.lt_or_eq with h | rfl
  · exact h
  exfalso
  set e := (complexChartAt (n := n) y).val with he
  have hys : y ∈ e.source := mem_complexChartAt_source y
  obtain ⟨U, φ, hUo, hU0, hφ0, hφd, hφi, hφB⟩ :=
    exists_param_of_regularAtDim (regularAtDim_chartGerm_zero hy) (univ_mem (f := 𝓝 0))
  have hφT : MapsTo φ U (chartGerm (n := n) T y) := fun u hu =>
    chartGerm_mono (n := n) hT'T y (hφB hu).1
  have hdim' : ∀ w j, RegularAtDim (n := n) (M := ComplexModel n) (chartGerm (n := n) T y) w j →
      j ≤ k := fun w j hw => hdim _ j (regularAtDim_of_chartGerm hw)
  obtain ⟨W, hWo, -, ⟨w, hwW, hwT⟩, hWsub⟩ :=
    exists_isOpen_subset_image_germ (isAnalyticGerm_chartGerm hT y) hdim' hUo hφd hφi hφT hU0 hφ0
      (univ_mem (f := 𝓝 0))
  set OM : Set M := e.source ∩ (fun p => e p - e y) ⁻¹' W with hOM
  have hOMo : IsOpen OM := by
    have hc : ContinuousOn (fun p => e p - e y) e.source := e.continuousOn.sub continuousOn_const
    exact hc.isOpen_inter_preimage e.open_source hWo
  -- `OM ∩ T ⊆ T'`
  have hsubT' : OM ∩ T ⊆ T' := by
    rintro p ⟨⟨hps, hpW⟩, hpT⟩
    have hpg : e p - e y ∈ chartGerm (n := n) T y := by
      change e p - e y + e y ∈ e.target ∩ e.symm ⁻¹' T
      rw [sub_add_cancel]
      exact ⟨e.map_source hps, by rw [mem_preimage, e.left_inv hps]; exact hpT⟩
    obtain ⟨u, hu, hue⟩ := hWsub ⟨hpW, hpg⟩
    have hT'g := (hφB hu).1
    rw [hue] at hT'g
    change e p - e y + e y ∈ e.target ∩ e.symm ⁻¹' T' at hT'g
    rw [sub_add_cancel] at hT'g
    have := hT'g.2
    rwa [mem_preimage, e.left_inv hps] at this
  have hempty := hthin OM hOMo hsubT'
  -- but `OM ∩ T` is nonempty
  have hwT' : w + e y ∈ e.target ∩ e.symm ⁻¹' T := hwT
  have hpm : e.symm (w + e y) ∈ OM ∩ T := by
    refine ⟨⟨e.map_target hwT'.1, ?_⟩, hwT'.2⟩
    change e (e.symm (w + e y)) - e y ∈ W
    rw [e.right_inv hwT'.1, add_sub_cancel_right]
    exact hwW
  rw [hempty] at hpm
  exact hpm

end Hironaka.ThinDimensionDrop
