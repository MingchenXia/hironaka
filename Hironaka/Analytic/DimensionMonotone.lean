/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.FiniteFibrePiece
import Hironaka.Analytic.GermComponentDimension
import Hironaka.Analytic.GermParametrizationProof
import Hironaka.Analytic.AnalyticDimensionBasics
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Analytic.AnalyticGermDecomposition
import Hironaka.Analytic.GermAlgebraicParametrization
import Hironaka.Analytic.GermNoetherNormalization
import Hironaka.Analytic.GermParametrizationData
import Hironaka.Analytic.GermParametrizationFunctions
import Hironaka.Analytic.GermParametrizationSets
import Hironaka.Analytic.HolomorphicGermRing
import Hironaka.Analytic.LocalStatementAssembly
import Hironaka.Analytic.RegularAtDimChart
import Hironaka.Analytic.RegularPointDimension
set_option autoImplicit false

/-!
# Monotonicity of dimension

Let `T` be an analytic subset of a complex manifold.

* `exists_parametrization`: an irreducible germ carries, after a linear change of coordinates,
  parametrization data and parametrizing sets.
* `exists_isOpen_subset_inter_of_cover`: a nonempty open set covered by finitely many relatively
  closed sets has a nonempty open subset inside one of them.
* `exists_regularAtDim_ge_germ` (germ level): if an injective holomorphic `k`-parameter piece of an
  analytic germ `T` at `0 ∈ ℂⁿ` passes through `0`, every neighbourhood of `0` contains a regular point
  of `T` of dimension `≥ k`.  The germ of `T` is a finite irredundant union of irreducible germs
  `A_i`; the piece has an open part inside one `A_i`, which in Noether coordinates bounds `k` by the
  dimension `d_i` of `A_i` (`FiniteFibrePiece.le_dim_of_injOn`); near `0`, off the other components,
  `A_i` has regular points of dimension `d_i`, and there `T = A_i`.
* `locDimGE_of_regularAtDim_subset` (manifold level): if `B ⊆ T` and `z` is a regular point of `B`
  of dimension `k`, then `dim_z T ≥ k` — read in the chart at `z`.
-/

open Set Filter Topology Metric

noncomputable section

namespace Hironaka.DimensionMonotone

open Hironaka.RegularLocusDense AnalyticGermDecomposition HolGerm GermAlgebraicParametrization GermParametrization GermParametrizationData GermComponentDimension RegularPointDimension RegularAtDimChart AnalyticLocalStatement AnalyticDescendingChain AnalyticDimensionBasics FiniteFibrePiece

variable {n : ℕ}

/-! ### Parametrizations of irreducible germs -/

/-- **An irreducible germ is parametrized after a linear change of coordinates.** -/
theorem exists_parametrization {A : Set (ComplexModel n)} (hA : IsIrreducibleGerm A) :
    ∃ (L : ComplexModel n ≃L[ℂ] ComplexModel n) (P : ParametrizationData (L ⁻¹' A)),
      Nonempty (SetsData P) := by
  have hprime : (vanishingIdeal A).IsPrime := (isIrreducibleGerm_iff_isPrime hA.1).1 hA
  obtain ⟨d, L, hN⟩ := exists_isNoetherNormalization (vanishingIdeal A)
  rw [map_vanishingIdeal_comapEquiv] at hN
  have : (vanishingIdeal (L ⁻¹' A)).IsPrime := by
    rw [← map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨AP⟩ := exists_algebraicParametrization hN
  obtain ⟨PD⟩ := GermParametrizationData.nonempty_parametrizationData
    (isAnalyticGerm_preimage L hA.1) AP
  exact ⟨L, PD, GermParametrizationData.nonempty_setsData PD⟩

/-! ### Finite covers by relatively closed sets -/

/-- **A nonempty open set covered by finitely many relatively closed sets** has a nonempty open
subset contained in one of them. -/
theorem exists_isOpen_subset_inter_of_cover {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    {F : ι → Set X} : ∀ {W : Set X}, IsOpen W → W.Nonempty → W ⊆ ⋃ i ∈ s, F i →
      (∀ i ∈ s, IsOpen (W \ F i)) →
      ∃ i ∈ s, ∃ W' : Set X, IsOpen W' ∧ W'.Nonempty ∧ W' ⊆ W ∩ F i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro W _ hne hcov _
    obtain ⟨x, hx⟩ := hne
    simpa using hcov hx
  | insert a s ha ih =>
    intro W hW hne hcov hF
    by_cases hWa : W ⊆ F a
    · exact ⟨a, Finset.mem_insert_self a s, W, hW, hne,
        fun x hx => ⟨hx, hWa hx⟩⟩
    · obtain ⟨x, hxW, hxa⟩ := not_subset.mp hWa
      have hW' : IsOpen (W \ F a) := hF a (Finset.mem_insert_self a s)
      have hcov' : W \ F a ⊆ ⋃ i ∈ s, F i := by
        intro y hy
        have := hcov hy.1
        simp only [Finset.set_biUnion_insert, mem_union] at this
        rcases this with h | h
        · exact absurd h hy.2
        · exact h
      have hF' : ∀ i ∈ s, IsOpen ((W \ F a) \ F i) := by
        intro i hi
        have heq : (W \ F a) \ F i = (W \ F i) ∩ (W \ F a) := by
          ext y
          simp only [Set.mem_sdiff, mem_inter_iff]
          tauto
        rw [heq]
        exact (hF i (Finset.mem_insert_of_mem hi)).inter hW'
      obtain ⟨i, hi, W'', hW''o, hW''ne, hW''sub⟩ := ih hW' ⟨x, hxW, hxa⟩ hcov' hF'
      exact ⟨i, Finset.mem_insert_of_mem hi, W'', hW''o, hW''ne,
        fun y hy => ⟨(hW''sub hy).1.1, (hW''sub hy).2⟩⟩

/-! ### The germ-level statement -/

/-- **Monotonicity of dimension, germ level.**  If `φ` is holomorphic and injective on an open
`U ⊆ ℂᵏ`, with values in the analytic germ `T` and `φ u₀ = 0`, then every neighbourhood of `0`
contains a regular point of `T` of dimension `≥ k`. -/
theorem exists_regularAtDim_ge_germ {T : Set (ComplexModel n)} (hT : IsAnalyticGerm T) {k : ℕ}
    {U : Set (ComplexModel k)} (hU : IsOpen U) {φ : ComplexModel k → ComplexModel n}
    (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (hφT : MapsTo φ U T)
    {u₀ : ComplexModel k} (hu₀ : u₀ ∈ U) (hφ0 : φ u₀ = 0) {O : Set (ComplexModel n)}
    (hO : O ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ y ∈ O, ∃ d, k ≤ d ∧ RegularAtDim (n := n) (M := ComplexModel n) T y d := by
  classical
  obtain ⟨r, A, hAirr, -, hTA, hpw⟩ := exists_irreducible_decomposition_euclidean hT
  choose L P hS using fun i => exists_parametrization (hAirr i)
  have S : ∀ i, SetsData (P i) := fun i => (hS i).some
  -- relatively closed representatives
  choose ρc hρc hρco using fun i => exists_isOpen_ball_diff (hAirr i).1
  -- the conditions at `0`
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (z ∈ T ↔ z ∈ ⋃ i, A i) ∧
      (∀ i, (L i).symm z ∈ ball (0 : ComplexModel n) (P i).rad) ∧ z ∈ O := by
    refine (Filter.eventuallyEq_set.mp hTA).and ((Filter.eventually_all.2 fun i => ?_).and hO)
    have hc : Tendsto (L i).symm (𝓝 0) (𝓝 0) := tendsto_linearEquiv_nhds_zero (L i).symm
    exact hc.eventually (ball_mem_nhds _ (P i).rad_pos)
  obtain ⟨ρ₀, hρ₀, hρ₀s⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hρev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ≤ ρ₀ ∧ ∀ i, ρ ≤ ρc i := by
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hρ₀)).and
      (Filter.eventually_all.2 fun i => eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (hρc i)))
  obtain ⟨ρ, ⟨hρρ₀, hρc'⟩, hρ⟩ := (hρev.and self_mem_nhdsWithin).exists
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hsub : ∀ z ∈ ball (0 : ComplexModel n) ρ, (z ∈ T ↔ z ∈ ⋃ i, A i) ∧
      (∀ i, (L i).symm z ∈ ball (0 : ComplexModel n) (P i).rad) ∧ z ∈ O :=
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
  obtain ⟨i, -, W, hWo, hWne, hWsub⟩ :=
    exists_isOpen_subset_inter_of_cover Finset.univ hU₁o ⟨u₀, hu₀U₁⟩ hcov hrel
  -- `k ≤ d_i`
  have hk : k ≤ (P i).dim := by
    refine le_dim_of_injOn (P i) hWo hWne (φ := fun u => (L i).symm (φ u)) ?_ ?_ ?_
    · exact (L i).symm.differentiable.comp_differentiableOn (hφ.mono fun u hu => (hWsub hu).1.1)
    · intro u hu v hv huv
      exact hinj (hWsub hu).1.1 (hWsub hv).1.1 ((L i).symm.injective huv)
    · intro u hu
      refine ⟨?_, (hsub _ (hWsub hu).1.2).2.1 i⟩
      change (L i) ((L i).symm (φ u)) ∈ A i
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact (hWsub hu).2
  -- a regular point of `A i` of dimension `d_i` near `0`, off the other components
  obtain ⟨Ωp, hΩpo, hΩp0, hΩp⟩ :=
    exists_pure_nhds_dim (hAirr i) fun ε hε => exists_regularAtDim_near_zero (L i) (S i) hε
  obtain ⟨O', hO'o, hO'sub, hne, hdisj⟩ :=
    exists_isOpen_disjoint_others hAirr hpw i (isOpen_ball.inter hΩpo)
      ⟨mem_ball_self hρ0, hΩp0⟩
  obtain ⟨z, hzO', hzA⟩ := hne
  obtain ⟨y, hyO', hyreg⟩ :=
    mem_closure_iff.mp ((hΩp O' hO'o (hO'sub.trans inter_subset_right)).2 ⟨hzA, hzO'⟩)
      O' hO'o hzO'
  have hcg : T ∩ O' = A i ∩ O' := by
    ext w
    constructor
    · rintro ⟨hw, hwO⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (((hsub w (hO'sub hwO).1).1).1 hw)
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hwO⟩
      · have : w ∈ O' ∩ A j := ⟨hwO, hj⟩
        rw [hdisj j hji] at this
        exact absurd this (notMem_empty w)
    · rintro ⟨hw, hwO⟩
      exact ⟨((hsub w (hO'sub hwO).1).1).2 (mem_iUnion.2 ⟨i, hw⟩), hwO⟩
  have hyT : RegularAtDim (n := n) (M := ComplexModel n) T y (P i).dim :=
    regularAtDim_of_inter_eq hO'o hyO' (by rw [hcg, inter_assoc, inter_self]) hyreg
  exact ⟨y, (hsub y (hO'sub hyO').1).2.2, (P i).dim, hk, hyT⟩

/-! ### Reading regular points in the chart germ -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A regular point `z` of `B` is the regular point `0` of the chart germ of `B` at `z`. -/
theorem regularAtDim_chartGerm_zero {B : Set M} {z : M} {k : ℕ}
    (hz : RegularAtDim (n := n) B z k) :
    RegularAtDim (n := n) (M := ComplexModel n) (chartGerm (n := n) B z) 0 k := by
  set e := (complexChartAt (n := n) z).val with he
  have hzs : z ∈ e.source := mem_complexChartAt_source z
  have h1 : RegularAtDim (n := n) (e.source ∩ e ⁻¹' (e.symm ⁻¹' B)) z k := by
    refine regularAtDim_of_inter_eq e.open_source hzs ?_ hz
    ext u
    constructor
    · rintro ⟨hu, hus⟩
      refine ⟨⟨hus, ?_⟩, hus⟩
      rw [mem_preimage, mem_preimage, e.left_inv hus]
      exact hu
    · rintro ⟨⟨hus, hu⟩, -⟩
      rw [mem_preimage, mem_preimage, e.left_inv hus] at hu
      exact ⟨hu, hus⟩
  have h2 := (regularAtDim_chart_iff (complexChartAt (n := n) z) (e.symm ⁻¹' B) hzs).mp h1
  have hset : chartGerm (n := n) B z
      = {w : ComplexModel n | w - (-(e z)) ∈ e.target ∩ e.symm ⁻¹' B} := by
    ext w
    simp [chartGerm, sub_neg_eq_add, he]
  rw [hset, AnalyticLocalStatement.regularAtDim_translate_iff, zero_sub, neg_neg, inter_comm]
  exact h2

/-- A regular point `y` of the chart germ of `A` at `x` is the regular point
`e.symm (y + e x)` of `A`. -/
theorem regularAtDim_of_chartGerm {A : Set M} {x : M} {y : ComplexModel n} {d : ℕ}
    (hy : RegularAtDim (n := n) (M := ComplexModel n) (chartGerm (n := n) A x) y d) :
    RegularAtDim (n := n) A
      ((complexChartAt (n := n) x).val.symm (y + (complexChartAt (n := n) x).val x)) d := by
  set e := (complexChartAt (n := n) x).val with he
  have hyT : RegularAtDim (n := n) (M := ComplexModel n)
      (e.target ∩ e.symm ⁻¹' A) (y + e x) d := by
    have hset : chartGerm (n := n) A x
        = {w : ComplexModel n | w - (-(e x)) ∈ e.target ∩ e.symm ⁻¹' A} := by
      ext w
      simp [chartGerm, sub_neg_eq_add, he]
    rw [hset] at hy
    have h := (AnalyticLocalStatement.regularAtDim_translate_iff
      (S := e.target ∩ e.symm ⁻¹' A) (-(e x)) y).mp hy
    simpa [sub_neg_eq_add] using h
  have hyt : y + e x ∈ e.target := hyT.2.1.1
  have hwsrc : e.symm (y + e x) ∈ e.source := e.map_target hyt
  have hew : e (e.symm (y + e x)) = y + e x := e.right_inv hyt
  have h1 : RegularAtDim (n := n) (e.source ∩ e ⁻¹' (e.symm ⁻¹' A))
      (e.symm (y + e x)) d := by
    rw [regularAtDim_chart_iff (complexChartAt (n := n) x) (e.symm ⁻¹' A) hwsrc, ← he, hew]
    rw [inter_comm] at hyT
    exact hyT
  refine regularAtDim_of_inter_eq e.open_source hwsrc ?_ h1
  ext u
  constructor
  · rintro ⟨⟨hu1, hu2⟩, hu3⟩
    refine ⟨?_, hu3⟩
    rw [mem_preimage, mem_preimage, e.left_inv hu1] at hu2
    exact hu2
  · rintro ⟨hu1, hu2⟩
    refine ⟨⟨hu2, ?_⟩, hu2⟩
    rw [mem_preimage, mem_preimage, e.left_inv hu2]
    exact hu1

/-! ### Monotonicity on manifolds -/

/-- **Monotonicity of dimension** (`rem:dimension-monotone`): if `B ⊆ T`, `T` analytic, and `z` is
a regular point of `B` of dimension `k`, then every neighbourhood of `z` contains a regular point of
`T` of dimension `≥ k`. -/
theorem locDimGE_of_regularAtDim_subset {T B : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    (hBT : B ⊆ T) {z : M} {k : ℕ} (hz : RegularAtDim (n := n) B z k) :
    LocDimGE (n := n) T z k := by
  intro N hN
  set e := (complexChartAt (n := n) z).val with he
  have hzs : z ∈ e.source := mem_complexChartAt_source z
  obtain ⟨U, φ, hUo, hU0, hφ0, hφd, hφi, hφB⟩ :=
    exists_param_of_regularAtDim (regularAtDim_chartGerm_zero hz) (univ_mem (f := 𝓝 0))
  have hφT : MapsTo φ U (chartGerm (n := n) T z) := fun u hu =>
    chartGerm_mono (n := n) hBT z (hφB hu).1
  have hcont : ContinuousAt (fun y : ComplexModel n => e.symm (y + e z)) 0 := by
    have h1 : ContinuousAt e.symm (e z) := e.continuousAt_symm (e.map_source hzs)
    have h2 : ContinuousAt (fun y : ComplexModel n => y + e z) 0 :=
      (continuous_id.add continuous_const).continuousAt
    have h3 : (fun y : ComplexModel n => y + e z) 0 = e z := by simp
    exact ContinuousAt.comp (g := e.symm) (by rw [zero_add]; exact h1) h2
  have hO : (fun y : ComplexModel n => e.symm (y + e z)) ⁻¹' N ∈ 𝓝 (0 : ComplexModel n) := by
    refine hcont.preimage_mem_nhds ?_
    simpa [e.left_inv hzs] using hN
  obtain ⟨y, hyO, d, hkd, hy⟩ :=
    exists_regularAtDim_ge_germ (isAnalyticGerm_chartGerm hT z) hUo hφd hφi hφT hU0 hφ0 hO
  exact ⟨_, hyO, d, hkd, regularAtDim_of_chartGerm hy⟩

/-- `dim T ≤ a` and `B ⊆ T` give `dim B ≤ a`. -/
theorem DimLE.anti {T B : Set M} (hT : IsComplexAnalyticSubset (n := n) T) (hBT : B ⊆ T)
    {a : ℕ} (h : DimLE (n := n) T a) : DimLE (n := n) B a := by
  intro y j hy
  obtain ⟨y', -, j', hjj', hy'⟩ := locDimGE_of_regularAtDim_subset hT hBT hy univ univ_mem
  exact hjj'.trans (h y' j' hy')

end Hironaka.DimensionMonotone
