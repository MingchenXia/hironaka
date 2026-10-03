/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.LocalHolomorphicInverse
import Hironaka.Blowup.BlowupFibreDirection
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupLocalSurjectivity
import Hironaka.Blowup.BlowupMonomialCharts
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Blowup.NestedFlattening
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.RegularPatchPullback
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Strict transforms of simple normal crossings divisors

Sources: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Definitions 2.2 and the remark after them
("`E'` is a normal crossings divisor transverse to `N'`, because `σ` is admissible"); Wlodarczyk 2005
(`wlodarczyk05-hironaka`), §2.1.

Let `π : Y → X` be the blowup along `C`, `N ⊇ C`, and `E = [H₁, …, H_s]` an ordered simple normal
crossings divisor.  The transformed divisor of a marked ideal is

  `E' = [H₁', …, H_s', π⁻¹ C]`,  `H' = closure (π⁻¹ (H \ C))`

(`MarkedIdeals.MarkedIdeal.geoTransform`, uses exactly this list).

* `mem_geoStrictTransform_iff_of_chart` -- **in a monomial chart `j` built on coordinates `Φ` with
  `C = ℂ^k × 0`, the strict transform of a coordinate subspace `L_T = {w_t = 0, t ∈ T}` is
  `{W ∈ L_T}` if `j ∉ T`, and misses the chart if `j ∈ T`** (no relation between `C` and `L_T`
  is needed);
* `isCoordinateFamilyAt_of_preimage` -- adapted coordinates pull back along a local
  biholomorphism;
* `IsAdaptedAt C N E x` -- coordinates at `x` in which `C ⊆ N` are the nested planes
  `ℂ^{k_C} × 0 ⊆ ℂ^{k_N} × 0` and each member of `E` through `x` is a coordinate hyperplane
  `{w_{s i} = 0}`, `s i < k_N` (transverse to `N`), the `s i` distinct;
* `isSNCDivisor_geoTransformE` -- if `E` is SNC and `C` admits adapted coordinates at each of its
  points, then `E'` is SNC;
* `isTransverse_geoTransformE` -- if moreover `E` is transverse to `N`, then `E'` is transverse
  to `N' = closure (π⁻¹ (N \ C))`.

The hypothesis `IsAdaptedAt` is the simultaneous normal crossings of `N`, `C` and `E` at the points
of the centre (Bierstone--Milman's "`C`, `E` have only normal crossings", read together with
`C ⊆ N` and `E` transverse to `N`); it is a hypothesis here, not an interface.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSNCTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection BlowupStrictSubmanifold BlowupStrictIdeal NormalCrossings RegularAtDimTransport Hironaka.RegularPatchPullback

noncomputable section

variable {n : ℕ}

/-! ### Lists and coordinate subspaces -/

section Basic

theorem length_map_append_singleton {α β : Type*} (E : List α) (f : α → β) (P : β) :
    (E.map f ++ [P]).length = E.length + 1 := by simp

theorem get_map_append_singleton {α β : Type*} (E : List α) (f : α → β) (P : β)
    (i : Fin (E.map f ++ [P]).length) :
    (E.map f ++ [P]).get i = if h : i.1 < E.length then f (E.get ⟨i.1, h⟩) else P := by
  rcases i with ⟨i, hi⟩
  simp only [List.get_eq_getElem]
  split_ifs with h
  · rw [List.getElem_append_left (by simpa using h)]
    simp
  · have : i = E.length := by simp at hi; omega
    subst this
    rw [List.getElem_append_right (by simp)]
    simp

theorem eq_of_not_lt {α β : Type*} {E : List α} {f : α → β} {P : β}
    {i i' : Fin (E.map f ++ [P]).length} (hi : ¬ i.1 < E.length) (hi' : ¬ i'.1 < E.length) :
    i = i' := by
  have h1 := i.2
  have h2 := i'.2
  simp only [List.length_append, List.length_map, List.length_singleton] at h1 h2
  exact Fin.ext (by omega)

theorem isClosed_coordSubspace (T : Finset (Fin n)) : IsClosed (coordSubspace (n := n) T) := by
  have : coordSubspace (n := n) T = ⋂ t ∈ T, {w : ComplexModel n | w t = 0} := by
    ext w; simp [coordSubspace]
  rw [this]
  exact isClosed_biInter fun t _ =>
    isClosed_eq (continuous_apply t |>.comp (PiLp.continuous_ofLp 2 _)) continuous_const

theorem mem_coordSubspace_singleton {s : Fin n} {w : ComplexModel n} :
    w ∈ coordSubspace {s} ↔ w s = 0 := by
  simp [coordSubspace]

theorem sub_mem_coordSubspace_iff {T : Finset (Fin n)} {w c : ComplexModel n}
    (hc : c ∈ coordSubspace T) : w - c ∈ coordSubspace T ↔ w ∈ coordSubspace T := by
  constructor
  · intro h t ht
    have := h t ht
    rw [PiLp.sub_apply, hc t ht, sub_zero] at this
    exact this
  · intro h t ht
    rw [PiLp.sub_apply, h t ht, hc t ht, sub_zero]

/-- `σ_j` maps every coordinate subspace `L_T` into itself. -/
theorem monomial_mem_coordSubspace {k : ℕ} {j : Fin n} {T : Finset (Fin n)} {w : ComplexModel n}
    (hw : w ∈ coordSubspace T) : monomial k j w ∈ coordSubspace T := by
  intro t ht
  rw [monomial_apply]
  split_ifs <;> simp [hw t ht]

/-- Off `w_j = 0`: `σ_j(w) ∈ L_T ⟺ j ∉ T ∧ w ∈ L_T`. -/
theorem monomial_mem_coordSubspace_iff {k : ℕ} {j : Fin n} {T : Finset (Fin n)}
    {w : ComplexModel n} (hwj : w j ≠ 0) :
    monomial k j w ∈ coordSubspace T ↔ j ∉ T ∧ w ∈ coordSubspace T := by
  refine ⟨fun h => ?_, fun h => monomial_mem_coordSubspace h.2⟩
  have hjT : j ∉ T := fun hjT => hwj (by simpa [monomial_apply] using h j hjT)
  refine ⟨hjT, fun t ht => ?_⟩
  have := h t ht
  rw [monomial_apply] at this
  split_ifs at this with hc
  · exact (mul_eq_zero.mp this).resolve_right hwj
  · exact this

end Basic

/-! ### The strict transform of a coordinate subspace in a monomial chart -/

section Chart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}
  {y₀ : X} {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y₀ y₀)} {k : ℕ}

/-- **The strict transform of a coordinate subspace in a monomial chart.**  Let `Φ` flatten `C`
onto `ℂ^k × 0` and a set `A` onto the coordinate subspace `L_T`; let `W` be the local inverse of
the monomial chart `j ≥ k` on `O`.  For `u ∈ O`: `u ∈ closure (π⁻¹(A \ C)) ⟺ j ∉ T ∧ W u ∈ L_T`. -/
theorem mem_geoStrictTransform_iff_of_chart (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) y₀).target)
    (hflatC : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ complexCoordinatePlane n k))
    {A : Set X} {T : Finset (Fin n)}
    (hflatA : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) y₀).source →
      chartAt (ComplexModel n) y₀ y ∈ Φ.source →
        (y ∈ A ↔ Φ.toFun (chartAt (ComplexModel n) y₀ y) ∈ coordSubspace T))
    {j : Fin n} (hj : k ≤ j.1) {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWeq : ∀ z' ∈ O, π z' ∈ flatDomain Φ ∧
      monomial k j (W z') = Φ.toFun (chartAt (ComplexModel n) y₀ (π z')))
    (hℓ : ∀ ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ →
        π ∘ ℓ = monomialChart Φ k j → ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ k j,
          ℓ (LiftedOpen.mk _ (W z') hw) = z')
    {u : Y} (hu : u ∈ O) :
    u ∈ geoStrictTransform π C A ↔ j ∉ T ∧ W u ∈ coordSubspace T := by
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j := fun z' hz' => by
    show monomial k j (W z') ∈ Φ.target
    rw [(hWeq z' hz').2]; exact Φ.mapsTo_toFun (hWeq z' hz').1.2
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hAu : ∀ u ∈ O, (π u ∈ A ↔ monomial k j (W u) ∈ coordSubspace T) := fun u hu => by
    rw [hflatA (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2]
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦsrc hflatC hj
  -- points of `π⁻¹(A \ C) ∩ O`
  have key : ∀ u' ∈ O, u' ∈ π ⁻¹' (A \ C) → j ∉ T ∧ W u' ∈ coordSubspace T :=
    fun u' hu'O hu'A => (monomial_mem_coordSubspace_iff
      (fun h0 => hu'A.2 ((hCu u' hu'O).mpr h0))).mp ((hAu u' hu'O).mp hu'A.1)
  constructor
  · intro hcl
    by_cases hjT : j ∈ T
    · exfalso
      obtain ⟨u', hu'O, hu'A⟩ := mem_closure_iff_nhds.mp hcl O (hO.mem_nhds hu)
      exact (key u' hu'O hu'A).1 hjT
    · refine ⟨hjT, ?_⟩
      by_contra hWu
      have hev : ∀ᶠ u' in 𝓝 u, u' ∈ O ∧ W u' ∉ coordSubspace T :=
        (hO.eventually_mem hu).and ((hWs u hu).continuousAt.eventually_mem
          ((isClosed_coordSubspace T).isOpen_compl.mem_nhds hWu))
      obtain ⟨u', hu'mem, hu'A⟩ := mem_closure_iff_nhds.mp hcl _ hev
      exact hu'mem.2 (key u' hu'mem.1 hu'A).2
  · rintro ⟨hjT, hWu⟩
    by_cases hWj : W u j = 0
    · rw [geoStrictTransform, mem_closure_iff_nhds]
      intro U hU
      have hp : W u ∈ monomialDomain Φ k j := hWmem u hu
      set p : LiftedOpen.{u} (monomialDomain Φ k j) := LiftedOpen.mk _ (W u) hp with hpdef
      have hℓp : ℓ p = u := hℓ ℓ hℓs hℓπ u hu hp
      have hpre : ℓ ⁻¹' U ∈ 𝓝 p := hℓs.continuous.continuousAt.preimage_mem_nhds (by
        rw [hℓp]; exact hU)
      have himg : LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∈ 𝓝 (W u) := by
        have := (LiftedOpen.isOpenEmbedding_toModel (S := monomialDomain Φ k j)).map_nhds_eq p
        rw [← LiftedOpen.toModel_mk (S := monomialDomain Φ k j) (W u) hp, ← this]
        exact image_mem_map hpre
      set e_j : ComplexModel n := EuclideanSpace.single j 1 with he_j
      have hcurve : Tendsto (fun t : ℂ => W u + t • e_j) (𝓝 0) (𝓝 (W u)) := by
        have : Continuous (fun t : ℂ => W u + t • e_j) := continuous_const.add
          (continuous_id.smul continuous_const)
        simpa using this.tendsto 0
      have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) ∧
          t ≠ 0 :=
        (show ∀ᶠ t in 𝓝[≠] (0 : ℂ), W u + t • e_j ∈ LiftedOpen.toModel _ '' (ℓ ⁻¹' U) from
          mem_nhdsWithin_of_mem_nhds (hcurve himg)).and self_mem_nhdsWithin
      obtain ⟨t, ⟨q, hqU, hqt⟩, ht0⟩ := hev.exists
      refine ⟨ℓ q, hqU, ?_⟩
      have hπq : π (ℓ q) = monomialChart Φ k j q := congrFun hℓπ q
      have hqmem : LiftedOpen.toModel _ q ∈ monomialDomain Φ k j := LiftedOpen.toModel_mem _ q
      have hmon : monomial k j (LiftedOpen.toModel _ q) ∈ Φ.target := hqmem
      have hsrc : π (ℓ q) ∈ flatDomain Φ := by
        rw [hπq]; exact monomialChart_mem_flatDomain hΦsrc q
      have hcoord : Φ.toFun (chartAt (ComplexModel n) y₀ (π (ℓ q))) =
          monomial k j (LiftedOpen.toModel _ q) := by
        rw [hπq, monomialChart, (chartAt (ComplexModel n) y₀).right_inv (hΦsrc
          (Φ.mapsTo_invFun hmon)), Φ.right_inv _ hmon]
      have hwq : LiftedOpen.toModel _ q = W u + t • e_j := hqt
      have hwqj : LiftedOpen.toModel _ q j = t := by
        rw [hwq]; simp [he_j, hWj]
      have hwqT : LiftedOpen.toModel _ q ∈ coordSubspace T := by
        rw [hwq]
        intro i hi
        have hij : i ≠ j := fun h => hjT (h ▸ hi)
        simp [he_j, hWu i hi, hij]
      refine ⟨?_, ?_⟩
      · rw [hflatA hsrc.1 hsrc.2, hcoord]
        exact monomial_mem_coordSubspace hwqT
      · rw [hflatC hsrc.1 hsrc.2, hcoord, monomial_mem_plane_iff hj, hwqj]
        exact ht0
    · exact subset_closure ⟨(hAu u hu).mpr (monomial_mem_coordSubspace hWu),
        fun hC' => hWj ((hCu u hu).mp hC')⟩

/-- The local inverse of a monomial chart has injective differential (in a chart). -/
theorem injective_fderiv_of_monomialInverse {j : Fin n} {O : Set Y} (hO : IsOpen O)
    {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    (hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ k j)
    {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y}
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓW : ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (W z') hw) = z')
    {z : Y} (hz : z ∈ O) :
    Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
      (chartAt (ComplexModel n) z z)) := by
  set ez := chartAt (ComplexModel n) z with hez
  have hdiff : DifferentiableAt ℂ (fun ζ => W (ez.symm ζ)) (ez z) := by
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) (ez.map_source (mem_chart_source _ z))
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W
        (ez.symm (ez z)) := by
      rw [ez.left_inv (mem_chart_source _ z)]
      exact (hWs _ hz).mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  by_contra hv0
  apply fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs hℓW hz hv0
  rw [hdiff.fderiv_restrictScalars ℝ]
  exact hv

end Chart

/-! ### Recentred coordinates and transport along local biholomorphisms -/

section Coordinates

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Recentred coordinates from a local inverse**: if `W` is holomorphic on `O` with injective
differential at `z`, then `W - W z` (after the chart at `z`) is a local holomorphic coordinate
system centred at `z`, defined on a part of `O`. -/
theorem exists_recentred_coords {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ W z')
    {z : Y} (hzO : z ∈ O)
    (hFinj : Function.Injective
      (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ)) (chartAt (ComplexModel n) z z))) :
    ∃ Θ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) z).val z),
      Θ.source ⊆ (complexChartAt (n := n) z).val.target ∧
      Θ.toFun ((complexChartAt (n := n) z).val z) = 0 ∧
      ∀ {u : Y}, u ∈ (complexChartAt (n := n) z).val.source →
        (complexChartAt (n := n) z).val u ∈ Θ.source →
          u ∈ O ∧ Θ.toFun ((complexChartAt (n := n) z).val u) = W u - W z := by
  set ez := chartAt (ComplexModel n) z with hez
  set F : ComplexModel n → ComplexModel n := fun ζ => W (ez.symm ζ) with hF
  set Nset : Set (ComplexModel n) := ez.target ∩ ez.symm ⁻¹' O with hNset
  have hNo : IsOpen Nset := ez.continuousOn_symm.isOpen_inter_preimage ez.open_target hO
  have hzN : ez z ∈ Nset :=
    ⟨ez.map_source (mem_chart_source _ z), by
      show ez.symm (ez z) ∈ O
      rw [ez.left_inv (mem_chart_source _ z)]; exact hzO⟩
  have hFd : DifferentiableOn ℂ F Nset := by
    intro ζ hζ
    have h1 := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas (ComplexModel n) z) hζ.1
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) W (ez.symm ζ) :=
      (hWs _ hζ.2).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp (h2.comp _ h1)).differentiableWithinAt
  obtain ⟨Θ, hΘN, hΘF, -⟩ := Hironaka.exists_localHolomorphicEquivAt hNo hzN hFd hFinj
  refine ⟨subConst Θ (W z), fun ζ hζ => (hΘN hζ).1, ?_, fun {u} hu huΘ => ?_⟩
  · show Θ.toFun (ez z) - W z = 0
    rw [hΘF]
    show W (ez.symm (ez z)) - W z = 0
    rw [ez.left_inv (mem_chart_source _ z), sub_self]
  · have h : ez.symm (ez u) ∈ O := (hΘN huΘ).2
    rw [ez.left_inv hu] at h
    refine ⟨h, ?_⟩
    show Θ.toFun (ez u) - W z = W u - W z
    rw [hΘF]
    show W (ez.symm (ez u)) - W z = W u - W z
    rw [ez.left_inv hu]

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **Adapted coordinates pull back along a local biholomorphism.** -/
theorem isCoordinateFamilyAt_of_preimage {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ BlowupSequences.exceptionalLocus n g) {ι : Type*} {A' : ι → Set Z}
    {A : ι → Set Y} {O : Set Z} (hO : IsOpen O) (hzO : z ∈ O)
    (hAO : ∀ i, ∀ u ∈ O, u ∈ A' i ↔ g u ∈ A i) {S : ι → Finset (Fin n)}
    (hA : IsCoordinateFamilyAt n A S (g z)) : IsCoordinateFamilyAt n A' S z := by
  obtain ⟨Φ, hΦt, hΦ0, hΦA⟩ := hA
  set I := 𝓘(ℂ, ComplexModel n) with hI
  have hrange : range I = univ := by simp [hI]
  set e := chartAt (ComplexModel n) z with he
  set e' := chartAt (ComplexModel n) (g z) with he'
  set F : ComplexModel n → ComplexModel n := fun u => e' (g (e.symm u)) with hF
  set N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' (O ∩ g ⁻¹' e'.source) with hN
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hO.inter (hg.continuous.isOpen_preimage _ e'.open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_chart_source _ z), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ z)]
    exact ⟨hzO, mem_chart_source _ (g z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (hg.contMDiffOn (s := univ))).2 z (g z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at this
    rw [hderiv] at this
    exact this.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z) = e' (g z) := by
    simp only [hF, e.left_inv (mem_chart_source _ z)]
  refine ⟨LocalHolomorphicEquivAt.comp Ψ Φ (hΨF ▸ hFz), ?_, ?_, ?_⟩
  · intro u hu
    exact (hΨN hu.1).1
  · change Φ.toFun (Ψ.toFun (e z)) = 0
    rw [hΨF, hFz]
    exact hΦ0
  · intro i hzi y hy hyΘ
    change e y ∈ Ψ.source ∩ Ψ.toFun ⁻¹' Φ.source at hyΘ
    change y ∈ A' i ↔ Φ.toFun (Ψ.toFun (e y)) ∈ coordSubspace (S i)
    have hyN := (hΨN hyΘ.1).2
    rw [mem_preimage, e.left_inv hy] at hyN
    have hFy : F (e y) = e' (g y) := by simp only [hF, e.left_inv hy]
    have hyΦ : e' (g y) ∈ Φ.source := by
      have := hyΘ.2
      rwa [mem_preimage, hΨF, hFy] at this
    rw [hAO i y hyN.1, hΨF, hFy]
    exact hΦA i ((hAO i z hzO).mp hzi) hyN.2 hyΦ

end Coordinates

/-! ### Adapted coordinates and the transformed divisor -/

section Transform

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

variable (n) in
/-- **Coordinates at `x` adapted to `C ⊆ N` and `E`**: one local biholomorphism `Φ` after the
preferred chart in which `C = ℂ^{k_C} × 0`, `N = ℂ^{k_N} × 0`, and every member of `E` through
`x` is the coordinate hyperplane `{w_{s i} = 0}` with `s i < k_N`, the `s i` distinct. -/
def IsAdaptedAt (C N : Set X) (E : List (Set X)) (x : X) : Prop :=
  ∃ (kC kN : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (s : Fin E.length → Fin n),
    Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
    (∀ i, x ∈ E.get i → (s i).1 < kN) ∧ Set.InjOn s {i | x ∈ E.get i} ∧
    ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kC) ∧
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kN) ∧
        ∀ i, x ∈ E.get i → (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (s i) = 0)

/-- **Coordinates on the blowup over a point of the centre.**  From adapted coordinates at `π y`,
the recentred local inverse of a monomial chart gives coordinates at `y` in which `π⁻¹ C`, the
strict transform `N'` (if `y ∈ N'`) and the strict transforms of the members of `E` through `y` are
coordinate subspaces, with the indices `j`, `{t ≥ k_N}` and `s i`. -/
theorem exists_coords_over_centre (hπ : IsBlowupAlong n C π) {N : Set X} {E : List (Set X)}
    (hEc : ∀ H ∈ E, IsClosed H) {y : Y} (hyC : π y ∈ C) (had : IsAdaptedAt n C N E (π y)) :
    ∃ (kN : ℕ) (j : Fin n) (s : Fin E.length → Fin n)
      (Θ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)),
      Θ.source ⊆ (complexChartAt (n := n) y).val.target ∧
      Θ.toFun ((complexChartAt (n := n) y).val y) = 0 ∧
      (∀ i, π y ∈ E.get i → (s i).1 < kN) ∧ Set.InjOn s {i | π y ∈ E.get i} ∧
      (∀ i, y ∈ geoStrictTransform π C (E.get i) → π y ∈ E.get i ∧ s i ≠ j) ∧
      (y ∈ geoStrictTransform π C N → j.1 < kN) ∧
      ∀ {u : Y}, u ∈ (complexChartAt (n := n) y).val.source →
        (complexChartAt (n := n) y).val u ∈ Θ.source →
          (u ∈ π ⁻¹' C ↔ Θ.toFun ((complexChartAt (n := n) y).val u) ∈ coordSubspace {j}) ∧
          (∀ i, y ∈ geoStrictTransform π C (E.get i) →
            (u ∈ geoStrictTransform π C (E.get i) ↔
              Θ.toFun ((complexChartAt (n := n) y).val u) ∈ coordSubspace {s i})) ∧
          (y ∈ geoStrictTransform π C N →
            (u ∈ geoStrictTransform π C N ↔ Θ.toFun ((complexChartAt (n := n) y).val u) ∈
              coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.1))) := by
  classical
  obtain ⟨kC, kN, Φ, s, hΦt, hslt, hsinj, hflat⟩ := had
  have hz' : π y ∈ flatDomain Φ :=
    ⟨mem_chart_source _ (π y), Φ.center_mem_source⟩
  have hflatC : ∀ {y' : X}, y' ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) y' ∈ Φ.source →
        (y' ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) y') ∈ complexCoordinatePlane n kC) :=
    fun hy hyΦ => (hflat hy hyΦ).1
  have hflatN : ∀ {y' : X}, y' ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) y' ∈ Φ.source →
        (y' ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π y) y') ∈
          coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.1)) :=
    fun hy hyΦ => by rw [coordSubspace_eq_complexCoordinatePlane]; exact (hflat hy hyΦ).2.1
  have hflatH : ∀ i, π y ∈ E.get i → ∀ {y' : X}, y' ∈ (chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) y' ∈ Φ.source →
        (y' ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) (π y) y') ∈ coordSubspace {s i}) :=
    fun i hi y' hy hyΦ => by rw [mem_coordSubspace_singleton]; exact (hflat hy hyΦ).2.2 i hi
  obtain ⟨j, hj, O, hO, hyO, W, hWs, hWeq, hℓ, -⟩ :=
    exists_monomialLocalInverse hπ hΦt hflatC hz'
  have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ kC j := fun z' hz'' => by
    show monomial kC j (W z') ∈ Φ.target
    rw [(hWeq z' hz'').2]; exact Φ.mapsTo_toFun (hWeq z' hz'').1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hπ hΦt hflatC hj
  have hFinj := injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hyO
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := exists_recentred_coords hO hWs hyO hFinj
  -- descriptions on the chart
  have hCu : ∀ u ∈ O, (π u ∈ C ↔ W u j = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hj]
  have hHu : ∀ i, π y ∈ E.get i → ∀ u ∈ O,
      (u ∈ geoStrictTransform π C (E.get i) ↔ j ∉ ({s i} : Finset (Fin n)) ∧
        W u ∈ coordSubspace {s i}) := fun i hi u hu =>
    mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC (hflatH i hi) hj hO hWs hWeq hℓ hu
  have hNu : ∀ u ∈ O, (u ∈ geoStrictTransform π C N ↔
      j ∉ (Finset.univ.filter fun t : Fin n => kN ≤ t.1) ∧
        W u ∈ coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.1)) := fun u hu =>
    mem_geoStrictTransform_iff_of_chart hπ hΦt hflatC hflatN hj hO hWs hWeq hℓ hu
  have hthrough : ∀ i, y ∈ geoStrictTransform π C (E.get i) → π y ∈ E.get i := fun i hi =>
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hEc _ (List.get_mem _ _)) hi
  refine ⟨kN, j, s, Θ, hΘt, hΘ0, hslt, hsinj, fun i hi => ⟨hthrough i hi, fun hsj => ?_⟩,
    fun hyN => ?_, fun {u} hu huΘ => ?_⟩
  · have := ((hHu i (hthrough i hi) y hyO).mp hi).1
    exact this (by simp [hsj])
  · have := ((hNu y hyO).mp hyN).1
    simpa using this
  · obtain ⟨huO, hΘu⟩ := hΘ hu huΘ
    rw [hΘu]
    refine ⟨?_, fun i hi => ?_, fun hyN => ?_⟩
    · show π u ∈ C ↔ _
      rw [hCu u huO, mem_coordSubspace_singleton, PiLp.sub_apply, (hCu y hyO).mp hyC, sub_zero]
    · obtain ⟨hjs, hWy⟩ := (hHu i (hthrough i hi) y hyO).mp hi
      rw [hHu i (hthrough i hi) u huO, sub_mem_coordSubspace_iff hWy]
      exact ⟨fun h => h.2, fun h => ⟨hjs, h⟩⟩
    · obtain ⟨hjN, hWy⟩ := (hNu y hyO).mp hyN
      rw [hNu u huO, sub_mem_coordSubspace_iff hWy]
      exact ⟨fun h => h.2, fun h => ⟨hjN, h⟩⟩

/-- **The transformed divisor is a simple normal crossings divisor**: if `E` is SNC and `C`
admits adapted coordinates at each of its points, then `[H₁', …, H_s', π⁻¹ C]` is SNC. -/
theorem isSNCDivisor_geoTransformE (hπ : IsBlowupAlong n C π) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hadapt : ∀ x ∈ C, IsAdaptedAt n C N E x) :
    IsSNCDivisor n (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  classical
  refine ⟨fun H hH => ?_, fun y => ?_⟩
  · rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨H₀, -, rfl⟩ := List.mem_map.mp hH
      exact isClosed_closure
    · rw [List.mem_singleton.mp hH]
      exact hπ.1.1.preimage hπ.contMDiff.continuous
  by_cases hyC : π y ∈ C
  · obtain ⟨kN, j, s, Θ, hΘt, hΘ0, -, hsinj, hthr, -, hcoord⟩ :=
      exists_coords_over_centre hπ hE.1 hyC (hadapt _ hyC)
    refine ⟨fun i => if h : i.1 < E.length then {s ⟨i.1, h⟩} else {j},
      ⟨Θ, hΘt, hΘ0, fun i hi u hu huΘ => ?_⟩, fun i _ => ?_, fun i hi i' hi' hii' => ?_⟩
    · dsimp only at hi ⊢
      rw [get_map_append_singleton] at hi ⊢
      by_cases h : i.1 < E.length
      · simp only [h, dif_pos] at hi ⊢
        exact (hcoord hu huΘ).2.1 _ hi
      · simp only [h, dif_neg, not_false_eq_true] at hi ⊢
        exact (hcoord hu huΘ).1
    · dsimp only
      split_ifs <;> simp
    · dsimp only at hii'
      simp only [mem_ofPred_eq, get_map_append_singleton] at hi hi'
      by_cases h : i.1 < E.length
      · by_cases h' : i'.1 < E.length
        · simp only [h, h', dif_pos, Finset.singleton_inj] at hi hi' hii'
          have := hsinj (hthr _ hi).1 (hthr _ hi').1 hii'
          exact Fin.ext (by simpa using congrArg Fin.val this)
        · simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Finset.singleton_inj] at hi hii'
          exact absurd hii' (hthr _ hi).2
      · by_cases h' : i'.1 < E.length
        · simp only [h, h', dif_pos, dif_neg, not_false_eq_true, Finset.singleton_inj] at hi' hii'
          exact absurd hii'.symm (hthr _ hi').2
        · exact eq_of_not_lt h h'
  · -- off the centre: transport the SNC coordinates of `E` at `π y` along `π`
    obtain ⟨S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard, hinj⟩ := hE.2 (π y)
    set A : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length → Set X := fun i =>
      if h : i.1 < E.length then E.get ⟨i.1, h⟩ else C with hAdef
    set S' : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length → Finset (Fin n) :=
      fun i => if h : i.1 < E.length then S ⟨i.1, h⟩ else ∅ with hS'def
    have hA : IsCoordinateFamilyAt n A S' (π y) := by
      refine ⟨Φ, hΦt, hΦ0, fun i hi y' hy' hy'Φ => ?_⟩
      by_cases h : i.1 < E.length
      · simp only [hAdef, hS'def, h, dif_pos] at hi ⊢
        exact hΦA _ hi hy' hy'Φ
      · simp only [hAdef, h, dif_neg, not_false_eq_true] at hi
        exact absurd hi hyC
    have hO : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
    have hAO : ∀ i, ∀ u ∈ π ⁻¹' Cᶜ,
        u ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i ↔ π u ∈ A i := by
      intro i u hu
      rw [get_map_append_singleton]
      by_cases h : i.1 < E.length
      · simp only [hAdef, h, dif_pos]
        exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
          (hE.1 _ (List.get_mem _ _)) hu
      · simp only [hAdef, h, dif_neg, not_false_eq_true]
        exact Iff.rfl
    have hyE : y ∉ exceptionalLocus n π := fun h =>
      hyC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
    refine ⟨S', isCoordinateFamilyAt_of_preimage hπ.contMDiff hyE hO hyC hAO hA,
      fun i hi => ?_, fun i hi i' hi' hii' => ?_⟩
    · have hi' := (hAO i y hyC).mp hi
      by_cases h : i.1 < E.length
      · simp only [hAdef, h, dif_pos] at hi'
        simp only [hS'def, h, dif_pos]
        exact hcard _ hi'
      · simp only [hAdef, h, dif_neg, not_false_eq_true] at hi'
        exact absurd hi' hyC
    · have h1 := (hAO i y hyC).mp hi
      have h2 := (hAO i' y hyC).mp hi'
      by_cases h : i.1 < E.length
      · by_cases h' : i'.1 < E.length
        · simp only [hAdef, h, h', dif_pos] at h1 h2
          simp only [hS'def, h, h', dif_pos] at hii'
          have := hinj h1 h2 hii'
          exact Fin.ext (by simpa using congrArg Fin.val this)
        · simp only [hAdef, h', dif_neg, not_false_eq_true] at h2
          exact absurd h2 hyC
      · simp only [hAdef, h, dif_neg, not_false_eq_true] at h1
        exact absurd h1 hyC

/-- **The transformed divisor is transverse to the strict transform of `N`**: if `E` is SNC and
transverse to the closed set `N ⊇ C`, and `C` admits adapted coordinates at each of its points, then
`[H₁', …, H_s', π⁻¹ C]` is transverse to `N' = closure (π⁻¹(N \ C))`. -/
theorem isTransverse_geoTransformE (hπ : IsBlowupAlong n C π) {N : Set X} (hNc : IsClosed N)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    (hadapt : ∀ x ∈ C, IsAdaptedAt n C N E x) :
    IsTransverse n (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  classical
  intro y hyN
  by_cases hyC : π y ∈ C
  · obtain ⟨kN, j, s, Θ, hΘt, hΘ0, hslt, -, hthr, hjN, hcoord⟩ :=
      exists_coords_over_centre hπ hE.1 hyC (hadapt _ hyC)
    have hjN' := hjN hyN
    refine ⟨Finset.univ.filter fun t : Fin n => kN ≤ t.1,
      fun i => if h : i.1 < E.length then {s ⟨i.1, h⟩} else {j},
      ⟨Θ, hΘt, hΘ0, ?_⟩, fun i hi => ?_⟩
    · rintro (_ | i) hi u hu huΘ
      · exact (hcoord hu huΘ).2.2 hyN
      · simp only [Option.elim] at hi ⊢
        rw [get_map_append_singleton] at hi ⊢
        by_cases h : i.1 < E.length
        · simp only [h, dif_pos] at hi ⊢
          exact (hcoord hu huΘ).2.1 _ hi
        · simp only [h, dif_neg, not_false_eq_true] at hi ⊢
          exact (hcoord hu huΘ).1
    · rw [get_map_append_singleton] at hi
      by_cases h : i.1 < E.length
      · simp only [h, dif_pos] at hi ⊢
        refine ⟨Finset.card_singleton _, Finset.disjoint_singleton_left.mpr ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        exact hslt _ (hthr _ hi).1
      · simp only [h, dif_neg, not_false_eq_true]
        refine ⟨Finset.card_singleton _, Finset.disjoint_singleton_left.mpr ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        exact hjN'
  · have hyπN : π y ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hyN
    obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hS⟩ := hT (π y) hyπN
    set A : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length) → Set X :=
      fun o => o.elim N fun i => if h : i.1 < E.length then E.get ⟨i.1, h⟩ else C with hAdef
    set S' : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length) →
        Finset (Fin n) :=
      fun o => o.elim S₀ fun i => if h : i.1 < E.length then S ⟨i.1, h⟩ else ∅ with hS'def
    have hA : IsCoordinateFamilyAt n A S' (π y) := by
      refine ⟨Φ, hΦt, hΦ0, ?_⟩
      rintro (_ | i) hi y' hy' hy'Φ
      · exact hΦA none hi hy' hy'Φ
      · by_cases h : i.1 < E.length
        · simp only [hAdef, hS'def, Option.elim, h, dif_pos] at hi ⊢
          exact hΦA (some ⟨i.1, h⟩) hi hy' hy'Φ
        · simp only [hAdef, Option.elim, h, dif_neg, not_false_eq_true] at hi
          exact absurd hi hyC
    have hO : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
    have hAO : ∀ o, ∀ u ∈ π ⁻¹' Cᶜ,
        u ∈ (o.elim (geoStrictTransform π C N) fun i =>
          (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i) ↔ π u ∈ A o := by
      rintro (_ | i) u hu
      · exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNc hu
      · simp only [Option.elim]
        rw [get_map_append_singleton]
        by_cases h : i.1 < E.length
        · simp only [hAdef, Option.elim, h, dif_pos]
          exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
            (hE.1 _ (List.get_mem _ _)) hu
        · simp only [hAdef, Option.elim, h, dif_neg, not_false_eq_true]
          exact Iff.rfl
    have hyE : y ∉ exceptionalLocus n π := fun h =>
      hyC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
    refine ⟨S₀, fun i => S' (some i),
      isCoordinateFamilyAt_of_preimage hπ.contMDiff hyE hO hyC hAO hA, fun i hi => ?_⟩
    have hi' := (hAO (some i) y hyC).mp hi
    by_cases h : i.1 < E.length
    · simp only [hAdef, Option.elim, h, dif_pos] at hi'
      simp only [hS'def, Option.elim, h, dif_pos]
      exact hS _ hi'
    · simp only [hAdef, Option.elim, h, dif_neg, not_false_eq_true] at hi'
      exact absurd hi' hyC

/-! ### The case `E = []`: the exceptional divisor alone -/

/-- **Adapted coordinates exist when `E` is empty**: nested flattening coordinates for `C ⊆ N`. -/
theorem isAdaptedAt_nil {N : Set X} (hC : IsClosedSubmanifold n C) (hN : IsClosedSubmanifold n N)
    (hCN : C ⊆ N) {x : X} (hx : x ∈ C) : IsAdaptedAt n C N ([] : List (Set X)) x := by
  obtain ⟨kC, hkC⟩ := hC.2 x hx
  obtain ⟨kN, hkN⟩ := hN.2 x (hCN hx)
  obtain ⟨Φ, hΦt, -, hflat⟩ :=
    NestedFlattening.exists_nested_flattening (le_of_regularAtDim_subset hkC hkN hCN) hkC hkN hCN
  exact ⟨kC, kN, Φ, Fin.elim0, hΦt, fun i => i.elim0, fun i => i.elim0,
    fun hy hyΦ => ⟨(hflat hy hyΦ).1, (hflat hy hyΦ).2, fun i => i.elim0⟩⟩

/-- **The exceptional divisor `π⁻¹ C` alone is a simple normal crossings divisor.** -/
theorem isSNCDivisor_preimage_centre (hπ : IsBlowupAlong n C π) :
    IsSNCDivisor n [π ⁻¹' C] := by
  have := isSNCDivisor_geoTransformE hπ (N := C) (isSNCDivisor_nil (M := X))
    fun x hx => isAdaptedAt_nil hπ.1 hπ.1 subset_rfl hx
  simpa using this

/-- **The exceptional divisor is transverse to the strict transform of a closed submanifold
`N ⊇ C`.** -/
theorem isTransverse_preimage_centre (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N) :
    IsTransverse n (geoStrictTransform π C N) [π ⁻¹' C] := by
  have := isTransverse_geoTransformE hπ hN.1 (isSNCDivisor_nil (M := X))
    (isTransverse_nil_of_isClosedSubmanifold hN) fun x hx => isAdaptedAt_nil hπ.1 hN hCN hx
  simpa using this

end Transform

end

end Hironaka.BlowupSNCTransform
