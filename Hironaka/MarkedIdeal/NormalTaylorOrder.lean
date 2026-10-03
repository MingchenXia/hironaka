/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Analytic.IdealPowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The order of a germ from its normal derivatives along a submanifold

Source: Włodarczyk 2005, proof of Lemma `le:S`; GGT 2008 (`wlodarczyk09-analytic-resolution`), proof of Proposition
5.6.4: in coordinates `(y, x)` with `S = {x = 0}`, write `f = ∑_α c_α(y) x^α`; then `ord_p f ≥ μ` as soon as `ord_p
(c_α|_S) ≥ μ - |α|` for `|α| < μ`, and `c_α|_S = (α!)⁻¹ (∂^α_x f)|_S`.

* `inNormalPow_of_normalDeriv` (in `ℂⁿ`): if for every list `L` of normal directions (`eₗ`, `l ≥ k`) with `|L| < μ`
  the derivative `∂^L F` agrees on the plane `ℂᵏ × 0` near `0` with a germ of `𝔪₀^{μ-|L|}`, then `F ∈ 𝔪₀^μ`
  (`InNormalPow 0 0 μ F`).  Induction on the number of normal coordinates: expand in the first one with the Taylor
  tail `exists_taylor_tail`; the coefficients `∂^j F ∘ pr` satisfy the hypothesis for the bigger plane with order
  `μ - j`.
* `inNormalPow_comp_of_mem_idealPow`: a germ of `𝔪_p^m` read in coordinates centred at `p` lies in `𝔪₀^m`.
* `mem_idealPow_of_normalDeriv` (on a manifold): for coordinates `ψ` centred at `p ∈ S` in which `S` is the plane
  `ℂᵏ × 0`, a holomorphic `f` lies in `𝔪_p^μ` if each normal derivative `∂^L f` (`|L| < μ`) vanishes to order
  `μ - |L|` along `S` at `p`.
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff Nat

namespace Hironaka.NormalTaylorOrder

open Hironaka.HolomorphicIdealSheaves Complex HolomorphicTaylorTail GermIdealOrder IdealWeightPowers OrderTaylor

noncomputable section

section Model

variable {n : ℕ}

/-- The basis vector `eₗ` of `ℂⁿ`. -/
abbrev bv (l : Fin n) : ComplexModel n := EuclideanSpace.single l (1 : ℂ)

/-- **A list of normal directions** for the plane `ℂᵏ × 0`: indices `l ≥ k`. -/
def NormalIdx (k : ℕ) (L : List (Fin n)) : Prop := ∀ l ∈ L, k ≤ l.1

theorem NormalIdx.mono {k k' : ℕ} (hkk' : k ≤ k') {L : List (Fin n)} (h : NormalIdx k' L) : NormalIdx k L :=
  fun l hl => le_trans hkk' (h l hl)

theorem NormalIdx.append {k : ℕ} {L L' : List (Fin n)} (h : NormalIdx k L) (h' : NormalIdx k L') :
    NormalIdx k (L ++ L') := fun l hl => by
  rcases List.mem_append.mp hl with hl | hl
  · exact h l hl
  · exact h' l hl

theorem normalIdx_replicate {k : ℕ} {i : Fin n} (hi : k ≤ i.1) (j : ℕ) : NormalIdx k (List.replicate j i) :=
  fun l hl => by rw [List.eq_of_mem_replicate hl]; exact hi

/-- `A ∈ 𝔪_q^m` and `B ∈ 𝔪_q` give `AB ∈ 𝔪_q^{m+1}` (normal-power form, `k = 0`). -/
theorem InNormalPow.mul_of_one {q : ComplexModel n} {m : ℕ} {A B : ComplexModel n → ℂ}
    (hA : InNormalPow 0 q m A) (hB : InNormalPow 0 q 1 B) : InNormalPow 0 q (m + 1) (fun u => A u * B u) := by
  obtain ⟨H, -, hH, hBeq⟩ := hB
  refine ⟨fun i u => H i u * A u, fun i hi => absurd hi (Nat.not_lt_zero _), fun i => ?_, ?_⟩
  · exact hA.const_mul_holo (hH i)
  · filter_upwards [hBeq] with u hu
    rw [hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Composition with the projection killing a coordinate keeps `𝔪₀^m`. -/
theorem InNormalPow.comp_killCoord (i : Fin n) :
    ∀ {m : ℕ} {H : ComplexModel n → ℂ}, InNormalPow 0 (0 : ComplexModel n) m H →
      InNormalPow 0 (0 : ComplexModel n) m (fun u => H (killCoord i u))
  | 0, H, hH => by
    have ht : Tendsto (killCoord i) (𝓝 (0 : ComplexModel n)) (𝓝 0) := by
      simpa using (killCoord i).continuous.tendsto (0 : ComplexModel n)
    filter_upwards [ht.eventually hH] with u hu
    exact hu.comp u (killCoord i).differentiableAt
  | m + 1, H, ⟨K, _, hK, hHeq⟩ => by
    classical
    have ht : Tendsto (killCoord i) (𝓝 (0 : ComplexModel n)) (𝓝 0) := by
      simpa using (killCoord i).continuous.tendsto (0 : ComplexModel n)
    refine ⟨fun l u => if l = i then 0 else K l (killCoord i u), fun l hl => absurd hl (Nat.not_lt_zero _),
      fun l => ?_, ?_⟩
    · by_cases hl : l = i
      · exact (inNormalPow_zero_fun (k := 0) (q := (0 : ComplexModel n)) m).congr
          (Eventually.of_forall fun u => by simp [hl])
      · exact (InNormalPow.comp_killCoord i (hK l)).congr (Eventually.of_forall fun u => by simp [hl])
    · filter_upwards [ht.eventually hHeq] with u hu
      rw [hu]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [killCoord_apply_apply]
      split_ifs with hl <;> simp

/-- The projection killing coordinate `i` fixes the basis vectors `eₗ`, `l ≠ i`. -/
theorem killCoord_bv {i l : Fin n} (hl : l ≠ i) : killCoord i (bv l) = bv l :=
  killCoord_of_apply_eq_zero (by simp [bv, Ne.symm hl])

/-- Induction on the number of normal coordinates for `inNormalPow_of_normalDeriv`. -/
theorem inNormalPow_of_normalDeriv_aux (d : ℕ) :
    ∀ (k : ℕ), n - k = d → ∀ (μ : ℕ) {F : ComplexModel n → ℂ},
      (∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F u) →
      (∀ L : List (Fin n), NormalIdx k L → L.length < μ → ∃ H : ComplexModel n → ℂ,
        InNormalPow 0 (0 : ComplexModel n) (μ - L.length) H ∧
        ∀ᶠ u in 𝓝 (0 : ComplexModel n), u ∈ complexCoordinatePlane n k → iterDeriv (L.map bv) F u = H u) →
      InNormalPow 0 (0 : ComplexModel n) μ F := by
  induction d with
  | zero =>
    intro k hk μ F hF hL
    rcases μ with _ | μ
    · exact hF
    · obtain ⟨H, hH, hFH⟩ := hL [] (fun l hl => absurd hl (by simp)) (by simp)
      have hall : ∀ y : ComplexModel n, y ∈ complexCoordinatePlane n k :=
        fun y i hi => absurd i.2 (by omega)
      refine hH.congr ?_
      filter_upwards [hFH] with u hu
      exact hu (hall u)
  | succ d ih =>
    intro k hk μ F hF hL
    have hkn : k < n := by omega
    set i : Fin n := ⟨k, hkn⟩ with hidef
    set e : ComplexModel n := bv i with hedef
    set pr : ComplexModel n →L[ℂ] ComplexModel n := killCoord i with hprdef
    have hpr0 : pr 0 = 0 := map_zero pr
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hF
    have hFU : DifferentiableOn ℂ F (ball 0 r) := fun z hz => (hball z hz).differentiableWithinAt
    have hprt : Tendsto pr (𝓝 0) (𝓝 0) := by
      simpa [hpr0] using pr.continuous.tendsto 0
    have hprU : ∀ᶠ u in 𝓝 (0 : ComplexModel n), pr u ∈ ball (0 : ComplexModel n) r :=
      hprt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    obtain ⟨G, hGd, hGeq⟩ := exists_taylor_tail hF e μ
    have hφt : Tendsto (fun u : ComplexModel n => (pr u, u i)) (𝓝 0) (𝓝 ((0 : ComplexModel n), (0 : ℂ))) := by
      have hc : Continuous (fun u : ComplexModel n => (pr u, u i)) :=
        pr.continuous.prodMk (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous
      simpa [hpr0] using hc.tendsto 0
    set g : ℕ → ComplexModel n → ℂ := fun j u => iterDeriv (List.replicate j e) F (pr u) with hgdef
    have hg : ∀ j < μ, InNormalPow 0 (0 : ComplexModel n) (μ - j) (g j) := by
      intro j hj
      refine ih (k + 1) (by omega) (μ - j) ?_ ?_
      · filter_upwards [hprU] with u hu
        exact ((differentiableOn_iterDeriv hFU isOpen_ball _).differentiableAt
          (isOpen_ball.mem_nhds hu)).comp u pr.differentiableAt
      · intro L hLn hLlen
        set L' : List (Fin n) := L ++ List.replicate j i with hL'
        have hL'n : NormalIdx k L' := (hLn.mono (Nat.le_succ k)).append (normalIdx_replicate le_rfl j)
        have hL'len : L'.length < μ := by simp [hL']; omega
        obtain ⟨H', hH', hEq⟩ := hL L' hL'n hL'len
        refine ⟨fun u => H' (pr u), ?_, ?_⟩
        · have h1 := InNormalPow.comp_killCoord i hH'
          rwa [show μ - L'.length = μ - j - L.length by simp [hL']; omega] at h1
        · filter_upwards [hprU, hprt.eventually hEq] with y hyU hyEq hy
          have hcomp := iterDeriv_comp_clm (differentiableOn_iterDeriv hFU isOpen_ball
            (List.replicate j e)) isOpen_ball pr (L.map bv) y hyU
          have hmap : (L.map bv).map pr = L.map bv := by
            rw [List.map_map]
            refine List.map_congr_left fun l hl => ?_
            have hli : l ≠ i := fun h => by have := hLn l hl; rw [h] at this; simp [hidef] at this
            exact killCoord_bv hli
          simp only [hgdef]
          rw [hcomp, hmap, ← iterDeriv_append]
          have hpl : pr y ∈ complexCoordinatePlane n k := fun l hl => by
            change killCoord i y l = 0
            rw [killCoord_apply_apply]
            split_ifs with hli
            · rfl
            · exact hy l (by
                have : l.1 ≠ k := fun h => hli (Fin.ext h)
                omega)
          have := hyEq hpl
          rw [hL', List.map_append, List.map_replicate] at this
          exact this
    have hi0 : (0 : ℕ) ≤ i.1 := Nat.zero_le _
    have hterm : ∀ j ∈ Finset.range μ, InNormalPow 0 (0 : ComplexModel n) μ
        (fun u => (j ! : ℂ)⁻¹ * (u i ^ j * g j u)) := by
      intro j hj
      have hjμ : j < μ := Finset.mem_range.mp hj
      have h1 := (hg j hjμ).coord_pow_mul hi0 j
      rw [Nat.sub_add_cancel hjμ.le] at h1
      exact h1.const_mul_holo (Eventually.of_forall fun _ => differentiableAt_const _)
    have hlast : InNormalPow 0 (0 : ComplexModel n) μ (fun u => u i ^ μ * G (pr u, u i)) := by
      have h0 : InNormalPow 0 (0 : ComplexModel n) 0 (fun u => G (pr u, u i)) := by
        filter_upwards [hφt.eventually hGd] with u hu
        exact hu.comp u (pr.differentiableAt.prodMk
          (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt)
      simpa using h0.coord_pow_mul hi0 μ
    refine ((inNormalPow_finset_sum _ hterm).add hlast).congr ?_
    filter_upwards [hφt.eventually hGeq] with u hu
    have hu' : F u = ∑ j ∈ Finset.range μ,
        (j ! : ℂ)⁻¹ * iterDeriv (List.replicate j e) F (pr u) * u i ^ j + u i ^ μ * G (pr u, u i) := by
      have hsum : pr u + u i • e = u := killCoord_add i u
      simpa only [hsum] using hu
    rw [hu']
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hgdef]
    ring

/-- **The order from the normal derivatives, in `ℂⁿ`.**  If `F` is holomorphic near `0` and for every list `L` of
normal directions (`eₗ`, `l ≥ k`) with `|L| < μ` the derivative `∂^L F` agrees on the plane `ℂᵏ × 0` near `0` with
a germ of `𝔪₀^{μ - |L|}`, then `F ∈ 𝔪₀^μ`. -/
theorem inNormalPow_of_normalDeriv (k μ : ℕ) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F u)
    (hL : ∀ L : List (Fin n), NormalIdx k L → L.length < μ → ∃ H : ComplexModel n → ℂ,
      InNormalPow 0 (0 : ComplexModel n) (μ - L.length) H ∧
      ∀ᶠ u in 𝓝 (0 : ComplexModel n), u ∈ complexCoordinatePlane n k → iterDeriv (L.map bv) F u = H u) :
    InNormalPow 0 (0 : ComplexModel n) μ F :=
  inNormalPow_of_normalDeriv_aux (n - k) k rfl μ hF hL

/-- A function holomorphic near `0` and vanishing at `0` lies in `𝔪₀`. -/
theorem inNormalPow_one_of_apply_eq_zero {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F u) (h0 : F 0 = 0) :
    InNormalPow 0 (0 : ComplexModel n) 1 F := by
  refine inNormalPow_of_iterDeriv_eq_zero 1 (fun i _ => rfl) hF (Eventually.of_forall fun y hy L hL => ?_)
  have hy0 : y = 0 := by ext i; exact hy i (Nat.zero_le _)
  have hL0 : L = [] := List.length_eq_zero_iff.mp (by omega)
  subst hy0 hL0
  exact h0

end Model

/-! ### On a manifold -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A germ of `𝔪_p^m`, read in coordinates centred at `p`, lies in `𝔪₀^m`.** -/
theorem inNormalPow_comp_of_mem_idealPow {p : M} {inv : ComplexModel n → M}
    (hinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) inv u)
    (hinv0 : inv 0 = p) :
    ∀ {m : ℕ} {h : M → ℂ}, (idealPow (pointIdeal n p) m).mem p h →
      InNormalPow 0 (0 : ComplexModel n) m (fun u => h (inv u))
  | 0, h, hh => by
    have hcont : ContinuousAt inv 0 := hinv.self_of_nhds.continuousAt
    have hh' : HolomorphicAt n h p := hh
    rw [← hinv0] at hh'
    filter_upwards [hinv, hcont.eventually hh'] with u hu hhu
    exact mdifferentiableAt_iff_differentiableAt.mp (hhu.comp u hu)
  | m + 1, h, hh => by
    obtain ⟨-, N, s, a, hs, ha, hsum⟩ := mem_idealPow_succ_iff.mp hh
    have hcont : ContinuousAt inv 0 := hinv.self_of_nhds.continuousAt
    have hterm : ∀ i : Fin N, InNormalPow 0 (0 : ComplexModel n) (m + 1) (fun u => a i (inv u) * s i (inv u)) := by
      intro i
      obtain ⟨b, c, hb, hc, hsi⟩ := hs i
      have hB := inNormalPow_comp_of_mem_idealPow hinv hinv0 hb
      have hC : InNormalPow 0 (0 : ComplexModel n) 1 (fun u => c (inv u)) := by
        refine inNormalPow_one_of_apply_eq_zero ?_ (by rw [hinv0]; exact apply_eq_zero_of_mem_pointIdeal hc)
        have hc' : HolomorphicAt n c p := hc.1
        rw [← hinv0] at hc'
        filter_upwards [hinv, hcont.eventually hc'] with u hu hcu
        exact mdifferentiableAt_iff_differentiableAt.mp (hcu.comp u hu)
      have hA : ∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun u => a i (inv u)) u := by
        have ha' : HolomorphicAt n (a i) p := ha i
        rw [← hinv0] at ha'
        filter_upwards [hinv, hcont.eventually ha'] with u hu hau
        exact mdifferentiableAt_iff_differentiableAt.mp (hau.comp u hu)
      refine ((InNormalPow.mul_of_one hB hC).const_mul_holo hA).congr (Eventually.of_forall fun u => ?_)
      simp only [hsi, Pi.mul_apply]
    have hsum' : (fun u => h (inv u)) =ᶠ[𝓝 (0 : ComplexModel n)]
        fun u => ∑ i, a i (inv u) * s i (inv u) := by
      rw [← hinv0] at hsum
      exact hcont.eventually hsum
    exact (inNormalPow_finset_sum _ fun i _ => hterm i).congr hsum'

/-- **The order of a germ from its normal derivatives along a submanifold.**  Let `ψ` be holomorphic coordinates
centred at `p ∈ S` (with holomorphic inverse `inv`) in which `S` is the plane `ℂᵏ × 0` near `p`, and let `f` be
holomorphic at `p`.  If for every list `L` of normal directions with `|L| < μ` the normal derivative
`y ↦ ∂^L (f ∘ inv)(ψ y)` vanishes to order `μ - |L|` along `S` at `p`, then `f ∈ 𝔪_p^μ`. -/
theorem mem_idealPow_of_normalDeriv {S : Set M} {p : M} {k μ : ℕ} {ψ : M → ComplexModel n}
    {inv : ComplexModel n → M}
    (hψ : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ y) (hψp : ψ p = 0)
    (hinv : ∀ᶠ u in 𝓝 (0 : ComplexModel n), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) inv u)
    (hinv0 : inv 0 = p) (hleft : ∀ᶠ y in 𝓝 p, inv (ψ y) = y)
    (hright : ∀ᶠ u in 𝓝 (0 : ComplexModel n), ψ (inv u) = u)
    (hflat : ∀ᶠ y in 𝓝 p, (y ∈ S ↔ ψ y ∈ complexCoordinatePlane n k))
    {f : M → ℂ} (hf : HolomorphicAt n f p)
    (hL : ∀ L : List (Fin n), NormalIdx k L → L.length < μ →
      VanishesToOrderOn n S p (μ - L.length) (fun y => iterDeriv (L.map bv) (fun u => f (inv u)) (ψ y))) :
    (idealPow (pointIdeal n p) μ).mem p f := by
  have hcont : ContinuousAt inv 0 := hinv.self_of_nhds.continuousAt
  have hcont' : Tendsto inv (𝓝 (0 : ComplexModel n)) (𝓝 p) := by
    have := hcont.tendsto; rwa [hinv0] at this
  have hF : ∀ᶠ u in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun u => f (inv u)) u := by
    filter_upwards [hinv, hcont'.eventually hf] with u hu hfu
    exact mdifferentiableAt_iff_differentiableAt.mp (hfu.comp u hu)
  have hFin : InNormalPow 0 (0 : ComplexModel n) μ (fun u => f (inv u)) := by
    refine inNormalPow_of_normalDeriv k μ hF fun L hLn hLlen => ?_
    obtain ⟨h, hh, hgh⟩ := hL L hLn hLlen
    refine ⟨fun u => h (inv u), inNormalPow_comp_of_mem_idealPow hinv hinv0 hh, ?_⟩
    filter_upwards [hright, hcont'.eventually hgh, hcont'.eventually hflat] with u hu hghu hflu hpl
    have hS : inv u ∈ S := hflu.mpr (by rw [hu]; exact hpl)
    have := hghu hS
    rw [hu] at this
    exact this
  have hψI : ∀ i : Fin n, 0 ≤ i.1 → (pointIdeal n p).mem p (fun y => ψ y i) := by
    intro i _
    refine mem_pointIdeal_of_apply_eq_zero ?_ (by simp [hψp])
    filter_upwards [hψ] with y hy
    exact (mdifferentiableAt_iff_differentiableAt.mpr
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt).comp y hy
  refine mem_idealPow_of_inNormalPow hψp hψ hψI μ hFin ?_
  filter_upwards [hleft] with y hy
  rw [hy]

end Manifold

end

end Hironaka.NormalTaylorOrder
