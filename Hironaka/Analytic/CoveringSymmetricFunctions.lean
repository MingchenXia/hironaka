/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.GermParametrizationDense

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonical defining functions of a finite unramified covering

Blueprint `rem:covering-symmetric-functions` (Demailly, *Complex analytic and differential
geometry*, II.8.8, the covering step of the Remmert--Stein theorem; step M9 of the route to Remmert's
proper mapping theorem, `blueprint/src/remmert.tex`).

Let `B₀ ⊆ ℂˢ` be open and preconnected, `R > 0`, and `E ⊆ B₀ × B(0, R) ⊆ ℂˢ × ℂᵈ` such that the
projection `E → B₀` is proper (`E ∩ π⁻¹K` is compact for compact `K ⊆ B₀`) and every point of `E` has
a neighbourhood `V` with `E ∩ V` the graph of a holomorphic map over an open set.

* `exists_local_sheets`: the fibre `E_w = {z | (w, z) ∈ E}` over `w₀ ∈ B₀` is finite, and near `w₀`
  the fibres are the values of finitely many holomorphic sheets `g_z` (`z ∈ E_{w₀}`), pairwise
  distinct (graph neighbourhoods separated by `Set.Finite.t2_separation`, properness off them).
* `exists_card_eq`: the fibres are finite of constant cardinality `q` on `B₀` (locally constant).
* `differentiableOn_coeff_fibrePoly`, `norm_coeff_fibrePoly_le`: for a linear form `λ` on `ℂᵈ`, the
  coefficients of `P_λ(w; T) = ∏_{z ∈ E_w} (T - λ z)` (the elementary symmetric functions of the
  values `λ z`, up to sign) are holomorphic on `B₀` and bounded by `(1 + ‖λ‖ R) ^ q`.
* `exists_forms_mem_iff`: for the `q d + 1` Vandermonde forms `λ_i(z) = ∑_k i^k z_k`
  (`GermParametrizationDense.form`), `(w, z) ∈ E` iff `P_{λ_i}(w; λ_i z) = 0` for all `i`
  (pigeonhole: `d` of the forms agree at `z` with one fibre point).

Sorry-free.
-/

open Set Filter Topology Metric Polynomial
open scoped ContDiff

noncomputable section

namespace Hironaka.CoveringSymmetricFunctions

open Hironaka.RegularLocusDense GermParametrizationData

variable {s d : ℕ}

/-- The fibre of `E` over `w`. -/
def fibreSet (E : Set (ComplexModel s × ComplexModel d)) (w : ComplexModel s) :
    Set (ComplexModel d) :=
  {z | (w, z) ∈ E}

open Classical in
/-- The canonical polynomial `P_λ(w; T) = ∏_{z ∈ E_w} (T - λ z)` (`1` if the fibre is infinite). -/
def fibrePoly (E : Set (ComplexModel s × ComplexModel d)) (l : ComplexModel d →L[ℂ] ℂ)
    (w : ComplexModel s) : ℂ[X] :=
  if h : (fibreSet E w).Finite then ∏ z ∈ h.toFinset, (X - C (l z)) else 1

theorem fibrePoly_eq {E : Set (ComplexModel s × ComplexModel d)} (l : ComplexModel d →L[ℂ] ℂ)
    {w : ComplexModel s} (h : (fibreSet E w).Finite) :
    fibrePoly E l w = ∏ z ∈ h.toFinset, (X - C (l z)) := by
  rw [fibrePoly, dif_pos h]

variable {B₀ : Set (ComplexModel s)} {R : ℝ} {E : Set (ComplexModel s × ComplexModel d)}

/-- **Local sheets.**  Over a neighbourhood of `w₀ ∈ B₀` the fibres of `E` are the values of the
holomorphic sheets `g z` (`z` in the finite fibre over `w₀`), pairwise distinct. -/
theorem exists_local_sheets (hB₀ : IsOpen B₀)
    (hprop : ∀ K ⊆ B₀, IsCompact K → IsCompact (E ∩ Prod.fst ⁻¹' K))
    (hgraph : ∀ p ∈ E, ∃ V ∈ 𝓝 p, ∃ U : Set (ComplexModel s), IsOpen U ∧
      ∃ g : ComplexModel s → ComplexModel d, DifferentiableOn ℂ g U ∧
        E ∩ V = (fun w => (w, g w)) '' U)
    {w₀ : ComplexModel s} (hw₀ : w₀ ∈ B₀) :
    (fibreSet E w₀).Finite ∧ ∃ N ∈ 𝓝 w₀, ∃ g : ComplexModel d → ComplexModel s → ComplexModel d,
      (∀ z ∈ fibreSet E w₀, ∀ w ∈ N, DifferentiableAt ℂ (g z) w) ∧
      ∀ w ∈ N, fibreSet E w = (fun z => g z w) '' fibreSet E w₀ ∧
        InjOn (fun z => g z w) (fibreSet E w₀) := by
  classical
  set F₀ := fibreSet E w₀ with hF₀
  -- graph data at the points of the fibre
  have hdata : ∀ z, ∃ V : Set (ComplexModel s × ComplexModel d), ∃ U : Set (ComplexModel s),
      ∃ g : ComplexModel s → ComplexModel d, z ∈ F₀ → (V ∈ 𝓝 (w₀, z) ∧ IsOpen U ∧
        DifferentiableOn ℂ g U ∧ E ∩ V = (fun w => (w, g w)) '' U) := by
    intro z
    by_cases hz : z ∈ F₀
    · obtain ⟨V, hV, U, hU, g, hg, hEV⟩ := hgraph (w₀, z) hz
      exact ⟨V, U, g, fun _ => ⟨hV, hU, hg, hEV⟩⟩
    · exact ⟨univ, univ, fun _ => 0, fun h => absurd h hz⟩
  choose V U g hVUg using hdata
  have hcentre : ∀ z ∈ F₀, w₀ ∈ U z ∧ g z w₀ = z := by
    intro z hz
    obtain ⟨hV, -, -, hEV⟩ := hVUg z hz
    have hmem : (w₀, z) ∈ E ∩ V z := ⟨hz, mem_of_mem_nhds hV⟩
    rw [hEV] at hmem
    obtain ⟨w, hwU, hw⟩ := hmem
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, hgz⟩ := hw
    exact ⟨hwU, hgz⟩
  -- the fibre is finite: compact and discrete
  have hFc : IsCompact F₀ := by
    have h := (hprop {w₀} (singleton_subset_iff.mpr hw₀) isCompact_singleton).image
      continuous_snd
    convert h using 1
    ext z
    constructor
    · intro hz
      exact ⟨(w₀, z), ⟨hz, rfl⟩, rfl⟩
    · rintro ⟨⟨w, z'⟩, ⟨hE, hw⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hw
      subst hw
      exact hE
  have hiso : ∀ z ∈ F₀, ∀ z' ∈ F₀, (w₀, z') ∈ V z → z' = z := by
    intro z hz z' hz' hV'
    obtain ⟨-, -, -, hEV⟩ := hVUg z hz
    have hmem : (w₀, z') ∈ E ∩ V z := ⟨hz', hV'⟩
    rw [hEV] at hmem
    obtain ⟨w, -, hw⟩ := hmem
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, hgz⟩ := hw
    rw [← hgz, (hcentre z hz).2]
  have hFfin : F₀.Finite := by
    have hO : ∀ z ∈ F₀, {z' | (w₀, z') ∈ interior (V z)} ∈ 𝓝 z := fun z hz =>
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (interior_mem_nhds.mpr (hVUg z hz).1)
    obtain ⟨t, htcov⟩ := hFc.elim_nhds_subcover' (fun z _ => {z' | (w₀, z') ∈ interior (V z)}) hO
    refine (t.image Subtype.val).finite_toSet.subset fun z' hz' => ?_
    obtain ⟨x, hxt, hz'x⟩ := mem_iUnion₂.mp (htcov hz')
    have := hiso x x.2 z' hz' (interior_subset hz'x)
    rw [this, Finset.coe_image]
    exact ⟨x, hxt, rfl⟩
  refine ⟨hFfin, ?_⟩
  -- disjoint neighbourhoods of the fibre points
  obtain ⟨Sep, hSep, hdisj⟩ := hFfin.t2_separation
  set Q : ComplexModel d → Set (ComplexModel s × ComplexModel d) :=
    fun z => interior (V z) ∩ (univ ×ˢ Sep z) with hQ
  have hQo : ∀ z, IsOpen (Q z) := fun z => isOpen_interior.inter (isOpen_univ.prod (hSep z).2)
  have hQz : ∀ z ∈ F₀, (w₀, z) ∈ Q z := fun z hz =>
    ⟨interior_mem_nhds.mpr (hVUg z hz).1 |> mem_of_mem_nhds, mem_univ _, (hSep z).1⟩
  -- properness off the neighbourhoods
  obtain ⟨K, hKc, hw₀K, hKB⟩ := exists_compact_subset hB₀ hw₀
  set Cset := (E ∩ Prod.fst ⁻¹' K) \ ⋃ z ∈ F₀, Q z with hCset
  have hCc : IsCompact (Prod.fst '' Cset) :=
    ((hprop K hKB hKc).diff (isOpen_biUnion fun z _ => hQo z)).image continuous_fst
  have hw₀C : w₀ ∉ Prod.fst '' Cset := by
    rintro ⟨⟨w, z'⟩, ⟨⟨hE, -⟩, hnot⟩, hw⟩
    simp only at hw
    subst hw
    exact hnot (mem_iUnion₂.mpr ⟨z', hE, hQz z' hE⟩)
  set N : Set (ComplexModel s) := (interior K ∩ (Prod.fst '' Cset)ᶜ) ∩
    ⋂ z ∈ F₀, (U z ∩ {w | (w, g z w) ∈ Q z}) with hN
  have hNmem : N ∈ 𝓝 w₀ := by
    refine inter_mem (inter_mem (interior_mem_nhds.mpr (mem_interior_iff_mem_nhds.mp hw₀K))
      (hCc.isClosed.isOpen_compl.mem_nhds hw₀C)) ((biInter_mem hFfin).mpr fun z hz => ?_)
    obtain ⟨-, hUo, hgd, -⟩ := hVUg z hz
    obtain ⟨hw₀U, hgw₀⟩ := hcentre z hz
    have hcont : ContinuousAt (fun w => (w, g z w)) w₀ :=
      continuousAt_id.prodMk (hgd.continuousOn.continuousAt (hUo.mem_nhds hw₀U))
    refine inter_mem (hUo.mem_nhds hw₀U) (hcont.preimage_mem_nhds ?_)
    simp only [hgw₀]
    exact (hQo z).mem_nhds (hQz z hz)
  refine ⟨N, hNmem, g, fun z hz w hw => ?_, fun w hw => ⟨?_, ?_⟩⟩
  · have hwz := (mem_iInter₂.mp hw.2) z hz
    obtain ⟨-, hUo, hgd, -⟩ := hVUg z hz
    exact hgd.differentiableAt (hUo.mem_nhds hwz.1)
  · ext z'
    constructor
    · intro hz'
      have hwK : w ∈ K := interior_subset hw.1.1
      have hnC : (w, z') ∉ Cset := fun hC => hw.1.2 ⟨(w, z'), hC, rfl⟩
      have hQ' : (w, z') ∈ ⋃ z ∈ F₀, Q z := by
        by_contra hn
        exact hnC ⟨⟨hz', hwK⟩, hn⟩
      obtain ⟨z, hzF, hzQ⟩ := mem_iUnion₂.mp hQ'
      obtain ⟨-, -, -, hEV⟩ := hVUg z hzF
      have hmem : (w, z') ∈ E ∩ V z := ⟨hz', interior_subset hzQ.1⟩
      rw [hEV] at hmem
      obtain ⟨w', -, hw'⟩ := hmem
      simp only [Prod.mk.injEq] at hw'
      obtain ⟨rfl, hgz⟩ := hw'
      exact ⟨z, hzF, hgz⟩
    · rintro ⟨z, hzF, rfl⟩
      have hwz := (mem_iInter₂.mp hw.2) z hzF
      obtain ⟨-, -, -, hEV⟩ := hVUg z hzF
      have hmem : (w, g z w) ∈ (fun w => (w, g z w)) '' U z := ⟨w, hwz.1, rfl⟩
      rw [← hEV] at hmem
      exact hmem.1
  · intro z₁ hz₁ z₂ hz₂ heq
    by_contra hne
    have h1 := ((mem_iInter₂.mp hw.2) z₁ hz₁).2.2
    have h2 := ((mem_iInter₂.mp hw.2) z₂ hz₂).2.2
    simp only [mem_prod, mem_univ, true_and] at h1 h2
    change g z₁ w = g z₂ w at heq
    rw [heq] at h1
    exact Set.disjoint_left.mp (hdisj hz₁ hz₂ hne) h1 h2

/-- **Constant fibre cardinality**: on the preconnected `B₀` the fibres are finite of constant
cardinality. -/
theorem exists_card_eq (hB₀ : IsOpen B₀) (hB₀c : IsPreconnected B₀)
    (hprop : ∀ K ⊆ B₀, IsCompact K → IsCompact (E ∩ Prod.fst ⁻¹' K))
    (hgraph : ∀ p ∈ E, ∃ V ∈ 𝓝 p, ∃ U : Set (ComplexModel s), IsOpen U ∧
      ∃ g : ComplexModel s → ComplexModel d, DifferentiableOn ℂ g U ∧
        E ∩ V = (fun w => (w, g w)) '' U) :
    ∃ q : ℕ, ∀ w ∈ B₀, (fibreSet E w).Finite ∧ (fibreSet E w).ncard = q := by
  rcases B₀.eq_empty_or_nonempty with h | ⟨w₁, hw₁⟩
  · exact ⟨0, by simp [h]⟩
  have hloc : ∀ w₀ ∈ B₀, ∀ᶠ w in 𝓝 w₀, (fibreSet E w).ncard = (fibreSet E w₀).ncard := by
    intro w₀ hw₀
    obtain ⟨-, N, hN, g, -, hfib⟩ := exists_local_sheets hB₀ hprop hgraph hw₀
    filter_upwards [hN] with w hw
    rw [(hfib w hw).1, (hfib w hw).2.ncard_image]
  have hcont : ContinuousOn (fun w => (fibreSet E w).ncard) B₀ := fun w₀ hw₀ =>
    (continuousAt_const.congr ((hloc w₀ hw₀).mono fun _ h => h.symm)).continuousWithinAt
  exact ⟨(fibreSet E w₁).ncard, fun w hw =>
    ⟨(exists_local_sheets hB₀ hprop hgraph hw).1, hB₀c.constant hcont hw hw₁⟩⟩

/-- **The canonical coefficients are holomorphic** on `B₀`. -/
theorem differentiableOn_coeff_fibrePoly (hB₀ : IsOpen B₀)
    (hprop : ∀ K ⊆ B₀, IsCompact K → IsCompact (E ∩ Prod.fst ⁻¹' K))
    (hgraph : ∀ p ∈ E, ∃ V ∈ 𝓝 p, ∃ U : Set (ComplexModel s), IsOpen U ∧
      ∃ g : ComplexModel s → ComplexModel d, DifferentiableOn ℂ g U ∧
        E ∩ V = (fun w => (w, g w)) '' U)
    (l : ComplexModel d →L[ℂ] ℂ) (j : ℕ) :
    DifferentiableOn ℂ (fun w => (fibrePoly E l w).coeff j) B₀ := by
  classical
  intro w₀ hw₀
  obtain ⟨hfin, N, hN, g, hgd, hfib⟩ := exists_local_sheets hB₀ hprop hgraph hw₀
  have heq : (fun w => (fibrePoly E l w).coeff j) =ᶠ[𝓝 w₀]
      fun w => (∏ z ∈ hfin.toFinset, (X - C (l (g z w)))).coeff j := by
    filter_upwards [hN] with w hw
    have hfinw : (fibreSet E w).Finite := by
      rw [(hfib w hw).1]
      exact hfin.image _
    rw [fibrePoly_eq l hfinw]
    have himg : hfinw.toFinset = hfin.toFinset.image (fun z => g z w) := by
      ext z'
      simp only [Set.Finite.mem_toFinset, Finset.mem_image]
      rw [(hfib w hw).1]
      rfl
    rw [himg, Finset.prod_image fun z₁ hz₁ z₂ hz₂ h =>
      (hfib w hw).2 (by simpa using hz₁) (by simpa using hz₂) h]
  have hd : DifferentiableAt ℂ (fun w => (∏ z ∈ hfin.toFinset, (X - C (l (g z w)))).coeff j) w₀ :=
    differentiableAt_coeff_prod_X_sub_C hfin.toFinset (fun z hz =>
      l.differentiableAt.comp w₀ (hgd z (by simpa using hz) w₀ (mem_of_mem_nhds hN))) j
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- **Bound on the canonical coefficients**: `‖σ_j‖ ≤ (1 + ‖λ‖ R) ^ #E_w`. -/
theorem norm_coeff_fibrePoly_le (hEsub : E ⊆ B₀ ×ˢ ball (0 : ComplexModel d) R) (hR : 0 ≤ R)
    (l : ComplexModel d →L[ℂ] ℂ) {w : ComplexModel s} (hfin : (fibreSet E w).Finite) (j : ℕ) :
    ‖(fibrePoly E l w).coeff j‖ ≤ (1 + ‖l‖ * R) ^ (fibreSet E w).ncard := by
  rw [fibrePoly_eq l hfin, Set.ncard_eq_toFinset_card _ hfin]
  refine norm_coeff_prod_X_sub_C_le _ (by positivity) (fun z hz => ?_) j
  have hzE : (w, z) ∈ E := by simpa [fibreSet] using hz
  have hzb : ‖z‖ < R := by simpa using (hEsub hzE).2
  calc ‖l z‖ ≤ ‖l‖ * ‖z‖ := l.le_opNorm z
    _ ≤ ‖l‖ * R := mul_le_mul_of_nonneg_left hzb.le (norm_nonneg _)

/-- **The canonical defining functions cut out `E`**: with the `q d + 1` Vandermonde forms
`λ_i`, `(w, z) ∈ E` iff `P_{λ_i}(w; λ_i z) = 0` for all `i`, at every `w ∈ B₀`. -/
theorem exists_forms_mem_iff {q : ℕ}
    (hq : ∀ w ∈ B₀, (fibreSet E w).Finite ∧ (fibreSet E w).ncard = q) {w : ComplexModel s}
    (hw : w ∈ B₀) (z : ComplexModel d) :
    (w, z) ∈ E ↔ ∀ i ∈ Finset.range (q * d + 1),
      (fibrePoly E (form d 0 i) w).eval (form d 0 i z) = 0 := by
  classical
  obtain ⟨hfin, hcard⟩ := hq w hw
  simp_rw [fibrePoly_eq _ hfin, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
    sub_eq_zero]
  constructor
  · intro hz i _
    exact ⟨z, by simpa [fibreSet] using hz, rfl⟩
  · intro h
    choose! f hf hfeq using h
    have hn : hfin.toFinset.card * d < (Finset.range (q * d + 1)).card := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, hcard, Finset.card_range]
      omega
    obtain ⟨y, hy, hlt⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    have hzy : z - y = 0 := by
      refine eq_zero_of_form_eq_zero (n := d) (d := 0) (I := (Finset.range (q * d + 1)).filter
        fun i => f i = y) (by omega) (Subsingleton.elim _ _) fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [map_sub, hfeq i hi.1, hi.2, sub_self]
    rw [sub_eq_zero.mp hzy]
    simpa [fibreSet] using hy

end Hironaka.CoveringSymmetricFunctions
