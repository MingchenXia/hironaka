/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaPolynomialCase
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.GermCoordinateTower
import Hironaka.Analytic.HolomorphicGermRing
import Hironaka.Coherence.OkaGermBridge
import Hironaka.Coherence.OkaRelationSheaf
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Oka's coherence theorem

Source: K. Oka, *Sur les fonctions analytiques de plusieurs variables VII* (1950); Grauert--
Remmert, *Coherent analytic sheaves*, Ch. 2 §5 ("Oka's coherence theorem"); Demailly, *Complex
analytic and differential geometry*, II.3.19--3.20; Gunning--Rossi, IV.C.

**Oka's coherence theorem** (`okaProperty_euclidean`): on `ℂⁿ`, the sheaf of relations of
finitely many holomorphic maps `F_j : ℂⁿ → ℂ^p` is locally finitely generated: near every point
`x₀` there are finitely many holomorphic relations on an open `U ∋ x₀` that generate the
relations at EVERY point of `U` (`OkaRelationSheaf.OkaProperty`).

## Proof (induction on `n`)

* `n = 0` (`okaProperty_of_subsingleton`): a row of constants either vanishes (unit vectors
  generate) or has a nonzero entry (trivial relations generate).
* `n → n + 1` (`okaProperty_prod`), one equation at a time (`okaProperty_of_scalar`), at the
  origin after translation.  If every `g_j` vanishes near `0`, unit vectors generate.  Otherwise
  some `g_{j₀}` is a nonzero germ; after a linear change of coordinates
  (`HolGerm.exists_mul_comapEquiv_eq_prodWeierstrassGerm`) a unit `u` makes `u g_{j₀} = W` a
  Weierstrass polynomial in the last variable, and Weierstrass division gives
  `g_j = Q_j W + R_j` with `R_j` polynomial in `t` of degree `< deg W`.  The invertible matrix
  `A` (row `j₀` = `(u⁻¹, Q_j)`, identity elsewhere) satisfies `g = G A` with `G_{j₀} = W`,
  `G_j = R_j`, so the relations of `g` are those of `G` transported by `A`
  (`RelationsFGAt.of_matrix`), and `G` is a Weierstrass system
  (`OkaPolynomialCase.relationsFGAt_polySystem`, which uses Oka for `ℂⁿ`).
-/

open Filter Topology Set

namespace Hironaka.OkaCoherence

open HolGerm OkaRelationSheaf OkaGermBridge OkaPolynomialCase

noncomputable section

/-! ### The elementary matrix -/

theorem sum_mul_elem {ι : Type*} [Fintype ι] [DecidableEq ι] (v α : ι → ℂ) (j₀ j : ι) :
    ∑ k, v k * (if k = j₀ then α j else if k = j then 1 else 0) =
      v j₀ * α j + if j = j₀ then 0 else v j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_univ,
    and_true]
  by_cases h : j = j₀ <;> simp [h]

/-! ### Base case -/

/-- **Oka's property in dimension `0`.** -/
theorem okaProperty_of_subsingleton {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Subsingleton X] : OkaProperty X := by
  refine okaProperty_of_scalar fun ι _ f x₀ hf => ?_
  classical
  have hdiff : ∀ j, DifferentiableOn ℂ (f j) univ := fun j x _ => by
    rw [Subsingleton.elim x x₀]
    exact (hf j).differentiableAt.differentiableWithinAt
  by_cases h : ∀ j, f j x₀ = 0
  · exact relationsFGAt_of_eqOn_zero isOpen_univ (mem_univ x₀)
      (fun _ j x _ => by rw [Subsingleton.elim x x₀]; exact h j) (Equiv.refl ι)
  · obtain ⟨j₀, hj₀⟩ := not_forall.1 h
    exact relationsFGAt_of_ne_zero isOpen_univ (mem_univ x₀) hdiff j₀
      (fun x _ => by rw [Subsingleton.elim x x₀]; exact hj₀) (Equiv.refl ι)

/-! ### The induction step -/

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The linear change of coordinates as a biholomorphic homeomorphism. -/
theorem differentiableAt_continuousLinearEquiv {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (L : X ≃L[ℂ] Y) (x : X) :
    DifferentiableAt ℂ (L.toHomeomorph : X → Y) x :=
  (L : X →L[ℂ] Y).differentiableAt

theorem differentiableAt_continuousLinearEquiv_symm {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (L : X ≃L[ℂ] Y) (y : Y) :
    DifferentiableAt ℂ (L.toHomeomorph.symm : Y → X) y :=
  (L.symm : Y →L[ℂ] X).differentiableAt

/-- **The induction step at the origin, after the change of coordinates**: if `u h_{j₀}` is a
Weierstrass polynomial `W` (germs at `0`, `u` a unit), the relations of `h` are finitely
generated near `0`. -/
theorem relationsFGAt_of_weierstrass (hE : OkaProperty E) {ι : Type} [Fintype ι] [DecidableEq ι]
    (h : ι → E × ℂ → ℂ) (hh : ∀ j, HolAt (h j) 0) (j₀ : ι) {d : ℕ} {A : ℕ → HolGerm E}
    (hA : ∀ k < d, HolGerm.eval (A k) = 0) {u : HolGerm (E × ℂ)} (hu : IsUnit u)
    (hW : u * mk (h j₀) (hh j₀) = prodWeierstrassGerm d A) :
    RelationsFGAt (fun (_ : Unit) => h) (0 : E × ℂ) := by
  -- representatives
  choose w hw hwA using fun k => exists_eq_mk (A k)
  obtain rfl : A = fun k => mk (w k) (hw k) := funext hwA
  obtain ⟨uf, huf, rfl⟩ := exists_eq_mk u
  have huf0 : uf 0 ≠ 0 := by
    have := (isUnit_iff_eval_ne_zero _).1 hu
    rwa [eval_mk] at this
  set W : E × ℂ → ℂ := fun x => x.2 ^ d + ∑ k ∈ Finset.range d, w k x.1 * x.2 ^ k with hWdef
  have hWu : (fun x => uf x * h j₀ x) =ᶠ[𝓝 0] W := by
    rw [prodWeierstrassGerm_eq_mk, ← mk_mul] at hW
    exact (mk_eq_mk_iff).1 hW
  -- Weierstrass division of every `h j`
  have hdiv := fun j => exists_eq_mul_prodWeierstrassGerm_add hA (mk (h j) (hh j))
  choose Q r hQr using hdiv
  choose Qf hQf hQQf using fun j => exists_eq_mk (Q j)
  choose rf hrf hrrf using fun j k => exists_eq_mk (r j k)
  have hdivf : ∀ j, h j =ᶠ[𝓝 0]
      fun x => Qf j x * W x + ∑ k ∈ Finset.range d, rf j k x.1 * x.2 ^ k := by
    intro j
    have e := hQr j
    simp only [hrrf] at e
    rw [hQQf j, prodWeierstrassGerm_eq_mk, sum_ofFst_mul_lastCoord_pow_eq_mk, ← mk_mul,
      ← mk_add] at e
    exact (mk_eq_mk_iff).1 e
  -- the Weierstrass system `G`
  set γ : ι → ℕ → E → ℂ := fun j l =>
    if j = j₀ then (if l < d then w l else if l = d then fun _ => 1 else fun _ => 0)
    else (if l < d then rf j l else fun _ => 0) with hγdef
  have hγhol : ∀ j l, HolAt (γ j l) 0 := by
    intro j l
    simp only [hγdef]
    split_ifs
    · exact hw l
    · exact holAt_const 1 0
    · exact holAt_const 0 0
    · exact hrf j l
    · exact holAt_const 0 0
  have hGj₀ : ∀ x, polySystem γ d j₀ x = W x := by
    intro x
    rw [polySystem, Finset.sum_range_succ, hWdef]
    have h1 : ∀ l ∈ Finset.range d, γ j₀ l x.1 * x.2 ^ l = w l x.1 * x.2 ^ l := fun l hl => by
      simp only [hγdef, if_pos rfl, if_pos (Finset.mem_range.1 hl)]
    have h2 : γ j₀ d x.1 = 1 := by simp [hγdef]
    rw [Finset.sum_congr rfl h1, h2, one_mul, add_comm]
  have hGj : ∀ j, j ≠ j₀ → ∀ x, polySystem γ d j x = ∑ k ∈ Finset.range d, rf j k x.1 * x.2 ^ k := by
    intro j hj x
    rw [polySystem, Finset.sum_range_succ]
    have h1 : ∀ l ∈ Finset.range d, γ j l x.1 * x.2 ^ l = rf j l x.1 * x.2 ^ l := fun l hl => by
      simp only [hγdef, if_neg hj, if_pos (Finset.mem_range.1 hl)]
    have h2 : γ j d x.1 = 0 := by simp [hγdef, hj]
    rw [Finset.sum_congr rfl h1, h2, zero_mul, add_zero]
  have hG : RelationsFGAt (fun (_ : Unit) => polySystem γ d) (0 : E × ℂ) :=
    relationsFGAt_polySystem hE γ le_rfl j₀ hγhol
      (fun z => by simp [hγdef])
      (fun l hl z => by
        simp [hγdef, show ¬ l < d by omega, show l ≠ d by omega])
  -- an open set where everything holds
  have hev : ∀ᶠ x in 𝓝 (0 : E × ℂ), uf x ≠ 0 ∧ DifferentiableAt ℂ uf x ∧ uf x * h j₀ x = W x ∧
      ∀ j, (DifferentiableAt ℂ (Qf j) x ∧
        h j x = Qf j x * W x + ∑ k ∈ Finset.range d, rf j k x.1 * x.2 ^ k) :=
    (huf.self_of_nhds.continuousAt.eventually_ne huf0).and (huf.and (hWu.and
      (eventually_all.2 fun j => (hQf j).and (hdivf j))))
  obtain ⟨U, hUev, hU, h0U⟩ := eventually_nhds_iff.1 hev
  have hUuf : DifferentiableOn ℂ uf U := fun x hx => (hUev x hx).2.1.differentiableWithinAt
  have hUQ : ∀ j, DifferentiableOn ℂ (Qf j) U := fun j x hx =>
    ((hUev x hx).2.2.2 j).1.differentiableWithinAt
  have hUne : ∀ x ∈ U, uf x ≠ 0 := fun x hx => (hUev x hx).1
  -- the matrix `A` and its inverse `B`
  set α : ι → E × ℂ → ℂ := fun j x => if j = j₀ then (uf x)⁻¹ else Qf j x with hαdef
  set β : ι → E × ℂ → ℂ := fun j x => if j = j₀ then uf x else -(uf x * Qf j x) with hβdef
  set Am : ι → ι → E × ℂ → ℂ := fun k j x => if k = j₀ then α j x else if k = j then 1 else 0
  set Bm : ι → ι → E × ℂ → ℂ := fun k j x => if k = j₀ then β j x else if k = j then 1 else 0
  have hαd : ∀ j, DifferentiableOn ℂ (α j) U := fun j => by
    simp only [hαdef]
    split_ifs
    · exact hUuf.inv hUne
    · exact hUQ j
  have hβd : ∀ j, DifferentiableOn ℂ (β j) U := fun j => by
    simp only [hβdef]
    split_ifs
    · exact hUuf
    · exact (hUuf.mul (hUQ j)).neg
  refine RelationsFGAt.of_matrix (G := fun (_ : Unit) => polySystem γ d) hU h0U Am Bm
    (fun k j => ?_) (fun k j => ?_) (fun _ j x hx => ?_) (fun j l x hx => ?_)
    (fun j l x hx => ?_) hG
  · simp only [Am]
    split_ifs
    · exact hαd j
    · exact differentiableOn_const _
    · exact differentiableOn_const _
  · simp only [Bm]
    split_ifs
    · exact hβd j
    · exact differentiableOn_const _
    · exact differentiableOn_const _
  · -- `h = G A`
    obtain ⟨hne, -, hWx, hdx⟩ := hUev x hx
    rw [sum_mul_elem (fun k => polySystem γ d k x) (fun j => α j x) j₀ j, hGj₀]
    by_cases hj : j = j₀
    · rw [if_pos hj, add_zero, hj]
      simp only [hαdef, if_pos rfl]
      rw [← hWx]
      field_simp
    · rw [if_neg hj, hGj j hj]
      simp only [hαdef, if_neg hj]
      rw [(hdx j).2]
      ring
  · -- `B A = 1`
    have hne := hUne x hx
    rw [sum_mul_elem (fun k => Bm j k x) (fun l => α l x) j₀ l]
    by_cases hj : j = j₀
    · subst hj
      by_cases hl : l = j
      · subst hl
        simp [Bm, hαdef, hβdef, hne]
      · simp [Bm, hαdef, hβdef, hl, Ne.symm hl]
    · by_cases hl : l = j₀
      · subst hl
        simp [Bm, hj]
      · simp [Bm, hj, hl]
  · -- `A B = 1`
    have hne := hUne x hx
    rw [sum_mul_elem (fun k => Am j k x) (fun l => β l x) j₀ l]
    by_cases hj : j = j₀
    · subst hj
      by_cases hl : l = j
      · subst hl
        simp [Am, hαdef, hβdef, hne]
      · simp [Am, hαdef, hβdef, hl, Ne.symm hl]
        field_simp
        ring
    · by_cases hl : l = j₀
      · subst hl
        simp [Am, hj]
      · simp [Am, hj, hl]

/-- **The induction step at the origin.** -/
theorem relationsFGAt_zero (hE : OkaProperty E) {ι : Type} [Fintype ι] (g : ι → E × ℂ → ℂ)
    (hg : ∀ j, HolAt (g j) 0) : RelationsFGAt (fun (_ : Unit) => g) (0 : E × ℂ) := by
  classical
  by_cases hzero : ∀ j, g j =ᶠ[𝓝 0] fun _ => 0
  · obtain ⟨U, hUev, hU, h0U⟩ := eventually_nhds_iff.1 (eventually_all.2 hzero)
    exact relationsFGAt_of_eqOn_zero hU h0U (fun _ j x hx => hUev x hx j) (Equiv.refl ι)
  obtain ⟨j₀, hj₀⟩ := not_forall.1 hzero
  have hne : mk (g j₀) (hg j₀) ≠ 0 := fun h0 =>
    hj₀ ((mk_eq_mk_iff (g := fun _ => (0 : ℂ)) (hg := eventually_differentiableAt_zero)).1
      (h0.trans mk_zero.symm))
  obtain ⟨L, u, d, A, hu, hA, hW⟩ := exists_mul_comapEquiv_eq_prodWeierstrassGerm hne
  rw [comapEquiv_mk] at hW
  set h : ι → E × ℂ → ℂ := fun j => g j ∘ L with hhdef
  have hh : ∀ j, HolAt (h j) 0 := fun j =>
    eventually_differentiableAt_comp_clm (L : (E × ℂ) →L[ℂ] E × ℂ) (hg j)
  have hH := relationsFGAt_of_weierstrass hE h hh j₀ hA hu hW
  have hφ0 : L.symm.toHomeomorph 0 = 0 := map_zero L.symm
  rw [← hφ0] at hH
  have := hH.comp_homeomorph L.symm.toHomeomorph
    (differentiableAt_continuousLinearEquiv L.symm)
    (differentiableAt_continuousLinearEquiv_symm L.symm)
  convert this using 2 with i
  funext j x
  simp [hhdef]

/-- **The induction step at every point**: translate to the origin. -/
theorem relationsFGAt_prod (hE : OkaProperty E) {ι : Type} [Fintype ι] (g : ι → E × ℂ → ℂ)
    (x₀ : E × ℂ) (hg : ∀ j, HolAt (g j) x₀) : RelationsFGAt (fun (_ : Unit) => g) x₀ := by
  have hG : ∀ j, HolAt (fun x => g j (x₀ + x)) 0 := fun j => (hg j).translate
  have h0 := relationsFGAt_zero hE (fun j x => g j (x₀ + x)) hG
  have hφ : (Homeomorph.subRight x₀) x₀ = 0 := sub_self x₀
  rw [← hφ] at h0
  have := h0.comp_homeomorph (Homeomorph.subRight x₀)
    (fun x => differentiableAt_id.sub (differentiableAt_const x₀))
    (fun x => differentiableAt_id.add (differentiableAt_const x₀))
  convert this using 2 with i
  funext j x
  simp

/-- **Oka's property passes from `E` to `E × ℂ`.** -/
theorem okaProperty_prod (hE : OkaProperty E) : OkaProperty (E × ℂ) :=
  okaProperty_of_scalar fun _ _ g x₀ hg => relationsFGAt_prod hE g x₀ hg

end Step

/-- **Oka's coherence theorem.**  On `ℂⁿ`, the relation sheaf of any finite matrix of functions
holomorphic near a point `x₀` is finitely generated near `x₀`: finitely many holomorphic
relations on an open `U ∋ x₀` generate the relations at every point of `U`. -/
theorem okaProperty_euclidean (n : ℕ) : OkaProperty (EuclideanSpace ℂ (Fin n)) := by
  induction n with
  | zero =>
      have : Subsingleton (EuclideanSpace ℂ (Fin 0)) :=
        ⟨fun x y => by ext i; exact i.elim0⟩
      exact okaProperty_of_subsingleton
  | succ n ih =>
      exact (okaProperty_prod ih).of_homeomorph (euclideanSnocCLE n).toHomeomorph
        (differentiableAt_continuousLinearEquiv _) (differentiableAt_continuousLinearEquiv_symm _)

end

end Hironaka.OkaCoherence
