/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.CohomologyP1
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The standard charts of `ℙ¹_k = Proj k[X₀, X₁]`

The projective line `ℙ¹_k = Proj k[X₀, X₁]` has `ℙ¹`-charts (`P1Charts`): the basic opens
`U = D₊(X₀)` and `V = D₊(X₁)` with `Γ(U, 𝒪) = k[X₁/X₀]`, `Γ(V, 𝒪) = k[X₀/X₁]` and
`Γ(U ∩ V, 𝒪) = k[X₁/X₀, X₀/X₁]` (`projectiveLineCharts`). Hence the cohomology of `𝒪(n)` on
`ℙ¹_k` is `h⁰ = max(n + 1, 0)`, `h¹ = max(-n - 1, 0)`
(`finrank_cohomology_zero_twist_projectiveLine`, `finrank_cohomology_one_twist_projectiveLine`;
in particular `finrank_cohomology_zero_projectiveLine`: `h⁰(𝒪) = 1`, and
`isZero_cohomology_one_projectiveLine`: `H¹(𝒪) = 0`; blueprint `sm-curves-fields-cohomology.tex`,
`lem:sm-p1-cohomology`). `ℙ¹_k` is quasi-compact (two affine charts) and separated (Mathlib), so
the cover-free cohomology `cohomology F c p` applies.

The algebra: for `i ≠ j` the homogeneous localization `k[X₀, X₁]_{(Xᵢ)}` is the polynomial ring in
`Xⱼ/Xᵢ` (`awayEquiv`): the map `k[X] → k[X₀, X₁]_{(Xᵢ)}`, `X ↦ Xⱼ/Xᵢ`, is injective because
`Xᵢ ↦ 1, Xⱼ ↦ X` gives a left inverse on `k[X₀, X₁][Xᵢ⁻¹]`, and surjective because a homogeneous
`a` of degree `n` satisfies `a / Xᵢⁿ = a(1, Xⱼ/Xᵢ)` (dehomogenization). The localization
`k[X₀, X₁]_{(X₀X₁)}` is `k[X₀, X₁]_{(X₀)}[(X₁/X₀)⁻¹]` (Mathlib's `Away.isLocalization_mul`),
hence `k[T, T⁻¹]`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace MvPolynomial
open HomogeneousLocalization
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

namespace ProjectiveLine

variable (k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The grading of `k[X₀, X₁]` by degree. -/
abbrev grading : ℕ → Submodule k (MvPolynomial (Fin 2) k) := homogeneousSubmodule (Fin 2) k

lemma X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) k) ∈ grading k 1 := isHomogeneous_X k i

/-- The constants of a homogeneous localization. -/
def cst (f : MvPolynomial (Fin 2) k) : k →+* Away (grading k) f :=
  (fromZeroRingHom (grading k) _).comp (algebraMap k (grading k 0))

/-- The fraction `Xⱼ / Xᵢ`. -/
def frac (i j : Fin 2) : Away (grading k) (X i) := Away.isLocalizationElem (X_mem k i) (X_mem k j)

/-- The map `k[X] → k[X₀, X₁]_{(Xᵢ)}`, `X ↦ Xⱼ/Xᵢ`. -/
def ψ (i j : Fin 2) : Polynomial k →+* Away (grading k) (X i) :=
  Polynomial.eval₂RingHom (cst k (X i)) (frac k i j)

/-- The dehomogenization `Xᵢ ↦ 1`, `Xⱼ ↦ X` on `k[X₀, X₁][Xᵢ⁻¹]`. -/
def ev (i : Fin 2) : Localization.Away (X i : MvPolynomial (Fin 2) k) →+* Polynomial k :=
  IsLocalization.Away.lift (X i) (g := MvPolynomial.eval₂Hom Polynomial.C
    (fun l => if l = i then 1 else Polynomial.X)) (by simp)

lemma val_cst (f : MvPolynomial (Fin 2) k) (a : k) :
    (cst k f a).val = algebraMap (MvPolynomial (Fin 2) k) (Localization (Submonoid.powers f))
      (MvPolynomial.C a) := by
  change Localization.mk _ 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

lemma ev_algebraMap (i : Fin 2) (a : MvPolynomial (Fin 2) k) :
    ev k i (algebraMap _ (Localization.Away (X i)) a) =
      MvPolynomial.eval₂Hom Polynomial.C (fun l => if l = i then 1 else Polynomial.X) a := by
  rw [ev, IsLocalization.Away.lift, IsLocalization.lift_eq]

lemma frac_val_mul (i j : Fin 2) :
    (frac k i j).val * algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X i : MvPolynomial (Fin 2) k)) (X i) =
      algebraMap (MvPolynomial (Fin 2) k) (Localization.Away (X i : MvPolynomial (Fin 2) k))
        (X j) := by
  rw [frac, Away.isLocalizationElem, Away.val_mk, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

lemma ev_comp (i j : Fin 2) (hij : i ≠ j) :
    (ev k i).comp ((algebraMap (Away (grading k) (X i)) (Localization.Away (X i))).comp
      (ψ k i j)) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      RingHom.id_apply]
    change ev k i (cst k (X i) a).val = _
    rw [val_cst, ev_algebraMap]
    simp
  · simp only [RingHom.comp_apply, ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      RingHom.id_apply]
    change ev k i (frac k i j).val = _
    have h := congrArg (ev k i) (frac_val_mul k i j)
    rw [map_mul, ev_algebraMap, ev_algebraMap] at h
    simpa [hij.symm] using h

lemma ψ_injective (i j : Fin 2) (hij : i ≠ j) : Function.Injective (ψ k i j) := by
  intro p q h
  have e := RingHom.congr_fun (ev_comp k i j hij)
  have hp := e p
  have hq := e q
  simp only [RingHom.comp_apply, RingHom.id_apply] at hp hq
  rw [← hp, ← hq, h]

/-- The dehomogenization `Xᵢ ↦ 1`, `Xⱼ ↦ X`. -/
abbrev dehom (i : Fin 2) : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun l => if l = i then 1 else Polynomial.X)

/-- `θ = val ∘ ψ ∘ dehom : k[X₀, X₁] → k[X₀, X₁][Xᵢ⁻¹]`, sending `Xᵢ ↦ 1`, `Xⱼ ↦ Xⱼ/Xᵢ`. -/
abbrev θ (i j : Fin 2) :
    MvPolynomial (Fin 2) k →+* Localization.Away (X i : MvPolynomial (Fin 2) k) :=
  (algebraMap (Away (grading k) (X i)) (Localization.Away (X i : MvPolynomial (Fin 2) k))).comp
    ((ψ k i j).comp (dehom k i))

lemma θ_C (i j : Fin 2) (c : k) :
    θ k i j (MvPolynomial.C c) = algebraMap (MvPolynomial (Fin 2) k)
      (Localization.Away (X i : MvPolynomial (Fin 2) k)) (MvPolynomial.C c) := by
  simp only [θ, RingHom.comp_apply, dehom, eval₂Hom_C, ψ, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C]
  exact val_cst k _ c

lemma θ_X_self (i j : Fin 2) : θ k i j (X i) = 1 := by
  simp [θ, dehom]

lemma θ_X_other (i j : Fin 2) (hij : i ≠ j) : θ k i j (X j) = (frac k i j).val := by
  simp only [θ, RingHom.comp_apply, dehom, eval₂Hom_X', if_neg hij.symm, ψ,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

lemma degree_two {a : MvPolynomial (Fin 2) k} {n : ℕ} (ha : a.IsHomogeneous n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ a.support) : d 0 + d 1 = n := by
  have := ha (mem_support_iff.mp hd)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this

lemma monomial_two (d : Fin 2 →₀ ℕ) (c : k) :
    monomial d c = MvPolynomial.C c * (X 0 ^ d 0 * X 1 ^ d 1) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

/-- **Dehomogenization**: `θ(a) · Xᵢⁿ = a` for `a` homogeneous of degree `n`. -/
lemma θ_mul_pow (i j : Fin 2) (hij : i ≠ j) {n : ℕ} {a : MvPolynomial (Fin 2) k}
    (ha : a.IsHomogeneous n) :
    θ k i j a * algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X i : MvPolynomial (Fin 2) k)) (X i) ^ n =
      algebraMap (MvPolynomial (Fin 2) k) (Localization.Away (X i : MvPolynomial (Fin 2) k)) a := by
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := degree_two k ha hd
  have hτ := frac_val_mul k i j
  rw [monomial_two, map_mul, θ_C]
  simp only [map_mul, map_pow]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · simp only [Fin.zero_eta, Fin.mk_one, θ_X_self, one_pow] at hτ ⊢
    rw [θ_X_other k 0 1 hij, ← hτ, ← hdeg, pow_add, mul_pow]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, θ_X_self, one_pow] at hτ ⊢
    rw [θ_X_other k 1 0 hij, ← hτ, ← hdeg, pow_add, mul_pow]
    ring
  · exact absurd rfl hij

lemma ψ_surjective (i j : Fin 2) (hij : i ≠ j) : Function.Surjective (ψ k i j) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading k) (X_mem k i) z
  refine ⟨dehom k i a, ?_⟩
  apply val_injective
  rw [Away.val_mk]
  have hhom : a.IsHomogeneous n := by simpa using ha
  have key := θ_mul_pow k i j hij hhom
  change θ k i j a = _
  rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simpa using key

/-- **`k[X₀, X₁]_{(Xᵢ)} ≅ k[Xⱼ/Xᵢ]`**. -/
def awayEquiv (i j : Fin 2) (hij : i ≠ j) : Polynomial k ≃+* Away (grading k) (X i) :=
  RingEquiv.ofBijective (ψ k i j) ⟨ψ_injective k i j hij, ψ_surjective k i j hij⟩

lemma awayEquiv_apply (i j : Fin 2) (hij : i ≠ j) (p : Polynomial k) :
    awayEquiv k i j hij p = ψ k i j p :=
  rfl

lemma ψ_X (i j : Fin 2) : ψ k i j Polynomial.X = frac k i j := by
  simp [ψ]

lemma ψ_C (i j : Fin 2) (a : k) : ψ k i j (Polynomial.C a) = cst k (X i) a := by
  simp [ψ]

/-! ### The intersection `D₊(X₀X₁)` -/

/-- Restriction `k[X₀, X₁]_{(X₀)} → k[X₀, X₁]_{(X₀X₁)}`. -/
abbrev mapUV : Away (grading k) (X 0) →+* Away (grading k) (X 0 * X 1) :=
  awayMap (grading k) (X_mem k 1) rfl

/-- Restriction `k[X₀, X₁]_{(X₁)} → k[X₀, X₁]_{(X₀X₁)}`. -/
abbrev mapVU : Away (grading k) (X 1) →+* Away (grading k) (X 0 * X 1) :=
  awayMap (grading k) (X_mem k 0) (mul_comm _ _)

lemma powers_map :
    Submonoid.map (awayEquiv k 0 1 (by decide)).toMonoidHom (Submonoid.powers Polynomial.X) =
      Submonoid.powers (frac k 0 1) := by
  rw [Submonoid.map_powers]
  congr 1
  exact ψ_X k 0 1

/-- **`k[X₀, X₁]_{(X₀X₁)} ≅ k[T, T⁻¹]`**, `T ↦ X₁/X₀`. -/
def awayUVEquiv : LaurentPolynomial k ≃+* Away (grading k) (X 0 * X 1) :=
  letI := (mapUV k).toAlgebra
  haveI : IsLocalization (Submonoid.powers (frac k 0 1)) (Away (grading k) (X 0 * X 1)) :=
    Away.isLocalization_mul (X_mem k 0) (X_mem k 1) rfl one_ne_zero
  IsLocalization.ringEquivOfRingEquiv (LaurentPolynomial k) (Away (grading k) (X 0 * X 1))
    (awayEquiv k 0 1 (by decide)) (powers_map k)

lemma awayUVEquiv_toLaurent (p : Polynomial k) :
    awayUVEquiv k (Polynomial.toLaurent p) = mapUV k (ψ k 0 1 p) := by
  let := (mapUV k).toAlgebra
  have : IsLocalization (Submonoid.powers (frac k 0 1)) (Away (grading k) (X 0 * X 1)) :=
    Away.isLocalization_mul (X_mem k 0) (X_mem k 1) rfl one_ne_zero
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq (powers_map k) p

lemma mapUV_mul_mapVU : mapUV k (frac k 0 1) * mapVU k (frac k 1 0) = 1 := by
  apply val_injective
  simp only [frac, Away.isLocalizationElem, awayMap_mk, val_mul, Away.val_mk, val_one,
    Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

lemma awayUVEquiv_invert (p : Polynomial k) :
    awayUVEquiv k (LaurentPolynomial.invert (Polynomial.toLaurent p)) = mapVU k (ψ k 1 0 p) := by
  have h₁ : ∀ q, awayUVEquiv k (LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      ((awayUVEquiv k).toRingHom.comp
        ((LaurentPolynomial.invert (R := k)).toRingEquiv.toRingHom.comp
          Polynomial.toLaurent)) q := fun _ => rfl
  have h₂ : ∀ q, mapVU k (ψ k 1 0 q) = ((mapVU k).comp (ψ k 1 0)) q := fun _ => rfl
  rw [h₁, h₂]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Polynomial.toLaurent_C, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      LaurentPolynomial.invert_C, ψ_C]
    rw [← Polynomial.toLaurent_C, awayUVEquiv_toLaurent, ψ_C]
    simp only [cst, RingHom.comp_apply, awayMap_fromZeroRingHom]
  · simp only [RingHom.comp_apply, Polynomial.toLaurent_X, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      LaurentPolynomial.invert_T, ψ_X]
    have hT : awayUVEquiv k (LaurentPolynomial.T 1) = mapUV k (frac k 0 1) := by
      rw [← Polynomial.toLaurent_X, awayUVEquiv_toLaurent, ψ_X]
    have hinv : awayUVEquiv k (LaurentPolynomial.T (-1)) * awayUVEquiv k (LaurentPolynomial.T 1) =
        1 := by
      rw [← map_mul, ← LaurentPolynomial.T_add, show (-1 : ℤ) + 1 = 0 by norm_num,
        LaurentPolynomial.T_zero, map_one]
    rw [hT] at hinv
    have h := mapUV_mul_mapVU k
    calc awayUVEquiv k (LaurentPolynomial.T (-1))
        = awayUVEquiv k (LaurentPolynomial.T (-1)) *
            (mapUV k (frac k 0 1) * mapVU k (frac k 1 0)) := by
          rw [h, mul_one]
      _ = mapVU k (frac k 1 0) := by rw [← mul_assoc, hinv, one_mul]

/-! ### Sections of `ℙ¹_k = Proj k[X₀, X₁]` over the charts -/

/-- The projective line `ℙ¹_k = Proj k[X₀, X₁]`. -/
abbrev projectiveLine : Scheme.{u} := Proj (grading k)

/-- The chart `D₊(X₀)`. -/
abbrev chartU : (projectiveLine k).Opens := Proj.basicOpen (grading k) (X 0)

/-- The chart `D₊(X₁)`. -/
abbrev chartV : (projectiveLine k).Opens := Proj.basicOpen (grading k) (X 1)

lemma X01_mem : (X 0 * X 1 : MvPolynomial (Fin 2) k) ∈ grading k 2 :=
  SetLike.mul_mem_graded (X_mem k 0) (X_mem k 1)

lemma chart_inf : chartU k ⊓ chartV k = Proj.basicOpen (grading k) (X 0 * X 1) :=
  (Proj.basicOpen_mul _ _ _).symm

/-- The irrelevant ideal of `k[X₀, X₁]` is generated by the coordinates (the argument of Codex's
`ProperSteinProjectiveCech.homogeneousPolynomial_irrelevant_le_coordinates`). -/
lemma irrelevant_le_span :
    (HomogeneousIdeal.irrelevant (grading k)).toIdeal ≤
      Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) := by
  classical
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn p hp
  have hp' : p.IsHomogeneous n := hp
  change p ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  have hdn : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp' (MvPolynomial.mem_support_iff.mp hd)
  by_contra! h
  have hz : d = 0 := by
    ext i
    exact h i (Set.mem_univ i)
  rw [hz] at hdn
  change 0 = n at hdn
  omega

lemma chart_sup : chartU k ⊔ chartV k = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (grading k) (X : Fin 2 → MvPolynomial (Fin 2) k)
    (irrelevant_le_span k)
  rw [← h]
  apply le_antisymm
  · exact sup_le (le_iSup (fun i => Proj.basicOpen (grading k) (X i)) 0)
      (le_iSup (fun i => Proj.basicOpen (grading k) (X i)) 1)
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right

/-- `Γ(D₊(X₀), 𝒪) ≅ k[X₁/X₀]`. -/
def secU : Polynomial k ≃+* Γ(projectiveLine k, chartU k) :=
  (awayEquiv k 0 1 (by decide)).trans
    (Proj.basicOpenIsoAway (grading k) (X 0) (X_mem k 0) one_pos).commRingCatIsoToRingEquiv

/-- `Γ(D₊(X₁), 𝒪) ≅ k[X₀/X₁]`. -/
def secV : Polynomial k ≃+* Γ(projectiveLine k, chartV k) :=
  (awayEquiv k 1 0 (by decide)).trans
    (Proj.basicOpenIsoAway (grading k) (X 1) (X_mem k 1) one_pos).commRingCatIsoToRingEquiv

/-- `Γ(D₊(X₀X₁), 𝒪) ≅ k[T, T⁻¹]`. -/
def secW' : LaurentPolynomial k ≃+* Γ(projectiveLine k, Proj.basicOpen (grading k) (X 0 * X 1)) :=
  (awayUVEquiv k).trans
    (Proj.basicOpenIsoAway (grading k) (X 0 * X 1) (X01_mem k) two_pos).commRingCatIsoToRingEquiv

/-- Sections over `D₊(X₀X₁)` are sections over `D₊(X₀) ∩ D₊(X₁)`. -/
def eqSec : Γ(projectiveLine k, Proj.basicOpen (grading k) (X 0 * X 1)) ≃+*
    Γ(projectiveLine k, chartU k ⊓ chartV k) :=
  RingEquiv.ofRingHom ((projectiveLine k).presheaf.map (homOfLE (chart_inf k).le).op).hom
    ((projectiveLine k).presheaf.map (homOfLE (chart_inf k).ge).op).hom
    (by rw [← CommRingCat.hom_comp, ← Functor.map_comp]; exact
      congrArg CommRingCat.Hom.hom ((projectiveLine k).presheaf.map_id _))
    (by rw [← CommRingCat.hom_comp, ← Functor.map_comp]; exact
      congrArg CommRingCat.Hom.hom ((projectiveLine k).presheaf.map_id _))

/-- `Γ(D₊(X₀) ∩ D₊(X₁), 𝒪) ≅ k[T, T⁻¹]`. -/
def secW : LaurentPolynomial k ≃+* Γ(projectiveLine k, chartU k ⊓ chartV k) :=
  (secW' k).trans (eqSec k)

lemma presheaf_map_map' {W₁ W₂ W₃ : (projectiveLine k).Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (h₃ : W₃ ≤ W₁) (x : Γ(projectiveLine k, W₁)) :
    (projectiveLine k).presheaf.map (homOfLE h₂).op ((projectiveLine k).presheaf.map
      (homOfLE h₁).op x) = (projectiveLine k).presheaf.map (homOfLE h₃).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma secU_apply (p : Polynomial k) :
    secU k p = Proj.awayToSection (grading k) (X 0) (ψ k 0 1 p) := rfl

lemma secV_apply (p : Polynomial k) :
    secV k p = Proj.awayToSection (grading k) (X 1) (ψ k 1 0 p) := rfl

lemma secW_apply (q : LaurentPolynomial k) :
    secW k q = (projectiveLine k).presheaf.map (homOfLE (chart_inf k).le).op
      (Proj.awayToSection (grading k) (X 0 * X 1) (awayUVEquiv k q)) := rfl

/-- Restriction from `D₊(X₀)` to the intersection is `toLaurent`. -/
lemma secU_restrict (p : Polynomial k) :
    (projectiveLine k).presheaf.map (homOfLE inf_le_left).op (secU k p) =
      secW k (Polynomial.toLaurent p) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading k) (X_mem k 1)
    (rfl : (X 0 * X 1 : MvPolynomial (Fin 2) k) = X 0 * X 1)) (ψ k 0 1 p)
  rw [secU_apply, secW_apply, awayUVEquiv_toLaurent]
  erw [e]
  rw [ConcreteCategory.comp_apply, presheaf_map_map']

/-- Restriction from `D₊(X₁)` to the intersection is `invert ∘ toLaurent`. -/
lemma secV_restrict (p : Polynomial k) :
    (projectiveLine k).presheaf.map (homOfLE inf_le_right).op (secV k p) =
      secW k (LaurentPolynomial.invert (Polynomial.toLaurent p)) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading k) (X_mem k 0)
    (mul_comm _ _ : (X 0 * X 1 : MvPolynomial (Fin 2) k) = X 1 * X 0)) (ψ k 1 0 p)
  rw [secV_apply, secW_apply, awayUVEquiv_invert]
  erw [e]
  rw [ConcreteCategory.comp_apply, presheaf_map_map']

/-! ### Constants -/

section Glue

variable {Y : Scheme.{u}} {U V : Y.Opens}

/-- Two sections over `U` and `V` agreeing on `U ∩ V` glue to a global section when
`U ∪ V = Y`. -/
lemma exists_glue (hUV : U ⊔ V = ⊤) (s : Γ(Y, U)) (t : Γ(Y, V))
    (h : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s =
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op t) :
    ∃ g : Γ(Y, ⊤), Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g = s ∧
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op g = t := by
  let sf : ∀ i : ULift.{u} (Fin 2), ToType (Y.presheaf.obj (op (pairCover U V i))) := fun i =>
    match i with
    | ⟨0⟩ => s
    | ⟨1⟩ => t
  have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 (pairCover U V) sf := by
    intro i j
    rcases eq_i₀_or_eq_i₁ i with rfl | rfl <;> rcases eq_i₀_or_eq_i₁ j with rfl | rfl
    · rfl
    · exact h
    · have hle : V ⊓ U ≤ U ⊓ V := fun x hx => ⟨hx.2, hx.1⟩
      have e := congrArg (Y.presheaf.map (homOfLE hle).op) h
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp] at e
      exact e.symm
    · rfl
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' (pairCover U V) ⊤
    (fun _ => homOfLE le_top) (by rw [iSup_pairCover, hUV]) sf hcompat
  exact ⟨g, hg i₀, hg i₁⟩

lemma eq_of_restrict (hUV : U ⊔ V = ⊤) {g g' : Γ(Y, ⊤)}
    (hU : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g =
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g')
    (hV : Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op g =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op g') : g = g' :=
  Y.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤)) (homOfLE (le_top : V ≤ ⊤))
    (by rw [hUV]) g g' hU hV

end Glue

lemma constants_agree (a : k) :
    (projectiveLine k).presheaf.map (homOfLE (inf_le_left : chartU k ⊓ chartV k ≤ chartU k)).op
        (secU k (Polynomial.C a)) =
      (projectiveLine k).presheaf.map (homOfLE (inf_le_right : chartU k ⊓ chartV k ≤ chartV k)).op
        (secV k (Polynomial.C a)) := by
  rw [secU_restrict, secV_restrict, Polynomial.toLaurent_C, LaurentPolynomial.invert_C]

/-- The global constant with value `a`. -/
def constGlob (a : k) : Γ(projectiveLine k, ⊤) :=
  (exists_glue (chart_sup k) _ _ (constants_agree k a)).choose

lemma constGlob_U (a : k) :
    (projectiveLine k).presheaf.map (homOfLE (le_top : chartU k ≤ ⊤)).op (constGlob k a) =
      secU k (Polynomial.C a) :=
  (exists_glue (chart_sup k) _ _ (constants_agree k a)).choose_spec.1

lemma constGlob_V (a : k) :
    (projectiveLine k).presheaf.map (homOfLE (le_top : chartV k ≤ ⊤)).op (constGlob k a) =
      secV k (Polynomial.C a) :=
  (exists_glue (chart_sup k) _ _ (constants_agree k a)).choose_spec.2

/-- The structure map `k → Γ(ℙ¹_k, 𝒪)`. -/
def constants : k →+* Γ(projectiveLine k, ⊤) where
  toFun := constGlob k
  map_one' := eq_of_restrict (chart_sup k) (by rw [constGlob_U, map_one, map_one, map_one])
    (by rw [constGlob_V, map_one, map_one, map_one])
  map_mul' a b := eq_of_restrict (chart_sup k)
    (by rw [constGlob_U, map_mul, map_mul, map_mul, constGlob_U, constGlob_U])
    (by rw [constGlob_V, map_mul, map_mul, map_mul, constGlob_V, constGlob_V])
  map_zero' := eq_of_restrict (chart_sup k) (by rw [constGlob_U, map_zero, map_zero, map_zero])
    (by rw [constGlob_V, map_zero, map_zero, map_zero])
  map_add' a b := eq_of_restrict (chart_sup k)
    (by rw [constGlob_U, map_add, map_add, map_add, constGlob_U, constGlob_U])
    (by rw [constGlob_V, map_add, map_add, map_add, constGlob_V, constGlob_V])

lemma constants_restrict_inf (a : k) :
    (projectiveLine k).presheaf.map (homOfLE (le_top : chartU k ⊓ chartV k ≤ ⊤)).op
      (constants k a) = secW k (LaurentPolynomial.C a) := by
  rw [← presheaf_map_map' k (le_top : chartU k ≤ ⊤) inf_le_left]
  change (projectiveLine k).presheaf.map _ ((projectiveLine k).presheaf.map _ (constGlob k a)) = _
  rw [constGlob_U, secU_restrict, Polynomial.toLaurent_C]

/-! ### The charts as `k`-modules -/

/-- `Γ(D₊(X₀), 𝒪) ≅ k[X₁/X₀]` as `k`-modules. -/
def chartEquivU : Polynomial k ≃ₗ[k]
    sectionsModuleCat (structureModule (projectiveLine k)) (constants k) (chartU k) le_top where
  toFun p := (secU k p : Γ(projectiveLine k, chartU k))
  invFun s := (secU k).symm s
  map_add' p q := map_add (secU k) p q
  map_smul' a p := by
    change secU k (a • p) = (projectiveLine k).presheaf.map (homOfLE le_top).op
      (constGlob k a) * secU k p
    rw [constGlob_U, Polynomial.smul_eq_C_mul, map_mul]
    rfl
  left_inv := (secU k).symm_apply_apply
  right_inv := (secU k).apply_symm_apply

/-- `Γ(D₊(X₁), 𝒪) ≅ k[X₀/X₁]` as `k`-modules. -/
def chartEquivV : Polynomial k ≃ₗ[k]
    sectionsModuleCat (structureModule (projectiveLine k)) (constants k) (chartV k) le_top where
  toFun p := (secV k p : Γ(projectiveLine k, chartV k))
  invFun s := (secV k).symm s
  map_add' p q := map_add (secV k) p q
  map_smul' a p := by
    change secV k (a • p) = (projectiveLine k).presheaf.map (homOfLE le_top).op
      (constGlob k a) * secV k p
    rw [constGlob_V, Polynomial.smul_eq_C_mul, map_mul]
    rfl
  left_inv := (secV k).symm_apply_apply
  right_inv := (secV k).apply_symm_apply

/-- `Γ(D₊(X₀) ∩ D₊(X₁), 𝒪) ≅ k[T, T⁻¹]` as `k`-modules. -/
def chartEquivUV : LaurentPolynomial k ≃ₗ[k] sectionsModuleCat (structureModule (projectiveLine k))
    (constants k) (chartU k ⊓ chartV k) le_top where
  toFun q := (secW k q : Γ(projectiveLine k, chartU k ⊓ chartV k))
  invFun s := (secW k).symm s
  map_add' p q := map_add (secW k) p q
  map_smul' a q := by
    change secW k (a • q) = (projectiveLine k).presheaf.map (homOfLE le_top).op
      (constants k a) * secW k q
    rw [constants_restrict_inf, LaurentPolynomial.smul_eq_C_mul, map_mul]
    rfl
  left_inv := (secW k).symm_apply_apply
  right_inv := (secW k).apply_symm_apply

/-- The coordinate `X₀/X₁` on `D₊(X₁)`. -/
def coordV : Γ(projectiveLine k, chartV k) := secV k Polynomial.X

lemma coordV_restrict :
    (projectiveLine k).presheaf.map (homOfLE (inf_le_right : chartU k ⊓ chartV k ≤ chartV k)).op
      (coordV k) = secW k (LaurentPolynomial.T (-1)) := by
  rw [coordV, secV_restrict, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]

lemma isUnit_coordV :
    IsUnit ((projectiveLine k).presheaf.map
      (homOfLE (inf_le_right : chartU k ⊓ chartV k ≤ chartV k)).op (coordV k)) := by
  rw [coordV_restrict]
  exact (LaurentPolynomial.isUnit_T (-1)).map (secW k)

/-- **The standard `ℙ¹`-charts of `ℙ¹_k = Proj k[X₀, X₁]`**: `U = D₊(X₀)`, `V = D₊(X₁)`, with
coordinates `X₁/X₀` and `s = X₀/X₁`. -/
def projectiveLineCharts : P1Charts (projectiveLine k) k (constants k) where
  U := chartU k
  V := chartV k
  sup_eq := chart_sup k
  isAffineOpen_U := Proj.isAffineOpen_basicOpen (grading k) (X 0) (X_mem k 0) one_pos
  isAffineOpen_V := Proj.isAffineOpen_basicOpen (grading k) (X 1) (X_mem k 1) one_pos
  isAffineOpen_inf := by
    rw [chart_inf]
    exact Proj.isAffineOpen_basicOpen (grading k) (X 0 * X 1) (X01_mem k) two_pos
  s := coordV k
  isUnit_s := isUnit_coordV k
  eU := chartEquivU k
  eV := chartEquivV k
  eUV := chartEquivUV k
  hU p := (secU_restrict k p).symm
  hV p := (secV_restrict k p).symm
  hS q := by
    change secW k (LaurentPolynomial.T (-1) * q) =
      ((isUnit_coordV k).unit : Γ(projectiveLine k, _)) * secW k q
    rw [IsUnit.unit_spec, coordV_restrict, map_mul]

/-! ### Cohomology of `𝒪(n)` on `ℙ¹_k` -/

instance : CompactSpace (projectiveLine k) := by
  constructor
  have h := (Proj.isAffineOpen_basicOpen (grading k) (X 0) (X_mem k 0) one_pos).isCompact.union
    (Proj.isAffineOpen_basicOpen (grading k) (X 1) (X_mem k 1) one_pos).isCompact
  have e : ((chartU k : Set (projectiveLine k)) ∪ chartV k) = Set.univ := by
    rw [← TopologicalSpace.Opens.coe_sup, chart_sup]
    rfl
  rwa [e] at h

/-- `ℙ¹_k` is separated (Mathlib: `Proj` is separated), so its diagonal is affine. -/
instance : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (projectiveLine k))) :=
  inferInstance

/-- The twisting sheaf `𝒪(n) = 𝒪(n · ∞)` on `ℙ¹_k`, `∞ = V(X₀)`. -/
abbrev twistingSheaf (n : ℤ) : (projectiveLine k).Modules :=
  (projectiveLineCharts k).twistingSheaf n

/-- `h⁰(ℙ¹_k, 𝒪) = 1`. -/
theorem finrank_cohomology_zero_projectiveLine :
    Module.finrank k (cohomology (structureModule (projectiveLine k)) (constants k) 0) = 1 :=
  (projectiveLineCharts k).finrank_cohomology_zero

/-- `H¹(ℙ¹_k, 𝒪) = 0`. -/
theorem isZero_cohomology_one_projectiveLine :
    Limits.IsZero (cohomology (structureModule (projectiveLine k)) (constants k) 1) :=
  (projectiveLineCharts k).isZero_cohomology_one

/-- `h⁰(ℙ¹_k, 𝒪(n)) = max(n + 1, 0)` (blueprint `lem:sm-p1-cohomology`). -/
theorem finrank_cohomology_zero_twist_projectiveLine (n : ℤ) :
    (Module.finrank k (cohomology (twistingSheaf k n) (constants k) 0) : ℤ) = max (n + 1) 0 :=
  (projectiveLineCharts k).finrank_cohomology_zero_twist n

/-- `h¹(ℙ¹_k, 𝒪(n)) = max(-n - 1, 0)` (blueprint `lem:sm-p1-cohomology`). -/
theorem finrank_cohomology_one_twist_projectiveLine (n : ℤ) :
    (Module.finrank k (cohomology (twistingSheaf k n) (constants k) 1) : ℤ) = max (-n - 1) 0 :=
  (projectiveLineCharts k).finrank_cohomology_one_twist n

end ProjectiveLine

end

end DeJongAlterations.StableModification.CurvesField
