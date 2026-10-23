import DeJongAlterations.StableModification.Curves.SemistableNormalEtale
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The Morse lemma in families

Let `O` be a ring and `P` an `O`-algebra étale over the plane `O[Y₀, Y₁]` with coordinates
`y₀, y₁`. If `G ∈ (y₀, y₁)` has `∂ⱼG ∈ (y₀, y₁)` and its Hessian is not in a prime `Q ⊇ (y₀, y₁)`,
then, étale locally near `Q`, `G = u · v` for new étale coordinates `u, v`
(`exists_etale_mul_of_hessian`). This is the algebraic core of the étale local structure of a
nodal family at a node (Stacks, Tag 0CBY, "proof not using Artin approximation"; blueprint
`sm-semistable-normal.tex`, `lem:sm-morse-families`).

The proof: `G = αy₀² + βy₀y₁ + γy₁²` with `β² - 4αγ ≡ -hessian G (mod (y₀, y₁))`
(`exists_quadratic_of_mem`, `hessian_add_disc_mem`), a binary quadratic form with discriminant
outside `Q`. Adjoining a root of `X² + (β/α)X + γ/α`, which is a standard étale extension because
its discriminant is invertible, factors it into two linear forms with invertible determinant
(`factorsEtaleLocally`); the two linear forms are étale coordinates near `Q` because their Jacobian
determinant agrees with that determinant modulo `(y₀, y₁)`.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen (coord planeDerivation planeDerivation_coord hessian)

universe u

section Factor

variable {W : Type u} [CommRing W]

/-- The binary quadratic form `αz₀² + βz₀z₁ + γz₁²` splits étale locally near the prime `Q`: there
are an étale `W`-algebra `W₁`, a prime `Q₁` over `Q`, and a matrix `m` over `W₁` with invertible
determinant such that the form is `(m₀₀z₀ + m₀₁z₁)(m₁₀z₀ + m₁₁z₁)` in `W₁`. -/
def FactorsEtaleLocally (Q : Ideal W) (α β γ z₀ z₁ : W) : Prop :=
  ∃ (W₁ : Type u) (_ : CommRing W₁) (_ : Algebra W W₁) (_ : Algebra.Etale W W₁)
    (Q₁ : Ideal W₁) (_ : Q₁.IsPrime), Q₁.comap (algebraMap W W₁) = Q ∧
    ∃ m : Fin 2 → Fin 2 → W₁, IsUnit (m 0 0 * m 1 1 - m 0 1 * m 1 0) ∧
      algebraMap W W₁ (α * z₀ ^ 2 + β * z₀ * z₁ + γ * z₁ ^ 2) =
        (m 0 0 * algebraMap W W₁ z₀ + m 0 1 * algebraMap W W₁ z₁) *
          (m 1 0 * algebraMap W W₁ z₀ + m 1 1 * algebraMap W W₁ z₁)

/-- The monic quadratic `X² + bX + c`. -/
def quadPoly (b c : W) : W[X] := X ^ 2 + C b * X + C c

theorem quadPoly_monic (b c : W) : (quadPoly b c).Monic := by
  have : quadPoly b c = X ^ 2 + (C b * X + C c) := by rw [quadPoly, add_assoc]
  rw [this]
  refine monic_X_pow_add ((degree_add_le _ _).trans_lt (max_lt ?_ ?_))
  · exact (degree_C_mul_X_le b).trans_lt (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
  · exact degree_C_le.trans_lt (by exact_mod_cast (by norm_num : (0 : ℕ) < 2))

theorem derivative_quadPoly (b c : W) : derivative (quadPoly b c) = C 2 * X + C b := by
  rw [quadPoly, derivative_add, derivative_add, derivative_X_sq, derivative_C_mul_X, derivative_C,
    add_zero]

/-- The standard étale pair `(X² + bX + c, 2X + b)`. -/
def quadPair (b c : W) : StandardEtalePair W where
  f := quadPoly b c
  monic_f := quadPoly_monic b c
  g := derivative (quadPoly b c)
  cond := ⟨1, 0, 1, by simp⟩

/-- **Splitting a binary form with invertible leading coefficient.** -/
theorem factorsEtaleLocally_of_isUnit (Q : Ideal W) [Q.IsPrime] {α : W} (hα : IsUnit α)
    (β γ z₀ z₁ : W) (hd : β ^ 2 - 4 * α * γ ∉ Q) : FactorsEtaleLocally Q α β γ z₀ z₁ := by
  obtain ⟨a, ha⟩ := hα.exists_left_inv
  let P := quadPair (a * β) (a * γ)
  -- a geometric point of `W₁` over `Q`
  let L := AlgebraicClosure (FractionRing (W ⧸ Q))
  let φ : W →+* L := (algebraMap (FractionRing (W ⧸ Q)) L).comp
    ((algebraMap (W ⧸ Q) (FractionRing (W ⧸ Q))).comp (Ideal.Quotient.mk Q))
  have hφker : RingHom.ker φ = Q := by
    ext x
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (W ⧸ Q)) L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (W ⧸ Q) (FractionRing (W ⧸ Q))),
      Ideal.Quotient.eq_zero_iff_mem]
  let : Algebra W L := φ.toAlgebra
  have hdeg : ((quadPoly (a * β) (a * γ)).map φ).degree ≠ 0 := by
    have : ((quadPoly (a * β) (a * γ)).map φ).degree = 2 := by
      simp only [quadPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_mul, Polynomial.map_C]
      compute_degree!
    rw [this]; exact two_ne_zero
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
  have ht' : t ^ 2 + φ (a * β) * t + φ (a * γ) = 0 := by
    simpa [quadPoly, IsRoot, eval_map] using ht
  have hφa : φ a * φ α = 1 := by rw [← map_mul, ha, map_one]
  have hdφ : φ (β ^ 2 - 4 * α * γ) ≠ 0 := by
    rw [Ne, ← RingHom.mem_ker, hφker]; exact hd
  have hmap : P.HasMap t := by
    refine ⟨?_, ?_⟩
    · change aeval t (quadPoly (a * β) (a * γ)) = 0
      simpa [quadPoly, aeval_def, eval₂_eq_eval_map, RingHom.algebraMap_toAlgebra] using ht'
    · change IsUnit (aeval t (derivative (quadPoly (a * β) (a * γ))))
      rw [derivative_quadPoly]
      simp only [map_add, map_mul, aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]
      refine IsUnit.mk0 _ fun h0 => hdφ ?_
      have h2 : φ 2 = 2 := map_ofNat φ 2
      have : (φ 2 * t + φ a * φ β) ^ 2 = (φ a) ^ 2 * φ (β ^ 2 - 4 * α * γ) := by
        rw [h2]
        simp only [map_sub, map_mul, map_pow, map_ofNat] at ht' ⊢
        linear_combination 4 * ht' + 4 * φ a * φ γ * hφa
      rw [h0, zero_pow two_ne_zero] at this
      have hφa0 : φ a ≠ 0 := left_ne_zero_of_mul_eq_one hφa
      exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero 2 hφa0)
  let ψ : P.Ring →ₐ[W] L := P.lift t hmap
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, RingHom.ker ψ.toRingHom,
    RingHom.ker_isPrime _, ?_, ?_⟩
  · ext x
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change ψ (algebraMap W P.Ring x) = 0 ↔ x ∈ Q
    rw [AlgHom.commutes]
    exact SetLike.ext_iff.mp hφker x
  · set r := P.X
    have hr : aeval r P.f = 0 := P.hasMap_X.1
    have hr' : IsUnit (aeval r P.g) := P.hasMap_X.2
    change aeval r (quadPoly (a * β) (a * γ)) = 0 at hr
    change IsUnit (aeval r (derivative (quadPoly (a * β) (a * γ)))) at hr'
    rw [derivative_quadPoly] at hr'
    simp only [quadPoly, map_add, map_mul, map_pow, aeval_X, aeval_C] at hr hr'
    set ι := algebraMap W P.Ring
    refine ⟨![![ι α, -(ι α * r)], ![1, ι (a * β) + r]], ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have : ι α * (ι (a * β) + r) - -(ι α * r) * 1 = ι α * (ι 2 * r + ι a * ι β) := by
        rw [map_ofNat, map_mul]; ring
      rw [this]
      exact (hα.map ι).mul hr'
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul,
        map_pow]
      have hαa : ι α * ι a = 1 := by rw [← map_mul, mul_comm, ha, map_one]
      linear_combination (ι α * ι z₁ ^ 2) * hr - (ι β * ι z₀ * ι z₁ + ι γ * ι z₁ ^ 2) * hαa

/-- A splitting over an étale `W`-algebra, at a prime over `Q`, gives one over `W`. -/
theorem FactorsEtaleLocally.of_etale {W' : Type u} [CommRing W'] [Algebra W W']
    [Algebra.Etale W W'] {Q : Ideal W} {Q' : Ideal W'} (hQ' : Q'.comap (algebraMap W W') = Q)
    {α β γ z₀ z₁ : W}
    (h : FactorsEtaleLocally Q' (algebraMap W W' α) (algebraMap W W' β) (algebraMap W W' γ)
      (algebraMap W W' z₀) (algebraMap W W' z₁)) :
    FactorsEtaleLocally Q α β γ z₀ z₁ := by
  obtain ⟨W₁, _, _, _, Q₁, _, hQ₁, m, hm, heq⟩ := h
  let : Algebra W W₁ := ((algebraMap W' W₁).comp (algebraMap W W')).toAlgebra
  have : IsScalarTower W W' W₁ := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨W₁, inferInstance, inferInstance, Algebra.Etale.comp W W' W₁, Q₁, inferInstance, ?_, m,
    hm, ?_⟩
  · rw [IsScalarTower.algebraMap_eq W W' W₁, ← Ideal.comap_comap, hQ₁, hQ']
  · simp only [map_add, map_mul, map_pow] at heq ⊢
    simp only [IsScalarTower.algebraMap_apply W W' W₁]
    exact heq

/-- **Splitting a binary form whose leading coefficient is a unit at `Q`**: invert it first. -/
theorem factorsEtaleLocally_of_notMem (Q : Ideal W) [Q.IsPrime] {α : W} (hα : α ∉ Q)
    (β γ z₀ z₁ : W) (hd : β ^ 2 - 4 * α * γ ∉ Q) : FactorsEtaleLocally Q α β γ z₀ z₁ := by
  let W' := Localization.Away α
  have hdisj : Disjoint (Submonoid.powers α : Set W) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hα
  let Q' := Q.map (algebraMap W W')
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers α) W' Q
    ‹_› hdisj
  have hQ' : Q'.comap (algebraMap W W') = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers α) W' ‹_› hdisj
  have : Algebra.Etale W W' := Algebra.Etale.of_isLocalizationAway α
  refine FactorsEtaleLocally.of_etale hQ' (factorsEtaleLocally_of_isUnit Q'
    (IsLocalization.Away.algebraMap_isUnit α) _ _ _ _ ?_)
  intro hmem
  apply hd
  rw [← hQ', Ideal.mem_comap]
  simpa only [map_sub, map_mul, map_pow, map_ofNat] using hmem

/-- **Binary quadratic forms with discriminant outside `Q` split étale locally near `Q`.** -/
theorem factorsEtaleLocally (Q : Ideal W) [Q.IsPrime] (α β γ z₀ z₁ : W)
    (hd : β ^ 2 - 4 * α * γ ∉ Q) : FactorsEtaleLocally Q α β γ z₀ z₁ := by
  by_cases hα : α ∈ Q
  · by_cases hγ : γ ∈ Q
    · -- substitute `z₁ ↦ z₀ + z₁`: the new leading coefficient `α - β + γ` is outside `Q`
      have hβ : β ∉ Q := by
        intro hβ
        apply hd
        exact Q.sub_mem (by rw [pow_two]; exact Q.mul_mem_left β hβ)
          (Q.mul_mem_right γ (Q.mul_mem_left 4 hα))
      have hα' : α - β + γ ∉ Q := by
        intro h
        apply hβ
        have : β = α + γ - (α - β + γ) := by ring
        rw [this]
        exact Q.sub_mem (Q.add_mem hα hγ) h
      obtain ⟨W₁, _, _, _, Q₁, _, hQ₁, n, hn, heq⟩ := factorsEtaleLocally_of_notMem Q hα'
        (β - 2 * γ) γ z₀ (z₀ + z₁) (by
          have : (β - 2 * γ) ^ 2 - 4 * (α - β + γ) * γ = β ^ 2 - 4 * α * γ := by ring
          rwa [this])
      refine ⟨W₁, inferInstance, inferInstance, inferInstance, Q₁, inferInstance, hQ₁,
        ![![n 0 0 + n 0 1, n 0 1], ![n 1 0 + n 1 1, n 1 1]], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        convert hn using 1
        ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have : α * z₀ ^ 2 + β * z₀ * z₁ + γ * z₁ ^ 2 =
            (α - β + γ) * z₀ ^ 2 + (β - 2 * γ) * z₀ * (z₀ + z₁) + γ * (z₀ + z₁) ^ 2 := by ring
        rw [this, heq, map_add]
        ring
    · -- swap the variables
      obtain ⟨W₁, _, _, _, Q₁, _, hQ₁, n, hn, heq⟩ := factorsEtaleLocally_of_notMem Q hγ
        β α z₁ z₀ (by
          have : β ^ 2 - 4 * γ * α = β ^ 2 - 4 * α * γ := by ring
          rwa [this])
      refine ⟨W₁, inferInstance, inferInstance, inferInstance, Q₁, inferInstance, hQ₁,
        ![![n 0 1, n 0 0], ![n 1 1, n 1 0]], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have : n 0 1 * n 1 0 - n 0 0 * n 1 1 = -(n 0 0 * n 1 1 - n 0 1 * n 1 0) := by ring
        rw [this]
        exact hn.neg
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have : α * z₀ ^ 2 + β * z₀ * z₁ + γ * z₁ ^ 2 =
            γ * z₁ ^ 2 + β * z₁ * z₀ + α * z₀ ^ 2 := by ring
        rw [this, heq]
        ring
  · exact factorsEtaleLocally_of_notMem Q hα β γ z₀ z₁ hd

end Factor

section Taylor

variable (O : Type u) [CommRing O] (P : Type u) [CommRing P] [Algebra O P]
  [Algebra (MvPolynomial (Fin 2) O) P] [IsScalarTower O (MvPolynomial (Fin 2) O) P]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) O) P]

/-- The ideal `(y₀, y₁)` of the zero section of the coordinates. -/
abbrev coordIdeal : Ideal P := Ideal.span {coord O P 0, coord O P 1}

omit [Algebra O P] [IsScalarTower O (MvPolynomial (Fin 2) O) P]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) O) P] in
theorem coord_mem_coordIdeal (i : Fin 2) : coord O P i ∈ coordIdeal O P := by
  fin_cases i
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

variable {O P}

theorem planeDerivation_mul_coord (k i : Fin 2) (F : P) :
    planeDerivation O P k (F * coord O P i) =
      F * (if i = k then 1 else 0) + coord O P i * planeDerivation O P k F := by
  rw [Derivation.leibniz, planeDerivation_coord, smul_eq_mul, smul_eq_mul]

theorem planeDerivation_mul_coord_mul_coord_mem (k a b : Fin 2) (F : P) :
    planeDerivation O P k (F * coord O P a * coord O P b) ∈ coordIdeal O P := by
  rw [planeDerivation_mul_coord, planeDerivation_mul_coord]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
    (coord_mem_coordIdeal O P a))) (Ideal.mul_mem_right _ _ (coord_mem_coordIdeal O P b))

theorem mk_planeDerivation_mul_coord (k a : Fin 2) (F : P) :
    Ideal.Quotient.mk (coordIdeal O P) (planeDerivation O P k (F * coord O P a)) =
      Ideal.Quotient.mk (coordIdeal O P) F * (if a = k then 1 else 0) := by
  rw [planeDerivation_mul_coord, map_add, map_mul, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr (coord_mem_coordIdeal O P a), zero_mul, add_zero]
  split_ifs <;> simp

/-- Second derivatives of a quadratic monomial modulo `(y₀, y₁)`. -/
theorem planeDerivation_planeDerivation_quadratic (j k a b : Fin 2) (F : P) :
    Ideal.Quotient.mk (coordIdeal O P)
        (planeDerivation O P k (planeDerivation O P j (F * coord O P a * coord O P b))) =
      Ideal.Quotient.mk (coordIdeal O P) F *
        ((if a = k then 1 else 0) * (if b = j then 1 else 0) +
          (if b = k then 1 else 0) * (if a = j then 1 else 0)) := by
  have e : planeDerivation O P j (F * coord O P a * coord O P b) =
      (F * (if b = j then 1 else 0)) * coord O P a + (F * (if a = j then 1 else 0)) * coord O P b +
        planeDerivation O P j F * coord O P a * coord O P b := by
    rw [planeDerivation_mul_coord, planeDerivation_mul_coord]
    ring
  rw [e, map_add, map_add, map_add, map_add, mk_planeDerivation_mul_coord,
    mk_planeDerivation_mul_coord,
    Ideal.Quotient.eq_zero_iff_mem.mpr (planeDerivation_mul_coord_mul_coord_mem k a b _),
    add_zero, map_mul, map_mul]
  split_ifs <;> (simp; try ring)

/-- **Taylor expansion to second order along the zero section.** If `G ∈ (y₀, y₁)` and
`∂₀G, ∂₁G ∈ (y₀, y₁)`, then `G = αy₀² + βy₀y₁ + γy₁²`. -/
theorem exists_quadratic_of_mem {G : P} (hG : G ∈ coordIdeal O P)
    (hdG : ∀ j, planeDerivation O P j G ∈ coordIdeal O P) :
    ∃ α β γ : P, G = α * coord O P 0 ^ 2 + β * coord O P 0 * coord O P 1 +
      γ * coord O P 1 ^ 2 := by
  obtain ⟨c₀, c₁, hc⟩ := Ideal.mem_span_pair.mp hG
  have hcj : ∀ j : Fin 2, (if j = 0 then c₀ else c₁) ∈ coordIdeal O P := by
    intro j
    have h := hdG j
    rw [← hc, map_add, Derivation.leibniz, Derivation.leibniz, planeDerivation_coord,
      planeDerivation_coord] at h
    simp only [smul_eq_mul] at h
    have : (if j = 0 then c₀ else c₁) = (c₀ * (if (0 : Fin 2) = j then 1 else 0) +
        coord O P 0 * planeDerivation O P j c₀ + (c₁ * (if (1 : Fin 2) = j then 1 else 0) +
        coord O P 1 * planeDerivation O P j c₁)) -
        (coord O P 0 * planeDerivation O P j c₀ + coord O P 1 * planeDerivation O P j c₁) := by
      fin_cases j <;> simp
    rw [this]
    refine Ideal.sub_mem _ h (Ideal.add_mem _ ?_ ?_)
    · exact Ideal.mul_mem_right _ _ (coord_mem_coordIdeal O P 0)
    · exact Ideal.mul_mem_right _ _ (coord_mem_coordIdeal O P 1)
  obtain ⟨b₀₀, b₀₁, hb₀⟩ := Ideal.mem_span_pair.mp (hcj 0)
  obtain ⟨b₁₀, b₁₁, hb₁⟩ := Ideal.mem_span_pair.mp (hcj 1)
  simp only [show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte] at hb₀ hb₁
  refine ⟨b₀₀, b₀₁ + b₁₀, b₁₁, ?_⟩
  rw [← hc, ← hb₀, ← hb₁]
  ring

/-- **The Hessian of a quadratic form along the zero section** is minus its discriminant:
`hessian G + (β² - 4αγ) ∈ (y₀, y₁)` for `G = αy₀² + βy₀y₁ + γy₁²`. -/
theorem hessian_add_disc_mem (α β γ : P) :
    hessian O P (α * coord O P 0 ^ 2 + β * coord O P 0 * coord O P 1 + γ * coord O P 1 ^ 2) +
      (β ^ 2 - 4 * α * γ) ∈ coordIdeal O P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have e : α * coord O P 0 ^ 2 + β * coord O P 0 * coord O P 1 + γ * coord O P 1 ^ 2 =
      α * coord O P 0 * coord O P 0 + β * coord O P 0 * coord O P 1 +
        γ * coord O P 1 * coord O P 1 := by ring
  have hd : ∀ j k : Fin 2, Ideal.Quotient.mk (coordIdeal O P)
      (planeDerivation O P k (planeDerivation O P j
        (α * coord O P 0 * coord O P 0 + β * coord O P 0 * coord O P 1 +
          γ * coord O P 1 * coord O P 1))) =
      Ideal.Quotient.mk (coordIdeal O P) α *
          ((if (0 : Fin 2) = k then 1 else 0) * (if (0 : Fin 2) = j then 1 else 0) +
            (if (0 : Fin 2) = k then 1 else 0) * (if (0 : Fin 2) = j then 1 else 0)) +
        Ideal.Quotient.mk (coordIdeal O P) β *
          ((if (0 : Fin 2) = k then 1 else 0) * (if (1 : Fin 2) = j then 1 else 0) +
            (if (1 : Fin 2) = k then 1 else 0) * (if (0 : Fin 2) = j then 1 else 0)) +
        Ideal.Quotient.mk (coordIdeal O P) γ *
          ((if (1 : Fin 2) = k then 1 else 0) * (if (1 : Fin 2) = j then 1 else 0) +
            (if (1 : Fin 2) = k then 1 else 0) * (if (1 : Fin 2) = j then 1 else 0)) := by
    intro j k
    rw [map_add, map_add, map_add, map_add, map_add, map_add,
      planeDerivation_planeDerivation_quadratic, planeDerivation_planeDerivation_quadratic,
      planeDerivation_planeDerivation_quadratic]
  rw [e, hessian, map_add, map_sub, map_mul, map_mul, hd, hd, hd, hd]
  simp only [show ((1 : Fin 2) = 0) = False from by decide,
    show ((0 : Fin 2) = 1) = False from by decide, if_true, if_false, map_sub, map_pow, map_mul,
    map_ofNat]
  ring

end Taylor

section Morse

variable {O : Type u} [CommRing O] {P : Type u} [CommRing P] [Algebra O P]
  [Algebra (MvPolynomial (Fin 2) O) P] [IsScalarTower O (MvPolynomial (Fin 2) O) P]

/-- The Jacobian determinant of two linear forms in the coordinates agrees with the determinant
of their coefficient matrix modulo `(y₀, y₁)`. -/
theorem jacobian_linear_sub_det_mem [Algebra.FormallyEtale (MvPolynomial (Fin 2) O) P]
    (m : Fin 2 → Fin 2 → P) :
    jacobian O P ![m 0 0 * coord O P 0 + m 0 1 * coord O P 1,
        m 1 0 * coord O P 0 + m 1 1 * coord O P 1] -
      (m 0 0 * m 1 1 - m 0 1 * m 1 0) ∈ coordIdeal O P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h : ∀ k : Fin 2, ∀ c₀ c₁ : P, Ideal.Quotient.mk (coordIdeal O P)
      (planeDerivation O P k (c₀ * coord O P 0 + c₁ * coord O P 1)) =
      Ideal.Quotient.mk (coordIdeal O P) (if k = 0 then c₀ else c₁) := by
    intro k c₀ c₁
    rw [map_add, map_add, mk_planeDerivation_mul_coord, mk_planeDerivation_mul_coord]
    fin_cases k <;> simp
  simp only [jacobian, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_mul, h]
  simp only [show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  ring

variable [Algebra.Etale (MvPolynomial (Fin 2) O) P]

/-- **The Morse lemma in families.** Let `P` be étale over `O[Y₀, Y₁]` with coordinates `y₀, y₁`,
and `G ∈ (y₀, y₁)` with `∂₀G, ∂₁G ∈ (y₀, y₁)`. If the Hessian of `G` is outside a prime
`Q ⊇ (y₀, y₁)`, there is an étale `P`-algebra `P'` with a prime `Q'` over `Q` and an étale plane
structure `O[U, V] → P'` whose coordinates `u, v` lie in `(y₀, y₁)P'` and satisfy `G = u · v`. -/
theorem exists_etale_mul_of_hessian {G : P} (Q : Ideal P) [Q.IsPrime]
    (hG : G ∈ coordIdeal O P) (hdG : ∀ j, planeDerivation O P j G ∈ coordIdeal O P)
    (hQ : coordIdeal O P ≤ Q) (hh : hessian O P G ∉ Q) :
    ∃ (P' : Type u) (_ : CommRing P') (_ : Algebra P P') (_ : Algebra.Etale P P')
      (_ : Algebra O P') (_ : IsScalarTower O P P')
      (_ : Algebra (MvPolynomial (Fin 2) O) P') (_ : IsScalarTower O (MvPolynomial (Fin 2) O) P')
      (_ : Algebra.Etale (MvPolynomial (Fin 2) O) P') (Q' : Ideal P') (_ : Q'.IsPrime),
      Q'.comap (algebraMap P P') = Q ∧
      (∀ i, coord O P' i ∈ (coordIdeal O P).map (algebraMap P P')) ∧
      algebraMap P P' G = coord O P' 0 * coord O P' 1 := by
  obtain ⟨α, β, γ, hGq⟩ := exists_quadratic_of_mem hG hdG
  have hd : β ^ 2 - 4 * α * γ ∉ Q := by
    intro h
    apply hh
    have := hQ (hessian_add_disc_mem α β γ)
    rw [← hGq] at this
    simpa using Q.sub_mem this h
  obtain ⟨P₁, _, _, _, Q₁, _, hQ₁, m, hm, heq⟩ :=
    factorsEtaleLocally Q α β γ (coord O P 0) (coord O P 1) hd
  -- the plane structure of `P₁` through `P`
  let : Algebra O P₁ := ((algebraMap P P₁).comp (algebraMap O P)).toAlgebra
  have : IsScalarTower O P P₁ := .of_algebraMap_eq' rfl
  let : Algebra (MvPolynomial (Fin 2) O) P₁ :=
    ((algebraMap P P₁).comp (algebraMap (MvPolynomial (Fin 2) O) P)).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin 2) O) P P₁ := .of_algebraMap_eq' rfl
  have : IsScalarTower O (MvPolynomial (Fin 2) O) P₁ := .of_algebraMap_eq fun o => by
    change algebraMap P P₁ (algebraMap O P o) =
      algebraMap P P₁ (algebraMap (MvPolynomial (Fin 2) O) P (algebraMap O _ o))
    rw [← IsScalarTower.algebraMap_apply O (MvPolynomial (Fin 2) O) P]
  have : Algebra.Etale (MvPolynomial (Fin 2) O) P₁ := Algebra.Etale.comp _ P P₁
  have hc₁ : ∀ i, coord O P₁ i = algebraMap P P₁ (coord O P i) := fun i => rfl
  set w : Fin 2 → P₁ := ![m 0 0 * coord O P₁ 0 + m 0 1 * coord O P₁ 1,
    m 1 0 * coord O P₁ 0 + m 1 1 * coord O P₁ 1] with hw
  have hyQ₁ : coordIdeal O P₁ ≤ Q₁ := by
    rw [Ideal.span_le]
    rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, hc₁, ← Ideal.mem_comap, hQ₁] <;>
      exact hQ (coord_mem_coordIdeal O P _)
  have hjQ : jacobian O P₁ w ∉ Q₁ := by
    intro h
    have hdet : m 0 0 * m 1 1 - m 0 1 * m 1 0 ∈ Q₁ := by
      have := Q₁.sub_mem h (hyQ₁ (jacobian_linear_sub_det_mem m))
      rwa [sub_sub_cancel] at this
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hdet hm)
  -- localize at the Jacobian
  let P₂ := Localization.Away (jacobian O P₁ w)
  have hdisj : Disjoint (Submonoid.powers (jacobian O P₁ w) : Set P₁) Q₁ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hjQ
  let Q₂ := Q₁.map (algebraMap P₁ P₂)
  have : Q₂.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (jacobian O P₁ w)) P₂ Q₁ ‹_› hdisj
  have hQ₂ : Q₂.comap (algebraMap P₁ P₂) = Q₁ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (jacobian O P₁ w)) P₂ ‹_›
      hdisj
  have : Algebra.Etale P₁ P₂ := Algebra.Etale.of_isLocalizationAway (jacobian O P₁ w)
  have : Algebra.Etale (MvPolynomial (Fin 2) O) P₂ := Algebra.Etale.comp _ P₁ P₂
  have : Algebra.Etale P P₂ := Algebra.Etale.comp P P₁ P₂
  have hc₂ : ∀ i, (IsScalarTower.toAlgHom O P₁ P₂) (coord O P₁ i) = coord O P₂ i := fun i =>
    (IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) O) P₁ P₂ _).symm
  set w₂ : Fin 2 → P₂ := fun i => algebraMap P₁ P₂ (w i) with hw₂
  have hjac₂ : IsUnit (jacobian O P₂ w₂) := by
    have := jacobian_map (IsScalarTower.toAlgHom O P₁ P₂) hc₂ w
    simp only [IsScalarTower.coe_toAlgHom'] at this
    rw [hw₂, this]
    exact IsLocalization.Away.algebraMap_isUnit _
  have : Algebra.FinitePresentation O P₂ := by
    have : Algebra.FinitePresentation O P :=
      Algebra.FinitePresentation.trans O (MvPolynomial (Fin 2) O) P
    have : Algebra.FinitePresentation O P₁ := Algebra.FinitePresentation.trans O P P₁
    exact Algebra.FinitePresentation.trans O P₁ P₂
  have hrec := etale_recoord O w₂ hjac₂
  -- the final algebra
  let e := Recoord.equiv O w₂
  let : Algebra P (Recoord O w₂) := (e.toRingHom.comp (algebraMap P P₂)).toAlgebra
  let eP : P₂ ≃ₐ[P] Recoord O w₂ := { e with commutes' := fun _ => rfl }
  have : Algebra.Etale P (Recoord O w₂) := Algebra.Etale.of_equiv eP
  have : IsScalarTower O P (Recoord O w₂) := .of_algebraMap_eq fun o => by
    change algebraMap O P₂ o = algebraMap P P₂ (algebraMap O P o)
    rw [IsScalarTower.algebraMap_apply O P₁ P₂, IsScalarTower.algebraMap_apply P P₁ P₂]
    rfl
  refine ⟨Recoord O w₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hrec, Q₂, ‹_›, ?_, ?_, ?_⟩
  · change Q₂.comap (algebraMap P P₂) = Q
    rw [IsScalarTower.algebraMap_eq P P₁ P₂, ← Ideal.comap_comap, hQ₂, hQ₁]
  · intro i
    rw [coord_recoord]
    change w₂ i ∈ (coordIdeal O P).map (algebraMap P P₂)
    have hmem : w i ∈ (coordIdeal O P).map (algebraMap P P₁) := by
      have : coordIdeal O P₁ = (coordIdeal O P).map (algebraMap P P₁) := by
        rw [Ideal.map_span, Set.image_pair]
        simp only [coordIdeal, hc₁]
      rw [← this]
      fin_cases i <;>
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (coord_mem_coordIdeal O P₁ 0))
          (Ideal.mul_mem_left _ _ (coord_mem_coordIdeal O P₁ 1))
    rw [IsScalarTower.algebraMap_eq P P₁ P₂, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hmem
  · rw [coord_recoord, coord_recoord]
    change algebraMap P P₂ G = w₂ 0 * w₂ 1
    rw [IsScalarTower.algebraMap_apply P P₁ P₂, hGq, heq, hw₂, ← map_mul]
    rfl

end Morse

end DeJongAlterations.StableModification.Curves.SemistableNormal
