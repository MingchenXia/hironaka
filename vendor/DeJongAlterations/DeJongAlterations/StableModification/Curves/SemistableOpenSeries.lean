import DeJongAlterations.Algebra.NodeVariableMorseJacobian
import DeJongAlterations.Algebra.NodeFieldJetRigidity
import DeJongAlterations.Algebra.NodeFieldCubicRelation
import DeJongAlterations.Algebra.NodeFieldGeometricCubicMap
import DeJongAlterations.Algebra.NodeFieldSeriesJetQuadratic
import DeJongAlterations.Algebra.NodeFieldUVJetLength
import DeJongAlterations.Algebra.NodeFieldCotangentGeneratorsJet

/-!
# Formal plane curve germs: smooth points and ordinary double points

Let `K` be a field and `G ∈ K[[x, y]]` a formal power series without constant term. This file
classifies the formal plane curve germ `K[[x, y]]/(G)` in the two cases needed for the openness of
the semi-stable locus (M. Temkin, *Stable modification of relative curves*, Lemma 5.1(i),
`references/temkin10-stable-modification/source/semi-stable.tex`, T:3282–3292; de Jong 1996, 2.21–2.23,
`references/dejong96-alterations/tex/page-0012.tex`), and records the formal fact behind the
"Hessian" open condition used there:

* `spanFinrank_maximalIdeal_equation_le_one`: if `G` has a nonzero linear term, the maximal ideal
  of `K[[x, y]]/(G)` is principal (a smooth formal germ).
* `equationEquivFormalUV`: if `G` has no linear term and its quadratic part has nonzero
  discriminant, then over an algebraically closed field `K[[x, y]]/(G) ≅ K[[u, v]]/(uv)`
  (Codex's formal Morse lemma, `Algebra.NodeVariableMorse.equationQuotientEquiv`, and the
  splitting of a nondegenerate quadratic form).
* `constantCoeff_hessian`: the constant term of the Hessian determinant
  `∂ₓ∂ₓG · ∂ᵧ∂ᵧG - ∂ₓ∂ᵧG · ∂ᵧ∂ₓG` is minus the discriminant of the quadratic part of `G`.
  So, for `G` without linear term, "`G` is an ordinary double point" is the open condition
  "the Hessian determinant is a unit" (this replaces the Fitting-ideal/Tjurina-number route of
  PLAN-SM-GEOM chapter D, which fails for embedded points, see the blueprint).
* `exists_ker_eq_span_of_formalUV`: conversely, if a surjection `ψ : K[[x, y]] → C` has target
  `C ≅ K[[u, v]]/(uv)` (with `K` algebraically closed), then its kernel is principal, generated
  by a series of order exactly two with nondegenerate quadratic part (Codex's cubic-relation and
  jet-rigidity lemmas). In particular, `jetDiscriminant_ne_zero_of_equationEquiv`: if
  `K[[x, y]]/(G) ≅ K[[u, v]]/(uv)`, then `G` has no linear term and nonzero discriminant.
-/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.StableModification.Curves.SemistableOpen

open Algebra.NodeFormalMorse Algebra.NodeVariableMorse Algebra.NodeGeometricCompletionFormalUV
  Algebra.NodeFieldQuadraticSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

variable {K : Type u} [Field K]

section Coefficients

/-- A series times an element of the variable ideal agrees with its constant term times that
element modulo the square of the variable ideal. -/
theorem mul_sub_C_mul_mem_sq (a f : Series K) (hf : f ∈ variableIdeal K) :
    a * f - C (constantCoeff a) * f ∈ variableIdeal K ^ 2 := by
  have ha : a - C (constantCoeff a) ∈ variableIdeal K :=
    mem_variableIdeal_of_constantCoeff_eq_zero (by simp)
  rw [← sub_mul, pow_two]
  exact Ideal.mul_mem_mul ha hf

/-- A series times an element of the square of the variable ideal agrees with its constant term
times that element modulo the cube of the variable ideal. -/
theorem mul_sub_C_mul_mem_cube (a f : Series K) (hf : f ∈ variableIdeal K ^ 2) :
    a * f - C (constantCoeff a) * f ∈ variableIdeal K ^ 3 := by
  have ha : a - C (constantCoeff a) ∈ variableIdeal K :=
    mem_variableIdeal_of_constantCoeff_eq_zero (by simp)
  rw [← sub_mul, pow_succ']
  exact Ideal.mul_mem_mul ha hf

/-- Coefficients of total degree less than `n` vanish on the `n`-th power of the variable
ideal. -/
theorem coeff_eq_zero_of_mem_pow {n : ℕ} {f : Series K} (hf : f ∈ variableIdeal K ^ n)
    {d : Fin 2 →₀ ℕ} (hd : d.degree < n) : coeff d f = 0 := by
  apply coeff_of_lt_order
  have ho := (mem_variableIdeal_pow_iff_order n f).mp hf
  exact lt_of_lt_of_le (by exact_mod_cast hd) ho

theorem degree_single_one (i : Fin 2) : (Finsupp.single i 1 : Fin 2 →₀ ℕ).degree = 1 := by
  simp

theorem degree_single_add_single (i j : Fin 2) :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin 2 →₀ ℕ).degree = 2 := by
  rw [map_add, degree_single_one, degree_single_one]

/-- The linear coefficients of `a * f`, for `f` without constant term, are those of `f` scaled by
the constant term of `a`. -/
theorem coeff_single_mul_of_mem (a f : Series K) (hf : f ∈ variableIdeal K) (i : Fin 2) :
    coeff (Finsupp.single i 1) (a * f) = constantCoeff a * coeff (Finsupp.single i 1) f := by
  have h := coeff_eq_zero_of_mem_pow (mul_sub_C_mul_mem_sq a f hf)
    (d := Finsupp.single i 1) (by rw [degree_single_one]; norm_num)
  rw [map_sub, sub_eq_zero, coeff_C_mul] at h
  exact h

/-- The quadratic coefficients of `a * f`, for `f` of order at least two, are those of `f` scaled
by the constant term of `a`. -/
theorem coeff_quadratic_mul_of_mem (a f : Series K) (hf : f ∈ variableIdeal K ^ 2)
    {d : Fin 2 →₀ ℕ} (hd : d.degree = 2) :
    coeff d (a * f) = constantCoeff a * coeff d f := by
  have h := coeff_eq_zero_of_mem_pow (mul_sub_C_mul_mem_cube a f hf) (d := d)
    (by rw [hd]; norm_num)
  rw [map_sub, sub_eq_zero, coeff_C_mul] at h
  exact h

/-- The discriminant of the quadratic part of `a * F`, for `F` of order at least two, is the
square of the constant term of `a` times that of `F`. -/
theorem jetDiscriminant_mul_of_mem (a F : Series K) (hF : F ∈ variableIdeal K ^ 2) :
    jetDiscriminant (a * F) = constantCoeff a ^ 2 * jetDiscriminant F := by
  have h0 := coeff_quadratic_mul_of_mem a F hF (d := Finsupp.single 0 2) (by simp)
  have h1 := coeff_quadratic_mul_of_mem a F hF
    (d := Finsupp.single 0 1 + Finsupp.single 1 1) (degree_single_add_single 0 1)
  have h2 := coeff_quadratic_mul_of_mem a F hF (d := Finsupp.single 1 2) (by simp)
  simp only [jetDiscriminant, quadraticCoefficient0, quadraticCoefficient1,
    quadraticCoefficient2, h0, h1, h2]
  ring

/-- The constant term of a second partial derivative is the corresponding quadratic
coefficient, with multiplicity. -/
theorem constantCoeff_pderiv_pderiv (G : Series K) (i j : Fin 2) :
    constantCoeff (pderiv K i (pderiv K j G)) =
      coeff (Finsupp.single i 1 + Finsupp.single j 1) G * ((Finsupp.single i 1 : Fin 2 →₀ ℕ) j + 1) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

/-- **The Hessian determinant at the origin is minus the discriminant of the quadratic part.** -/
theorem constantCoeff_hessian (G : Series K) :
    constantCoeff (pderiv K 0 (pderiv K 0 G) * pderiv K 1 (pderiv K 1 G) -
      pderiv K 0 (pderiv K 1 G) * pderiv K 1 (pderiv K 0 G)) = - jetDiscriminant G := by
  rw [map_sub, map_mul, map_mul, constantCoeff_pderiv_pderiv, constantCoeff_pderiv_pderiv,
    constantCoeff_pderiv_pderiv, constantCoeff_pderiv_pderiv]
  have e00 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 0 1 : Fin 2 →₀ ℕ) =
      Finsupp.single 0 2 := by rw [← Finsupp.single_add]
  have e11 : (Finsupp.single (1 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) =
      Finsupp.single 1 2 := by rw [← Finsupp.single_add]
  have e10 : (Finsupp.single (1 : Fin 2) 1 + Finsupp.single 0 1 : Fin 2 →₀ ℕ) =
      Finsupp.single 0 1 + Finsupp.single 1 1 := add_comm _ _
  rw [e00, e11, e10]
  simp only [jetDiscriminant, quadraticCoefficient0, quadraticCoefficient1,
    quadraticCoefficient2, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
      (show (0 : Fin 2) ≠ 1 by decide), Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  push_cast
  ring

end Coefficients

/-- Membership in the square of the variable ideal: vanishing constant and linear terms. -/
theorem mem_variableIdeal_sq_iff (f : Series K) :
    f ∈ variableIdeal K ^ 2 ↔ constantCoeff f = 0 ∧ coeff (Finsupp.single 0 1) f = 0 ∧
      coeff (Finsupp.single 1 1) f = 0 := by
  rw [Algebra.NodeFieldCotangentGeneratorsJet.mem_variableSquare_iff]
  constructor
  · intro h
    refine ⟨?_, congrArg (fun p => p.2 0) h, congrArg (fun p => p.2 1) h⟩
    have h' : coeff 0 f = 0 := congrArg Prod.fst h
    rwa [coeff_zero_eq_constantCoeff_apply] at h'
  · rintro ⟨hc, h0, h1⟩
    have hc' : coeff 0 f = 0 := by rwa [coeff_zero_eq_constantCoeff_apply]
    apply Prod.ext
    · exact hc'
    · funext k
      fin_cases k
      · exact h0
      · exact h1

section Smooth

/-- If `G` has no constant term and a nonzero linear coefficient, then in `K[[x, y]]/(G)` the
maximal ideal is generated by the image of the other variable. -/
theorem maximalIdeal_equation_eq_span (G : Series K) (hc : constantCoeff G = 0) (i : Fin 2)
    (hi : coeff (Finsupp.single i 1) G ≠ 0) :
    letI := equationLocalRing K G hc
    maximalIdeal (Equation G) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {G}) (X (if i = 0 then 1 else 0))} := by
  let := equationLocalRing K G hc
  have := equationNoetherian K G
  set j : Fin 2 := if i = 0 then 1 else 0 with hj
  have hij : ∀ k : Fin 2, k = i ∨ k = j := by
    intro k; fin_cases i <;> fin_cases k <;> simp [hj]
  have hji : j ≠ i := by fin_cases i <;> simp [hj]
  let π := Ideal.Quotient.mk (Ideal.span {G})
  set c := coeff (Finsupp.single i 1) G
  set d := coeff (Finsupp.single j 1) G
  -- `G - c Xᵢ - d Xⱼ` has order at least two
  have hcoeff : ∀ k : Fin 2, coeff (Finsupp.single k 1) (G - (C c * X i + C d * X j)) = 0 := by
    intro k
    rcases hij k with rfl | rfl
    · simp [coeff_X, c, Finsupp.single_left_inj, hji.symm, coeff_C_mul]
    · simp [coeff_X, d, Finsupp.single_left_inj, hji, coeff_C_mul]
  have hr : G - (C c * X i + C d * X j) ∈ variableIdeal K ^ 2 := by
    rw [mem_variableIdeal_sq_iff]
    exact ⟨by simp [hc], hcoeff 0, hcoeff 1⟩
  set m := maximalIdeal (Equation G)
  have hm : m = (variableIdeal K).map π := equation_maximalIdeal K G hc
  have hXi : π (X i) ∈ Ideal.span {π (X j)} ⊔ m ^ 2 := by
    have hrel : π (C c * X i) = - (π (C d * X j) + π (G - (C c * X i + C d * X j))) := by
      have h0 : π G = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [map_sub, h0, map_add]; ring
    have hcX : π (X i) = π (C c⁻¹) * π (C c * X i) := by
      rw [← map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul]
    rw [hcX, hrel]
    apply Ideal.mul_mem_left
    apply neg_mem
    apply Ideal.add_mem
    · apply Ideal.mem_sup_left
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · apply Ideal.mem_sup_right
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
  have hle : m ≤ Ideal.span {π (X j)} ⊔ m • m := by
    have hspan : m = Ideal.span (π '' Set.range X) := by rw [hm, Ideal.map_span]
    conv_lhs => rw [hspan]
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rcases hij k with rfl | rfl
    · rw [Ideal.smul_eq_mul, ← pow_two]; exact hXi
    · exact Ideal.mem_sup_left (Ideal.subset_span rfl)
  have hmj : Ideal.span {π (X j)} ≤ m := by
    rw [Ideal.span_le, Set.singleton_subset_iff, hm]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine le_antisymm ?_ hmj
  have := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (maximalIdeal_le_jacobson _) hle
  exact this

/-- **Smooth formal plane germs.** If `G` has no constant term and some nonzero linear
coefficient, the maximal ideal of `K[[x, y]]/(G)` has span rank at most one. -/
theorem spanFinrank_maximalIdeal_equation_le_one (G : Series K) (hc : constantCoeff G = 0)
    (i : Fin 2) (hi : coeff (Finsupp.single i 1) G ≠ 0) :
    letI := equationLocalRing K G hc
    (maximalIdeal (Equation G)).spanFinrank ≤ 1 := by
  let := equationLocalRing K G hc
  rw [maximalIdeal_equation_eq_span G hc i hi]
  calc (Ideal.span {Ideal.Quotient.mk (Ideal.span {G}) (X (if i = 0 then 1 else 0))}).spanFinrank
      ≤ ({Ideal.Quotient.mk (Ideal.span {G}) (X (if i = 0 then 1 else 0))} : Set _).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)
    _ = 1 := Set.ncard_singleton _

end Smooth

section Node

variable [IsAlgClosed K]

/-- **Formal Morse lemma for plane germs.** Over an algebraically closed field, a series without
constant and linear terms whose quadratic part has nonzero discriminant defines the formal
ordinary double point: `K[[x, y]]/(G) ≅ K[[u, v]]/(uv)`. -/
def equationEquivFormalUV (G : Series K) (hc : constantCoeff G = 0)
    (h0 : coeff (Finsupp.single 0 1) G = 0) (h1 : coeff (Finsupp.single 1 1) G = 0)
    (hΔ : jetDiscriminant G ≠ 0) : Equation G ≃ₐ[K] FormalUV K :=
  (equationQuotientEquiv G hc h0 h1 hΔ).trans
    ((Ideal.quotientEquivAlgOfEq K (by
      rw [Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply])).trans
      (Algebra.NodeFieldSeriesJetQuadratic.splitEquationEquiv K K G hΔ))

end Node

section Kernel

variable {C : Type v} [CommRing C] [IsLocalRing C] [Algebra K C]

/-- An algebra isomorphism of local `K`-algebras induces isomorphisms of all jet quotients. -/
def jetAlgEquiv {D : Type*} [CommRing D] [IsLocalRing D] [Algebra K D] (e : C ≃ₐ[K] D) (n : ℕ) :
    (C ⧸ maximalIdeal C ^ n) ≃ₐ[K] (D ⧸ maximalIdeal D ^ n) :=
  Ideal.quotientEquivAlg _ _ e (by
    rw [Ideal.map_pow]
    exact (congrArg (fun I => I ^ n) (map_ringEquiv_maximalIdeal e.toRingEquiv)).symm)

theorem finrank_jet_formalUV (n : ℕ) :
    Module.finrank K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) = 2 * n - 1 := by
  cases n with
  | zero =>
    have : Subsingleton (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    rw [Module.finrank_zero_of_subsingleton]
  | succ n =>
    rw [Algebra.NodeFieldUVJetLength.nativeJet_finrank_succ]
    omega

theorem finiteDimensional_jet_formalUV (n : ℕ) :
    FiniteDimensional K (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ n) := by
  cases n with
  | zero =>
    have : Subsingleton (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    infer_instance
  | succ n =>
    apply Module.finite_of_finrank_pos
    rw [Algebra.NodeFieldUVJetLength.nativeJet_finrank_succ]
    omega

theorem finrank_jet_of_algEquiv (e : C ≃ₐ[K] FormalUV K) (n : ℕ) :
    Module.finrank K (C ⧸ maximalIdeal C ^ n) = 2 * n - 1 := by
  rw [(jetAlgEquiv e n).toLinearEquiv.finrank_eq, finrank_jet_formalUV]

theorem finiteDimensional_jet_of_algEquiv (e : C ≃ₐ[K] FormalUV K) (n : ℕ) :
    FiniteDimensional K (C ⧸ maximalIdeal C ^ n) := by
  have := finiteDimensional_jet_formalUV (K := K) n
  exact Module.Finite.equiv (jetAlgEquiv e n).symm.toLinearEquiv

/-- The kernel of a surjection `K[[x, y]] → C` onto a local ring with three-dimensional
second jet lies in the square of the variable ideal. -/
theorem ker_le_variableIdeal_sq (ψ : Series K →ₐ[K] C) (hψ : Function.Surjective ψ)
    [FiniteDimensional K (C ⧸ maximalIdeal C ^ 2)]
    (h2 : Module.finrank K (C ⧸ maximalIdeal C ^ 2) = 3) :
    RingHom.ker ψ ≤ variableIdeal K ^ 2 := by
  intro F hF
  have hsrc : Module.finrank K (Series K ⧸ maximalIdeal (Series K) ^ 2) = 3 := by
    rw [← variableIdeal_eq_maximalIdeal]
    exact Algebra.NodeFieldCotangentGeneratorsJet.source_finrank K
  have : FiniteDimensional K (Series K ⧸ maximalIdeal (Series K) ^ 2) :=
    Module.finite_of_finrank_pos (by rw [hsrc]; norm_num)
  have hinj := Algebra.NodeFieldJetRigidity.jetMap_injective_of_finrank_eq K ψ hψ 2
    (hsrc.trans h2.symm)
  have hz : Algebra.NodeFieldJetRigidity.jetMap K ψ hψ 2 (Ideal.Quotient.mk _ F) = 0 := by
    rw [Algebra.NodeFieldJetRigidity.jetMap_mk, RingHom.mem_ker.mp hF, map_zero]
  have := hinj (hz.trans (map_zero _).symm)
  rw [variableIdeal_eq_maximalIdeal]
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

variable [IsAlgClosed K]

/-- **Kernels of presentations of the formal node are principal.** If `ψ : K[[x, y]] → C` is a
surjective `K`-algebra map onto `C ≅ K[[u, v]]/(uv)`, then its kernel is generated by one series
`F` of order exactly two whose quadratic part has nonzero discriminant. -/
theorem exists_ker_eq_span_of_formalUV (ψ : Series K →ₐ[K] C) (hψ : Function.Surjective ψ)
    (e : C ≃ₐ[K] FormalUV K) :
    ∃ F : Series K, RingHom.ker ψ = Ideal.span {F} ∧ F ∈ variableIdeal K ^ 2 ∧
      F ∉ variableIdeal K ^ 3 ∧ jetDiscriminant F ≠ 0 := by
  have := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  have hjC := finiteDimensional_jet_of_algEquiv e
  have hV : (variableIdeal K).map ψ.toRingHom = maximalIdeal C := by
    rw [variableIdeal_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective ψ.toRingHom hψ
  have h3 : Module.finrank K (C ⧸ maximalIdeal C ^ 3) = 5 := finrank_jet_of_algEquiv e 3
  obtain ⟨F, hF, hF3⟩ := Algebra.NodeFieldCubicRelation.exists_relation_not_mem_cube K C ψ hV hψ h3
  have hF2 : F ∈ variableIdeal K ^ 2 :=
    ker_le_variableIdeal_sq ψ hψ (finrank_jet_of_algEquiv e 2) (RingHom.mem_ker.mpr hF)
  let e3 : TensorProduct K K (C ⧸ maximalIdeal C ^ 3) ≃ₐ[K]
      (FormalUV K ⧸ maximalIdeal (FormalUV K) ^ 3) :=
    (Algebra.TensorProduct.lid K _).trans (jetAlgEquiv e 3)
  have hΔ := Algebra.NodeFieldGeometricCubicMap.relation_discriminant_ne_zero K K C ψ hV e3 hψ F
    hF hF2 hF3
  refine ⟨F, ?_, hF2, hF3, hΔ⟩
  -- the induced map `K[[x, y]]/(F) → C` is an isomorphism by jet rigidity
  have hc : constantCoeff F = 0 := by
    have := ((Algebra.NodeFieldCotangentGeneratorsJet.mem_variableSquare_iff K F).mp hF2)
    exact congrArg Prod.fst this
  have h0 : coeff (Finsupp.single 0 1) F = 0 := by
    have := ((Algebra.NodeFieldCotangentGeneratorsJet.mem_variableSquare_iff K F).mp hF2)
    exact congrArg (fun p => p.2 0) this
  have h1 : coeff (Finsupp.single 1 1) F = 0 := by
    have := ((Algebra.NodeFieldCotangentGeneratorsJet.mem_variableSquare_iff K F).mp hF2)
    exact congrArg (fun p => p.2 1) this
  let := equationLocalRing K F hc
  let := equationNoetherian K F
  let eF := equationEquivFormalUV F hc h0 h1 hΔ
  have hjE := finiteDimensional_jet_of_algEquiv eF
  have hle : Ideal.span {F} ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.mpr hF
  let p : Equation F →ₐ[K] C := Ideal.Quotient.liftₐ (Ideal.span {F}) ψ (fun a ha => hle ha)
  have hp : Function.Surjective p := by
    intro c
    obtain ⟨a, rfl⟩ := hψ c
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hdim : ∀ n : ℕ, Module.finrank K (Equation F ⧸ maximalIdeal (Equation F) ^ n) =
      Module.finrank K (C ⧸ maximalIdeal C ^ n) := fun n => by
    rw [finrank_jet_of_algEquiv eF, finrank_jet_of_algEquiv e]
  have hinj := Algebra.NodeFieldJetRigidity.injective_of_all_jet_finrank_eq K p hp hdim
  refine le_antisymm (fun a ha => ?_) hle
  have h : p (Ideal.Quotient.mk _ a) = p 0 := by
    rw [map_zero]
    exact RingHom.mem_ker.mp ha
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj h)

/-- **Equations of the formal node.** If `K[[x, y]]/(G) ≅ K[[u, v]]/(uv)` for a series `G` without
constant term, then `G` has order exactly two and the discriminant of its quadratic part is
nonzero. -/
theorem jetDiscriminant_ne_zero_of_equationEquiv (G : Series K) (e : Equation G ≃ₐ[K] FormalUV K)
    (hc : constantCoeff G = 0) :
    G ∈ variableIdeal K ^ 2 ∧ jetDiscriminant G ≠ 0 := by
  let := equationLocalRing K G hc
  obtain ⟨F, hker, hF2, hF3, hΔ⟩ :=
    exists_ker_eq_span_of_formalUV (Ideal.Quotient.mkₐ K (Ideal.span {G}))
      (Ideal.Quotient.mkₐ_surjective K _) e
  have hk : RingHom.ker (Ideal.Quotient.mkₐ K (Ideal.span {G})) = Ideal.span {G} := by
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [hk] at hker
  have hG : G ∈ Ideal.span {F} := hker ▸ Ideal.subset_span rfl
  have hFG : F ∈ Ideal.span {G} := hker ▸ Ideal.subset_span rfl
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hG
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hFG
  have hF0 : F ≠ 0 := fun h => hF3 (h ▸ Ideal.zero_mem _)
  -- `a` is a unit: `F = b a F` in the domain `K[[x, y]]`
  have hab : b * a = 1 := by
    have : (b * a - 1) * F = 0 := by rw [sub_mul, mul_assoc, ha, hb, one_mul, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hF0
  have hca : constantCoeff a ≠ 0 := by
    intro h
    have := congrArg constantCoeff hab
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  refine ⟨ha ▸ Ideal.mul_mem_left _ _ hF2, ?_⟩
  rw [← ha, jetDiscriminant_mul_of_mem a F hF2]
  exact mul_ne_zero (pow_ne_zero 2 hca) hΔ

end Kernel

end DeJongAlterations.StableModification.Curves.SemistableOpen
