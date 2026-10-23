import DeJongAlterations.StableModification.Curves.SemistableNormalLocal
import DeJongAlterations.StableModification.Curves.StandardModels

/-!
# Normality of a hypersurface at a critical point with smooth generic fibre

Let `R` be an integrally closed domain, `P` étale over `R[X₀, X₁]` and `g ∈ P` with invertible
Hessian. At a prime `Q` of `T = P/(g)` containing the partial derivatives of `g` (a node), the
local ring `T_Q` is an integrally closed domain, provided `T` is formally smooth over `R` at the
primes `w ⊆ Q` of the generic fibre (`isDomain_isIntegrallyClosed_hypersurface`). This is the
local form of the normality of semi-stable curves with smooth generic fibre (Temkin, T:2966–2967;
blueprint `sm-semistable-normal.tex`).

The proof uses the node chart (`exists_nodeChart`) over the local ring `O'` of the critical locus
`O = P/(∂₀g, ∂₁g)` at `Q`: a ring `W` étale over `O' ⊗_R T` and over `O'[u, v]/(uv - c)`,
`c = -g|_{O'}`. Here:

* `O'` is an integrally closed domain, since `O` is étale over `R` (lane SS1,
  `isDomain_isIntegrallyClosed_localization_of_etale`);
* `c ≠ 0`: otherwise `g` vanishes on the generic point `w` of `Spec O'`, a critical point of `g` in
  the generic fibre, and formal smoothness of `T_w` would force `g = 0` near `w`
  (`algebraMap_eq_zero_of_formallySmooth`), contradicting the invertibility of the Hessian
  (`hessian_algebraMap_eq_zero`);
* so `O'[u, v]/(uv - c)` is an integrally closed domain (Codex, `node_isIntegrallyClosed`), the
  local rings of `W` are integrally closed domains, and normality descends along the faithfully
  flat local map `T_Q → W_𝔔` (`isDomain_isIntegrallyClosed_of_faithfullyFlat`).
-/

noncomputable section

open TensorProduct IsLocalRing

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen (coord planeDerivation planeDerivation_coord hessian planeDerivation_map
  hessian_map)

universe u

section Descent

/-- **Normality descends along faithfully flat maps**: if `A → A'` is faithfully flat and `A'` is
an integrally closed domain, so is `A` (`a ∈ bA' ∩ A = bA`). -/
theorem isDomain_isIntegrallyClosed_of_faithfullyFlat {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.FaithfullyFlat A A'] [IsDomain A'] [IsIntegrallyClosed A'] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A A') := FaithfulSMul.algebraMap_injective A A'
  have : IsDomain A := hinj.isDomain _
  refine ⟨this, ?_⟩
  let K := FractionRing A
  let L := FractionRing A'
  let φ : K →+* L := IsLocalization.map L (algebraMap A A')
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hφ : φ.comp (algebraMap A K) = (algebraMap A' L).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  have hint : IsIntegral A' (φ (IsLocalization.mk' K a b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap A A'), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hφ, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨a', ha'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hb : algebraMap A' L (algebraMap A A' b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A' L)).mpr
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero b.2))
  have hab : a' * algebraMap A A' b = algebraMap A A' a := by
    apply IsFractionRing.injective A' L
    rw [map_mul, ha', ← RingHom.comp_apply, ← RingHom.comp_apply, ← hφ, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hmem : a ∈ Ideal.span {(b : A)} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := A') (Ideal.span {(b : A)}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨a', hab⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨c, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hc]

/-- **Normality descends along flat maps, locally**: if `B → W` is flat and the local ring of `W`
at `𝔔` is an integrally closed domain, so is the local ring of `B` at the prime under `𝔔`. -/
theorem isDomain_isIntegrallyClosed_localization_of_flat {B W : Type*} [CommRing B] [CommRing W]
    [Algebra B W] [Module.Flat B W] (𝔔 : Ideal W) [𝔔.IsPrime] (p : Ideal B) [p.IsPrime]
    (hp : 𝔔.comap (algebraMap B W) = p) [IsDomain (Localization.AtPrime 𝔔)]
    [IsIntegrallyClosed (Localization.AtPrime 𝔔)] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  subst hp
  let := Localization.AtPrime.algebraOfLiesOver (𝔔.under B) 𝔔
  have : IsLocalHom (algebraMap (Localization.AtPrime (𝔔.under B)) (Localization.AtPrime 𝔔)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom _ 𝔔 (algebraMap B W) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime (𝔔.under B)) (Localization.AtPrime 𝔔) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isDomain_isIntegrallyClosed_of_faithfullyFlat (A' := Localization.AtPrime 𝔔)

end Descent

section Kernel

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P] (w : Ideal P)
  [w.IsPrime]

/-- Derivations preserve the kernel of a localization at a prime: if `s x = 0` with `s ∉ w`, then
`s² D(x) = 0`. -/
theorem derivation_algebraMap_eq_zero (D : Derivation R P P) {x : P}
    (hx : algebraMap P (Localization.AtPrime w) x = 0) :
    algebraMap P (Localization.AtPrime w) (D x) = 0 := by
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff w.primeCompl _ x).mp hx
  rw [IsLocalization.map_eq_zero_iff w.primeCompl]
  refine ⟨⟨s * s, w.primeCompl.mul_mem hs hs⟩, ?_⟩
  have h := congrArg D hsx
  rw [Derivation.leibniz, map_zero, smul_eq_mul, smul_eq_mul] at h
  change s * s * D x = 0
  simp only at hsx
  linear_combination s * h - D s * hsx

variable [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) R) P]

/-- If `g` vanishes near `w`, so does its Hessian. -/
theorem hessian_algebraMap_eq_zero {g : P} (hg : algebraMap P (Localization.AtPrime w) g = 0) :
    algebraMap P (Localization.AtPrime w) (hessian R P g) = 0 := by
  have h1 : ∀ i, algebraMap P (Localization.AtPrime w) (planeDerivation R P i g) = 0 :=
    fun i => derivation_algebraMap_eq_zero w _ hg
  have h2 : ∀ i j, algebraMap P (Localization.AtPrime w)
      (planeDerivation R P j (planeDerivation R P i g)) = 0 :=
    fun i j => derivation_algebraMap_eq_zero w _ (h1 i)
  simp only [hessian, map_sub, map_mul, h2, mul_zero, sub_zero]

end Kernel

section Smooth

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) R) P]

/-- **A formally smooth hypersurface is not singular.** Let `w` be a prime of `P` containing `g`
and its partial derivatives. If the local ring of `P/(g)` at `w` is formally smooth over `R`, then
`g` vanishes in `P_w`. (Lift the identity of `P_w/(g)` to `P_w/(g²)`; the difference with the
canonical map is a derivation `D` with `D g = -g`, and the chain rule
`D g = ∂₀g · D u₀ + ∂₁g · D u₁` puts `g` into `𝔪 · (g)`.) -/
theorem algebraMap_eq_zero_of_formallySmooth (g : P) (wT : Ideal (P ⧸ Ideal.span {g}))
    [wT.IsPrime] (hcrit : ∀ i, Ideal.Quotient.mk _ (planeDerivation R P i g) ∈ wT)
    [Algebra.FormallySmooth R (Localization.AtPrime wT)] :
    algebraMap P (Localization.AtPrime (wT.comap (Ideal.Quotient.mk (Ideal.span {g})))) g = 0 := by
  set T := P ⧸ Ideal.span {g}
  set w := wT.comap (Ideal.Quotient.mk (Ideal.span {g})) with hwT
  have hgw : g ∈ w := by
    rw [hwT, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)]
    exact wT.zero_mem
  set Pw := Localization.AtPrime w
  set gw := algebraMap P Pw g
  set N : Ideal Pw := Ideal.span {gw}
  have hN2 : N ^ 2 ≤ N := Ideal.pow_le_self two_ne_zero
  -- the map `T_w → P_w/(g)`
  let βT : T →ₐ[R] Pw ⧸ N := Ideal.Quotient.liftₐ (Ideal.span {g})
    ((Ideal.Quotient.mkₐ R N).comp (IsScalarTower.toAlgHom R P Pw)) (fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk,
        map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self gw), mul_zero])
  have hβT : ∀ p, βT (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk N (algebraMap P Pw p) :=
    fun _ => rfl
  have hunit : ∀ y : wT.primeCompl, IsUnit (βT y) := by
    rintro ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hp : p ∉ w := hy
    rw [hβT]
    exact (IsLocalization.map_units Pw (⟨p, hp⟩ : w.primeCompl)).map _
  let β : Localization.AtPrime wT →ₐ[R] Pw ⧸ N := IsLocalization.liftAlgHom hunit
  -- the lift to `P_w/(g²)`
  let fac : Pw ⧸ N ^ 2 →ₐ[R] Pw ⧸ N := Ideal.Quotient.factorₐ R hN2
  have hfac : Function.Surjective fac := Ideal.Quotient.factor_surjective hN2
  have hfacker : RingHom.ker (fac : Pw ⧸ N ^ 2 →+* Pw ⧸ N) = N.map (Ideal.Quotient.mk (N ^ 2)) :=
    Ideal.Quotient.factor_ker hN2
  have hsq : N.map (Ideal.Quotient.mk (N ^ 2)) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hnil : IsNilpotent (RingHom.ker (fac : Pw ⧸ N ^ 2 →+* Pw ⧸ N)) :=
    ⟨2, by rw [hfacker, hsq, Ideal.zero_eq_bot]⟩
  let s := Algebra.FormallySmooth.liftOfSurjective β fac hfac hnil
  have hs : ∀ x, fac (s x) = β x := Algebra.FormallySmooth.liftOfSurjective_apply β fac hfac hnil
  -- the two maps `P → P_w/(g²)` and their difference
  set C := Pw ⧸ N ^ 2
  let θ : P →ₐ[R] Localization.AtPrime wT :=
    (IsScalarTower.toAlgHom R T (Localization.AtPrime wT)).comp (Ideal.Quotient.mkₐ R _)
  let φ : P →ₐ[R] C := s.comp θ
  let ρ : P →ₐ[R] C := IsScalarTower.toAlgHom R P C
  have hφg : φ g = 0 := by
    change s (algebraMap T _ (Ideal.Quotient.mk _ g)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g), map_zero, map_zero]
  have hdiff : ∀ x, φ x - ρ x ∈ N.map (Ideal.Quotient.mk (N ^ 2)) := by
    intro x
    rw [← hfacker, RingHom.mem_ker, map_sub]
    change fac (s (θ x)) - fac (Ideal.Quotient.mk _ (algebraMap P Pw x)) = 0
    rw [hs]
    change IsLocalization.lift hunit (algebraMap T _ (Ideal.Quotient.mk _ x)) - _ = 0
    rw [IsLocalization.lift_eq]
    exact sub_self _
  have hprod : ∀ x y, (φ x - ρ x) * (φ y - ρ y) = 0 := by
    intro x y
    have : (φ x - ρ x) * (φ y - ρ y) ∈
        N.map (Ideal.Quotient.mk (N ^ 2)) * N.map (Ideal.Quotient.mk (N ^ 2)) :=
      Ideal.mul_mem_mul (hdiff x) (hdiff y)
    rw [(sq _).symm.trans hsq] at this
    exact Ideal.mem_bot.mp this
  let D : Derivation R P C :=
    { toLinearMap := φ.toLinearMap - ρ.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul, Algebra.smul_def]
        have hρ : ∀ x, algebraMap P C x = ρ x := fun _ => rfl
        rw [hρ, hρ]
        linear_combination hprod a b }
  have hD : ∀ x, D x = φ x - ρ x := fun _ => rfl
  -- the chain rule
  have hchain := derivation_eq_sum R P D g
  rw [hD, hφg, zero_sub, Fin.sum_univ_two] at hchain
  -- `D uᵢ ∈ (g)`
  have hspan : N.map (Ideal.Quotient.mk (N ^ 2)) = Ideal.span {Ideal.Quotient.mk (N ^ 2) gw} := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨e₀, he₀⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hdiff (coord R P 0))
  obtain ⟨e₁, he₁⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hdiff (coord R P 1))
  obtain ⟨k₀, rfl⟩ := Ideal.Quotient.mk_surjective e₀
  obtain ⟨k₁, rfl⟩ := Ideal.Quotient.mk_surjective e₁
  rw [← hD] at he₀ he₁
  rw [← he₀, ← he₁, Algebra.smul_def, Algebra.smul_def] at hchain
  -- lift to `P_w`
  set m := algebraMap P Pw (planeDerivation R P 0 g) * k₀ +
    algebraMap P Pw (planeDerivation R P 1 g) * k₁
  have hm : m ∈ maximalIdeal Pw := by
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Pw w _).mpr (hcrit 0 : _)
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Pw w _).mpr (hcrit 1 : _)
  have hgwm : gw ∈ maximalIdeal Pw := (IsLocalization.AtPrime.to_map_mem_maximal_iff Pw w _).mpr hgw
  have hmk : Ideal.Quotient.mk (N ^ 2) (gw * (1 + m)) = 0 := by
    have hρ : ∀ x, ρ x = Ideal.Quotient.mk (N ^ 2) (algebraMap P Pw x) := fun _ => rfl
    have halg : ∀ x, algebraMap P C x = Ideal.Quotient.mk (N ^ 2) (algebraMap P Pw x) :=
      fun _ => rfl
    rw [hρ, halg, halg] at hchain
    simp only [m, map_mul, map_add, map_one]
    rw [← neg_eq_zero, ← sub_eq_zero.mpr hchain]
    ring
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmk
  obtain ⟨r, hr⟩ := hmk
  have hu : IsUnit (1 + m - r * gw) := by
    by_contra h
    have h1 : 1 + m - r * gw ∈ maximalIdeal Pw := h
    apply (maximalIdeal.isMaximal Pw).ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : Pw) = (1 + m - r * gw) - m + r * gw := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h1 hm) (Ideal.mul_mem_left _ _ hgwm)
  have h0 : gw * (1 + m - r * gw) = 0 := by linear_combination -hr
  exact (hu.mul_left_eq_zero).mp h0

end Smooth

section Hypersurface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  (P : Type u) [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.Etale (MvPolynomial (Fin 2) R) P]

omit [IsDomain R] [IsIntegrallyClosed R] in
/-- The base change `T → O ⊗_R T` along a flat `R → O` is flat. -/
theorem flat_includeRight (O T : Type u) [CommRing O] [Algebra R O] [Module.Flat R O]
    [CommRing T] [Algebra R T] :
    (Algebra.TensorProduct.includeRight : T →ₐ[R] O ⊗[R] T).toRingHom.Flat := by
  have h : (Algebra.TensorProduct.includeRight : T →ₐ[R] O ⊗[R] T).toRingHom =
      (Algebra.TensorProduct.comm R T O).toRingHom.comp (algebraMap T (T ⊗[R] O)) := by
    ext t
    rfl
  rw [h]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R T O).bijective)

open DeJongAlterations.Algebra.NodeBlowupChart in
/-- **Normality of a hypersurface at a critical point with smooth generic fibre.** Let `R` be an
integrally closed domain, `P` étale over `R[X₀, X₁]`, `g ∈ P` with invertible Hessian and `Q` a
prime of `P/(g)` containing `∂₀g, ∂₁g`. If `P/(g)` is formally smooth over `R` at every prime
`w ⊆ Q` lying over the generic point of `R`, then the local ring of `P/(g)` at `Q` is an
integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_hypersurface (g : P) (hg : IsUnit (hessian R P g))
    (Q : Ideal (P ⧸ Ideal.span {g})) [Q.IsPrime]
    (hcrit : ∀ i, Ideal.Quotient.mk _ (planeDerivation R P i g) ∈ Q)
    (hgen : ∀ (w : Ideal (P ⧸ Ideal.span {g})) [w.IsPrime], w ≤ Q →
      w.comap (algebraMap R (P ⧸ Ideal.span {g})) = ⊥ →
      Algebra.FormallySmooth R (Localization.AtPrime w)) :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  set T := P ⧸ Ideal.span {g}
  set Q₀ := Q.comap (Ideal.Quotient.mk (Ideal.span {g})) with hQ₀
  -- the critical locus `O` and its local ring `O'` at `Q`
  have : Algebra.Etale R (P ⧸ critIdeal R P g) := etale_critical R P g hg
  set O := P ⧸ critIdeal R P g
  have hcritQ₀ : critIdeal R P g ≤ Q₀ := by
    rw [critIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hcrit 0
    · exact hcrit 1
  set 𝔮 := Q₀.map (Ideal.Quotient.mk (critIdeal R P g))
  have : 𝔮.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hcritQ₀)
  have h𝔮 : ∀ p, Ideal.Quotient.mk (critIdeal R P g) p ∈ 𝔮 ↔ p ∈ Q₀ := by
    intro p
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hcritQ₀]
  set O' := Localization.AtPrime 𝔮
  obtain ⟨hO'dom, hO'int⟩ := isDomain_isIntegrallyClosed_localization_of_etale R 𝔮
  let π : P →ₐ[R] O' := (IsScalarTower.toAlgHom R O O').comp (Ideal.Quotient.mkₐ R _)
  have hπ : ∀ i, π (planeDerivation R P i g) = 0 := by
    intro i
    change algebraMap O O' (Ideal.Quotient.mk _ _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
    fin_cases i
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hπmem : ∀ p, π p ∈ maximalIdeal O' ↔ p ∈ Q₀ := by
    intro p
    change algebraMap O O' _ ∈ _ ↔ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O' 𝔮]
    exact h𝔮 p
  have hgQ₀ : g ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)]
    exact Q.zero_mem
  have hπg : π g ∈ maximalIdeal O' := (hπmem g).mpr hgQ₀
  obtain ⟨W, _, _, _, _, _, 𝔔, _, -, hPW, -, -⟩ :=
    exists_nodeChart R P O' g hg π hπ (maximalIdeal O') hπg
  -- the parameter `c = -π g` of the node is nonzero
  have hc : -π g ≠ 0 := by
    rw [neg_ne_zero]
    intro hπ0
    set w₀ := RingHom.ker π.toRingHom
    have : w₀.IsPrime := RingHom.ker_isPrime _
    have hgw₀ : g ∈ w₀ := hπ0
    have hw₀Q₀ : w₀ ≤ Q₀ := fun p hp =>
      (hπmem p).mp (by rw [show π p = 0 from hp]; exact zero_mem _)
    have : Module.Flat R O' := Module.Flat.trans R O O'
    have hinj : Function.Injective (algebraMap R O') := FaithfulSMul.algebraMap_injective R O'
    set wT := w₀.map (Ideal.Quotient.mk (Ideal.span {g}))
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {g})) ≤ w₀ := by
      rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
      exact hgw₀
    have : wT.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hwT : wT.comap (Ideal.Quotient.mk _) = w₀ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    have hwTQ : wT ≤ Q := by
      rw [Ideal.map_le_iff_le_comap]
      exact hw₀Q₀
    have hwTR : wT.comap (algebraMap R T) = ⊥ := by
      ext r
      rw [Ideal.mem_comap, Ideal.mem_bot, IsScalarTower.algebraMap_apply R P T]
      change Ideal.Quotient.mk _ (algebraMap R P r) ∈ wT ↔ _
      rw [← Ideal.mem_comap, hwT]
      change π (algebraMap R P r) = 0 ↔ r = 0
      rw [AlgHom.commutes, map_eq_zero_iff _ hinj]
    have := hgen wT hwTQ hwTR
    have hcritw : ∀ i, Ideal.Quotient.mk (Ideal.span {g}) (planeDerivation R P i g) ∈ wT :=
      fun i => Ideal.mem_map_of_mem _ (hπ i)
    have h0 := algebraMap_eq_zero_of_formallySmooth g wT hcritw
    have hh := hessian_algebraMap_eq_zero (R := R) _ h0
    exact (hg.map (algebraMap P _)).ne_zero hh
  -- the node `O'[u, v]/(uv - c)` and the chart `W` are normal
  have : IsDomain (Node O' (-π g)) :=
    DeJongAlterations.Algebra.NodeDomain.nodeQuotient_isDomain _ hc
  have : IsIntegrallyClosed (Node O' (-π g)) :=
    DeJongAlterations.Algebra.NodeNormal.node_isIntegrallyClosed _ hc
  obtain ⟨hWdom, hWint⟩ := isDomain_isIntegrallyClosed_localization_of_etale (Node O' (-π g)) 𝔔
  -- descend along the flat map `T → W`
  have : Module.Flat R O' := Module.Flat.trans R O O'
  let : Algebra T W := ((algebraMap (O' ⊗[R] T) W).comp
    (Algebra.TensorProduct.includeRight : T →ₐ[R] O' ⊗[R] T).toRingHom).toAlgebra
  have : Module.Flat T W := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.comp (flat_includeRight R O' T)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply isDomain_isIntegrallyClosed_localization_of_flat 𝔔 Q
  ext t
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [Ideal.mem_comap]
  change algebraMap (O' ⊗[R] T) W ((1 : O') ⊗ₜ Ideal.Quotient.mk _ p) ∈ 𝔔 ↔ _
  rw [hPW, hπmem]
  rfl

end Hypersurface

end DeJongAlterations.StableModification.Curves.SemistableNormal
