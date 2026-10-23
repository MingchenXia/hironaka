import DeJongAlterations.StableModification.Curves.SemistableNormalAlgebra
import DeJongAlterations.Algebra.RegularLocalDomain

/-!
# Normality of a nodal family at a smooth point of a geometric fibre

Let `R` be an integrally closed domain, `B` a flat finitely presented `R`-algebra and
`z ⊂ K ⊗_R B` a closed point of a geometric fibre whose local ring has principal maximal ideal.
Lane SS2 presents `B_f` as a quotient of a surface `P` étale over `R[X₀, X₁]` in which the second
coordinate `u₁` vanishes. If the geometric local rings of `B_f` are one-dimensional, the kernel of
`P/(u₁) → B_f` vanishes near every closed point of every geometric fibre
(`exists_annihilator_of_coord_eq_zero`: the geometric local ring of `P/(u₁)` is a discrete
valuation ring mapping onto a one-dimensional ring, so the map is injective, and flatness of `B`
spreads this out, as in SS2's `exists_principal_kernel`). Hence `B_f` is, near such a point, a
localization of `P/(u₁)`, which is étale over `R[X₀, X₁]/(X₁) ≅ R[X₀]`, and so its local rings are
integrally closed domains (`exists_away_isIntegrallyClosed_of_spanFinrank_le_one`).
-/

noncomputable section

open IsLocalRing TensorProduct Polynomial

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen

universe u

section Line

variable (R : Type u) [CommRing R]

/-- `R[X₀, X₁]/(X₁) ≅ R[X]`. -/
def quotientXOneEquiv :
    (MvPolynomial (Fin 2) R ⧸ Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) R)}) ≃ₐ[R]
      R[X] :=
  AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![Polynomial.X, 0]) fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp)
    (Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 0)))
    (by
      apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, Polynomial.aeval_X, AlgHom.id_apply]
      change MvPolynomial.aeval ![Polynomial.X, 0] (MvPolynomial.X (0 : Fin 2)) = _
      rw [MvPolynomial.aeval_X]
      rfl)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · change Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 0))
          (MvPolynomial.aeval ![Polynomial.X, 0] (MvPolynomial.X (0 : Fin 2))) =
          Ideal.Quotient.mk _ (MvPolynomial.X 0)
        rw [MvPolynomial.aeval_X]
        exact Polynomial.aeval_X _
      · change Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 0))
          (MvPolynomial.aeval ![Polynomial.X, 0] (MvPolynomial.X (1 : Fin 2))) =
          Ideal.Quotient.mk _ (MvPolynomial.X 1)
        rw [MvPolynomial.aeval_X]
        change Polynomial.aeval _ (0 : R[X]) = _
        rw [map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm)

variable [IsDomain R] [IsIntegrallyClosed R]

instance : IsDomain (MvPolynomial (Fin 2) R ⧸ Ideal.span {MvPolynomial.X (R := R) (1 : Fin 2)}) :=
  (quotientXOneEquiv R).toRingEquiv.injective.isDomain (quotientXOneEquiv R).toRingEquiv.toRingHom

instance :
    IsIntegrallyClosed
      (MvPolynomial (Fin 2) R ⧸ Ideal.span {MvPolynomial.X (R := R) (1 : Fin 2)}) :=
  IsIntegrallyClosed.of_equiv (quotientXOneEquiv R).toRingEquiv.symm

end Line

section DimOne

/-- The local map induced by a surjection is surjective. -/
theorem localRingHom_surjective {T B : Type*} [CommRing T] [CommRing B] (ψ : T →+* B)
    (hψ : Function.Surjective ψ) (y : Ideal B) [y.IsPrime] :
    Function.Surjective (Localization.localRingHom (y.comap ψ) y ψ rfl) := by
  intro w
  obtain ⟨b, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq y.primeCompl w
  obtain ⟨t, rfl⟩ := hψ b
  obtain ⟨t', rfl⟩ := hψ s
  exact ⟨IsLocalization.mk' _ t (⟨t', hs⟩ : (y.comap ψ).primeCompl),
    Localization.localRingHom_mk' _ _ _ _ _ _⟩

/-- **Injectivity at a smooth point.** Let `ψ : T → B` be surjective with `T` Noetherian, `y` a
prime of `B` such that the maximal ideal of `T` at `ψ⁻¹ y` is principal and the local ring of `B`
at `y` is one-dimensional. Then the local map `T_{ψ⁻¹ y} → B_y` is injective: its source is a
regular local ring of dimension one, hence a domain, and a nonzero kernel would drop the
dimension. -/
theorem localRingHom_injective_of_ringKrullDim {T B : Type*} [CommRing T] [CommRing B]
    [IsNoetherianRing T] (ψ : T →+* B) (hψ : Function.Surjective ψ) (y : Ideal B) [y.IsPrime]
    (hle : (maximalIdeal (Localization.AtPrime (y.comap ψ))).spanFinrank ≤ 1)
    (hdim : ringKrullDim (Localization.AtPrime y) = 1) :
    Function.Injective (Localization.localRingHom (y.comap ψ) y ψ rfl) := by
  set p := y.comap ψ
  set A := Localization.AtPrime p
  set q := Localization.localRingHom p y ψ rfl
  have hq : Function.Surjective q := localRingHom_surjective ψ hψ y
  have hdimA1 : 1 ≤ ringKrullDim A := hdim ▸ ringKrullDim_le_of_surjective q hq
  have hreg : IsRegularLocalRing A := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := A)
    ((by exact_mod_cast hle : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) ≤ 1).trans hdimA1)
  have hdimA2 : ringKrullDim A ≤ 1 :=
    (ringKrullDim_le_spanFinrank_maximalIdeal A).trans (by exact_mod_cast hle)
  have : IsDomain A := DeJongAlterations.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing A
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
  let q' : A ⧸ Ideal.span {x} →+* Localization.AtPrime y :=
    Ideal.Quotient.lift _ q fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hx, mul_zero]
  have hq' : Function.Surjective q' := fun w => by
    obtain ⟨a, rfl⟩ := hq w
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have h2 := ringKrullDim_le_of_surjective q' hq'
  rw [hdim] at h2
  have h3 : (1 : WithBot ℕ∞) + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h1.trans hdimA2)
  exact absurd h3 (by decide)

end DimOne

section Kernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {P : Type u} [CommRing P] [Algebra R P]
  [Algebra (MvPolynomial (Fin 2) R) P] [IsScalarTower R (MvPolynomial (Fin 2) R) P]
  [Algebra.Etale (MvPolynomial (Fin 2) R) P]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]
  (φ : P →ₐ[R] B) (hφ : Function.Surjective φ)
  {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
  (z : Ideal (K ⊗[R] B)) [z.IsMaximal]

include hφ in
/-- **Near a one-dimensional smooth geometric point the kernel is generated by `u₁`.** Let
`φ : P → B` be a surjection from an algebra étale over `R[X₀, X₁]` with `φ(u₁) = 0`, `B` flat and
finitely presented over `R`, and `z` a closed point of `K ⊗_R B` whose local ring is
one-dimensional. Then some `h ∈ P` outside the point under `z` satisfies `h · ker φ ⊆ (u₁)`. -/
theorem exists_annihilator_of_coord_eq_zero (h1 : φ (coord R P 1) = 0)
    (hdim : ringKrullDim (Localization.AtPrime z) = 1) :
    ∃ h : P,
      h ∉ z.comap ((Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).comp φ).toRingHom ∧
      ∀ j ∈ RingHom.ker φ.toRingHom, h * j ∈ Ideal.span {coord R P 1} := by
  classical
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.trans R (MvPolynomial (Fin 2) R) P
  set g := coord R P 1 with hgdef
  set J := RingHom.ker φ.toRingHom with hJ
  -- base change to `K`
  let Φ : PlaneBaseChange R K P →ₐ[K] K ⊗[R] B := Algebra.TensorProduct.map (AlgHom.id K K) φ
  have hΦ : Function.Surjective Φ := LinearMap.lTensor_surjective K hφ
  set Q := z.comap Φ.toRingHom with hQdef
  have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hΦ
  have : Algebra.FiniteType K (PlaneBaseChange R K P) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin 2) K) inferInstance inferInstance
  have hres := algebraMap_quotient_surjective_of_isAlgClosed K (PlaneBaseChange R K P) Q
  choose c hc using fun j : Fin 2 =>
    hres (Ideal.Quotient.mk Q (coord K (PlaneBaseChange R K P) j))
  have hQ : IsRationalPoint Q c := by
    refine ⟨fun j => ?_, hres⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc j, Ideal.Quotient.mk_algebraMap, sub_self]
  -- the hypersurface `T = P/(u₁)` and the surjection `T → B`
  have hgJ : g ∈ J := h1
  have hgker : ∀ a ∈ Ideal.span {g}, φ a = 0 := fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, h1, mul_zero]
  let Φbar : (P ⧸ Ideal.span {g}) →ₐ[R] B := Ideal.Quotient.liftₐ (Ideal.span {g}) φ hgker
  have hΦbar : Function.Surjective Φbar := fun x => by
    obtain ⟨p, rfl⟩ := hφ x
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  let πT := baseQuotientMap R K P g
  let ΦT : HypersurfaceFibre R K P g →ₐ[K] K ⊗[R] B :=
    Algebra.TensorProduct.map (AlgHom.id K K) Φbar
  have hΦT : Function.Surjective ΦT := LinearMap.lTensor_surjective K hΦbar
  have hcomp : ∀ x : K ⊗[R] P, ΦT (πT x) = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul k p => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  set QT := z.comap ΦT.toRingHom with hQTdef
  have : QT.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hΦT
  have hQT : QT.comap πT.toRingHom = Q := by
    ext x
    change ΦT (πT x) ∈ z ↔ Φ x ∈ z
    rw [hcomp]
  -- the hypersurface is smooth at `QT`
  have hd : planeDerivation K (PlaneBaseChange R K P) 1 (toPlaneBaseChange R K P g) ∉ Q := by
    rw [hgdef, toPlaneBaseChange_coord, planeDerivation_coord, if_pos rfl]
    exact fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h)
  have hle := hQ.spanFinrank_maximalIdeal_le_one πT QT hQT (baseQuotientMap_surjective R K P g)
    (toPlaneBaseChange R K P g) (ker_baseQuotientMap R K P g) 1 hd
  have : Algebra.FinitePresentation R (P ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  have : Algebra.FiniteType K (HypersurfaceFibre R K P g) :=
    inferInstanceAs (Algebra.FiniteType K (K ⊗[R] (P ⧸ Ideal.span {g})))
  have : IsNoetherianRing (HypersurfaceFibre R K P g) := Algebra.FiniteType.isNoetherianRing K _
  have hinjT := localRingHom_injective_of_ringKrullDim ΦT.toRingHom hΦT z hle hdim
  obtain ⟨s, hsQT, hs⟩ := exists_notMem_forall_mul_eq_zero (RingHom.ker ΦT.toRingHom)
    (IsNoetherian.noetherian _) QT fun x hx => by
      have h0 : algebraMap _ (Localization.AtPrime QT) x = 0 := by
        apply hinjT
        rw [Localization.localRingHom_to_map, map_zero]
        change algebraMap _ _ (ΦT x) = 0
        rw [show ΦT x = 0 from RingHom.mem_ker.mp hx, map_zero]
      obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff QT.primeCompl _ x).mp h0
      exact ⟨m, hm, hmx⟩
  -- the kernel `M` of `T → B` and its fibre
  set M := RingHom.ker Φbar.toRingHom with hMdef
  have hMfg : M.FG := Algebra.FinitePresentation.ker_fG_of_surjective Φbar hΦbar
  have : Module.Finite (P ⧸ Ideal.span {g}) M := Module.Finite.iff_fg.mpr hMfg
  have hflat : Function.Injective ((M.subtype.restrictScalars R).lTensor K) :=
    LinearMap.lTensor_injective_of_exact_of_flat Φbar.toLinearMap hΦbar
      (M.subtype.restrictScalars R) Subtype.val_injective (fun t => by
        constructor
        · intro ht
          exact ⟨⟨t, ht⟩, rfl⟩
        · rintro ⟨m, rfl⟩
          exact m.2) K
  let : Field (HypersurfaceFibre R K P g ⧸ QT) := Ideal.Quotient.field QT
  let ρ : K ⊗[R] (P ⧸ Ideal.span {g}) →+* HypersurfaceFibre R K P g ⧸ QT := Ideal.Quotient.mk QT
  have hρs : ρ s ≠ 0 := by
    change Ideal.Quotient.mk QT s ≠ 0
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsub := subsingleton_tensor_of_lTensor_injective M K hflat ρ s hρs fun m hm => hs _ (by
    rw [RingHom.mem_ker]
    change (1 : K) ⊗ₜ Φbar m = 0
    rw [show Φbar m = 0 from hm, tmul_zero])
  let : Algebra (P ⧸ Ideal.span {g}) (HypersurfaceFibre R K P g ⧸ QT) :=
    (ρ.comp (Algebra.TensorProduct.includeRight :
      (P ⧸ Ideal.span {g}) →ₐ[R] K ⊗[R] (P ⧸ Ideal.span {g})).toRingHom).toAlgebra
  set Qbar := QT.comap (Algebra.TensorProduct.includeRight :
      (P ⧸ Ideal.span {g}) →ₐ[R] K ⊗[R] (P ⧸ Ideal.span {g})).toRingHom with hQbar
  have hker : RingHom.ker (algebraMap (P ⧸ Ideal.span {g}) (HypersurfaceFibre R K P g ⧸ QT)) =
      Qbar := by
    ext t
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsupp := notMem_support_of_subsingleton_tensor (B := P ⧸ Ideal.span {g}) (M := M)
    (F := HypersurfaceFibre R K P g ⧸ QT) ⟨Qbar, inferInstance⟩ hker
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hsupp
  obtain ⟨hbar, hann, hhbar⟩ := hsupp
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective hbar
  refine ⟨h, hhbar, fun j hj => ?_⟩
  have hjM : Ideal.Quotient.mk (Ideal.span {g}) j ∈ M := by
    rw [RingHom.mem_ker]
    exact RingHom.mem_ker.mp hj
  have := congrArg Subtype.val (Module.mem_annihilator.mp hann ⟨_, hjM⟩)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  exact this

end Kernel

section SmoothNormal

variable {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {B : Type u} [CommRing B]
  [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A flat family over a normal domain is normal near a smooth geometric point.** Let `R` be an
integrally closed domain, `B` a flat finitely presented `R`-algebra and `z ⊂ K ⊗_R B` a closed
point of a geometric fibre whose local ring has principal maximal ideal. There is `f` outside the
point under `z` such that for every closed point `z'` of a geometric fibre of `B_f` with
one-dimensional local ring, the local ring of `B_f` at the point under `z'` is an integrally
closed domain. -/
theorem exists_away_isIntegrallyClosed_of_spanFinrank_le_one
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    (z : Ideal (K ⊗[R] B)) [z.IsMaximal]
    (hz : (maximalIdeal (Localization.AtPrime z)).spanFinrank ≤ 1) :
    ∃ f : B, f ∉ z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ∧
      ∀ (K' : Type u) [Field K'] [IsAlgClosed K'] [Algebra R K']
        (z' : Ideal (K' ⊗[R] Localization.Away f)) [z'.IsMaximal],
        ringKrullDim (Localization.AtPrime z') = 1 →
        IsDomain (Localization.AtPrime (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom)) ∧
        IsIntegrallyClosed (Localization.AtPrime (z'.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).toRingHom)) := by
  obtain ⟨b, hb0, hunr⟩ := exists_isUnramifiedAt_plane z 1 (by norm_num) hz
  let : Algebra (MvPolynomial (Fin 2) R) B := (MvPolynomial.aeval (R := R) b).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) B := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = MvPolynomial.aeval b (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C]
  have : Algebra.FiniteType (MvPolynomial (Fin 2) R) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial (Fin 2) R) B
  have := hunr
  obtain ⟨f, hfq, Pe, ψ, hψ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := MvPolynomial (Fin 2) R)
      (z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom)
  refine ⟨f, hfq, fun K' _ _ _ z' _ hdim => ?_⟩
  let : Algebra R Pe.Ring := ((algebraMap (MvPolynomial (Fin 2) R) Pe.Ring).comp
    (algebraMap R (MvPolynomial (Fin 2) R))).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pe.Ring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψR : Pe.Ring →ₐ[R] Localization.Away f := ψ.restrictScalars R
  have h1 : ψR (coord R Pe.Ring 1) = 0 := by
    change ψ (algebraMap (MvPolynomial (Fin 2) R) Pe.Ring (MvPolynomial.X 1)) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) B
      (Localization.Away f)]
    change algebraMap B _ (MvPolynomial.aeval b (MvPolynomial.X 1)) = 0
    rw [MvPolynomial.aeval_X, hb0 1 (by simp), map_zero]
  have : Module.Flat R (Localization.Away f) := Module.Flat.trans R B (Localization.Away f)
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    Algebra.FinitePresentation.trans R B (Localization.Away f)
  obtain ⟨h, hhQ, hJ⟩ := exists_annihilator_of_coord_eq_zero ψR hψ z' h1 hdim
  set Q₀ := z'.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away f →ₐ[R] K' ⊗[R] Localization.Away f).comp ψR).toRingHom with hQ₀
  have : Q₀.IsPrime := Ideal.comap_isPrime _ _
  set a := h * 1 with ha
  have haQ : a ∉ Q₀ := by rw [ha, mul_one]; exact hhQ
  -- localize at `a`
  let Pa := Localization.Away a
  have : Algebra.Etale Pe.Ring Pa := Algebra.Etale.of_isLocalizationAway a
  have : Algebra.Etale (MvPolynomial (Fin 2) R) Pa := Algebra.Etale.comp _ Pe.Ring Pa
  have : IsScalarTower R (MvPolynomial (Fin 2) R) Pa := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Pe.Ring Pa,
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) Pe.Ring,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  have hdisj : Disjoint (Submonoid.powers a : Set Pe.Ring) Q₀ :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr haQ
  set Q₀a := Q₀.map (algebraMap Pe.Ring Pa)
  have : Q₀a.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) Pa Q₀ ‹_› hdisj
  have hQ₀a : Q₀a.comap (algebraMap Pe.Ring Pa) = Q₀ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) Pa ‹_› hdisj
  set ga := algebraMap Pe.Ring Pa (coord R Pe.Ring 1)
  have hgQ₀ : coord R Pe.Ring 1 ∈ Q₀ := by
    rw [hQ₀, Ideal.mem_comap]
    change (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[R] _)
      (ψR (coord R Pe.Ring 1)) ∈ z'
    rw [h1, map_zero]
    exact z'.zero_mem
  have hgaQ : ga ∈ Q₀a := Ideal.mem_map_of_mem _ hgQ₀
  -- the curve `T = Pa/(u₁) ≅ (B_f)_{ψ a}`, étale over `R[X₀, X₁]/(X₁)`
  set I₁ := Ideal.span {MvPolynomial.X (R := R) (1 : Fin 2)}
  have hI₁ : I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa) = Ideal.span {ga} := by
    rw [Ideal.map_span, Set.image_singleton, IsScalarTower.algebraMap_apply
      (MvPolynomial (Fin 2) R) Pe.Ring Pa]
  set T := Pa ⧸ I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)
  let Bfs := Localization.Away (ψR a)
  let φa : Pa →ₐ[R] Bfs := Localization.awayMapₐ ψR a
  have hφa : Function.Surjective φa := IsLocalization.Away.mapₐ_surjective_of_surjective a hψ
  have hker : RingHom.ker φa.toRingHom = Ideal.span {ga} :=
    ker_awayMap_eq_span ψR (coord R Pe.Ring 1) h1 h 1 hJ
  let eB : T ≃ₐ[R] Bfs :=
    (Ideal.quotientEquivAlgOfEq R (hI₁.trans hker.symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hφa)
  have heB : ∀ x, eB (Ideal.Quotient.mk _ x) = φa x := fun _ => rfl
  have himg : ∀ p : Pe.Ring, algebraMap (Localization.Away f) Bfs (ψR p) =
      φa (algebraMap Pe.Ring Pa p) := by
    intro p
    change _ = IsLocalization.Away.map Pa Bfs ψR.toRingHom a (algebraMap Pe.Ring Pa p)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have : Algebra.FinitePresentation (MvPolynomial (Fin 2) R) T :=
    Algebra.FinitePresentation.quotient (hI₁ ▸ Submodule.fg_span_singleton ga)
  have := formallyEtale_quotient_map (MvPolynomial (Fin 2) R) Pa I₁
  have := isScalarTower_quotient_map (MvPolynomial (Fin 2) R) Pa I₁ (MvPolynomial (Fin 2) R)
  have : Algebra.FinitePresentation (MvPolynomial (Fin 2) R ⧸ I₁) T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (MvPolynomial (Fin 2) R)
      (MvPolynomial (Fin 2) R ⧸ I₁) T
  have : Algebra.Etale (MvPolynomial (Fin 2) R ⧸ I₁) T := ⟨inferInstance, inferInstance⟩
  -- the point
  set QT : Ideal T := Q₀a.map (Ideal.Quotient.mk _)
  have hkerT : RingHom.ker (Ideal.Quotient.mk (I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)))
      ≤ Q₀a := by
    rw [Ideal.mk_ker, hI₁, Ideal.span_le, Set.singleton_subset_iff]
    exact hgaQ
  have : QT.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerT
  have hQT : ∀ x, Ideal.Quotient.mk (I₁.map (algebraMap (MvPolynomial (Fin 2) R) Pa)) x ∈ QT ↔
      x ∈ Q₀a := by
    intro x
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerT]
  have hT := isDomain_isIntegrallyClosed_localization_of_etale (MvPolynomial (Fin 2) R ⧸ I₁) QT
  -- transport back to `B_f`
  have h1' := isDomain_isIntegrallyClosed_localization_of_ringEquiv eB.toRingEquiv QT hT
  have h2 := isDomain_isIntegrallyClosed_localization_localization (Submonoid.powers (ψR a)) _ h1'
  refine isDomain_isIntegrallyClosed_of_eq ?_ h2
  apply Ideal.comap_injective_of_surjective ψR.toRingHom hψ
  ext p
  simp only [Ideal.mem_comap]
  change eB.symm (algebraMap (Localization.Away f) Bfs (ψR p)) ∈ QT ↔ _
  rw [himg, ← heB, AlgEquiv.symm_apply_apply, hQT, ← Ideal.mem_comap, hQ₀a, hQ₀]
  rfl

end SmoothNormal

end DeJongAlterations.StableModification.Curves.SemistableNormal
