import DeJongAlterations.Algebra.AdicCompletionTransportQuotient
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Actual completed local maps for formally etale local algebras

The ring map is local, essentially of finite type, formally smooth and
formally unramified. The only field comparison hypothesis is bijectivity
of its actual native residue-field map. Every finite-level inverse is
constructed using native infinitesimal lifting, and the final equivalence
has the actual completed ring map as its forward map.
-/

noncomputable section

namespace DeJongAlterations.Algebra.AdicCompletionEtale

open IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The actual quotient by a maximal-ideal power. -/
abbrev PowerQuotient (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  R ⧸ maximalIdeal R ^ n

/-- Reduction of an actual power quotient to the native residue field. -/
def powerResidue (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (hn : n ≠ 0) :
    PowerQuotient R n →ₐ[R] ResidueField R :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn)

@[simp]
theorem powerResidue_mk (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : n ≠ 0) (r : R) :
    powerResidue R n hn (Ideal.Quotient.mk _ r) = residue R r := rfl

theorem powerResidue_surjective (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : n ≠ 0) : Function.Surjective (powerResidue R n hn) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_self hn)

/-- The kernel of reduction is the actual extension of the maximal ideal. -/
theorem ker_powerResidue (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (powerResidue R n hn).toRingHom =
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ n)) := by
  ext a
  induction a using Quotient.inductionOn' with
  | _ a =>
    change Ideal.Quotient.mk (maximalIdeal R) a = 0 ↔
      Ideal.Quotient.mk (maximalIdeal R ^ n) a ∈
        (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ n))
    rw [Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_quotient_iff_mem (Ideal.pow_le_self hn)]

/-- Reduction to the native residue field has an internally proved nilpotent kernel. -/
theorem ker_powerResidue_isNilpotent (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) (hn : n ≠ 0) : IsNilpotent (RingHom.ker (powerResidue R n hn).toRingHom) := by
  refine ⟨n, ?_⟩
  rw [ker_powerResidue, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]

/-- Native unramified local maps extend the actual maximal ideal to the actual maximal ideal. -/
theorem map_maximalIdeal : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
  Algebra.FormallyUnramified.map_maximalIdeal

/-- The actual map of maximal-power quotients. -/
def powerQuotientMap (n : ℕ) : PowerQuotient A n →ₐ[A] PowerQuotient B n :=
  Ideal.quotientMapₐ (maximalIdeal B ^ n) (Algebra.ofId A B) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    change ((maximalIdeal A).map (algebraMap A B)) ^ n ≤ maximalIdeal B ^ n
    rw [map_maximalIdeal])

@[simp]
theorem powerQuotientMap_mk (n : ℕ) (a : A) :
    powerQuotientMap (A := A) (B := B) n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A B a) := rfl

/-- The actual residue-field isomorphism, with its original coefficient structure. -/
def residueEquiv (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    ResidueField A ≃ₐ[A] ResidueField B :=
  AlgEquiv.ofBijective
    { ResidueField.map (algebraMap A B) with
      commutes' := fun a => by
        change ResidueField.map (algebraMap A B) (residue A a) = residue B (algebraMap A B a)
        rfl } hκ

/-- The original map from B to the original residue field of A. -/
def residueBack (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    B →ₐ[A] ResidueField A :=
  (residueEquiv hκ).symm.toAlgHom.comp (IsScalarTower.toAlgHom A B (ResidueField B))

variable [Algebra.FormallySmooth A B]

/-- An actual lift of B to each actual finite power quotient of A. -/
def liftToPower (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) : B →ₐ[A] PowerQuotient A n :=
  Algebra.FormallySmooth.liftOfSurjective (residueBack hκ)
    (powerResidue A n hn) (powerResidue_surjective A n hn)
    (ker_powerResidue_isNilpotent A n hn)

omit [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] in
@[simp]
theorem powerResidue_liftToPower
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) (b : B) :
    powerResidue A n hn (liftToPower hκ n hn b) = residueBack hκ b :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ b

/-- The internally constructed lift kills the actual nth maximal-ideal power of B. -/
theorem power_le_ker_liftToPower
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) :
    maximalIdeal B ^ n ≤ RingHom.ker (liftToPower hκ n hn).toRingHom := by
  rw [← map_maximalIdeal (A := A) (B := B), ← Ideal.map_pow,
    Ideal.map_le_iff_le_comap]
  intro a ha
  change liftToPower hκ n hn (algebraMap A B a) = 0
  rw [AlgHom.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- The actual inverse map on the positive-level power quotient. -/
def inversePowerQuotientMap
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) : PowerQuotient B n →ₐ[A] PowerQuotient A n :=
  Ideal.Quotient.liftₐ _ (liftToPower hκ n hn) (fun _ ha =>
    power_le_ker_liftToPower hκ n hn ha)

/-- The first composite is the actual identity because it fixes A. -/
theorem inversePowerQuotientMap_comp
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) :
    (inversePowerQuotientMap hκ n hn).comp (powerQuotientMap n) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change liftToPower hκ n hn (algebraMap A B a) = Ideal.Quotient.mk _ a
  exact (liftToPower hκ n hn).commutes a

omit [Algebra.FormallySmooth A B] in
/-- Actual finite-level maps agree with the original residue-field map. -/
theorem powerResidue_powerQuotientMap
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) (a : PowerQuotient A n) :
    powerResidue B n hn (powerQuotientMap n a) =
      residueEquiv hκ (powerResidue A n hn a) := by
  induction a using Quotient.inductionOn' with
  | _ a => rfl

/-- Formal unramifiedness proves the second actual composite is the identity. -/
theorem powerQuotientMap_comp_inverse
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (hn : n ≠ 0) :
    (powerQuotientMap n).comp (inversePowerQuotientMap hκ n hn) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply Algebra.FormallyUnramified.ext' (powerResidue B n hn).toRingHom
    (ker_powerResidue_isNilpotent B n hn)
  intro b
  change powerResidue B n hn (powerQuotientMap n (liftToPower hκ n hn b)) = residue B b
  rw [powerResidue_powerQuotientMap hκ, powerResidue_liftToPower]
  exact (residueEquiv hκ).apply_symm_apply _

/-- Bijectivity of every actual finite-level map, including the zero-ring level. -/
theorem powerQuotientMap_bijective
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) (n : ℕ) :
    Function.Bijective (powerQuotientMap (A := A) (B := B) n) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (PowerQuotient A 0) := by
      change Subsingleton (A ⧸ maximalIdeal A ^ 0)
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    have : Subsingleton (PowerQuotient B 0) := by
      change Subsingleton (B ⧸ maximalIdeal B ^ 0)
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩
  · exact ⟨Function.LeftInverse.injective
      (fun a => AlgHom.congr_fun (inversePowerQuotientMap_comp hκ n hn) a),
      Function.RightInverse.surjective
      (fun b => AlgHom.congr_fun (powerQuotientMap_comp_inverse hκ n hn) b)⟩

/-- The actual completed ring map, defined independently of any residue-field comparison. -/
def completionMap :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  (AdicCompletion.congrRingEquiv
    ((maximalIdeal A).map (algebraMap A B)) (maximalIdeal B) (RingEquiv.refl B)
    (by simpa using (map_maximalIdeal (A := A) (B := B)).symm)).toRingHom.comp
    (AdicCompletion.mapRingHom (maximalIdeal A))

omit [Algebra.FormallySmooth A B] in
@[simp]
theorem completionMap_of (a : A) :
    completionMap (AdicCompletion.of (maximalIdeal A) A a) =
      AdicCompletion.of (maximalIdeal B) B (algebraMap A B a) := by
  unfold completionMap
  rw [RingHom.comp_apply, AdicCompletion.mapRingHom_of]
  change AdicCompletion.congrRingEquiv _ _ (RingEquiv.refl B) _
    (AdicCompletion.of _ B (algebraMap A B a)) = _
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ _

/-- Each finite-level isomorphism has the actual coefficient map as its forward map. -/
def quotientEquiv (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) (n : ℕ) :
    (A ⧸ (maximalIdeal A ^ n • ⊤ : Ideal A)) ≃ₐ[A]
      (B ⧸ (maximalIdeal B ^ n • ⊤ : Ideal B)) :=
  (Ideal.quotientEquivAlgOfEq A
    (by simp : (maximalIdeal A ^ n • ⊤ : Ideal A) = maximalIdeal A ^ n)).trans
    ((AlgEquiv.ofBijective (powerQuotientMap n) (powerQuotientMap_bijective hκ n)).trans
      (Ideal.quotientEquivAlgOfEq A
        (by simp : (maximalIdeal B ^ n • ⊤ : Ideal B) = maximalIdeal B ^ n)).symm)

@[simp]
theorem quotientEquiv_mk (hκ : Function.Bijective (ResidueField.map (algebraMap A B)))
    (n : ℕ) (a : A) :
    quotientEquiv hκ n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap A B a) := rfl

/-- The actual finite-level maps commute with the native inverse-system reductions. -/
theorem transitionMap_quotientEquiv
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) {m n : ℕ} (hmn : m ≤ n)
    (a : A ⧸ (maximalIdeal A ^ n • ⊤ : Ideal A)) :
    AdicCompletion.transitionMap (maximalIdeal B) B hmn (quotientEquiv hκ n a) =
      quotientEquiv hκ m (AdicCompletion.transitionMap (maximalIdeal A) A hmn a) := by
  induction a using Quotient.inductionOn' with
  | _ a => rfl

/-- The equivalence between the native completed local rings, constructed from the actual map. -/
def completedRingEquiv (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B where
  toFun a :=
    ⟨fun n => quotientEquiv hκ n (a.val n), fun hmn => by
      rw [transitionMap_quotientEquiv, a.property hmn]⟩
  invFun b :=
    ⟨fun n => (quotientEquiv hκ n).symm (b.val n), fun {m n} hmn => by
      apply (quotientEquiv hκ m).injective
      rw [← transitionMap_quotientEquiv, AlgEquiv.apply_symm_apply,
        AlgEquiv.apply_symm_apply, b.property hmn]⟩
  left_inv a := by
    ext n
    exact (quotientEquiv hκ n).symm_apply_apply (a.val n)
  right_inv b := by
    ext n
    exact (quotientEquiv hκ n).apply_symm_apply (b.val n)
  map_mul' a b := by
    ext n
    exact map_mul (quotientEquiv hκ n) (a.val n) (b.val n)
  map_add' a b := by
    ext n
    exact map_add (quotientEquiv hκ n) (a.val n) (b.val n)

@[simp]
theorem completedRingEquiv_of
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) (a : A) :
    completedRingEquiv hκ (AdicCompletion.of (maximalIdeal A) A a) =
      AdicCompletion.of (maximalIdeal B) B (algebraMap A B a) := by
  ext n
  exact quotientEquiv_mk hκ n a

/-- The forward isomorphism is literally the original completed ring map. -/
theorem completedRingEquiv_toRingHom
    (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    (completedRingEquiv hκ).toRingHom = completionMap (A := A) (B := B) := by
  apply RingHom.ext
  intro a
  apply AdicCompletion.ext
  intro n
  change quotientEquiv hκ n (a.val n) =
    AdicCompletion.quotientRingEquiv _ _ (RingEquiv.refl B) _ n
      (AdicCompletion.quotientMapOfAlgebraMap (maximalIdeal A) n (a.val n))
  induction a.val n using Quotient.inductionOn' with
  | _ a => rfl

/-- The actual completed local map is an algebra isomorphism over the original source ring. -/
def completedAlgEquiv (hκ : Function.Bijective (ResidueField.map (algebraMap A B))) :
    AdicCompletion (maximalIdeal A) A ≃ₐ[A] AdicCompletion (maximalIdeal B) B :=
  AlgEquiv.ofRingEquiv (f := completedRingEquiv hκ) fun a => by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact completedRingEquiv_of hκ a

end DeJongAlterations.Algebra.AdicCompletionEtale
