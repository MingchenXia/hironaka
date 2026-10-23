import DeJongAlterations.Geometry.ProperSteinProjectiveCechLaurent
import DeJongAlterations.Geometry.ProperSteinProjectiveCechModuleLocalization
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetLocalization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

/-! # Actual polynomial coordinate-intersection localizations

The maps below use the genuine polynomial localization and its native module
localization equivalence. In particular the homogeneous piece consists of
literal fractions, with the actual degree of their actual numerator.
-/

/-!
Adapted from the same workspace `BingWangEntropy/PolynomialCoordinateLocalization.lean`,
SHA256 15aa80c14a029fc66a5a04a10e7a11eac7b4f8db7510a4c6f521bad4023ad0e6.
Original polynomial-embedding helpers are extracted from `ProjectiveSectionFiniteness.lean`,
SHA256 4853b161af90b336994c663ff326526b7907a2d7e2148b2939393fdb581d4997.
Only native Mathlib and owned DeJongAlterations modules are imported.
The actual coefficient ring is generalized to a Noetherian commutative ring.
-/

universe u

open CategoryTheory

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section PolynomialEmbedding

variable {K I : Type u} [CommRing K]

/-- Homogeneous polynomial exponent vectors embed in actual integer Laurent exponents. -/
def polynomialExponentToInt : (I →₀ ℕ) →+ (I → ℤ) where
  toFun d := fun i => (d i : ℤ)
  map_zero' := rfl
  map_add' d e := by ext i; exact Int.natCast_add _ _

/-- No two ordinary polynomial exponent vectors acquire the same Laurent exponent. -/
theorem polynomialExponentToInt_injective :
    Function.Injective (polynomialExponentToInt (I := I)) := by
  intro d e h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

/-- The genuine ordinary-polynomial inclusion into the actual Laurent algebra. -/
def polynomialToProjectiveLaurent : MvPolynomial I K →ₐ[K] projectiveLaurentAlgebra K I :=
  AddMonoidAlgebra.mapDomainAlgHom K K polynomialExponentToInt

/-- The genuine polynomial-to-Laurent inclusion is injective. -/
theorem polynomialToProjectiveLaurent_injective :
    Function.Injective (polynomialToProjectiveLaurent (K := K) (I := I)) :=
  AddMonoidAlgebra.mapDomain_injective polynomialExponentToInt_injective


/-- A homogeneous coordinate becomes its actual Laurent monomial. -/
theorem polynomialToProjectiveLaurent_X (i : I) :
    polynomialToProjectiveLaurent (K := K) (MvPolynomial.X i) =
      AddMonoidAlgebra.single (polynomialExponentToInt (Finsupp.single i 1)) 1 := by
  change AddMonoidAlgebra.mapDomain polynomialExponentToInt
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  exact AddMonoidAlgebra.mapDomain_single

/-- The inverted chart coordinate is an actual unit in the Laurent algebra. -/
theorem polynomialToProjectiveLaurent_X_isUnit (i : I) :
    IsUnit (polynomialToProjectiveLaurent (K := K) (MvPolynomial.X i)) := by
  rw [polynomialToProjectiveLaurent_X]
  apply IsUnit.of_mul_eq_one
    (AddMonoidAlgebra.single (-polynomialExponentToInt (Finsupp.single i 1)) 1)
  simp only [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
  rfl


/-- Actual polynomial monomials have no negative Laurent exponents. -/
theorem polynomialToProjectiveLaurent_exponent_nonnegative (p : MvPolynomial I K)
    {d : I → ℤ} (hd : (polynomialToProjectiveLaurent p).coeff d ≠ 0) (j : I) : 0 ≤ d j := by
  classical
  have hs : d ∈ (polynomialToProjectiveLaurent p).coeff.support := Finsupp.mem_support_iff.mpr hd
  change d ∈ ((AddMonoidAlgebra.coeff p).mapDomain polynomialExponentToInt).support at hs
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
  rw [← he]
  exact Int.natCast_nonneg _


end PolynomialEmbedding

variable {K I : Type u} [CommRing K] [hK : IsNoetherianRing K] [LinearOrder I] [Fintype I]
omit hK

/-- The genuine product inverted on a coordinate intersection. -/
def polynomialCoordinateProduct (S : Finset I) : MvPolynomial I K :=
  ∏ i ∈ S, MvPolynomial.X i

/-- The actual exponent vector of the product of the selected coordinates. -/
def polynomialCoordinateProductExponent (S : Finset I) : I → ℤ :=
  ∑ i ∈ S, polynomialExponentToInt (Finsupp.single i 1)

omit [Fintype I] in
/-- The coordinate-product exponent is the literal indicator of the selected coordinates. -/
theorem polynomialCoordinateProductExponent_apply (S : Finset I) (i : I) :
    polynomialCoordinateProductExponent S i = if i ∈ S then 1 else 0 := by
  classical
  simp [polynomialCoordinateProductExponent, polynomialExponentToInt, Finsupp.single_apply]

omit [LinearOrder I] [Fintype I] in
/-- The genuine polynomial coordinate product becomes its actual Laurent monomial. -/
theorem polynomialToProjectiveLaurent_coordinateProduct (S : Finset I) :
    polynomialToProjectiveLaurent (K := K) (polynomialCoordinateProduct S) =
      AddMonoidAlgebra.single (polynomialCoordinateProductExponent S) 1 := by
  classical
  simp [polynomialCoordinateProduct, map_prod, polynomialToProjectiveLaurent_X,
    AddMonoidAlgebra.prod_single, polynomialCoordinateProductExponent]

omit [LinearOrder I] [Fintype I] in
/-- Every genuine coordinate product maps to an actual Laurent unit. -/
theorem polynomialCoordinateProduct_laurent_isUnit (S : Finset I) :
    IsUnit (polynomialToProjectiveLaurent (K := K) (polynomialCoordinateProduct S)) := by
  classical
  rw [polynomialCoordinateProduct, map_prod]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (polynomialToProjectiveLaurent_X_isUnit i).mul ih

/-- The actual polynomial localization at a coordinate product maps to the actual Laurent algebra. -/
def polynomialCoordinateLocalizationToLaurent (S : Finset I) :
    Localization.Away (polynomialCoordinateProduct (K := K) S) →ₐ[K]
      projectiveLaurentAlgebra K I :=
  IsLocalization.Away.liftAlgHom _ (polynomialCoordinateProduct_laurent_isUnit S)

omit [LinearOrder I] [Fintype I] in
/-- The actual localization map really extends the genuine polynomial inclusion. -/
theorem polynomialCoordinateLocalizationToLaurent_algebraMap (S : Finset I) (p : MvPolynomial I K) :
    polynomialCoordinateLocalizationToLaurent S
      (algebraMap _ (Localization.Away (polynomialCoordinateProduct (K := K) S)) p) =
      polynomialToProjectiveLaurent p :=
  IsLocalization.Away.lift_eq _ (polynomialCoordinateProduct_laurent_isUnit S) p

omit [LinearOrder I] [Fintype I] in
/-- The genuine coordinate-product localization embeds faithfully into the Laurent algebra. -/
theorem polynomialCoordinateLocalizationToLaurent_injective (S : Finset I) :
    Function.Injective (polynomialCoordinateLocalizationToLaurent (K := K) S) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
    (polynomialCoordinateLocalizationToLaurent S).toRingHom).mpr
  intro p q
  change algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) p =
      algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) q ↔
    polynomialCoordinateLocalizationToLaurent S (algebraMap _ _ p) =
      polynomialCoordinateLocalizationToLaurent S (algebraMap _ _ q)
  rw [polynomialCoordinateLocalizationToLaurent_algebraMap,
    polynomialCoordinateLocalizationToLaurent_algebraMap]
  constructor
  · intro h
    simpa only [polynomialCoordinateLocalizationToLaurent_algebraMap] using
      congrArg (polynomialCoordinateLocalizationToLaurent S) h
  · intro h
    exact congrArg _ (polynomialToProjectiveLaurent_injective h)

/-- The native module localization of the polynomial ring is its native ring localization. -/
def polynomialCoordinateModuleLocalizationEquiv (S : Finset I) :
    LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S)) (MvPolynomial I K)
      ≃ₗ[MvPolynomial I K] Localization.Away (polynomialCoordinateProduct (K := K) S) :=
  IsLocalizedModule.iso (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
    (Algebra.linearMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct (K := K) S)))

/-- The actual native module localization maps linearly into the actual Laurent algebra. -/
def polynomialCoordinateModuleToLaurent (S : Finset I) :
    LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S)) (MvPolynomial I K)
      →ₗ[K] projectiveLaurentAlgebra K I :=
  (polynomialCoordinateLocalizationToLaurent S).toLinearMap.comp
    ((polynomialCoordinateModuleLocalizationEquiv S).restrictScalars K).toLinearMap

omit [LinearOrder I] [Fintype I] in
/-- The actual native module-localization Laurent map is faithful. -/
theorem polynomialCoordinateModuleToLaurent_injective (S : Finset I) :
    Function.Injective (polynomialCoordinateModuleToLaurent (K := K) S) :=
  (polynomialCoordinateLocalizationToLaurent_injective S).comp
    (polynomialCoordinateModuleLocalizationEquiv S).injective

omit [LinearOrder I] [Fintype I] in
/-- The native module/ring localization equivalence preserves genuine numerators. -/
theorem polynomialCoordinateModuleLocalizationEquiv_mk_one (S : Finset I) (p : MvPolynomial I K) :
    polynomialCoordinateModuleLocalizationEquiv S (LocalizedModule.mk p 1) =
      algebraMap (MvPolynomial I K) (Localization.Away (polynomialCoordinateProduct S)) p :=
  IsLocalizedModule.iso_mk_one _ _ _

omit [LinearOrder I] [Fintype I] in
/-- Clearing a literal denominator in the actual Laurent image gives precisely
the actual polynomial numerator, with its actual coordinate-product monomial. -/
theorem polynomialCoordinateModuleToLaurent_clear (S : Finset I) (p : MvPolynomial I K) (n : ℕ) :
    polynomialCoordinateModuleToLaurent S
        (LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) *
      AddMonoidAlgebra.single (n • polynomialCoordinateProductExponent S) 1 =
        polynomialToProjectiveLaurent p := by
  have hmul : (polynomialCoordinateProduct (K := K) S) ^ n •
      LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n) =
        (LocalizedModule.mk p 1 : LocalizedModule
          (Submonoid.powers (polynomialCoordinateProduct (K := K) S)) (MvPolynomial I K)) := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (homogeneousPowerDenominator (polynomialCoordinateProduct S) n) p
  have hR := congrArg (polynomialCoordinateModuleLocalizationEquiv S) hmul
  rw [LinearEquiv.map_smul, polynomialCoordinateModuleLocalizationEquiv_mk_one] at hR
  rw [Algebra.smul_def] at hR
  have hL := congrArg (polynomialCoordinateLocalizationToLaurent S) hR
  rw [map_mul, polynomialCoordinateLocalizationToLaurent_algebraMap,
    polynomialCoordinateLocalizationToLaurent_algebraMap, map_pow,
    polynomialToProjectiveLaurent_coordinateProduct, AddMonoidAlgebra.single_pow, one_pow] at hL
  rw [mul_comm]
  exact hL

/-- The actual Laurent exponent of a coordinate product has total degree equal
to the number of actual selected coordinates. -/
theorem polynomialCoordinateProductExponent_sum (S : Finset I) :
    ∑ i, polynomialCoordinateProductExponent S i = (S.card : ℤ) := by
  classical
  simp [polynomialCoordinateProductExponent_apply]

/-- The native integral polynomial grading assigns weight one to every actual coordinate. -/
abbrev polynomialIntegralGrading : ℤ → Submodule K (MvPolynomial I K) :=
  MvPolynomial.weightedHomogeneousSubmodule K (fun _ : I => (1 : ℤ))

/-- The native weighted polynomial grading is a genuine graded algebra. -/
instance polynomialIntegralGradingGradedAlgebra :
    GradedAlgebra (polynomialIntegralGrading (K := K) (I := I)) :=
  MvPolynomial.weightedGradedAlgebra K (fun _ : I => (1 : ℤ))

omit [LinearOrder I] [Fintype I] in
/-- The true coordinate product is homogeneous of its actual cardinal degree. -/
theorem polynomialCoordinateProduct_degree (S : Finset I) :
    polynomialCoordinateProduct (K := K) S ∈ polynomialIntegralGrading (S.card : ℤ) := by
  simpa only [polynomialCoordinateProduct, Finset.sum_const, nsmul_eq_mul, mul_one] using
    SetLike.prod_mem_graded (polynomialIntegralGrading (K := K) (I := I))
      (fun _ : I => (1 : ℤ)) (fun i => (MvPolynomial.X i : MvPolynomial I K))
      (F := S) (fun i _ => MvPolynomial.isWeightedHomogeneous_X K (fun _ : I => (1 : ℤ)) i)

omit [LinearOrder I] in
/-- A genuine weighted-homogeneous numerator has the same literal total degree
after its genuine inclusion into the Laurent algebra. -/
theorem polynomialToProjectiveLaurent_homogeneous_degree (p : MvPolynomial I K) (m : ℤ)
    (hp : p ∈ polynomialIntegralGrading m) {α : I → ℤ}
    (hα : (polynomialToProjectiveLaurent p).coeff α ≠ 0) : ∑ i, α i = m := by
  classical
  have hs : α ∈ (polynomialToProjectiveLaurent p).coeff.support :=
    Finsupp.mem_support_iff.mpr hα
  change α ∈ ((AddMonoidAlgebra.coeff p).mapDomain polynomialExponentToInt).support at hs
  obtain ⟨β, hβ, hβα⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
  have hdegree := hp (Finsupp.mem_support_iff.mp hβ)
  rw [← hβα]
  change (∑ i, (β i : ℤ)) = m
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_one] using hdegree

/-- The actual homogeneous polynomial module-localization piece consists of
literal fractions with native homogeneous numerators of the actual shifted degree. -/
abbrev polynomialCoordinateHomogeneousPiece (m : ℤ) (S : Finset I) :=
  localizedHomogeneousModulePiece (polynomialIntegralGrading (K := K) (I := I))
    (polynomialIntegralGrading (K := K) (I := I))
    (polynomialCoordinateProduct S) (S.card : ℤ) (polynomialCoordinateProduct_degree S) m

/-- The actual Laurent image of every literal homogeneous fraction has the
required integral degree and can have negative exponents only at inverted coordinates. -/
theorem polynomialCoordinateModuleToLaurent_mem (m : ℤ) (S : Finset I)
    (z : polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S) :
    polynomialCoordinateModuleToLaurent S z.val ∈
      subsetHomogeneousLaurentModule (K := K) m S := by
  classical
  obtain ⟨n, p, hp, he⟩ : ∃ n : ℕ, ∃ p : MvPolynomial I K, p ∈ polynomialIntegralGrading
      (m + (n : ℤ) * (S.card : ℤ)) ∧
      LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n) = z.val :=
    z.property
  apply AddMonoidAlgebra.mem_supported.mpr
  intro α hα
  have hcoeff : (polynomialCoordinateModuleToLaurent S z.val).coeff α ≠ 0 :=
    Finsupp.mem_support_iff.mp hα
  let a : I → ℤ := n • polynomialCoordinateProductExponent S
  have hclear := polynomialCoordinateModuleToLaurent_clear S p n
  rw [he] at hclear
  have hc : (polynomialToProjectiveLaurent p).coeff (α + a) =
      (polynomialCoordinateModuleToLaurent S z.val).coeff α := by
    rw [← hclear]
    exact (AddMonoidAlgebra.coeff_mul_single_add _ 1 _ _).trans (mul_one _)
  have hnonzero : (polynomialToProjectiveLaurent p).coeff (α + a) ≠ 0 := by
    rw [hc]
    exact hcoeff
  have hdegree := polynomialToProjectiveLaurent_homogeneous_degree p _ hp hnonzero
  have hsum : ∑ i, a i = (n : ℤ) * (S.card : ℤ) := by
    simp [a, nsmul_eq_mul, ← Finset.mul_sum,
      polynomialCoordinateProductExponent_sum]
  constructor
  · rw [show (∑ i, (α + a) i) = (∑ i, α i) + ∑ i, a i by
      simp only [Pi.add_apply, Finset.sum_add_distrib], hsum] at hdegree
    exact add_right_cancel hdegree
  · intro i hi
    have hnonneg := polynomialToProjectiveLaurent_exponent_nonnegative p hnonzero i
    simpa [a, polynomialCoordinateProductExponent_apply, hi] using hnonneg

/-- Restricting the genuine native module-localization map gives an actual map
from literal homogeneous polynomial fractions to the supported Laurent piece. -/
def polynomialCoordinateHomogeneousToLaurent (m : ℤ) (S : Finset I) :
    polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S →ₗ[K]
      subsetHomogeneousLaurentModule (K := K) (I := I) m S :=
  ((polynomialCoordinateModuleToLaurent S).comp
    (polynomialCoordinateHomogeneousPiece m S).subtype).codRestrict _
      (polynomialCoordinateModuleToLaurent_mem m S)

/-- The actual homogeneous polynomial-fraction comparison is injective. -/
theorem polynomialCoordinateHomogeneousToLaurent_injective (m : ℤ) (S : Finset I) :
    Function.Injective (polynomialCoordinateHomogeneousToLaurent (K := K) (I := I) m S) := by
  intro z z' h
  apply Subtype.ext
  exact polynomialCoordinateModuleToLaurent_injective S (congrArg Subtype.val h)

/-- A genuine finite bound clears every negative coordinate exponent at once. -/
def polynomialLaurentClearingPower (α : I → ℤ) : ℕ := ∑ i, (-α i).toNat

/-- Adding the produced coordinate-product exponent makes every allowed Laurent
monomial a genuine polynomial monomial. -/
theorem polynomialLaurentClearedExponent_nonnegative (m : ℤ) (S : Finset I)
    {α : I → ℤ} (hα : α ∈ subsetHomogeneousLaurentExponents m S) (i : I) :
    0 ≤ α i + (polynomialLaurentClearingPower α : ℤ) * polynomialCoordinateProductExponent S i := by
  classical
  by_cases hi : i ∈ S
  · have hterm : (-α i).toNat ≤ polynomialLaurentClearingPower α :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((-α j).toNat)) (Finset.mem_univ i)
    have hcast : (((-α i).toNat : ℕ) : ℤ) ≤ (polynomialLaurentClearingPower α : ℤ) :=
      Int.ofNat_le.mpr hterm
    have hself := Int.self_le_toNat (-α i)
    rw [polynomialCoordinateProductExponent_apply, if_pos hi, mul_one]
    omega
  · rw [polynomialCoordinateProductExponent_apply, if_neg hi, mul_zero, add_zero]
    exact hα.2 i hi

/-- The produced cleared numerator exponent is an actual finitely-supported
ordinary polynomial exponent vector. -/
def polynomialLaurentClearedExponent (S : Finset I) (α : I → ℤ) : I →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    (α i + (polynomialLaurentClearingPower α : ℤ) * polynomialCoordinateProductExponent S i).toNat)

/-- The actual polynomial numerator exponent is exactly the original Laurent
exponent plus the actual denominator exponent. -/
theorem polynomialLaurentClearedExponent_toInt (m : ℤ) (S : Finset I)
    {α : I → ℤ} (hα : α ∈ subsetHomogeneousLaurentExponents m S) :
    polynomialExponentToInt (polynomialLaurentClearedExponent S α) =
      α + polynomialLaurentClearingPower α • polynomialCoordinateProductExponent S := by
  funext i
  change ((α i + (polynomialLaurentClearingPower α : ℤ) *
    polynomialCoordinateProductExponent S i).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (polynomialLaurentClearedExponent_nonnegative m S hα i)]
  rfl

/-- The actual cleared polynomial monomial has the exact native shifted homogeneous degree. -/
theorem polynomialLaurentClearedExponent_degree (m : ℤ) (S : Finset I)
    {α : I → ℤ} (hα : α ∈ subsetHomogeneousLaurentExponents m S) :
    Finsupp.weight (fun _ : I => (1 : ℤ)) (polynomialLaurentClearedExponent S α) =
      m + (polynomialLaurentClearingPower α : ℤ) * (S.card : ℤ) := by
  have he := polynomialLaurentClearedExponent_toInt m S hα
  calc
    _ = ∑ i, (polynomialLaurentClearedExponent S α i : ℤ) := by
      simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_one]
    _ = ∑ i, (α + polynomialLaurentClearingPower α • polynomialCoordinateProductExponent S) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun he i
    _ = _ := by
      simp [Finset.sum_add_distrib, nsmul_eq_mul, ← Finset.mul_sum,
        polynomialCoordinateProductExponent_sum, hα.1]

omit [LinearOrder I] [Fintype I] in
/-- Genuine polynomial monomials map to precisely their genuine integral Laurent monomials. -/
theorem polynomialToProjectiveLaurent_monomial (β : I →₀ ℕ) :
    polynomialToProjectiveLaurent (K := K) (MvPolynomial.monomial β 1) =
      AddMonoidAlgebra.single (polynomialExponentToInt β) 1 := by
  change AddMonoidAlgebra.mapDomain polynomialExponentToInt
    (AddMonoidAlgebra.single β 1) = _
  exact AddMonoidAlgebra.mapDomain_single

/-- Every actual allowed Laurent basis monomial is produced by a literal
homogeneous polynomial fraction with an explicitly cleared denominator. -/
theorem polynomialCoordinateHomogeneousToLaurent_monomial_preimage (m : ℤ) (S : Finset I)
    {α : I → ℤ} (hα : α ∈ subsetHomogeneousLaurentExponents m S) :
    ∃ z : polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S,
      (polynomialCoordinateHomogeneousToLaurent m S z).val = AddMonoidAlgebra.single α 1 := by
  let n := polynomialLaurentClearingPower α
  let p : MvPolynomial I K := MvPolynomial.monomial (polynomialLaurentClearedExponent S α) 1
  have hp : p ∈ polynomialIntegralGrading (m + (n : ℤ) * (S.card : ℤ)) :=
    MvPolynomial.isWeightedHomogeneous_monomial _ _ _
      (polynomialLaurentClearedExponent_degree m S hα)
  let z : polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S :=
    ⟨LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n),
      n, p, hp, rfl⟩
  refine ⟨z, ?_⟩
  change polynomialCoordinateModuleToLaurent S z.val = AddMonoidAlgebra.single α 1
  have hclear := polynomialCoordinateModuleToLaurent_clear S p n
  have hu : IsUnit (AddMonoidAlgebra.single (n • polynomialCoordinateProductExponent S) (1 : K)) := by
    simpa only [map_pow, polynomialToProjectiveLaurent_coordinateProduct,
      AddMonoidAlgebra.single_pow, one_pow] using
      (polynomialCoordinateProduct_laurent_isUnit (K := K) S).pow n
  apply hu.mul_right_cancel
  change polynomialCoordinateModuleToLaurent S
      (LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) *
      AddMonoidAlgebra.single (n • polynomialCoordinateProductExponent S) 1 = _
  rw [hclear]
  change polynomialToProjectiveLaurent (K := K)
      (MvPolynomial.monomial (polynomialLaurentClearedExponent S α) 1) = _
  rw [polynomialToProjectiveLaurent_monomial, polynomialLaurentClearedExponent_toInt m S hα,
    AddMonoidAlgebra.single_mul_single, one_mul]

/-- The actual homogeneous polynomial-fraction map is onto the entire literal
supported Laurent module, because it produces every actual Laurent basis monomial. -/
theorem polynomialCoordinateHomogeneousToLaurent_surjective (m : ℤ) (S : Finset I) :
    Function.Surjective (polynomialCoordinateHomogeneousToLaurent (K := K) (I := I) m S) := by
  let f : polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S →ₗ[K]
      projectiveLaurentAlgebra K I :=
    (subsetHomogeneousLaurentModule m S).subtype.comp (polynomialCoordinateHomogeneousToLaurent m S)
  have hsub : subsetHomogeneousLaurentModule (K := K) (I := I) m S ≤ f.range := by
    rw [subsetHomogeneousLaurentModule, AddMonoidAlgebra.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    exact polynomialCoordinateHomogeneousToLaurent_monomial_preimage m S hα
  intro l
  obtain ⟨z, hz⟩ := hsub l.property
  exact ⟨z, Subtype.ext hz⟩

/-- The actual fixed-integral-degree coordinate-product localization is linearly
equivalent to the literal Laurent module used in the proved Čech contraction. -/
def polynomialCoordinateHomogeneousLaurentEquiv (m : ℤ) (S : Finset I) :
    polynomialCoordinateHomogeneousPiece (K := K) (I := I) m S ≃ₗ[K]
      subsetHomogeneousLaurentModule (K := K) (I := I) m S :=
  LinearEquiv.ofBijective (polynomialCoordinateHomogeneousToLaurent m S)
    ⟨polynomialCoordinateHomogeneousToLaurent_injective m S,
      polynomialCoordinateHomogeneousToLaurent_surjective m S⟩

omit [LinearOrder I] [Fintype I] in
/-- Literal homogeneous coordinate fractions satisfy the actual polynomial
denominator-clearing identity before any monomial rewriting. -/
theorem polynomialCoordinateModuleToLaurent_clear_polynomial
    (S : Finset I) (p : MvPolynomial I K) (n : ℕ) :
    polynomialCoordinateModuleToLaurent S
        (LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) *
      polynomialToProjectiveLaurent (polynomialCoordinateProduct S) ^ n =
        polynomialToProjectiveLaurent p := by
  rw [polynomialToProjectiveLaurent_coordinateProduct, AddMonoidAlgebra.single_pow, one_pow]
  exact polynomialCoordinateModuleToLaurent_clear S p n

omit [LinearOrder I] [Fintype I] in
/-- The actual native divisor restriction commutes with the actual faithful
Laurent maps, as proved by the literal denominator-clearing identities. -/
theorem polynomialCoordinateModuleToLaurent_restriction
    (S T : Finset I) (c : MvPolynomial I K)
    (hy : polynomialCoordinateProduct T = polynomialCoordinateProduct S * c)
    (z : LocalizedModule (Submonoid.powers (polynomialCoordinateProduct (K := K) S))
      (MvPolynomial I K)) :
    polynomialCoordinateModuleToLaurent T
      (actualLocalizedModuleDivisorRestriction (M := MvPolynomial I K)
        (polynomialCoordinateProduct S) (polynomialCoordinateProduct T) ⟨c, hy⟩ z) =
      polynomialCoordinateModuleToLaurent S z := by
  induction z using LocalizedModule.induction_on with
  | h p s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = homogeneousPowerDenominator (polynomialCoordinateProduct S) n :=
      Subtype.ext hn.symm
    rw [hs, actualLocalizedModuleDivisorRestriction_mk _ _ c hy]
    change polynomialCoordinateModuleToLaurent T
      (LocalizedModule.mk (c ^ n * p) (homogeneousPowerDenominator (polynomialCoordinateProduct T) n)) = _
    apply ((polynomialCoordinateProduct_laurent_isUnit (K := K) T).pow n).mul_right_cancel
    have hprod : polynomialToProjectiveLaurent (polynomialCoordinateProduct (K := K) T) ^ n =
        polynomialToProjectiveLaurent (polynomialCoordinateProduct S) ^ n *
          polynomialToProjectiveLaurent c ^ n := by
      rw [hy, map_mul, mul_pow]
    calc
      _ = polynomialToProjectiveLaurent (c ^ n * p) :=
        polynomialCoordinateModuleToLaurent_clear_polynomial T (c ^ n * p) n
      _ = polynomialToProjectiveLaurent p * polynomialToProjectiveLaurent c ^ n := by
        rw [map_mul, map_pow, mul_comm]
      _ = (polynomialCoordinateModuleToLaurent S
          (LocalizedModule.mk p (homogeneousPowerDenominator (polynomialCoordinateProduct S) n)) *
          polynomialToProjectiveLaurent (polynomialCoordinateProduct S) ^ n) *
            polynomialToProjectiveLaurent c ^ n := by
        rw [polynomialCoordinateModuleToLaurent_clear_polynomial]
      _ = _ := by rw [hprod, mul_assoc]

omit [LinearOrder I] [Fintype I] in
/-- Every true coordinate lies in the native integral degree-one polynomial piece. -/
theorem polynomialCoordinate_X_degree (i : I) :
    (MvPolynomial.X i : MvPolynomial I K) ∈ polynomialIntegralGrading 1 :=
  MvPolynomial.isWeightedHomogeneous_X K (fun _ : I => (1 : ℤ)) i

/-- The actual polynomial degree-m coordinate-intersection diagram uses literal
native homogeneous module fractions on every genuine coordinate subset. -/
def polynomialCoordinateHomogeneousDiagram (m : ℤ) : Finset I ⥤ ModuleCat.{u} K :=
  homogeneousCoordinateSubsetDiagram (polynomialIntegralGrading (K := K) (I := I))
    (polynomialIntegralGrading (K := K) (I := I))
    (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m

/-- The literal homogeneous localization-to-Laurent maps commute with genuine
subset restrictions and therefore form an actual natural transformation. -/
def polynomialCoordinateHomogeneousDiagramToLaurent (m : ℤ) :
    polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m ⟶
      polynomialLaurentCechDiagram (K := K) (I := I) m where
  app S := ModuleCat.ofHom (polynomialCoordinateHomogeneousToLaurent m S)
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact polynomialCoordinateModuleToLaurent_restriction S T
      (polynomialCoordinateProduct (T \ S))
      (homogeneousCoordinateSubsetProduct_factor
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) (leOfHom f)) z.val

/-- The actual homogeneous polynomial-localization diagram is naturally
isomorphic to the literal Laurent diagram on which the genuine contraction was proved. -/
def polynomialCoordinateHomogeneousDiagramLaurentIso (m : ℤ) :
    polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m ≅
      polynomialLaurentCechDiagram (K := K) (I := I) m :=
  NatIso.ofComponents
    (fun S => (polynomialCoordinateHomogeneousLaurentEquiv m S).toModuleIso)
    (fun f => (polynomialCoordinateHomogeneousDiagramToLaurent m).naturality f)

/-- The normalized actual subset Čech construction is functorial in genuine
module-valued coordinate-intersection diagrams. -/
def actualSubsetCechFunctor :
    (Finset I ⥤ ModuleCat.{u} K) ⥤ CochainComplex (ModuleCat.{u} K) ℕ where
  obj F := subsetCechComplex F
  map α := subsetCechComplexMap α
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl
  map_comp α β := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl

/-- The true homogeneous polynomial coordinate-localization Čech complex is
isomorphic to the genuinely computed Laurent Čech complex. -/
def polynomialCoordinateHomogeneousCechLaurentIso (m : ℤ) :
    subsetCechComplex (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m) ≅
      polynomialLaurentCechComplex (K := K) (I := I) m :=
  (actualSubsetCechFunctor (K := K) (I := I)).mapIso
    (polynomialCoordinateHomogeneousDiagramLaurentIso m)

include hK in
/-- Every native cohomology module of the actual homogeneous polynomial
coordinate-localization Čech complex is finite in every integral twisting degree. -/
theorem polynomialCoordinateHomogeneousCech_homology_finite (m : ℤ) (p : ℕ) :
    Module.Finite K
      ((subsetCechComplex (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).homology p) := by
  let := polynomialLaurentCechComplex_homology_finite (K := K) (I := I) m p
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso (polynomialCoordinateHomogeneousCechLaurentIso m) p).toLinearEquiv.symm

/-- Positive-degree actual polynomial-localization Čech complexes are exact
away from the genuine top coordinate intersection. -/
theorem polynomialCoordinateHomogeneousCech_exactAt_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 2 ≠ Fintype.card I) :
    (subsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).ExactAt (n + 1) :=
  (polynomialLaurentCechComplex_exactAt_of_ne_top (K := K) (I := I) m n hn).of_iso
    (polynomialCoordinateHomogeneousCechLaurentIso m).symm

/-- The actual native cohomology of homogeneous polynomial coordinate
localizations vanishes in positive degrees away from the top intersection. -/
theorem polynomialCoordinateHomogeneousCech_homology_isZero_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 2 ≠ Fintype.card I) :
    CategoryTheory.Limits.IsZero
      ((subsetCechComplex
        (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).homology (n + 1)) :=
  (polynomialCoordinateHomogeneousCech_exactAt_of_ne_top (K := K) (I := I) m n hn).isZero_homology

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
