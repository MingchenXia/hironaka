import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubset
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Tactic

/-! # Laurent exponent contraction for polynomial projective Čech cohomology

Every chart piece is a literal supported submodule of the multivariate Laurent
algebra, with fixed integral total degree. Its coefficient complexes use the
genuine alternating subset differential.
-/

/-!
Adapted from the same workspace `BingWangEntropy/PolynomialCechCohomology.lean`,
SHA256 7336659be1459e0cd5871ab638e8fafb9b8d7f8e2c3dc69a0601eafabee3e97a.
The scalar ring is generalized from a field to an ORIGINAL Noetherian commutative ring.
The only needed item from ProjectiveSectionFiniteness is the native Laurent-algebra abbrev,
redefined below (original source SHA256 4853b161af90b336994c663ff326526b7907a2d7e2148b2939393fdb581d4997).
No external project module is imported.
-/

universe u

open CategoryTheory

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The ACTUAL original Laurent algebra; no field or fraction-field model is chosen. -/
abbrev projectiveLaurentAlgebra (K : Type u) [CommRing K] (I : Type u) :=
  AddMonoidAlgebra K (I → ℤ)

variable {K I : Type u} [CommRing K] [hK : IsNoetherianRing K] [LinearOrder I]
omit hK

/-- The genuine constant coefficient diagram on coordinate subsets. -/
def scalarSubsetCechDiagram (K I : Type u) [CommRing K] [LinearOrder I] :
    Finset I ⥤ ModuleCat.{u} K :=
  (Functor.const (Finset I)).obj (ModuleCat.of K K)

/-- The literal scalar coefficient differential of the Laurent Čech complex. -/
def scalarSubsetCechDifferential : (Finset I → K) →ₗ[K] (Finset I → K) :=
  subsetCechDifferential (scalarSubsetCechDiagram K I)

@[simp]
theorem scalarSubsetCechDifferential_apply (c : Finset I → K) (S : Finset I) :
    scalarSubsetCechDifferential c S =
      ∑ i ∈ S, subsetCechSign S i • c (S.erase i) := rfl

/-- Scalar coefficient differentials inherit the proved square-zero relation. -/
theorem scalarSubsetCechDifferential_squared (c : Finset I → K) :
    scalarSubsetCechDifferential (scalarSubsetCechDifferential c) = 0 :=
  subsetCechDifferential_squared (scalarSubsetCechDiagram K I) c

/-- Each actual alternating position sign squares to one. -/
theorem subsetCechSign_square (S : Finset I) (i : I) :
    subsetCechSign S i * subsetCechSign S i = 1 := by
  unfold subsetCechSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Inserting the evaluated vertex does not change its position sign. -/
theorem subsetCechSign_insert_self (S : Finset I) (i : I) :
    subsetCechSign (insert i S) i = subsetCechSign S i := by
  simp only [subsetCechSign, Finset.filter_insert, lt_self_iff_false, if_false]

/-- Erasing the evaluated vertex does not change its position sign. -/
theorem subsetCechSign_erase_self (S : Finset I) (i : I) :
    subsetCechSign (S.erase i) i = subsetCechSign S i := by
  unfold subsetCechSign
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp

/-- The actual signs in the two terms of the simplex contraction cancel. -/
theorem subsetCechSign_contraction (S : Finset I) {i j : I}
    (hi : i ∈ S) (hj : j ∉ S) :
    subsetCechSign S i * subsetCechSign (S.erase i) j =
      -(subsetCechSign S j * subsetCechSign (insert j S) i) := by
  have hij : i ≠ j := by intro h; subst j; exact hj hi
  have h := subsetCechSign_two_deletions (insert j S)
    (Finset.mem_insert_self j S) (Finset.mem_insert_of_mem hi) hij.symm
  rw [subsetCechSign_insert_self, Finset.erase_insert hj] at h
  have herase : (insert j S).erase i = insert j (S.erase i) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_insert]
    aesop
  rw [herase, subsetCechSign_insert_self] at h
  calc
    subsetCechSign S i * subsetCechSign (S.erase i) j =
        subsetCechSign S j *
          (subsetCechSign S j * subsetCechSign S i) *
            subsetCechSign (S.erase i) j := by
              rw [← mul_assoc (subsetCechSign S j), subsetCechSign_square, one_mul]
    _ = -(subsetCechSign S j * subsetCechSign (insert j S) i) *
        (subsetCechSign (S.erase i) j * subsetCechSign (S.erase i) j) := by
          rw [h]
          ring
    _ = -(subsetCechSign S j * subsetCechSign (insert j S) i) := by
      rw [subsetCechSign_square, mul_one]

/-- The literal simplex contraction inserts the chosen coordinate vertex. -/
def scalarSubsetCechContraction (j : I) : (Finset I → K) →ₗ[K] (Finset I → K) where
  toFun c S := if j ∈ S then 0 else subsetCechSign S j • c (insert j S)
  map_add' c c' := by
    funext S
    by_cases hj : j ∈ S <;> simp [hj, smul_add]
  map_smul' a c := by
    funext S
    by_cases hj : j ∈ S
    · simp only [if_pos hj, Pi.smul_apply, smul_zero]
    · simp only [if_neg hj, Pi.smul_apply, RingHom.id_apply]
      exact smul_comm _ _ _

@[simp]
theorem scalarSubsetCechContraction_apply (j : I) (c : Finset I → K) (S : Finset I) :
    scalarSubsetCechContraction j c S =
      if j ∈ S then 0 else subsetCechSign S j • c (insert j S) := rfl

/-- The actual subset operations used in the two contraction terms agree. -/
theorem subsetCech_erase_insert_of_ne (S : Finset I) {i j : I} (hij : i ≠ j) :
    (insert j S).erase i = insert j (S.erase i) := by
  ext t
  simp only [Finset.mem_erase, Finset.mem_insert]
  aesop

/-- The literal signed insertion map contracts the augmented simplex complex. -/
theorem scalarSubsetCechContraction_identity (j : I) (c : Finset I → K) :
    scalarSubsetCechDifferential (scalarSubsetCechContraction j c) +
      scalarSubsetCechContraction j (scalarSubsetCechDifferential c) = c := by
  funext S
  simp only [Pi.add_apply]
  by_cases hj : j ∈ S
  · rw [scalarSubsetCechContraction_apply, if_pos hj, add_zero,
      scalarSubsetCechDifferential_apply]
    rw [Finset.sum_eq_single j]
    · simp only [scalarSubsetCechContraction_apply, Finset.notMem_erase, if_false,
        Finset.insert_erase hj, smul_smul, subsetCechSign_erase_self,
        subsetCechSign_square, one_smul]
    · intro i hi hij
      have hji : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
      simp only [scalarSubsetCechContraction_apply, if_pos hji, smul_zero]
    · intro hj'
      exact (hj' hj).elim
  · have hj' (i : I) : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hleft :
        scalarSubsetCechDifferential (scalarSubsetCechContraction j c) S =
          ∑ i ∈ S, (subsetCechSign S i * subsetCechSign (S.erase i) j) •
            c (insert j (S.erase i)) := by
      simp only [scalarSubsetCechDifferential_apply, scalarSubsetCechContraction_apply,
        if_neg (hj' _), smul_smul]
    have hright :
        scalarSubsetCechContraction j (scalarSubsetCechDifferential c) S =
          c S + ∑ i ∈ S,
            (subsetCechSign S j * subsetCechSign (insert j S) i) •
              c ((insert j S).erase i) := by
      rw [scalarSubsetCechContraction_apply, if_neg hj,
        scalarSubsetCechDifferential_apply, Finset.sum_insert hj,
        smul_add, Finset.smul_sum]
      simp only [smul_smul, subsetCechSign_insert_self, subsetCechSign_square,
        Finset.erase_insert hj, one_smul]
    rw [hleft, hright]
    have hcancel :
        (∑ i ∈ S, (subsetCechSign S i * subsetCechSign (S.erase i) j) •
            c (insert j (S.erase i))) +
          (∑ i ∈ S, (subsetCechSign S j * subsetCechSign (insert j S) i) •
            c ((insert j S).erase i)) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i ≠ j := by intro h; subst j; exact hj hi
      rw [subsetCech_erase_insert_of_ne S hij,
        subsetCechSign_contraction S hi hj, neg_smul]
      exact neg_add_cancel _
    calc
      _ = c S +
          ((∑ i ∈ S, (subsetCechSign S i * subsetCechSign (S.erase i) j) •
            c (insert j (S.erase i))) +
            (∑ i ∈ S, (subsetCechSign S j * subsetCechSign (insert j S) i) •
              c ((insert j S).erase i))) := by abel
      _ = c S := by rw [hcancel, add_zero]

section FiniteCoordinates

variable [Fintype I]

/-- The actual finite set of coordinates with a negative Laurent exponent. -/
def projectiveNegativeSupport (α : I → ℤ) : Finset I :=
  Finset.univ.filter (fun i => α i < 0)

/-- Fixed integral total degree and precisely the denominators available on an
actual coordinate intersection. -/
def subsetHomogeneousLaurentExponents (m : ℤ) (S : Finset I) : Set (I → ℤ) :=
  {α | (∑ i, α i) = m ∧ ∀ i, i ∉ S → 0 ≤ α i}

/-- The literal homogeneous Laurent module on a coordinate intersection. -/
def subsetHomogeneousLaurentModule (m : ℤ) (S : Finset I) :
    Submodule K (projectiveLaurentAlgebra K I) :=
  AddMonoidAlgebra.supported K K (subsetHomogeneousLaurentExponents m S)

/-- The denominator condition is exactly containment of actual negative support. -/
theorem subsetHomogeneousLaurentExponents_iff (m : ℤ) (S : Finset I) (α : I → ℤ) :
    α ∈ subsetHomogeneousLaurentExponents m S ↔
      (∑ i, α i) = m ∧ projectiveNegativeSupport α ⊆ S := by
  simp only [subsetHomogeneousLaurentExponents, Set.mem_ofPred_eq,
    projectiveNegativeSupport, Finset.subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, fun i hi => by by_contra hni; exact (not_lt_of_ge (h i hni)) hi⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, fun i hi => le_of_not_gt (fun hneg => hi (h hneg))⟩

omit [LinearOrder I] in
/-- Actual coordinate restrictions are literal inclusions in the common Laurent
algebra, produced solely by adding inverted coordinates. -/
theorem subsetHomogeneousLaurentModule_mono (m : ℤ) {S T : Finset I}
    (hST : S ⊆ T) :
    subsetHomogeneousLaurentModule (K := K) m S ≤ subsetHomogeneousLaurentModule m T := by
  apply AddMonoidAlgebra.supported_mono
  intro α hα
  exact ⟨hα.1, fun i hi => hα.2 i (fun h => hi (hST h))⟩

/-- The actual polynomial homogeneous coordinate Čech diagram in every integral degree. -/
def polynomialLaurentCechDiagram (m : ℤ) : Finset I ⥤ ModuleCat.{u} K where
  obj S := ModuleCat.of K (subsetHomogeneousLaurentModule (K := K) m S)
  map f := ModuleCat.ofHom (Submodule.inclusion
    (subsetHomogeneousLaurentModule_mono m (leOfHom f)))
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The genuine normalized coordinate-cover Laurent Čech complex in integral degree m. -/
def polynomialLaurentCechComplex (m : ℤ) : CochainComplex (ModuleCat.{u} K) ℕ :=
  subsetCechComplex (polynomialLaurentCechDiagram (K := K) (I := I) m)

/-- Genuine degree-m nonnegative Laurent exponent vectors. -/
def nonnegativeIntegralHomogeneousExponents (m : ℤ) : Set (I → ℤ) :=
  {α | (∑ i, α i) = m ∧ ∀ i, 0 ≤ α i}

/-- Genuine degree-m strictly negative Laurent exponent vectors. -/
def negativeIntegralHomogeneousExponents (m : ℤ) : Set (I → ℤ) :=
  {α | (∑ i, α i) = m ∧ ∀ i, α i < 0}

omit [LinearOrder I] in
/-- Each actual nonnegative fixed-degree exponent lies in a finite coordinate interval. -/
theorem nonnegativeIntegralHomogeneousExponents_bound (m : ℤ) {α : I → ℤ}
    (hα : α ∈ nonnegativeIntegralHomogeneousExponents (I := I) m) (i : I) :
    α i ∈ Set.Icc 0 m := by
  refine ⟨hα.2 i, ?_⟩
  rw [← hα.1]
  exact Finset.single_le_sum (fun j _ => hα.2 j) (Finset.mem_univ i)

/-- Each actual strictly negative fixed-degree exponent lies in a finite coordinate interval. -/
theorem negativeIntegralHomogeneousExponents_bound (m : ℤ) {α : I → ℤ}
    (hα : α ∈ negativeIntegralHomogeneousExponents (I := I) m) (i : I) :
    α i ∈ Set.Icc m (-1) := by
  have hsum := Finset.sum_erase_add Finset.univ α (Finset.mem_univ i)
  have hnonpos : (∑ j ∈ Finset.univ.erase i, α j) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => le_of_lt (hα.2 j))
  rw [hα.1] at hsum
  have hi := hα.2 i
  constructor <;> omega

omit [LinearOrder I] in
/-- The actual nonnegative fixed-degree exponent family is finite. -/
theorem nonnegativeIntegralHomogeneousExponents_finite (m : ℤ) :
    (nonnegativeIntegralHomogeneousExponents (I := I) m).Finite := by
  apply (Set.Finite.pi (fun _ : I => Set.finite_Icc 0 m)).subset
  intro α hα i _
  exact nonnegativeIntegralHomogeneousExponents_bound m hα i

/-- The actual strictly negative fixed-degree exponent family is finite. -/
theorem negativeIntegralHomogeneousExponents_finite (m : ℤ) :
    (negativeIntegralHomogeneousExponents (I := I) m).Finite := by
  apply (Set.Finite.pi (fun _ : I => Set.finite_Icc m (-1))).subset
  intro α hα i _
  exact negativeIntegralHomogeneousExponents_bound m hα i

/-- Extract one actual Laurent monomial coefficient as a native linear map. -/
def projectiveLaurentCoefficient (α : I → ℤ) :
    projectiveLaurentAlgebra K I →ₗ[K] K :=
  (Finsupp.lapply α).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

omit [LinearOrder I] [Fintype I] in
@[simp]
theorem projectiveLaurentCoefficient_apply (α : I → ℤ)
    (f : projectiveLaurentAlgebra K I) :
    projectiveLaurentCoefficient α f = f.coeff α := rfl

/-- The actual coefficient cochain family of a genuine Laurent Čech cochain. -/
def polynomialLaurentCechCoefficient (m : ℤ) (α : I → ℤ) :
    subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) →ₗ[K]
      (Finset I → K) :=
  LinearMap.pi (fun S =>
    ((projectiveLaurentCoefficient α).comp (subsetHomogeneousLaurentModule m S).subtype).comp
      (LinearMap.proj S))

omit [LinearOrder I] in
@[simp]
theorem polynomialLaurentCechCoefficient_apply (m : ℤ) (α : I → ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m))
    (S : Finset I) :
    polynomialLaurentCechCoefficient m α c S = (c S).val.coeff α := rfl

/-- Coefficient extraction commutes with the actual native Laurent Čech differential. -/
theorem polynomialLaurentCechCoefficient_differential (m : ℤ) (α : I → ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)) :
    polynomialLaurentCechCoefficient m α
        (subsetCechDifferential (polynomialLaurentCechDiagram m) c) =
      scalarSubsetCechDifferential (polynomialLaurentCechCoefficient m α c) := by
  funext S
  change ((projectiveLaurentCoefficient α).comp
    (subsetHomogeneousLaurentModule m S).subtype) (∑ i ∈ S, _) =
      ∑ i ∈ S, _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rfl

/-- A chosen nonnegative coordinate contracts precisely the exponent complexes
which possess one; no chosen vertex exists for the strictly negative family. -/
def projectiveLaurentContractionIndex (α : I → ℤ) : Option I :=
  if h : ∃ i, 0 ≤ α i then some (Classical.choose h) else none

omit [LinearOrder I] in
/-- Every produced contraction coordinate really has a nonnegative exponent. -/
theorem projectiveLaurentContractionIndex_nonnegative {α : I → ℤ} {j : I}
    (h : projectiveLaurentContractionIndex α = some j) : 0 ≤ α j := by
  classical
  unfold projectiveLaurentContractionIndex at h
  split_ifs at h with hex
  · have hj := Option.some.inj h
    rw [← hj]
    exact Classical.choose_spec hex

omit [LinearOrder I] in
/-- The actual surviving exponent family consists exactly of all-negative exponents. -/
theorem projectiveLaurentContractionIndex_none_iff (α : I → ℤ) :
    projectiveLaurentContractionIndex α = none ↔ ∀ i, α i < 0 := by
  classical
  unfold projectiveLaurentContractionIndex
  by_cases h : ∃ i, 0 ≤ α i
  · simp only [dif_pos h, Option.some_ne_none, false_iff]
    rintro hall
    obtain ⟨i, hi⟩ := h
    exact (not_lt_of_ge hi) (hall i)
  · simp only [dif_neg h, true_iff]
    intro i
    exact lt_of_not_ge (fun hi => h ⟨i, hi⟩)

/-- Filtering actual Laurent coefficients is an actual linear operator. -/
def projectiveLaurentFilter (p : (I → ℤ) → Prop) [DecidablePred p] :
    projectiveLaurentAlgebra K I →ₗ[K] projectiveLaurentAlgebra K I := by
  let f : ((I → ℤ) →₀ K) →ₗ[K] ((I → ℤ) →₀ K) :=
    { toFun := Finsupp.filter p
      map_add' := fun _ _ => Finsupp.filter_add
      map_smul' := fun _ _ => Finsupp.filter_smul }
  exact (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    (f.comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

omit [LinearOrder I] [Fintype I] in
@[simp]
theorem projectiveLaurentFilter_coeff (p : (I → ℤ) → Prop) [DecidablePred p]
    (f : projectiveLaurentAlgebra K I) (α : I → ℤ) :
    (projectiveLaurentFilter p f).coeff α = if p α then f.coeff α else 0 := by
  exact Finsupp.filter_apply p f.coeff α

/-- The contraction keeps just the actual monomials assigned to coordinate j.
Its target chart is legitimate because those monomials have no negative j exponent. -/
def polynomialLaurentCechContractionTerm (m : ℤ) (S : Finset I) (j : I) :
    subsetHomogeneousLaurentModule (K := K) m (insert j S) →ₗ[K]
      subsetHomogeneousLaurentModule (K := K) m S :=
  ((projectiveLaurentFilter (fun α => projectiveLaurentContractionIndex α = some j)).comp
    (subsetHomogeneousLaurentModule m (insert j S)).subtype).codRestrict
      (subsetHomogeneousLaurentModule m S) (by
        intro f
        apply AddMonoidAlgebra.mem_supported.mpr
        intro α hα
        have hcoeff := Finsupp.mem_support_iff.mp hα
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hcoeff
        rw [projectiveLaurentFilter_coeff] at hcoeff
        split_ifs at hcoeff with hindex
        · have hold := (AddMonoidAlgebra.mem_supported.mp f.property)
            (Finsupp.mem_support_iff.mpr hcoeff)
          refine ⟨hold.1, ?_⟩
          intro i hi
          by_cases hij : i = j
          · subst i
            exact projectiveLaurentContractionIndex_nonnegative hindex
          · exact hold.2 i (by simpa only [Finset.mem_insert, not_or] using ⟨hij, hi⟩)
        · exact (hcoeff rfl).elim)

@[simp]
theorem polynomialLaurentCechContractionTerm_coeff (m : ℤ) (S : Finset I) (j : I)
    (f : subsetHomogeneousLaurentModule (K := K) m (insert j S)) (α : I → ℤ) :
    (polynomialLaurentCechContractionTerm m S j f).val.coeff α =
      if projectiveLaurentContractionIndex α = some j then f.val.coeff α else 0 :=
  projectiveLaurentFilter_coeff _ _ _

/-- The actual Laurent contraction is a finite sum of honest coefficient filters,
so it preserves finite monomial support and every actual chart denominator bound. -/
def polynomialLaurentCechContraction (m : ℤ) :
    subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) →ₗ[K]
      subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) :=
  LinearMap.pi (fun S =>
    ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), subsetCechSign S j •
      ((polynomialLaurentCechContractionTerm m S j).comp (LinearMap.proj (insert j S))))

/-- Literal coefficients of the finite-filter Laurent contraction. -/
theorem polynomialLaurentCechContraction_coeff_sum (m : ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m))
    (S : Finset I) (α : I → ℤ) :
    (polynomialLaurentCechContraction m c S).val.coeff α =
      ∑ j ∈ Finset.univ.filter (fun j => j ∉ S), subsetCechSign S j •
        (if projectiveLaurentContractionIndex α = some j then
          (c (insert j S)).val.coeff α else 0) := by
  simp only [polynomialLaurentCechContraction, LinearMap.pi_apply,
    LinearMap.sum_apply]
  change ((projectiveLaurentCoefficient (K := K) α).comp
    (subsetHomogeneousLaurentModule m S).subtype)
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((projectiveLaurentCoefficient (K := K) α).comp
    (subsetHomogeneousLaurentModule m S).subtype)
      (subsetCechSign S j • polynomialLaurentCechContractionTerm m S j (c (insert j S))) = _
  rw [map_zsmul]
  exact congrArg (fun x : K => subsetCechSign S j • x)
    (polynomialLaurentCechContractionTerm_coeff m S j (c (insert j S)) α)

/-- For an actual assigned exponent, Laurent contraction is exactly its produced
scalar simplex contraction. -/
theorem polynomialLaurentCechContraction_coeff_some (m : ℤ) {α : I → ℤ} {j : I}
    (hindex : projectiveLaurentContractionIndex α = some j)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)) :
    polynomialLaurentCechCoefficient m α (polynomialLaurentCechContraction m c) =
      scalarSubsetCechContraction j (polynomialLaurentCechCoefficient m α c) := by
  funext S
  rw [polynomialLaurentCechCoefficient_apply, polynomialLaurentCechContraction_coeff_sum,
    scalarSubsetCechContraction_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by
      intro h
      subst i
      exact (Finset.mem_filter.mp hi).2 hj
    simp only [hindex, Option.some.injEq, if_neg hij.symm, smul_zero]
  · rw [if_neg hj, Finset.sum_eq_single j]
    · simp [hindex]
    · intro i _ hij
      simp only [hindex, Option.some.injEq, if_neg hij.symm, smul_zero]
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)).elim

/-- Strictly negative actual exponents have no contraction term. -/
theorem polynomialLaurentCechContraction_coeff_none (m : ℤ) {α : I → ℤ}
    (hindex : projectiveLaurentContractionIndex α = none)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)) :
    polynomialLaurentCechCoefficient m α (polynomialLaurentCechContraction m c) = 0 := by
  funext S
  rw [polynomialLaurentCechCoefficient_apply, polynomialLaurentCechContraction_coeff_sum]
  simp [hindex]

omit [LinearOrder I] in
/-- The actual fixed-degree Čech cochains are separated by their literal
Laurent monomial coefficients. -/
theorem polynomialLaurentCechCoefficient_ext (m : ℤ)
    {c c' : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)}
    (h : ∀ α, polynomialLaurentCechCoefficient m α c =
      polynomialLaurentCechCoefficient m α c') : c = c' := by
  funext S
  apply Subtype.ext
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro α
  exact congrFun (h α) S

/-- Keeping actual strictly negative Laurent monomials preserves every actual
coordinate chart piece. -/
def polynomialLaurentCechSurvivorTerm (m : ℤ) (S : Finset I) :
    subsetHomogeneousLaurentModule (K := K) m S →ₗ[K]
      subsetHomogeneousLaurentModule (K := K) m S :=
  ((projectiveLaurentFilter (fun α => projectiveLaurentContractionIndex α = none)).comp
    (subsetHomogeneousLaurentModule m S).subtype).codRestrict
      (subsetHomogeneousLaurentModule m S) (by
        intro f
        apply AddMonoidAlgebra.mem_supported.mpr
        intro α hα
        have hcoeff := Finsupp.mem_support_iff.mp hα
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hcoeff
        rw [projectiveLaurentFilter_coeff] at hcoeff
        split_ifs at hcoeff
        · exact (AddMonoidAlgebra.mem_supported.mp f.property)
            (Finsupp.mem_support_iff.mpr hcoeff)
        · exact (hcoeff rfl).elim)

/-- The actual surviving-monomial projection on the actual fixed-degree Čech cube. -/
def polynomialLaurentCechSurvivor (m : ℤ) :
    subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) →ₗ[K]
      subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m) :=
  LinearMap.pi (fun S => (polynomialLaurentCechSurvivorTerm m S).comp (LinearMap.proj S))

omit [LinearOrder I] in
@[simp]
theorem polynomialLaurentCechSurvivor_coeff (m : ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m))
    (S : Finset I) (α : I → ℤ) :
    (polynomialLaurentCechSurvivor m c S).val.coeff α =
      if projectiveLaurentContractionIndex α = none then (c S).val.coeff α else 0 :=
  projectiveLaurentFilter_coeff _ _ _

/-- The genuine finite-support Laurent contraction leaves precisely the actual
strictly-negative exponent projection. -/
theorem polynomialLaurentCechContraction_identity (m : ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)) :
    subsetCechDifferential (polynomialLaurentCechDiagram m)
        (polynomialLaurentCechContraction m c) +
      polynomialLaurentCechContraction m
        (subsetCechDifferential (polynomialLaurentCechDiagram m) c) +
      polynomialLaurentCechSurvivor m c = c := by
  apply polynomialLaurentCechCoefficient_ext m
  intro α
  rw [map_add, map_add, polynomialLaurentCechCoefficient_differential]
  cases hindex : projectiveLaurentContractionIndex α with
  | none =>
    rw [polynomialLaurentCechContraction_coeff_none m hindex,
      polynomialLaurentCechContraction_coeff_none m hindex, map_zero, zero_add, zero_add]
    funext S
    simp only [polynomialLaurentCechCoefficient_apply,
      polynomialLaurentCechSurvivor_coeff, hindex, if_true]
  | some j =>
    rw [polynomialLaurentCechContraction_coeff_some m hindex,
      polynomialLaurentCechContraction_coeff_some m hindex,
      polynomialLaurentCechCoefficient_differential]
    have hzero : polynomialLaurentCechCoefficient m α
        (polynomialLaurentCechSurvivor m c) = 0 := by
      funext S
      simp [hindex]
    rw [hzero, add_zero]
    exact scalarSubsetCechContraction_identity j (polynomialLaurentCechCoefficient m α c)

/-- Actual Laurent contraction decreases cardinal degree by one. -/
theorem polynomialLaurentCechContraction_mem_cardPiece (m : ℤ) (n : ℕ)
    (c : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)) :
    polynomialLaurentCechContraction m c.val ∈
      subsetCechCardPiece (polynomialLaurentCechDiagram m) n := by
  intro S hS
  simp only [polynomialLaurentCechContraction, LinearMap.pi_apply, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  have hcard : (insert j S).card ≠ n + 1 := by
    rw [Finset.card_insert_of_notMem hj']
    exact fun h => hS (Nat.add_right_cancel h)
  change subsetCechSign S j • polynomialLaurentCechContractionTerm m S j
    (c.val (insert j S)) = 0
  rw [c.property (insert j S) hcard, map_zero, smul_zero]

omit [LinearOrder I] in
/-- The actual survivor projection preserves cardinal degree. -/
theorem polynomialLaurentCechSurvivor_mem_cardPiece (m : ℤ) (n : ℕ)
    (c : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) n) :
    polynomialLaurentCechSurvivor m c.val ∈
      subsetCechCardPiece (polynomialLaurentCechDiagram m) n := by
  intro S hS
  change polynomialLaurentCechSurvivorTerm m S (c.val S) = 0
  rw [c.property S hS, map_zero]

/-- The actual surviving Laurent coefficient module in fixed integral degree. -/
def negativeIntegralLaurentModule (m : ℤ) : Submodule K (projectiveLaurentAlgebra K I) :=
  AddMonoidAlgebra.supported K K (negativeIntegralHomogeneousExponents m)

/-- Finiteness of the actual surviving Laurent module follows from its literal
finite monomial basis, not from a cohomology premise. -/
theorem negativeIntegralLaurentModule_finite (m : ℤ) :
    Module.Finite K (negativeIntegralLaurentModule (K := K) (I := I) m) := by
  let := (negativeIntegralHomogeneousExponents_finite (I := I) m).to_subtype
  exact Module.Finite.of_basis
    (⟨AddMonoidAlgebra.supportedEquivFinsupp _⟩ :
      Module.Basis (negativeIntegralHomogeneousExponents (I := I) m) K
        (negativeIntegralLaurentModule (K := K) (I := I) m))

omit [LinearOrder I] in
/-- Every actual survivor section has only genuinely strictly-negative monomials. -/
theorem polynomialLaurentCechSurvivor_mem_negative (m : ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m)) (S : Finset I) :
    (polynomialLaurentCechSurvivor m c S).val ∈ negativeIntegralLaurentModule m := by
  apply AddMonoidAlgebra.mem_supported.mpr
  intro α hα
  have hcoeff := Finsupp.mem_support_iff.mp hα
  rw [polynomialLaurentCechSurvivor_coeff] at hcoeff
  split_ifs at hcoeff with hindex
  · have hold := (AddMonoidAlgebra.mem_supported.mp (c S).property)
      (Finsupp.mem_support_iff.mpr hcoeff)
    exact ⟨hold.1, (projectiveLaurentContractionIndex_none_iff α).mp hindex⟩
  · exact (hcoeff rfl).elim

/-- An honest linear embedding of the actual survivor image into a finite product
of actual finite surviving-monomial modules. -/
def polynomialLaurentCechSurvivorRangeEmbedding (m : ℤ) :
    (polynomialLaurentCechSurvivor (K := K) (I := I) m).range →ₗ[K]
      (Finset I → negativeIntegralLaurentModule (K := K) (I := I) m) where
  toFun c S := ⟨(c.val S).val, by
    obtain ⟨d, hd⟩ := c.property
    rw [← hd]
    exact polynomialLaurentCechSurvivor_mem_negative m d S⟩
  map_add' c c' := by funext S; rfl
  map_smul' a c := by funext S; rfl

omit [LinearOrder I] in
/-- The produced embedding of the actual survivor image is faithful. -/
theorem polynomialLaurentCechSurvivorRangeEmbedding_injective (m : ℤ) :
    Function.Injective (polynomialLaurentCechSurvivorRangeEmbedding (K := K) (I := I) m) := by
  intro c c' h
  apply Subtype.ext
  funext S
  apply Subtype.ext
  exact congrArg (fun f : Finset I → negativeIntegralLaurentModule (K := K) m =>
    (f S).val) h

include hK in
/-- The actual survivor image in the actual Laurent Čech cube is finite. -/
theorem polynomialLaurentCechSurvivor_range_finite (m : ℤ) :
    Module.Finite K ((polynomialLaurentCechSurvivor (K := K) (I := I) m).range) := by
  let := negativeIntegralLaurentModule_finite (K := K) (I := I) m
  exact Module.Finite.of_injective (polynomialLaurentCechSurvivorRangeEmbedding m)
    (polynomialLaurentCechSurvivorRangeEmbedding_injective m)

omit [LinearOrder I] in
/-- The empty-intersection Laurent module is exactly the actual nonnegative
fixed-degree polynomial monomial module. -/
theorem subsetHomogeneousLaurentModule_empty (m : ℤ) :
    subsetHomogeneousLaurentModule (K := K) (I := I) m ∅ =
      AddMonoidAlgebra.supported K K (nonnegativeIntegralHomogeneousExponents m) := by
  unfold subsetHomogeneousLaurentModule
  congr 1
  ext α
  simp [subsetHomogeneousLaurentExponents, nonnegativeIntegralHomogeneousExponents]

omit [LinearOrder I] in
/-- The genuine empty-intersection polynomial degree piece is finite. -/
theorem subsetHomogeneousLaurentModule_empty_finite (m : ℤ) :
    Module.Finite K (subsetHomogeneousLaurentModule (K := K) (I := I) m ∅) := by
  rw [subsetHomogeneousLaurentModule_empty]
  let := (nonnegativeIntegralHomogeneousExponents_finite (I := I) m).to_subtype
  exact Module.Finite.of_basis
    (⟨AddMonoidAlgebra.supportedEquivFinsupp _⟩ :
      Module.Basis (nonnegativeIntegralHomogeneousExponents (I := I) m) K
        (AddMonoidAlgebra.supported K K (nonnegativeIntegralHomogeneousExponents m)))

/-- The empty-subset value reads the entire actual cardinal-zero piece. -/
def polynomialLaurentCechCardZeroEvaluation (m : ℤ) :
    subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 0 →ₗ[K]
      subsetHomogeneousLaurentModule (K := K) (I := I) m ∅ :=
  (LinearMap.proj ∅).comp (subsetCechCardPiece (polynomialLaurentCechDiagram m) 0).subtype

omit [LinearOrder I] in
/-- The cardinal-zero cochain is determined by the actual empty intersection. -/
theorem polynomialLaurentCechCardZeroEvaluation_injective (m : ℤ) :
    Function.Injective (polynomialLaurentCechCardZeroEvaluation (K := K) (I := I) m) := by
  intro c c' h
  apply Subtype.ext
  funext S
  by_cases hS : S.card = 0
  · have hS' : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    exact h
  · rw [c.property S hS, c'.property S hS]

omit [LinearOrder I] in
include hK in
/-- Actual cardinal-zero cochains are finite-dimensional because their actual
empty intersection has only finitely many nonnegative degree-m monomials. -/
theorem polynomialLaurentCechCardZero_finite (m : ℤ) :
    Module.Finite K (subsetCechCardPiece
      (polynomialLaurentCechDiagram (K := K) (I := I) m) 0) := by
  let := subsetHomogeneousLaurentModule_empty_finite (K := K) (I := I) m
  exact Module.Finite.of_injective (polynomialLaurentCechCardZeroEvaluation m)
    (polynomialLaurentCechCardZeroEvaluation_injective m)

/-- Actual nonaugmented degree-zero cocycles are embedded by their produced
empty-piece primitive and their produced strictly-negative survivor. -/
def polynomialLaurentCechZeroCyclesEmbedding (m : ℤ) :
    (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) 1).ker →ₗ[K]
      (subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 0 ×
        (polynomialLaurentCechSurvivor (K := K) (I := I) m).range) where
  toFun c :=
    (⟨polynomialLaurentCechContraction m c.val.val,
      polynomialLaurentCechContraction_mem_cardPiece m 0 c.val⟩,
     ⟨polynomialLaurentCechSurvivor m c.val.val, ⟨c.val.val, rfl⟩⟩)
  map_add' c c' := by
    apply Prod.ext <;> apply Subtype.ext
    · exact (polynomialLaurentCechContraction m).map_add _ _
    · exact (polynomialLaurentCechSurvivor m).map_add _ _
  map_smul' a c := by
    apply Prod.ext <;> apply Subtype.ext
    · exact (polynomialLaurentCechContraction m).map_smul _ _
    · exact (polynomialLaurentCechSurvivor m).map_smul _ _

/-- The genuine contraction identity separates actual nonaugmented H0 cocycles. -/
theorem polynomialLaurentCechZeroCyclesEmbedding_injective (m : ℤ) :
    Function.Injective (polynomialLaurentCechZeroCyclesEmbedding (K := K) (I := I) m) := by
  intro c c' h
  have hH : polynomialLaurentCechContraction m c.val.val =
      polynomialLaurentCechContraction m c'.val.val :=
    congrArg (fun z => z.1.val) h
  have hP : polynomialLaurentCechSurvivor m c.val.val =
      polynomialLaurentCechSurvivor m c'.val.val :=
    congrArg (fun z => z.2.val) h
  have hc := polynomialLaurentCechContraction_identity m c.val.val
  have hc' := polynomialLaurentCechContraction_identity m c'.val.val
  have hdc : subsetCechDifferential (polynomialLaurentCechDiagram m) c.val.val = 0 :=
    congrArg Subtype.val c.property
  have hdc' : subsetCechDifferential (polynomialLaurentCechDiagram m) c'.val.val = 0 :=
    congrArg Subtype.val c'.property
  rw [hdc, map_zero, add_zero] at hc
  rw [hdc', map_zero, add_zero] at hc'
  apply Subtype.ext
  apply Subtype.ext
  rw [← hc, ← hc', hH, hP]

include hK in
/-- The actual nonaugmented degree-zero Čech cocycle module is finite; the genuine
empty-intersection image is retained instead of being incorrectly quotiented away. -/
theorem polynomialLaurentCechZeroCycles_finite (m : ℤ) :
    Module.Finite K ((subsetCechCardDifferential
      (polynomialLaurentCechDiagram (K := K) (I := I) m) 1).ker) := by
  let := polynomialLaurentCechCardZero_finite (K := K) (I := I) m
  let := polynomialLaurentCechSurvivor_range_finite (K := K) (I := I) m
  exact Module.Finite.of_injective (R := K)
    (M := (subsetCechCardDifferential
      (polynomialLaurentCechDiagram (K := K) (I := I) m) 1).ker)
    (N := subsetCechCardPiece
      (polynomialLaurentCechDiagram (K := K) (I := I) m) 0 ×
        (polynomialLaurentCechSurvivor (K := K) (I := I) m).range)
    (polynomialLaurentCechZeroCyclesEmbedding (K := K) (I := I) m)
    (polynomialLaurentCechZeroCyclesEmbedding_injective (K := K) (I := I) m)

/-- The genuine Laurent contraction between actual consecutive cardinal pieces. -/
def polynomialLaurentCechCardContraction (m : ℤ) (n : ℕ) :
    subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1) →ₗ[K]
      subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) n :=
  ((polynomialLaurentCechContraction m).comp
    (subsetCechCardPiece (polynomialLaurentCechDiagram m) (n + 1)).subtype).codRestrict
      (subsetCechCardPiece (polynomialLaurentCechDiagram m) n)
        (polynomialLaurentCechContraction_mem_cardPiece m n)

/-- The genuine strictly-negative projection on an actual cardinal piece. -/
def polynomialLaurentCechCardSurvivor (m : ℤ) (n : ℕ) :
    subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1) →ₗ[K]
      subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1) :=
  ((polynomialLaurentCechSurvivor m).comp
    (subsetCechCardPiece (polynomialLaurentCechDiagram m) (n + 1)).subtype).codRestrict
      (subsetCechCardPiece (polynomialLaurentCechDiagram m) (n + 1))
        (polynomialLaurentCechSurvivor_mem_cardPiece m (n + 1))

/-- The actual cycle module in cardinal degree n+1. -/
abbrev polynomialLaurentCechCardCycles (m : ℤ) (n : ℕ) :=
  (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)).ker

/-- Actual cycle coefficients retain the native additive group of the actual kernel. -/
instance polynomialLaurentCechCardCyclesAddCommGroup (m : ℤ) (n : ℕ) :
    AddCommGroup (polynomialLaurentCechCardCycles (K := K) (I := I) m n) :=
  (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)).ker.addCommGroup

/-- Actual cycle coefficients retain the native scalar action of the actual kernel. -/
instance polynomialLaurentCechCardCyclesModule (m : ℤ) (n : ℕ) :
    Module K (polynomialLaurentCechCardCycles (K := K) (I := I) m n) :=
  (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)).ker.module

/-- Every actual cocycle equals an actual boundary plus its produced actual
strictly-negative representative. -/
theorem polynomialLaurentCechCardCycles_identity (m : ℤ) (n : ℕ)
    (c : polynomialLaurentCechCardCycles (K := K) (I := I) m n) :
    subsetCechCardDifferential (polynomialLaurentCechDiagram m) n
        (polynomialLaurentCechCardContraction m n c.val) +
      polynomialLaurentCechCardSurvivor m n c.val = c.val := by
  apply Subtype.ext
  have h := polynomialLaurentCechContraction_identity m c.val.val
  have hd : subsetCechDifferential (polynomialLaurentCechDiagram m) c.val.val = 0 :=
    congrArg Subtype.val c.property
  rw [hd, map_zero, add_zero] at h
  exact h

/-- The actual incoming differential takes values in the actual next kernel,
as certified by the already proved native d²=0 relation. -/
def polynomialLaurentCechCardToCycles (m : ℤ) (n : ℕ) :
    subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) n →ₗ[K]
      polynomialLaurentCechCardCycles (K := K) (I := I) m n :=
  (subsetCechCardDifferential (polynomialLaurentCechDiagram m) n).codRestrict
    (polynomialLaurentCechCardCycles m n)
      (subsetCechCardDifferential_squared (polynomialLaurentCechDiagram m) n)

/-- The produced strictly-negative representative of a genuine cycle is again
a genuine cycle, derived by applying the actual outgoing differential. -/
def polynomialLaurentCechCardCyclesSurvivor (m : ℤ) (n : ℕ) :
    polynomialLaurentCechCardCycles (K := K) (I := I) m n →ₗ[K]
      polynomialLaurentCechCardCycles (K := K) (I := I) m n :=
  ((polynomialLaurentCechCardSurvivor m n).comp
    (polynomialLaurentCechCardCycles m n).subtype).codRestrict
      (polynomialLaurentCechCardCycles m n) (by
        intro c
        have h := congrArg
          (subsetCechCardDifferential (polynomialLaurentCechDiagram m) (n + 1))
          (polynomialLaurentCechCardCycles_identity m n c)
        rw [map_add, subsetCechCardDifferential_squared, c.property, zero_add] at h
        exact h)

/-- The finite actual survivor module faithfully contains the genuine image
of the survivor operator on actual cycles. -/
def polynomialLaurentCechCardCyclesSurvivorRangeEmbedding (m : ℤ) (n : ℕ) :
    (polynomialLaurentCechCardCyclesSurvivor (K := K) (I := I) m n).range →ₗ[K]
      (polynomialLaurentCechSurvivor (K := K) (I := I) m).range where
  toFun c := ⟨c.val.val.val, by
    obtain ⟨d, hd⟩ := c.property
    exact ⟨d.val.val, congrArg (fun z => z.val.val) hd⟩⟩
  map_add' c c' := rfl
  map_smul' a c := rfl

/-- The actual survivor-range embedding is injective on genuine cycles. -/
theorem polynomialLaurentCechCardCyclesSurvivorRangeEmbedding_injective (m : ℤ) (n : ℕ) :
    Function.Injective
      (polynomialLaurentCechCardCyclesSurvivorRangeEmbedding (K := K) (I := I) m n) := by
  intro c c' h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (polynomialLaurentCechSurvivor (K := K) (I := I) m).range =>
    z.val) h

include hK in
/-- The genuine image of the survivor operator on actual cocycles is finite. -/
theorem polynomialLaurentCechCardCyclesSurvivor_range_finite (m : ℤ) (n : ℕ) :
    Module.Finite K
      ((polynomialLaurentCechCardCyclesSurvivor (K := K) (I := I) m n).range) := by
  let := polynomialLaurentCechSurvivor_range_finite (K := K) (I := I) m
  exact Module.Finite.of_injective (R := K)
    (M := (polynomialLaurentCechCardCyclesSurvivor (K := K) (I := I) m n).range)
    (N := (polynomialLaurentCechSurvivor (K := K) (I := I) m).range)
    (polynomialLaurentCechCardCyclesSurvivorRangeEmbedding (K := K) (I := I) m n)
    (polynomialLaurentCechCardCyclesSurvivorRangeEmbedding_injective (K := K) (I := I) m n)

/-- Literal kernel modulo literal incoming image in the actual Laurent subset complex. -/
abbrev polynomialLaurentCechCardHomology (m : ℤ) (n : ℕ) :=
  polynomialLaurentCechCardCycles (K := K) (I := I) m n ⧸
    (polynomialLaurentCechCardToCycles (K := K) (I := I) m n).range

/-- The actual quotient projection restricted to the finite produced cycle representatives. -/
def polynomialLaurentCechRepresentativesToHomology (m : ℤ) (n : ℕ) :
    (polynomialLaurentCechCardCyclesSurvivor (K := K) (I := I) m n).range →ₗ[K]
      polynomialLaurentCechCardHomology (K := K) (I := I) m n :=
  (polynomialLaurentCechCardToCycles m n).range.mkQ.comp
    (polynomialLaurentCechCardCyclesSurvivor m n).range.subtype

/-- Every genuine homology class has a genuine strictly-negative representative,
via the actual Laurent contraction and the actual incoming differential. -/
theorem polynomialLaurentCechRepresentativesToHomology_surjective (m : ℤ) (n : ℕ) :
    Function.Surjective
      (polynomialLaurentCechRepresentativesToHomology (K := K) (I := I) m n) := by
  intro q
  obtain ⟨c, hc⟩ := (polynomialLaurentCechCardToCycles (K := K) (I := I) m n).range.mkQ_surjective q
  refine ⟨⟨polynomialLaurentCechCardCyclesSurvivor m n c, ⟨c, rfl⟩⟩, ?_⟩
  change (polynomialLaurentCechCardToCycles m n).range.mkQ
    (polynomialLaurentCechCardCyclesSurvivor m n c) = q
  rw [← hc]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-polynomialLaurentCechCardContraction m n c.val, ?_⟩
  apply Subtype.ext
  change subsetCechCardDifferential (polynomialLaurentCechDiagram m) n
    (-polynomialLaurentCechCardContraction m n c.val) =
      polynomialLaurentCechCardSurvivor m n c.val - c.val
  rw [map_neg]
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = -subsetCechCardDifferential (polynomialLaurentCechDiagram m) n
        (polynomialLaurentCechCardContraction m n c.val) +
        (subsetCechCardDifferential (polynomialLaurentCechDiagram m) n
          (polynomialLaurentCechCardContraction m n c.val) +
            polynomialLaurentCechCardSurvivor m n c.val) :=
      congrArg (fun z =>
        -subsetCechCardDifferential (polynomialLaurentCechDiagram m) n
          (polynomialLaurentCechCardContraction m n c.val) + z)
        (polynomialLaurentCechCardCycles_identity m n c).symm
    _ = polynomialLaurentCechCardSurvivor m n c.val := by abel

include hK in
/-- Every actual cardinal-degree Laurent Čech kernel/image quotient is finite,
derived from the literal contraction and the finite actual monomial survivors. -/
theorem polynomialLaurentCechCardHomology_finite (m : ℤ) (n : ℕ) :
    Module.Finite K (polynomialLaurentCechCardHomology (K := K) (I := I) m n) := by
  let := polynomialLaurentCechCardCyclesSurvivor_range_finite (K := K) (I := I) m n
  exact Module.Finite.of_surjective
    (polynomialLaurentCechRepresentativesToHomology (K := K) (I := I) m n)
    (polynomialLaurentCechRepresentativesToHomology_surjective (K := K) (I := I) m n)

/-- The actual three consecutive cardinal terms form a native short complex. -/
def polynomialLaurentCechCardShortComplex (m : ℤ) (n : ℕ) :
    ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk
    (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) n)
    (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1))
    (by
      apply LinearMap.ext
      intro c
      exact subsetCechCardDifferential_squared (polynomialLaurentCechDiagram m) n c)

/-- Native homology agrees with the literal kernel/image quotient of the actual
Laurent Čech differential, by the native module homology construction. -/
def polynomialLaurentCechCardHomologyEquiv (m : ℤ) (n : ℕ) :
    (polynomialLaurentCechCardShortComplex (K := K) (I := I) m n).homology ≃ₗ[K]
      polynomialLaurentCechCardHomology (K := K) (I := I) m n :=
  (polynomialLaurentCechCardShortComplex m n).moduleCatHomologyIso.toLinearEquiv

include hK in
/-- Native homology of every actual cardinal-degree Laurent Čech short complex is finite. -/
theorem polynomialLaurentCechCardNativeHomology_finite (m : ℤ) (n : ℕ) :
    Module.Finite K
      ((polynomialLaurentCechCardShortComplex (K := K) (I := I) m n).homology) := by
  let := polynomialLaurentCechCardHomology_finite (K := K) (I := I) m n
  exact Module.Finite.equiv
    (polynomialLaurentCechCardHomologyEquiv (K := K) (I := I) m n).symm

/-- The three actual consecutive terms of the nonaugmented native complex agree
with the actual cardinal short complex in positive degree. -/
theorem polynomialLaurentCechComplex_sc'_eq (m : ℤ) (n : ℕ) :
    (polynomialLaurentCechComplex (K := K) (I := I) m).sc' n (n + 1) (n + 2) =
      polynomialLaurentCechCardShortComplex (K := K) (I := I) m (n + 1) := by
  simp [polynomialLaurentCechComplex, subsetCechComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', polynomialLaurentCechCardShortComplex,
    ShortComplex.moduleCatMk, CochainComplex.of.d, Nat.add_assoc]

/-- The actual native degree-zero short complex has zero incoming map and the
literal cardinal-one outgoing Čech differential. -/
def polynomialLaurentCechZeroShortComplex (m : ℤ) :
    ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk
    (0 : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 1 →ₗ[K]
      subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) 1)
    (subsetCechCardDifferential (polynomialLaurentCechDiagram (K := K) (I := I) m) 1)
    (by simp)

include hK in
/-- Native nonaugmented degree-zero homology is finite because its genuine
cocycle module is finite. -/
theorem polynomialLaurentCechZeroNativeHomology_finite (m : ℤ) :
    Module.Finite K
      ((polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).homology) := by
  let := polynomialLaurentCechZeroCycles_finite (K := K) (I := I) m
  have hker : Module.Finite K
      (polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).g.hom.ker :=
    polynomialLaurentCechZeroCycles_finite (K := K) (I := I) m
  let := hker
  have hquot : Module.Finite K
      (polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).moduleCatLeftHomologyData.H := by
    change Module.Finite K
      ((polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).g.hom.ker ⧸
        (polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).moduleCatToCycles.range)
    infer_instance
  let := hquot
  exact Module.Finite.equiv
    (polynomialLaurentCechZeroShortComplex (K := K) (I := I) m).moduleCatHomologyIso.toLinearEquiv.symm

/-- The actual native degree-zero short complex retains the original
nonaugmented cocycles. -/
theorem polynomialLaurentCechComplex_sc'_zero_eq (m : ℤ) :
    (polynomialLaurentCechComplex (K := K) (I := I) m).sc' 0 0 1 =
      polynomialLaurentCechZeroShortComplex (K := K) (I := I) m := by
  simp [polynomialLaurentCechComplex, subsetCechComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', polynomialLaurentCechZeroShortComplex,
    ShortComplex.moduleCatMk, CochainComplex.of.d]

include hK in
/-- Every actual native cohomology module of the nonaugmented polynomial
projective Laurent Čech complex is finite in every integral homogeneous degree. -/
theorem polynomialLaurentCechComplex_homology_finite (m : ℤ) (p : ℕ) :
    Module.Finite K
      ((polynomialLaurentCechComplex (K := K) (I := I) m).homology p) := by
  cases p with
  | zero =>
    have hfin : Module.Finite K
        ((polynomialLaurentCechComplex (K := K) (I := I) m).sc' 0 0 1).homology := by
      rw [polynomialLaurentCechComplex_sc'_zero_eq]
      exact polynomialLaurentCechZeroNativeHomology_finite (K := K) (I := I) m
    let := hfin
    exact Module.Finite.equiv
      ((polynomialLaurentCechComplex (K := K) (I := I) m).homologyIsoSc' 0 0 1
        CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).toLinearEquiv.symm
  | succ n =>
    have hfin : Module.Finite K
        ((polynomialLaurentCechComplex (K := K) (I := I) m).sc' n (n + 1) (n + 2)).homology := by
      rw [polynomialLaurentCechComplex_sc'_eq]
      exact polynomialLaurentCechCardNativeHomology_finite (K := K) (I := I) m (n + 1)
    let := hfin
    exact Module.Finite.equiv
      ((polynomialLaurentCechComplex (K := K) (I := I) m).homologyIsoSc' n (n + 1) (n + 2)
        (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).toLinearEquiv.symm

omit [LinearOrder I] in
/-- Strictly-negative monomials cannot occur on any proper coordinate
intersection, because an uninverted coordinate must have a nonnegative exponent. -/
theorem polynomialLaurentCechSurvivor_eq_zero_of_ne_univ (m : ℤ)
    (c : subsetCechCube (polynomialLaurentCechDiagram (K := K) (I := I) m))
    (S : Finset I) (hS : S ≠ Finset.univ) :
    polynomialLaurentCechSurvivor m c S = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : I, i ∉ S := by
    by_contra h
    apply hS
    apply Finset.eq_univ_iff_forall.mpr
    simpa only [not_exists, not_not] using h
  apply Subtype.ext
  apply (AddMonoidAlgebra.coeffLinearEquiv K).injective
  apply Finsupp.ext
  intro α
  change (polynomialLaurentCechSurvivor m c S).val.coeff α = 0
  rw [polynomialLaurentCechSurvivor_coeff]
  split_ifs with hindex
  · by_contra hcoeff
    have hallowed := (AddMonoidAlgebra.mem_supported.mp (c S).property)
      (Finsupp.mem_support_iff.mpr hcoeff)
    have hnonneg : 0 ≤ α i := hallowed.2 i hi
    exact (not_lt_of_ge hnonneg)
      ((projectiveLaurentContractionIndex_none_iff α).mp hindex i)
  · rfl

omit [LinearOrder I] in
/-- The actual survivor on a cardinal term vanishes unless this is the genuine
top coordinate intersection. -/
theorem polynomialLaurentCechCardSurvivor_eq_zero (m : ℤ) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card I)
    (c : subsetCechCardPiece (polynomialLaurentCechDiagram (K := K) (I := I) m) (n + 1)) :
    polynomialLaurentCechCardSurvivor m n c = 0 := by
  apply Subtype.ext
  funext S
  by_cases hS : S.card = n + 1
  · exact polynomialLaurentCechSurvivor_eq_zero_of_ne_univ m c.val S (by
      intro h
      subst S
      exact hn (by simpa using hS.symm))
  · change polynomialLaurentCechSurvivorTerm m S (c.val S) = 0
    rw [c.property S hS, map_zero]

/-- Away from the genuine top intersection, every actual Laurent Čech cocycle
is the actual differential of its produced contraction. -/
theorem polynomialLaurentCechCardToCycles_surjective_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card I) :
    Function.Surjective (polynomialLaurentCechCardToCycles (K := K) (I := I) m n) := by
  intro c
  refine ⟨polynomialLaurentCechCardContraction m n c.val, ?_⟩
  apply Subtype.ext
  have h := polynomialLaurentCechCardCycles_identity m n c
  rw [polynomialLaurentCechCardSurvivor_eq_zero m n hn, add_zero] at h
  exact h

/-- The genuine native cardinal Čech short complex is exact away from the top
intersection; the actual contraction produces its exactness witnesses. -/
theorem polynomialLaurentCechCardShortComplex_exact_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card I) :
    (polynomialLaurentCechCardShortComplex (K := K) (I := I) m n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c hc
  obtain ⟨b, hb⟩ := polynomialLaurentCechCardToCycles_surjective_of_ne_top
    (K := K) (I := I) m n hn ⟨c, hc⟩
  exact ⟨b, congrArg Subtype.val hb⟩

/-- In every positive degree except the top coordinate degree, the actual
nonaugmented native Laurent Čech complex is exact. -/
theorem polynomialLaurentCechComplex_exactAt_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 2 ≠ Fintype.card I) :
    (polynomialLaurentCechComplex (K := K) (I := I) m).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).mpr
  rw [polynomialLaurentCechComplex_sc'_eq]
  exact polynomialLaurentCechCardShortComplex_exact_of_ne_top (K := K) (I := I) m (n + 1) hn

/-- All actual positive-degree cohomology modules away from the genuine top
coordinate degree are zero, by the produced native exactness proof. -/
theorem polynomialLaurentCechComplex_homology_isZero_of_ne_top (m : ℤ) (n : ℕ)
    (hn : n + 2 ≠ Fintype.card I) :
    CategoryTheory.Limits.IsZero
      ((polynomialLaurentCechComplex (K := K) (I := I) m).homology (n + 1)) :=
  (polynomialLaurentCechComplex_exactAt_of_ne_top (K := K) (I := I) m n hn).isZero_homology

end FiniteCoordinates

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
