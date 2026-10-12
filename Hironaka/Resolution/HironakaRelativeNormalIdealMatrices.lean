/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Actual entire relative normal ideal matrices and genuine fixed-degree localizations

The internally proved distinct normal monomial basis constructs true FULL
whole base-germ coordinates, complete normal-power kernels and genuine finite
original ideal matrices. Actual Noetherian holomorphic generators produce
entire original ideal images, and the literal original quotient is the actual
finite matrix cokernel. Genuine holomorphic matrix representatives exist on
one actual base neighbourhood for each degree.

Finite presentation and an internally constructed genuine fraction-field
basis produce a real nonzero fixed-degree denominator, actual localized whole
quotient freeness and its actual generic rank. No caller matrix/kernel/rank/
basis/freeness/flatness certificate is supplied. No common denominator or
analytic normal-flat patch for all degrees is asserted. All-degree graded
Noetherian generic freeness, higher HS descent and general G8 remain OPEN.
Blueprint: `hironaka-relative-normal-ideal-matrices-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalIdealMatrices
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaSmoothCentreRelativeIdeal HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis
open Hironaka
attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass
noncomputable section

/-- Genuine entire base coordinates in the internally proved original finite normal-monomial basis. -/
def normalMonomialCoordinates (d t q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      (normalExponentIndex t q → HolGerm (ComplexModel d)) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  (normalPowerLinearEquiv d t q).symm.toLinearMap.comp
    (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap

/-- The actual coordinate map is surjective onto the FULL true entire base coefficient module. -/
theorem normalMonomialCoordinates_surjective (d t q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    Function.Surjective (normalMonomialCoordinates d t q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  exact (normalPowerLinearEquiv d t q).symm.surjective.comp Ideal.Quotient.mk_surjective

/-- Complete equality of actual entire coordinates is exactly WHOLE original normal-power remainder membership. -/
theorem normalMonomialCoordinates_eq_iff (d t q : ℕ)
    (g h : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCoordinates d t q g = normalMonomialCoordinates d t q h ↔
      g-h ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [normalMonomialCoordinates, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (normalPowerLinearEquiv d t q).symm.injective.eq_iff.trans Ideal.Quotient.eq

/-- The actual entire coordinate kernel is the COMPLETE original normal ideal power. -/
theorem ker_normalMonomialCoordinates (d t q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    LinearMap.ker (normalMonomialCoordinates d t q) =
      (normalIdeal d t ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  ext g
  rw [LinearMap.mem_ker, ← map_zero (normalMonomialCoordinates d t q)]
  change normalMonomialCoordinates d t q g = normalMonomialCoordinates d t q 0 ↔ g ∈ normalIdeal d t ^ q
  simpa only [sub_zero] using normalMonomialCoordinates_eq_iff d t q g 0

/-- True whole normal-power membership gives the zero ENTIRE actual coefficient tuple. -/
theorem normalMonomialCoordinates_eq_zero_of_mem (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCoordinates d t q g = 0 := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  change g ∈ LinearMap.ker (normalMonomialCoordinates d t q)
  rw [ker_normalMonomialCoordinates]
  exact hg

/-- The genuine entire relative monomial representative has true original base coefficients. -/
theorem exists_normalMonomial_coefficient_representative (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    ∃ a : normalExponentIndex t q → HolGerm (ComplexModel d),
      let := normalExponentFintype t q
      g-∑ α, tangentPullback d t (a α)*normalExponentMonomial d t α.val ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  obtain ⟨a, ha⟩ := normalMonomialCombination_surjective d t q (Ideal.Quotient.mk (normalIdeal d t ^ q) g)
  rw [normalMonomialCombination_apply] at ha
  refine ⟨a, ?_⟩
  have hm := Ideal.Quotient.eq.mp ha.symm
  simpa only [map_sum, normalPolynomialEval_monomial] using hm

/-- Whole original tangential multiplication gives genuine ENTIRE base-linear coordinates. -/
theorem normalMonomialCoordinates_tangent_mul (d t q : ℕ)
    (a : HolGerm (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCoordinates d t q (tangentPullback d t a*g) = a • normalMonomialCoordinates d t q g := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  have he : tangentPullback d t a*g = a • g := by rw [Algebra.smul_def]; rfl
  rw [he, map_smul]

/-- The ORIGINAL actual monomial coordinates are precisely the true standard basis vectors. -/
theorem normalMonomialCoordinates_monomial (d t q : ℕ) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCoordinates d t q (normalExponentMonomial d t α.val) = Pi.single α 1 := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  change (normalPowerLinearEquiv d t q).symm
    (Ideal.Quotient.mk (normalIdeal d t ^ q) (normalExponentMonomial d t α.val)) = _
  rw [← normalMonomialBasis_apply, normalMonomialBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  exact (normalPowerLinearEquiv d t q).symm_apply_apply _

/-- Actual original multiplier coordinates lie in the genuine finite monomial-generator column span. -/
theorem normalMonomialCoordinates_mul_mem_columns (d t q : ℕ)
    (a h : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    normalMonomialCoordinates d t q (a*h) ∈ Submodule.span (HolGerm (ComplexModel d))
      (range fun α : normalExponentIndex t q =>
        normalMonomialCoordinates d t q (normalExponentMonomial d t α.val*h)) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  let T := normalMonomialCoordinates d t q
  obtain ⟨b, hrem⟩ := exists_normalMonomial_coefficient_representative d t q a
  let P := ∑ α : normalExponentIndex t q, tangentPullback d t (b α)*normalExponentMonomial d t α.val
  have hz : T ((a-P)*h) = 0 := normalMonomialCoordinates_eq_zero_of_mem d t q _
    (Ideal.mul_mem_right h _ hrem)
  have he : T (a*h) = T (P*h) := by
    rw [sub_mul, map_sub, sub_eq_zero] at hz
    exact hz
  rw [he]
  dsimp only [P]
  rw [Finset.sum_mul, map_sum]
  apply Submodule.sum_mem
  intro α _
  rw [mul_assoc, normalMonomialCoordinates_tangent_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α,rfl⟩)

/-- The WHOLE original ideal image is precisely the finite actual DISTINCT monomial-generator column span. -/
theorem map_span_ideal_normalMonomialCoordinates_eq_columns (d t q : ℕ)
    {ι : Type*} [Fintype ι] (G : ι → HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    ((Ideal.span (range G)).restrictScalars (HolGerm (ComplexModel d))).map
      (normalMonomialCoordinates d t q) = Submodule.span (HolGerm (ComplexModel d))
      (range fun b : normalExponentIndex t q × ι =>
        normalMonomialCoordinates d t q (normalExponentMonomial d t b.1.val*G b.2)) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  let T := normalMonomialCoordinates d t q
  let C := Submodule.span (HolGerm (ComplexModel d))
    (range fun b : normalExponentIndex t q × ι => T (normalExponentMonomial d t b.1.val*G b.2))
  apply le_antisymm
  · rintro v ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    rw [← ha, map_sum]
    apply Submodule.sum_mem
    intro i _
    have hle : Submodule.span (HolGerm (ComplexModel d))
        (range fun α : normalExponentIndex t q => T (normalExponentMonomial d t α.val*G i)) ≤ C := by
      apply Submodule.span_le.mpr
      rintro v ⟨α, rfl⟩
      exact Submodule.subset_span ⟨(α,i),rfl⟩
    exact hle (normalMonomialCoordinates_mul_mem_columns d t q (a i) (G i))
  · apply Submodule.span_le.mpr
    rintro v ⟨b, rfl⟩
    exact Submodule.mem_map.mpr ⟨normalExponentMonomial d t b.1.val*G b.2,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := b.2)),rfl⟩

/-- The genuine finite matrix uses ENTIRE base coordinates of ORIGINAL monomial-generator products. -/
def relativeNormalIdealMatrix (d t q : ℕ) {ι : Type*}
    (G : ι → HolGerm (ComplexModel (d+t))) :
    Matrix (normalExponentIndex t q) (normalExponentIndex t q × ι) (HolGerm (ComplexModel d)) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  fun α b => normalMonomialCoordinates d t q (normalExponentMonomial d t b.1.val*G b.2) α

/-- Literal multiplication by the actual original matrix is precisely its true entire column combination. -/
theorem relativeNormalIdealMatrix_mulVecLin_eq (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    Matrix.mulVecLin (relativeNormalIdealMatrix d t q G) =
      Fintype.linearCombination (HolGerm (ComplexModel d))
        (fun b : normalExponentIndex t q × ι =>
          normalMonomialCoordinates d t q (normalExponentMonomial d t b.1.val*G b.2)) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  apply LinearMap.ext
  intro a
  funext α
  change (∑ b, relativeNormalIdealMatrix d t q G α b*a b) =
    (∑ b, a b • normalMonomialCoordinates d t q (normalExponentMonomial d t b.1.val*G b.2)) α
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- The real matrix range is EXACTLY the WHOLE coordinate image of the original generated ideal. -/
theorem range_relativeNormalIdealMatrix (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    LinearMap.range (Matrix.mulVecLin (relativeNormalIdealMatrix d t q G)) =
      ((Ideal.span (range G)).restrictScalars (HolGerm (ComplexModel d))).map
        (normalMonomialCoordinates d t q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [relativeNormalIdealMatrix_mulVecLin_eq, Fintype.range_linearCombination]
  exact (map_span_ideal_normalMonomialCoordinates_eq_columns d t q G).symm

/-- Arbitrary ORIGINAL whole ideals internally select true finite holomorphic generators and ALL actual relative ideal matrices. -/
theorem exists_original_generators_relativeNormalIdealMatrix (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    ∃ (r : ℕ) (G : Fin r → ComplexModel (d+t) → ℂ)
      (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ (G i) z),
      Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I ∧
      ∀ q : ℕ, let := normalExponentFintype t q
        LinearMap.range (Matrix.mulVecLin (relativeNormalIdealMatrix d t q
          (fun i => HolGerm.mk (G i) (hG i)))) =
            (I.restrictScalars (HolGerm (ComplexModel d))).map (normalMonomialCoordinates d t q) := by
  let := tangentAlgebra d t
  obtain ⟨r,G,hG,hspan,_⟩ := exists_original_generators_normalTaylor_columns d t I
  refine ⟨r,G,hG,hspan,?_⟩
  intro q
  let := normalExponentFintype t q
  dsimp only
  simpa only [hspan] using range_relativeNormalIdealMatrix d t q (fun i => HolGerm.mk (G i) (hG i))

/-- Every genuine actual whole matrix entry has internally chosen ORIGINAL holomorphic representatives on one common base neighbourhood. -/
theorem exists_holomorphic_relativeNormalIdealMatrix (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (d+t))) :
    let := normalExponentFintype t q
    ∃ (F : normalExponentIndex t q → (normalExponentIndex t q × ι) → ComplexModel d → ℂ)
      (hF : ∀ α b, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (F α b) z),
      (∀ α b, relativeNormalIdealMatrix d t q G α b = HolGerm.mk (F α b) (hF α b)) ∧
      ∃ U : Set (ComplexModel d), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
        ∀ z ∈ U, ∀ α b, DifferentiableAt ℂ (F α b) z := by
  let := normalExponentFintype t q
  choose F hF hrep using fun α b => HolGerm.exists_eq_mk (relativeNormalIdealMatrix d t q G α b)
  refine ⟨F,hF,hrep,?_⟩
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel d), ∀ α b, DifferentiableAt ℂ (F α b) z :=
    eventually_all.mpr (fun α => eventually_all.mpr (hF α))
  obtain ⟨U,hU,hopen,h0⟩ := eventually_nhds_iff.mp hall
  exact ⟨U,hopen,h0,hU⟩

/-- Genuine entire coordinates followed by quotient by the WHOLE original ideal image. -/
def relativeIdealMonomialCoordinateQuotientMap (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      ((normalExponentIndex t q → HolGerm (ComplexModel d)) ⧸
        (I.restrictScalars (HolGerm (ComplexModel d))).map (normalMonomialCoordinates d t q)) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  ((I.restrictScalars (HolGerm (ComplexModel d))).map (normalMonomialCoordinates d t q)).mkQ.comp
    (normalMonomialCoordinates d t q)

/-- The ACTUAL original coordinate cokernel has complete WHOLE original kernel I+J^q. -/
theorem ker_relativeIdealMonomialCoordinateQuotientMap (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    LinearMap.ker (relativeIdealMonomialCoordinateQuotientMap d t q I) =
      (I ⊔ normalIdeal d t ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  let T := normalMonomialCoordinates d t q
  let W := (I.restrictScalars (HolGerm (ComplexModel d))).map T
  ext g
  rw [LinearMap.mem_ker]
  change W.mkQ (T g) = 0 ↔ g ∈ I ⊔ normalIdeal d t ^ q
  change T g ∈ LinearMap.ker W.mkQ ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · intro hg
    obtain ⟨a,ha,he⟩ := Submodule.mem_map.mp hg
    have hrem : g-a ∈ normalIdeal d t ^ q := (normalMonomialCoordinates_eq_iff d t q g a).mp he.symm
    have ha' : a ∈ I ⊔ normalIdeal d t ^ q := (show I ≤ I ⊔ normalIdeal d t ^ q from le_sup_left) ha
    have hr' : g-a ∈ I ⊔ normalIdeal d t ^ q :=
      (show normalIdeal d t ^ q ≤ I ⊔ normalIdeal d t ^ q from le_sup_right) hrem
    simpa only [add_sub_cancel] using Ideal.add_mem _ ha' hr'
  · intro hg
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hg
    have hz : T b = 0 := normalMonomialCoordinates_eq_zero_of_mem d t q b hb
    apply Submodule.mem_map.mpr
    refine ⟨a,ha,?_⟩
    rw [← he,map_add,hz,add_zero]

/-- Literal ENTIRE original ideal quotient is genuinely the FULL true monomial-coordinate cokernel. -/
def relativeIdealMonomialCoordinateQuotientEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) ≃ₗ[HolGerm (ComplexModel d)]
      ((normalExponentIndex t q → HolGerm (ComplexModel d)) ⧸
        (I.restrictScalars (HolGerm (ComplexModel d))).map (normalMonomialCoordinates d t q)) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  let F := relativeIdealMonomialCoordinateQuotientMap d t q I
  (Submodule.quotEquivOfEq _ _ (ker_relativeIdealMonomialCoordinateQuotientMap d t q I).symm).trans
    (F.quotKerEquivOfSurjective (Submodule.mkQ_surjective _ |>.comp
      (normalMonomialCoordinates_surjective d t q)))

/-- The genuine ORIGINAL entire generated-ideal quotient is the literal cokernel of its ACTUAL finite relative matrix. -/
def relativeNormalIdealMatrixCokernelEquiv (d t q : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (d+t))) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    (HolGerm (ComplexModel (d+t)) ⧸ (Ideal.span (range G) ⊔ normalIdeal d t ^ q)) ≃ₗ[HolGerm (ComplexModel d)]
      ((normalExponentIndex t q → HolGerm (ComplexModel d)) ⧸
        LinearMap.range (Matrix.mulVecLin (relativeNormalIdealMatrix d t q G))) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  (relativeIdealMonomialCoordinateQuotientEquiv d t q (Ideal.span (range G))).trans
    (Submodule.quotEquivOfEq _ _ (range_relativeNormalIdealMatrix d t q G).symm)

/-- Every ORIGINAL arbitrary ideal internally provides finite holomorphic generators and its real whole quotient/ACTUAL matrix cokernel dictionary at ALL degrees. -/
theorem exists_original_relativeNormalIdealMatrixCokernel (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    ∃ (r : ℕ) (G : Fin r → ComplexModel (d+t) → ℂ)
      (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ (G i) z),
      Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I ∧
      ∀ q : ℕ, let := normalExponentFintype t q
        Nonempty ((HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) ≃ₗ[HolGerm (ComplexModel d)]
          ((normalExponentIndex t q → HolGerm (ComplexModel d)) ⧸
            LinearMap.range (Matrix.mulVecLin (relativeNormalIdealMatrix d t q
              (fun i => HolGerm.mk (G i) (hG i)))))) := by
  let := tangentAlgebra d t
  obtain ⟨r,G,hG,hspan,_⟩ := exists_original_generators_relativeNormalIdealMatrix d t I
  refine ⟨r,G,hG,hspan,?_⟩
  intro q
  let := normalExponentFintype t q
  dsimp only
  rw [← hspan]
  exact ⟨relativeNormalIdealMatrixCokernelEquiv d t q (fun i => HolGerm.mk (G i) (hG i))⟩

/-- The ORIGINAL whole quotient has an internally produced genuine nonzero fixed-degree free base localization, with actual generic rank. -/
theorem exists_nonzero_free_localization_original_quotient (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    ∃ b : HolGerm (ComplexModel d), b ≠ 0 ∧
      Module.Free (Localization.Away b)
        (LocalizedModule.Away b (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) ∧
      Module.finrank (Localization.Away b)
        (LocalizedModule.Away b (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) =
          Module.finrank (FractionRing (HolGerm (ComplexModel d)))
            (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
              (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) := by
  let := tangentAlgebra d t
  let := isNoetherianRing_holGerm_euclidean d
  let := finite_quotient_sup_normalIdeal_pow d t q I
  let B := HolGerm (ComplexModel d)
  let M := HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)
  let := Module.finitePresentation_of_finite B M
  let : Field (FractionRing B) := FractionRing.field B
  let : Module.Free (FractionRing B) (LocalizedModule (nonZeroDivisors B) M) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (FractionRing B) (LocalizedModule (nonZeroDivisors B) M))
  obtain ⟨b,hb,hfree,hrank⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors B) (LocalizedModule.mkLinearMap (nonZeroDivisors B) M) (FractionRing B)
  exact ⟨b,nonZeroDivisors.ne_zero hb,hfree,hrank⟩

end
end Hironaka.HironakaRelativeNormalIdealMatrices
