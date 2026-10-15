/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalAnalyticGraphQuotient
import Hironaka.Resolution.HironakaRelativeNormalUniformTruncations
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HironakaRelativeNormalFiniteJetSplitting
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalUniformLocalization HironakaRelativeNormalLocalizedAssociatedGraded
  HironakaRelativeNormalUniformTruncations HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalAnalyticGraphQuotient HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalCoherentSaturation

abbrev ambientNormalJet (d t q : ℕ) := HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q

abbrev originalJetDenominators (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  Submonoid.powers (originalUniformNormalDenominator d t I)

abbrev originalJetBase (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  Localization.Away (originalUniformNormalDenominator d t I)

def actualJetProjection (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    ambientNormalJet d t q →ₐ[HolGerm (ComplexModel d)] originalNormalTruncation d t I q :=
  letI := tangentAlgebra d t
  Ideal.Quotient.factorₐ (HolGerm (ComplexModel d)) (show normalIdeal d t ^ q ≤ I ⊔ normalIdeal d t ^ q from le_sup_right)

theorem actualJetProjection_mk (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) : let := tangentAlgebra d t
    actualJetProjection d t I q (Ideal.Quotient.mk (normalIdeal d t ^ q) g) =
      Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) g := rfl

theorem actualJetProjection_surjective (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Surjective (actualJetProjection d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro x
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (normalIdeal d t ^ q) g,rfl⟩

def actualIdealJetMap (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    (I.restrictScalars (HolGerm (ComplexModel d))) →ₗ[HolGerm (ComplexModel d)] ambientNormalJet d t q :=
  letI := tangentAlgebra d t
  (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.comp
    (I.restrictScalars (HolGerm (ComplexModel d))).subtype

theorem actualIdealJetMap_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (g : I) : let := tangentAlgebra d t
    actualIdealJetMap d t I q g = Ideal.Quotient.mk (normalIdeal d t ^ q) g.val := rfl

theorem actualIdealJetMap_projection_exact (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Exact (actualIdealJetMap d t I q) (actualJetProjection d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro x
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [actualJetProjection_mk,Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hg
    obtain ⟨a,ha,c,hc,he⟩ := Submodule.mem_sup.mp hg
    refine ⟨⟨a,show a ∈ I.restrictScalars (HolGerm (ComplexModel d)) from ha⟩,?_⟩
    change Ideal.Quotient.mk (normalIdeal d t ^ q) a = Ideal.Quotient.mk (normalIdeal d t ^ q) g
    rw [← he,map_add]
    have hc0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hc0,add_zero]
  · rintro ⟨a,ha⟩
    change Ideal.Quotient.mk (normalIdeal d t ^ q) a.val = Ideal.Quotient.mk (normalIdeal d t ^ q) g at ha
    have he := congrArg (actualJetProjection d t I q) ha
    rw [actualJetProjection_mk,actualJetProjection_mk] at he
    have ha0 : Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) a.val = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left a.property)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (he.symm.trans ha0)

abbrev localizedAmbientNormalJet (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  letI := tangentAlgebra d t
  LocalizedModule (originalJetDenominators d t I) (ambientNormalJet d t q)

def actualLocalizedJetProjection (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    localizedAmbientNormalJet d t I q →ₗ[originalJetBase d t I] originalLocalizedNormalTruncation d t I q :=
  letI := tangentAlgebra d t
  LocalizedModule.map (originalJetDenominators d t I) (actualJetProjection d t I q).toLinearMap

def actualLocalizedIdealJetMap (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    LocalizedModule (originalJetDenominators d t I) (I.restrictScalars (HolGerm (ComplexModel d))) →ₗ[originalJetBase d t I]
      localizedAmbientNormalJet d t I q :=
  letI := tangentAlgebra d t
  LocalizedModule.map (originalJetDenominators d t I) (actualIdealJetMap d t I q)

theorem actualLocalizedJetProjection_surjective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Surjective (actualLocalizedJetProjection d t I q) :=
  let := tangentAlgebra d t
  LocalizedModule.map_surjective _ (actualJetProjection d t I q).toLinearMap (actualJetProjection_surjective d t I q)

theorem actualLocalizedIdealJetMap_projection_exact (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Exact (actualLocalizedIdealJetMap d t I q) (actualLocalizedJetProjection d t I q) :=
  let := tangentAlgebra d t
  LocalizedModule.map_exact (originalJetDenominators d t I)
    (actualIdealJetMap d t I q) (actualJetProjection d t I q).toLinearMap
    (actualIdealJetMap_projection_exact d t I q)


/-- Actual localization of the entire original finite normal monomial basis. -/
def actualLocalizedJetBasis (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    Module.Basis (normalExponentIndex t q) (originalJetBase d t I) (localizedAmbientNormalJet d t I q) :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  (normalMonomialBasis d t q).ofIsLocalizedModule (originalJetBase d t I)
    (originalJetDenominators d t I)
    (LocalizedModule.mkLinearMap (originalJetDenominators d t I) (ambientNormalJet d t q))

theorem actualLocalizedJetBasis_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (q : ℕ) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualLocalizedJetBasis d t I q α =
      LocalizedModule.mk (Ideal.Quotient.mk (normalIdeal d t ^ q) (normalExponentMonomial d t α.val)) 1 := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [actualLocalizedJetBasis,Module.Basis.ofIsLocalizedModule_apply,normalMonomialBasis_apply]
  rfl

theorem actualLocalizedAmbientJet_finite_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Free (originalJetBase d t I) (localizedAmbientNormalJet d t I q) ∧
      Module.Finite (originalJetBase d t I) (localizedAmbientNormalJet d t I q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  exact ⟨Module.Free.of_basis (actualLocalizedJetBasis d t I q),
    Module.Finite.of_basis (actualLocalizedJetBasis d t I q)⟩

theorem exists_actualLocalizedJetSection (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    ∃ s : originalLocalizedNormalTruncation d t I q →ₗ[originalJetBase d t I]
      localizedAmbientNormalJet d t I q,
      (actualLocalizedJetProjection d t I q).comp s = LinearMap.id := by
  let := tangentAlgebra d t
  let := (originalLocalizedNormalTruncation_finite_free d t I q).1
  exact Module.projective_lifting_property (actualLocalizedJetProjection d t I q)
    LinearMap.id (actualLocalizedJetProjection_surjective d t I q)

def actualLocalizedJetSection (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalLocalizedNormalTruncation d t I q →ₗ[originalJetBase d t I] localizedAmbientNormalJet d t I q :=
  letI := tangentAlgebra d t
  Classical.choose (exists_actualLocalizedJetSection d t I q)

theorem actualLocalizedJetSection_spec (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    (actualLocalizedJetProjection d t I q).comp (actualLocalizedJetSection d t I q) = LinearMap.id :=
  let := tangentAlgebra d t
  Classical.choose_spec (exists_actualLocalizedJetSection d t I q)

theorem actualLocalizedJetSection_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : originalLocalizedNormalTruncation d t I q) :
    let := tangentAlgebra d t
    actualLocalizedJetProjection d t I q (actualLocalizedJetSection d t I q x) = x :=
  let := tangentAlgebra d t
  LinearMap.congr_fun (actualLocalizedJetSection_spec d t I q) x

def actualJetP (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    localizedAmbientNormalJet d t I q →ₗ[originalJetBase d t I] localizedAmbientNormalJet d t I q :=
  letI := tangentAlgebra d t
  (actualLocalizedJetSection d t I q).comp (actualLocalizedJetProjection d t I q)

def actualJetQ (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    localizedAmbientNormalJet d t I q →ₗ[originalJetBase d t I] localizedAmbientNormalJet d t I q :=
  letI := tangentAlgebra d t
  LinearMap.id - actualJetP d t I q

theorem actualJetP_comp_self (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    (actualJetP d t I q).comp (actualJetP d t I q) = actualJetP d t I q := by
  let := tangentAlgebra d t
  apply LinearMap.ext
  intro x
  change actualLocalizedJetSection d t I q
    (actualLocalizedJetProjection d t I q (actualLocalizedJetSection d t I q (actualLocalizedJetProjection d t I q x))) = _
  rw [actualLocalizedJetSection_apply]
  rfl

theorem actualJetP_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) : let := tangentAlgebra d t
    actualJetP d t I q x = actualLocalizedJetSection d t I q (actualLocalizedJetProjection d t I q x) := rfl

theorem actualJetQ_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) : let := tangentAlgebra d t
    actualJetQ d t I q x = x - actualJetP d t I q x := rfl

theorem actualJetProjection_P (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) : let := tangentAlgebra d t
    actualLocalizedJetProjection d t I q (actualJetP d t I q x) = actualLocalizedJetProjection d t I q x := by
  let := tangentAlgebra d t
  rw [actualJetP_apply,actualLocalizedJetSection_apply]

theorem actualJetProjection_Q (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) : let := tangentAlgebra d t
    actualLocalizedJetProjection d t I q (actualJetQ d t I q x) = 0 := by
  let := tangentAlgebra d t
  rw [actualJetQ_apply,map_sub,actualJetProjection_P,sub_self]

theorem actualJetP_add_Q (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    actualJetP d t I q + actualJetQ d t I q = LinearMap.id := by
  let := tangentAlgebra d t
  apply LinearMap.ext
  intro x
  change actualJetP d t I q x + (x-actualJetP d t I q x) = x
  abel

theorem actualJetQ_comp_self (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    (actualJetQ d t I q).comp (actualJetQ d t I q) = actualJetQ d t I q := by
  let := tangentAlgebra d t
  apply LinearMap.ext
  intro x
  change actualJetQ d t I q (actualJetQ d t I q x) = actualJetQ d t I q x
  rw [actualJetQ_apply,actualJetP_apply,actualJetProjection_Q,LinearMap.map_zero (actualLocalizedJetSection d t I q),sub_zero]

theorem actualJetP_eq_zero_iff (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) : let := tangentAlgebra d t
    actualJetP d t I q x = 0 ↔ actualLocalizedJetProjection d t I q x = 0 := by
  let := tangentAlgebra d t
  constructor
  · intro h
    have he := congrArg (actualLocalizedJetProjection d t I q) h
    rw [actualJetProjection_P,LinearMap.map_zero (actualLocalizedJetProjection d t I q)] at he
    exact he
  · intro h
    rw [actualJetP_apply,h,LinearMap.map_zero (actualLocalizedJetSection d t I q)]

theorem actualJetQ_projection_exact (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Exact (actualJetQ d t I q) (actualLocalizedJetProjection d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro x
  constructor
  · intro hx
    refine ⟨x,?_⟩
    rw [actualJetQ_apply,actualJetP_apply,hx,LinearMap.map_zero (actualLocalizedJetSection d t I q),sub_zero]
  · rintro ⟨y,rfl⟩
    exact actualJetProjection_Q d t I q y

theorem actualJetQ_range_eq_originalIdealImage (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    LinearMap.range (actualJetQ d t I q) = LinearMap.range (actualLocalizedIdealJetMap d t I q) := by
  let := tangentAlgebra d t
  apply Submodule.ext
  intro x
  change (∃ y,actualJetQ d t I q y=x) ↔ ∃ y,actualLocalizedIdealJetMap d t I q y=x
  exact (actualJetQ_projection_exact d t I q x).symm.trans
    (actualLocalizedIdealJetMap_projection_exact d t I q x)

def actualJetPMatrix (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    Matrix (normalExponentIndex t q) (normalExponentIndex t q) (originalJetBase d t I) := by
  classical
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  exact LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q)
    (actualJetP d t I q)

def actualJetQMatrix (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    Matrix (normalExponentIndex t q) (normalExponentIndex t q) (originalJetBase d t I) := by
  classical
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  exact LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q)
    (actualJetQ d t I q)

theorem actualJetPMatrix_mul_self (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetPMatrix d t I q * actualJetPMatrix d t I q = actualJetPMatrix d t I q := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  change LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetP d t I q) *
    LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetP d t I q) = _
  rw [← LinearMap.toMatrix_comp,actualJetP_comp_self]
  rfl

theorem actualJetQMatrix_mul_self (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetQMatrix d t I q * actualJetQMatrix d t I q = actualJetQMatrix d t I q := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  change LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetQ d t I q) *
    LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetQ d t I q) = _
  rw [← LinearMap.toMatrix_comp,actualJetQ_comp_self]
  rfl

theorem actualJetPMatrix_add_QMatrix (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetPMatrix d t I q + actualJetQMatrix d t I q = 1 := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  change LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetP d t I q) +
    LinearMap.toMatrix (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q) (actualJetQ d t I q) = _
  rw [← map_add,actualJetP_add_Q,LinearMap.toMatrix_id]

def actualJetIdealColumn (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α : normalExponentIndex t q) :
    letI := tangentAlgebra d t
    letI := normalExponentFintype t q
    localizedAmbientNormalJet d t I q :=
  letI := tangentAlgebra d t
  letI := normalExponentFintype t q
  actualJetQ d t I q (actualLocalizedJetBasis d t I q α)

theorem actualJetQMatrix_apply (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (α β : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetQMatrix d t I q α β =
      (actualLocalizedJetBasis d t I q).repr (actualJetIdealColumn d t I q β) α := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  exact LinearMap.toMatrix_apply (actualLocalizedJetBasis d t I q) (actualLocalizedJetBasis d t I q)
    (actualJetQ d t I q) α β

theorem actualJetIdealColumn_mem_originalIdealImage (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetIdealColumn d t I q α ∈ LinearMap.range (actualLocalizedIdealJetMap d t I q) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  exact (actualLocalizedIdealJetMap_projection_exact d t I q
    (actualJetIdealColumn d t I q α)).mp
    (actualJetProjection_Q d t I q (actualLocalizedJetBasis d t I q α))

theorem actualJetQ_basis_expansion (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : localizedAmbientNormalJet d t I q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualJetQ d t I q x = ∑ α, (actualLocalizedJetBasis d t I q).repr x α • actualJetIdealColumn d t I q α := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  calc
    actualJetQ d t I q x = actualJetQ d t I q
        (∑ α, (actualLocalizedJetBasis d t I q).repr x α • actualLocalizedJetBasis d t I q α) :=
      congrArg (actualJetQ d t I q) ((actualLocalizedJetBasis d t I q).sum_repr x).symm
    _ = _ := by rw [map_sum]; simp only [map_smul,actualJetIdealColumn]

theorem mem_originalIdealJetImage_iff_actual_columns (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) (y : localizedAmbientNormalJet d t I q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    y ∈ LinearMap.range (actualLocalizedIdealJetMap d t I q) ↔
      ∃ c : normalExponentIndex t q → originalJetBase d t I,
        ∑ α,c α • actualJetIdealColumn d t I q α = y := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  constructor
  · intro hy
    rw [← actualJetQ_range_eq_originalIdealImage] at hy
    obtain ⟨x,hx⟩ := hy
    exact ⟨fun α => (actualLocalizedJetBasis d t I q).repr x α,
      (actualJetQ_basis_expansion d t I q x).symm.trans hx⟩
  · rintro ⟨c,rfl⟩
    exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _
      (actualJetIdealColumn_mem_originalIdealImage d t I q α)

/-- Original coherent input internally selects N/U and the actual finite jet splitting at N+1. -/
theorem exists_original_coherent_finiteJet_split (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
      let := normalExponentFintype t (N+1)
      IsOpen U ∧ 0 ∈ U ∧
      originalUniformNormalDenominator d t (originalCoherentOriginIdeal I) ≠ 0 ∧
      Nonempty ((HolGerm (ComplexModel (deformationDimension d t)) ⧸
        originalCoherentOriginIdeal (originalDeformationIdeal d t I)) ≃+*
        (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t I)) ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) =
        Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t I N) ∧
      (actualLocalizedJetProjection d t (originalCoherentOriginIdeal I) (N+1)).comp
        (actualLocalizedJetSection d t (originalCoherentOriginIdeal I) (N+1)) = LinearMap.id ∧
      actualJetPMatrix d t (originalCoherentOriginIdeal I) (N+1) *
        actualJetPMatrix d t (originalCoherentOriginIdeal I) (N+1) =
          actualJetPMatrix d t (originalCoherentOriginIdeal I) (N+1) ∧
      actualJetQMatrix d t (originalCoherentOriginIdeal I) (N+1) *
        actualJetQMatrix d t (originalCoherentOriginIdeal I) (N+1) =
          actualJetQMatrix d t (originalCoherentOriginIdeal I) (N+1) ∧
      actualJetPMatrix d t (originalCoherentOriginIdeal I) (N+1) +
        actualJetQMatrix d t (originalCoherentOriginIdeal I) (N+1) = 1 ∧
      (∀ y : localizedAmbientNormalJet d t (originalCoherentOriginIdeal I) (N+1),
        y ∈ LinearMap.range (actualLocalizedIdealJetMap d t (originalCoherentOriginIdeal I) (N+1)) ↔
          ∃ c : normalExponentIndex t (N+1) → originalJetBase d t (originalCoherentOriginIdeal I),
            ∑ α,c α • actualJetIdealColumn d t (originalCoherentOriginIdeal I) (N+1) α = y) ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t I N).mem y g) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem y g) ↔
        (originalDeformationColonIdeal d t I N).mem y g := by
  let := tangentAlgebra d t
  dsimp only
  obtain ⟨N,U,hU,h0U,hquot,hcomap,hcentral,hgraph,hgraphsat,hchain,hpow,hsat⟩ :=
    exists_original_graph_quotient_and_saturation d t I hI
  let := normalExponentFintype t (N+1)
  exact ⟨N,U,hU,h0U,originalUniformNormalDenominator_ne_zero d t (originalCoherentOriginIdeal I),
    hquot,hcentral,actualLocalizedJetSection_spec d t (originalCoherentOriginIdeal I) (N+1),
    actualJetPMatrix_mul_self d t (originalCoherentOriginIdeal I) (N+1),
    actualJetQMatrix_mul_self d t (originalCoherentOriginIdeal I) (N+1),
    actualJetPMatrix_add_QMatrix d t (originalCoherentOriginIdeal I) (N+1),
    mem_originalIdealJetImage_iff_actual_columns d t (originalCoherentOriginIdeal I) (N+1),
    hgraph,hchain,hsat⟩

end
end Hironaka.HironakaRelativeNormalFiniteJetSplitting
