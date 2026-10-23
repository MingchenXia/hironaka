/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.CurvesField.DualitySchemeCharts
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.KrullDimension.Zero

/-! The SAME actual original isolated etale marking quotient is the ORIGINAL
coefficient field, internally. Blueprint: `stable-marked-simple-quotient.tex`. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace DeJongAlterations.StableModificationBridge.StableMarkedSimpleQuotient
open StableModification StableModification.Cohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The actual original isolated etale marking quotient has its actual original
K-coefficient map bijective; neither fieldness nor dimension is assumed. -/
theorem bijective_algebraMap_quotient {Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (q : Y ⟶ Spec (.of K)) (I : Y.IdealSheafData) [Etale (I.subschemeι ≫ q)]
    {V : Y.Opens} (hV : IsAffineOpen V) (y : Y) (hyV : y ∈ V) (hyI : y ∈ I.support)
    (hisol : ∀ z : Y, z ∈ I.support → z ∈ V → z = y) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    Function.Bijective (algebraMap K (Γ(Y, V) ⧸ I.ideal ⟨V, hV⟩)) := by
  let := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let U : Y.affineOpens := ⟨V, hV⟩
  let Q := Γ(Y, V) ⧸ I.ideal U
  let j : Spec (.of Q) ⟶ Y := I.glueDataObjι U ≫ U.1.ι
  have hrange : Set.range j = (I.support : Set Y) ∩ V := by
    change Set.range (I.glueDataObjι U ≫ U.1.ι) = _
    rw [I.range_glueDataObjι_ι U]
    ext z
    constructor
    · rintro ⟨hz, hzV⟩
      exact ⟨(I.mem_support_iff_of_mem hzV).mpr hz, hzV⟩
    · rintro ⟨hz, hzV⟩
      exact ⟨(I.mem_support_iff_of_mem hzV).mp hz, hzV⟩
  obtain ⟨z, hz⟩ := hrange.symm ▸ (show y ∈ (I.support : Set Y) ∩ V from ⟨hyI, hyV⟩)
  let : Nontrivial Q := z.nontrivial
  let : Subsingleton (PrimeSpectrum Q) := ⟨fun z₁ z₂ => by
    apply j.isEmbedding.injective
    have h₁ := hrange ▸ Set.mem_range_self (f := j) z₁
    have h₂ := hrange ▸ Set.mem_range_self (f := j) z₂
    exact (hisol _ h₁.1 h₁.2).trans (hisol _ h₂.1 h₂.2).symm⟩
  let : Subsingleton (MaximalSpectrum Q) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  let : IsLocalRing Q := .of_singleton_maximalSpectrum
  have he : Etale (j ≫ q) := by
    change Etale ((I.glueDataObjι U ≫ U.1.ι) ≫ q)
    rw [← I.subschemeCover_map_subschemeι U, Category.assoc]
    infer_instance
  have hcoeff : j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
    change (I.glueDataObjι U ≫ U.1.ι) ≫ q = _
    rw [I.glueDataObjι_ι, Category.assoc,
      CurvesField.DualityScheme.fromSpec_comp_eq q hV, ← Spec.map_comp]
    rfl
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap K Q))) := by rw [← hcoeff]; exact he
  let : Algebra.Etale K Q := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap K Q))).mp inferInstance)
  exact Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing K Q

/-- The ACTUAL original quotient, with its SAME actual original K action, has
finite dimension exactly one, derived from actual etale isolated marking geometry. -/
theorem quotient_finiteDimensional_finrank_one {Y : Scheme.{u}} {K : Type u}
    [Field K] [IsAlgClosed K] (q : Y ⟶ Spec (.of K)) (I : Y.IdealSheafData)
    [Etale (I.subschemeι ≫ q)] {V : Y.Opens} (hV : IsAffineOpen V)
    (y : Y) (hyV : y ∈ V) (hyI : y ∈ I.support)
    (hisol : ∀ z : Y, z ∈ I.support → z ∈ V → z = y) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    FiniteDimensional K (Γ(Y, V) ⧸ I.ideal ⟨V, hV⟩) ∧
      Module.finrank K (Γ(Y, V) ⧸ I.ideal ⟨V, hV⟩) = 1 := by
  let := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let e := (AlgEquiv.ofBijective (Algebra.ofId K (Γ(Y, V) ⧸ I.ideal ⟨V, hV⟩))
    (bijective_algebraMap_quotient q I hV y hyV hyI hisol)).toLinearEquiv
  exact ⟨Module.Finite.equiv e, by rw [← e.finrank_eq, Module.finrank_self]⟩

end DeJongAlterations.StableModificationBridge.StableMarkedSimpleQuotient
