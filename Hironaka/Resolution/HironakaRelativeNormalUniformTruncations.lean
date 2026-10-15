/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalLocalizedAssociatedGraded
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Projective

/-! # ONE original denominator for ALL literal original normal truncation quotients

The genuine original quotient map R/(I+J^(q+1)) → R/(I+J^q) retains
EVERY original whole numerator. Its COMPLETE original kernel is precisely
the SAME literal original normal graded piece. Subtype inclusion and true
quotient surjectivity give the actual original short exact filtration.
Genuine exact localization, actual inclusion injectivity and actual quotient
surjectivity retain this SAME filtration on ONE original base denominator.
The previously internally proved ALL-degree original piece bases feed genuine
projectivity, which internally produces actual sections and true original
successor product equivalences. Actual zero-order original quotient is zero;
its empty basis and the actual product equivalences inductively give ALL
literal original normal truncations finite free at that SAME original germ.
The original consumer exposes ONE nonzero entire original base germ and
ALL actual original quotient orders, with no q-dependent denominator.

No caller exactness, localization, section, basis, free, finite-presentation
or result certificate. Generic private linear algebra receives only actual
original producers inside the induction. Uniform analytic spread to nearby
analytic stalks, higher HS and general G8 remain separate OPEN producers.
-/

set_option autoImplicit false
open Set
namespace Hironaka.HironakaRelativeNormalUniformTruncations
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalLocalizedAssociatedGraded

/-- The SAME literal arbitrary original quotient at the ACTUAL normal truncation order. -/
abbrev originalNormalTruncation (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)

/-- Genuine original normal ideal powers give the actual consecutive original quotient ideal inclusion. -/
theorem originalNormalTruncationIdeal_le (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    I ⊔ normalIdeal d t ^ (q+1) ≤ I ⊔ normalIdeal d t ^ q :=
  sup_le_sup_left (Ideal.pow_le_pow_right (I := normalIdeal d t) (Nat.le_succ q)) I

/-- The ACTUAL original consecutive quotient map with the genuine tangential scalar action. -/
def originalNormalTruncationMap (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalNormalTruncation d t I (q+1) →ₐ[HolGerm (ComplexModel d)] originalNormalTruncation d t I q :=
  letI := tangentAlgebra d t
  Ideal.Quotient.factorₐ (HolGerm (ComplexModel d)) (originalNormalTruncationIdeal_le d t I q)

/-- EVERY actual original numerator is retained literally by the TRUE original truncation map. -/
theorem originalNormalTruncationMap_mk (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : HolGerm (ComplexModel (d+t))) : let := tangentAlgebra d t
    originalNormalTruncationMap d t I q (Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) x) =
      Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) x := rfl

/-- The actual literal original graded-piece inclusion into the SAME actual next original truncation. -/
def originalNormalTruncationPieceInclusion (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalNormalGradedPiece d t I q →ₗ[HolGerm (ComplexModel d)] originalNormalTruncation d t I (q+1) :=
  letI := tangentAlgebra d t
  (originalNormalGradedPiece d t I q).subtype

/-- The COMPLETE whole original kernel dictionary is the SAME actual ORIGINAL normal graded piece. -/
theorem originalNormalTruncationMap_eq_zero_iff (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : originalNormalTruncation d t I (q+1)) : let := tangentAlgebra d t
    originalNormalTruncationMap d t I q x=0 ↔ x ∈ originalNormalGradedPiece d t I q := by
  let := tangentAlgebra d t
  dsimp only
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [originalNormalTruncationMap_mk,Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hz
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hz
    refine Submodule.mem_map.mpr ⟨b,hb,?_⟩
    have ha0 : Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) a=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ha)
    change Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) b = Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) z
    rw [← hab,map_add,ha0,zero_add]
  · intro hx
    obtain ⟨b,hb,he⟩ := Submodule.mem_map.mp hx
    have hh := congrArg (originalNormalTruncationMap d t I q) he
    change originalNormalTruncationMap d t I q (Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) b) =
      Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) z at hh
    rw [originalNormalTruncationMap_mk] at hh
    have hb0 : Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ q) b=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hb)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hh.symm.trans hb0)

/-- The genuine original graded-piece inclusion is injective on WHOLE original classes. -/
theorem originalNormalTruncationPieceInclusion_injective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Injective (originalNormalTruncationPieceInclusion d t I q) :=
  let := tangentAlgebra d t
  Subtype.val_injective

/-- Every ACTUAL original target quotient class has its SAME original numerator in the next truncation. -/
theorem originalNormalTruncationMap_surjective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Surjective (originalNormalTruncationMap d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro x
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d t ^ (q+1)) z,originalNormalTruncationMap_mk d t I q z⟩

/-- The complete TRUE original truncation sequence is exact at the SAME actual whole next quotient. -/
theorem originalNormalTruncation_exact (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Exact (originalNormalTruncationPieceInclusion d t I q) (originalNormalTruncationMap d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  intro x
  have hk := originalNormalTruncationMap_eq_zero_iff d t I q x
  rw [hk]
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨z,hz⟩ => hz ▸ z.property⟩

/-- The SAME literal actual original normal truncation localized at powers of the ONE actual original denominator. -/
abbrev originalLocalizedNormalTruncation (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :=
  letI := tangentAlgebra d t
  LocalizedModule (Submonoid.powers (originalUniformNormalDenominator d t I)) (originalNormalTruncation d t I q)

/-- TRUE actual original truncation map localized at the SAME original base germ, with its actual localized scalar action. -/
def originalLocalizedNormalTruncationMap (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalLocalizedNormalTruncation d t I (q+1) →ₗ[Localization.Away (originalUniformNormalDenominator d t I)]
      originalLocalizedNormalTruncation d t I q :=
  letI := tangentAlgebra d t
  LocalizedModule.map (Submonoid.powers (originalUniformNormalDenominator d t I))
    (originalNormalTruncationMap d t I q).toLinearMap

/-- The TRUE localized inclusion of the SAME literal original graded piece. -/
def originalLocalizedNormalTruncationPieceInclusion (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalLocalizedGradedPiece d t I q →ₗ[Localization.Away (originalUniformNormalDenominator d t I)]
      originalLocalizedNormalTruncation d t I (q+1) :=
  letI := tangentAlgebra d t
  LocalizedModule.map (Submonoid.powers (originalUniformNormalDenominator d t I))
    (originalNormalTruncationPieceInclusion d t I q)

/-- Genuine exactness localization is compatible with the TRUE localized coefficient scalar maps. -/
private theorem actualLocalizedMaps_exact {B : Type*} [CommRing B] (S : Submonoid B)
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module B M₀] [Module B M₁] [Module B M₂] (g : M₀ →ₗ[B] M₁) (h : M₁ →ₗ[B] M₂)
    (ex : Function.Exact g h) : Function.Exact (LocalizedModule.map S g) (LocalizedModule.map S h) :=
  LocalizedModule.map_exact S g h ex

/-- The SAME actual original localized truncation sequence is genuinely exact. -/
theorem originalLocalizedNormalTruncation_exact (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Exact (originalLocalizedNormalTruncationPieceInclusion d t I q)
      (originalLocalizedNormalTruncationMap d t I q) :=
  let := tangentAlgebra d t
  actualLocalizedMaps_exact (Submonoid.powers (originalUniformNormalDenominator d t I))
    (originalNormalTruncationPieceInclusion d t I q) (originalNormalTruncationMap d t I q).toLinearMap
    (originalNormalTruncation_exact d t I q)

/-- The ACTUAL same-denominator localized original graded-piece inclusion is injective. -/
theorem originalLocalizedNormalTruncationPieceInclusion_injective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Injective (originalLocalizedNormalTruncationPieceInclusion d t I q) :=
  let := tangentAlgebra d t
  LocalizedModule.map_injective (Submonoid.powers (originalUniformNormalDenominator d t I))
    (originalNormalTruncationPieceInclusion d t I q) (originalNormalTruncationPieceInclusion_injective d t I q)

/-- The ACTUAL same-denominator localized original truncation map is surjective. -/
theorem originalLocalizedNormalTruncationMap_surjective (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Function.Surjective (originalLocalizedNormalTruncationMap d t I q) :=
  let := tangentAlgebra d t
  LocalizedModule.map_surjective (Submonoid.powers (originalUniformNormalDenominator d t I))
    (originalNormalTruncationMap d t I q).toLinearMap (originalNormalTruncationMap_surjective d t I q)


/-- Genuine projectivity internally produces the section and ACTUAL product decomposition of a true short exact sequence. -/
private def actualShortExactProductEquiv {B : Type*} [CommRing B]
    {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module B L] [Module B M] [Module B N] [Module.Projective B N]
    (g : L →ₗ[B] M) (h : M →ₗ[B] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) : M ≃ₗ[B] L × N := by
  let hex := Module.projective_lifting_property h (LinearMap.id : N →ₗ[B] N) hh
  let s := Classical.choose hex
  have hs := Classical.choose_spec hex
  have hsec : ∀ y, h (s y)=y := fun y => LinearMap.congr_fun hs y
  have hgzero : ∀ z, h (g z)=0 := fun z => (ex (g z)).mpr ⟨z,rfl⟩
  let gk : L →ₗ[B] LinearMap.ker h := g.codRestrict (LinearMap.ker h) hgzero
  have hgb : Function.Bijective gk := by
    constructor
    · intro x y hxy
      exact hg (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨z,hz⟩ := (ex x.val).mp x.property
      exact ⟨z,Subtype.ext hz⟩
  let E := LinearEquiv.ofBijective gk hgb
  let k : M →ₗ[B] LinearMap.ker h :=
    (LinearMap.id-s.comp h).codRestrict (LinearMap.ker h) (fun x => by
      change h (x-s (h x))=0
      rw [map_sub,hsec,sub_self])
  let f : M →ₗ[B] L × N := (E.symm.toLinearMap.comp k).prod h
  let inv : L × N →ₗ[B] M := g.comp (LinearMap.fst B L N) + s.comp (LinearMap.snd B L N)
  have hfi : f.comp inv = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨z,y⟩
    change (E.symm (k (g z+s y)),h (g z+s y))=(z,y)
    apply Prod.ext
    · apply E.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      change (g z+s y)-s (h (g z+s y))=g z
      rw [map_add,hgzero,zero_add,hsec]
      abel
    · change h (g z+s y)=y
      rw [map_add,hgzero,hsec,zero_add]
  have hif : inv.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change g (E.symm (k x))+s (h x)=x
    have hk := congrArg Subtype.val (E.apply_symm_apply (k x))
    change g (E.symm (k x))=x-s (h x) at hk
    rw [hk]
    abel
  exact LinearEquiv.ofLinearMap f inv hfi hif


/-- The ACTUAL zero-order original quotient is zero, because the genuine normal ideal zeroth power is the whole ring. -/
theorem originalNormalTruncation_zero_subsingleton (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) : Subsingleton (originalNormalTruncation d t I 0) := by
  change Subsingleton (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ 0))
  rw [pow_zero,Ideal.one_eq_top,sup_top_eq]
  infer_instance

/-- Internal induction on the TRUE localized original short exact filtration gives ALL-order actual original truncation finite freeness at the SAME denominator. -/
theorem originalLocalizedNormalTruncation_finite_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    let := tangentAlgebra d t
    Module.Free (Localization.Away (originalUniformNormalDenominator d t I)) (originalLocalizedNormalTruncation d t I q) ∧
      Module.Finite (Localization.Away (originalUniformNormalDenominator d t I)) (originalLocalizedNormalTruncation d t I q) := by
  let := tangentAlgebra d t
  dsimp only
  induction q with
  | zero =>
      let := originalNormalTruncation_zero_subsingleton d t I
      let : Subsingleton (originalLocalizedNormalTruncation d t I 0) := inferInstance
      let b0 : Module.Basis PEmpty.{1} (Localization.Away (originalUniformNormalDenominator d t I))
          (originalLocalizedNormalTruncation d t I 0) := Module.Basis.empty _
      exact ⟨Module.Free.of_basis b0,Module.Finite.of_basis b0⟩
  | succ q ih =>
      let := ih.1
      let := ih.2
      let := moduleFree_all_originalLocalizedGradedPiece d t I q
      let := moduleFinite_all_originalLocalizedGradedPiece d t I q
      let E := actualShortExactProductEquiv (originalLocalizedNormalTruncationPieceInclusion d t I q)
        (originalLocalizedNormalTruncationMap d t I q)
        (originalLocalizedNormalTruncationPieceInclusion_injective d t I q)
        (originalLocalizedNormalTruncationMap_surjective d t I q)
        (originalLocalizedNormalTruncation_exact d t I q)
      exact ⟨Module.Free.of_equiv E.symm,Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective⟩


/-- EVERY true localized original truncation numerator retains the LITERAL original quotient image and SAME denominator. -/
theorem originalLocalizedNormalTruncationMap_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : originalNormalTruncation d t I (q+1)) (r : Submonoid.powers (originalUniformNormalDenominator d t I)) :
    let := tangentAlgebra d t
    originalLocalizedNormalTruncationMap d t I q (LocalizedModule.mk x r) =
      LocalizedModule.mk (originalNormalTruncationMap d t I q x) r :=
  let := tangentAlgebra d t
  LocalizedModule.map_mk _ _ _ _

/-- The actual localized original piece inclusion retains the SAME whole original class numerator and denominator. -/
theorem originalLocalizedNormalTruncationPieceInclusion_mk (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ)
    (x : originalNormalGradedPiece d t I q) (r : Submonoid.powers (originalUniformNormalDenominator d t I)) :
    let := tangentAlgebra d t
    originalLocalizedNormalTruncationPieceInclusion d t I q (LocalizedModule.mk x r) =
      LocalizedModule.mk x.val r :=
  let := tangentAlgebra d t
  LocalizedModule.map_mk _ _ _ _

/-- The genuine internally produced section exposes the TRUE consecutive original localized quotient product decomposition at EVERY order. -/
def originalLocalizedNormalTruncationSuccProductEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    originalLocalizedNormalTruncation d t I (q+1) ≃ₗ[Localization.Away (originalUniformNormalDenominator d t I)]
      (originalLocalizedGradedPiece d t I q × originalLocalizedNormalTruncation d t I q) :=
  letI := tangentAlgebra d t
  letI := (originalLocalizedNormalTruncation_finite_free d t I q).1
  actualShortExactProductEquiv (originalLocalizedNormalTruncationPieceInclusion d t I q)
    (originalLocalizedNormalTruncationMap d t I q)
    (originalLocalizedNormalTruncationPieceInclusion_injective d t I q)
    (originalLocalizedNormalTruncationMap_surjective d t I q)
    (originalLocalizedNormalTruncation_exact d t I q)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONE internally produced nonzero whole original tangential germ makes ALL literal original quotient truncations genuinely finite free. -/
theorem exists_nonzero_all_original_normal_truncation_finite_free (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ b : HolGerm (ComplexModel d), b ≠ 0 ∧ ∀ q : ℕ,
      let := tangentAlgebra d t
      Module.Free (Localization.Away b)
        (LocalizedModule (Submonoid.powers b) (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) ∧
      Module.Finite (Localization.Away b)
        (LocalizedModule (Submonoid.powers b) (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q))) :=
  ⟨originalUniformNormalDenominator d t I,originalUniformNormalDenominator_ne_zero d t I,
    fun q => originalLocalizedNormalTruncation_finite_free d t I q⟩


end
end Hironaka.HironakaRelativeNormalUniformTruncations
