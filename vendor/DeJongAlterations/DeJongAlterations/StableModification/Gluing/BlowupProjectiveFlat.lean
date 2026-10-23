/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.Algebra.ReesFlatBaseChange
import DeJongAlterations.Geometry.AffineBlowupFunctor
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat base change of affine blow-ups

Let `R → S` be a flat ring map and `I ⊆ R` an ideal. The blow-up of `IS` in `Spec S` is the base
change of the blow-up of `I` in `Spec R`:
`Bl_{IS}(Spec S) = Bl_I(Spec R) ×_{Spec R} Spec S` (EGA IV 19.4.?; Stacks, Tag 0805). This is
the comparison needed to identify the chart blow-ups of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), proof of Proposition 4.3.1 (T:2976–2983), which are
spread along étale (in particular flat) charts, with the native blow-up of an ideal sheaf
(Codex's `Geometry.BlowupGluing.blowup`), to which SERRE-I applies (`PLAN-T5.md` node A4).

## Main results

* `awayTensor_bijective`: for a homogeneous `a ∈ Rees(I)` the degree-zero localizations satisfy
  `Rees(IS)_{(a)} = S ⊗_R Rees(I)_{(a)}` (flatness is used for injectivity, through the
  injectivity of `S ⊗_R I^n → I^n S`, Codex's `reesBaseChangeMap_injective`);
* `isPushout_away`: the corresponding pushout square of commutative rings;
* `isPullback_affineBlowupMap_of_flat`: **flat base change of affine blow-ups**, the Cartesian
  square `Bl_{IS} → Bl_I`, `Bl_{IS} → Spec S`, `Bl_I → Spec R`, `Spec S → Spec R`, checked on the
  standard affine cover `D₊(a)` of `Proj Rees(I)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial HomogeneousLocalization
open scoped TensorProduct

universe u

namespace DeJongAlterations.StableModification.Gluing.BlowupFlat

open DeJongAlterations DeJongAlterations.Algebra.ReesLocalization
  DeJongAlterations.Algebra.ReesFlatBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- The extended ideal `IS`. -/
local notation "J" => I.map (algebraMap R S)

/-- The graded coefficient map `Rees(I) → Rees(IS)`. -/
local notation "φ" => reesGradedMap I (algebraMap R S)

variable {d : ℕ} {a : reesAlgebra I} (ha : a ∈ reesGrading I d)

/-- The degree-zero localization `Rees(I)_{(a)}` as an `R`-algebra (a type synonym, so that the
`R`-algebra structure through `R ≅ Rees(I)₀` does not clash with other scalar actions). -/
def AwayR (a : reesAlgebra I) : Type u := Away (reesGrading I) a

instance (a : reesAlgebra I) : CommRing (AwayR I a) :=
  inferInstanceAs (CommRing (Away (reesGrading I) a))

/-- The structure map `R ≅ Rees(I)₀ → Rees(I)_{(a)}`. -/
def awayBase (a : reesAlgebra I) : R →+* Away (reesGrading I) a :=
  (fromZeroRingHom (reesGrading I) _).comp (reesDegreeZeroEquiv I).toRingHom

instance (a : reesAlgebra I) : Algebra R (AwayR I a) := (awayBase I a).toAlgebra

/-- The degree-zero localization `Rees(IS)_{(φ a)}` as an `S`-algebra (a type synonym). -/
def AwayS (a : reesAlgebra I) : Type u := Away (reesGrading J) (φ a)

instance (a : reesAlgebra I) : CommRing (AwayS (S := S) I a) :=
  inferInstanceAs (CommRing (Away (reesGrading J) (φ a)))

instance (a : reesAlgebra I) : Algebra S (AwayS (S := S) I a) := (awayBase J (φ a)).toAlgebra

instance (a : reesAlgebra I) : Algebra R (AwayS (S := S) I a) :=
  ((awayBase J (φ a)).comp (algebraMap R S)).toAlgebra

instance (a : reesAlgebra I) : IsScalarTower R S (AwayS (S := S) I a) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The coefficient map on degree-zero localizations. -/
def awayMap (a : reesAlgebra I) : AwayR I a →+* AwayS (S := S) I a :=
  Away.map (reesGradedMap I (algebraMap R S)) a

instance (a : reesAlgebra I) : Algebra (AwayR I a) (AwayS (S := S) I a) := (awayMap I a).toAlgebra

theorem awayMap_awayBase (a : reesAlgebra I) (r : R) :
    awayMap (S := S) I a (awayBase I a r) = awayBase J (φ a) (algebraMap R S r) := by
  change Away.map (reesGradedMap I (algebraMap R S)) a
    (HomogeneousLocalization.mk ⟨0, reesDegreeZeroEquiv I r, 1, one_mem _⟩) =
    HomogeneousLocalization.mk ⟨0, reesDegreeZeroEquiv J (algebraMap R S r), 1, one_mem _⟩
  rw [Away.map, HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  · exact reesMap_algebraMap I (algebraMap R S) r
  · exact Subtype.ext (map_one (reesMap I (algebraMap R S)))

instance (a : reesAlgebra I) : IsScalarTower R (AwayR I a) (AwayS (S := S) I a) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    change awayBase J (φ a) (algebraMap R S r) = awayMap I a (awayBase I a r)
    exact (awayMap_awayBase I a r).symm

/-- The fractions `x / a^m`, `x ∈ Rees(I)_{md}`, as an `R`-linear map. -/
def fracMap (m : ℕ) : reesGrading I (m • d) →ₗ[R] AwayR I a where
  toFun x := Away.mk (reesGrading I) ha m x x.2
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    change (Away.mk (reesGrading I) ha m (x + y : reesGrading I (m • d)) (x + y).2).val =
      (Away.mk (reesGrading I) ha m x x.2 + Away.mk (reesGrading I) ha m y y.2).val
    rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
      Localization.add_mk_self]
    rfl
  map_smul' r x := by
    apply HomogeneousLocalization.val_injective
    change Localization.mk _ _ = (awayBase I a r * Away.mk (reesGrading I) ha m x x.2).val
    rw [HomogeneousLocalization.val_mul]
    change _ = Localization.mk _ 1 * Localization.mk _ _
    rw [Localization.mk_mul, one_mul]
    congr 1
    change r • (x : reesAlgebra I) = _
    rw [Algebra.smul_def]
    rfl

theorem fracMap_apply (m : ℕ) (x : reesGrading I (m • d)) :
    fracMap I ha m x = Away.mk (reesGrading I) ha m x x.2 := rfl

/-- Multiplication by `a^(N-m)`, from degree `md` to degree `Nd`. -/
def shift {m N : ℕ} (hmN : m ≤ N) : reesGrading I (m • d) →ₗ[R] reesGrading I (N • d) where
  toFun x := ⟨a ^ (N - m) * x, by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded (N - m) ha) x.2
    rwa [← add_smul, Nat.sub_add_cancel hmN] at h⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_smul_comm r _ _)

theorem fracMap_shift {m N : ℕ} (hmN : m ≤ N) (x : reesGrading I (m • d)) :
    fracMap I ha N (shift I ha hmN x) = fracMap I ha m x := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (a ^ (N - m) * (x : reesAlgebra I))
      (⟨a ^ N, N, rfl⟩ : Submonoid.powers a) =
    Localization.mk (x : reesAlgebra I) (⟨a ^ m, m, rfl⟩ : Submonoid.powers a)
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmN]

/-- Every tensor `z ∈ S ⊗_R Rees(I)_{(a)}` is `Σ sᵢ ⊗ xᵢ / a^N` for one exponent `N`. -/
theorem exists_eq_baseChange_fracMap (z : S ⊗[R] AwayR I a) :
    ∃ (N : ℕ) (w : S ⊗[R] reesGrading I (N • d)), (fracMap I ha N).baseChange S w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul s y =>
    obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective (reesGrading I) ha y
    exact ⟨n, s ⊗ₜ ⟨x, hx⟩, rfl⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨N₁, w₁, rfl⟩ := h₁
    obtain ⟨N₂, w₂, rfl⟩ := h₂
    refine ⟨N₁ + N₂, (shift I ha (Nat.le_add_right N₁ N₂)).baseChange S w₁ +
      (shift I ha (Nat.le_add_left N₂ N₁)).baseChange S w₂, ?_⟩
    have e₁ : fracMap I ha (N₁ + N₂) ∘ₗ shift I ha (Nat.le_add_right N₁ N₂) = fracMap I ha N₁ :=
      LinearMap.ext (fracMap_shift I ha _)
    have e₂ : fracMap I ha (N₁ + N₂) ∘ₗ shift I ha (Nat.le_add_left N₂ N₁) = fracMap I ha N₂ :=
      LinearMap.ext (fracMap_shift I ha _)
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, e₁, e₂]

/-- The degree-`n` part of `S ⊗_R Rees(I) → Rees(IS)`. -/
def degreeMap (n : ℕ) : S ⊗[R] reesGrading I n →ₗ[S] reesAlgebra J :=
  (reesBaseChangeMap (S := S) I).toLinearMap ∘ₗ ((reesGrading I n).subtype.baseChange S)

theorem degreeMap_tmul (n : ℕ) (s : S) (x : reesGrading I n) :
    degreeMap (S := S) I n (s ⊗ₜ x) = s • reesMap I (algebraMap R S) x := rfl

theorem degreeMap_injective [Module.Flat R S] (n : ℕ) :
    Function.Injective (degreeMap (S := S) I n) := by
  refine (reesBaseChangeMap_injective (S := S) I).comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

theorem degreeMap_shift {m N : ℕ} (hmN : m ≤ N) (w : S ⊗[R] reesGrading I (m • d)) :
    degreeMap (S := S) I (N • d) ((shift I ha hmN).baseChange S w) =
      φ a ^ (N - m) * degreeMap (S := S) I (m • d) w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, mul_zero]
  | tmul s x =>
    change s • reesMap I (algebraMap R S) (a ^ (N - m) * x) =
      reesMap I (algebraMap R S) a ^ (N - m) * (s • reesMap I (algebraMap R S) x)
    rw [map_mul, map_pow, mul_smul_comm]
  | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mul_add]

/-- The comparison map `S ⊗_R Rees(I)_{(a)} → Rees(IS)_{(φ a)}`. -/
def awayTensor (a : reesAlgebra I) : S ⊗[R] AwayR I a →ₐ[S] AwayS (S := S) I a :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (IsScalarTower.toAlgHom R (AwayR I a) (AwayS (S := S) I a)) fun _ _ ↦ Commute.all _ _

theorem awayTensor_tmul (s : S) (y : AwayR I a) :
    awayTensor (S := S) I a (s ⊗ₜ y) = algebraMap S (AwayS (S := S) I a) s * awayMap I a y := rfl

theorem val_awayBase (T : Type u) [CommRing T] (K : Ideal T) (b : reesAlgebra K) (t : T) :
    (awayBase K b t).val = Localization.mk (algebraMap T (reesAlgebra K) t) 1 := rfl

theorem val_awayTensor_baseChange_fracMap (N : ℕ) (w : S ⊗[R] reesGrading I (N • d)) :
    (awayTensor (S := S) I a ((fracMap I ha N).baseChange S w)).val =
      Localization.mk (degreeMap (S := S) I (N • d) w)
        (⟨φ a ^ N, N, rfl⟩ : Submonoid.powers (φ a)) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, HomogeneousLocalization.val_zero,
      Localization.mk_zero]
  | tmul s x =>
    rw [LinearMap.baseChange_tmul, awayTensor_tmul, fracMap_apply]
    change (awayBase J (φ a) s * Away.map (reesGradedMap I (algebraMap R S)) a
      (Away.mk (reesGrading I) ha N x x.2)).val = _
    rw [Away.map_mk, HomogeneousLocalization.val_mul, val_awayBase, Away.val_mk,
      Localization.mk_mul]
    congr 1
    · exact (Algebra.smul_def s _).symm
    · exact Subtype.ext (one_mul _)
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, HomogeneousLocalization.val_add, h₁, h₂, map_add,
      Localization.add_mk_self]

include ha in
theorem awayTensor_injective [Module.Flat R S] :
    Function.Injective (awayTensor (S := S) I a) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨N, w, rfl⟩ := exists_eq_baseChange_fracMap (S := S) I ha z
  have h := congrArg HomogeneousLocalization.val hz
  rw [val_awayTensor_baseChange_fracMap, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := h
  have hw : (shift I ha (Nat.le_add_right N k)).baseChange S w = 0 := by
    apply degreeMap_injective (S := S) I
    rw [degreeMap_shift, Nat.add_sub_cancel_left, map_zero]
    exact hk
  have e : fracMap I ha (N + k) ∘ₗ shift I ha (Nat.le_add_right N k) = fracMap I ha N :=
    LinearMap.ext (fracMap_shift I ha _)
  rw [← e, LinearMap.baseChange_comp, LinearMap.comp_apply, hw, map_zero]

theorem awayMk_mem_range_awayTensor {n : ℕ} {c : S} (hc : c ∈ J ^ (n • d))
    (z : reesAlgebra J) (hz : z ∈ reesGrading J (n • d))
    (hzc : (z : S[X]) = monomial (n • d) c) :
    Away.mk (reesGrading J) ((reesGradedMap I (algebraMap R S)).map_mem ha) n z hz ∈
      (awayTensor (S := S) I a).range := by
  have key : J ^ (n • d) = Submodule.span S (algebraMap R S '' (I ^ (n • d) : Ideal R)) := by
    rw [← Ideal.map_pow]
    rfl
  have hc' : c ∈ Submodule.span S (algebraMap R S '' (I ^ (n • d) : Ideal R)) := key ▸ hc
  induction hc' using Submodule.span_induction generalizing z with
  | mem c hcmem =>
    obtain ⟨r, hr, rfl⟩ := hcmem
    let x : reesAlgebra I := ⟨monomial (n • d) r, reesAlgebra.monomial_mem.mpr hr⟩
    have hx : x ∈ reesGrading I (n • d) := ⟨r, rfl⟩
    obtain rfl : z = reesGradedMap I (algebraMap R S) x := by
      apply Subtype.ext
      rw [hzc]
      exact (Polynomial.map_monomial _).symm
    refine ⟨1 ⊗ₜ (Away.mk (reesGrading I) ha n x hx : AwayR I a), ?_⟩
    change awayTensor (S := S) I a (1 ⊗ₜ (Away.mk (reesGrading I) ha n x hx : AwayR I a)) = _
    rw [awayTensor_tmul, map_one, one_mul]
    exact Away.map_mk _ _ ha n x hx
  | zero =>
    obtain rfl : z = 0 := Subtype.ext (by rw [hzc, map_zero]; rfl)
    convert (awayTensor (S := S) I a).range.zero_mem
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]
  | add c₁ c₂ h₁ h₂ ih₁ ih₂ =>
    have m₁ : c₁ ∈ J ^ (n • d) := key ▸ h₁
    have m₂ : c₂ ∈ J ^ (n • d) := key ▸ h₂
    let z₁ : reesAlgebra J := ⟨monomial (n • d) c₁, reesAlgebra.monomial_mem.mpr m₁⟩
    let z₂ : reesAlgebra J := ⟨monomial (n • d) c₂, reesAlgebra.monomial_mem.mpr m₂⟩
    have hz₁ : z₁ ∈ reesGrading J (n • d) := ⟨c₁, rfl⟩
    have hz₂ : z₂ ∈ reesGrading J (n • d) := ⟨c₂, rfl⟩
    obtain rfl : z = z₁ + z₂ := Subtype.ext (by rw [hzc, map_add]; rfl)
    convert (awayTensor (S := S) I a).range.add_mem (ih₁ m₁ z₁ hz₁ rfl) (ih₂ m₂ z₂ hz₂ rfl)
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
      Localization.add_mk_self]
  | smul t c h ih =>
    have m : c ∈ J ^ (n • d) := key ▸ h
    let z₁ : reesAlgebra J := ⟨monomial (n • d) c, reesAlgebra.monomial_mem.mpr m⟩
    have hz₁ : z₁ ∈ reesGrading J (n • d) := ⟨c, rfl⟩
    obtain rfl : z = algebraMap S (reesAlgebra J) t * z₁ := Subtype.ext (by
      rw [hzc]
      change monomial (n • d) (t * c) = C t * monomial (n • d) c
      rw [Polynomial.C_mul_monomial])
    convert (awayTensor (S := S) I a).range.mul_mem
      ((awayTensor (S := S) I a).range.algebraMap_mem t) (ih m z₁ hz₁ rfl)
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk]
    change _ = Localization.mk _ 1 * _
    rw [Localization.mk_mul, one_mul]
    rfl

include ha in
theorem awayTensor_surjective : Function.Surjective (awayTensor (S := S) I a) := by
  intro y
  obtain ⟨n, z, hz, rfl⟩ := Away.mk_surjective (reesGrading J)
    ((reesGradedMap I (algebraMap R S)).map_mem ha) y
  have hzc := (mem_reesGrading_iff J _ z).mp hz
  exact awayMk_mem_range_awayTensor I ha (z.2 (n • d)) z hz hzc

include ha in
/-- **Degree-zero localizations of Rees algebras commute with flat base change**:
`S ⊗_R Rees(I)_{(a)} ≅ Rees(IS)_{(a)}`. -/
theorem awayTensor_bijective [Module.Flat R S] : Function.Bijective (awayTensor (S := S) I a) :=
  ⟨awayTensor_injective I ha, awayTensor_surjective I ha⟩

include ha in
theorem isPushout_awayR [Module.Flat R S] :
    Algebra.IsPushout R S (AwayR I a) (AwayS (S := S) I a) := by
  refine ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (awayTensor (S := S) I a).toLinearMap
    (awayTensor_bijective I ha)) fun x ↦ ?_⟩
  change awayTensor (S := S) I a (1 ⊗ₜ x) = _
  rw [awayTensor_tmul, map_one, one_mul]
  rfl

end Algebra


section Geometry

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] (I : Ideal R)

/-- The chart `D₊(a)` of `Bl_I`, composed with the structure map, is `Spec` of
`R → Rees(I)_{(a)}`. -/
theorem awayι_affineBlowupStructure {T : Type u} [CommRing T] (K : Ideal T) {d : ℕ}
    (hd : 0 < d) {b : reesAlgebra K} (hb : b ∈ reesGrading K d) :
    Proj.awayι (reesGrading K) b hb hd ≫ affineBlowupStructure K =
      Spec.map (CommRingCat.ofHom (awayBase K b)) := by
  rw [affineBlowupStructure, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- **Flat base change of affine blow-ups**: for a flat `R → S`, the square
`Bl_{IS} → Bl_I`, `Bl_{IS} → Spec S`, `Bl_I → Spec R`, `Spec S → Spec R` is Cartesian. -/
theorem isPullback_affineBlowupMap_of_flat :
    IsPullback (affineBlowupMap I (algebraMap R S))
      (affineBlowupStructure (I.map (algebraMap R S))) (affineBlowupStructure I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover (reesGrading I)).openCover
  rintro ⟨⟨d, hd⟩, ⟨a, ha⟩⟩
  let φ := reesGradedMap I (algebraMap R S)
  have hf := reesGradedMap_irrelevant_le_map I (algebraMap R S)
  -- the chart of `Bl_{IS}` over the chart `D₊(a)` of `Bl_I`
  have sq1 : IsPullback (Spec.map (CommRingCat.ofHom (awayMap (S := S) I a)))
      (Proj.awayι (reesGrading (I.map (algebraMap R S))) (φ a) (φ.map_mem ha) hd)
      (Proj.awayι (reesGrading I) a ha hd) (affineBlowupMap I (algebraMap R S)) := by
    apply IsOpenImmersion.isPullback
    · exact Proj.awayι_comp_map φ hf hd a ha
    · rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
      exact Proj.map_preimage_basicOpen φ hf a
  -- the affine square
  have : Algebra.IsPushout R S (AwayR I a) (AwayS (S := S) I a) := isPushout_awayR I ha
  have sq2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (AwayR I a) (AwayS (S := S) I a))).flip
  change IsPullback (pullback.snd (affineBlowupMap I (algebraMap R S))
      (Proj.awayι (reesGrading I) a ha hd))
    (pullback.fst (affineBlowupMap I (algebraMap R S)) (Proj.awayι (reesGrading I) a ha hd) ≫
      affineBlowupStructure (I.map (algebraMap R S)))
    (Proj.awayι (reesGrading I) a ha hd ≫ affineBlowupStructure I)
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  refine sq2.of_iso sq1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
    rfl
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      awayι_affineBlowupStructure]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [awayι_affineBlowupStructure]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end Geometry

end DeJongAlterations.StableModification.Gluing.BlowupFlat
