import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Ring

/-!
# Coefficient localization on actual homogeneous affine charts

If a graded ring map is ordinary localization at a degree-zero element, its
actual homogeneous chart map is ordinary localization at the same constant.
-/

open Graded HomogeneousLocalization

noncomputable section

namespace DeJongAlterations.Algebra.HomogeneousCoefficientLocalization

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B σ τ : Type u}
  [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The numerator of a homogeneous target element can be chosen in the same degree. -/
theorem exists_homogeneous_numerator (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
    [Algebra A B] [IsLocalization.Away (s : A) B]
    (hf : f.toRingHom = algebraMap A B) {d : ℕ} {c : B} (hc : c ∈ ℬ d) :
    ∃ (n : ℕ) (a : A), a ∈ 𝒜 d ∧ c * f (s : A) ^ n = f a := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (s : A) c
  have hfs : f (s : A) ∈ ℬ 0 := map_mem f s.property
  have hpow : f (s : A) ^ n ∈ ℬ 0 := by
    simpa using SetLike.pow_mem_graded n hfs
  have hca : c * f (s : A) ^ n = f a := by
    change c * f.toRingHom (s : A) ^ n = f.toRingHom a
    rw [hf]
    exact ha
  refine ⟨n, DirectSum.decompose 𝒜 a d, (DirectSum.decompose 𝒜 a d).property, ?_⟩
  rw [f.map_directSumDecompose, ← hca]
  exact (DirectSum.decompose_of_mem_same ℬ
    (show c * f (s : A) ^ n ∈ ℬ d by
      simpa using SetLike.mul_mem_graded hc hpow)).symm

/-- The canonical chart algebra structure is the native homogeneous localization map. -/
abbrev chartAlgebra (f : 𝒜 →+*ᵍ ℬ) (a : A) :
    Algebra (Away 𝒜 a) (Away ℬ (f a)) :=
  (Away.map f a).toAlgebra

/-- The homogeneous chart map preserves the actual degree-zero constants. -/
theorem chart_map_fromZero (f : 𝒜 →+*ᵍ ℬ) (a : A) (s : 𝒜 0) :
    Away.map f a (fromZeroRingHom 𝒜 (Submonoid.powers a) s) =
      fromZeroRingHom ℬ (Submonoid.powers (f a)) (f.gradedZeroRingHom s) := by
  ext
  dsimp only [Away.map, fromZeroRingHom]
  simp [HomogeneousLocalization.map_mk]

/-- A degree-zero constant has its actual ordinary fraction value. -/
theorem val_fromZero {M : Submonoid A} (s : 𝒜 0) :
    (fromZeroRingHom 𝒜 M s).val = Localization.mk (s : A) 1 := rfl

/-- Every actual localized homogeneous-chart fraction has a source numerator. -/
theorem chart_surj (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
    [Algebra A B] [IsLocalization.Away (s : A) B]
    (hf : f.toRingHom = algebraMap A B) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)
    (z : Away ℬ (f a)) :
    ∃ (n : ℕ) (x : Away 𝒜 a),
      z * Away.map f a (fromZeroRingHom 𝒜 (Submonoid.powers a) s) ^ n =
        Away.map f a x := by
  obtain ⟨m, c, hc, rfl⟩ := Away.mk_surjective ℬ (map_mem f ha) z
  obtain ⟨n, b, hb, hcb⟩ := exists_homogeneous_numerator f s hf hc
  refine ⟨n, Away.mk 𝒜 ha m b hb, ?_⟩
  rw [chart_map_fromZero]
  ext
  simp only [val_mul, val_pow, Away.val_mk, Away.map_mk,
    val_fromZero, Localization.mk_pow, Localization.mk_mul, one_pow, mul_one]
  change Localization.mk (c * f (s : A) ^ n) _ = _
  rw [hcb]

/-- Equal target chart fractions agree after a power of the actual coefficient. -/
theorem chart_exists_of_eq (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
    [Algebra A B] [IsLocalization.Away (s : A) B]
    (hf : f.toRingHom = algebraMap A B) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)
    (x y : Away 𝒜 a) (hxy : Away.map f a x = Away.map f a y) :
    ∃ n : ℕ, (fromZeroRingHom 𝒜 (Submonoid.powers a) s) ^ n * x =
      (fromZeroRingHom 𝒜 (Submonoid.powers a) s) ^ n * y := by
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective 𝒜 ha x
  obtain ⟨m, q, hq, rfl⟩ := Away.mk_surjective 𝒜 ha y
  replace hxy := congrArg val hxy
  simp only [Away.map_mk, Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists] at hxy
  obtain ⟨⟨_, k, rfl⟩, hcross⟩ := hxy
  have hmap : algebraMap A B (a ^ k * (p * a ^ m)) =
      algebraMap A B (a ^ k * (q * a ^ n)) := by
    rw [← hf]
    change f (a ^ k * (p * a ^ m)) = f (a ^ k * (q * a ^ n))
    simpa only [map_mul, map_pow, mul_comm] using hcross
  obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (s : A) hmap
  refine ⟨N, ?_⟩
  ext
  simp only [val_mul, val_pow, val_fromZero, Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, one_pow, one_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨a ^ k, ⟨k, rfl⟩⟩, ?_⟩
  change a ^ k * (a ^ m * ((s : A) ^ N * p)) =
    a ^ k * (a ^ n * ((s : A) ^ N * q))
  calc
    _ = (s : A) ^ N * (a ^ k * (p * a ^ m)) := by ring
    _ = (s : A) ^ N * (a ^ k * (q * a ^ n)) := hN
    _ = _ := by ring

/-- The degree-zero coefficient becomes a unit in the actual target chart. -/
theorem chart_map_isUnit (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
    [Algebra A B] [IsLocalization.Away (s : A) B]
    (hf : f.toRingHom = algebraMap A B) (a : A) :
    IsUnit (Away.map f a (fromZeroRingHom 𝒜 (Submonoid.powers a) s)) := by
  have hu : IsUnit (f (s : A)) := by
    change IsUnit (f.toRingHom (s : A))
    rw [hf]
    exact IsLocalization.Away.algebraMap_isUnit (S := B) (s : A)
  have hu0 : IsUnit (f.gradedZeroRingHom s) := by
    have h := hu.map (GradedRing.projZeroRingHom' ℬ)
    change IsUnit ((GradedRing.projZeroRingHom' ℬ) ((f.gradedZeroRingHom s : ℬ 0) : B)) at h
    rw [GradedRing.projZeroRingHom'_apply_coe] at h
    exact h
  rw [chart_map_fromZero]
  exact hu0.map (fromZeroRingHom ℬ (Submonoid.powers (f a)))

/-- The actual homogeneous chart map is localization at the degree-zero coefficient. -/
theorem chart_isLocalization (f : 𝒜 →+*ᵍ ℬ) (s : 𝒜 0)
    [Algebra A B] [IsLocalization.Away (s : A) B]
    (hf : f.toRingHom = algebraMap A B) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    letI := chartAlgebra f a
    IsLocalization.Away (fromZeroRingHom 𝒜 (Submonoid.powers a) s)
      (Away ℬ (f a)) := by
  let := chartAlgebra f a
  apply IsLocalization.Away.mk
  · exact chart_map_isUnit f s hf a
  · exact chart_surj f s hf ha
  · exact chart_exists_of_eq f s hf ha

end DeJongAlterations.Algebra.HomogeneousCoefficientLocalization
