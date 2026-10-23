import DeJongAlterations.Geometry.ProperSteinProjectiveCechGradedPresentation

/-! # Actual homogeneous localized module pieces

The degree pieces below consist of literal native localization fractions.
Their homogeneous numerator degrees include the actual denominator degree.
The definition permits localization torsion and negative twisting degrees.
-/

/-!
Adapted from the same workspace `BingWangEntropy/HomogeneousModuleLocalization.lean`,
SHA256 1aa1a339f0792163cde6f82255b720568d9f6d806e6d6f7b3a05fb1a156ceb41.
Only native Mathlib and the owned DeJongAlterations modules are imported.
-/

universe u v w

open DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {K : Type u} {R : Type v} {M : Type w}
  [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- A literal power denominator in the actual native localization monoid. -/
def homogeneousPowerDenominator (x : R) (n : ℕ) : Submonoid.powers x :=
  ⟨x ^ n, n, rfl⟩

/-- Multiplication of actual power denominators adds their actual exponents. -/
theorem homogeneousPowerDenominator_add (x : R) (n p : ℕ) :
    homogeneousPowerDenominator x (n + p) =
      homogeneousPowerDenominator x n * homogeneousPowerDenominator x p :=
  Subtype.ext (pow_add x n p)

/-- The genuine degree-k localized module piece, with literal homogeneous numerators. -/
def localizedHomogeneousModulePiece (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ) :
    Submodule K (LocalizedModule (Submonoid.powers x) M) where
  carrier := {z | ∃ n : ℕ, ∃ m : M, m ∈ ℳ (k + (n : ℤ) * d) ∧
    LocalizedModule.mk m (homogeneousPowerDenominator x n) = z}
  zero_mem' := by
    exact ⟨0, 0, (ℳ _).zero_mem, LocalizedModule.zero_mk _⟩
  add_mem' := by
    rintro z z' ⟨n, m, hm, rfl⟩ ⟨p, m', hm', rfl⟩
    refine ⟨n + p, x ^ p • m + x ^ n • m', ?_, ?_⟩
    · apply (ℳ _).add_mem
      · convert SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded (A := 𝒜) p hx) hm using 1
        congr 1
        simp only [nsmul_eq_mul, Nat.cast_add, vadd_eq_add]
        ring
      · convert SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded (A := 𝒜) n hx) hm' using 1
        congr 1
        simp only [nsmul_eq_mul, Nat.cast_add, vadd_eq_add]
        ring
    · rw [LocalizedModule.mk_add_mk, homogeneousPowerDenominator_add]
      rfl
  smul_mem' := by
    rintro a z ⟨n, m, hm, rfl⟩
    exact ⟨n, a • m, (ℳ _).smul_mem a hm, (LocalizedModule.smul'_mk a m _).symm⟩

section Maps

variable {N : Type w} [AddCommGroup N] [Module K N] [Module R N]
  [IsScalarTower K R N] (𝒩 : ℤ → Submodule K N) [SetLike.GradedSMul 𝒜 𝒩]

/-- The native localization of an actual linear module map. -/
def actualLocalizedModuleMap (S : Submonoid R) (f : M →ₗ[R] N) :
    LocalizedModule S M →ₗ[R] LocalizedModule S N :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f

omit [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] in
/-- The actual localized map sends actual fractions to their actual image fractions. -/
theorem actualLocalizedModuleMap_mk (S : Submonoid R) (f : M →ₗ[R] N)
    (m : M) (s : S) :
    actualLocalizedModuleMap S f (LocalizedModule.mk m s) = LocalizedModule.mk (f m) s := by
  rw [IsLocalizedModule.mk_eq_mk', actualLocalizedModuleMap,
    IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

/-- Genuine degree-preserving maps induce genuine maps of the literal localized degree pieces. -/
def localizedHomogeneousModuleMap (f : M →ₗ[R] N)
    (hf : ∀ k m, m ∈ ℳ k → f m ∈ 𝒩 k)
    (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ) :
    localizedHomogeneousModulePiece 𝒜 ℳ x d hx k →ₗ[K]
      localizedHomogeneousModulePiece 𝒜 𝒩 x d hx k :=
  (((actualLocalizedModuleMap (Submonoid.powers x) f).restrictScalars K).comp
    (localizedHomogeneousModulePiece 𝒜 ℳ x d hx k).subtype).codRestrict _ (by
      rintro z
      obtain ⟨n, m, hm, he⟩ := z.property
      refine ⟨n, f m, hf _ m hm, ?_⟩
      change LocalizedModule.mk (f m) (homogeneousPowerDenominator x n) =
        actualLocalizedModuleMap (Submonoid.powers x) f z.val
      rw [← he, actualLocalizedModuleMap_mk])

/-- Surjectivity of actual homogeneous maps gives surjectivity of actual localized degree maps. -/
theorem localizedHomogeneousModuleMap_surjective
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    (f : M →ₗ[R] N) (hf : ∀ k m, m ∈ ℳ k → f m ∈ 𝒩 k)
    (hs : Function.Surjective f) (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ) :
    Function.Surjective (localizedHomogeneousModuleMap 𝒜 ℳ 𝒩 f hf x d hx k) := by
  intro z
  obtain ⟨n, m, hm, he⟩ := z.property
  obtain ⟨a, ha, hfa⟩ := homogeneousMap_surjectiveDegree ℳ 𝒩 f hf hs _ m hm
  refine ⟨⟨LocalizedModule.mk a (homogeneousPowerDenominator x n), n, a, ha, rfl⟩, ?_⟩
  apply Subtype.ext
  change actualLocalizedModuleMap (Submonoid.powers x) f
    (LocalizedModule.mk a (homogeneousPowerDenominator x n)) = z.val
  rw [actualLocalizedModuleMap_mk, hfa, he]

section Exactness

variable {P : Type w} [AddCommGroup P] [Module K P] [Module R P]
  [IsScalarTower K R P] (𝓟 : ℤ → Submodule K P) [SetLike.GradedSMul 𝒜 𝓟]

/-- Actual homogeneous localization preserves actual degreewise exactness, even
when a quotient has localization torsion. -/
theorem localizedHomogeneousModuleMap_exact
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ k m, m ∈ ℳ k → f m ∈ 𝒩 k)
    (hg : ∀ k m, m ∈ 𝒩 k → g m ∈ 𝓟 k) (h : Function.Exact f g)
    (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ) :
    Function.Exact (localizedHomogeneousModuleMap 𝒜 ℳ 𝒩 f hf x d hx k)
      (localizedHomogeneousModuleMap 𝒜 𝒩 𝓟 g hg x d hx k) := by
  intro z
  constructor
  · intro hz
    obtain ⟨n, m, hm, he⟩ := z.property
    have hz' : actualLocalizedModuleMap (Submonoid.powers x) g z.val = 0 :=
      congrArg Subtype.val hz
    have hzmk : IsLocalizedModule.mk'
        (LocalizedModule.mkLinearMap (Submonoid.powers x) P) (g m)
        (homogeneousPowerDenominator x n) = 0 := by
      rw [← IsLocalizedModule.mk_eq_mk', ← actualLocalizedModuleMap_mk, he]
      exact hz'
    obtain ⟨t, ht⟩ :=
      (IsLocalizedModule.mk'_eq_zero'
        (LocalizedModule.mkLinearMap (Submonoid.powers x) P)
        (homogeneousPowerDenominator x n)).mp hzmk
    obtain ⟨p, hp⟩ := t.property
    have hgzero : g (x ^ p • m) = 0 := by
      rw [map_smul]
      simpa only [Submonoid.smul_def, ← hp] using ht
    have hdeg : x ^ p • m ∈ 𝒩 (k + ((n + p : ℕ) : ℤ) * d) := by
      convert SetLike.GradedSMul.smul_mem
        (SetLike.pow_mem_graded (A := 𝒜) p hx) hm using 1
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_add, vadd_eq_add]
      ring
    obtain ⟨a, ha, hfa⟩ := homogeneousMap_exactDegree ℳ 𝒩 f g hf h _ _ hdeg hgzero
    refine ⟨⟨LocalizedModule.mk a (homogeneousPowerDenominator x (n + p)),
      n + p, a, ha, rfl⟩, ?_⟩
    apply Subtype.ext
    change actualLocalizedModuleMap (Submonoid.powers x) f
      (LocalizedModule.mk a (homogeneousPowerDenominator x (n + p))) = z.val
    rw [actualLocalizedModuleMap_mk, hfa, ← he, homogeneousPowerDenominator_add]
    exact LocalizedModule.mk_cancel_common_right
      (homogeneousPowerDenominator x n) (homogeneousPowerDenominator x p) m
  · rintro ⟨a, rfl⟩
    obtain ⟨n, m, hm, he⟩ := a.property
    apply Subtype.ext
    change actualLocalizedModuleMap (Submonoid.powers x) g
      (actualLocalizedModuleMap (Submonoid.powers x) f a.val) = 0
    rw [← he, actualLocalizedModuleMap_mk, actualLocalizedModuleMap_mk,
      h.apply_apply_eq_zero, LocalizedModule.zero_mk]

end Exactness

end Maps

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
