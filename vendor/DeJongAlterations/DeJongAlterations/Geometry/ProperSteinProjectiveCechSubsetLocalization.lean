import DeJongAlterations.Geometry.ProperSteinProjectiveCechModuleLocalization
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubset

/-! # The actual homogeneous coordinate-subset localization diagram

Subset arrows use the native module-localization universal property. The
restriction maps need not be injective, so actual quotient relations and
localization torsion are retained.
-/

/-!
Adapted from the same workspace `BingWangEntropy/HomogeneousSubsetLocalization.lean`,
SHA256 c810b535733c14880063c56d7eb09080d5767f82521bd24ea3283e1b7d13246c.
Only native Mathlib and owned DeJongAlterations algebraic producers are imported.
-/

universe u

open CategoryTheory DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section DivisorLocalizations

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- A true divisor of the inverted element acts invertibly on the actual localized module. -/
theorem actualLocalizedModuleDivisorUnits (x y : R) (hxy : x ∣ y) :
    ∀ s : Submonoid.powers x,
      IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers y) M)) s) := by
  let E := Module.End R (LocalizedModule (Submonoid.powers y) M)
  obtain ⟨c, hy⟩ := hxy
  have hu : IsUnit (algebraMap R E y) :=
    IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Submonoid.powers y) M)
      (⟨y, 1, by simp⟩ : Submonoid.powers y)
  have hxunit : IsUnit (algebraMap R E x) := by
    have hmul := congrArg (algebraMap R E) hy
    rw [map_mul] at hmul
    rw [hmul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at hu
    exact hu.1
  intro s
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact hxunit.pow n

/-- The actual native localization restriction associated to actual divisibility. -/
def actualLocalizedModuleDivisorRestriction (x y : R) (hxy : x ∣ y) :
    LocalizedModule (Submonoid.powers x) M →ₗ[R]
      LocalizedModule (Submonoid.powers y) M :=
  LocalizedModule.lift (Submonoid.powers x)
    (LocalizedModule.mkLinearMap (Submonoid.powers y) M)
    (actualLocalizedModuleDivisorUnits (M := M) x y hxy)

/-- The true restriction sends every true original module element to its true localized image. -/
theorem actualLocalizedModuleDivisorRestriction_comp (x y : R) (hxy : x ∣ y) :
    (actualLocalizedModuleDivisorRestriction (M := M) x y hxy).comp
      (LocalizedModule.mkLinearMap (Submonoid.powers x) M) =
        LocalizedModule.mkLinearMap (Submonoid.powers y) M :=
  LocalizedModule.lift_comp (Submonoid.powers x) _ _

/-- Actual divisibility restrictions compose, as actual module localization maps. -/
theorem actualLocalizedModuleDivisorRestriction_trans (x y z : R)
    (hxy : x ∣ y) (hyz : y ∣ z) :
    (actualLocalizedModuleDivisorRestriction (M := M) y z hyz).comp
      (actualLocalizedModuleDivisorRestriction (M := M) x y hxy) =
        actualLocalizedModuleDivisorRestriction (M := M) x z (hxy.trans hyz) := by
  apply IsLocalizedModule.ext (Submonoid.powers x)
    (LocalizedModule.mkLinearMap (Submonoid.powers x) M)
    (actualLocalizedModuleDivisorUnits (M := M) x z (hxy.trans hyz))
  rw [LinearMap.comp_assoc, actualLocalizedModuleDivisorRestriction_comp,
    actualLocalizedModuleDivisorRestriction_comp, actualLocalizedModuleDivisorRestriction_comp]

/-- Actual restriction along equality of the inverted element is the actual identity. -/
theorem actualLocalizedModuleDivisorRestriction_refl (x : R) :
    actualLocalizedModuleDivisorRestriction (M := M) x x (dvd_refl x) = LinearMap.id := by
  apply IsLocalizedModule.ext (Submonoid.powers x)
    (LocalizedModule.mkLinearMap (Submonoid.powers x) M)
    (actualLocalizedModuleDivisorUnits (M := M) x x (dvd_refl x))
  rw [actualLocalizedModuleDivisorRestriction_comp, LinearMap.id_comp]

/-- Restriction to a genuine multiple rewrites a literal fraction using the
actual complementary factor in its numerator. -/
theorem actualLocalizedModuleDivisorRestriction_mk (x y c : R)
    (hy : y = x * c) (m : M) (n : ℕ) :
    actualLocalizedModuleDivisorRestriction (M := M) x y ⟨c, hy⟩
      (LocalizedModule.mk m (homogeneousPowerDenominator x n)) =
        LocalizedModule.mk (c ^ n • m) (homogeneousPowerDenominator y n) := by
  rw [actualLocalizedModuleDivisorRestriction, LocalizedModule.lift_mk,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff,
    LocalizedModule.smul'_mk, smul_smul]
  change LocalizedModule.mk m 1 =
    LocalizedModule.mk ((x ^ n * c ^ n) • m) (homogeneousPowerDenominator y n)
  rw [← mul_pow, ← congrArg (fun z => z ^ n) hy]
  exact (LocalizedModule.mk_cancel (homogeneousPowerDenominator y n) m).symm

/-- Actual localization restrictions commute with actual module maps. -/
theorem actualLocalizedModuleDivisorRestriction_map
    {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (x y : R) (hxy : x ∣ y) :
    (actualLocalizedModuleDivisorRestriction (M := N) x y hxy).comp
      (actualLocalizedModuleMap (Submonoid.powers x) f) =
        (actualLocalizedModuleMap (Submonoid.powers y) f).comp
          (actualLocalizedModuleDivisorRestriction (M := M) x y hxy) := by
  obtain ⟨c, hy⟩ := hxy
  apply LinearMap.ext
  intro z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = homogeneousPowerDenominator x n := Subtype.ext hn.symm
    simp only [LinearMap.comp_apply]
    rw [hs, actualLocalizedModuleMap_mk,
      actualLocalizedModuleDivisorRestriction_mk x y c hy,
      actualLocalizedModuleDivisorRestriction_mk x y c hy,
      actualLocalizedModuleMap_mk, map_smul]

end DivisorLocalizations

section HomogeneousRestrictions

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- An actual homogeneous complementary factor produces an actual restriction
between literal homogeneous degree pieces. -/
def localizedHomogeneousDivisorRestriction (x y c : R) (d e : ℤ)
    (hx : x ∈ 𝒜 d) (hc : c ∈ 𝒜 e) (hy : y = x * c) (k : ℤ) :
    localizedHomogeneousModulePiece 𝒜 ℳ x d hx k →ₗ[K]
      localizedHomogeneousModulePiece 𝒜 ℳ y (d + e)
        (hy ▸ SetLike.mul_mem_graded hx hc) k :=
  (((actualLocalizedModuleDivisorRestriction (M := M) x y ⟨c, hy⟩).restrictScalars K).comp
    (localizedHomogeneousModulePiece 𝒜 ℳ x d hx k).subtype).codRestrict _ (by
      rintro z
      obtain ⟨n, m, hm, he⟩ := z.property
      refine ⟨n, c ^ n • m, ?_, ?_⟩
      · convert SetLike.GradedSMul.smul_mem
          (SetLike.pow_mem_graded (A := 𝒜) n hc) hm using 1
        congr 1
        simp only [nsmul_eq_mul, vadd_eq_add]
        ring
      · change LocalizedModule.mk (c ^ n • m) (homogeneousPowerDenominator y n) =
          actualLocalizedModuleDivisorRestriction (M := M) x y ⟨c, hy⟩ z.val
        rw [← he, actualLocalizedModuleDivisorRestriction_mk x y c hy m n])

end HomogeneousRestrictions

section CoordinateSubsets

variable {K R M I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [LinearOrder I]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

/-- The actual product inverted on a true coordinate intersection. -/
def homogeneousCoordinateSubsetProduct (S : Finset I) : R := ∏ i ∈ S, x i

omit [LinearOrder I] in
/-- The product of true degree-one coordinates has its true cardinal degree. -/
theorem homogeneousCoordinateSubsetProduct_degree (hx : ∀ i, x i ∈ 𝒜 1) (S : Finset I) :
    homogeneousCoordinateSubsetProduct x S ∈ 𝒜 (S.card : ℤ) := by
  simpa only [homogeneousCoordinateSubsetProduct, Finset.sum_const,
    nsmul_eq_mul, mul_one] using
    SetLike.prod_mem_graded 𝒜 (fun _ : I => (1 : ℤ)) x (F := S) (fun i _ => hx i)

/-- A coordinate-subset inclusion has its actual complementary product factor. -/
theorem homogeneousCoordinateSubsetProduct_factor {S T : Finset I} (hST : S ⊆ T) :
    homogeneousCoordinateSubsetProduct x T =
      homogeneousCoordinateSubsetProduct x S * homogeneousCoordinateSubsetProduct x (T \ S) := by
  exact (mul_comm _ _).trans (Finset.prod_sdiff hST) |>.symm

/-- A true coordinate-subset product divides the true product on every larger subset. -/
theorem homogeneousCoordinateSubsetProduct_dvd {S T : Finset I} (hST : S ⊆ T) :
    homogeneousCoordinateSubsetProduct x S ∣ homogeneousCoordinateSubsetProduct x T :=
  ⟨homogeneousCoordinateSubsetProduct x (T \ S),
    homogeneousCoordinateSubsetProduct_factor x hST⟩

/-- The true restriction on a true coordinate intersection retains its literal
degree and all actual localization relations. -/
def homogeneousCoordinateSubsetRestriction {S T : Finset I} (hST : S ⊆ T) (k : ℤ) :
    localizedHomogeneousModulePiece 𝒜 ℳ (homogeneousCoordinateSubsetProduct x S)
      (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k →ₗ[K]
    localizedHomogeneousModulePiece 𝒜 ℳ (homogeneousCoordinateSubsetProduct x T)
      (T.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx T) k :=
  (((actualLocalizedModuleDivisorRestriction (M := M)
    (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
    ⟨homogeneousCoordinateSubsetProduct x (T \ S),
      homogeneousCoordinateSubsetProduct_factor x hST⟩).restrictScalars K).comp
    (localizedHomogeneousModulePiece 𝒜 ℳ (homogeneousCoordinateSubsetProduct x S)
      (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k).subtype).codRestrict _ (by
      intro z
      obtain ⟨n, m, hm, he⟩ := z.property
      refine ⟨n, homogeneousCoordinateSubsetProduct x (T \ S) ^ n • m, ?_, ?_⟩
      · have hc : (T.card : ℤ) = (S.card : ℤ) + ((T \ S).card : ℤ) := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hST]
          have hcard := Finset.card_le_card hST
          omega
        convert SetLike.GradedSMul.smul_mem
          (SetLike.pow_mem_graded (A := 𝒜) n
            (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx (T \ S))) hm using 1
        congr 1
        simp only [nsmul_eq_mul, vadd_eq_add]
        rw [hc]
        ring
      · change LocalizedModule.mk _ _ =
          actualLocalizedModuleDivisorRestriction (M := M)
            (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
            (homogeneousCoordinateSubsetProduct_dvd x hST) z.val
        rw [← he, actualLocalizedModuleDivisorRestriction_mk
          (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
          (homogeneousCoordinateSubsetProduct x (T \ S))
          (homogeneousCoordinateSubsetProduct_factor x hST) m n])

/-- The genuine homogeneous coordinate-intersection diagram of a true graded module. -/
def homogeneousCoordinateSubsetDiagram (k : ℤ) : Finset I ⥤ ModuleCat.{u} K where
  obj S := ModuleCat.of K (localizedHomogeneousModulePiece 𝒜 ℳ
    (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k)
  map f := ModuleCat.ofHom (homogeneousCoordinateSubsetRestriction 𝒜 ℳ x hx (leOfHom f) k)
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change actualLocalizedModuleDivisorRestriction (M := M)
      (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x S)
      (dvd_refl _) z.val = z.val
    rw [actualLocalizedModuleDivisorRestriction_refl]
    rfl
  map_comp {S T U} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change actualLocalizedModuleDivisorRestriction (M := M)
      (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x U)
      (homogeneousCoordinateSubsetProduct_dvd x ((leOfHom f).trans (leOfHom g))) z.val =
      actualLocalizedModuleDivisorRestriction (M := M)
        (homogeneousCoordinateSubsetProduct x T) (homogeneousCoordinateSubsetProduct x U)
        (homogeneousCoordinateSubsetProduct_dvd x (leOfHom g))
        (actualLocalizedModuleDivisorRestriction (M := M)
          (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
          (homogeneousCoordinateSubsetProduct_dvd x (leOfHom f)) z.val)
    exact (LinearMap.congr_fun (actualLocalizedModuleDivisorRestriction_trans _ _ _
      (homogeneousCoordinateSubsetProduct_dvd x (leOfHom f))
      (homogeneousCoordinateSubsetProduct_dvd x (leOfHom g))) z.val).symm

/-- The native normalized coordinate-cover Čech complex of a true graded module
in any actual integral twisting degree. -/
def homogeneousCoordinateCechComplex (k : ℤ) : CochainComplex (ModuleCat.{u} K) ℕ :=
  subsetCechComplex (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k)

variable {N P : Type u} [AddCommGroup N] [AddCommGroup P]
  [Module K N] [Module K P] [Module R N] [Module R P]
  [IsScalarTower K R N] [IsScalarTower K R P]
  (𝒩 : ℤ → Submodule K N) (𝓟 : ℤ → Submodule K P)
  [SetLike.GradedSMul 𝒜 𝒩] [SetLike.GradedSMul 𝒜 𝓟]

/-- A genuine homogeneous module map gives a genuine natural map of all actual
coordinate-subset localizations. -/
def homogeneousCoordinateSubsetDiagramMap (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (k : ℤ) :
    homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k ⟶
      homogeneousCoordinateSubsetDiagram 𝒜 𝒩 x hx k where
  app S := ModuleCat.ofHom (localizedHomogeneousModuleMap 𝒜 ℳ 𝒩 f hf
    (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k)
  naturality {S T} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change actualLocalizedModuleMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x T)) f
      (actualLocalizedModuleDivisorRestriction (M := M)
        (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
        (homogeneousCoordinateSubsetProduct_dvd x (leOfHom a)) z.val) =
      actualLocalizedModuleDivisorRestriction (M := N)
        (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
        (homogeneousCoordinateSubsetProduct_dvd x (leOfHom a))
        (actualLocalizedModuleMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x S)) f z.val)
    exact (LinearMap.congr_fun (actualLocalizedModuleDivisorRestriction_map f _ _
      (homogeneousCoordinateSubsetProduct_dvd x (leOfHom a))) z.val).symm

/-- Actual homogeneous module maps induce actual maps of the native coordinate-cover complexes. -/
def homogeneousCoordinateCechComplexMap (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (k : ℤ) :
    homogeneousCoordinateCechComplex 𝒜 ℳ x hx k ⟶
      homogeneousCoordinateCechComplex 𝒜 𝒩 x hx k :=
  subsetCechComplexMap (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf k)

/-- A true homogeneous surjection is a surjection on every actual coordinate intersection. -/
theorem homogeneousCoordinateSubsetDiagramMap_surjective
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    (f : M →ₗ[R] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)
    (hs : Function.Surjective f) (k : ℤ) (S : Finset I) :
    Function.Surjective (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf k |>.app S) :=
  localizedHomogeneousModuleMap_surjective 𝒜 ℳ 𝒩 f hf hs
    (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k

/-- A true homogeneous exact sequence is exact on every actual coordinate intersection. -/
theorem homogeneousCoordinateSubsetDiagramMap_exact
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d)
    (hg : ∀ d m, m ∈ 𝒩 d → g m ∈ 𝓟 d)
    (he : Function.Exact f g) (k : ℤ) (S : Finset I) :
    Function.Exact (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf k |>.app S)
      (homogeneousCoordinateSubsetDiagramMap 𝒜 𝒩 x hx 𝓟 g hg k |>.app S) :=
  localizedHomogeneousModuleMap_exact 𝒜 ℳ 𝒩 𝓟 f g hf hg he
    (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k

end CoordinateSubsets

section CechExactness

variable {K I : Type u} [CommRing K] [LinearOrder I]
  {F G H : Finset I ⥤ ModuleCat.{u} K}

omit [LinearOrder I] in
/-- True pointwise surjectivity of true diagrams is surjectivity of every
actual cardinal Čech term. -/
theorem subsetCechCardMap_surjective (α : F ⟶ G)
    (hs : ∀ S, Function.Surjective (α.app S)) (n : ℕ) :
    Function.Surjective (subsetCechCardMap α n) := by
  classical
  intro z
  choose a ha using fun S => hs S (z.val S)
  refine ⟨⟨fun S => if S.card = n then a S else 0, ?_⟩, ?_⟩
  · intro S hS
    simp only [if_neg hS]
  · apply Subtype.ext
    funext S
    change α.app S (if S.card = n then a S else 0) = z.val S
    by_cases hS : S.card = n
    · rw [if_pos hS, ha S]
    · rw [if_neg hS, map_zero, z.property S hS]

omit [LinearOrder I] in
/-- True pointwise exactness of true diagrams is exactness of every actual
cardinal Čech term, including diagrams with localization torsion. -/
theorem subsetCechCardMap_exact (α : F ⟶ G) (β : G ⟶ H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S)) (n : ℕ) :
    Function.Exact (subsetCechCardMap α n) (subsetCechCardMap β n) := by
  classical
  intro z
  constructor
  · intro hz
    have hzS (S : Finset I) : β.app S (z.val S) = 0 :=
      congrArg (fun w : subsetCechCardPiece H n => w.val S) hz
    choose a ha using fun S => (he S (z.val S)).mp (hzS S)
    refine ⟨⟨fun S => if S.card = n then a S else 0, ?_⟩, ?_⟩
    · intro S hS
      simp only [if_neg hS]
    · apply Subtype.ext
      funext S
      change α.app S (if S.card = n then a S else 0) = z.val S
      by_cases hS : S.card = n
      · rw [if_pos hS, ha S]
      · rw [if_neg hS, map_zero, z.property S hS]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext S
    change β.app S (α.app S (a.val S)) = 0
    exact (he S).apply_apply_eq_zero (a.val S)

end CechExactness

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
