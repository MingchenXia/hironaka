import DeJongAlterations.Geometry.ProperSteinProjectiveCechSyzygies
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetLocalization
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Genuine native Čech dimension shifting

True homogeneous kernel sequences give actual short exact sequences of actual
coordinate-cover complexes. The native connecting morphism and exact homology
sequence supply the dimension-shifting step.
-/

/-!
Adapted from the same workspace `BingWangEntropy/HomogeneousCechDimensionShift.lean`,
SHA256 22d8e2498f5776148aab5be7d5017a6762b67af76919fc017e1b2feb8e84eadb.
Only native Mathlib and owned DeJongAlterations modules are imported.
-/

universe u

open CategoryTheory DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section FiniteExactModules

variable {K A B C : Type u} [CommRing K] [IsNoetherianRing K]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module K A] [Module K B] [Module K C]

/-- True exactness and finite outer modules imply that the actual middle module is finite. -/
theorem actualExact_moduleFinite_middle (f : A →ₗ[K] B) (g : B →ₗ[K] C)
    (he : Function.Exact f g) [Module.Finite K A] [Module.Finite K C] :
    Module.Finite K B := by
  have : Module.Finite K (LinearMap.range g) :=
    Module.Finite.of_injective (LinearMap.range g).subtype (LinearMap.range g).subtype_injective
  have he' : Function.Exact f g.rangeRestrict := by
    intro b
    constructor
    · intro hb
      exact (he b).mp (congrArg Subtype.val hb)
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      exact he.apply_apply_eq_zero a
  exact Module.Finite.of_exact he' (by rintro ⟨c, b, rfl⟩; exact ⟨b, rfl⟩)

/-- The actual native connecting morphism gives the genuine one-step finiteness dimension shift. -/
theorem nativeCochainHomology_finite_dimensionShift
    (S : ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ)) (hS : S.ShortExact) (p : ℕ)
    [Module.Finite K (S.X₂.homology p)] [Module.Finite K (S.X₁.homology (p + 1))] :
    Module.Finite K (S.X₃.homology p) := by
  have he := hS.homology_exact₃ p (p + 1) (by rfl)
  have he' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  exact actualExact_moduleFinite_middle _ _ he'

end FiniteExactModules

section DiagramShortExact

variable {K I : Type u} [CommRing K] [LinearOrder I]
  {F G H : Finset I ⥤ ModuleCat.{u} K}

omit [LinearOrder I] in
/-- True pointwise injectivity gives true injectivity on every actual cardinal Čech term. -/
theorem subsetCechCardMap_injective (α : F ⟶ G)
    (hi : ∀ S, Function.Injective (α.app S)) (n : ℕ) :
    Function.Injective (subsetCechCardMap α n) := by
  intro a b hab
  apply Subtype.ext
  funext S
  apply hi S
  exact congrArg (fun z : subsetCechCardPiece G n => z.val S) hab

/-- Actual pointwise exact diagram maps form an actual short complex of native Čech complexes. -/
def actualSubsetCechShortComplex (α : F ⟶ G) (β : G ⟶ H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S)) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) :=
  ShortComplex.mk (subsetCechComplexMap α) (subsetCechComplexMap β) (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext S
    change β.app S (α.app S (a.val S)) = 0
    exact (he S).apply_apply_eq_zero (a.val S))

/-- True pointwise short exactness gives true native Čech-complex short exactness. -/
theorem actualSubsetCechShortComplex_shortExact (α : F ⟶ G) (β : G ⟶ H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S))
    (hi : ∀ S, Function.Injective (α.app S))
    (hs : ∀ S, Function.Surjective (β.app S)) :
    (actualSubsetCechShortComplex α β he).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact subsetCechCardMap_exact α β he (n + 1)
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact subsetCechCardMap_injective α hi (n + 1)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact subsetCechCardMap_surjective β hs (n + 1)

end DiagramShortExact

section CoverDimension

variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
  (F : Finset I ⥤ ModuleCat.{u} K)

omit [LinearOrder I] in
/-- The actual cardinal Čech term vanishes above the true number of cover coordinates. -/
theorem subsetCechCardPiece_subsingleton (n : ℕ) (hn : Fintype.card I < n) :
    Subsingleton (subsetCechCardPiece F n) := by
  constructor
  intro a b
  apply Subtype.ext
  funext S
  have hS : S.card ≠ n := by
    have hc := Finset.card_le_univ S
    simpa only [Finset.card_univ] using ne_of_lt (lt_of_le_of_lt hc hn)
  rw [a.property S hS, b.property S hS]

/-- The true finite cover makes the actual native Čech complex exact above its cardinal bound. -/
theorem subsetCechComplex_exactAt_of_card_le (p : ℕ) (hp : Fintype.card I ≤ p) :
    (subsetCechComplex F).ExactAt p := by
  have : Subsingleton ((subsetCechComplex F).X p) :=
    subsetCechCardPiece_subsingleton F (p + 1) (by omega)
  exact HomologicalComplex.ExactAt.of_isZero (ModuleCat.isZero_of_subsingleton _)

/-- True native Čech cohomology above the actual finite cover dimension is zero. -/
theorem subsetCechComplex_homology_isZero_of_card_le (p : ℕ) (hp : Fintype.card I ≤ p) :
    Limits.IsZero ((subsetCechComplex F).homology p) :=
  (subsetCechComplex_exactAt_of_card_le F p hp).isZero_homology

/-- True native Čech cohomology above the actual finite cover dimension is a finite module. -/
theorem subsetCechComplex_homology_finite_of_card_le (p : ℕ) (hp : Fintype.card I ≤ p) :
    Module.Finite K ((subsetCechComplex F).homology p) := by
  have : Subsingleton ((subsetCechComplex F).homology p) :=
    ModuleCat.subsingleton_of_isZero (subsetCechComplex_homology_isZero_of_card_le F p hp)
  infer_instance

end CoverDimension

section HomogeneousInjection

variable {K R M N : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module R N] [IsScalarTower K R N]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) (𝒩 : ℤ → Submodule K N)
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]

/-- True homogeneous injections stay injective on true localized degree pieces. -/
theorem localizedHomogeneousModuleMap_injective (f : M →ₗ[R] N)
    (hf : ∀ k m, m ∈ ℳ k → f m ∈ 𝒩 k) (hi : Function.Injective f)
    (x : R) (d : ℤ) (hx : x ∈ 𝒜 d) (k : ℤ) :
    Function.Injective (localizedHomogeneousModuleMap 𝒜 ℳ 𝒩 f hf x d hx k) := by
  intro a b hab
  apply Subtype.ext
  exact IsLocalizedModule.map_injective (Submonoid.powers x)
    (LocalizedModule.mkLinearMap (Submonoid.powers x) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers x) N) f hi
      (congrArg Subtype.val hab)

variable {I : Type u} [LinearOrder I] (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

/-- True homogeneous injections stay injective at every actual coordinate intersection. -/
theorem homogeneousCoordinateSubsetDiagramMap_injective (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hi : Function.Injective f)
    (k : ℤ) (S : Finset I) :
    Function.Injective
      (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf k |>.app S) :=
  localizedHomogeneousModuleMap_injective 𝒜 ℳ 𝒩 f hf hi
    (homogeneousCoordinateSubsetProduct x S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k

end HomogeneousInjection

section HomogeneousKernelSequence

variable {K R M N I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [AddCommGroup N] [LinearOrder I]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module R N] [IsScalarTower K R N]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) (𝒩 : ℤ → Submodule K N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

/-- The actual homogeneous kernel sequence gives a literal short complex of actual coordinate-cover complexes. -/
def actualHomogeneousKernelCechShortComplex (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (k : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) := by
  let ℒ := homogeneousSubmodulePiece ℳ (LinearMap.ker f)
  letI := actualHomogeneousKernelDecomposition ℳ 𝒩 f hf
  let hi := actualHomogeneousKernelInclusion_homogeneous ℳ f
  exact actualSubsetCechShortComplex
    (homogeneousCoordinateSubsetDiagramMap 𝒜 ℒ x hx ℳ (LinearMap.ker f).subtype hi k)
    (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf k)
    (fun S => homogeneousCoordinateSubsetDiagramMap_exact 𝒜 ℒ x hx ℳ 𝒩
      (LinearMap.ker f).subtype f hi hf (LinearMap.exact_subtype_ker_map f) k S)

/-- A true homogeneous surjection gives a genuine native short exact sequence of coordinate-cover complexes. -/
theorem actualHomogeneousKernelCechShortComplex_shortExact (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hs : Function.Surjective f) (k : ℤ) :
    (actualHomogeneousKernelCechShortComplex 𝒜 ℳ 𝒩 x hx f hf k).ShortExact := by
  let ℒ := homogeneousSubmodulePiece ℳ (LinearMap.ker f)
  let _ := actualHomogeneousKernelDecomposition ℳ 𝒩 f hf
  let hi := actualHomogeneousKernelInclusion_homogeneous ℳ f
  apply actualSubsetCechShortComplex_shortExact _ _
    (fun S => homogeneousCoordinateSubsetDiagramMap_exact 𝒜 ℒ x hx ℳ 𝒩
      (LinearMap.ker f).subtype f hi hf (LinearMap.exact_subtype_ker_map f) k S)
  · exact fun S => homogeneousCoordinateSubsetDiagramMap_injective 𝒜 ℒ ℳ x hx
      (LinearMap.ker f).subtype hi (LinearMap.ker f).subtype_injective k S
  · exact fun S => homogeneousCoordinateSubsetDiagramMap_surjective 𝒜 ℳ x hx 𝒩 f hf hs k S

end HomogeneousKernelSequence

section FiniteModuleCohomology

variable {K R I : Type u} [CommRing K] [IsNoetherianRing K]
  [CommRing R] [IsNoetherianRing R] [Algebra K R]
  [LinearOrder I] [Fintype I]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)
  (hfree : ∀ (J : Type u) [Fintype J] [DecidableEq J] (δ : J → ℤ) (k : ℤ) (p : ℕ),
    Module.Finite K ((homogeneousCoordinateCechComplex 𝒜
      (finiteShiftedFreePiece 𝒜 δ) x hx k).homology p))

include hfree

/-- Genuine finite shifted free cohomology and actual successive kernels yield finite native
cohomology in every degree within the true finite-cover dimension bound. -/
theorem homogeneousCoordinateCech_homology_finite_dimensionInduction (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
      (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite R M] (k : ℤ) (p : ℕ),
      Fintype.card I ≤ p + n →
      Module.Finite K ((homogeneousCoordinateCechComplex 𝒜 ℳ x hx k).homology p) := by
  classical
  induction n with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    exact subsetCechComplex_homology_finite_of_card_le _ p (by simpa using hp)
  | succ n ih =>
    intro M _ _ _ _ ℳ _ _ _ k p hp
    obtain ⟨s, δ, hg, hs, _⟩ := finiteShiftedGradedPresentation_exists 𝒜 ℳ
    let ℱ := finiteShiftedFreePiece 𝒜 δ
    let f := finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))
    let hf := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ _ hg
    let _ : DirectSum.Decomposition ℱ := finiteShiftedFreeDecomposition 𝒜 δ
    let _ : SetLike.GradedSMul 𝒜 ℱ := finiteShiftedFreeGradedSMul 𝒜 δ
    let ℒ := homogeneousSubmodulePiece ℱ (LinearMap.ker f)
    let _ : DirectSum.Decomposition ℒ := actualHomogeneousKernelDecomposition ℱ ℳ f hf
    have hker : Module.Finite K
        ((homogeneousCoordinateCechComplex 𝒜 ℒ x hx k).homology (p + 1)) :=
      ih (LinearMap.ker f) ℒ k (p + 1) (by omega)
    have hsource : Module.Finite K
        ((homogeneousCoordinateCechComplex 𝒜 ℱ x hx k).homology p) :=
      hfree s δ k p
    let S := actualHomogeneousKernelCechShortComplex 𝒜 ℱ ℳ x hx f hf k
    have : Module.Finite K (S.X₁.homology (p + 1)) := hker
    have : Module.Finite K (S.X₂.homology p) := hsource
    exact nativeCochainHomology_finite_dimensionShift S
      (actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ ℳ x hx f hf hs k) p

/-- Every true finite graded module has finite actual native coordinate-cover cohomology,
when the true finite shifted free modules have finite actual native cohomology. -/
theorem homogeneousCoordinateCech_homology_finite_of_shiftedFree
    (M : Type u) [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite R M] (k : ℤ) (p : ℕ) :
    Module.Finite K ((homogeneousCoordinateCechComplex 𝒜 ℳ x hx k).homology p) :=
  homogeneousCoordinateCech_homology_finite_dimensionInduction 𝒜 x hx hfree
    (Fintype.card I) M ℳ k p (by omega)

end FiniteModuleCohomology

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
