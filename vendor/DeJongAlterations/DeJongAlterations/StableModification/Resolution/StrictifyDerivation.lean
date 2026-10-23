import DeJongAlterations.StableModification.Resolution.StrictifyAlgebra
import DeJongAlterations.Algebra.CompletionRegularityCotangent
import DeJongAlterations.Algebra.NodeGeometricCompletionDerivation
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Enough derivations at a rational point of a smooth algebra

Let `k` be a field, `A` a formally smooth `k`-algebra, `O = A_𝔭` the localization at a prime
`𝔭` whose residue field is `k` (a rational point), and `Ô` the completion of `O`. Every
`k`-derivation `D` of `A` extends to `O` (`localizeDerivation`) and to `Ô`
(`completeDerivation`). These extensions are numerous enough to separate any part of a regular
system of parameters of `Ô`:

* `hasDualDerivations_completion`: for a family `t_1, …, t_n ∈ 𝔪_Ô` with linearly independent
  classes in `𝔪_Ô/𝔪_Ô²`, there are `Ô`-linear combinations `E_i` of extended derivations of `A`
  with `E_i(t_l) = δ_{il}`.

This is the input of the multiplicity strata computation `deltaIdeal_iterate_span_prod`
(file `StrictifyAlgebra`): the derivatives of the local equation of a normal crossings divisor
cut out its strata also after completion (de Jong 1996, 2.4,
`references/dejong96-alterations/tex/page-0006.tex`).

The proof: a `k`-linear form `φ` on `𝔪_O/𝔪_O²` gives the residue derivation
`o ↦ φ(o - [o])` of `O` with values in the residue field (`residueDerivation`); since `Ω_{A/k}`
is projective it lifts to a derivation of `A` (`exists_derivation_residue`). A matrix over the
local ring `Ô` which is the identity modulo `𝔪_Ô` is invertible.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

open Algebra.CompletionRegularityCotangent Algebra.CompletionRegularityBasics

theorem compDer_apply {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
    (f : M →ₗ[A] N) (D : Derivation R A M) (a : A) : f.compDer D a = f (D a) := rfl

section Localize

variable {k A O : Type*} [CommRing k] [CommRing A] [CommRing O] [Algebra k A] [Algebra k O]
  [Algebra A O] [IsScalarTower k A O] (M : Submonoid A) [IsLocalization M O]

/-- The extension of a derivation of `A` to the localization `O`. -/
def localizeDerivation (D : Derivation k A A) : Derivation k O O :=
  ((IsLocalizedModule.lift M (KaehlerDifferential.map k k A O)
      ((Algebra.linearMap A O).comp D.liftKaehlerDifferential)
      (IsLocalizedModule.map_units (Algebra.linearMap A O))).extendScalarsOfIsLocalization
        M O).compDer (KaehlerDifferential.D k O)

@[simp]
theorem localizeDerivation_algebraMap (D : Derivation k A A) (a : A) :
    localizeDerivation M D (algebraMap A O a) = algebraMap A O (D a) := by
  rw [localizeDerivation, compDer_apply, LinearMap.extendScalarsOfIsLocalization_apply',
    ← KaehlerDifferential.map_D k k A O a, IsLocalizedModule.lift_apply]
  simp

omit [Algebra k A] [IsScalarTower k A O] in
include M in
/-- Derivations out of a localization are determined by their values on the original ring. -/
theorem derivation_ext_of_isLocalization {N : Type*} [AddCommGroup N] [Module O N] [Module k N]
    [IsScalarTower k O N] (D₁ D₂ : Derivation k O N)
    (h : ∀ a : A, D₁ (algebraMap A O a) = D₂ (algebraMap A O a)) : D₁ = D₂ := by
  ext x
  obtain ⟨⟨a, u⟩, hx⟩ := IsLocalization.surj M x
  have hs : IsUnit (algebraMap A O u) := IsLocalization.map_units O u
  have key : ∀ D : Derivation k O N, algebraMap A O u • D x =
      D (algebraMap A O a) - x • D (algebraMap A O u) := by
    intro D
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz]
    exact congrArg D hx
  apply hs.smul_left_cancel.mp
  rw [key, key, h, h]

end Localize

section Residue

variable {k O : Type*} [Field k] [CommRing O] [IsLocalRing O] [Algebra k O]
  (hres : Function.Bijective (algebraMap k (ResidueField O)))

/-- The section `κ(O) ≅ k → O` of the residue map. -/
def residueSection : ResidueField O →+* O :=
  (algebraMap k O).comp (RingEquiv.ofBijective _ hres).symm.toRingHom

theorem residue_residueSection (z : ResidueField O) : residue O (residueSection hres z) = z := by
  simp only [residueSection, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply k O (ResidueField O)]
  exact (RingEquiv.ofBijective _ hres).apply_symm_apply z

theorem sub_residueSection_mem (o : O) :
    o - residueSection hres (residue O o) ∈ maximalIdeal O := by
  rw [← residue_eq_zero_iff, map_sub, residue_residueSection, sub_self]

theorem residueSection_algebraMap (c : k) :
    residueSection hres (algebraMap k (ResidueField O) c) = algebraMap k O c := by
  simp only [residueSection, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  congr 1
  exact (RingEquiv.ofBijective _ hres).symm_apply_apply c

/-- The class in `𝔪/𝔪²` of `o - [o]`, where `[o] ∈ k` is the residue of `o`. -/
def centeredCotangent (o : O) : CotangentSpace O :=
  (maximalIdeal O).toCotangent ⟨_, sub_residueSection_mem hres o⟩

theorem centeredCotangent_of_mem (y : maximalIdeal O) :
    centeredCotangent hres (y : O) = (maximalIdeal O).toCotangent y := by
  have : residueSection hres (residue O y) = 0 := by
    rw [(residue_eq_zero_iff (y : O)).mpr y.property, map_zero]
  unfold centeredCotangent
  congr 1
  ext
  simp [this]

theorem centeredCotangent_add (o o' : O) :
    centeredCotangent hres (o + o') = centeredCotangent hres o + centeredCotangent hres o' := by
  unfold centeredCotangent
  rw [← map_add]
  congr 1
  ext
  simp only [map_add, Submodule.coe_add]
  ring

theorem centeredCotangent_smul (c : k) (o : O) :
    centeredCotangent hres (c • o) = algebraMap k O c • centeredCotangent hres o := by
  unfold centeredCotangent
  rw [← map_smul]
  congr 1
  ext
  have h1 : residueSection hres (residue O (algebraMap k O c)) = algebraMap k O c := by
    rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      residueSection_algebraMap]
  simp only [Algebra.smul_def, map_mul, Submodule.coe_smul, Algebra.algebraMap_self,
    RingHom.id_apply, h1]
  ring

theorem smul_cotangent_eq_of_residue_eq {a b : O} (hab : residue O a = residue O b)
    (v : CotangentSpace O) : a • v = b • v := by
  rw [← algebraMap_smul (ResidueField O) a v, ← algebraMap_smul (ResidueField O) b v]
  exact congrArg (· • v) hab

theorem centeredCotangent_mul (o o' : O) :
    centeredCotangent hres (o * o') = o • centeredCotangent hres o' +
      o' • centeredCotangent hres o := by
  set c := residueSection hres (residue O o) with hc
  set c' := residueSection hres (residue O o') with hc'
  have hy : o - c ∈ maximalIdeal O := sub_residueSection_mem hres o
  have hy' : o' - c' ∈ maximalIdeal O := sub_residueSection_mem hres o'
  have hres_c : residue O c = residue O o := residue_residueSection hres _
  have hres_c' : residue O c' = residue O o' := residue_residueSection hres _
  have hdecomp : (⟨o * o' - residueSection hres (residue O (o * o')),
      sub_residueSection_mem hres _⟩ : maximalIdeal O) =
      ⟨(o - c) * (o' - c'), Ideal.mul_mem_left _ _ hy'⟩ + c • ⟨o' - c', hy'⟩ +
        c' • ⟨o - c, hy⟩ := by
    ext
    simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    rw [← hc, ← hc']
    ring
  unfold centeredCotangent
  rw [hdecomp, map_add, map_add, map_smul, map_smul,
    (Ideal.toCotangent_eq_zero _ _).mpr (by rw [pow_two]; exact Ideal.mul_mem_mul hy hy'),
    zero_add, smul_cotangent_eq_of_residue_eq hres_c, smul_cotangent_eq_of_residue_eq hres_c']

theorem centeredCotangent_one : centeredCotangent hres (1 : O) = 0 := by
  unfold centeredCotangent
  rw [← map_zero ((maximalIdeal O).toCotangent)]
  congr 1
  ext
  simp

variable (φ : CotangentSpace O →ₗ[ResidueField O] ResidueField O)

/-- The residue derivation `o ↦ φ(o - [o])` attached to a linear form on `𝔪/𝔪²`. -/
def residueDerivation : Derivation k O (ResidueField O) where
  toFun o := φ (centeredCotangent hres o)
  map_add' o o' := by rw [centeredCotangent_add, map_add]
  map_smul' c o := by
    rw [centeredCotangent_smul, RingHom.id_apply,
      ← algebraMap_smul (ResidueField O) (algebraMap k O c), map_smul, smul_eq_mul,
      Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  map_one_eq_zero' := by
    change φ (centeredCotangent hres 1) = 0
    rw [centeredCotangent_one, map_zero]
  leibniz' o o' := by
    change φ (centeredCotangent hres (o * o')) =
      o • φ (centeredCotangent hres o') + o' • φ (centeredCotangent hres o)
    rw [centeredCotangent_mul, map_add, ← algebraMap_smul (ResidueField O) o,
      ← algebraMap_smul (ResidueField O) o', map_smul, map_smul]
    simp only [smul_eq_mul, Algebra.smul_def]

theorem residueDerivation_apply (o : O) :
    residueDerivation hres φ o = φ (centeredCotangent hres o) := rfl

end Residue

section Lift

variable {k A O : Type*} [Field k] [CommRing A] [CommRing O] [IsLocalRing O] [Algebra k A]
  [Algebra k O] [Algebra A O] [IsScalarTower k A O] (M : Submonoid A) [IsLocalization M O]
  (hres : Function.Bijective (algebraMap k (ResidueField O)))

include hres in
/-- A linear form on `𝔪_O/𝔪_O²` is the residue of the localization of a derivation of `A`,
provided `Ω_{A/k}` is projective. -/
theorem exists_derivation_residue [Module.Projective A Ω[A⁄k]]
    (φ : CotangentSpace O →ₗ[ResidueField O] ResidueField O) :
    ∃ D : Derivation k A A, ∀ y : maximalIdeal O,
      residue O (localizeDerivation M D y) = φ ((maximalIdeal O).toCotangent y) := by
  let ρ := residueDerivation hres φ
  let ρA : Derivation k A (ResidueField O) := ρ.compAlgebraMap A
  let π : A →ₗ[A] ResidueField O := Algebra.linearMap A (ResidueField O)
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨c, rfl⟩ := hres.2 z
    refine ⟨algebraMap k A c, ?_⟩
    simp only [π, Algebra.linearMap_apply]
    rw [← IsScalarTower.algebraMap_apply]
  obtain ⟨h, hh⟩ := Module.projective_lifting_property π ρA.liftKaehlerDifferential hπ
  refine ⟨h.compDer (KaehlerDifferential.D k A), ?_⟩
  have heq : (Algebra.linearMap O (ResidueField O)).compDer
      (localizeDerivation M (h.compDer (KaehlerDifferential.D k A))) = ρ := by
    apply derivation_ext_of_isLocalization M
    intro a
    have := congrArg (fun f ↦ f (KaehlerDifferential.D k A a)) hh
    simp only [LinearMap.coe_comp, Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D,
      π, Algebra.linearMap_apply] at this
    simp only [compDer_apply, localizeDerivation_algebraMap, Algebra.linearMap_apply,
      compDer_apply]
    rw [← IsScalarTower.algebraMap_apply, this]
    rfl
  intro y
  have := congrArg (fun D ↦ D (y : O)) heq
  simp only [compDer_apply, Algebra.linearMap_apply] at this
  rw [← centeredCotangent_of_mem hres y]
  exact this

end Lift

section Complete

variable {k O : Type*} [Field k] [CommRing O] [IsLocalRing O] [Algebra k O]

/-- The extension of a derivation of the local ring `O` to its completion. -/
def completeDerivation (D : Derivation k O O) :
    Derivation k (AdicCompletion (maximalIdeal O) O) (AdicCompletion (maximalIdeal O) O) :=
  Algebra.NodeGeometricCompletionDerivation.completedDifferential (maximalIdeal O) D

@[simp]
theorem completeDerivation_algebraMap (D : Derivation k O O) (o : O) :
    completeDerivation D (algebraMap O (AdicCompletion (maximalIdeal O) O) o) =
      algebraMap O (AdicCompletion (maximalIdeal O) O) (D o) :=
  Algebra.NodeGeometricCompletionDerivation.completedDifferential_algebraMap _ D o

end Complete

/-- A derivation maps `I²` into `I`. -/
theorem derivation_mem_of_mem_sq {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (I : Ideal R) {r : R} (hr : r ∈ I ^ 2) : D r ∈ I := by
  rw [pow_two] at hr
  refine Submodule.mul_induction_on hr ?_ ?_
  · intro a ha b hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  · intro a b ha hb
    rw [map_add]
    exact Ideal.add_mem _ ha hb

/-- Evaluation of a finite linear combination of derivations. -/
theorem derivation_sum_smul_apply {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type*} (s : Finset ι) (c : ι → R) (D : ι → Derivation K R R) (x : R) :
    (∑ j ∈ s, c j • D j) x = ∑ j ∈ s, c j * D j x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Derivation.add_apply, Derivation.smul_apply,
      ih, smul_eq_mul]

section Dual

variable {k A O : Type*} [Field k] [CommRing A] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Algebra k A] [Algebra k O] [Algebra A O] [IsScalarTower k A O] (M : Submonoid A)
  [IsLocalization M O] (hres : Function.Bijective (algebraMap k (ResidueField O)))

local notation "Ô" => AdicCompletion (maximalIdeal O) O

/-- The extensions to the completion of all derivations of `A`. -/
def completedDerivations : Set (Derivation k Ô Ô) :=
  Set.range fun D : Derivation k A A ↦ completeDerivation (localizeDerivation M D)

/-- A family in `𝔪_Ô` with independent cotangent classes lifts to a family in `𝔪_O` with
independent cotangent classes, congruent modulo `𝔪_Ô²`. -/
theorem exists_lift_cotangent {ι : Type*} (t : ι → maximalIdeal Ô)
    (hli : LinearIndependent (ResidueField Ô) fun i ↦ (maximalIdeal Ô).toCotangent (t i)) :
    ∃ y : ι → maximalIdeal O,
      LinearIndependent (ResidueField O) (fun i ↦ (maximalIdeal O).toCotangent (y i)) ∧
      ∀ i, (t i : Ô) - algebraMap O Ô (y i) ∈ maximalIdeal Ô ^ 2 := by
  have hsurj : ∀ i, ∃ y : maximalIdeal O,
      cotangentMap O ((maximalIdeal O).toCotangent y) = (maximalIdeal Ô).toCotangent (t i) := by
    intro i
    obtain ⟨v, hv⟩ := cotangentMap_surjective O ((maximalIdeal Ô).toCotangent (t i))
    obtain ⟨y, rfl⟩ := (maximalIdeal O).toCotangent_surjective v
    exact ⟨y, hv⟩
  choose y hy using hsurj
  refine ⟨y, ?_, fun i ↦ ?_⟩
  · rw [linearIndependent_iff'] at hli ⊢
    intro s g hg i hi
    have h0 := congrArg (cotangentMap O) hg
    rw [map_zero, map_sum] at h0
    simp only [cotangentMap_residue_smul, hy] at h0
    have := hli s (fun j ↦ ResidueField.map (algebraMap O Ô) (g j)) h0 i hi
    exact (ResidueField.map (algebraMap O Ô)).injective (by rw [this, map_zero])
  · have h := hy i
    rw [cotangentMap_toCotangent, Ideal.toCotangent_eq] at h
    have := (maximalIdeal Ô ^ 2).neg_mem h
    simpa using this

include hres in
/-- **Enough derivations.** For a family `t` in `𝔪_Ô` with independent cotangent classes, the
`Ô`-span of the extended derivations of `A` contains derivations `E_i` with `E_i(t_l) = δ_{il}`.
-/
theorem hasDualDerivations_completion [Module.Projective A Ω[A⁄k]] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → maximalIdeal Ô)
    (hli : LinearIndependent (ResidueField Ô) fun i ↦ (maximalIdeal Ô).toCotangent (t i)) :
    HasDualDerivations (completedDerivations (k := k) M) (fun i ↦ (t i : Ô)) Finset.univ := by
  obtain ⟨y, hyli, hty⟩ := exists_lift_cotangent t hli
  -- dual forms on the cotangent space of `O`
  have hφ : ∀ i, ∃ φ : CotangentSpace O →ₗ[ResidueField O] ResidueField O,
      ∀ l, φ ((maximalIdeal O).toCotangent (y l)) = if l = i then 1 else 0 := by
    intro i
    let B := Module.Basis.span hyli
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.coord i)
    refine ⟨g, fun l ↦ ?_⟩
    have hBl : (B l : CotangentSpace O) = (maximalIdeal O).toCotangent (y l) := by
      rw [Module.Basis.span_apply]
    rw [← hBl]
    have := LinearMap.congr_fun hg (B l)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  choose φ hφ using hφ
  have hD : ∀ i, ∃ D : Derivation k A A, ∀ z : maximalIdeal O,
      residue O (localizeDerivation M D z) = φ i ((maximalIdeal O).toCotangent z) :=
    fun i ↦ exists_derivation_residue M hres (φ i)
  choose D hD using hD
  let Dh : ι → Derivation k Ô Ô := fun i ↦ completeDerivation (localizeDerivation M (D i))
  let N : Matrix ι ι Ô := fun i l ↦ Dh i (t l)
  have hN : ∀ i l, residue Ô (N i l) = if l = i then 1 else 0 := by
    intro i l
    have hsub : Dh i (t l) - Dh i (algebraMap O Ô (y l)) ∈ maximalIdeal Ô := by
      rw [← map_sub]
      exact derivation_mem_of_mem_sq (Dh i) _ (hty l)
    have h1 : residue Ô (N i l) = residue Ô (Dh i (algebraMap O Ô (y l))) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hsub
    rw [h1]
    simp only [Dh, completeDerivation_algebraMap]
    rw [← ResidueField.map_residue, hD i (y l), hφ i l]
    split_ifs <;> simp
  have hdet : IsUnit N.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← residue_eq_zero_iff, RingHom.map_det]
    have : (residue Ô).mapMatrix N = 1 := by
      ext i l
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hN, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
    rw [this, Matrix.det_one]
    exact one_ne_zero
  intro i _
  refine ⟨∑ j, (N⁻¹ i j) • Dh j, ?_, fun l _ ↦ ?_⟩
  · exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨D j, rfl⟩)
  · have hinv : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N hdet
    have := congrFun (congrFun hinv i) l
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [derivation_sum_smul_apply, this]
    exact if_congr eq_comm rfl rfl

end Dual

end DeJongAlterations.StableModification.Resolution.Strictify
