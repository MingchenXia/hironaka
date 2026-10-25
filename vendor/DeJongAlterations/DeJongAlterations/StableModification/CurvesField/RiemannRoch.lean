/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.CohomologyTwistLocal
import DeJongAlterations.StableModification.Cohomology.CechAcyclic

/-!
# Weak Riemann–Roch, Serre vanishing and global generation for `F(mD)`

Let `Y` be a scheme covered by two opens `U`, `V`, let `f ∈ Γ(V, 𝒪_Y)` be a unit on `U ∩ V` and
let `D = V(f) ⊆ V`; `D` is disjoint from `U`. For a module `F` on `Y` the twist
`F(mD) = divisorTwist F U V hf m` (`m ∈ ℤ`) is the twist of `F` along `(U, V)` by `fᵐ`
(`CohomologyTwist`): it is `F` on `U`, and on `V` its sections are `f⁻ᵐ` times sections of `F`.
For an effective Cartier divisor `D = Σ nᵢ pᵢ` on a curve, cut out by `f` in an affine
neighbourhood `V` of its support, and `U` an affine open with `U ∩ D = ∅`, `U ∩ V ⊆ D(f)`, this is
the sheaf `F ⊗ 𝒪(mD)` of Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Prop. 4.4.6 (`references/temkin10-stable-modification/source/semi-stable.tex`,
lines 3204–3225, `𝒪(m Σ pᵢ)`). Blueprint: `sm-curves-fields-cohomology.tex`.

All cohomology here is Čech cohomology for the cover `(U, V)` (`cechCohomology … (pairCover U V)`);
when `U`, `V`, `U ∩ V` are affine and the module is quasi-coherent this is `H^p(Y, -)`
(`cohomologyPairOneEquiv`), and for `F` itself this is recorded in `cohomologyOneEquivH1`.

## Main results

* `weak_riemann_roch` (blueprint `thm:sm-weak-rr`): over a field `K`, if `f` is a nonzerodivisor
  on `Γ(V, F)` and `Ȟ⁰(F)`, `Ȟ¹(F)`, `Γ(V, F) ⧸ f Γ(V, F)` are finite-dimensional, then
  `χ(F(mD)) = χ(F) + m · dim_K Γ(V, F) ⧸ f Γ(V, F)` for every `m ∈ ℤ`. For `F = 𝒪_Y` the number
  `deg D = dim_K Γ(V, 𝒪) ⧸ (f)` is the degree of `D` (for `D` a sum of `k`-points with
  multiplicities `nᵢ`, `Σ nᵢ`).
* `serre_vanishing_of_limit`, `serre_vanishing` (blueprint `lem:sm-serre-vanishing-curve`): if
  `Ȟ¹(F)` is finitely generated and `Y ∖ D` has vanishing `Ȟ¹` in the sense of `IsTwistLimit`
  (automatic when `U ∩ V = D(f)` in the affine `V`, i.e. `U = Y ∖ D` is affine, and `F` is
  quasi-coherent: `isTwistLimit_of_basicOpen`), then `Ȟ¹(F(mD)) = 0` for `m ≫ 0`.
* `exists_global_section_of_vanishing`, `exists_global_section_field` (blueprint
  `lem:sm-global-generation`, along `D`): every class in `Γ(V, F) ⧸ f Γ(V, F)` is the `V`-component
  of a global section of `F((m+1)D)` for `m ≫ 0`; over a field this needs no condition on
  `Y ∖ D`. For `F = 𝒪_Y` and the class of `1` this is a rational function with poles of exact
  order `(m+1) nᵢ` at the points of `D` (Temkin's `h_s`, line 3221).
* `exists_global_section_extending` (global generation on `U`): every section of `F` over `U`
  extends to a global section of `F(mD)` for `m ≫ 0`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

variable {Y : Scheme.{u}} (F : Y.Modules) (U V : Y.Opens) {R : Type u} [CommRing R]
  (c : R →+* Γ(Y, ⊤)) {f : Γ(Y, V)}
  (hf : IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op f))

omit [CommRing R] in
/-- A section of `F` as an element of `Γ(F, W)` (the identity, used to fix elaboration). -/
abbrev secVal {R : Type u} [CommRing R] {c : R →+* Γ(Y, ⊤)} {W : Y.Opens}
    (s : sectionsModuleCat F c W le_top) : Γ(F, W) := s

/-- The twist `F(mD)` of `F` by the divisor `D = V(f)`: the twist along `(U, V)` by `fᵐ`
(blueprint `def:sm-divisor-twist`). -/
def divisorTwist (m : ℤ) : Y.Modules := twist F U V (hf.unit ^ m)

/-- Multiplication by `f|_{U ∩ V}` on `Γ(U ∩ V, F)`, a linear automorphism. -/
def fEquiv : sectionsModuleCat F c (U ⊓ V) le_top ≃ₗ[R] sectionsModuleCat F c (U ⊓ V) le_top where
  __ := smulLin F c (hf.unit : Γ(Y, U ⊓ V))
  invFun := smulLin F c ((hf.unit⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V))
  left_inv s := (fun x : Γ(F, U ⊓ V) => show ((hf.unit⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V)) •
      ((hf.unit : Γ(Y, U ⊓ V)) • x) = x by rw [smul_smul, Units.inv_mul, one_smul]) s
  right_inv s := (fun x : Γ(F, U ⊓ V) => show (hf.unit : Γ(Y, U ⊓ V)) •
      (((hf.unit⁻¹ : Γ(Y, U ⊓ V)ˣ) : Γ(Y, U ⊓ V)) • x) = x by
    rw [smul_smul, Units.mul_inv, one_smul]) s

variable (f) in
/-- Multiplication by `f` on `Γ(V, F)`. -/
abbrev fMul : sectionsModuleCat F c V le_top →ₗ[R] sectionsModuleCat F c V le_top :=
  smulLin F c f

lemma fEquiv_apply (s : sectionsModuleCat F c (U ⊓ V) le_top) :
    fEquiv F U V c hf s = (hf.unit : Γ(Y, U ⊓ V)) • secVal F s :=
  rfl

lemma resVU_fMul :
    resVU F U V c ∘ₗ fMul F V c f = (fEquiv F U V c hf).toLinearMap ∘ₗ resVU F U V c := by
  apply LinearMap.ext
  intro s
  exact (fun x : Γ(F, V) => show F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
      (f • x) = (hf.unit : Γ(Y, U ⊓ V)) • F.presheaf.map (homOfLE inf_le_right).op x by
    rw [Scheme.Modules.map_smul, IsUnit.unit_spec]) s

/-- The family of twisting maps: multiplication by `fᵐ` on `Γ(U ∩ V, F)`. -/
abbrev twistFamily (m : ℤ) :
    sectionsModuleCat F c (U ⊓ V) le_top →ₗ[R] sectionsModuleCat F c (U ⊓ V) le_top :=
  smulLin F c (((hf.unit ^ m : Γ(Y, U ⊓ V)ˣ)) : Γ(Y, U ⊓ V))

lemma twistFamily_succ (m : ℤ) :
    twistFamily F U V c hf (m + 1) =
      (fEquiv F U V c hf).toLinearMap ∘ₗ twistFamily F U V c hf m := by
  apply LinearMap.ext
  intro s
  exact (fun x : Γ(F, U ⊓ V) => show (((hf.unit ^ (m + 1) : Γ(Y, U ⊓ V)ˣ)) : Γ(Y, U ⊓ V)) • x =
      (hf.unit : Γ(Y, U ⊓ V)) • ((((hf.unit ^ m : Γ(Y, U ⊓ V)ˣ)) : Γ(Y, U ⊓ V)) • x) by
    rw [smul_smul, zpow_add_one, mul_comm, Units.val_mul]) s

lemma twistFamily_zero : twistFamily F U V c hf 0 = smulLin F c 1 := by
  simp [twistFamily]

/-- `Ȟ¹((U, V), F(mD))` as the cokernel of the twisted differential. -/
def cechDivisorTwistOneEquiv (m : ℤ) :
    cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m) :=
  cechTwistOneEquiv F U V (hf.unit ^ m) c

/-- `Ȟ⁰((U, V), F(mD))` as the kernel of the twisted differential. -/
def cechDivisorTwistZeroEquiv (m : ℤ) :
    cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m) :=
  cechTwistZeroEquiv F U V (hf.unit ^ m) c

/-- Global sections of `F(mD)`: pairs `(a, b)`, `a ∈ Γ(U, F)`, `b ∈ Γ(V, F)`, with
`b| = fᵐ a|` on `U ∩ V`. -/
def divisorTwistGlobalEquiv (m : ℤ) :
    sectionsModuleCat (divisorTwist F U V hf m) c ⊤ le_top ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m) :=
  twistGlobalEquiv F U V (hf.unit ^ m) c

/-- `Ȟ¹((U, V), F)` in the notation of the twisted complexes (`m = 0`). -/
def cechOneEquivTwistZero :
    cechCohomology F (pairCover U V) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0) :=
  (cechOneEquivH1 F U V c).trans (Submodule.quotEquivOfEq _ _ (by rw [twistFamily_zero]))

/-- `Ȟ⁰((U, V), F)` in the notation of the twisted complexes (`m = 0`). -/
def cechZeroEquivTwistZero :
    cechCohomology F (pairCover U V) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0) :=
  (cechZeroEquivH0 F U V c).trans (LinearEquiv.ofEq _ _ (by rw [twistFamily_zero]))

section WeakRR

variable {K : Type u} [Field K] (c : K →+* Γ(Y, ⊤))
  [FiniteDimensional K (cechCohomology F (pairCover U V) c 0)]
  [FiniteDimensional K (cechCohomology F (pairCover U V) c 1)]
  [FiniteDimensional K (sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f))]
  (hinj : Function.Injective (fMul F V c f))

include hinj

/-- The cohomology of every `F(mD)` is finite-dimensional. -/
theorem finiteDimensional_divisorTwist (m : ℤ) :
    FiniteDimensional K (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 0) ∧
      FiniteDimensional K (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1) := by
  have h0 : FiniteDimensional K (H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechZeroEquivTwistZero F U V c hf)
  have h1 : FiniteDimensional K (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechOneEquivTwistZero F U V c hf)
  obtain ⟨g0, g1⟩ := finiteDimensional_family (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) hinj
    (twistFamily F U V c hf) (twistFamily_succ F U V c hf) m
  exact ⟨Module.Finite.equiv (cechDivisorTwistZeroEquiv F U V c hf m).symm,
    Module.Finite.equiv (cechDivisorTwistOneEquiv F U V c hf m).symm⟩

/-- **Weak Riemann–Roch** (blueprint `thm:sm-weak-rr`):
`χ(F(mD)) = χ(F) + m · dim_K Γ(V, F) ⧸ f Γ(V, F)`. -/
theorem weak_riemann_roch (m : ℤ) :
    (Module.finrank K (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 0) : ℤ) -
        Module.finrank K (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1) =
      (Module.finrank K (cechCohomology F (pairCover U V) c 0) : ℤ) -
          Module.finrank K (cechCohomology F (pairCover U V) c 1) +
        m * Module.finrank K
          (sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f)) := by
  have h0 : FiniteDimensional K (H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechZeroEquivTwistZero F U V c hf)
  have h1 : FiniteDimensional K (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechOneEquivTwistZero F U V c hf)
  have key := euler_family (resUV F U V c) (resVU F U V c) (fEquiv F U V c hf) (fMul F V c f)
    (resVU_fMul F U V c hf) hinj (twistFamily F U V c hf) (twistFamily_succ F U V c hf) m
  unfold euler at key
  rw [LinearEquiv.finrank_eq (cechDivisorTwistZeroEquiv F U V c hf m),
    LinearEquiv.finrank_eq (cechDivisorTwistOneEquiv F U V c hf m),
    LinearEquiv.finrank_eq (cechZeroEquivTwistZero F U V c hf),
    LinearEquiv.finrank_eq (cechOneEquivTwistZero F U V c hf)]
  exact key

end WeakRR

section Vanishing

/-- The condition `Ȟ¹(Y ∖ D, F) = 0` in the form used for Serre vanishing: every section over
`U ∩ V`, multiplied by a suitable power `fⁿ`, is a coboundary `b| - fⁿ a|` of `F(nD)`. -/
def IsTwistLimit : Prop :=
  ∀ w : sectionsModuleCat F c (U ⊓ V) le_top, ∃ n : ℕ, (fEquiv F U V c hf)^[n] w ∈
    LinearMap.range (twistDiff (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf n))

/-- **Serre vanishing** (blueprint `lem:sm-serre-vanishing-curve`, general form): if `Ȟ¹(F)` is a
finitely generated `R`-module and `Ȟ¹(Y ∖ D, F) = 0` (`IsTwistLimit`), then `Ȟ¹(F(mD)) = 0` for
all `m ≫ 0`. -/
theorem serre_vanishing_of_limit [Module.Finite R (cechCohomology F (pairCover U V) c 1)]
    (hlim : IsTwistLimit F U V c hf) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Limits.IsZero (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1) := by
  have : Module.Finite R (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechOneEquivTwistZero F U V c hf)
  obtain ⟨m₀, hm₀⟩ := exists_forall_subsingleton_H1_of_limit (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) (twistFamily F U V c hf)
    (twistFamily_succ F U V c hf) hlim
  refine ⟨m₀, fun m hm => ?_⟩
  have := hm₀ m hm
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (cechDivisorTwistOneEquiv F U V c hf m).injective.subsingleton

lemma fEquiv_iterate (n : ℕ) (w : sectionsModuleCat F c (U ⊓ V) le_top) :
    (fEquiv F U V c hf)^[n] w =
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (f ^ n) • secVal F w := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, map_one]
    exact ((fun x : Γ(F, U ⊓ V) => (one_smul Γ(Y, U ⊓ V) x).symm) w)
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact (fun x : Γ(F, U ⊓ V) => show (hf.unit : Γ(Y, U ⊓ V)) •
        (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (f ^ n) • x) =
        Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (f ^ (n + 1)) • x by
      rw [smul_smul, IsUnit.unit_spec, pow_succ', map_mul]) w

/-- On an affine `V` with `U ∩ V = D(f)`, every section of a quasi-coherent `F` over `U ∩ V` is
`f⁻ⁿ` times the restriction of a section over `V`. -/
lemma exists_pow_smul_eq_res [F.IsQuasicoherent] (hV : IsAffineOpen V)
    (hUV : U ⊓ V = Y.basicOpen f) (w : Γ(F, U ⊓ V)) :
    ∃ (n : ℕ) (x : Γ(F, V)), Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (f ^ n) • w =
      F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x := by
  let := Module.compHom Γ(F, Y.basicOpen f) (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom
  have hloc := isLocalizedModule_restrictLinearNative F hV f
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (r := f)
    (restrictLinearNative F (Y.basicOpen_le f)) (F.presheaf.map (homOfLE hUV.ge).op w)
  refine ⟨n, x, ?_⟩
  change Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (f ^ n) •
      F.presheaf.map (homOfLE hUV.ge).op w = F.presheaf.map (homOfLE (Y.basicOpen_le f)).op x at hx
  have e := congrArg (F.presheaf.map (homOfLE hUV.le).op) hx
  rw [Scheme.Modules.map_smul, presheaf_map_map_self, ringMap_ringMap,
    presheaf_map_map F _ _ inf_le_right] at e
  exact e

/-- If `U ∩ V = D(f)` in the affine `V` (so `U = Y ∖ D`) and `F` is quasi-coherent, the limit
condition holds. -/
theorem isTwistLimit_of_basicOpen [F.IsQuasicoherent] (hV : IsAffineOpen V)
    (hUV : U ⊓ V = Y.basicOpen f) : IsTwistLimit F U V c hf := by
  intro w
  obtain ⟨n, x, hx⟩ := exists_pow_smul_eq_res F U V hV hUV w
  refine ⟨n, (0, x), ?_⟩
  rw [twistDiff_apply, map_zero, map_zero, sub_zero, fEquiv_iterate]
  exact hx.symm

/-- **Serre vanishing** (blueprint `lem:sm-serre-vanishing-curve`): if `V` is affine,
`U ∩ V = D(f)` (that is, `U = Y ∖ D`), `F` is quasi-coherent and `Ȟ¹(F)` is finitely generated,
then `Ȟ¹(F(mD)) = 0` for all `m ≫ 0`. -/
theorem serre_vanishing [F.IsQuasicoherent] [Module.Finite R (cechCohomology F (pairCover U V) c 1)]
    (hV : IsAffineOpen V) (hUV : U ⊓ V = Y.basicOpen f) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Limits.IsZero (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1) :=
  serre_vanishing_of_limit F U V c hf (isTwistLimit_of_basicOpen F U V c hf hV hUV)

end Vanishing

section Generation

/-- **Global generation along `D`** (blueprint `lem:sm-global-generation`): if
`Ȟ¹(F(mD)) = 0`, every class `x ∈ Γ(V, F) ⧸ f Γ(V, F)` is the class of the `V`-component of a
global section of `F((m+1)D)`. -/
theorem exists_global_section_of_vanishing (m : ℤ)
    (hm : Limits.IsZero (cechCohomology (divisorTwist F U V hf m) (pairCover U V) c 1))
    (x : sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f)) :
    ∃ s : sectionsModuleCat (divisorTwist F U V hf (m + 1)) c ⊤ le_top,
      (LinearMap.range (fMul F V c f)).mkQ
        ((divisorTwistGlobalEquiv F U V c hf (m + 1) s).1.2) = x := by
  have : Subsingleton (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m)) := by
    rw [ModuleCat.isZero_iff_subsingleton] at hm
    exact (cechDivisorTwistOneEquiv F U V c hf m).symm.injective.subsingleton
  obtain ⟨p, hp, hpx⟩ := stepQ_surjective_family (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) (twistFamily F U V c hf)
    (twistFamily_succ F U V c hf) m x
  refine ⟨(divisorTwistGlobalEquiv F U V c hf (m + 1)).symm ⟨p, hp⟩, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hpx

/-- **Global generation along `D`, Serre form**: under the hypotheses of `serre_vanishing`, for
`m ≫ 0` every class of `Γ(V, F) ⧸ f Γ(V, F)` is the class of the `V`-component of a global section
of `F((m+1)D)`. -/
theorem exists_global_section [F.IsQuasicoherent]
    [Module.Finite R (cechCohomology F (pairCover U V) c 1)]
    (hV : IsAffineOpen V) (hUV : U ⊓ V = Y.basicOpen f) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ x : sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f),
      ∃ s : sectionsModuleCat (divisorTwist F U V hf (m + 1)) c ⊤ le_top,
        (LinearMap.range (fMul F V c f)).mkQ
          ((divisorTwistGlobalEquiv F U V c hf (m + 1) s).1.2) = x := by
  obtain ⟨m₀, hm₀⟩ := serre_vanishing F U V c hf hV hUV
  exact ⟨m₀, fun m hm x => exists_global_section_of_vanishing F U V c hf m (hm₀ m hm) x⟩

/-- **Global generation on `U`**: under the hypotheses of `serre_vanishing` (without finiteness),
every section `a` of `F` over `U` is the `U`-component of a global section of `F(mD)` for
`m ≫ 0`. -/
theorem exists_global_section_extending [F.IsQuasicoherent] (hV : IsAffineOpen V)
    (hUV : U ⊓ V = Y.basicOpen f) (a : sectionsModuleCat F c U le_top) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ s : sectionsModuleCat (divisorTwist F U V hf m) c ⊤ le_top,
      (divisorTwistGlobalEquiv F U V c hf m s).1.1 = a := by
  have hlim : ∀ w : sectionsModuleCat F c (U ⊓ V) le_top, ∃ n : ℕ,
      (fEquiv F U V c hf)^[n] w ∈ LinearMap.range (resVU F U V c) := by
    intro w
    obtain ⟨n, x, hx⟩ := exists_pow_smul_eq_res F U V hV hUV w
    exact ⟨n, x, by rw [fEquiv_iterate]; exact hx.symm⟩
  obtain ⟨m₀, hm₀⟩ := exists_mem_H0_of_limit (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) (twistFamily F U V c hf)
    (twistFamily_succ F U V c hf) hlim a
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨b, hb⟩ := hm₀ m hm
  refine ⟨(divisorTwistGlobalEquiv F U V c hf m).symm ⟨(a, b), hb⟩, ?_⟩
  rw [LinearEquiv.apply_symm_apply]

section Field

variable {K : Type u} [Field K] (c : K →+* Γ(Y, ⊤))
  [FiniteDimensional K (cechCohomology F (pairCover U V) c 0)]
  [FiniteDimensional K (cechCohomology F (pairCover U V) c 1)]
  [FiniteDimensional K (sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f))]
  (hinj : Function.Injective (fMul F V c f))

include hinj in
/-- **Global generation along `D` over a field** (no condition on `Y ∖ D`): for `m ≫ 0` every
class of `Γ(V, F) ⧸ f Γ(V, F)` is the class of the `V`-component of a global section of
`F((m+1)D)`. For `F = 𝒪_Y` and the class of `1`, the section is a rational function, regular
off `D`, whose product with `f^{m+1}` is a unit along `D`: its poles are exactly `(m+1)D`. -/
theorem exists_global_section_field :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ x : sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f),
      ∃ s : sectionsModuleCat (divisorTwist F U V hf (m + 1)) c ⊤ le_top,
        (LinearMap.range (fMul F V c f)).mkQ
          ((divisorTwistGlobalEquiv F U V c hf (m + 1) s).1.2) = x := by
  have h0 : FiniteDimensional K (H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechZeroEquivTwistZero F U V c hf)
  have h1 : FiniteDimensional K (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cechOneEquivTwistZero F U V c hf)
  obtain ⟨m₀, hm₀⟩ := exists_forall_surjective_family (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) hinj (twistFamily F U V c hf)
    (twistFamily_succ F U V c hf)
  refine ⟨m₀, fun m hm x => ?_⟩
  obtain ⟨p, hp, hpx⟩ := hm₀ m hm x
  refine ⟨(divisorTwistGlobalEquiv F U V c hf ((m : ℤ) + 1)).symm ⟨p, hp⟩, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hpx

end Field

end Generation

section CoverFree

/-! ### The same statements for the cohomology `H^p(Y, -)` of the Čech library

When `U`, `V`, `U ∩ V` are affine, `Y` is quasi-compact with affine diagonal and `F` is
quasi-coherent, the twists are quasi-coherent (`twist_isQuasicoherent`) and `H^p(Y, -)` is computed
by the cover `(U, V)`. -/

variable [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  [F.IsQuasicoherent] (h : U ⊔ V = ⊤) (h₀ : IsAffineOpen U) (h₁ : IsAffineOpen V)
  (h₀₁ : IsAffineOpen (U ⊓ V))

/-- `H¹(Y, F(mD))` as the cokernel of the twisted differential. -/
def cohomologyDivisorTwistOneEquiv (m : ℤ) :
    cohomology (divisorTwist F U V hf m) c 1 ≃ₗ[R]
      H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m) :=
  cohomologyTwistOneEquiv F U V (hf.unit ^ m) c h h₀ h₁ h₀₁

/-- `H⁰(Y, F(mD))` as the kernel of the twisted differential. -/
def cohomologyDivisorTwistZeroEquiv (m : ℤ) :
    cohomology (divisorTwist F U V hf m) c 0 ≃ₗ[R]
      H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf m) :=
  cohomologyTwistZeroEquiv F U V (hf.unit ^ m) c h h₀ h₁ h₀₁

/-- `H¹(Y, F)` in the notation of the twisted complexes. -/
def cohomologyOneEquivTwistZero :
    cohomology F c 1 ≃ₗ[R] H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0) :=
  (cohomologyOneEquivH1 F U V c h h₀ h₁ h₀₁).trans
    (Submodule.quotEquivOfEq _ _ (by rw [twistFamily_zero]))

/-- `H⁰(Y, F)` in the notation of the twisted complexes. -/
def cohomologyZeroEquivTwistZero :
    cohomology F c 0 ≃ₗ[R] H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0) :=
  (cohomologyZeroEquivH0 F U V c h h₀ h₁ h₀₁).trans
    (LinearEquiv.ofEq _ _ (by rw [twistFamily_zero]))

include h h₀ h₁ h₀₁ in
/-- `H^p(Y, F(mD)) = 0` for `p ≥ 2`. -/
theorem isZero_cohomology_divisorTwist (m : ℤ) (p : ℕ) (hp : 2 ≤ p) :
    Limits.IsZero (cohomology (divisorTwist F U V hf m) c p) :=
  isZero_cohomology_twist F U V (hf.unit ^ m) c h h₀ h₁ h₀₁ p hp

include h h₀ h₁ h₀₁ in
/-- **Serre vanishing** (blueprint `lem:sm-serre-vanishing-curve`), cover-free: if
`U ∩ V = D(f)` in `V` (so `U = Y ∖ D` is affine) and `H¹(Y, F)` is finitely generated, then
`H¹(Y, F(mD)) = 0` for `m ≫ 0`. -/
theorem serre_vanishing_cohomology [Module.Finite R (cohomology F c 1)]
    (hUV : U ⊓ V = Y.basicOpen f) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Limits.IsZero (cohomology (divisorTwist F U V hf m) c 1) := by
  have : Module.Finite R (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cohomologyOneEquivTwistZero F U V c hf h h₀ h₁ h₀₁)
  obtain ⟨m₀, hm₀⟩ := exists_forall_subsingleton_H1_of_limit (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) (twistFamily F U V c hf)
    (twistFamily_succ F U V c hf) (isTwistLimit_of_basicOpen F U V c hf h₁ hUV)
  refine ⟨m₀, fun m hm => ?_⟩
  have := hm₀ m hm
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (cohomologyDivisorTwistOneEquiv F U V c hf h h₀ h₁ h₀₁ m).injective.subsingleton

section Field

variable {K : Type u} [Field K] (c : K →+* Γ(Y, ⊤))
  [FiniteDimensional K (cohomology F c 0)] [FiniteDimensional K (cohomology F c 1)]
  [FiniteDimensional K (sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f))]
  (hinj : Function.Injective (fMul F V c f))

include h h₀ h₁ h₀₁ hinj in
/-- **Weak Riemann–Roch** (blueprint `thm:sm-weak-rr`), cover-free:
`χ(Y, F(mD)) = χ(Y, F) + m · dim_K Γ(V, F) ⧸ f Γ(V, F)` for all `m ∈ ℤ`. -/
theorem weak_riemann_roch_cohomology (m : ℤ) :
    (Module.finrank K (cohomology (divisorTwist F U V hf m) c 0) : ℤ) -
        Module.finrank K (cohomology (divisorTwist F U V hf m) c 1) =
      (Module.finrank K (cohomology F c 0) : ℤ) - Module.finrank K (cohomology F c 1) +
        m * Module.finrank K
          (sectionsModuleCat F c V le_top ⧸ LinearMap.range (fMul F V c f)) := by
  have h0 : FiniteDimensional K (H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cohomologyZeroEquivTwistZero F U V c hf h h₀ h₁ h₀₁)
  have h1 : FiniteDimensional K (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cohomologyOneEquivTwistZero F U V c hf h h₀ h₁ h₀₁)
  have key := euler_family (resUV F U V c) (resVU F U V c) (fEquiv F U V c hf) (fMul F V c f)
    (resVU_fMul F U V c hf) hinj (twistFamily F U V c hf) (twistFamily_succ F U V c hf) m
  unfold euler at key
  rw [LinearEquiv.finrank_eq (cohomologyDivisorTwistZeroEquiv F U V c hf h h₀ h₁ h₀₁ m),
    LinearEquiv.finrank_eq (cohomologyDivisorTwistOneEquiv F U V c hf h h₀ h₁ h₀₁ m),
    LinearEquiv.finrank_eq (cohomologyZeroEquivTwistZero F U V c hf h h₀ h₁ h₀₁),
    LinearEquiv.finrank_eq (cohomologyOneEquivTwistZero F U V c hf h h₀ h₁ h₀₁)]
  exact key

include h h₀ h₁ h₀₁ hinj in
/-- The cohomology of every `F(mD)` is finite-dimensional (cover-free). -/
theorem finiteDimensional_cohomology_divisorTwist (m : ℤ) :
    FiniteDimensional K (cohomology (divisorTwist F U V hf m) c 0) ∧
      FiniteDimensional K (cohomology (divisorTwist F U V hf m) c 1) := by
  have h0 : FiniteDimensional K (H0 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cohomologyZeroEquivTwistZero F U V c hf h h₀ h₁ h₀₁)
  have h1 : FiniteDimensional K (H1 (resUV F U V c) (resVU F U V c) (twistFamily F U V c hf 0)) :=
    Module.Finite.equiv (cohomologyOneEquivTwistZero F U V c hf h h₀ h₁ h₀₁)
  obtain ⟨g0, g1⟩ := finiteDimensional_family (resUV F U V c) (resVU F U V c)
    (fEquiv F U V c hf) (fMul F V c f) (resVU_fMul F U V c hf) hinj
    (twistFamily F U V c hf) (twistFamily_succ F U V c hf) m
  exact ⟨Module.Finite.equiv (cohomologyDivisorTwistZeroEquiv F U V c hf h h₀ h₁ h₀₁ m).symm,
    Module.Finite.equiv (cohomologyDivisorTwistOneEquiv F U V c hf h h₀ h₁ h₀₁ m).symm⟩

end Field

end CoverFree

end

end DeJongAlterations.StableModification.CurvesField
