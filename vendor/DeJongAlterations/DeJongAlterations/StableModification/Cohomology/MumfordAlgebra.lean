/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechRefinement
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.Module

/-!
# Universal quasi-isomorphisms and the Mumford complex (algebra)

This file contains the homological algebra behind the Mumford complex (Mumford, *Abelian
varieties*, §5; Hartshorne III.12.2–12.3; EGA III 6.10; Stacks 0BDJ), used for the constancy of
the Euler characteristic and for semicontinuity and base change (Temkin, *Stable modification of
relative curves*, Lemma 4.4.2, Proposition 4.4.6). Blueprint `sm-cohomology-finite.tex`,
`lem:sm-univ-quasi-iso`, `thm:sm-perfect-model`.

For a ring map `φ : A → B`, `baseChange φ` applies `B ⊗_A -` degreewise to `ℕ`-indexed cochain
complexes of `A`-modules. A chain map is a *universal quasi-isomorphism* (`IsUnivQuasiIso`) if it
is a quasi-isomorphism after every base change.

## Main results

* `flat_ker_of_surjective`: the kernel of a surjection of flat modules is flat.
* `univQuasiIso_of_shortExact` (blueprint `lem:sm-univ-quasi-iso`): if `0 → K → M → N → 0` is a
  short exact sequence of complexes with `N` degreewise flat and universally acyclic, then
  `K → M` is a universal quasi-isomorphism (the base-changed sequence stays exact by
  `Tor₁(N^i, B) = 0`).
* `replComplex`, `replHom`, `isUnivQuasiIso_replHom`, `replTopEquiv` (blueprint
  `lem:sm-replacement`): for `α : P → D^{m+1}` with `α(P) + d(D^m) = D^{m+1}`, the kernel of
  `D ⊕ (P = P)[m] → (D^{m+1} = D^{m+1})[m]` is a complex with `P` in degree `m + 1` mapping by a
  universal quasi-isomorphism to `D`, without change outside degrees `m, m + 1`.
* `exists_perfect_model` (blueprint `thm:sm-perfect-model`; Mumford, *Abelian varieties*, §5,
  Lemma 1): a degreewise flat complex over a Noetherian ring, bounded above, with finite
  cohomology, receives a universal quasi-isomorphism from a bounded complex of finite projective
  modules.
-/

universe u

open CategoryTheory Limits

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section FlatKernel

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The kernel of a surjection between flat modules is flat. -/
theorem flat_ker_of_surjective [Module.Flat R M] [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMapₛ.{u}]
  intro P P' _ _ _ _ i hi
  let _ := Module.addCommMonoidToAddCommGroup R (M := P)
  -- `P ⊗ ker f → P ⊗ M` is injective because `N` is flat
  have h1 : Function.Injective ((LinearMap.ker f).subtype.lTensor P) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) P
  -- `P ⊗ M → P' ⊗ M` is injective because `M` is flat
  have h2 : Function.Injective (i.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  have hcomm : (i.rTensor M).comp ((LinearMap.ker f).subtype.lTensor P) =
      ((LinearMap.ker f).subtype.lTensor P').comp (i.rTensor (LinearMap.ker f)) := by
    ext p k
    simp
  intro x y hxy
  apply h1
  apply h2
  have := congrArg ((LinearMap.ker f).subtype.lTensor P') hxy
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply,
    LinearMap.comp_apply] at this
  exact this

end FlatKernel

section BaseChangeModules

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- `B` as an `A`-module through `φ`. -/
abbrev scalarsModule : ModuleCat.{u} A := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)

/-- On underlying types, extension of scalars of a map is `lTensor`. -/
lemma extendScalars_map_eq_lTensor {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    ⇑((ModuleCat.extendScalars.{u, u, u} φ).map g) =
      ⇑(LinearMap.lTensor (scalarsModule φ) g.hom) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero ((ModuleCat.extendScalars φ).map g).hom).trans (map_zero _).symm
  | tmul b m => rfl
  | add x y hx hy =>
    exact (map_add ((ModuleCat.extendScalars φ).map g).hom x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- Extension of scalars preserves short exact sequences of modules whose third term is flat. -/
theorem shortExact_map_extendScalars {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    [Module.Flat A S.X₃] : (S.map (ModuleCat.extendScalars.{u, u, u} φ)).ShortExact := by
  have hf := hS.moduleCat_injective_f
  have hg := hS.moduleCat_surjective_g
  have hfg : Function.Exact S.f S.g := by
    intro y
    constructor
    · intro hy
      exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact y hy
    · rintro ⟨x, rfl⟩
      exact ConcreteCategory.congr_hom S.zero x
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    change (ModuleCat.extendScalars φ).map S.g y = 0 at hy
    rw [extendScalars_map_eq_lTensor] at hy
    obtain ⟨x, hx⟩ := ((lTensor_exact (scalarsModule φ) hfg hg) y).mp hy
    refine ⟨x, ?_⟩
    change (ModuleCat.extendScalars φ).map S.f x = y
    rw [extendScalars_map_eq_lTensor]
    exact hx
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.extendScalars φ).map S.f)
    rw [extendScalars_map_eq_lTensor]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hg S.f.hom hf hfg _
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective ((ModuleCat.extendScalars φ).map S.g)
    rw [extendScalars_map_eq_lTensor]
    exact LinearMap.lTensor_surjective _ hg

end BaseChangeModules

section LES

variable {C : Type*} [Category C] [Abelian C]

/-- In a short exact sequence of `ℕ`-indexed cochain complexes whose third term is acyclic, the
first map is a quasi-isomorphism. -/
theorem isIso_homologyMap_f_of_acyclic {S : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) (h : ∀ p, IsZero (S.X₃.homology p)) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.f p) := by
  have hepi : Epi (HomologicalComplex.homologyMap S.f p) :=
    (hS.homology_exact₂ p).epi_f ((h p).eq_of_tgt _ _)
  have hmono : Mono (HomologicalComplex.homologyMap S.f p) := by
    cases p with
    | zero =>
      have := hS.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by simp)
    | succ k =>
      exact (hS.homology_exact₁ k (k + 1) (by simp)).mono_g ((h k).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end LES

section Complexes

variable {A : Type u} [CommRing A]

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

instance extendScalars_additive {B : Type u} [CommRing B] (φ : A →+* B) :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end

/-- Base change `B ⊗_A -` of `ℕ`-indexed cochain complexes of `A`-modules. -/
abbrev baseChange {B : Type u} [CommRing B] (φ : A →+* B) :
    CochainComplex (ModuleCat.{u} A) ℕ ⥤ CochainComplex (ModuleCat.{u} B) ℕ :=
  (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℕ)

/-- A chain map is a *universal quasi-isomorphism* if it is a quasi-isomorphism and stays one after
every base change (blueprint `def:sm-univ-quasi-iso`). -/
def IsUnivQuasiIso {K L : CochainComplex (ModuleCat.{u} A) ℕ} (f : K ⟶ L) : Prop :=
  QuasiIso f ∧ ∀ (B : Type u) [CommRing B] (φ : A →+* B), QuasiIso ((baseChange φ).map f)

/-- A complex is *universally acyclic* if it and all its base changes are acyclic. -/
def IsUnivAcyclic (E : CochainComplex (ModuleCat.{u} A) ℕ) : Prop :=
  (∀ n, IsZero (E.homology n)) ∧
    ∀ (B : Type u) [CommRing B] (φ : A →+* B) (n : ℕ), IsZero (((baseChange φ).obj E).homology n)

lemma IsUnivQuasiIso.comp {K L M : CochainComplex (ModuleCat.{u} A) ℕ} {f : K ⟶ L} {g : L ⟶ M}
    (hf : IsUnivQuasiIso f) (hg : IsUnivQuasiIso g) : IsUnivQuasiIso (f ≫ g) := by
  refine ⟨?_, fun B _ φ => ?_⟩
  · have := hf.1
    have := hg.1
    infer_instance
  · have := hf.2 B φ
    have := hg.2 B φ
    rw [Functor.map_comp]
    infer_instance

lemma isUnivQuasiIso_of_isIso {K L : CochainComplex (ModuleCat.{u} A) ℕ} (f : K ⟶ L)
    [IsIso f] : IsUnivQuasiIso f :=
  ⟨inferInstance, fun _ _ _ => inferInstance⟩

lemma quasiIso_of_isIso_homologyMap {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (h : ∀ p, IsIso (HomologicalComplex.homologyMap f p)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro p
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact h p

/-- Base change preserves degreewise short exact sequences of complexes whose third term is
degreewise flat. -/
theorem shortExact_map_baseChange {S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)}
    (hS : S.ShortExact) (hflat : ∀ i, Module.Flat A (S.X₃.X i)) {B : Type u} [CommRing B]
    (φ : A →+* B) : (S.map (baseChange φ)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hi : (S.map (HomologicalComplex.eval _ _ i)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.eval _ _ i)
  have : Module.Flat A (S.map (HomologicalComplex.eval _ _ i)).X₃ := hflat i
  exact shortExact_map_extendScalars φ (S := S.map (HomologicalComplex.eval _ _ i)) hi

/-- **Universal quasi-isomorphisms from short exact sequences** (blueprint
`lem:sm-univ-quasi-iso`): if `0 → K → M → N → 0` is short exact with `N` degreewise flat and
universally acyclic, then `K → M` is a universal quasi-isomorphism. -/
theorem univQuasiIso_of_shortExact {S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ)}
    (hS : S.ShortExact) (hflat : ∀ i, Module.Flat A (S.X₃.X i)) (hN : IsUnivAcyclic S.X₃) :
    IsUnivQuasiIso S.f := by
  refine ⟨quasiIso_of_isIso_homologyMap _ (isIso_homologyMap_f_of_acyclic hS hN.1), fun B _ φ => ?_⟩
  exact quasiIso_of_isIso_homologyMap _ (isIso_homologyMap_f_of_acyclic (S := S.map (baseChange φ))
    (shortExact_map_baseChange hS hflat φ) (hN.2 B φ))

end Complexes

section Acyclic

variable {R : Type u} [CommRing R]

lemma eq_zero_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) (x : M) : x = 0 := by
  have := ConcreteCategory.congr_hom (h.eq_of_src (𝟙 M) 0) x
  simpa using this

/-- A complex concentrated in degrees `m, m + 1` with bijective differential is acyclic. -/
lemma isZero_homology_of_two (K : CochainComplex (ModuleCat.{u} R) ℕ) (m : ℕ)
    (hz : ∀ k, k ≠ m → k ≠ m + 1 → IsZero (K.X k))
    (hb : Function.Bijective (K.d m (m + 1))) (n : ℕ) : IsZero (K.homology n) := by
  cases n with
  | zero =>
    rw [isZero_homology_zero_iff]
    by_cases h0 : m = 0
    · subst h0
      exact hb.1
    · intro x y _
      rw [eq_zero_of_isZero (hz 0 (Ne.symm h0) (by omega)) x,
        eq_zero_of_isZero (hz 0 (Ne.symm h0) (by omega)) y]
  | succ p =>
    rw [isZero_homology_succ_iff]
    intro x hx
    by_cases h1 : p + 1 = m
    · subst h1
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact (hb.1 (hx.trans (map_zero _).symm)).symm
    · by_cases h2 : p = m
      · subst h2
        exact hb.2 x
      · refine ⟨0, ?_⟩
        rw [map_zero, eq_zero_of_isZero (hz (p + 1) h1 (by omega)) x]

end Acyclic

section Double

variable {A : Type u} [CommRing A]

lemma rel_succ (m : ℕ) : (ComplexShape.up ℕ).Rel m (m + 1) := rfl

/-- The two-term complex `X --𝟙--> X` in degrees `m, m + 1` is universally acyclic. -/
theorem isUnivAcyclic_double (X : ModuleCat.{u} A) (m : ℕ) :
    IsUnivAcyclic (HomologicalComplex.double (𝟙 X) (rel_succ m)) := by
  have hne : m ≠ m + 1 := by omega
  have hiso : IsIso ((HomologicalComplex.double (𝟙 X) (rel_succ m)).d m (m + 1)) := by
    rw [HomologicalComplex.double_d _ _ hne]
    infer_instance
  refine ⟨fun n => ?_, fun B _ φ n => ?_⟩
  · exact isZero_homology_of_two _ m
      (fun k h0 h1 => HomologicalComplex.isZero_double_X _ _ k h0 h1)
      (ConcreteCategory.bijective_of_isIso _) n
  · refine isZero_homology_of_two _ m
      (fun k h0 h1 => Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ)
        (HomologicalComplex.isZero_double_X (𝟙 X) (rel_succ m) k h0 h1))
      ?_ n
    change Function.Bijective
      ((ModuleCat.extendScalars φ).map ((HomologicalComplex.double (𝟙 X) (rel_succ m)).d m (m + 1)))
    exact ConcreteCategory.bijective_of_isIso _

/-- The projection `D ⊞ E → D` is a universal quasi-isomorphism if `E` is universally acyclic. -/
theorem isUnivQuasiIso_biprod_fst (D E : CochainComplex (ModuleCat.{u} A) ℕ)
    (hE : IsUnivAcyclic E) : IsUnivQuasiIso (biprod.fst : D ⊞ E ⟶ D) := by
  let S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ) :=
    ShortComplex.mk (biprod.inr : E ⟶ D ⊞ E) biprod.fst (by simp)
  let sp : S.Splitting :=
    { r := biprod.snd
      s := biprod.inl
      f_r := by simp [S]
      s_g := by simp [S]
      id := by
        change biprod.snd ≫ biprod.inr + biprod.fst ≫ biprod.inl = 𝟙 (D ⊞ E)
        rw [add_comm]
        exact biprod.total }
  refine ⟨quasiIso_of_isIso_homologyMap _ (isIso_homologyMap_g_of_acyclic (S := S)
    sp.shortExact hE.1), fun B _ φ => ?_⟩
  exact quasiIso_of_isIso_homologyMap _ (isIso_homologyMap_g_of_acyclic (S := S.map (baseChange φ))
    (sp.map (baseChange φ)).shortExact (hE.2 B φ))

end Double

section HomToDouble

variable {V : Type*} [Category V] [Preadditive V] [HasZeroObject V]
  (K : CochainComplex V ℕ) (X : V) (m : ℕ) (ψ : K.X (m + 1) ⟶ X)

open scoped Classical in
/-- A chain map `K → (X --𝟙--> X)` (degrees `m, m + 1`) from `ψ : K^{m+1} → X`; in degree `m` it is
`ψ ∘ d`. -/
noncomputable def homToDouble : K ⟶ HomologicalComplex.double (𝟙 X) (rel_succ m) where
  f k :=
    if hk₀ : k = m then
      eqToHom (by rw [hk₀]) ≫ K.d m (m + 1) ≫ ψ ≫
        (HomologicalComplex.doubleXIso₀ (𝟙 X) (rel_succ m)).inv ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = m + 1 then
      eqToHom (by rw [hk₁]) ≫ ψ ≫
        (HomologicalComplex.doubleXIso₁ (𝟙 X) (rel_succ m) (by omega)).inv ≫ eqToHom (by rw [hk₁])
    else 0
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst hij'
    by_cases h₀ : i = m
    · subst h₀
      rw [dif_pos rfl, dif_neg (by omega), dif_pos rfl, HomologicalComplex.double_d _ _ (by omega)]
      simp
    · rw [dif_neg h₀]
      by_cases h₁ : i = m + 1
      · subst h₁
        rw [dif_pos rfl, dif_neg (by omega), dif_neg (by omega),
          HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)]
        simp
      · rw [dif_neg h₁, zero_comp]
        by_cases h₂ : i + 1 = m
        · subst h₂
          rw [dif_pos rfl]
          simp
        · rw [dif_neg h₂, dif_neg (by omega), comp_zero]

@[reassoc]
lemma homToDouble_f₀ : (homToDouble K X m ψ).f m =
    K.d m (m + 1) ≫ ψ ≫ (HomologicalComplex.doubleXIso₀ (𝟙 X) (rel_succ m)).inv := by
  simp [homToDouble]

@[reassoc]
lemma homToDouble_f₁ : (homToDouble K X m ψ).f (m + 1) =
    ψ ≫ (HomologicalComplex.doubleXIso₁ (𝟙 X) (rel_succ m) (by omega)).inv := by
  simp [homToDouble]

end HomToDouble

section Replacement

variable {A : Type u} [CommRing A] (D : CochainComplex (ModuleCat.{u} A) ℕ) (m : ℕ)
  (P : ModuleCat.{u} A) (α : P ⟶ D.X (m + 1))

lemma succ_ne (m : ℕ) : m ≠ m + 1 := by omega

/-- The two-term complex `D^{m+1} --𝟙--> D^{m+1}` in degrees `m, m + 1`. -/
abbrev replTarget : CochainComplex (ModuleCat.{u} A) ℕ :=
  HomologicalComplex.double (𝟙 (D.X (m + 1))) (rel_succ m)

/-- The two-term complex `P --𝟙--> P` in degrees `m, m + 1`. -/
abbrev replAux : CochainComplex (ModuleCat.{u} A) ℕ :=
  HomologicalComplex.double (𝟙 P) (rel_succ m)

/-- `D → replTarget`: the differential in degree `m`, the identity in degree `m + 1`. -/
noncomputable def replLeft : D ⟶ replTarget D m := homToDouble D (D.X (m + 1)) m (𝟙 _)

/-- `replAux → replTarget`: `α` in both degrees. -/
noncomputable def replRight : replAux m P ⟶ replTarget D m :=
  HomologicalComplex.mkHomFromDouble (rel_succ m) (succ_ne m)
    (α ≫ (HomologicalComplex.doubleXIso₀ (𝟙 (D.X (m + 1))) (rel_succ m)).inv)
    (α ≫ (HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m) (succ_ne m)).inv)
    (by rw [HomologicalComplex.double_d _ _ (succ_ne m)]; simp)
    (by intro k _; rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)]; simp)

/-- `D ⊞ replAux → replTarget`, `(x, p) ↦ x - α p` in the relevant degrees. -/
noncomputable def replMap : D ⊞ replAux m P ⟶ replTarget D m :=
  biprod.desc (replLeft D m) (-replRight D m P α)

/-- The replaced complex: the kernel of `replMap`; in degree `m + 1` it is `P`, in degree `m` it
is the fibre product `D^m ×_{D^{m+1}} P`, and it agrees with `D` elsewhere. -/
noncomputable abbrev replComplex : CochainComplex (ModuleCat.{u} A) ℕ := kernel (replMap D m P α)

/-- The comparison map `replComplex → D`. -/
noncomputable def replHom : replComplex D m P α ⟶ D := kernel.ι (replMap D m P α) ≫ biprod.fst

lemma replMap_inl_f (k : ℕ) (x : D.X k) :
    (replMap D m P α).f k ((biprod.inl : D ⟶ D ⊞ replAux m P).f k x) = (replLeft D m).f k x := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, replMap, biprod.inl_desc]

lemma replMap_inr_f (k : ℕ) (e : (replAux m P).X k) :
    (replMap D m P α).f k ((biprod.inr : replAux m P ⟶ D ⊞ replAux m P).f k e) =
      -(replRight D m P α).f k e := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, replMap, biprod.inr_desc]
  rfl

variable {D m P α}

theorem epi_replMap
    (hsurj : ∀ y : D.X (m + 1), ∃ (p : P) (x : D.X m), α p + D.d m (m + 1) x = y) :
    Epi (replMap D m P α) := by
  apply HomologicalComplex.epi_of_epi_f
  intro k
  rw [ModuleCat.epi_iff_surjective]
  by_cases h₀ : k = m
  · subst h₀
    intro y'
    obtain ⟨p, x, hpx⟩ := hsurj ((HomologicalComplex.doubleXIso₀ (𝟙 (D.X (k + 1))) (rel_succ k)).hom y')
    refine ⟨(biprod.inl : D ⟶ D ⊞ replAux k P).f k x -
      (biprod.inr : replAux k P ⟶ D ⊞ replAux k P).f k
        ((HomologicalComplex.doubleXIso₀ (𝟙 P) (rel_succ k)).inv p), ?_⟩
    rw [map_sub, replMap_inl_f, replMap_inr_f, sub_neg_eq_add, replLeft, replRight,
      homToDouble_f₀, HomologicalComplex.mkHomFromDouble_f₀]
    simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
    rw [Iso.inv_hom_id_apply, ← map_add]
    have h : (D.d k (k + 1)) x + α p =
        (HomologicalComplex.doubleXIso₀ (𝟙 (D.X (k + 1))) (rel_succ k)).hom y' := by
      rw [← hpx]
      exact add_comm _ _
    rw [h, Iso.hom_inv_id_apply]
  · by_cases h₁ : k = m + 1
    · subst h₁
      intro y'
      refine ⟨(biprod.inl : D ⟶ D ⊞ replAux m P).f (m + 1)
        ((HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m) (succ_ne m)).hom y'), ?_⟩
      rw [replMap_inl_f, replLeft, homToDouble_f₁]
      simp
    · intro y'
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact (eq_zero_of_isZero (HomologicalComplex.isZero_double_X _ _ k h₀ h₁) y').symm

end Replacement

section ShortExactModules

variable {R : Type u} [CommRing R]

/-- In a short exact sequence of modules with flat middle and right terms, the left term is
flat. -/
theorem flat_X₁_of_shortExact {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Flat R S.X₂] [Module.Flat R S.X₃] : Module.Flat R S.X₁ := by
  have hf := hS.moduleCat_injective_f
  have hg := hS.moduleCat_surjective_g
  have hker := flat_ker_of_surjective S.g.hom hg
  have hrange : LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ConcreteCategory.congr_hom S.zero x
    · intro hy
      exact (ShortComplex.moduleCat_exact_iff S).mp hS.exact y hy
  let e : S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom :=
    (LinearEquiv.ofInjective S.f.hom hf).trans (LinearEquiv.ofEq _ _ hrange)
  exact Module.Flat.of_linearEquiv e

lemma flat_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) : Module.Flat R M := by
  have : Subsingleton M := ⟨fun x y => by rw [eq_zero_of_isZero h x, eq_zero_of_isZero h y]⟩
  infer_instance

lemma flat_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N) [Module.Flat R N] : Module.Flat R M :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Products of two flat modules are flat. -/
theorem flat_prod (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap'.{u}]
  intro P P' _ _ _ _ f hf
  have hcomm : ∀ x, TensorProduct.prodRight R R P' M N (f.rTensor (M × N) x) =
      Prod.map (f.rTensor M) (f.rTensor N) (TensorProduct.prodRight R R P M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact Prod.ext (map_zero _).symm (map_zero _).symm
    | tmul p mn => simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]
      exact Prod.ext (map_add _ _ _).symm (map_add _ _ _).symm
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  intro x y hxy
  apply (TensorProduct.prodRight R R P M N).injective
  have := congrArg (TensorProduct.prodRight R R P' M N) hxy
  rw [hcomm, hcomm] at this
  exact Prod.ext (h1 (congrArg Prod.fst this)) (h2 (congrArg Prod.snd this))

/-- Biproducts of flat modules are flat. -/
instance flat_biprod (M N : ModuleCat.{u} R) [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M ⊞ N : ModuleCat.{u} R) :=
  have : Module.Flat R (ModuleCat.of R (M × N)) := flat_prod M N
  flat_of_iso (ModuleCat.biprodIsoProd M N)

end ShortExactModules

section ReplacementProperties

variable {A : Type u} [CommRing A] {D : CochainComplex (ModuleCat.{u} A) ℕ} {m : ℕ}
  {P : ModuleCat.{u} A} {α : P ⟶ D.X (m + 1)}

lemma flat_double_X (X : ModuleCat.{u} A) [Module.Flat A X] (m k : ℕ) :
    Module.Flat A ((HomologicalComplex.double (𝟙 X) (rel_succ m)).X k) := by
  by_cases h₀ : k = m
  · subst h₀
    exact flat_of_iso (HomologicalComplex.doubleXIso₀ (𝟙 X) (rel_succ k))
  · by_cases h₁ : k = m + 1
    · subst h₁
      exact flat_of_iso (HomologicalComplex.doubleXIso₁ (𝟙 X) (rel_succ m) (succ_ne m))
    · exact flat_of_isZero (HomologicalComplex.isZero_double_X _ _ k h₀ h₁)

/-- The short exact sequence `0 → replComplex → D ⊞ replAux → replTarget → 0`. -/
noncomputable abbrev replSES (D : CochainComplex (ModuleCat.{u} A) ℕ) (m : ℕ)
    (P : ModuleCat.{u} A) (α : P ⟶ D.X (m + 1)) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℕ) :=
  ShortComplex.mk (kernel.ι (replMap D m P α)) (replMap D m P α) (kernel.condition _)

variable (hsurj : ∀ y : D.X (m + 1), ∃ (p : P) (x : D.X m), α p + D.d m (m + 1) x = y)
include hsurj

theorem shortExact_replSES : (replSES D m P α).ShortExact := by
  have := epi_replMap hsurj
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance this

theorem shortExact_replSES_X (k : ℕ) :
    ((replSES D m P α).map (HomologicalComplex.eval _ _ k)).ShortExact :=
  (shortExact_replSES hsurj).map_of_exact (HomologicalComplex.eval _ _ k)

/-- The comparison map of the replacement is a universal quasi-isomorphism
(blueprint `lem:sm-replacement`). -/
theorem isUnivQuasiIso_replHom [Module.Flat A (D.X (m + 1))] :
    IsUnivQuasiIso (replHom D m P α) :=
  (univQuasiIso_of_shortExact (shortExact_replSES hsurj)
    (fun k => flat_double_X (D.X (m + 1)) m k) (isUnivAcyclic_double _ m)).comp
    (isUnivQuasiIso_biprod_fst D (replAux m P) (isUnivAcyclic_double P m))

/-- The replaced complex is degreewise flat. -/
theorem flat_replComplex_X [∀ k, Module.Flat A (D.X k)] [Module.Flat A P] (k : ℕ) :
    Module.Flat A ((replComplex D m P α).X k) := by
  have hS := shortExact_replSES_X hsurj k
  have : Module.Flat A ((replSES D m P α).map (HomologicalComplex.eval _ _ k)).X₂ := by
    have := flat_double_X P m k
    exact flat_of_iso (HomologicalComplex.biprodXIso D (replAux m P) k)
  have : Module.Flat A ((replSES D m P α).map (HomologicalComplex.eval _ _ k)).X₃ :=
    flat_double_X (D.X (m + 1)) m k
  exact flat_X₁_of_shortExact hS

/-- Away from degrees `m, m + 1`, the replacement does not change the complex. -/
theorem isIso_replHom_f {k : ℕ} (h₀ : k ≠ m) (h₁ : k ≠ m + 1) :
    IsIso ((replHom D m P α).f k) := by
  have hS := shortExact_replSES_X hsurj k
  have hz : IsZero ((replTarget D m).X k) := HomologicalComplex.isZero_double_X _ _ k h₀ h₁
  have hι : IsIso ((kernel.ι (replMap D m P α)).f k) := by
    have := hS.mono_f
    have : Epi ((replSES D m P α).map (HomologicalComplex.eval _ _ k)).f :=
      hS.exact.epi_f (hz.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi ((replSES D m P α).map (HomologicalComplex.eval _ _ k)).f
  have hE : IsZero ((replAux m P).X k) := HomologicalComplex.isZero_double_X _ _ k h₀ h₁
  have hfst : IsIso ((biprod.fst : D ⊞ replAux m P ⟶ D).f k) := by
    rw [← HomologicalComplex.biprodXIso_hom_fst]
    have : IsIso (biprod.fst : D.X k ⊞ (replAux m P).X k ⟶ D.X k) :=
      (isoBiprodZero hE).isIso_inv
    infer_instance
  have heq : (replHom D m P α).f k =
      (kernel.ι (replMap D m P α)).f k ≫ (biprod.fst : D ⊞ replAux m P ⟶ D).f k := rfl
  rw [heq]
  infer_instance

end ReplacementProperties

section ReplacementTop

variable {A : Type u} [CommRing A] {D : CochainComplex (ModuleCat.{u} A) ℕ} {m : ℕ}
  {P : ModuleCat.{u} A} {α : P ⟶ D.X (m + 1)}

/-- An element of a biproduct of complexes is the sum of its two components. -/
lemma biprod_X_eq {K L : CochainComplex (ModuleCat.{u} A) ℕ} (k : ℕ) (e : (K ⊞ L).X k) :
    e = (biprod.inl : K ⟶ K ⊞ L).f k ((biprod.fst : K ⊞ L ⟶ K).f k e) +
      (biprod.inr : L ⟶ K ⊞ L).f k ((biprod.snd : K ⊞ L ⟶ L).f k e) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.Hom.f φ k)
    (biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (K ⊞ L))) e
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at h
  exact h.symm

lemma biprod_snd_inl_f_apply {K L : CochainComplex (ModuleCat.{u} A) ℕ} (k : ℕ) (x : K.X k) :
    (biprod.snd : K ⊞ L ⟶ L).f k ((biprod.inl : K ⟶ K ⊞ L).f k x) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.biprod_inl_snd_f]
  rfl

lemma biprod_snd_inr_f_apply {K L : CochainComplex (ModuleCat.{u} A) ℕ} (k : ℕ) (y : L.X k) :
    (biprod.snd : K ⊞ L ⟶ L).f k ((biprod.inr : L ⟶ K ⊞ L).f k y) = y := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.biprod_inr_snd_f]
  rfl

lemma replLeft_f₁ : (replLeft D m).f (m + 1) =
    (HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m) (succ_ne m)).inv := by
  rw [replLeft, homToDouble_f₁, Category.id_comp]

lemma replRight_f₁ : (replRight D m P α).f (m + 1) =
    (HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).hom ≫ α ≫
      (HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m) (succ_ne m)).inv := by
  rw [replRight, HomologicalComplex.mkHomFromDouble_f₁]

variable (D m P α) in
/-- The degree-`(m + 1)` term of the replacement is `P`: the second component. -/
noncomputable def replTop : (replComplex D m P α).X (m + 1) ⟶ P :=
  (kernel.ι (replMap D m P α)).f (m + 1) ≫
    (biprod.snd : D ⊞ replAux m P ⟶ replAux m P).f (m + 1) ≫
      (HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).hom

variable (hsurj : ∀ y : D.X (m + 1), ∃ (p : P) (x : D.X m), α p + D.d m (m + 1) x = y)
include hsurj

theorem bijective_replTop : Function.Bijective (replTop D m P α) := by
  have hS := shortExact_replSES_X hsurj (m + 1)
  have hinj : Function.Injective ((kernel.ι (replMap D m P α)).f (m + 1)) :=
    hS.moduleCat_injective_f
  have hex := (ShortComplex.moduleCat_exact_iff _).mp hS.exact
  have hcond : ∀ z, (replMap D m P α).f (m + 1) ((kernel.ι (replMap D m P α)).f (m + 1) z) = 0 :=
    fun z => by
      rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, kernel.condition]
      rfl
  -- the value of `replMap` on a decomposed element
  have hval : ∀ (x : D.X (m + 1)) (e : (replAux m P).X (m + 1)),
      (replMap D m P α).f (m + 1) ((biprod.inl : D ⟶ D ⊞ replAux m P).f (m + 1) x +
        (biprod.inr : replAux m P ⟶ D ⊞ replAux m P).f (m + 1) e) =
      (HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m) (succ_ne m)).inv
        (x - α ((HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).hom e)) := by
    intro x e
    rw [map_add, replMap_inl_f, replMap_inr_f, replLeft_f₁, replRight_f₁, map_sub,
      ← sub_eq_add_neg]
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    apply hinj
    rw [map_zero]
    set e := (kernel.ι (replMap D m P α)).f (m + 1) z with he
    have hsnd : (biprod.snd : D ⊞ replAux m P ⟶ replAux m P).f (m + 1) e = 0 := by
      apply (HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).toLinearEquiv.injective
      rw [map_zero]
      exact hz
    have h0 := hcond z
    rw [← he, biprod_X_eq (m + 1) e, hval, hsnd, map_zero, map_zero, sub_zero] at h0
    have hfst : (biprod.fst : D ⊞ replAux m P ⟶ D).f (m + 1) e = 0 := by
      apply (HomologicalComplex.doubleXIso₁ (𝟙 (D.X (m + 1))) (rel_succ m)
        (succ_ne m)).toLinearEquiv.symm.injective
      rw [map_zero]
      exact h0
    rw [biprod_X_eq (m + 1) e, hfst, hsnd, map_zero, map_zero, add_zero]
  · intro p
    let e : (replAux m P).X (m + 1) :=
      (HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).inv p
    obtain ⟨z, hz⟩ := hex ((biprod.inl : D ⟶ D ⊞ replAux m P).f (m + 1) (α p) +
      (biprod.inr : replAux m P ⟶ D ⊞ replAux m P).f (m + 1) e) (by
        change (replMap D m P α).f (m + 1) _ = 0
        rw [hval]
        simp [e])
    refine ⟨z, ?_⟩
    change (HomologicalComplex.doubleXIso₁ (𝟙 P) (rel_succ m) (succ_ne m)).hom
      ((biprod.snd : D ⊞ replAux m P ⟶ replAux m P).f (m + 1)
        ((kernel.ι (replMap D m P α)).f (m + 1) z)) = p
    change (kernel.ι (replMap D m P α)).f (m + 1) z = _ at hz
    rw [hz, map_add, biprod_snd_inl_f_apply, biprod_snd_inr_f_apply, zero_add]
    exact Iso.inv_hom_id_apply _ p

/-- The degree-`(m + 1)` term of the replacement is linearly equivalent to `P`. -/
noncomputable def replTopEquiv : (replComplex D m P α).X (m + 1) ≃ₗ[A] P :=
  LinearEquiv.ofBijective (replTop D m P α).hom (bijective_replTop hsurj)

end ReplacementTop

section Finiteness

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- If `H(S)` and `S.X₃` are finite over a Noetherian ring, so is `S.opcycles`, by the exact
sequence `0 → H(S) → S.opcycles → S.X₃`. -/
theorem finite_opcycles (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology]
    [Module.Finite R S.X₃] : Module.Finite R S.opcycles := by
  have hex : (ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles).Exact :=
    ShortComplex.exact_of_f_is_kernel _ S.homologyIsKernel
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have := isNoetherian_of_range_eq_ker S.homologyι.hom S.fromOpcycles.hom hex
  infer_instance

/-- If `H^{m+1}(D)` and `D^{m+2}` are finite over a Noetherian ring, so is `D^{m+1}/B^{m+1}`. -/
theorem finite_quotient_range_d (D : CochainComplex (ModuleCat.{u} R) ℕ) (m : ℕ)
    [Module.Finite R (D.homology (m + 1))] [Module.Finite R (D.X (m + 2))] :
    Module.Finite R (D.X (m + 1) ⧸ LinearMap.range (D.d m (m + 1)).hom) := by
  let S := D.sc' m (m + 1) (m + 2)
  have : Module.Finite R S.homology :=
    Module.Finite.equiv (D.homologyIsoSc' m (m + 1) (m + 2) (by simp) (by simp)).toLinearEquiv
  have : Module.Finite R S.X₃ := ‹Module.Finite R (D.X (m + 2))›
  have := finite_opcycles S
  exact Module.Finite.equiv S.moduleCatOpcyclesIso.toLinearEquiv

/-- If `H^0(K)` and `K^1` are finite over a Noetherian ring, so is `K^0`. -/
theorem finite_X_zero (K : CochainComplex (ModuleCat.{u} R) ℕ) [Module.Finite R (K.homology 0)]
    [Module.Finite R (K.X 1)] : Module.Finite R (K.X 0) := by
  have hex : (ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel 0 1 (by simp))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have : Module.Finite R (K.cycles 0) :=
    Module.Finite.equiv (CochainComplex.isoHomologyπ₀ K).symm.toLinearEquiv
  have := isNoetherian_of_range_eq_ker (K.iCycles 0).hom (K.d 0 1).hom hex
  infer_instance

omit [IsNoetherianRing R] in
/-- Generators of `D^{m+1}/B^{m+1}` lift to a map from a finite free module. -/
theorem exists_free_lift (D : CochainComplex (ModuleCat.{u} R) ℕ) (m : ℕ)
    [Module.Finite R (D.X (m + 1) ⧸ LinearMap.range (D.d m (m + 1)).hom)] :
    ∃ (r : ℕ) (α : ModuleCat.of R (Fin r → R) ⟶ D.X (m + 1)),
      ∀ y : D.X (m + 1), ∃ (p : Fin r → R) (x : D.X m), α p + D.d m (m + 1) x = y := by
  obtain ⟨r, f, hf⟩ :=
    Module.Finite.exists_fin' R (D.X (m + 1) ⧸ LinearMap.range (D.d m (m + 1)).hom)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (LinearMap.range (D.d m (m + 1)).hom).mkQ f (Submodule.mkQ_surjective _)
  refine ⟨r, ModuleCat.ofHom g, fun y => ?_⟩
  obtain ⟨p, hp⟩ := hf (Submodule.mkQ _ y)
  have hmem : y - g p ∈ LinearMap.range (D.d m (m + 1)).hom := by
    rw [← Submodule.Quotient.eq]
    change Submodule.mkQ _ y = Submodule.mkQ _ (g p)
    rw [← LinearMap.comp_apply, hg, hp]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨p, x, ?_⟩
  change g p + (D.d m (m + 1)).hom x = y
  rw [hx, add_sub_cancel]

end Finiteness

section PerfectModel

variable {A : Type u} [CommRing A]

/-- **Replacement step** (blueprint `lem:sm-replacement`): for a degreewise flat complex `D` over a
Noetherian ring with `H^{m+1}(D)` and `D^{m+2}` finite, there is a universal quasi-isomorphism
`K → D` with `K` degreewise flat, `K^{m+1}` finite free, and `K^k → D^k` an isomorphism for
`k ∉ {m, m + 1}`. -/
theorem exists_replacement [IsNoetherianRing A] (D : CochainComplex (ModuleCat.{u} A) ℕ) (m : ℕ)
    (hflat : ∀ k, Module.Flat A (D.X k)) [Module.Finite A (D.homology (m + 1))]
    [Module.Finite A (D.X (m + 2))] :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ D), IsUnivQuasiIso g ∧
      (∀ k, Module.Flat A (K.X k)) ∧ Module.Finite A (K.X (m + 1)) ∧
      Module.Free A (K.X (m + 1)) ∧ ∀ k, k ≠ m → k ≠ m + 1 → IsIso (g.f k) := by
  have := finite_quotient_range_d D m
  obtain ⟨r, α, hsurj⟩ := exists_free_lift D m
  have : ∀ k, Module.Flat A (D.X k) := hflat
  let e := replTopEquiv (α := α) hsurj
  exact ⟨replComplex D m _ α, replHom D m _ α, isUnivQuasiIso_replHom hsurj,
    flat_replComplex_X hsurj, Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm,
    fun k h₀ h₁ => isIso_replHom_f hsurj h₀ h₁⟩

lemma finite_homology_of_quasiIso {K L : CochainComplex (ModuleCat.{u} A) ℕ} (g : K ⟶ L)
    [QuasiIso g] (k : ℕ) [Module.Finite A (L.homology k)] : Module.Finite A (K.homology k) :=
  Module.Finite.equiv (isoOfQuasiIsoAt g k).symm.toLinearEquiv

/-- **Perfect models** (blueprint `thm:sm-perfect-model`; Mumford, *Abelian varieties*, §5,
Lemma 1; Hartshorne III.12.3; Stacks 0BDJ): a degreewise flat complex over a Noetherian ring,
concentrated in degrees `≤ n` and with finite cohomology, receives a universal
quasi-isomorphism from a complex of finite projective modules concentrated in degrees `≤ n`. -/
theorem exists_perfect_model [IsNoetherianRing A] (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (hflat : ∀ k, Module.Flat A (C.X k)) (hzero : ∀ k, n < k → IsZero (C.X k))
    (hH : ∀ k, Module.Finite A (C.homology k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite A (K.X k)) ∧ (∀ k, Module.Projective A (K.X k)) ∧
      ∀ k, n < k → IsZero (K.X k) := by
  have key : ∀ t, t ≤ n → ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ C),
      IsUnivQuasiIso g ∧ (∀ k, Module.Flat A (K.X k)) ∧
      (∀ k, n - t < k → Module.Finite A (K.X k) ∧ Module.Projective A (K.X k)) ∧
      ∀ k, n < k → IsZero (K.X k) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨C, 𝟙 C, isUnivQuasiIso_of_isIso _, hflat, fun k hk => ?_, hzero⟩
      have : Subsingleton (C.X k) :=
        ⟨fun x y => by
          rw [eq_zero_of_isZero (hzero k (by omega)) x, eq_zero_of_isZero (hzero k (by omega)) y]⟩
      have := Module.Free.of_subsingleton A (C.X k)
      exact ⟨inferInstance, inferInstance⟩
    | succ t ih =>
      intro ht
      obtain ⟨K, g, hg, hKflat, hKfin, hKzero⟩ := ih (by omega)
      have hj : n - (t + 1) + 1 = n - t := by omega
      have := hg.1
      have : Module.Finite A (K.homology (n - (t + 1) + 1)) := by
        have := hH (n - (t + 1) + 1)
        exact finite_homology_of_quasiIso g _
      have : Module.Finite A (K.X (n - (t + 1) + 2)) := (hKfin _ (by omega)).1
      obtain ⟨K', g', hg', hflat', hfin', hfree', hiso'⟩ :=
        exists_replacement K (n - (t + 1)) hKflat
      refine ⟨K', g' ≫ g, hg'.comp hg, hflat', fun k hk => ?_, fun k hk => ?_⟩
      · by_cases hk1 : k = n - (t + 1) + 1
        · subst hk1
          exact ⟨hfin', inferInstance⟩
        · have := hiso' k (by omega) hk1
          obtain ⟨h1, h2⟩ := hKfin k (by omega)
          exact ⟨Module.Finite.equiv (asIso (g'.f k)).toLinearEquiv.symm,
            Module.Projective.of_equiv (asIso (g'.f k)).toLinearEquiv.symm⟩
      · have := hiso' k (by omega) (by omega)
        exact (hKzero k hk).of_iso (asIso (g'.f k))
  obtain ⟨K, g, hg, hKflat, hKfin, hKzero⟩ := key n le_rfl
  have hfin : ∀ k, Module.Finite A (K.X k) := by
    intro k
    cases k with
    | zero =>
      have := hg.1
      have : Module.Finite A (K.homology 0) := by
        have := hH 0
        exact finite_homology_of_quasiIso g 0
      have : Module.Finite A (K.X 1) := (hKfin 1 (by omega)).1
      exact finite_X_zero K
    | succ k => exact (hKfin (k + 1) (by omega)).1
  refine ⟨K, g, hg, hfin, fun k => ?_, hKzero⟩
  have := hfin k
  have := hKflat k
  have := Module.finitePresentation_of_finite A (K.X k)
  exact Module.Flat.projective_of_finitePresentation

end PerfectModel

end

end DeJongAlterations.StableModification.Cohomology
