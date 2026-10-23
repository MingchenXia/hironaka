/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.MumfordAlgebra

/-!
# Consequences of the Mumford complex (algebra)

Let `A` be a Noetherian ring and `C` a degreewise flat `ℕ`-indexed cochain complex of `A`-modules,
bounded above, with finite cohomology. By `exists_perfect_model` there is a universal
quasi-isomorphism `K → C` from a bounded complex of finite projective modules. This file draws the
consequences used for proper flat families (Mumford, *Abelian varieties*, §5, Corollaries 1–3;
Hartshorne III.12.8–12.11; Temkin, *Stable modification of relative curves*, proofs of
Lemma 4.4.2 and Proposition 4.4.6). Blueprint `sm-cohomology-finite.tex`.

## Main results

* `exists_perfect_model_le`: if moreover `Hⁱ(C) = 0` for `i > q`, the perfect model can be taken
  in degrees `≤ q` (truncation, using that a surjection onto a projective module splits).
* `toBaseChange`: the comparison chain map `C → C ⊗_A B` (`x ↦ 1 ⊗ x`), as complexes of
  `A`-modules.
* `epi_homologyMap_toBaseChange`: if `Hⁱ(C) = 0` for `i > t` and `A → B` is surjective, then
  `Hᵗ(C) → Hᵗ(C ⊗_A B)` is surjective (top cohomology commutes with base change).
* `isZero_homology_baseChange_of_residue` (blueprint `cor:sm-semicontinuity`): over
  a Noetherian local ring with residue field `k`, if `Hⁱ(C) = 0` for `i > s + 1` and
  `H^{s+1}(C ⊗ k) = 0`, then `H^{s+1}(C) = 0` and `H^{s+1}(C ⊗_A B) = 0` for every `A → B`.
* `epi_homologyMap_toBaseChange_of_residue` (blueprint `cor:sm-base-change-onto`):
  under the same hypotheses, `Hˢ(C) → Hˢ(C ⊗_A B)` is surjective for every surjective `A → B`;
  for curves (`s = 0`): `h¹(F_s) = 0` implies `H⁰(X, F) → H⁰(X_s, F_s)` onto.
* `sum_finrank_homology_eq`: for a bounded complex of finite-dimensional vector spaces the
  alternating sums of the dimensions of the terms and of the cohomology agree.
* `exists_eulerChar_baseChange` (blueprint `cor:sm-euler-constant`): over a Noetherian local
  ring, `∑ (-1)^i dim_κ Hⁱ(C ⊗_A κ)` is independent of the field `κ` over `A`.
-/

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section Nakayama

variable {A : Type u} [CommRing A]

/-- **Nakayama's lemma for maps**: over a local ring, a map into a finite module is surjective if
it is surjective after base change to the residue field. -/
theorem surjective_of_extendScalars_residue [IsLocalRing A] {M N : ModuleCat.{u} A}
    [Module.Finite A N] (f : M ⟶ N)
    (h : Function.Surjective
      ((ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue A)).map f)) :
    Function.Surjective f := by
  have hg : Function.Surjective (LinearMap.lTensor (IsLocalRing.ResidueField A) f.hom) := by
    have heq : ∀ v, LinearMap.lTensor (IsLocalRing.ResidueField A) f.hom v =
        (ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue A)).map f v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul c x => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    intro w
    obtain ⟨v, hv⟩ := h w
    exact ⟨v, (heq v).trans hv⟩
  have key' : ∀ v, LinearMap.lTensor (IsLocalRing.ResidueField A) f.hom v ∈
      (LinearMap.range f.hom).map (TensorProduct.mk A (IsLocalRing.ResidueField A) N 1) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | tmul c x =>
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨f (a • x), ⟨a • x, rfl⟩, ?_⟩
      change (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] f (a • x) = IsLocalRing.residue A a ⊗ₜ[A] f x
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have key : (LinearMap.range f.hom).map
      (TensorProduct.mk A (IsLocalRing.ResidueField A) N 1) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hg w
    exact key' v
  rw [IsLocalRing.map_tensorProduct_mk_eq_top] at key
  exact LinearMap.range_eq_top.mp key

end Nakayama

section Truncation

variable {A : Type u} [CommRing A]

lemma finite_double_X (X : ModuleCat.{u} A) [Module.Finite A X] (m k : ℕ) :
    Module.Finite A ((HomologicalComplex.double (𝟙 X) (rel_succ m)).X k) := by
  by_cases h₀ : k = m
  · subst h₀
    exact Module.Finite.equiv (HomologicalComplex.doubleXIso₀ (𝟙 X) (rel_succ k)).symm.toLinearEquiv
  · by_cases h₁ : k = m + 1
    · subst h₁
      exact Module.Finite.equiv
        (HomologicalComplex.doubleXIso₁ (𝟙 X) (rel_succ m) (succ_ne m)).symm.toLinearEquiv
    · have : Subsingleton ((HomologicalComplex.double (𝟙 X) (rel_succ m)).X k) :=
        ⟨fun x y => by
          rw [eq_zero_of_isZero (HomologicalComplex.isZero_double_X _ _ k h₀ h₁) x,
            eq_zero_of_isZero (HomologicalComplex.isZero_double_X _ _ k h₀ h₁) y]⟩
      infer_instance

lemma finite_biprod_X (K L : CochainComplex (ModuleCat.{u} A) ℕ) (k : ℕ) [Module.Finite A (K.X k)]
    [Module.Finite A (L.X k)] : Module.Finite A ((K ⊞ L).X k) :=
  Module.Finite.equiv ((HomologicalComplex.biprodXIso K L k) ≪≫
    ModuleCat.biprodIsoProd (K.X k) (L.X k)).symm.toLinearEquiv

/-- Over a Noetherian ring, the replacement of a degreewise finite complex is degreewise finite. -/
theorem finite_replComplex_X [IsNoetherianRing A] {D : CochainComplex (ModuleCat.{u} A) ℕ} {m : ℕ}
    {P : ModuleCat.{u} A} {α : P ⟶ D.X (m + 1)}
    (hsurj : ∀ y : D.X (m + 1), ∃ (p : P) (x : D.X m), α p + D.d m (m + 1) x = y)
    (hfin : ∀ k, Module.Finite A (D.X k)) [Module.Finite A P] (k : ℕ) :
    Module.Finite A ((replComplex D m P α).X k) := by
  have hS := shortExact_replSES_X hsurj k
  have := hfin k
  have := finite_double_X P m k
  have : Module.Finite A ((D ⊞ replAux m P).X k) := finite_biprod_X _ _ k
  exact Module.Finite.of_injective ((kernel.ι (replMap D m P α)).f k).hom hS.moduleCat_injective_f

/-- **Truncation**: a bounded complex of finite projective modules over a Noetherian ring with
`K^i = 0` for `i > q + 1` and `H^{q+1}(K) = 0` receives a universal quasi-isomorphism from a
complex of finite projective modules concentrated in degrees `≤ q`. -/
theorem exists_truncation [IsNoetherianRing A] (K : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ)
    (hfin : ∀ k, Module.Finite A (K.X k)) (hproj : ∀ k, Module.Projective A (K.X k))
    (hzero : ∀ k, q + 1 < k → IsZero (K.X k)) (hH : IsZero (K.homology (q + 1))) :
    ∃ (K' : CochainComplex (ModuleCat.{u} A) ℕ) (g : K' ⟶ K), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite A (K'.X k)) ∧ (∀ k, Module.Projective A (K'.X k)) ∧
      ∀ k, q < k → IsZero (K'.X k) := by
  let P : ModuleCat.{u} A := ModuleCat.of A (Fin 0 → A)
  let α : P ⟶ K.X (q + 1) := 0
  have hsurj : ∀ y : K.X (q + 1), ∃ (p : P) (x : K.X q), α p + K.d q (q + 1) x = y := by
    intro y
    obtain ⟨x, hx⟩ := (isZero_homology_succ_iff K q).mp hH y
      (eq_zero_of_isZero (hzero (q + 2) (by omega)) _)
    exact ⟨0, x, by rw [map_zero, zero_add]; exact hx⟩
  have hflat : ∀ k, Module.Flat A (K.X k) := fun k => by
    have := hproj k
    infer_instance
  have := hflat (q + 1)
  have hfinK' := finite_replComplex_X hsurj hfin
  have hflatK' := flat_replComplex_X (P := P) (α := α) hsurj
  let e := replTopEquiv hsurj
  have hzero' : IsZero ((replComplex K q P α).X (q + 1)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact e.toEquiv.subsingleton
  refine ⟨replComplex K q P α, replHom K q P α, isUnivQuasiIso_replHom hsurj, hfinK',
    fun k => ?_, fun k hk => ?_⟩
  · have := hfinK' k
    have := hflatK' k
    have := Module.finitePresentation_of_finite A ((replComplex K q P α).X k)
    exact Module.Flat.projective_of_finitePresentation
  · by_cases hk1 : k = q + 1
    · subst hk1
      exact hzero'
    · have := isIso_replHom_f hsurj (k := k) (by omega) hk1
      exact (hzero k (by omega)).of_iso (asIso ((replHom K q P α).f k))

/-- **Perfect models in degrees `≤ q`**: if in `exists_perfect_model` moreover `Hⁱ(C) = 0` for
`i > q`, the perfect model can be taken in degrees `≤ q`. -/
theorem exists_perfect_model_le [IsNoetherianRing A] (C : CochainComplex (ModuleCat.{u} A) ℕ)
    (n q : ℕ) (hflat : ∀ k, Module.Flat A (C.X k)) (hzero : ∀ k, n < k → IsZero (C.X k))
    (hH : ∀ k, Module.Finite A (C.homology k)) (hvan : ∀ k, q < k → IsZero (C.homology k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite A (K.X k)) ∧ (∀ k, Module.Projective A (K.X k)) ∧
      ∀ k, q < k → IsZero (K.X k) := by
  obtain ⟨K₀, g₀, hg₀, hfin₀, hproj₀, hzero₀⟩ := exists_perfect_model C n hflat hzero hH
  have key : ∀ j, ∃ (K : CochainComplex (ModuleCat.{u} A) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite A (K.X k)) ∧ (∀ k, Module.Projective A (K.X k)) ∧
      ∀ k, q + (n - j) < k → IsZero (K.X k) := by
    intro j
    induction j with
    | zero => exact ⟨K₀, g₀, hg₀, hfin₀, hproj₀, fun k hk => hzero₀ k (by omega)⟩
    | succ j ih =>
      obtain ⟨K, g, hg, hfin, hproj, hzeroK⟩ := ih
      by_cases hj : n - j = 0
      · exact ⟨K, g, hg, hfin, hproj, fun k hk => hzeroK k (by omega)⟩
      · have hdeg : q + (n - (j + 1)) + 1 = q + (n - j) := by omega
        have := hg.1
        have hH' : IsZero (K.homology (q + (n - (j + 1)) + 1)) :=
          (hvan _ (by omega)).of_iso (isoOfQuasiIsoAt g _)
        obtain ⟨K', g', hg', hfin', hproj', hzero'⟩ :=
          exists_truncation K (q + (n - (j + 1))) hfin hproj
            (fun k hk => hzeroK k (by omega)) hH'
        exact ⟨K', g' ≫ g, hg'.comp hg, hfin', hproj', hzero'⟩
  obtain ⟨K, g, hg, hfin, hproj, hzeroK⟩ := key n
  exact ⟨K, g, hg, hfin, hproj, fun k hk => hzeroK k (by omega)⟩

end Truncation

section Comparison

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Restriction of scalars of complexes along `φ`. -/
abbrev restrictComplex : CochainComplex (ModuleCat.{u} B) ℕ ⥤ CochainComplex (ModuleCat.{u} A) ℕ :=
  (ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The comparison chain map `C → C ⊗_A B`, `x ↦ 1 ⊗ x`, as a map of complexes of `A`-modules. -/
def toBaseChange (C : CochainComplex (ModuleCat.{u} A) ℕ) :
    C ⟶ (restrictComplex φ).obj ((baseChange φ).obj C) where
  f i := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app (C.X i)
  comm' i j _ := ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.naturality (C.d i j)).symm

lemma toBaseChange_naturality {K C : CochainComplex (ModuleCat.{u} A) ℕ} (g : K ⟶ C) :
    g ≫ toBaseChange φ C = toBaseChange φ K ≫ (restrictComplex φ).map ((baseChange φ).map g) := by
  ext i : 1
  exact (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.naturality (g.f i)

/-- For surjective `φ`, the comparison map is degreewise surjective. -/
lemma surjective_toBaseChange_f (hφ : Function.Surjective φ)
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (i : ℕ) :
    Function.Surjective ((toBaseChange φ C).f i) := by
  intro w
  change ((ModuleCat.extendScalars.{u, u, u} φ).obj (C.X i) : Type u) at w
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b x =>
    obtain ⟨a, rfl⟩ := hφ b
    refine ⟨a • x, ?_⟩
    let : Module A B := Module.compHom B φ
    have h1 : (1 : B) ⊗ₜ[A] (a • x) = (a • (1 : B)) ⊗ₜ[A] x := (TensorProduct.smul_tmul _ _ _).symm
    have h2 : a • (1 : B) = φ a := mul_one (φ a)
    rw [h2] at h1
    exact h1
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ x' y'⟩

instance quasiIso_restrictComplex_map {K L : CochainComplex (ModuleCat.{u} B) ℕ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((restrictComplex φ).map f) := inferInstance

end Comparison

section TopDegree

variable {C : Type*} [Category C] [Abelian C]

/-- In the top degree, a degreewise epimorphism induces an epimorphism on cohomology. -/
lemma epi_homologyMap_of_top {K L : CochainComplex C ℕ} (f : K ⟶ L) (t : ℕ)
    (hK : K.d t (t + 1) = 0) (hL : L.d t (t + 1) = 0) [Epi (f.f t)] :
    Epi (HomologicalComplex.homologyMap f t) := by
  have := K.isIso_homologyι t (t + 1) (by simp) hK
  have := L.isIso_homologyι t (t + 1) (by simp) hL
  have hop : Epi (HomologicalComplex.opcyclesMap f t) := by
    have h := HomologicalComplex.p_opcyclesMap f t
    have : Epi (K.pOpcycles t ≫ HomologicalComplex.opcyclesMap f t) := by
      rw [h]
      infer_instance
    exact epi_of_epi (K.pOpcycles t) _
  have h := HomologicalComplex.homologyι_naturality f t
  have : Epi (HomologicalComplex.homologyMap f t ≫ L.homologyι t) := by
    rw [h]
    infer_instance
  have e : HomologicalComplex.homologyMap f t =
      (HomologicalComplex.homologyMap f t ≫ L.homologyι t) ≫ inv (L.homologyι t) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

end TopDegree

section Corollaries

variable {A : Type u} [CommRing A]

lemma isIso_homologyMap_of_quasiIso {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) [QuasiIso f] (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap f i) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

/-- **Top cohomology commutes with surjective base change**: if `Hⁱ(C) = 0` for `i > t`, then
`Hᵗ(C) → Hᵗ(C ⊗_A B)` is surjective for every surjective `φ : A → B`. -/
theorem epi_homologyMap_toBaseChange [IsNoetherianRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (n t : ℕ) (hflat : ∀ k, Module.Flat A (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.Finite A (C.homology k))
    (hvan : ∀ k, t < k → IsZero (C.homology k)) {B : Type u} [CommRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (toBaseChange φ C) t) := by
  obtain ⟨K, g, hg, -, -, hzeroK⟩ := exists_perfect_model_le C n t hflat hzero hH hvan
  have := hg.1
  have := hg.2 B φ
  have hK : Epi (HomologicalComplex.homologyMap (toBaseChange φ K) t) := by
    have : Epi ((toBaseChange φ K).f t) :=
      (ModuleCat.epi_iff_surjective _).mpr (surjective_toBaseChange_f φ hφ K t)
    apply epi_homologyMap_of_top
    · exact (hzeroK (t + 1) (by omega)).eq_of_tgt _ _
    · exact (Functor.map_isZero (ModuleCat.restrictScalars.{u} φ)
        (Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ)
          (hzeroK (t + 1) (by omega)))).eq_of_tgt _ _
  have hnat := congrArg (fun f => HomologicalComplex.homologyMap f t) (toBaseChange_naturality φ g)
  simp only [HomologicalComplex.homologyMap_comp] at hnat
  have := isIso_homologyMap_of_quasiIso g t
  have := isIso_homologyMap_of_quasiIso ((restrictComplex φ).map ((baseChange φ).map g)) t
  have e : HomologicalComplex.homologyMap (toBaseChange φ C) t =
      inv (HomologicalComplex.homologyMap g t) ≫
        HomologicalComplex.homologyMap (toBaseChange φ K) t ≫
          HomologicalComplex.homologyMap ((restrictComplex φ).map ((baseChange φ).map g)) t := by
    rw [← hnat, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- **Vanishing of top cohomology from the closed fibre** (blueprint `cor:sm-semicontinuity`):
over a Noetherian local ring with residue field `k`, if `Hⁱ(C) = 0` for `i > s + 1` and
`H^{s+1}(C ⊗_A k) = 0`, then `H^{s+1}(C) = 0` and `H^{s+1}(C ⊗_A B) = 0` for every `A → B`. -/
theorem isZero_homology_baseChange_of_residue [IsNoetherianRing A] [IsLocalRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (n s : ℕ) (hflat : ∀ k, Module.Flat A (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.Finite A (C.homology k))
    (hvan : ∀ k, s + 1 < k → IsZero (C.homology k))
    (hk : IsZero (((baseChange (IsLocalRing.residue A)).obj C).homology (s + 1))) :
    IsZero (C.homology (s + 1)) ∧ ∀ (B : Type u) [CommRing B] (φ : A →+* B),
      IsZero (((baseChange φ).obj C).homology (s + 1)) := by
  obtain ⟨K, g, hg, hfin, -, hzeroK⟩ := exists_perfect_model_le C n (s + 1) hflat hzero hH hvan
  have hk' : IsZero (((baseChange (IsLocalRing.residue A)).obj K).homology (s + 1)) := by
    have := hg.2 _ (IsLocalRing.residue A)
    exact hk.of_iso (isoOfQuasiIsoAt ((baseChange (IsLocalRing.residue A)).map g) (s + 1))
  have hsurjk : Function.Surjective
      ((ModuleCat.extendScalars.{u, u, u} (IsLocalRing.residue A)).map (K.d s (s + 1))) := by
    intro y
    obtain ⟨x, hx⟩ := (isZero_homology_succ_iff _ s).mp hk' y
      (eq_zero_of_isZero (Functor.map_isZero (ModuleCat.extendScalars.{u, u, u}
        (IsLocalRing.residue A)) (hzeroK (s + 2) (by omega))) _)
    exact ⟨x, hx⟩
  have := hfin (s + 1)
  have hsurj : Function.Surjective (K.d s (s + 1)) :=
    surjective_of_extendScalars_residue _ hsurjk
  refine ⟨?_, fun B _ φ => ?_⟩
  · have := hg.1
    have hK0 : IsZero (K.homology (s + 1)) := by
      rw [isZero_homology_succ_iff]
      intro y _
      exact hsurj y
    exact hK0.of_iso (isoOfQuasiIsoAt g _).symm
  · have := hg.2 B φ
    have hKB : IsZero (((baseChange φ).obj K).homology (s + 1)) := by
      rw [isZero_homology_succ_iff]
      intro y _
      have h : Function.Surjective
          ((ModuleCat.extendScalars.{u, u, u} φ).map (K.d s (s + 1))) := by
        rw [extendScalars_map_eq_lTensor]
        exact LinearMap.lTensor_surjective _ hsurj
      exact h y
    exact hKB.of_iso (isoOfQuasiIsoAt ((baseChange φ).map g) (s + 1)).symm

/-- **Cohomology and base change, onto form** (blueprint `cor:sm-base-change-onto`): over a
Noetherian local ring with residue field `k`, if `Hⁱ(C) = 0` for `i > s + 1` and
`H^{s+1}(C ⊗_A k) = 0`, then `Hˢ(C) → Hˢ(C ⊗_A B)` is surjective for every surjective
`φ : A → B`. For a curve (`s = 0`): `h¹(F_s) = 0` implies that `H⁰(X, F) → H⁰(X_s, F_s)` is
onto. -/
theorem epi_homologyMap_toBaseChange_of_residue [IsNoetherianRing A] [IsLocalRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (n s : ℕ) (hflat : ∀ k, Module.Flat A (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.Finite A (C.homology k))
    (hvan : ∀ k, s + 1 < k → IsZero (C.homology k))
    (hk : IsZero (((baseChange (IsLocalRing.residue A)).obj C).homology (s + 1)))
    {B : Type u} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ) :
    Epi (HomologicalComplex.homologyMap (toBaseChange φ C) s) := by
  refine epi_homologyMap_toBaseChange C n s hflat hzero hH (fun k hk' => ?_) φ hφ
  by_cases h : k = s + 1
  · subst h
    exact (isZero_homology_baseChange_of_residue C n s hflat hzero hH hvan hk).1
  · exact hvan k (by omega)

end Corollaries

section EulerField

variable {κ : Type u} [Field κ]

/-- Over a field, `dim Hʲ(V) + rank(d_{ij}) = dim ker(d_{jk})`. -/
lemma finrank_homology_add (V : CochainComplex (ModuleCat.{u} κ) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    [FiniteDimensional κ (V.X j)] :
    Module.finrank κ (V.homology j) + Module.finrank κ (LinearMap.range (V.d i j).hom) =
      Module.finrank κ (LinearMap.ker (V.d j k).hom) := by
  let S := V.sc' i j k
  have : FiniteDimensional κ S.X₂ := ‹FiniteDimensional κ (V.X j)›
  have e1 : Module.finrank κ (V.homology j) =
      Module.finrank κ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    LinearEquiv.finrank_eq ((V.homologyIsoSc' i j k hi hk) ≪≫ S.moduleCatHomologyIso).toLinearEquiv
  have e3 : Module.finrank κ (LinearMap.range S.moduleCatToCycles) =
      Module.finrank κ (LinearMap.range (V.d i j).hom) := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (LinearMap.ker S.g.hom).subtype
      (Submodule.injective_subtype _) (LinearMap.range S.moduleCatToCycles)),
      ← LinearMap.range_comp]
    rfl
  rw [e1, ← e3]
  exact Submodule.finrank_quotient_add_finrank _

/-- **Euler characteristic over a field**: for a complex of finite-dimensional vector spaces with
`V^{n+1} = 0`, `∑_{i ≤ n} (-1)^i dim Hⁱ(V) = ∑_{i ≤ n} (-1)^i dim Vⁱ`. -/
theorem sum_finrank_homology_eq (V : CochainComplex (ModuleCat.{u} κ) ℕ) (n : ℕ)
    [hV : ∀ i, FiniteDimensional κ (V.X i)] (hzero : IsZero (V.X (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank κ (V.homology i) : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank κ (V.X i) : ℤ) := by
  let z : ℕ → ℤ := fun i => Module.finrank κ (LinearMap.ker (V.d i (i + 1)).hom)
  let r : ℕ → ℤ := fun i => Module.finrank κ (LinearMap.range (V.d i (i + 1)).hom)
  let h : ℕ → ℤ := fun i => Module.finrank κ (V.homology i)
  have hX : ∀ i, (Module.finrank κ (V.X i) : ℤ) = r i + z i := fun i => by
    simp only [r, z]
    exact_mod_cast (LinearMap.finrank_range_add_finrank_ker (V.d i (i + 1)).hom).symm
  have h0 : h 0 = z 0 := by
    have e := finrank_homology_add V 0 0 1 (by simp) (by simp)
    have hd : V.d 0 0 = 0 := V.shape 0 0 (by simp)
    have : Module.finrank κ (LinearMap.range (V.d 0 0).hom) = 0 := by
      rw [hd]
      simp
    simp only [h, z]
    rw [this, add_zero] at e
    exact_mod_cast e
  have hs : ∀ i, h (i + 1) + r i = z (i + 1) := fun i => by
    have e := finrank_homology_add V i (i + 1) (i + 1 + 1) (by simp) (by simp)
    simp only [h, r, z]
    exact_mod_cast e
  have hr : r n = 0 := by
    simp only [r]
    have : Subsingleton (V.X (n + 1)) :=
      ⟨fun x y => by rw [eq_zero_of_isZero hzero x, eq_zero_of_isZero hzero y]⟩
    have : Module.finrank κ (LinearMap.range (V.d n (n + 1)).hom) = 0 :=
      Submodule.finrank_eq_zero.mpr (Subsingleton.elim _ _)
    exact_mod_cast this
  have key : ∀ m, ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * h i =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * (r i + z i) - (-1 : ℤ) ^ m * r m := by
    intro m
    induction m with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, h0]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (m + 1), ← hs m, pow_succ]
      ring
  have hsum : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank κ (V.X i) : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (r i + z i) :=
    Finset.sum_congr rfl fun i _ => by rw [hX i]
  rw [hsum]
  have := key n
  rw [hr, mul_zero, sub_zero] at this
  exact this

end EulerField

section Euler

variable {A : Type u} [CommRing A]

/-- **Constancy of the Euler characteristic** (blueprint `cor:sm-euler-constant`): over a
Noetherian local ring, for `C` as in `exists_perfect_model` (degreewise flat, zero above `n`,
finite cohomology) the Euler characteristic `∑_{i ≤ n} (-1)^i dim_κ Hⁱ(C ⊗_A κ)` is the same for
all fields `κ` over `A`: it equals `∑ (-1)^i rank Kⁱ` for a perfect model `K`. -/
theorem exists_eulerChar_baseChange [IsNoetherianRing A] [IsLocalRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) (hflat : ∀ k, Module.Flat A (C.X k))
    (hzero : ∀ k, n < k → IsZero (C.X k)) (hH : ∀ k, Module.Finite A (C.homology k)) :
    ∃ χ : ℤ, ∀ (κ : Type u) [Field κ] (φ : A →+* κ),
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * (Module.finrank κ (((baseChange φ).obj C).homology i) : ℤ) = χ := by
  obtain ⟨K, g, hg, hfin, hproj, hzeroK⟩ := exists_perfect_model C n hflat hzero hH
  refine ⟨∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank A (K.X i) : ℤ),
    fun κ _ φ => ?_⟩
  have := hg.2 κ φ
  let _ := φ.toAlgebra
  have hfd : ∀ i, FiniteDimensional κ (((baseChange φ).obj K).X i) := fun i => by
    have := hfin i
    exact Module.Finite.base_change A κ (K.X i)
  have hz : IsZero (((baseChange φ).obj K).X (n + 1)) :=
    Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ) (hzeroK (n + 1) (by omega))
  have e := sum_finrank_homology_eq ((baseChange φ).obj K) n hz
  have hH' : ∀ i, Module.finrank κ (((baseChange φ).obj C).homology i) =
      Module.finrank κ (((baseChange φ).obj K).homology i) := fun i =>
    (LinearEquiv.finrank_eq (isoOfQuasiIsoAt ((baseChange φ).map g) i).toLinearEquiv).symm
  have hX : ∀ i, Module.finrank κ (((baseChange φ).obj K).X i) = Module.finrank A (K.X i) :=
    fun i => by
      have := hfin i
      have := hproj i
      have : Module.Free A (K.X i) := Module.free_of_flat_of_isLocalRing
      exact Module.finrank_baseChange
  simp only [hH']
  rw [e]
  simp only [hX]

end Euler

end

end DeJongAlterations.StableModification.Cohomology
