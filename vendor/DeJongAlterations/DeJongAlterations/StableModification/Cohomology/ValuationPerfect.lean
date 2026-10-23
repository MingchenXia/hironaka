/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.MumfordCorollaries
import DeJongAlterations.StableModification.Cohomology.ValuationCoherent

/-!
# Perfect models over a valuation ring

Let `V` be a valuation ring and `C` a bounded complex of flat `V`-modules whose cohomology modules
are finitely presented. Then there is a bounded complex `K` of finite free `V`-modules with a
universal quasi-isomorphism `K → C` (`exists_perfect_model_valuation`), and `K` can be chosen in
degrees `≤ q` if `Hⁱ(C) = 0` for `i > q` (`exists_perfect_model_le_valuation`).

This is the valuation-ring form of the perfect models of `MumfordAlgebra.lean` and
`MumfordCorollaries.lean` (lane COH2, blueprint `thm:sm-perfect-model`, `lem:sm-truncation`;
Mumford, *Abelian varieties*, §5, Lemma 1). The replacement step and its universality are COH2's
(`replComplex`, `isUnivQuasiIso_replHom`); only the finiteness inputs change. COH2 uses that
submodules of finite modules over a Noetherian ring are finite. Over `V` we use instead that `V`
is coherent (`finitePresentation_ker_valuation`): if `D^{m+2}`, `D^{m+3}` and `H^{m+2}(D)` are
finitely presented, the boundaries `B^{m+2} ⊆ D^{m+2}` are finitely generated
(`fg_range_f_valuation`), so `D^{m+1}/B^{m+1}` is finitely generated
(`finite_quotient_range_d_valuation`); and a finite flat module over the local ring `V` is free.
Blueprint: `sm-cohomology-valuation.tex`, `lem:sm-val-perfect-model`.
-/

universe u

open CategoryTheory Limits
open DeJongAlterations.Geometry.ProperSteinProjectiveCech
open DeJongAlterations.StableModification.ValuationRing

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

section General

variable {R : Type u} [CommRing R]

/-- If `H(S)` is finite and the image of `S.g` is finitely generated, then `S.X₂ / im S.f` is
finite. -/
theorem finite_quotient_range_f (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.homology] (hg : (LinearMap.range S.g.hom).FG) :
    Module.Finite R (S.X₂ ⧸ LinearMap.range S.f.hom) := by
  have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
    rintro _ ⟨x, rfl⟩
    exact S.moduleCat_zero_apply x
  have hH : Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv
  let φ : LinearMap.ker S.g.hom →ₗ[R] S.X₂ ⧸ LinearMap.range S.f.hom :=
    (LinearMap.range S.f.hom).mkQ ∘ₗ (LinearMap.ker S.g.hom).subtype
  have hφ : LinearMap.range S.moduleCatToCycles ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  have hker : LinearMap.ker ((LinearMap.range S.f.hom).liftQ S.g.hom hle) =
      LinearMap.range ((LinearMap.range S.moduleCatToCycles).liftQ φ hφ) := by
    rw [Submodule.ker_liftQ, Submodule.range_liftQ, LinearMap.range_comp, Submodule.range_subtype]
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker
    ((LinearMap.range S.f.hom).liftQ S.g.hom hle) ?_ ?_⟩
  · rw [Submodule.map_top, Submodule.range_liftQ]
    exact hg
  · rw [top_inf_eq, hker]
    have := Module.Finite.fg_top.map ((LinearMap.range S.moduleCatToCycles).liftQ φ hφ)
    rwa [← LinearMap.range_eq_map] at this

end General

section Valuation

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- Over a valuation ring, if `S.X₂`, `S.X₃` and `H(S)` are finitely presented, then the image of
`S.f` is finitely generated. -/
theorem fg_range_f_valuation (S : ShortComplex (ModuleCat.{u} V))
    [Module.FinitePresentation V S.X₂] [Module.FinitePresentation V S.X₃]
    [Module.FinitePresentation V S.homology] : (LinearMap.range S.f.hom).FG := by
  have := finitePresentation_ker_valuation S.g.hom
  have : Module.FinitePresentation V
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Module.FinitePresentation.of_equiv S.moduleCatHomologyIso.toLinearEquiv
  have h := Module.FinitePresentation.fg_ker (LinearMap.range S.moduleCatToCycles).mkQ
    (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ] at h
  have heq : LinearMap.range S.f.hom =
      (LinearMap.range S.moduleCatToCycles).map (LinearMap.ker S.g.hom).subtype := by
    rw [← LinearMap.range_comp, LinearMap.subtype_comp_codRestrict]
  rw [heq]
  exact h.map _

/-- Over a valuation ring, `D^{m+1} / B^{m+1}` is finitely generated if `H^{m+1}(D)`,
`H^{m+2}(D)`, `D^{m+2}` and `D^{m+3}` are finitely presented. -/
theorem finite_quotient_range_d_valuation (D : CochainComplex (ModuleCat.{u} V) ℕ) (m : ℕ)
    [Module.FinitePresentation V (D.homology (m + 1))]
    [Module.FinitePresentation V (D.homology (m + 2))]
    [Module.FinitePresentation V (D.X (m + 2))] [Module.FinitePresentation V (D.X (m + 3))] :
    Module.Finite V (D.X (m + 1) ⧸ LinearMap.range (D.d m (m + 1)).hom) := by
  let S := D.sc' m (m + 1) (m + 2)
  let S' := D.sc' (m + 1) (m + 2) (m + 3)
  have : Module.Finite V S.homology :=
    Module.Finite.equiv (D.homologyIsoSc' m (m + 1) (m + 2) (by simp) (by simp)).toLinearEquiv
  have : Module.FinitePresentation V S'.homology :=
    Module.FinitePresentation.of_equiv
      (D.homologyIsoSc' (m + 1) (m + 2) (m + 3) (by simp) (by simp)).toLinearEquiv
  have : Module.FinitePresentation V S'.X₂ := ‹Module.FinitePresentation V (D.X (m + 2))›
  have : Module.FinitePresentation V S'.X₃ := ‹Module.FinitePresentation V (D.X (m + 3))›
  exact finite_quotient_range_f S (fg_range_f_valuation S')

/-- Over a valuation ring, `K⁰` is finitely generated if `H⁰(K)` is finitely generated and
`H¹(K)`, `K¹`, `K²` are finitely presented. -/
theorem finite_X_zero_valuation (K : CochainComplex (ModuleCat.{u} V) ℕ)
    [Module.Finite V (K.homology 0)] [Module.FinitePresentation V (K.homology 1)]
    [Module.FinitePresentation V (K.X 1)] [Module.FinitePresentation V (K.X 2)] :
    Module.Finite V (K.X 0) := by
  have hker : Module.Finite V (LinearMap.ker (K.d 0 1).hom) :=
    Module.Finite.equiv (nativeCochainZeroCocyclesIso K).toLinearEquiv.symm
  let S' := K.sc' 0 1 2
  have : Module.FinitePresentation V S'.homology :=
    Module.FinitePresentation.of_equiv (K.homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv
  have : Module.FinitePresentation V S'.X₂ := ‹Module.FinitePresentation V (K.X 1)›
  have : Module.FinitePresentation V S'.X₃ := ‹Module.FinitePresentation V (K.X 2)›
  have hr : (LinearMap.range (K.d 0 1).hom).FG := fg_range_f_valuation S'
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (K.d 0 1).hom ?_ ?_⟩
  · rw [Submodule.map_top]
    exact hr
  · rw [top_inf_eq]
    exact Module.Finite.iff_fg.mp hker

/-- The first term of a short exact sequence of modules over a valuation ring with finitely
presented middle and last terms is finitely presented. -/
theorem finitePresentation_X₁_of_shortExact {S : ShortComplex (ModuleCat.{u} V)}
    (hS : S.ShortExact) [Module.FinitePresentation V S.X₂] [Module.FinitePresentation V S.X₃] :
    Module.FinitePresentation V S.X₁ := by
  have := finitePresentation_ker_valuation S.g.hom
  have hrange : LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
    hS.exact.moduleCat_range_eq_ker
  exact Module.FinitePresentation.of_equiv
    ((LinearEquiv.ofInjective S.f.hom hS.moduleCat_injective_f).trans
      (LinearEquiv.ofEq _ _ hrange)).symm

omit [IsDomain V] [ValuationRing V] in
/-- **Replacement step over a valuation ring**: as `exists_replacement` (COH2), with the
finiteness of `D^{m+1}/B^{m+1}` as input. -/
theorem exists_replacement_valuation (D : CochainComplex (ModuleCat.{u} V) ℕ) (m : ℕ)
    (hflat : ∀ k, Module.Flat V (D.X k))
    [Module.Finite V (D.X (m + 1) ⧸ LinearMap.range (D.d m (m + 1)).hom)] :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ D), IsUnivQuasiIso g ∧
      (∀ k, Module.Flat V (K.X k)) ∧ Module.Finite V (K.X (m + 1)) ∧
      Module.Free V (K.X (m + 1)) ∧ ∀ k, k ≠ m → k ≠ m + 1 → IsIso (g.f k) := by
  obtain ⟨r, α, hsurj⟩ := exists_free_lift D m
  have : ∀ k, Module.Flat V (D.X k) := hflat
  let e := replTopEquiv (α := α) hsurj
  exact ⟨replComplex D m _ α, replHom D m _ α, isUnivQuasiIso_replHom hsurj,
    flat_replComplex_X hsurj, Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm,
    fun k h₀ h₁ => isIso_replHom_f hsurj h₀ h₁⟩

/-- **Perfect models over a valuation ring** (blueprint `lem:sm-val-perfect-model`): a bounded
complex of flat modules over a valuation ring, concentrated in degrees `≤ n`, with finitely
presented cohomology, receives a universal quasi-isomorphism from a complex of finite free
modules concentrated in degrees `≤ n`. -/
theorem exists_perfect_model_valuation (C : CochainComplex (ModuleCat.{u} V) ℕ) (n : ℕ)
    (hflat : ∀ k, Module.Flat V (C.X k)) (hzero : ∀ k, n < k → IsZero (C.X k))
    (hH : ∀ k, Module.FinitePresentation V (C.homology k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      ∀ k, n < k → IsZero (K.X k) := by
  have key : ∀ t, t ≤ n → ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ C),
      IsUnivQuasiIso g ∧ (∀ k, Module.Flat V (K.X k)) ∧
      (∀ k, n - t < k → Module.FinitePresentation V (K.X k)) ∧
      ∀ k, n < k → IsZero (K.X k) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨C, 𝟙 C, isUnivQuasiIso_of_isIso _, hflat, fun k hk => ?_, hzero⟩
      have : Subsingleton (C.X k) := ModuleCat.subsingleton_of_isZero (hzero k (by omega))
      exact Module.FinitePresentation.of_subsingleton _
    | succ t ih =>
      intro ht
      obtain ⟨K, g, hg, hKflat, hKfp, hKzero⟩ := ih (by omega)
      have := hg.1
      have hHK : ∀ k, Module.FinitePresentation V (K.homology k) := fun k =>
        have := hH k
        Module.FinitePresentation.of_equiv (isoOfQuasiIsoAt g k).symm.toLinearEquiv
      have : Module.FinitePresentation V (K.homology (n - (t + 1) + 1)) := hHK _
      have : Module.FinitePresentation V (K.homology (n - (t + 1) + 2)) := hHK _
      have : Module.FinitePresentation V (K.X (n - (t + 1) + 2)) := hKfp _ (by omega)
      have : Module.FinitePresentation V (K.X (n - (t + 1) + 3)) := hKfp _ (by omega)
      have := finite_quotient_range_d_valuation K (n - (t + 1))
      obtain ⟨K', g', hg', hflat', hfin', hfree', hiso'⟩ :=
        exists_replacement_valuation K (n - (t + 1)) hKflat
      refine ⟨K', g' ≫ g, hg'.comp hg, hflat', fun k hk => ?_, fun k hk => ?_⟩
      · by_cases hk1 : k = n - (t + 1) + 1
        · subst hk1
          exact Module.finitePresentation_of_projective V _
        · have := hiso' k (by omega) hk1
          have := hKfp k (by omega)
          exact Module.FinitePresentation.of_equiv (asIso (g'.f k)).toLinearEquiv.symm
      · have := hiso' k (by omega) (by omega)
        exact (hKzero k hk).of_iso (asIso (g'.f k))
  obtain ⟨K, g, hg, hKflat, hKfp, hKzero⟩ := key n le_rfl
  have := hg.1
  have hfin : ∀ k, Module.Finite V (K.X k) := by
    intro k
    cases k with
    | zero =>
      have : Module.Finite V (K.homology 0) := by
        have := hH 0
        exact Module.Finite.equiv (isoOfQuasiIsoAt g 0).symm.toLinearEquiv
      have : Module.FinitePresentation V (K.homology 1) := by
        have := hH 1
        exact Module.FinitePresentation.of_equiv (isoOfQuasiIsoAt g 1).symm.toLinearEquiv
      have : Module.FinitePresentation V (K.X 1) := hKfp 1 (by omega)
      have : Module.FinitePresentation V (K.X 2) := hKfp 2 (by omega)
      exact finite_X_zero_valuation K
    | succ k =>
      have := hKfp (k + 1) (by omega)
      infer_instance
  refine ⟨K, g, hg, hfin, fun k => ?_, hKzero⟩
  have := hfin k
  have := hKflat k
  exact Module.free_of_flat_of_isLocalRing

omit [IsDomain V] [ValuationRing V] in
/-- Finite presentation of the terms of a double complex `X --𝟙--> X`. -/
lemma finitePresentation_double_X (X : ModuleCat.{u} V) [Module.FinitePresentation V X]
    (m k : ℕ) :
    Module.FinitePresentation V ((HomologicalComplex.double (𝟙 X) (rel_succ m)).X k) := by
  by_cases h₀ : k = m
  · subst h₀
    exact Module.FinitePresentation.of_equiv
      (HomologicalComplex.doubleXIso₀ (𝟙 X) (rel_succ k)).symm.toLinearEquiv
  · by_cases h₁ : k = m + 1
    · subst h₁
      exact Module.FinitePresentation.of_equiv
        (HomologicalComplex.doubleXIso₁ (𝟙 X) (rel_succ m) (succ_ne m)).symm.toLinearEquiv
    · have : Subsingleton ((HomologicalComplex.double (𝟙 X) (rel_succ m)).X k) :=
        ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_double_X _ _ k h₀ h₁)
      exact Module.FinitePresentation.of_subsingleton _

/-- **Truncation over a valuation ring**: a bounded complex of finite free modules over a valuation
ring with `K^i = 0` for `i > q + 1` and `H^{q+1}(K) = 0` receives a universal quasi-isomorphism
from a complex of finite free modules concentrated in degrees `≤ q`. -/
theorem exists_truncation_valuation (K : CochainComplex (ModuleCat.{u} V) ℕ) (q : ℕ)
    (hfin : ∀ k, Module.Finite V (K.X k)) (hfree : ∀ k, Module.Free V (K.X k))
    (hzero : ∀ k, q + 1 < k → IsZero (K.X k)) (hH : IsZero (K.homology (q + 1))) :
    ∃ (K' : CochainComplex (ModuleCat.{u} V) ℕ) (g : K' ⟶ K), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite V (K'.X k)) ∧ (∀ k, Module.Free V (K'.X k)) ∧
      ∀ k, q < k → IsZero (K'.X k) := by
  let P : ModuleCat.{u} V := ModuleCat.of V (Fin 0 → V)
  let α : P ⟶ K.X (q + 1) := 0
  have hsurj : ∀ y : K.X (q + 1), ∃ (p : P) (x : K.X q), α p + K.d q (q + 1) x = y := by
    intro y
    obtain ⟨x, hx⟩ := (isZero_homology_succ_iff K q).mp hH y
      (eq_zero_of_isZero (hzero (q + 2) (by omega)) _)
    exact ⟨0, x, by rw [map_zero, zero_add]; exact hx⟩
  have hfp : ∀ k, Module.FinitePresentation V (K.X k) := fun k => by
    have := hfin k
    have := hfree k
    exact Module.finitePresentation_of_projective V _
  have hflat : ∀ k, Module.Flat V (K.X k) := fun k => by
    have := hfree k
    infer_instance
  have := hflat (q + 1)
  have hflatK' := flat_replComplex_X (P := P) (α := α) hsurj
  have hfpK' : ∀ k, Module.FinitePresentation V ((replComplex K q P α).X k) := by
    intro k
    have hS := shortExact_replSES_X hsurj k
    have := hfp k
    have : Module.FinitePresentation V ((replAux q P).X k) := finitePresentation_double_X P q k
    have : Module.FinitePresentation V ((replTarget K q).X k) :=
      finitePresentation_double_X (K.X (q + 1)) q k
    have h₂ : Module.FinitePresentation V ((K ⊞ replAux q P).X k) :=
      Module.FinitePresentation.of_equiv ((HomologicalComplex.biprodXIso K (replAux q P) k) ≪≫
        ModuleCat.biprodIsoProd (K.X k) ((replAux q P).X k)).symm.toLinearEquiv
    have : Module.FinitePresentation V
        ((replSES K q P α).map (HomologicalComplex.eval _ _ k)).X₂ := h₂
    have : Module.FinitePresentation V
        ((replSES K q P α).map (HomologicalComplex.eval _ _ k)).X₃ :=
      ‹Module.FinitePresentation V ((replTarget K q).X k)›
    exact finitePresentation_X₁_of_shortExact hS
  let e := replTopEquiv hsurj
  have hzero' : IsZero ((replComplex K q P α).X (q + 1)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact e.toEquiv.subsingleton
  refine ⟨replComplex K q P α, replHom K q P α, isUnivQuasiIso_replHom hsurj,
    fun k => by have := hfpK' k; infer_instance, fun k => ?_, fun k hk => ?_⟩
  · have := hfpK' k
    have := hflatK' k
    exact Module.free_of_flat_of_isLocalRing
  · by_cases hk1 : k = q + 1
    · subst hk1
      exact hzero'
    · have := isIso_replHom_f hsurj (k := k) (by omega) hk1
      exact (hzero k (by omega)).of_iso (asIso ((replHom K q P α).f k))

/-- **Perfect models in degrees `≤ q` over a valuation ring** (blueprint
`lem:sm-val-perfect-model`): if in `exists_perfect_model_valuation` moreover `Hⁱ(C) = 0` for
`i > q`, the model can be taken in degrees `≤ q`. -/
theorem exists_perfect_model_le_valuation (C : CochainComplex (ModuleCat.{u} V) ℕ) (n q : ℕ)
    (hflat : ∀ k, Module.Flat V (C.X k)) (hzero : ∀ k, n < k → IsZero (C.X k))
    (hH : ∀ k, Module.FinitePresentation V (C.homology k))
    (hvan : ∀ k, q < k → IsZero (C.homology k)) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      ∀ k, q < k → IsZero (K.X k) := by
  obtain ⟨K₀, g₀, hg₀, hfin₀, hfree₀, hzero₀⟩ := exists_perfect_model_valuation C n hflat hzero hH
  have key : ∀ j, ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (g : K ⟶ C), IsUnivQuasiIso g ∧
      (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      ∀ k, q + (n - j) < k → IsZero (K.X k) := by
    intro j
    induction j with
    | zero => exact ⟨K₀, g₀, hg₀, hfin₀, hfree₀, fun k hk => hzero₀ k (by omega)⟩
    | succ j ih =>
      obtain ⟨K, g, hg, hfin, hfree, hzeroK⟩ := ih
      by_cases hj : n - j = 0
      · exact ⟨K, g, hg, hfin, hfree, fun k hk => hzeroK k (by omega)⟩
      · have := hg.1
        have hH' : IsZero (K.homology (q + (n - (j + 1)) + 1)) :=
          (hvan _ (by omega)).of_iso (isoOfQuasiIsoAt g _)
        obtain ⟨K', g', hg', hfin', hfree', hzero'⟩ :=
          exists_truncation_valuation K (q + (n - (j + 1))) hfin hfree
            (fun k hk => hzeroK k (by omega)) hH'
        exact ⟨K', g' ≫ g, hg'.comp hg, hfin', hfree', hzero'⟩
  obtain ⟨K, g, hg, hfin, hfree, hzeroK⟩ := key n
  exact ⟨K, g, hg, hfin, hfree, fun k hk => hzeroK k (by omega)⟩

end Valuation

end

end DeJongAlterations.StableModification.Cohomology
