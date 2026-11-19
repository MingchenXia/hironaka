/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.SymmetricAlgebra.Defs
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The standard charts of `Proj Sym M` and their base change

For an `R`-module `M` and `x₀ ∈ M`, the chart `D₊(x₀)` of `Proj (Sym_R M)` is `Spec` of the
degree-zero part `(Sym M)_(x₀)` of the localization at `x₀ ∈ Sym¹ M`. Every element of it is a
fraction `a / x₀ⁿ` with `a ∈ Symⁿ M`, and `a / x₀ⁿ` is the value at `a` of the *dehomogenization*
`SymmetricAlgebra.dehom : Sym M → (Sym M)_(x₀)`, the ring map with `ι x ↦ x / x₀`
(`SymmetricAlgebra.val_dehom_of_mem`, `SymmetricAlgebra.dehom_surjective`). So a ring map out of
the chart is determined by its values on the fractions `x / x₀`, and every `R`-linear map
`g : M → T` to a commutative `R`-algebra with `g x₀ = 1` is such a family of values
(`SymmetricAlgebra.awayLift`): the chart is the free commutative `R`-algebra on `M` with `x₀ = 1`.

From this universal property the chart commutes with base change: for a ring map `φ : R → S` and a
`φ`-semilinear map `f : M → N` that exhibits `N` as `S ⊗_R M` (every `φ`-semilinear map out of `M`
extends to an `S`-linear map out of `N`, and `f(M)` spans `N`), the square of rings
`R → (Sym_R M)_(x₀)`, `S → (Sym_S N)_(f x₀)` is a pushout (`SymmetricAlgebra.isPushout_away`): both
corners have the universal property of `S`-algebras with an `R`-linear map from `M` sending `x₀`
to `1` [Sta, Tag 01N2].
-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace SymmetricAlgebra

section Basic

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

theorem ι_mem_grading_one (x : M) : ι R M x ∈ grading R M 1 := by
  simpa only [grading, pow_one] using LinearMap.mem_range_self _ x

theorem algebraMap_mem_grading_zero (r : R) :
    algebraMap R (SymmetricAlgebra R M) r ∈ grading R M 0 := by
  rw [grading, pow_zero]
  exact Submodule.algebraMap_mem r

/-- Two ring maps out of `Sym_R M` that agree on the constants and on `ι(M)` are equal. -/
theorem ringHom_ext {T : Type*} [Semiring T] {F G : SymmetricAlgebra R M →+* T}
    (h₁ : ∀ r, F (algebraMap R _ r) = G (algebraMap R _ r)) (h₂ : ∀ x, F (ι R M x) = G (ι R M x)) :
    F = G := by
  refine RingHom.ext fun a =>
    SymmetricAlgebra.induction (R := R) (M := M) (motive := fun a => F a = G a) h₁ h₂
    (fun a b ha hb => ?_) (fun a b ha hb => ?_) a
  · rw [map_mul, map_mul, ha, hb]
  · rw [map_add, map_add, ha, hb]

/-- The ring map `Sym_R M → T` of a ring map `ψ : R → T` and a `ψ`-semilinear additive map
`g : M → T`: the lift of `g` for the `R`-algebra structure of `T` along `ψ`. -/
noncomputable def liftₛₗ {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) : SymmetricAlgebra R M →+* T :=
  letI := ψ.toAlgebra
  (lift { toFun := g, map_add' := g.map_add, map_smul' := fun r x => (hg r x).trans rfl } :
    SymmetricAlgebra R M →ₐ[R] T).toRingHom

theorem liftₛₗ_ι {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (x : M) : liftₛₗ ψ g hg (ι R M x) = g x := by
  let := ψ.toAlgebra
  exact lift_ι_apply _ x

theorem liftₛₗ_algebraMap {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (r : R) :
    liftₛₗ ψ g hg (algebraMap R _ r) = ψ r := by
  let := ψ.toAlgebra
  exact AlgHom.commutes _ r

variable {S : Type u} {N : Type u} [CommRing S] [AddCommGroup N] [Module S N]

theorem gradedMap_ι (φ : R →+* S) (f : M →ₛₗ[φ] N) (x : M) :
    gradedMap φ f (ι R M x) = ι S N (f x) := by
  let := algebraOfRingHom (N := N) φ
  exact lift_ι_apply (ιₛₗ φ f) x

theorem gradedMap_algebraMap (φ : R →+* S) (f : M →ₛₗ[φ] N) (r : R) :
    gradedMap φ f (algebraMap R _ r) = algebraMap S _ (φ r) := by
  let := algebraOfRingHom (N := N) φ
  exact AlgHom.commutes (lift (ιₛₗ φ f)) r

end Basic

section Dehomogenize

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The constants `R → (Sym M)_(e)`: `R ≅ Sym⁰ M` followed by `r ↦ r / 1`. -/
noncomputable def toAway (e : SymmetricAlgebra R M) : R →+* Away (grading R M) e :=
  (fromZeroRingHom (grading R M) _).comp (algebraMap R (grading R M 0))

theorem val_toAway (e : SymmetricAlgebra R M) (r : R) :
    (toAway e r).val = Localization.mk (algebraMap R _ r) 1 :=
  rfl

variable (e : SymmetricAlgebra R M) (x₀ : M) (he : ι R M x₀ = e)
include he

theorem e_mem_grading_one : e ∈ grading R M 1 := he ▸ ι_mem_grading_one x₀

/-- The fraction `x / x₀` of the chart `(Sym M)_(x₀)`, for `x ∈ M`. -/
noncomputable def frac (x : M) : Away (grading R M) e :=
  Away.mk (grading R M) (e_mem_grading_one e x₀ he) 1 (ι R M x)
    (by simpa only [smul_eq_mul, mul_one] using ι_mem_grading_one x)

theorem val_frac (x : M) :
    (frac e x₀ he x).val = Localization.mk (ι R M x) ⟨e, Submonoid.mem_powers e⟩ := by
  rw [frac, Away.val_mk]
  exact congrArg (Localization.mk _) (Subtype.ext (pow_one e))

/-- **The dehomogenization** `Sym M → (Sym M)_(x₀)`, `ι x ↦ x / x₀`, the ring map whose value at
`a ∈ Symⁿ M` is the fraction `a / x₀ⁿ` (`val_dehom_of_mem`). -/
noncomputable def dehom : SymmetricAlgebra R M →+* Away (grading R M) e :=
  liftₛₗ (toAway e)
    { toFun := frac e x₀ he
      map_zero' := val_injective _ (by rw [val_frac, map_zero, Localization.mk_zero, val_zero])
      map_add' := fun x y => val_injective _ (by
        rw [val_add, val_frac, val_frac, val_frac, map_add, Localization.add_mk_self]) }
    fun r x => val_injective _ (by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, val_mul, val_frac, val_toAway,
        Localization.mk_mul, one_mul, LinearMap.map_smul, Algebra.smul_def])

theorem dehom_ι (x : M) : dehom e x₀ he (ι R M x) = frac e x₀ he x :=
  liftₛₗ_ι _ _ _ x

theorem dehom_algebraMap (r : R) : dehom e x₀ he (algebraMap R _ r) = toAway e r :=
  liftₛₗ_algebraMap _ _ _ r

theorem dehom_e : dehom e x₀ he e = 1 := by
  refine (congrArg (dehom e x₀ he) he.symm).trans ?_
  rw [dehom_ι]
  refine val_injective _ ?_
  rw [val_frac, val_one, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [he]⟩

/-- The value of the dehomogenization at `a ∈ Symⁿ M` is `a / x₀ⁿ`. -/
theorem val_dehom_of_mem {n : ℕ} {a : SymmetricAlgebra R M} (ha : a ∈ grading R M n) :
    (dehom e x₀ he a).val =
      Localization.mk a ⟨e ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers e) n⟩ := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [dehom_algebraMap, val_toAway]
    congr 1
    exact Subtype.ext (pow_zero e).symm
  | add x y i hx hy ihx ihy =>
    rw [map_add, val_add, ihx, ihy, Localization.add_mk_self]
  | mem_mul m hm i a ha ih =>
    obtain ⟨x, rfl⟩ := hm
    rw [map_mul, val_mul, ih, dehom_ι, val_frac, Localization.mk_mul]
    congr 1
    exact Subtype.ext (pow_succ' e i).symm

theorem dehom_surjective : Function.Surjective (dehom e x₀ he) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading R M) (e_mem_grading_one e x₀ he) z
  have ha' : a ∈ grading R M n := by simpa only [smul_eq_mul, mul_one] using ha
  exact ⟨a, val_injective _ (by rw [val_dehom_of_mem e x₀ he ha', Away.val_mk])⟩

/-- Ring maps out of the chart `(Sym M)_(x₀)` are determined by their values on the fractions
`x / x₀` and on the constants. -/
theorem away_ringHom_ext {T : Type*} [Semiring T] {F G : Away (grading R M) e →+* T}
    (h₁ : ∀ r, F (toAway e r) = G (toAway e r))
    (h₂ : ∀ x, F (dehom e x₀ he (ι R M x)) = G (dehom e x₀ he (ι R M x))) : F = G := by
  have : F.comp (dehom e x₀ he) = G.comp (dehom e x₀ he) :=
    ringHom_ext (fun r => by simpa [dehom_algebraMap] using h₁ r) h₂
  ext z
  obtain ⟨a, rfl⟩ := dehom_surjective e x₀ he z
  exact RingHom.congr_fun this a

omit he in
/-- The lift through the localization at `e` of a ring map sending `e` to `1` sends `a / eⁿ` to the
image of `a`. -/
theorem awayLift_mk_of_eq_one {T : Type*} [CommRing T] (L : SymmetricAlgebra R M →+* T)
    (hu : L e = 1) (hunit : IsUnit (L e)) (a : SymmetricAlgebra R M) (s : Submonoid.powers e) :
    Localization.awayLift L e hunit (Localization.mk a s) = L a := by
  obtain ⟨_, n, rfl⟩ := s
  rw [Localization.mk_eq_mk']
  exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (by simp [map_pow, hu])

/-- **The universal property of the chart**: a ring map `ψ : R → T` and a `ψ`-semilinear additive
map `g : M → T` with `g x₀ = 1` define the ring map `(Sym M)_(x₀) → T`, `x / x₀ ↦ g x`: the lift
of `g` to `Sym M`, which sends `x₀` to the unit `1`, through the localization at `x₀`. -/
noncomputable def awayLift {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (h₀ : g x₀ = 1) :
    Away (grading R M) e →+* T :=
  (Localization.awayLift (liftₛₗ ψ g hg) e (by rw [← he, liftₛₗ_ι, h₀]; exact isUnit_one)).comp
    (algebraMap (Away (grading R M) e) (Localization.Away e))

theorem awayLift_dehom {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (h₀ : g x₀ = 1) (a : SymmetricAlgebra R M) :
    awayLift e x₀ he ψ g hg h₀ (dehom e x₀ he a) = liftₛₗ ψ g hg a := by
  have hu : liftₛₗ ψ g hg e = 1 := by rw [← he, liftₛₗ_ι, h₀]
  refine RingHom.congr_fun (ringHom_ext (F := (awayLift e x₀ he ψ g hg h₀).comp (dehom e x₀ he))
    (G := liftₛₗ ψ g hg) (fun r => ?_) (fun x => ?_)) a
  · simp only [RingHom.comp_apply, awayLift, dehom_algebraMap, algebraMap_apply, val_toAway]
    exact awayLift_mk_of_eq_one e _ hu _ _ _
  · simp only [RingHom.comp_apply, awayLift, dehom_ι, algebraMap_apply, val_frac]
    exact awayLift_mk_of_eq_one e _ hu _ _ _

theorem awayLift_toAway {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (h₀ : g x₀ = 1) (r : R) :
    awayLift e x₀ he ψ g hg h₀ (toAway e r) = ψ r := by
  rw [← dehom_algebraMap e x₀ he, awayLift_dehom, liftₛₗ_algebraMap]

theorem awayLift_frac {T : Type*} [CommRing T] (ψ : R →+* T) (g : M →+ T)
    (hg : ∀ (r : R) (x : M), g (r • x) = ψ r * g x) (h₀ : g x₀ = 1) (x : M) :
    awayLift e x₀ he ψ g hg h₀ (dehom e x₀ he (ι R M x)) = g x := by
  rw [awayLift_dehom, liftₛₗ_ι]

end Dehomogenize

section BaseChange

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} {N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
variable (φ : R →+* S) (f : M →ₛₗ[φ] N) (x₀ : M)

theorem awayMap_toAway (r : R) :
    Away.map (gradedMap φ f) (ι R M x₀) (toAway (ι R M x₀) r) =
      toAway (gradedMap φ f (ι R M x₀)) (φ r) := by
  change HomogeneousLocalization.map (gradedMap φ f) _
      (HomogeneousLocalization.mk ⟨0, algebraMap R (grading R M 0) r, 1, one_mem _⟩) =
    HomogeneousLocalization.mk ⟨0, algebraMap S (grading S N 0) (φ r), 1, one_mem _⟩
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.ext_iff_val, val_mk, val_mk]
  congr 1
  · exact gradedMap_algebraMap φ f r
  · exact Subtype.ext (map_one _)

theorem awayMap_frac (x : M) :
    Away.map (gradedMap φ f) (ι R M x₀) (frac (ι R M x₀) x₀ rfl x) =
      frac (gradedMap φ f (ι R M x₀)) (f x₀) (gradedMap_ι φ f x₀).symm (f x) := by
  refine val_injective _ ?_
  rw [val_frac, frac, Away.map_mk, Away.val_mk]
  congr 1
  · exact gradedMap_ι φ f x
  · exact Subtype.ext (pow_one _)

/-- The dehomogenizations commute with the graded map of symmetric algebras. -/
theorem awayMap_dehom (a : SymmetricAlgebra R M) :
    Away.map (gradedMap φ f) (ι R M x₀) (dehom (ι R M x₀) x₀ rfl a) =
      dehom (gradedMap φ f (ι R M x₀)) (f x₀) (gradedMap_ι φ f x₀).symm (gradedMap φ f a) := by
  refine RingHom.congr_fun (ringHom_ext
    (F := (Away.map (gradedMap φ f) (ι R M x₀)).comp (dehom (ι R M x₀) x₀ rfl))
    (G := (dehom (gradedMap φ f (ι R M x₀)) (f x₀) (gradedMap_ι φ f x₀).symm).comp
      (gradedMap φ f).toRingHom) (fun r => ?_) (fun x => ?_)) a
  · simp only [RingHom.comp_apply, dehom_algebraMap, awayMap_toAway]
    rw [GradedRingHom.coe_toRingHom, gradedMap_algebraMap, dehom_algebraMap]
  · simp only [RingHom.comp_apply, dehom_ι, awayMap_frac]
    rw [GradedRingHom.coe_toRingHom, gradedMap_ι φ f x, dehom_ι]

/-- **The chart of `Proj Sym M` commutes with base change** [Sta, Tag 01N2]: if
`f : M → N` is `φ`-semilinear, its image spans `N`, and every `φ`-semilinear map out of `M`
extends along `f` to an `S`-linear map out of `N` (so that `N = S ⊗_R M`), the square
`R → S`, `R → (Sym_R M)_(x₀)`, `S → (Sym_S N)_(f x₀)`, `(Sym_R M)_(x₀) → (Sym_S N)_(f x₀)` is a
pushout of rings. Both ways round, a ring map out of the corner is a ring map `b` out of `S` with
an additive map `N → T` (or `M → T`), semilinear along `b` (or `b ∘ φ`), sending `f x₀` (or `x₀`) to
`1` (`awayLift`); the extension property turns the second kind into the first, and the spanning
property makes the extension unique. -/
theorem isPushout_away (hspan : Submodule.span S (Set.range f) = ⊤)
    (hext : ∀ (T : Type u) [AddCommGroup T] [Module S T] (g : M →ₛₗ[φ] T),
      ∃ g' : N →ₗ[S] T, ∀ x, g' (f x) = g x) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (toAway (ι R M x₀)))
      (CommRingCat.ofHom (toAway (gradedMap φ f (ι R M x₀))))
      (CommRingCat.ofHom (Away.map (gradedMap φ f) (ι R M x₀))) := by
  set e' := gradedMap φ f (ι R M x₀)
  have he' : ι S N (f x₀) = e' := (gradedMap_ι φ f x₀).symm
  have hsq : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (toAway e') =
      CommRingCat.ofHom (toAway (ι R M x₀)) ≫
        CommRingCat.ofHom (Away.map (gradedMap φ f) (ι R M x₀)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (awayMap_toAway φ f x₀ r).symm
  -- For a cocone `(b, a)`, the semilinear map `x ↦ a (x / x₀)` and its extension along `f`.
  let gR (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) :
      letI := s.inl.hom.toModule
      M →ₛₗ[φ] s.pt :=
    letI := s.inl.hom.toModule
    { toFun := fun x => s.inr.hom (dehom (ι R M x₀) x₀ rfl (ι R M x))
      map_add' := fun x y => by rw [map_add, map_add, map_add]
      map_smul' := fun r x => by
        rw [LinearMap.map_smul, Algebra.smul_def, map_mul, map_mul, dehom_algebraMap]
        change _ = s.inl.hom (φ r) * _
        congr 1
        exact (congrArg (fun h => h.hom r) s.condition).symm }
  let gN (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) :
      letI := s.inl.hom.toModule
      N →ₗ[S] s.pt :=
    letI := s.inl.hom.toModule
    Classical.choose (hext s.pt (gR s))
  have hgN (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) (x : M) :
      gN s (f x) = s.inr.hom (dehom (ι R M x₀) x₀ rfl (ι R M x)) :=
    letI := s.inl.hom.toModule
    Classical.choose_spec (hext s.pt (gR s)) x
  have hsmul (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) (c : S) (n : N) :
      (gN s).toAddMonoidHom (c • n) = s.inl.hom c * (gN s).toAddMonoidHom n :=
    letI := s.inl.hom.toModule
    (gN s).map_smul c n
  have h₀ (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) : (gN s).toAddMonoidHom (f x₀) = 1 := by
    change gN s (f x₀) = 1
    rw [hgN, dehom_e, map_one]
  let desc (s : Limits.PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (toAway (ι R M x₀)))) :
      CommRingCat.of (Away (grading S N) e') ⟶ s.pt :=
    CommRingCat.ofHom (awayLift e' (f x₀) he' s.inl.hom (gN s).toAddMonoidHom
      (hsmul s) (h₀ s))
  refine IsPushout.of_isColimit (Limits.PushoutCocone.IsColimit.mk hsq desc
    (fun s => ?_) (fun s => ?_) (fun s m hl hr => ?_))
  · ext c
    exact awayLift_toAway e' (f x₀) he' _ _ (hsmul s) (h₀ s) c
  · refine CommRingCat.hom_ext (away_ringHom_ext (ι R M x₀) x₀ rfl (fun r => ?_) (fun x => ?_))
    · change desc s (Away.map (gradedMap φ f) (ι R M x₀) (toAway (ι R M x₀) r)) =
        s.inr.hom (toAway (ι R M x₀) r)
      rw [awayMap_toAway]
      change awayLift e' (f x₀) he' _ _ (hsmul s) (h₀ s) (toAway e' (φ r)) = _
      rw [awayLift_toAway]
      exact congrArg (fun h => h.hom r) s.condition
    · change desc s (Away.map (gradedMap φ f) (ι R M x₀) (dehom (ι R M x₀) x₀ rfl (ι R M x))) =
        s.inr.hom (dehom (ι R M x₀) x₀ rfl (ι R M x))
      rw [awayMap_dehom, gradedMap_ι φ f x]
      change awayLift e' (f x₀) he' _ _ (hsmul s) (h₀ s)
        (dehom e' (f x₀) he' (ι S N (f x))) = _
      rw [awayLift_frac]
      exact hgN s x
  · refine CommRingCat.hom_ext (away_ringHom_ext e' (f x₀) he' (fun c => ?_) (fun n => ?_))
    · change m.hom (toAway e' c) = desc s (toAway e' c)
      rw [show desc s (toAway e' c) = s.inl.hom c from
        awayLift_toAway e' (f x₀) he' _ _ (hsmul s) (h₀ s) c]
      exact congrArg (fun h => h.hom c) hl
    · change m.hom (dehom e' (f x₀) he' (ι S N n)) = desc s (dehom e' (f x₀) he' (ι S N n))
      rw [show desc s (dehom e' (f x₀) he' (ι S N n)) = gN s n from
        awayLift_frac e' (f x₀) he' _ _ (hsmul s) (h₀ s) n]
      have hn : n ∈ Submodule.span S (Set.range f) := hspan ▸ Submodule.mem_top
      induction hn using Submodule.span_induction with
      | mem n hn =>
        obtain ⟨x, rfl⟩ := hn
        rw [hgN, ← gradedMap_ι, ← awayMap_dehom]
        exact congrArg (fun h => h.hom (dehom (ι R M x₀) x₀ rfl (ι R M x))) hr
      | zero => rw [map_zero, map_zero, map_zero, map_zero]
      | add n n' _ _ hn hn' => rw [map_add, map_add, map_add, hn, hn', map_add]
      | smul c n _ hn =>
        change _ = (gN s).toAddMonoidHom (c • n)
        rw [hsmul, LinearMap.map_smul, Algebra.smul_def, map_mul, map_mul, dehom_algebraMap, hn]
        congr 1
        exact congrArg (fun h => h.hom c) hl

end BaseChange

end SymmetricAlgebra
