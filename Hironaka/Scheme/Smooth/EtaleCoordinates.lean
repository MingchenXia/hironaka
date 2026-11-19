/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
public import Hironaka.Algebra.RegularSmooth.Stalk
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Algebra.Smooth.EtaleCriterion
import Hironaka.Algebra.Smooth.SpreadOut

/-!
# Étale coordinates: the coordinate morphism `U ⟶ 𝔸ⁿ_k`

`toAffineSpace f U v : U ⟶ 𝔸ⁿ_k = Spec k[t]` is `U.toSpecΓ ≫ Spec (aeval v)`. This module relates
its properties to the ring map `k[t] → Γ(X, U)`, `t_i ↦ v_i`:

* for `U` affine, `toAffineSpace f U v` is étale iff `aeval v` is an étale ring map
  (`etale_toAffineSpace_iff`; `U.toSpecΓ` is an isomorphism and `Etale` is a property of ring
  maps, Mathlib's `HasRingHomProperty`);
* restriction to a smaller open `U' ≤ U` composes with the inclusion `U' ⟶ U`
  (`homOfLE_toAffineSpace`), so étaleness passes to smaller opens (`etale_toAffineSpace_restrict`);
* the `k`-algebra structures `Scheme.Hom.sectionsAlgebra` on `Γ(X, U)` and `Γ(X, U')` form a
  scalar tower with the restriction map (`isScalarTower_sectionsAlgebra_restrict`);
* sections `v` of an affine open `V ∋ x` whose differentials at `x` form a basis of
  `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` are étale coordinates on a smaller affine open `U ∋ x`
  (`exists_etale_toAffineSpace_of_basis`), the argument of [Sta, Tag 054L] in given coordinates:
  on a standard smooth affine open the `d v_i` generate `Ω` at the stalk, hence, by Nakayama
  spread out along a basic open (`Hironaka/Algebra/Smooth/SpreadOut.lean`), on an affine
  neighbourhood, where the étale criterion `etale_aeval_of_span_eq_top`
  (`Hironaka/Algebra/Smooth/EtaleCriterion.lean`) applies.

These are the tools with which étale coordinates are produced throughout `Hironaka/Smooth/`.
-/

@[expose] public section

namespace AlgebraicGeometry

open Algebra

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section Restrict

variable {U U' : X.Opens} (h : U' ≤ U)

/-- The restriction map `Γ(X, U) → Γ(X, U')` as an algebra structure (local use). -/
noncomputable abbrev restrictAlgebra : Algebra Γ(X, U) Γ(X, U') :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- `k → Γ(X, U) → Γ(X, U')` is a scalar tower for the structures induced by `f`. -/
theorem isScalarTower_sectionsAlgebra_restrict :
    letI := f.sectionsAlgebra U
    letI := f.sectionsAlgebra U'
    letI := restrictAlgebra (X := X) h
    IsScalarTower k Γ(X, U) Γ(X, U') := by
  let _ := f.sectionsAlgebra U
  let _ := f.sectionsAlgebra U'
  let _ := restrictAlgebra (X := X) h
  refine IsScalarTower.of_algebraMap_eq' ?_
  have e := Scheme.Hom.appLE_map f (U := ⊤) (V := U) (V' := U') le_top (homOfLE h).op
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U' le_top).hom =
    (X.presheaf.map (homOfLE h).op).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  rw [← CommRingCat.hom_comp, Category.assoc, e]

end Restrict

section Points

variable {U : X.Opens} {x : X}

/-- Membership in the basic open of `s` at a point of an affine open, through the prime of the
point. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf (hU : IsAffineOpen U) (hx : x ∈ U) (s : Γ(X, U)) :
    x ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  rw [X.mem_basicOpen s x hx]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

end Points

section Etale

variable {n : ℕ}

/-- For `U` affine, the coordinate morphism is étale iff the ring map `k[t] → Γ(X, U)`,
`t_i ↦ v_i`, is étale. -/
theorem etale_toAffineSpace_iff {U : X.Opens} (hU : IsAffineOpen U) (v : Fin n → Γ(X, U)) :
    Etale (toAffineSpace f U v) ↔
      letI := f.sectionsAlgebra U
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  let _ := f.sectionsAlgebra U
  have : IsIso U.toSpecΓ := hU.isoSpec_hom ▸ inferInstance
  unfold toAffineSpace
  refine Iff.trans ?_ (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom))
  constructor
  · intro h
    have : Etale (inv U.toSpecΓ ≫
        (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom))) :=
      inferInstance
    rwa [IsIso.inv_hom_id_assoc] at this
  · intro h
    infer_instance

/-- The coordinate morphism restricted to a smaller open is the coordinate morphism of the
restricted sections. -/
theorem homOfLE_toAffineSpace {U U' : X.Opens} (h : U' ≤ U) (v : Fin n → Γ(X, U)) :
    X.homOfLE h ≫ toAffineSpace f U v =
      toAffineSpace f U' fun i => X.presheaf.map (homOfLE h).op (v i) := by
  let _ := f.sectionsAlgebra U
  let _ := f.sectionsAlgebra U'
  let _ := restrictAlgebra (X := X) h
  have := isScalarTower_sectionsAlgebra_restrict f h
  have e : CommRingCat.ofHom (MvPolynomial.aeval (R := k) v).toRingHom ≫
      X.presheaf.map (homOfLE h).op =
      CommRingCat.ofHom (MvPolynomial.aeval (R := k)
        fun i => X.presheaf.map (homOfLE h).op (v i)).toRingHom := by
    ext1
    apply MvPolynomial.ringHom_ext
    · intro c
      change X.presheaf.map (homOfLE h).op (MvPolynomial.aeval v (MvPolynomial.C c)) =
        MvPolynomial.aeval (fun i => X.presheaf.map (homOfLE h).op (v i)) (MvPolynomial.C c)
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k Γ(X, U) Γ(X, U') c).symm
    · intro j
      change X.presheaf.map (homOfLE h).op (MvPolynomial.aeval v (MvPolynomial.X j)) =
        MvPolynomial.aeval (fun i => X.presheaf.map (homOfLE h).op (v i)) (MvPolynomial.X j)
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  unfold toAffineSpace
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U' U h, Category.assoc,
    ← Spec.map_comp, e]

/-- Étaleness of the coordinate morphism passes to smaller opens. -/
theorem etale_toAffineSpace_restrict {U U' : X.Opens} (h : U' ≤ U) (v : Fin n → Γ(X, U))
    [Etale (toAffineSpace f U v)] :
    Etale (toAffineSpace f U' fun i => X.presheaf.map (homOfLE h).op (v i)) := by
  rw [← homOfLE_toAffineSpace]
  infer_instance

end Etale

section Assembly

open KaehlerDifferential _root_.TensorProduct IsLocalRing

variable (n : ℕ) [SmoothOfRelativeDimension n f]

omit [SmoothOfRelativeDimension n f] in
/-- A basic open of an affine open on which `X` is standard smooth of relative dimension `n` over
`k` is again standard smooth of relative dimension `n` (localization away from a section is
standard smooth of relative dimension `0`). -/
theorem isStandardSmoothOfRelativeDimension_basicOpen {U : X.Opens} (hU : IsAffineOpen U)
    (t : Γ(X, U))
    (hstd : letI := f.sectionsAlgebra U; Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U)) :
    letI := f.sectionsAlgebra (X.basicOpen t)
    Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, X.basicOpen t) := by
  let _ := f.sectionsAlgebra U
  let _ := f.sectionsAlgebra (X.basicOpen t)
  let _ := restrictAlgebra (X := X) (X.basicOpen_le t)
  have := isScalarTower_sectionsAlgebra_restrict f (X.basicOpen_le t)
  have hloc : IsLocalization.Away t Γ(X, X.basicOpen t) :=
    hU.isLocalization_of_eq_basicOpen t (homOfLE (X.basicOpen_le t)) rfl
  have h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 Γ(X, U) Γ(X, X.basicOpen t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away t
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := n) (m := 0) (R := k)
    (S := Γ(X, U)) (T := Γ(X, X.basicOpen t))
  rwa [zero_add] at h

omit [SmoothOfRelativeDimension n f] in
/-- The instances of the étale criterion for a standard smooth algebra of relative dimension `n`
(free `Ω` of rank `n`, formally smooth, of finite presentation). -/
theorem etale_aeval_of_isStandardSmoothOfRelativeDimension {S : Type u} [CommRing S] [Algebra k S]
    [Nontrivial S] [Algebra.IsStandardSmoothOfRelativeDimension n k S] (v : Fin n → S)
    (hspan : Submodule.span S (Set.range fun i => D k S (v i)) = ⊤) :
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have hrank : Module.finrank S Ω[S⁄k] = n :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) n)
  exact etale_aeval_of_span_eq_top v hrank hspan

/-- Sections `v` of an affine open `V ∋ x` whose differentials at `x` form a basis of
`κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` are étale coordinates on a smaller affine open `U ∋ x` (the argument of
[Sta, Tag 054L] in given coordinates). -/
theorem exists_etale_toAffineSpace_of_basis {x : X} (V : X.affineOpens) (hxV : x ∈ V.1)
    (v : Fin n → Γ(X, V.1))
    (hb : letI := f.stalkAlgebra x
      ∃ b : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
          (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
        ∀ i, b i = 1 ⊗ₜ D k (X.presheaf.stalk x) (X.presheaf.germ V.1 x hxV (v i))) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (hUV : U.1 ≤ V.1),
      Etale (toAffineSpace f U.1 fun i => X.presheaf.map (homOfLE hUV).op (v i)) := by
  classical
  -- a standard smooth affine open `V'` around `x`, and a basic open `U ⊆ V ⊓ V'` of it
  obtain ⟨V', hV', hxV', hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  obtain ⟨t, htV, hxt⟩ := hV'.exists_basicOpen_le (V := V.1) ⟨x, hxV⟩ hxV'
  set U : X.Opens := X.basicOpen t with hUdef
  have hU : IsAffineOpen U := hV'.basicOpen t
  have hxU : x ∈ U := hxt
  have hstdU : letI := f.sectionsAlgebra U;
      Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) :=
    isStandardSmoothOfRelativeDimension_basicOpen f n hV' t hstd
  set w : Fin n → Γ(X, U) := fun i => X.presheaf.map (homOfLE htV).op (v i) with hwdef
  -- Nakayama at the stalk: the `d w_i` generate `Ω[𝒪_{X,x}⁄k]`
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  set p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with hpdef
  have : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have hfinT : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    finite_kaehlerDifferential_of_isLocalization (k := k) p.primeCompl
  obtain ⟨b, hb⟩ := hb
  have hb' : ∀ i, b i = 1 ⊗ₜ D k (X.presheaf.stalk x)
      (algebraMap Γ(X, U) (X.presheaf.stalk x) (w i)) := by
    intro i
    rw [hb i]
    change _ = 1 ⊗ₜ D k (X.presheaf.stalk x)
      (X.presheaf.germ U x hxU (X.presheaf.map (homOfLE htV).op (v i)))
    rw [X.presheaf.germ_res_apply]
  have hspanT := span_eq_top_of_basis_tensor (k := k) (S := Γ(X, U)) (T := X.presheaf.stalk x)
    w b hb'
  -- spread out: `s ∉ p` with `s • Ω[Γ(U)⁄k] ⊆ span (d w_i)`
  obtain ⟨s, hsp, hs⟩ := exists_mem_forall_smul_mem_span (k := k) (T := X.presheaf.stalk x)
    p.primeCompl w hspanT
  -- the basic open of `s`
  set U' : X.Opens := X.basicOpen s with hU'def
  have hU' : IsAffineOpen U' := hU.basicOpen s
  have hU'U : U' ≤ U := X.basicOpen_le s
  have hxU' : x ∈ U' := (mem_basicOpen_iff_notMem_primeIdealOf hU hxU s).mpr hsp
  have hU'V : U' ≤ V.1 := hU'U.trans htV
  let _ := f.sectionsAlgebra U'
  let _ := restrictAlgebra (X := X) hU'U
  have := isScalarTower_sectionsAlgebra_restrict f hU'U
  have hloc' : IsLocalization.Away s Γ(X, U') :=
    hU.isLocalization_of_eq_basicOpen s (homOfLE hU'U) rfl
  have hspan' := span_eq_top_of_forall_smul_mem (k := k) (S' := Γ(X, U')) (Submonoid.powers s) w
    (Submonoid.mem_powers s) hs
  have hw' : ∀ i, algebraMap Γ(X, U) Γ(X, U') (w i) = X.presheaf.map (homOfLE hU'V).op (v i) := by
    intro i
    change X.presheaf.map (homOfLE hU'U).op (X.presheaf.map (homOfLE htV).op (v i)) = _
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  simp only [hw'] at hspan'
  -- étale by the criterion
  have hstdU' : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U') :=
    isStandardSmoothOfRelativeDimension_basicOpen f n hU s hstdU
  have : Nonempty U' := ⟨⟨x, hxU'⟩⟩
  have hnt : Nontrivial Γ(X, U') := Scheme.component_nontrivial X U'
  refine ⟨⟨U', hU'⟩, hxU', hU'V, ?_⟩
  exact (etale_toAffineSpace_iff f hU' _).mpr
    (etale_aeval_of_isStandardSmoothOfRelativeDimension (k := k) n _ hspan')

end Assembly

end AlgebraicGeometry
