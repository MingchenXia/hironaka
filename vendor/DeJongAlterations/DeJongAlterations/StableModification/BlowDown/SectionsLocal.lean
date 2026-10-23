/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.InvertibleSmooth
import DeJongAlterations.StableModification.Blowups.TransportSection
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Local equations of sections through smooth points (Temkin, Prop. 4.4.6)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3207–3209): "find a point `Pᵢ ∈ C'_η` such that the `s`-fiber of its closure `P̄ᵢ`
is a smooth point `pᵢ ∈ Zᵢ`, and so `P̄ᵢ` lies in the smooth locus of `C'`. In particular,
`∪ P̄ᵢ` is a Cartier divisor." This file proves the local form used here
(`exists_localEquation`): for a nodal curve `q : Y → Spec V` over a henselian local ring with
algebraically closed residue field and a closed point `p` of the closed fibre at which `q` is
smooth, there are an open `U ∋ p` and `t ∈ Γ(U, 𝒪)` such that the zero locus `T = U ∖ D(t)` is
**closed in `Y`** and meets the closed fibre only in `p`.

## The argument

* Near `p`, `Y` is standard smooth of relative dimension one over `V` (lane OM1's
  `Omega.exists_isStandardSmoothOfRelativeDimension_one`), hence étale over the affine line
  `𝔸¹_V = Spec V[x]` (Mathlib's `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`):
  `φ : W → 𝔸¹_V` for an affine open `W ∋ p`.
* `p` is a rational point of the closed fibre (`exists_algHom_residueField_of_isMaximal`: the
  Nullstellensatz), so Hensel's lemma gives a `V`-algebra map `σ : Γ(W) → V` through `p`
  (`ValuationRing.exists_algHom_lift_of_isSmoothAt`), and `i = Spec(σ ∘ φ^♯) : Spec V → 𝔸¹_V` is a
  section of the line through `φ(p)`, the closed subscheme `x = c` with `c = σ(φ^♯ x)`.
* Lane T41's shrinking step (`Blowups.exists_open_isClosed_locus`, the étale preimage of a section
  over a henselian base splits off the component through `p`) gives `U ⊆ W` on which
  `φ⁻¹(x = c)` is closed in `Y` with `p` as its only point on the closed fibre; on `U` it is the
  zero locus of `t = φ^♯(x - c)` (`mem_span_X_sub_C`).

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-local-equation`.
-/

namespace DeJongAlterations.StableModification.BlowDown.SectionsLocal

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Algebra

/-- **The Nullstellensatz at a closed point of the closed fibre.** If `A` is of finite type over a
local ring `V` with algebraically closed residue field and `q` is a maximal ideal of `A` over the
maximal ideal of `V`, then `A → A ⧸ q` is a rational point: there is a `V`-algebra map
`A → κ(V)` with kernel `q`. -/
theorem exists_algHom_residueField_of_isMaximal {V A : Type u} [CommRing V] [IsLocalRing V]
    [IsAlgClosed (ResidueField V)] [CommRing A] [Algebra V A] [Algebra.FiniteType V A]
    (q : Ideal A) [hq : q.IsMaximal] (hqV : q.comap (algebraMap V A) = maximalIdeal V) :
    ∃ φ : A →ₐ[V] ResidueField V, RingHom.ker φ = q := by
  let K := A ⧸ q
  let : Field K := Ideal.Quotient.field q
  have hker : RingHom.ker (algebraMap V K) = maximalIdeal V := by
    rw [IsScalarTower.algebraMap_eq V A K, ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq,
      Ideal.mk_ker, hqV]
  let f : ResidueField V →+* K := Ideal.Quotient.lift _ (algebraMap V K) (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  let : Algebra (ResidueField V) K := f.toAlgebra
  have hfV : ∀ v : V, f (residue V v) = algebraMap V K v := fun v => rfl
  have : IsScalarTower V (ResidueField V) K := IsScalarTower.of_algebraMap_eq fun v => (hfV v).symm
  have : Algebra.FiniteType A K :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType V K := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType (ResidueField V) K := Algebra.FiniteType.of_restrictScalars_finiteType V _ _
  have : Module.Finite (ResidueField V) K := finite_of_finite_type_of_isJacobsonRing _ _
  have hbij : Function.Bijective (algebraMap (ResidueField V) K) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ResidueField V ≃+* K := RingEquiv.ofBijective _ hbij
  refine ⟨{ toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk q), commutes' := fun v => ?_ },
    ?_⟩
  · change e.symm (Ideal.Quotient.mk q (algebraMap V A v)) = algebraMap V (ResidueField V) v
    rw [RingEquiv.symm_apply_eq]
    exact (hfV v).symm
  · ext a
    change e.symm (Ideal.Quotient.mk q a) = 0 ↔ a ∈ q
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- In `R[x]` (as `MvPolynomial (Fin 1) R`), for a ring map `ρ` with `ρ ∘ C = id`, every
polynomial `F` satisfies `F - C (ρ F) ∈ (x - C (ρ x))`. -/
theorem sub_C_mem_span {R : Type u} [CommRing R] (ρ : MvPolynomial (Fin 1) R →+* R)
    (hρ : ∀ r, ρ (MvPolynomial.C r) = r) (F : MvPolynomial (Fin 1) R) :
    F - MvPolynomial.C (ρ F) ∈
      Ideal.span {MvPolynomial.X 0 - MvPolynomial.C (ρ (MvPolynomial.X 0))} := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [hρ, sub_self]; exact zero_mem _
  | add F G hF hG =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hF hG
  | mul_X F i hF =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have e : F * MvPolynomial.X 0 - MvPolynomial.C (ρ (F * MvPolynomial.X 0)) =
        (F - MvPolynomial.C (ρ F)) * MvPolynomial.X 0 +
          MvPolynomial.C (ρ F) * (MvPolynomial.X 0 - MvPolynomial.C (ρ (MvPolynomial.X 0))) := by
      rw [map_mul, map_mul]
      ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hF) (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

/-- The kernel of a retraction `ρ : R[x] → R` of `C` is contained in every ideal containing
`x - C (ρ x)`. -/
theorem ker_le_of_mem {R : Type u} [CommRing R] (ρ : MvPolynomial (Fin 1) R →+* R)
    (hρ : ∀ r, ρ (MvPolynomial.C r) = r) {I : Ideal (MvPolynomial (Fin 1) R)}
    (hI : MvPolynomial.X 0 - MvPolynomial.C (ρ (MvPolynomial.X 0)) ∈ I) : RingHom.ker ρ ≤ I := by
  intro F hF
  have h := sub_C_mem_span ρ hρ F
  rw [RingHom.mem_ker.mp hF, map_zero, sub_zero] at h
  exact (Ideal.span_singleton_le_iff_mem I).mpr hI h

end Algebra

section Scheme

variable {V : Type u} [CommRing V] [HenselianLocalRing V] [IsAlgClosed (ResidueField V)]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of V)) [IsSeparated q] [LocallyOfFinitePresentation q]

/-- **Local equation of a section through a smooth point** (Temkin, T:3207–3209): for a closed
point `p` of the closed fibre at which `q` is smooth (the geometric fibres of `q` being of pure
dimension one), there are an open `U ∋ p` and `t ∈ Γ(U, 𝒪)` whose zero locus `U ∖ D(t)` is closed
in `Y`, contains `p` and meets the closed fibre only in `p`. -/
theorem exists_localEquation (hpure : Curves.SemistableOpen.PureOneDimensionalFibres q) {p : Y}
    (hp : p ∈ q.smoothLocus) (hpc : IsClosed ({p} : Set Y)) (hps : q p = closedPoint V) :
    ∃ (U : Y.Opens) (t : Γ(Y, U)), p ∈ U ∧ p ∉ Y.basicOpen t ∧
      IsClosed ((U : Set Y) \ Y.basicOpen t) ∧
      ∀ y ∈ (U : Set Y) \ Y.basicOpen t, q y = closedPoint V → y = p := by
  obtain ⟨V', hV', W, hW, hWV', hpW, -, hstd⟩ :=
    Omega.exists_isStandardSmoothOfRelativeDimension_one q hpure hp
  have hV'top : V' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hs : closedPoint V ∈ V' := by
      rw [← hps]
      exact hWV' hpW
    exact (IsLocalRing.specializes_closedPoint x).mem_open V'.isOpen hs
  subst hV'top
  -- the structure map `V → Γ(W)` and its standard smoothness
  let φV : CommRingCat.of V ⟶ Γ(Y, W) := (Scheme.ΓSpecIso (.of V)).inv ≫ q.appLE ⊤ W hWV'
  have hφV : φV.hom.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
      (Scheme.ΓSpecIso (.of V)).symm.commRingCatIsoToRingEquiv hstd
  obtain ⟨g, hgC, hg⟩ := RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial hφV
  -- the étale map `φ : W → 𝔸¹_V`
  let qM : Spec (.of (MvPolynomial (Fin 1) V)) ⟶ Spec (.of V) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : V →+* MvPolynomial (Fin 1) V))
  let φ : W.toScheme ⟶ Spec (.of (MvPolynomial (Fin 1) V)) :=
    hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g)
  have : Etale (Spec.map (CommRingCat.ofHom g)) :=
    HasRingHomProperty.Spec_iff (P := @Etale) |>.mpr hg
  have : Etale φ := by
    change Etale (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g))
    infer_instance
  have hsq : hW.fromSpec ≫ q = Spec.map φV := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hW hWV',
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have hCg : CommRingCat.ofHom (MvPolynomial.C : V →+* MvPolynomial (Fin 1) V) ≫
      CommRingCat.ofHom g = φV := by
    ext v
    exact RingHom.congr_fun hgC v
  have hφ : φ ≫ qM = W.ι ≫ q := by
    change (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g)) ≫ qM = W.ι ≫ q
    rw [Category.assoc, ← Spec.map_comp, hCg, ← hsq, IsAffineOpen.fromSpec, Category.assoc,
      Iso.hom_inv_id_assoc]
  -- the rational point and Hensel's lemma
  let : Algebra V Γ(Y, W) := φV.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 V Γ(Y, W) := hφV
  have : Algebra.IsStandardSmooth V Γ(Y, W) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Algebra.FormallySmooth V Γ(Y, W) := ⟨inferInstance, inferInstance⟩
  set qp := hW.primeIdealOf ⟨p, hpW⟩ with hqpdef
  have hqx : hW.fromSpec qp = p := hW.fromSpec_primeIdealOf ⟨p, hpW⟩
  have : qp.asIdeal.IsMaximal := hW.primeIdealOf_isMaximal_of_isClosed ⟨p, hpW⟩ hpc
  have hq : qp.asIdeal.comap (algebraMap V Γ(Y, W)) = maximalIdeal V := by
    have h : (Spec.map φV) qp = closedPoint V := by
      rw [← hsq, Scheme.Hom.comp_apply, hqx, hps]
    exact congrArg PrimeSpectrum.asIdeal h
  obtain ⟨ψ, hψ⟩ := exists_algHom_residueField_of_isMaximal qp.asIdeal hq
  obtain ⟨σ, hσ⟩ := ValuationRing.exists_algHom_lift_of_isSmoothAt qp.asIdeal ψ hψ
  -- the section `i : Spec V → 𝔸¹_V` through `φ(p)`
  let ρ : MvPolynomial (Fin 1) V →+* V := σ.toRingHom.comp g
  have hρC : ∀ r, ρ (MvPolynomial.C r) = r := by
    intro r
    change σ (g (MvPolynomial.C r)) = r
    rw [show g (MvPolynomial.C r) = algebraMap V Γ(Y, W) r from RingHom.congr_fun hgC r]
    exact σ.commutes r
  have hρsurj : Function.Surjective ρ := fun r => ⟨MvPolynomial.C r, hρC r⟩
  let i : Spec (.of V) ⟶ Spec (.of (MvPolynomial (Fin 1) V)) := Spec.map (CommRingCat.ofHom ρ)
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ hρsurj
  have hi : i ≫ qM = Spec.map (CommRingCat.ofHom (algebraMap V V)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact hρC r
  have hσm : (maximalIdeal V).comap σ.toRingHom = qp.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hψ, RingHom.mem_ker, ← hσ, ← residue_eq_zero_iff]
    rfl
  have hφp : φ ⟨p, hpW⟩ = i (closedPoint V) := by
    apply PrimeSpectrum.ext
    change (qp.asIdeal).comap g = (maximalIdeal V).comap (σ.toRingHom.comp g)
    rw [← Ideal.comap_comap, hσm]
  have hxi : φ ⟨p, hpW⟩ ∈ Set.range i := ⟨_, hφp.symm⟩
  obtain ⟨U₀, hU₀W, hpU₀, hcl, honly⟩ :=
    Blowups.exists_open_isClosed_locus q W qM φ hφ (Ā := V) (fun v => ⟨v, rfl⟩) i hi p hpW
      hps hxi
  -- the local equation `t = φ^♯(x - c)`
  let t₀ : MvPolynomial (Fin 1) V := MvPolynomial.X 0 - MvPolynomial.C (ρ (MvPolynomial.X 0))
  let f : Γ(Y, W) := g t₀
  let t : Γ(Y, U₀) := Y.presheaf.map (homOfLE hU₀W).op f
  have hmemf : ∀ (y : Y) (hy : y ∈ W),
      y ∈ Y.basicOpen f ↔ f ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro y hy
    have h := hW.fromSpec_preimage_basicOpen f
    have h' : hW.primeIdealOf ⟨y, hy⟩ ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen f ↔
        hW.primeIdealOf ⟨y, hy⟩ ∈ PrimeSpectrum.basicOpen f := by rw [h]
    rw [Scheme.Hom.mem_preimage, hW.fromSpec_primeIdealOf] at h'
    exact h'
  have hrange : ∀ (y : Y) (hy : y ∈ W),
      φ ⟨y, hy⟩ ∈ Set.range i ↔ f ∈ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro y hy
    have hr : Set.range i = PrimeSpectrum.zeroLocus (RingHom.ker ρ) :=
      range_comap_of_surjective _ ρ hρsurj
    rw [hr, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    change RingHom.ker ρ ≤ (hW.primeIdealOf ⟨y, hy⟩).asIdeal.comap g ↔ _
    constructor
    · intro h
      have ht₀ : t₀ ∈ RingHom.ker ρ := by
        rw [RingHom.mem_ker]
        simp only [t₀, map_sub, hρC, sub_self]
      exact h ht₀
    · intro h
      exact ker_le_of_mem ρ hρC h
  have hset : (U₀ : Set Y) \ Y.basicOpen t = (U₀ : Set Y) ∩ W.ι '' (φ ⁻¹' Set.range i) := by
    ext y
    constructor
    · rintro ⟨hyU, hyt⟩
      have hyW : y ∈ W := hU₀W hyU
      refine ⟨hyU, ⟨y, hyW⟩, ?_, rfl⟩
      rw [Set.mem_preimage, hrange y hyW]
      by_contra hf
      apply hyt
      rw [Scheme.basicOpen_res]
      exact ⟨hyU, (hmemf y hyW).mpr hf⟩
    · rintro ⟨hyU, ⟨y', hy'⟩, hy'r, rfl⟩
      refine ⟨hyU, ?_⟩
      rw [Scheme.basicOpen_res]
      rintro ⟨-, hyf⟩
      rw [Set.mem_preimage, hrange _ hy'] at hy'r
      exact ((hmemf _ hy').mp hyf) hy'r
  have hpT : p ∈ (U₀ : Set Y) \ Y.basicOpen t := by
    rw [hset]
    exact ⟨hpU₀, ⟨p, hpW⟩, hxi, rfl⟩
  refine ⟨U₀, t, hpU₀, hpT.2, ?_, ?_⟩
  · rw [hset]
    exact hcl
  · rw [hset]
    exact honly

end Scheme

end

end DeJongAlterations.StableModification.BlowDown.SectionsLocal
