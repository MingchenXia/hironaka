import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Sections of smooth morphisms over a henselian local ring

Let `V` be a henselian local ring with residue field `κ`, and `A` a finitely presented
`V`-algebra. If `φ : A → κ` is a `κ`-point of the closed fibre of `Spec A → Spec V` at which `A`
is smooth over `V`, then `φ` lifts to a section `σ : A → V`, i.e. `Spec V → Spec A` is a section
through the given point. The proof uses the local structure of smooth algebras
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`: near the point, `A` is standard étale
over a polynomial ring `V[x₁, …, xₙ]`): lift the coordinates of the point arbitrarily to `V`,
specialize the standard étale presentation `P[X]_g/(f)` along the lift, and solve the resulting
monic equation with a simple root modulo `𝔪` by Hensel's lemma.

This is used by Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
in the proof of Proposition 4.4.6 (`semi-stable.tex` lines 3207–3209: "find a point
`Pᵢ ∈ C'_η` such that the `s`-fiber of its closure `P̄ᵢ` is a smooth point `pᵢ ∈ Zᵢ`"), where the
base is a valuation ring with separably closed fraction field, hence strictly henselian
(`Valuation/SepClosed.lean`, `instHenselianLocalRingValuationSubring`). Blueprint chapter
`sm-valuation-geometry.tex`, node `lem:sm-hensel-sections`.

## Main results

* `exists_algHom_lift_of_isSmoothAt`: the algebraic statement.
* `exists_section_of_isSmoothAt`: the section `Spec V → Spec A` through the given point.
-/

noncomputable section

open IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.ValuationRing

variable {V : Type u} [CommRing V] [HenselianLocalRing V]

/-- **Hensel lifting for standard étale algebras over a polynomial ring.** Let `P = V[x₁, …, xₙ]`
and let `B` be a standard étale `P`-algebra. Every `V`-algebra map `B → κ(V)` lifts to a
`V`-algebra map `B → V`. -/
theorem exists_algHom_lift_of_isStandardEtale {n : ℕ} {B : Type*} [CommRing B] [Algebra V B]
    [Algebra (MvPolynomial (Fin n) V) B] [IsScalarTower V (MvPolynomial (Fin n) V) B]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) V) B] (φ : B →ₐ[V] ResidueField V) :
    ∃ σ : B →ₐ[V] V, (IsScalarTower.toAlgHom V V (ResidueField V)).comp σ = φ := by
  classical
  set P := MvPolynomial (Fin n) V
  set κ := ResidueField V
  -- the point of `Spec P` below `φ`, and a lift `ψ : P → V` of it
  let φP : P →ₐ[V] κ := φ.comp (IsScalarTower.toAlgHom V P B)
  choose a ha using fun i : Fin n ↦ residue_surjective (φP (MvPolynomial.X i))
  let ψ : P →ₐ[V] V := MvPolynomial.aeval a
  have hψ : (IsScalarTower.toAlgHom V V κ).comp ψ = φP := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [ψ, AlgHom.comp_apply, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom']
    exact ha i
  -- the standard étale presentation of `B` over `P`
  let E : StandardEtalePresentation P B := Nonempty.some inferInstance
  -- `P`-algebra structures on `V` (via `ψ`) and on `κ` (via `φP`)
  let : Algebra P V := ψ.toRingHom.toAlgebra
  let : Algebra P κ := φP.toRingHom.toAlgebra
  have hPV : ∀ p : P, algebraMap P V p = ψ p := fun _ ↦ rfl
  have hPκ : ∀ p : P, algebraMap P κ p = φP p := fun _ ↦ rfl
  have hVκ : ∀ p : P, residue V (ψ p) = φP p := fun p ↦ congr($hψ p)
  -- `φ` as a `P`-algebra map
  let φ' : B →ₐ[P] κ :=
    { φ.toRingHom with
      commutes' := fun p ↦ by
        change φ (algebraMap P B p) = algebraMap P κ p
        rfl }
  have hφ' : ∀ b, φ' b = φ b := fun _ ↦ rfl
  -- the residue of the presentation's generator
  set b₀ : κ := φ E.x with hb₀
  obtain ⟨c₀, hc₀⟩ := residue_surjective b₀
  have hmapE : E.HasMap (φ' E.x) := E.hasMap.map φ'
  have hderE : IsUnit (aeval (φ' E.x) E.f.derivative) := hmapE.isUnit_derivative_f
  -- the specialized monic polynomial over `V`
  set F : V[X] := E.f.map ψ.toRingHom with hF
  have hFmonic : F.Monic := E.monic_f.map _
  have hres : ∀ (p : P[X]) (c : V), residue V ((p.map ψ.toRingHom).eval c) =
      aeval (residue V c) p := by
    intro p c
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, aeval_def]
    congr 1
    exact RingHom.ext fun q ↦ hVκ q
  have hF0 : F.eval c₀ ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, hF, hres, hc₀]
    exact hmapE.1
  have hF1 : IsUnit (F.derivative.eval c₀) := by
    rw [hF, Polynomial.derivative_map]
    have hne : residue V ((E.f.derivative.map ψ.toRingHom).eval c₀) ≠ 0 := by
      rw [hres, hc₀]
      exact hderE.ne_zero
    rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    exact hne
  obtain ⟨c, hcroot, hcc₀⟩ := HenselianLocalRing.is_henselian F hFmonic c₀ hF0 hF1
  have hcres : residue V c = b₀ := by
    rw [← hc₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hcc₀
  -- the lift `B → V`
  have hmapV : E.HasMap c := by
    refine ⟨?_, ?_⟩
    · rw [aeval_def, Polynomial.eval₂_eq_eval_map]
      exact hcroot
    · have hne : residue V (aeval c E.g) ≠ 0 := by
        rw [aeval_def, Polynomial.eval₂_eq_eval_map]
        change residue V ((E.g.map ψ.toRingHom).eval c) ≠ 0
        rw [hres, hcres]
        exact (hmapE.2).ne_zero
      rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
      exact hne
  have : IsScalarTower V P V := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  let σP : B →ₐ[P] V := (E.lift c hmapV).comp E.equivRing.toAlgHom
  refine ⟨σP.restrictScalars V, ?_⟩
  -- compare with `φ` on the generator
  have : IsScalarTower P V κ := IsScalarTower.of_algebraMap_eq fun p ↦ (hVκ p).symm
  let ρ : V →ₐ[P] κ :=
    { (residue V) with commutes' := fun p ↦ hVκ p }
  have hcomp : ρ.comp σP = φ' := by
    apply E.hom_ext
    change residue V ((E.lift c hmapV) (E.equivRing E.x)) = φ E.x
    rw [StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X, hcres]
  ext b
  exact congr($hcomp b)

/-- **Sections through smooth rational points** (Temkin, proof of Proposition 4.4.6). Let `V` be a
henselian local ring, `A` a finitely presented `V`-algebra and `q` a prime of `A` at which `A` is
smooth over `V`. If `q` is the kernel of a `V`-algebra map `φ : A → κ(V)` (a rational point of the
closed fibre), then `φ` lifts to a `V`-algebra map `σ : A → V`. -/
theorem exists_algHom_lift_of_isSmoothAt {A : Type*} [CommRing A] [Algebra V A]
    [Algebra.FinitePresentation V A] (q : Ideal A) [q.IsPrime] [Algebra.IsSmoothAt V q]
    (φ : A →ₐ[V] ResidueField V) (hφ : RingHom.ker φ = q) :
    ∃ σ : A →ₐ[V] V, (IsScalarTower.toAlgHom V V (ResidueField V)).comp σ = φ := by
  obtain ⟨f, hf, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := q)
  have hu : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
    rintro ⟨y, k, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ (isUnit_iff_ne_zero.mpr fun h ↦ hf ?_)
    rw [← hφ]
    exact h
  let φB : Localization.Away f →ₐ[V] ResidueField V := IsLocalization.liftAlgHom hu
  obtain ⟨σB, hσB⟩ := exists_algHom_lift_of_isStandardEtale (n := n) φB
  refine ⟨σB.comp (IsScalarTower.toAlgHom V A (Localization.Away f)), ?_⟩
  ext a
  have h := congr($hσB (algebraMap A (Localization.Away f) a))
  simpa [φB, IsLocalization.lift_eq] using h

open AlgebraicGeometry CategoryTheory in
/-- **Sections through smooth rational points, geometric form.** Let `V` be a henselian local
ring, `A` a finitely presented `V`-algebra and `q` a prime of `A` at which `A` is smooth over `V`
and which is the kernel of a `V`-algebra map `A → κ(V)` (a rational point of the closed fibre of
`Spec A → Spec V`). There is a section `σ : Spec V → Spec A` of `Spec A → Spec V` mapping the
closed point to `q`. -/
theorem exists_section_of_isSmoothAt {A : Type u} [CommRing A] [Algebra V A]
    [Algebra.FinitePresentation V A] (q : Ideal A) [q.IsPrime] [Algebra.IsSmoothAt V q]
    (φ : A →ₐ[V] ResidueField V) (hφ : RingHom.ker φ = q) :
    ∃ σ : Spec (.of V) ⟶ Spec (.of A),
      σ ≫ Spec.map (CommRingCat.ofHom (algebraMap V A)) = 𝟙 _ ∧
        (σ (closedPoint V)).asIdeal = q := by
  obtain ⟨σ, hσ⟩ := exists_algHom_lift_of_isSmoothAt q φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom σ.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact σ.commutes r
  · ext a
    change σ a ∈ maximalIdeal V ↔ a ∈ q
    rw [← hφ, RingHom.mem_ker, ← residue_eq_zero_iff, ← hσ]
    rfl

end DeJongAlterations.StableModification.ValuationRing
