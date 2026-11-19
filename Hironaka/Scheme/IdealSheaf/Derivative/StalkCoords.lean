/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.DifferentialBasisAny
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Derivation.Lie

/-!
# Regular coordinates on the stalks of a smooth scheme

[Kol07, Definition 73]: for local coordinates `x₁, …, xₙ` at a point `p ∈ X`, the derivations
`∂/∂x₁, …, ∂/∂xₙ` are "local generators of `Der_X`". For the stalk `𝒪_{X,x}` of a scheme
smooth of relative dimension `n` over a field `k` of characteristic zero, this module produces the
coordinate structure `RegularCoords 𝒪_{X,x} m` of `Hironaka/Algebra/Local/Coords.lean` with
`k`-linear derivations: a regular system of parameters `y₁, …, y_m` (`m = dim 𝒪_{X,x}`) and
`k`-derivations `∂ᵢ` with `∂ᵢ yⱼ = δᵢⱼ` (`exists_regularCoords_stalk`; with a prescribed regular
system of parameters, `exists_regularCoords_stalk_of_span_eq`).

The construction reads Kollár's "local coordinates" at an arbitrary point: `Ω_{𝒪_{X,x}/k}` is
finitely presented and projective (the stalk is essentially of finite type and formally smooth
over `k`, being a localization of a standard smooth algebra, `formallySmooth_stalk`), and a
`κ(x)`-basis of `κ(x) ⊗ Ω` lifts to a basis of `Ω` (Mathlib's
`Module.exists_basis_of_basis_baseChange`); the basis `dy₁, …, dy_m, dz₁, …, dz_t` of `κ(x) ⊗ Ω`
is `exists_basis_tensor_kaehlerDifferential_sum` of
`Hironaka/Scheme/Smooth/DifferentialBasisAny.lean`, for lifts `z` of a transcendence basis of
`κ(x)/k`, separating because `k` has characteristic zero. The `∂ᵢ` are the duals of the `dyᵢ` under
`Ω[A⁄k] →ₗ A ≃ Der_k(A, A)` (`linearMapEquivDerivation`); they commute because their commutator is a
derivation vanishing on every `yⱼ` and `zₗ`, hence on the basis of `Ω`. Every `k`-derivation is
`δ = ∑ᵢ δ(yᵢ) ∂ᵢ + ∑ₗ δ(zₗ) ∂'ₗ` (`exists_regularCoords_stalk_aux`); when `κ(x)` is algebraic over
`k`, at every closed point, the transcendence basis is empty and the `∂ᵢ` span `Der_k(𝒪_{X,x})`
(`SpansDerivations k`, `exists_regularCoords_stalk_of_isAlgebraic`). At a non-closed point
(`t > 0`) the `∂ᵢ` do not span, the dual of a `dzₗ` killing every parameter; there only the
inclusion `c.D ≤ D` is available (`D_le_derivative`, `Hironaka/Algebra/Derivative/Basic.lean`).

Used for the cosupport of the derivative ideals
(`Hironaka/Scheme/IdealSheaf/Derivative/Cosupport.lean`,
`Hironaka/Scheme/IdealSheaf/Derivative/Properties.lean`,
`Hironaka/Scheme/IdealSheaf/Derivative/FlagCoords.lean`), for maximal contact and tuning on schemes
(`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivBridge.lean`,
`Hironaka/Resolution/Algebraic/Tuning/MCTuned.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`) and on manifolds
(`Hironaka/Manifold/Germ/CoordDerivCoords.lean`,
`Hironaka/Manifold/BlowUp/Transform/DerivTransform.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- `ℚ → k → 𝒪_{X,x}` is a scalar tower for the structures induced by `f`. -/
theorem isScalarTower_rat_stalkAlgebra [CharZero k] (x : X) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    IsScalarTower ℚ k (X.presheaf.stalk x) :=
  letI := f.stalkAlgebra x
  letI := f.stalkAlgebraRat x
  IsScalarTower.of_algebraMap_eq fun _ => rfl

include n in
/-- The stalk of a smooth `k`-scheme is formally smooth over `k`: it is a localization of a
standard smooth `k`-algebra (`exists_affineOpen_isStandardSmoothOfRelativeDimension`). -/
theorem formallySmooth_stalk (x : X) :
    letI := f.stalkAlgebra x
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have h1 : Algebra.FormallySmooth k Γ(X, U) :=
    (inferInstance : Algebra.Smooth k Γ(X, U)).formallySmooth
  have h2 : Algebra.FormallySmooth Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X, U) (X.presheaf.stalk x)

include n in
/-- The construction with a prescribed regular system of parameters `y` of `𝒪_{X,x}`
(`m = dim 𝒪_{X,x}` members generating `𝔪_x`): regular coordinates `c` with `c.x = y` and `k`-linear
derivations `∂ᵢ`, lifts `z` of a transcendence basis of `κ(x)/k`, and `k`-derivations `∂'ₗ` dual to
the `dzₗ`, such that every `k`-derivation is `δ = ∑ᵢ δ(yᵢ) ∂ᵢ + ∑ₗ δ(zₗ) ∂'ₗ` (the `∂ᵢ`, `∂'ₗ` are
the dual basis of `dy₁, …, dy_m, dz₁, …, dz_t` lifted to `Ω_{𝒪_{X,x}/k}`). Used with flag
parameters in `Hironaka/Scheme/IdealSheaf/Derivative/FlagCoords.lean`. -/
theorem exists_regularCoords_stalk_of_span_eq [CharZero k] (x : X) (m : ℕ)
    (y : Fin m → X.presheaf.stalk x)
    (hm : (m : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hy : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y)) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) x
    ∃ (t : ℕ) (c : RegularCoords (X.presheaf.stalk x) m) (z : Fin t → X.presheaf.stalk x)
      (der' : Fin t → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      c.x = y ∧ c.IsLinearOver k ∧
      IsTranscendenceBasis k (fun j => residue (X.presheaf.stalk x) (z j)) ∧
      ∀ (δ : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)) (r : X.presheaf.stalk x),
        δ r = ∑ i, δ (c.x i) * c.pderiv i r + ∑ j, δ (z j) * der' j r := by
  classical
  let _ := f.stalkAlgebra x
  let _ := f.stalkAlgebraRat x
  have hST : IsScalarTower ℚ k (X.presheaf.stalk x) := isScalarTower_rat_stalkAlgebra f x
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := @isRegularLocalRing_stalk k _ X f hs x
  -- lifts `z` of a (separating) transcendence basis of the residue field
  have hE := essFiniteType_residueField_stalk f n x
  obtain ⟨T, hT⟩ :=
    exists_finset_isTranscendenceBasis (K := k) (L := ResidueField (X.presheaf.stalk x))
  choose zl hzl using fun w : T => residue_surjective (R := X.presheaf.stalk x) (w : ResidueField _)
  let z : Fin T.card → X.presheaf.stalk x := fun j => zl (T.equivFin.symm j)
  have hzres : (fun j => residue (X.presheaf.stalk x) (z j)) =
      ((↑) : T → ResidueField (X.presheaf.stalk x)) ∘ T.equivFin.symm := by
    funext j
    simp [z, hzl]
  have hz : IsTranscendenceBasis k fun j => residue (X.presheaf.stalk x) (z j) := by
    rw [hzres, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨(algebraicIndependent_equiv T.equivFin.symm).mpr hT.1, ?_⟩
    rw [T.equivFin.symm.surjective.range_comp]
    exact hT.1.isTranscendenceBasis_iff_isAlgebraic.mp hT
  have hsep : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range fun j => residue (X.presheaf.stalk x) (z j)))
      (ResidueField (X.presheaf.stalk x)) := by
    have : CharZero
        (IntermediateField.adjoin k (Set.range fun j => residue (X.presheaf.stalk x) (z j))) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    have := hz.isAlgebraic_field
    infer_instance
  obtain ⟨bκ, hbκ1, hbκ2⟩ := exists_basis_tensor_kaehlerDifferential_sum f n x
    m T.card y hm hy z hz hsep
  -- lift the basis of `κ ⊗ Ω` to a basis of `Ω`
  have hFS := formallySmooth_stalk f n x
  have hEF := essFiniteType_stalk f n x
  let v : Fin m ⊕ Fin T.card → Ω[X.presheaf.stalk x⁄k] :=
    Sum.elim (fun i => D k (X.presheaf.stalk x) (y i)) (fun j => D k (X.presheaf.stalk x) (z j))
  have hvfun : (TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ v) = bκ := by
    funext w
    rcases w with i | j
    · simp [v, hbκ1]
    · simp [v, hbκ2]
  have hli : LinearIndependent (ResidueField (X.presheaf.stalk x))
      (TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
        Ω[X.presheaf.stalk x⁄k] 1 ∘ v) := by
    rw [hvfun]
    exact bκ.linearIndependent
  have hsp : Submodule.span (ResidueField (X.presheaf.stalk x))
      (Set.range (TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
        Ω[X.presheaf.stalk x⁄k] 1 ∘ v)) = ⊤ := by
    rw [hvfun]
    exact bκ.span_eq
  have hinj : Function.Injective
      ((maximalIdeal (X.presheaf.stalk x)).subtype.rTensor Ω[X.presheaf.stalk x⁄k]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange v hli hsp hinj
  have hv : ∀ w, v w = D k (X.presheaf.stalk x) (Sum.elim y z w) := by
    rintro (j' | j') <;> rfl
  -- the dual derivations of `dy₁, …, dy_m` (and of the `dzₗ`)
  let L := linearMapEquivDerivation k (X.presheaf.stalk x) (M := X.presheaf.stalk x)
  let der : Fin m → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x) :=
    fun i => L (b.coord (Sum.inl i))
  have hder : ∀ (i : Fin m) (w : Fin m ⊕ Fin T.card),
      der i (Sum.elim y z w) = if Sum.inl i = w then 1 else 0 := by
    intro i w
    have h1 : der i (Sum.elim y z w) = b.coord (Sum.inl i) (v w) := by
      rcases w with j | j <;> rfl
    rw [h1, ← hb w, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : Sum.inl i = w
    · simp [h]
    · simp [h, Ne.symm h]
  have hder_y : ∀ i j, der i (y j) = if i = j then 1 else 0 := by
    intro i j
    have := hder i (Sum.inl j)
    simpa using this
  -- the `∂ᵢ` commute: their commutator is a derivation vanishing on the basis of `Ω`
  have hcomm : ∀ i j r, der i (der j r) = der j (der i r) := by
    intro i j r
    have h0 : ⁅der i, der j⁆ = 0 := by
      apply L.symm.injective
      rw [map_zero]
      refine b.ext fun w => ?_
      rw [hb w, hv w, LinearMap.zero_apply]
      change (⁅der i, der j⁆).liftKaehlerDifferential (D k _ (Sum.elim y z w)) = 0
      rw [Derivation.liftKaehlerDifferential_comp_D, Derivation.commutator_apply, hder j w,
        hder i w]
      split_ifs <;> simp
    have := Derivation.congr_fun h0 r
    rw [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
    exact this
  -- every derivation is a combination of the dual basis (`derivation_mem_span_range_dualBasis`)
  have hspan' : ∀ (δ : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x))
      (r : X.presheaf.stalk x),
      δ r = ∑ i, δ (y i) * der i r + ∑ j, δ (z j) * L (b.coord (Sum.inr j)) r := by
    intro δ r
    have hφ : L.symm δ = ∑ w, (L.symm δ) (b w) • b.coord w := by
      refine b.ext fun w' => ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        smul_eq_mul]
      rw [Finset.sum_eq_single w' (fun w _ hw => by rw [Finsupp.single_eq_of_ne hw, mul_zero])
        (fun h => (h (Finset.mem_univ w')).elim), Finsupp.single_eq_same, mul_one]
    have hval : ∀ w, (L.symm δ) (b w) = δ (Sum.elim y z w) := by
      intro w
      rw [hb w, hv w]
      exact Derivation.liftKaehlerDifferential_comp_D δ _
    have h1 : δ r = (L.symm δ) (D k (X.presheaf.stalk x) r) :=
      (Derivation.liftKaehlerDifferential_comp_D δ r).symm
    rw [h1, hφ, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun w _ => ?_ <;> rw [hval] <;> rfl
  refine ⟨T.card, { x := y
                    pderiv := fun i => (der i).restrictScalars ℚ
                    span_x := hy
                    card := hm
                    pderiv_x := fun i j => hder_y i j
                    pderiv_comm := fun i j r => hcomm i j r },
    z, fun j => L (b.coord (Sum.inr j)), rfl, fun i a => (der i).map_algebraMap a, hz, hspan'⟩


include n in
/-- The construction for a regular system of parameters chosen here: regular coordinates `c` on
the stalk with `k`-linear derivations `∂ᵢ`, lifts `z` of a transcendence basis of `κ(x)/k`, and
`k`-derivations `∂'ₗ` dual to the `dzₗ`, such that every `k`-derivation is
`δ = ∑ᵢ δ(yᵢ) ∂ᵢ + ∑ₗ δ(zₗ) ∂'ₗ` (the `∂ᵢ`, `∂'ₗ` are the dual basis of `dy₁, …, dy_m, dz₁, …, dz_t`
lifted to `Ω_{𝒪_{X,x}/k}`). -/
theorem exists_regularCoords_stalk_aux [CharZero k] (x : X) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) x
    ∃ (m t : ℕ) (c : RegularCoords (X.presheaf.stalk x) m) (z : Fin t → X.presheaf.stalk x)
      (der' : Fin t → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      c.IsLinearOver k ∧
      IsTranscendenceBasis k (fun j => residue (X.presheaf.stalk x) (z j)) ∧
      ∀ (δ : Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)) (r : X.presheaf.stalk x),
        δ r = ∑ i, δ (c.x i) * c.pderiv i r + ∑ j, δ (z j) * der' j r := by
  classical
  let _ := f.stalkAlgebra x
  let _ := f.stalkAlgebraRat x
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hreg := @isRegularLocalRing_stalk k _ X f hs x
  -- a regular system of parameters `y`
  have hfg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hm : (s.card : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
    rw [hcard]
    exact (isRegularLocalRing_iff _).mp hreg
  let y : Fin s.card → X.presheaf.stalk x := fun i => (s.equivFin.symm i : X.presheaf.stalk x)
  have hrange : Set.range y = (s : Set (X.presheaf.stalk x)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro ha
      exact ⟨s.equivFin ⟨a, ha⟩, by simp [y]⟩
  have hy : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y) := by
    rw [hrange, ← hspan]
  obtain ⟨t, c, z, der', -, hk, hz, hspan'⟩ :=
    exists_regularCoords_stalk_of_span_eq f n x s.card y hm hy
  exact ⟨s.card, t, c, z, der', hk, hz, hspan'⟩

include n in
/-- **Regular coordinates on the stalks** (Kollár's local coordinates, [Kol07, Definition 73]):
at every point of a scheme smooth of relative dimension `n` over a field `k` of characteristic
zero, the stalk carries regular coordinates (`RegularCoords`) whose derivations are `k`-linear.
The spanning of the `k`-derivations holds at the points with residue field algebraic over `k`
(`exists_regularCoords_stalk_of_isAlgebraic`) and fails at the other points, where the dual of a
`dzₗ` kills every parameter. -/
theorem exists_regularCoords_stalk [CharZero k] (x : X) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) x
    ∃ (m : ℕ) (c : RegularCoords (X.presheaf.stalk x) m), c.IsLinearOver k := by
  obtain ⟨m, _, c, _, _, hk, -, -⟩ := exists_regularCoords_stalk_aux f n x
  exact ⟨m, c, hk⟩

include n in
/-- At a point whose residue field is algebraic over `k`, in particular at every closed point, the
stalk carries regular coordinates whose `k`-linear derivations `∂ᵢ` span the `k`-derivations,
`δ = ∑ᵢ δ(yᵢ) ∂ᵢ` (Kollár's "the derivations `∂/∂x₁, …, ∂/∂xₙ` are local generators of `Der_X`",
[Kol07, Definition 73]): the transcendence basis of `κ(x)/k` is empty, so the `∂ᵢ` are the whole
dual basis. -/
theorem exists_regularCoords_stalk_of_isAlgebraic [CharZero k] (x : X)
    (halg : letI := f.stalkAlgebra x
      Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk x))) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) x
    ∃ (m : ℕ) (c : RegularCoords (X.presheaf.stalk x) m),
      c.IsLinearOver k ∧ c.SpansDerivations k := by
  let _ := f.stalkAlgebra x
  let _ := f.stalkAlgebraRat x
  obtain ⟨m, t, c, z, der', hk, hz, hspan⟩ := exists_regularCoords_stalk_aux f n x
  have ht : IsEmpty (Fin t) := hz.isEmpty_iff_isAlgebraic.mpr halg
  refine ⟨m, c, hk, fun δ r => ?_⟩
  have h0 : ∑ j, δ (z j) * der' j r = 0 := Finset.sum_eq_zero fun j _ => isEmptyElim j
  rw [hspan δ r, h0, add_zero]

end AlgebraicGeometry
