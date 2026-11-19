/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.Stalk
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.EtaleCoordinates

/-!
# Smooth schemes are étale-locally affine spaces

Every point `x` of `X` smooth of relative dimension `n` over `k` has an affine open neighbourhood
`U` with an étale morphism `U ⟶ 𝔸ⁿ_k` ([Sta, Tag 054L]; `exists_etale_toAffineSpace`). The
argument of that lemma, run in coordinates chosen at the point rather than from a standard smooth
presentation: `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` has dimension `n` (`Ω[𝒪_{X,x}⁄k]` is free of rank `n`, the
localization of the free module of a standard smooth chart) and is spanned by the classes
`1 ⊗ d a`, `a ∈ 𝒪_{X,x}`; a basis `1 ⊗ d a_0, …, 1 ⊗ d a_{n-1}` is extracted from this spanning
set, the `a_i` are lifted to sections `v_i` of an affine open around `x`
(`exists_affineOpen_germ_eq`), and `exists_etale_toAffineSpace_of_basis`
(`Hironaka/Scheme/Smooth/EtaleCoordinates.lean`) makes `(v_0, …, v_{n-1})` étale coordinates on a
smaller affine open. The lifting lemma `exists_affineOpen_germ_eq` is used wherever elements of a
stalk are spread out to sections (`EtaleCoordinatesAdapted.lean`, `CoordinateSystemPair.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section Lift

/-- Finitely many elements of the stalk at `x` are germs of sections over one affine open
neighbourhood of `x` inside a given affine open `V`. -/
theorem exists_affineOpen_germ_eq {x : X} (V : X.affineOpens) (hxV : x ∈ V.1) {m : ℕ}
    (a : Fin m → X.presheaf.stalk x) :
    ∃ (U : X.affineOpens) (hxU : x ∈ U.1) (_ : U.1 ≤ V.1) (w : Fin m → Γ(X, U.1)),
      ∀ i, X.presheaf.germ U.1 x hxU (w i) = a i := by
  classical
  have key : ∀ i, ∃ (W : X.Opens) (_ : W ≤ V.1) (hxW : x ∈ W) (s : Γ(X, W)),
      X.presheaf.germ W x hxW s = a i := fun i => by
    obtain ⟨W, hWV, hxW, s, hs⟩ := X.presheaf.exists_le_germ_eq (a i) hxV
    exact ⟨W, hWV, hxW, s, hs⟩
  choose W hWV hxW s hs using key
  set W₀ : X.Opens := V.1 ⊓ ⨅ i, W i with hW₀
  have hxW₀ : x ∈ W₀ := by
    refine ⟨hxV, ?_⟩
    change x ∈ ((⨅ i, W i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW
  obtain ⟨t, htW, hxt⟩ := V.2.exists_basicOpen_le (V := W₀) ⟨x, hxW₀⟩ hxV
  have hle : ∀ i, X.basicOpen t ≤ W i := fun i =>
    htW.trans (inf_le_right.trans (iInf_le W i))
  refine ⟨⟨X.basicOpen t, V.2.basicOpen t⟩, hxt, X.basicOpen_le t,
    fun i => X.presheaf.map (homOfLE (hle i)).op (s i), fun i => ?_⟩
  rw [X.presheaf.germ_res_apply]
  exact hs i

end Lift

section Count

variable (n : ℕ) [SmoothOfRelativeDimension n f] (x : X)
include f n

/-- `Ω[𝒪_{X,x}⁄k]` is free of rank `n`: the base change of `Ω[Γ(U)⁄k]`, free of rank `n` on a
standard smooth affine chart `U ∋ x`. -/
theorem free_kaehlerDifferential_stalk :
    letI := f.stalkAlgebra x
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧
      Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  obtain ⟨U, hU, hxU, hstd⟩ := f.exists_affineOpen_isStandardSmoothOfRelativeDimension n x
  let _ := f.sectionsAlgebra U
  let _ := f.stalkAlgebra x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := f.isScalarTower_sectionsAlgebra_stalk U hxU
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n (R := k)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hnt : Nontrivial Γ(X, U) := Scheme.component_nontrivial X U
  have hrank : Module.finrank Γ(X, U) Ω[Γ(X, U)⁄k] = n :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) n)
  set e := (IsLocalizedModule.isBaseChange (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk x))).equiv
  refine ⟨Module.Free.of_equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, hrank]

/-- `dim_κ κ(x) ⊗ Ω[𝒪_{X,x}⁄k] = n` at every point (base change of a free module of rank `n`). -/
theorem finrank_residueField_tensor_kaehler_stalk :
    letI := f.stalkAlgebra x
    Module.finrank (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) = n := by
  let _ := f.stalkAlgebra x
  obtain ⟨hfree, hrank⟩ := free_kaehlerDifferential_stalk f n x
  rw [Module.finrank_baseChange, hrank]

/-- A basis of `κ(x) ⊗ Ω[𝒪_{X,x}⁄k]` consisting of classes `1 ⊗ d a_i` of `n` elements of the
stalk. -/
theorem exists_basis_tensor_kaehler_stalk :
    letI := f.stalkAlgebra x
    ∃ (a : Fin n → X.presheaf.stalk x)
      (b : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k])),
      ∀ i, b i = 1 ⊗ₜ D k (X.presheaf.stalk x) (a i) := by
  classical
  let _ := f.stalkAlgebra x
  have hfr := finrank_residueField_tensor_kaehler_stalk f n x
  have := finite_kaehlerDifferential_stalk f n x
  set S₀ : Set (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]) :=
    Set.range fun a : X.presheaf.stalk x => (1 : ResidueField (X.presheaf.stalk x)) ⊗ₜ
      D k (X.presheaf.stalk x) a with hS₀def
  have hS₀ : Submodule.span (ResidueField (X.presheaf.stalk x)) S₀ = ⊤ := by
    have h1 := Submodule.baseChange_span (R := X.presheaf.stalk x)
      (M := Ω[X.presheaf.stalk x⁄k]) (A := ResidueField (X.presheaf.stalk x))
      (Set.range (D k (X.presheaf.stalk x)))
    rw [KaehlerDifferential.span_range_derivation, Submodule.baseChange_top] at h1
    have hS : S₀ = TensorProduct.mk (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x))
        Ω[X.presheaf.stalk x⁄k] 1 '' Set.range (D k (X.presheaf.stalk x)) := by
      rw [hS₀def, ← Set.range_comp]
      rfl
    rw [hS]
    exact h1.symm
  obtain ⟨B, hBS, hBspan, hBli⟩ := exists_linearIndependent (ResidueField (X.presheaf.stalk x)) S₀
  rw [hS₀] at hBspan
  let bB := Module.Basis.mk hBli (by rw [Subtype.range_val, hBspan])
  have hBfin : Finite B := Module.Finite.finite_basis bB
  have hcard : Nat.card B = n := by
    have := Fintype.ofFinite B
    rw [← hfr, Module.finrank_eq_card_basis bB, Fintype.card_eq_nat_card]
  let e : B ≃ Fin n := (Finite.equivFin B).trans (finCongr hcard)
  let b := bB.reindex e
  have hmem : ∀ i, b i ∈ S₀ := fun i => by
    have : b i = ((e.symm i : B) : _) := by
      simp only [b, Module.Basis.reindex_apply, bB, Module.Basis.mk_apply]
    rw [this]
    exact hBS (e.symm i).2
  choose a ha using hmem
  exact ⟨a, b, fun i => (ha i).symm⟩

/-- Every point of a scheme smooth of relative dimension `n` over `k` has an affine open
neighbourhood with an étale coordinate morphism to `𝔸ⁿ_k` [Sta, Tag 054L]. -/
theorem exists_etale_toAffineSpace :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (v : Fin n → Γ(X, U.1)), Etale (toAffineSpace f U.1 v) := by
  let _ := f.stalkAlgebra x
  obtain ⟨a, b, hb⟩ := exists_basis_tensor_kaehler_stalk f n x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨U, hxU, -, w, hw⟩ := exists_affineOpen_germ_eq ⟨V, hV⟩ hxV a
  have hb' : ∃ b' : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
      ∀ i, b' i = 1 ⊗ₜ D k (X.presheaf.stalk x) (X.presheaf.germ U.1 x hxU (w i)) :=
    ⟨b, fun i => by rw [hb i, hw i]⟩
  obtain ⟨U', hxU', hU'U, hE⟩ := exists_etale_toAffineSpace_of_basis f n U hxU w hb'
  exact ⟨U', hxU', _, hE⟩

end Count

end AlgebraicGeometry
