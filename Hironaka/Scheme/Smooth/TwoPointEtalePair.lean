/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.Smooth.Adapted
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.DifferentialBasis
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Hironaka.Scheme.Smooth.EtaleLocal
import Hironaka.Scheme.Smooth.Origin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Two embedded smooth points of equal codimension are étale equivalent

Kollár, in the proof of Theorem 27: for two smooth points `x, x'` of an embedded `X ↪ P`, the
embeddings `(x ∈ X ↪ P)` and `(x' ∈ X ↪ P)` "have isomorphic étale neighborhoods"
([Kol07, Theorem 27], the proof); and "any two smooth points of `X` are étale equivalent"
([Kol07, 4.2]). In the vocabulary
of this library: for a closed subscheme `V(Z)` smooth of relative dimension `n − r` in `X` smooth
of relative dimension `n` over the perfect field `k`, and two closed points `x, x' ∈ V(Z)`, there
is an affine scheme `W` with a point `q` and two étale maps `ψ, ψ' : W ⟶ X` over `k`, `ψ q = x`,
`ψ' q = x'`, along which `Z` pulls back to the SAME ideal sheaf `Z.comap ψ = Z.comap ψ'`: the pair
of embedded points is one embedded point of `W`.

The construction: adapted étale coordinates at each point (`EtaleCoordinatesAdapted.lean`),
chosen to VANISH at the point (a regular system of parameters lies in the maximal ideal), so that
both coordinate morphisms `g : U ⟶ 𝔸ⁿ_k`, `g' : U' ⟶ 𝔸ⁿ_k` send the point to the origin
(`toAffineSpace_base_eq_origin_iff`, `Origin.lean`) and `Z` to the same coordinate subspace
`L = V(t_0, …, t_{r−1})`; `W := U ×_{𝔸ⁿ} U'` is the fibre product (affine, as a fibre product of
affine schemes), `q` a point over `(x, x')` (Mathlib's `exists_preimage_pullback`), `ψ, ψ'` the
projections followed by the inclusions, étale by base change, and
`Z.comap ψ = L.comap (pr₁ ≫ g) = L.comap (pr₂ ≫ g') = Z.comap ψ'`.

`EtaleNbhdPair` (`Graph.lean`) is the ONE-point version (both maps to the same point, with
isomorphic residue fields) and does not apply to two points with different residue fields; the
pair here asks nothing of the residue field of `q`.

* `exists_etaleCoordinatesAdapted_germ_mem_maximalIdeal`: adapted étale coordinates with the
  coordinates vanishing at the point (the construction of `EtaleCoordinatesAdapted.lean`, the
  vanishing recorded).
* `exists_etale_pair_of_isClosed`: the two-point étale pair.
* `exists_etale_pair_of_isClosedImmersion`: the pair for a closed immersion `X₁ ⟶ A` of smooth
  schemes and two points of `X₁` closed in `A`.

Used to show that the functorial resolution is an isomorphism over the smooth locus
(`Hironaka/Resolution/Algebraic/Kol07/Thm36/IsoOverSmoothLocus.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing KaehlerDifferential
  TensorProduct

universe u

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (n r : ℕ) [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)]

/-- At a closed point `x` of a center `V(Z)` smooth of relative dimension `n − r`, there are étale
coordinates adapted to `Z` whose coordinate functions all vanish at `x`: the adapted regular
system of parameters lies in the maximal ideal, and the two restrictions of the construction of
`nonempty_etaleCoordinatesAdapted` preserve germs. -/
theorem exists_etaleCoordinatesAdapted_germ_mem_maximalIdeal (hrn : r ≤ n) {x : X}
    (hxZ : x ∈ Z.support) (hx : IsClosed ({x} : Set X)) :
    ∃ c : EtaleCoordinatesAdapted f n r Z x,
      ∀ i, X.presheaf.germ c.U.1 x c.mem (c.v i) ∈ maximalIdeal (X.presheaf.stalk x) := by
  classical
  let _ := f.stalkAlgebra x
  -- adapted parameters at the stalk
  obtain ⟨y, -, hspan, hZ⟩ := exists_adaptedCoordinates Z f n r hrn hxZ hx
  have hy : ∀ i, y i ∈ maximalIdeal (X.presheaf.stalk x) := fun i => by
    rw [hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  -- lift them to sections of an affine open `V ∋ x`
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨V, hxV, -, w, hw⟩ := exists_affineOpen_germ_eq ⟨V₀, hV₀⟩ hxV₀ y
  -- their differentials form a basis at `x`
  obtain ⟨b, hb⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f n hx y hspan
  have hb' : ∃ b' : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k]),
      ∀ i, b' i = 1 ⊗ₜ D k (X.presheaf.stalk x) (X.presheaf.germ V.1 x hxV (w i)) :=
    ⟨b, fun i => by rw [hb i, hw i]⟩
  -- étale coordinates on a smaller affine open `U`
  obtain ⟨U, hxU, hUV, hE⟩ := exists_etale_toAffineSpace_of_basis f n V hxV w hb'
  set w' : Fin n → Γ(X, U.1) := fun i => X.presheaf.map (homOfLE hUV).op (w i) with hw'def
  have hw' : ∀ i, X.presheaf.germ U.1 x hxU (w' i) = y i := fun i => by
    rw [hw'def]
    change X.presheaf.germ U.1 x hxU (X.presheaf.map (homOfLE hUV).op (w i)) = y i
    rw [X.presheaf.germ_res_apply, hw i]
  -- the stalk of `Z` is generated by the germs of `w'_0, …, w'_{r-1}`
  have hZ' : Z.stalkIdeal x =
      Ideal.span ((fun i => X.presheaf.germ U.1 x hxU (w' i)) '' {i | i.val < r}) := by
    rw [hZ]
    congr 1
    refine Set.image_congr fun i _ => ?_
    exact (hw' i).symm
  -- adaptedness on a smaller affine open `U'`
  obtain ⟨U', hxU', hU'U, hAd⟩ :=
    exists_comap_eq_comap_coordinateSubspace f n r Z U hxU w' hZ'
  have : Etale (toAffineSpace f U.1 w') := hE
  refine ⟨⟨U', hxU', fun i => X.presheaf.map (homOfLE hU'U).op (w' i),
    etale_toAffineSpace_restrict f hU'U w', hAd⟩, fun i => ?_⟩
  change X.presheaf.germ U'.1 x hxU' (X.presheaf.map (homOfLE hU'U).op (w' i)) ∈ _
  rw [X.presheaf.germ_res_apply, hw' i]
  exact hy i

/-- **Two closed points of a smooth center are étale equivalent as embedded points** (the proof of
[Kol07, Theorem 27]; [Kol07, 4.2]): an affine scheme `W` with a point `q` and two étale maps
`ψ, ψ' : W ⟶ X` over `k` sending `q` to `x` and to `x'`, along which `Z` pulls back to the same
ideal sheaf. `W` is the fibre product of two adapted coordinate charts over `𝔸ⁿ_k`, the
coordinates vanishing at the points so that both land at the origin. -/
theorem exists_etale_pair_of_isClosed (hrn : r ≤ n) {x x' : X} (hxZ : x ∈ Z.support)
    (hx'Z : x' ∈ Z.support) (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X)) :
    ∃ (W : Scheme.{u}) (q : W) (ψ ψ' : W ⟶ X), IsAffine W ∧ Etale ψ ∧ Etale ψ' ∧
      ψ q = x ∧ ψ' q = x' ∧ Z.comap ψ = Z.comap ψ' ∧ ψ ≫ f = ψ' ≫ f := by
  obtain ⟨c, hc⟩ := exists_etaleCoordinatesAdapted_germ_mem_maximalIdeal f n r Z hrn hxZ hx
  obtain ⟨c', hc'⟩ := exists_etaleCoordinatesAdapted_germ_mem_maximalIdeal f n r Z hrn hx'Z hx'
  have hg : Etale (toAffineSpace f c.U.1 c.v) := c.etale
  have hg' : Etale (toAffineSpace f c'.U.1 c'.v) := c'.etale
  have hU : IsAffine (c.U.1 : Scheme.{u}) := c.U.2
  have hU' : IsAffine (c'.U.1 : Scheme.{u}) := c'.U.2
  -- both points land at the origin
  have h0 : (toAffineSpace f c.U.1 c.v).base ⟨x, c.mem⟩ = origin k n :=
    (toAffineSpace_base_eq_origin_iff f c.U.2 c.v ⟨x, c.mem⟩).2 hc
  have h0' : (toAffineSpace f c'.U.1 c'.v).base ⟨x', c'.mem⟩ = origin k n :=
    (toAffineSpace_base_eq_origin_iff f c'.U.2 c'.v ⟨x', c'.mem⟩).2 hc'
  obtain ⟨q, hq, hq'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := toAffineSpace f c.U.1 c.v) (g := toAffineSpace f c'.U.1 c'.v)
    ⟨x, c.mem⟩ ⟨x', c'.mem⟩ (h0.trans h0'.symm)
  refine ⟨pullback (toAffineSpace f c.U.1 c.v) (toAffineSpace f c'.U.1 c'.v), q,
    pullback.fst _ _ ≫ c.U.1.ι, pullback.snd _ _ ≫ c'.U.1.ι,
    inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, hq]
    rfl
  · rw [Scheme.Hom.comp_apply, hq']
    rfl
  · calc Z.comap (pullback.fst _ _ ≫ c.U.1.ι)
        = (coordinateSubspace k n r).comap
            (pullback.fst (toAffineSpace f c.U.1 c.v) (toAffineSpace f c'.U.1 c'.v) ≫
              toAffineSpace f c.U.1 c.v) := by
          rw [Scheme.IdealSheafData.comap_comp, c.adapted, ← Scheme.IdealSheafData.comap_comp]
      _ = (coordinateSubspace k n r).comap
            (pullback.snd (toAffineSpace f c.U.1 c.v) (toAffineSpace f c'.U.1 c'.v) ≫
              toAffineSpace f c'.U.1 c'.v) := by
          rw [pullback.condition]
      _ = Z.comap (pullback.snd _ _ ≫ c'.U.1.ι) := by
          symm
          rw [Scheme.IdealSheafData.comap_comp, c'.adapted, ← Scheme.IdealSheafData.comap_comp]
  · rw [Category.assoc, Category.assoc, ← toAffineSpace_comp_structure f c.U.1 c.v,
      ← toAffineSpace_comp_structure f c'.U.1 c'.v, ← Category.assoc, ← Category.assoc,
      pullback.condition]

/-! ### The pair for a closed immersion -/

/-- For a closed immersion `emb : X₁ ⟶ A` whose source is smooth of relative dimension `d ≤ n`
over `k`: two points of `X₁` whose images are closed in `A` are étale equivalent as embedded
points, the pair of `exists_etale_pair_of_isClosed` for the kernel `emb.ker`, whose subscheme is
`X₁` (`emb.toImage` is an isomorphism, `toImage_imageι`). -/
theorem exists_etale_pair_of_isClosedImmersion {A : Scheme.{u}} (fA : A ⟶ Spec (.of k)) (n d : ℕ)
    [SmoothOfRelativeDimension n fA] {X₁ : Scheme.{u}} (emb : X₁ ⟶ A) [IsClosedImmersion emb]
    [SmoothOfRelativeDimension d (emb ≫ fA)] {x x' : X₁}
    (hx : IsClosed ({emb x} : Set A)) (hx' : IsClosed ({emb x'} : Set A)) :
    ∃ (W : Scheme.{u}) (q : W) (ψ ψ' : W ⟶ A), IsAffine W ∧ Etale ψ ∧ Etale ψ' ∧
      ψ q = emb x ∧ ψ' q = emb x' ∧ emb.ker.comap ψ = emb.ker.comap ψ' ∧ ψ ≫ fA = ψ' ≫ fA := by
  -- `d ≤ n`: the closed immersion is surjective on stalks at the closed point `x`
  have hxc : IsClosed ({x} : Set X₁) := by
    have : ({x} : Set X₁) = emb ⁻¹' {emb x} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => emb.isClosedEmbedding.injective h⟩
    rw [this]
    exact hx.preimage emb.continuous
  have hdn : d ≤ n := by
    have h1 := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed fA n hx
    have h2 := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed (emb ≫ fA) d hxc
    have h3 := ringKrullDim_le_of_surjective (emb.stalkMap x).hom (emb.stalkMap_surjective x)
    rw [h1, h2] at h3
    exact_mod_cast h3
  -- the subscheme of the kernel is `X₁`: transport the relative dimension along `emb.toImage`
  have hsub : SmoothOfRelativeDimension d (emb.ker.subschemeι ≫ fA) := by
    have h0 : emb.toImage ≫ emb.imageι = emb := emb.toImage_imageι
    have h1 : inv emb.toImage ≫ (emb ≫ fA) = emb.imageι ≫ fA := by
      calc inv emb.toImage ≫ (emb ≫ fA)
          = inv emb.toImage ≫ ((emb.toImage ≫ emb.imageι) ≫ fA) := by rw [h0]
        _ = emb.imageι ≫ fA := by simp
    have h2 : SmoothOfRelativeDimension (0 + d) (inv emb.toImage ≫ (emb ≫ fA)) := inferInstance
    rw [h1, Nat.zero_add] at h2
    exact h2
  have hsub' : SmoothOfRelativeDimension (n - (n - d)) (emb.ker.subschemeι ≫ fA) := by
    rw [Nat.sub_sub_self hdn]; exact hsub
  have hrange : ∀ y : X₁, emb y ∈ emb.ker.support := fun y => by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker,
      emb.isClosedEmbedding.isClosed_range.closure_eq]
    exact ⟨y, rfl⟩
  exact exists_etale_pair_of_isClosed fA n (n - d) emb.ker (Nat.sub_le n d) (hrange x) (hrange x')
    hx hx'

end AlgebraicGeometry
