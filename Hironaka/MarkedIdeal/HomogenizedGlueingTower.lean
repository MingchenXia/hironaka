/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma along multiple test blow-ups (pullback form)

Source: Włodarczyk 2005, §2.10, Lemma `le:homo` (Glueing Lemma) (1)–(3) restated on open sets, and the part of (4)
that follows from the functoriality of multiple test blow-ups under étale maps (Proposition `pr:funct`), φ_v: X̄ →
X` become an open neighbourhood `U` of `x` with `φ_v` the inclusion and `φ_u = φ` a biholomorphism of `U` onto an
open `U'`.

## Biholomorphisms between open sets

* `LocalInversePair φ ψ W`: on the open set `W`, `φ` and `ψ` are holomorphic and inverse to each other.

## The glueing biholomorphism

* `GlueingData 𝔞 μ u v` bundles `φ, ψ, W` with the conclusions of the glueing lemma on `W`.

## Towers

* `strictAlong T A`: the iterated strict transform of `A` along a tower; `strictAlong_restrict`: it commutes with
  restriction to open sets and with transport along a biholomorphism; `N_geoTransformAlong`: it is the `N` of the
  transform.

Not here: the identification of the `φ`-pullback of `T` with the restriction of `T` to `U` stage by stage
(the lifts `φ_i` of `φ` along `T` and the fact that they fix the cosupports, Włodarczyk's induction in the
proof of `le:homo` (4)).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal HomogenizedIdeal HomogenizedGlueing BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen BlowupTowerTransforms BlowupRestrictOpen MarkedIdealOpenBiholomorphism

noncomputable section

/-! ### Biholomorphisms between open sets -/

section LocalInverse

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A local inverse pair**: on the open set `W`, the maps `φ` and `ψ` are holomorphic and inverse to each
other. -/
structure LocalInversePair (φ ψ : M → M) (W : Set M) : Prop where
  isOpen : IsOpen W
  mdifferentiableAt_left : ∀ p ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p
  mdifferentiableAt_right : ∀ p ∈ W, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ p
  left_inv : ∀ p ∈ W, ψ (φ p) = p
  right_inv : ∀ p ∈ W, φ (ψ p) = p

namespace LocalInversePair

variable {φ ψ : M → M} {W : Set M} (P : LocalInversePair (n := n) φ ψ W)
include P

theorem continuousOn_left : ContinuousOn φ W := fun p hp =>
  (P.mdifferentiableAt_left p hp).continuousAt.continuousWithinAt

theorem continuousOn_right : ContinuousOn ψ W := fun p hp =>
  (P.mdifferentiableAt_right p hp).continuousAt.continuousWithinAt

/-- The domain `U = W ∩ φ⁻¹W`. -/
def dom : Opens M := ⟨W ∩ φ ⁻¹' W, P.continuousOn_left.isOpen_inter_preimage P.isOpen P.isOpen⟩

/-- The codomain `U' = W ∩ ψ⁻¹U`. -/
def cod : Opens M :=
  ⟨W ∩ ψ ⁻¹' (P.dom : Set M), P.continuousOn_right.isOpen_inter_preimage P.isOpen P.dom.isOpen⟩

theorem apply_mem_cod {p : M} (hp : p ∈ P.dom) : φ p ∈ P.cod :=
  ⟨hp.2, show ψ (φ p) ∈ P.dom by rw [P.left_inv p hp.1]; exact hp⟩

theorem apply_mem_dom {q : M} (hq : q ∈ P.cod) : ψ q ∈ P.dom := hq.2

theorem contMDiff_dom :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun p : P.dom => φ p) := fun p =>
  (contMDiffAt_of_eventually_mdifferentiableAt'
    (eventually_of_mem (P.isOpen.mem_nhds p.2.1) P.mdifferentiableAt_left)).comp p
    (contMDiff_subtype_val p)

theorem contMDiff_cod :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun q : P.cod => ψ q) := fun q =>
  (contMDiffAt_of_eventually_mdifferentiableAt'
    (eventually_of_mem (P.isOpen.mem_nhds q.2.1) P.mdifferentiableAt_right)).comp q
    (contMDiff_subtype_val q)

/-- **The biholomorphism `U ≅ U'`** given by `φ`, with inverse `ψ`. -/
def toDiffeomorph :
    CMfd.of (n := n) P.dom ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) P.cod where
  toFun p := ⟨φ p, P.apply_mem_cod p.2⟩
  invFun q := ⟨ψ q, P.apply_mem_dom q.2⟩
  left_inv p := Subtype.ext (P.left_inv p.1 p.2.1)
  right_inv q := Subtype.ext (P.right_inv q.1 q.2.1)
  contMDiff_toFun := contMDiff_opens_mk P.contMDiff_dom fun p => P.apply_mem_cod p.2
  contMDiff_invFun := contMDiff_opens_mk P.contMDiff_cod fun q => P.apply_mem_dom q.2

@[simp] theorem toDiffeomorph_apply (p : P.dom) : (P.toDiffeomorph p : M) = φ p := rfl

@[simp] theorem toDiffeomorph_symm_apply (q : P.cod) : (P.toDiffeomorph.symm q : M) = ψ q := rfl

end LocalInversePair

end LocalInverse

/-! ### The glueing biholomorphism -/

section Glueing

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The glueing data of two tangent directions** `u`, `v` of `(𝔞, μ)`: a local inverse pair `(φ, ψ)` on an
open set `W` on which the conclusions of the glueing lemma hold: `φ^* 𝓗(𝔞) = 𝓗(𝔞)`, `u ∘ φ = v`, and `φ`
fixes `cosupp(𝔞, μ)` pointwise. -/
structure GlueingData (𝔞 : GermIdeal n M) (μ : ℕ) (u v : M → ℂ) where
  /-- The coordinate change replacing `u` by `v`. -/
  φ : M → M
  /-- Its inverse. -/
  ψ : M → M
  /-- The open set on which everything holds. -/
  W : Set M
  pair : LocalInversePair (n := n) φ ψ W
  pullback_iff : ∀ y ∈ W, ∀ g, (GermIdeal.pullback (m := n) φ (homogenizedIdeal 𝔞 μ)).mem y g ↔
    (homogenizedIdeal 𝔞 μ).mem y g
  comp_eq : ∀ p ∈ W, u (φ p) = v p
  apply_eq_self : ∀ y ∈ W, y ∈ cosupport n univ 𝔞 μ → φ y = y

end Glueing

/-! ### Strict transforms along towers -/

section Strict

variable {n : ℕ}

/-- **The iterated strict transform** of `A ⊆ X` along a tower: `A` for the empty tower, and
`closure (π⁻¹(A' \ C))` after a blowup `π` along `C` on top of a tower along which `A` has strict transform
`A'`. -/
def strictAlong {X : CMfd.{u} n} : {Y : CMfd.{u} n} → BlowupTower X Y → Set X → Set Y
  | _, .refl, A => A
  | _, .step T C π _, A => BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T A)

variable {X X' : CMfd.{u} n}

@[simp] theorem strictAlong_refl (A : Set X) :
    strictAlong (BlowupTower.refl : BlowupTower X X) A = A := rfl

theorem strictAlong_step {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (A : Set X) :
    strictAlong (.step T C π hπ) A = BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T A) :=
  rfl

/-- The `N` of the transform of a marked ideal along a tower is the strict transform of `N`. -/
theorem N_geoTransformAlong (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    (geoTransformAlong 𝔪 T).N = strictAlong T 𝔪.N
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [N_geoTransformAlong_step, N_geoTransformAlong 𝔪 T]
      rfl

/-- **Strict transforms commute with restriction to an open set**: the strict transform of `A ∩ U` along the
restricted tower is the trace of the strict transform of `A` on the open preimage of `U`. -/
theorem strictAlong_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A : Set X) →
    strictAlong (restrict U T) ((↑) ⁻¹' A : Set U) = (↑) ⁻¹' strictAlong T A
  | _, .refl, _ => rfl
  | _, .step T C π hπ, A => by
      change BlowupStrictSubmanifold.geoStrictTransform _ ((↑) ⁻¹' C : Set (openPreimage T U))
          (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U)) = _
      rw [strictAlong_restrict U T A]
      exact geoStrictTransform_restrict (openPreimage T U) _ (strictAlong T A)

end Strict

/-! ### The glueing lemma along multiple test blow-ups -/

section GlueingTower

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ}

theorem isClosedSubmanifold_univ : IsClosedSubmanifold n (univ : Set M) :=
  ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩

end GlueingTower

end

end Hironaka.HomogenizedGlueingTower
