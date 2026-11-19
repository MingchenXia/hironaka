/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.UniversalProperty
public import Hironaka.Scheme.BlowUp.Transform.Defs
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The strict transform is a blow-up

The strict transform `X'` of a closed subscheme `X ⊆ S` under the blow-up of `S` along `Z` is the
blow-up of `X` in the closed subscheme `f⁻¹Z` of `X` [Sta, Tag 080E]; [Hau14, Corollary 5.2 (a)].
The Stacks Project proves it by the Proj computation on charts; here it is proved from the
universal property alone [Hau14, Definition 4.4], for any pair of blow-ups in the sense of
`IsBlowUp` (`Hironaka.Scheme.BlowUp.UniversalProperty`), so that no chart of the construction is
unfolded. The argument, for `π : B ⟶ X` a blow-up of `X` along `D`, `ι : Y ⟶ X` the closed
subscheme of `J`, `π' : B' ⟶ Y` a blow-up of `Y` along `D.comap ι`, `E := D.comap π` the exceptional
ideal, `Jˢ` the strict transform (the `E`-power torsion saturation of `J* = J.comap π`):

1. `π' ≫ ι` is admissible for `D` (its inverse image of `D` is the exceptional ideal of `B'`), so it
   lifts to `φ : B' ⟶ B` over `X`.
2. `φ` lands in `V(Jˢ)`: `J*.comap φ = ⊥` because `J.comap ι = ⊥`, and the saturation pulls back
   into the saturation of `⊥` by the invertible exceptional ideal of `B'` (`comap_saturate_le`),
   which is `⊥` (`saturate_bot_of_isInvertible`). Hence `φ = φ' ≫ ιˢ` with `ιˢ : V(Jˢ) ⟶ B`.
3. `ιˢ ≫ π` factors through `ι` as `g : V(Jˢ) ⟶ Y` (`J.comap (ιˢ ≫ π) ≤ Jˢ.comap ιˢ = ⊥`), and `g`
   is admissible for `D.comap ι`: its inverse image is the restriction `E.comap ιˢ` of the
   exceptional ideal to the saturated closed subscheme, which is invertible because a local
   generator of `E` stays a nonzerodivisor modulo an `E`-saturated ideal
   (`isInvertible_comap_subschemeι_of_colon_eq`). So `g` lifts to `ψ : V(Jˢ) ⟶ B'` over `Y`.
4. `φ' ≫ ψ = 𝟙` by uniqueness of lifts of `π'` (both are lifts), and `ψ ≫ φ' = 𝟙` by uniqueness
   of lifts of the admissible `ιˢ ≫ π` into `B` (`ψ ≫ φ` and `ιˢ` both lift it; `ιˢ` is a
   monomorphism).

## Generic lemmas on ideal sheaves used along the way

* `comap_mul`, `comap_pow`: the inverse image ideal sheaf is multiplicative (the affine formula
  for inverse images on a cover).
* `comap_iSup`: `comap` preserves suprema (it is a lower adjoint).
* `comap_colon_le`, `comap_saturate_le`: colons and saturations pull back into colons and
  saturations.
* `colon_pow_bot_of_isInvertible`, `saturate_bot_of_isInvertible`: an invertible ideal sheaf has
  no torsion.
* `colon_saturate_of_fg`: the saturation is saturated, `(I : K^∞) : K = (I : K^∞)`, for `K`
  finitely generated on affine opens (in particular invertible).
* `comap_subschemeι_eq_bot`: `I.comap I.subschemeι = ⊥`.
* `isInvertible_comap_subschemeι_of_colon_eq`: for `E` invertible and `S` with `(S : E) = S`,
  `E.comap S.subschemeι` is invertible.

## Conventions

`IsBlowUp I π` is the predicate of `Hironaka.Scheme.BlowUp.UniversalProperty`: `π` admissible and
every admissible morphism lifts uniquely. Closed subschemes are Mathlib's `IdealSheafData.subscheme`
with `subschemeι`; factorizations through them are `IsClosedImmersion.lift` (kernel containment).
The strict transform is `strictTransformAlong π E J`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-! ### The inverse image ideal sheaf and products, colons, saturations -/

/-- Every point of `Y` has an affine neighbourhood mapping into an affine open of `X`. -/
theorem exists_affineOpens_le_preimage (f : Y ⟶ X) (y : Y) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens), y ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
  obtain ⟨U, hU⟩ := exists_affineOpens_mem (f y)
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (f ⁻¹ᵁ U.1 : Set Y) from hU)
      (f ⁻¹ᵁ U.1).2
  exact ⟨U, ⟨V, hV⟩, hyV, hVU⟩

/-- The inverse image ideal sheaf is multiplicative ([Sta, Tag 080A]: the ideal of the exceptional
divisor of a composite of blow-ups is the product of the two inverse images), by the affine formula
`ideal_comap_of_le` on a cover. -/
theorem comap_mul (I K : X.IdealSheafData) (f : Y ⟶ X) :
    (I * K).comap f = I.comap f * K.comap f := by
  choose U V hyV hVU using exists_affineOpens_le_preimage f
  refine ext_of_iSup_eq_top V ?_ fun y => ?_
  · exact top_le_iff.mp fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hyV z⟩
  · rw [ideal_comap_of_le _ f (U y) (V y) (hVU y), ideal_mul, Pi.mul_apply, ideal_mul,
      Pi.mul_apply, ideal_comap_of_le I f (U y) (V y) (hVU y),
      ideal_comap_of_le K f (U y) (V y) (hVU y), Ideal.map_mul]

/-- The power form: `f⁻¹(K^n)·𝒪_Y = (f⁻¹K·𝒪_Y)^n`. -/
theorem comap_pow (K : X.IdealSheafData) (f : Y ⟶ X) (n : ℕ) :
    (K ^ n).comap f = K.comap f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, comap_mul, ih, pow_succ]

theorem comap_iSup {ι : Sort*} (I : ι → X.IdealSheafData) (f : Y ⟶ X) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f :=
  (map_gc f).l_iSup

theorem comap_colon_le (I K : X.IdealSheafData) (f : Y ⟶ X) :
    (I.colon K).comap f ≤ (I.comap f).colon (K.comap f) := by
  rw [le_colon_iff_mul_le, ← comap_mul]
  exact comap_mono f (colon_mul_le I K)

theorem comap_saturate_le (I K : X.IdealSheafData) (f : Y ⟶ X) :
    (I.saturate K).comap f ≤ (I.comap f).saturate (K.comap f) := by
  rw [saturate, comap_iSup]
  refine iSup_mono fun i => ?_
  rw [← comap_pow]
  exact comap_colon_le I (K ^ i) f

/-- An invertible ideal sheaf has no torsion: `(⊥ : E ^ i) = ⊥`. -/
theorem colon_pow_bot_of_isInvertible {E : X.IdealSheafData} (hE : E.IsInvertible) (i : ℕ) :
    (⊥ : X.IdealSheafData).colon (E ^ i) = ⊥ := by
  refine le_antisymm ?_ bot_le
  have hEi := isInvertible_pow hE i
  choose U hxU e he hEe using hEi
  refine le_of_iSup_eq_top U ?_ fun x => ?_
  · exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  · intro u hu
    have hu' := ideal_colon_le ⊥ (E ^ i) (U x) hu
    rw [hEe x] at hu'
    have hue : u * e x ∈ (⊥ : X.IdealSheafData).ideal (U x) := by
      simpa using Submodule.mem_colon.mp hu' (e x) (Ideal.mem_span_singleton_self _)
    rw [ideal_bot, Pi.bot_apply, Ideal.mem_bot] at hue
    rw [ideal_bot, Pi.bot_apply, Ideal.mem_bot]
    exact (he x).2 u hue

theorem saturate_bot_of_isInvertible {E : X.IdealSheafData} (hE : E.IsInvertible) :
    (⊥ : X.IdealSheafData).saturate E = ⊥ := by
  rw [saturate]
  exact iSup_eq_bot.mpr fun i => colon_pow_bot_of_isInvertible hE i

/-- For `K` finitely generated on every affine open, `((I : K^∞) : K) = (I : K^∞)`: the saturation
is saturated. -/
theorem colon_saturate_of_fg (I K : X.IdealSheafData) (hK : ∀ U : X.affineOpens, (K.ideal U).FG) :
    (I.saturate K).colon K = I.saturate K := by
  refine le_antisymm ?_ (le_colon_self _ K)
  refine le_def.mpr fun U => ?_
  rw [ideal_colon_of_fg _ K hK U, ideal_saturate]
  intro u hu
  obtain ⟨s, hs⟩ := hK U
  have hdir : Directed (· ≤ ·) fun i : ℕ => (I.colon (K ^ i)).ideal U :=
    (show Monotone (fun i : ℕ => (I.colon (K ^ i)).ideal U) from
      fun _ _ h => colon_pow_mono I K h U).directed_le
  -- each generator `k ∈ s` has `u * k` in some `(I : K^{i_k})(U)`; take the largest index
  have key : ∀ k ∈ s, ∃ i : ℕ, u * k ∈ (I.colon (K ^ i)).ideal U := by
    intro k hk
    have : u * k ∈ ⨆ i : ℕ, (I.colon (K ^ i)).ideal U := by
      simpa using Submodule.mem_colon.mp hu k (hs ▸ Ideal.subset_span hk)
    exact (Submodule.mem_iSup_of_directed _ hdir).mp this
  choose! n hn using key
  classical
  set N := s.sup n with hN
  -- `u * K(U) ⊆ (I(U) : K(U)^N)`
  have hspan : ∀ b ∈ K.ideal U,
      u * b ∈ (I.ideal U).colon ((K.ideal U ^ N : Ideal Γ(X, U)) : Set Γ(X, U)) := by
    have hle : K.ideal U ≤
        ((I.ideal U).colon ((K.ideal U ^ N : Ideal Γ(X, U)) : Set Γ(X, U))).colon {u} := by
      conv_lhs => rw [← hs]
      rw [Ideal.span_le]
      intro k hk
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
      have h1 := ideal_colon_le I (K ^ (n k)) U (hn k hk)
      rw [ideal_pow, Pi.pow_apply] at h1
      exact Submodule.colon_mono le_rfl
        (SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (Finset.le_sup (f := n) hk))) h1
    intro b hb
    have := hle hb
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] at this
  refine (Submodule.mem_iSup_of_directed _ hdir).mpr ⟨N + 1, ?_⟩
  rw [ideal_colon_of_fg _ (K ^ (N + 1)) (fun V => (hK V).pow) U, ideal_pow, Pi.pow_apply, pow_succ]
  refine Submodule.mem_colon.mpr fun v hv => ?_
  rw [smul_eq_mul]
  refine Submodule.mul_induction_on hv (fun a ha b hb => ?_)
    (fun x y hx hy => by rw [mul_add]; exact add_mem hx hy)
  rw [show u * (a * b) = (u * b) * a by ring]
  simpa using Submodule.mem_colon.mp (hspan b hb) a ha

/-! ### Closed subschemes: the kernel of the inclusion and the restriction of an invertible ideal -/

/-- `I.comap I.subschemeι = ⊥`: the ideal of a closed subscheme pulls back to zero on it. -/
theorem comap_subschemeι_eq_bot (I : X.IdealSheafData) : I.comap I.subschemeι = ⊥ := by
  have h : I ≤ (⊥ : I.subscheme.IdealSheafData).map I.subschemeι := by
    rw [map_bot, ker_subschemeι]
  exact le_bot_iff.mp (le_map_iff_comap_le.mp h)

/-- The restriction of an invertible ideal sheaf `E` to the closed subscheme of an `E`-saturated
ideal sheaf `S` (`(S : E) = S`) is invertible: on an affine open where `E = (e)` with `e` a
nonzerodivisor, `e` stays a nonzerodivisor modulo `S(U)`, because `u e ∈ S(U)` forces
`u ∈ (S(U) : e) = S(U)`. -/
theorem isInvertible_comap_subschemeι_of_colon_eq {E S : X.IdealSheafData} (hE : E.IsInvertible)
    (hS : S.colon E = S) : (E.comap S.subschemeι).IsInvertible := by
  intro z
  obtain ⟨U, hxU, e, he, hEe⟩ := hE (S.subschemeι z)
  let ι := S.subschemeι
  let V : S.subscheme.affineOpens := ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩
  have hzV : z ∈ V.1 := hxU
  refine ⟨V, hzV, ι.app U.1 e, ?_, ?_⟩
  · -- `ē` is a nonzerodivisor of `Γ(V(S), ι⁻¹U) = Γ(U)/S(U)`
    have hker : ∀ u : Γ(X, U), ι.app U.1 u = 0 ↔ u ∈ S.ideal U := fun u => by
      rw [← S.ker_subschemeι_app U, RingHom.mem_ker]
    have hcol : (S.ideal U).colon ({e} : Set Γ(X, U)) = S.ideal U := by
      have this : (S.colon E).ideal U = S.ideal U := by rw [hS]
      rw [ideal_colon_of_isInvertible S E hE U, hEe, Ideal.colon_span] at this
      exact this
    have key : ∀ w : Γ(S.subscheme, V), w * ι.app U.1 e = 0 → w = 0 := by
      intro w hw
      obtain ⟨u, rfl⟩ := S.subschemeι_app_surjective U w
      rw [← map_mul, hker] at hw
      have hu : u ∈ (S.ideal U).colon ({e} : Set Γ(X, U)) :=
        Submodule.mem_colon_singleton.mpr (by simpa using hw)
      rw [hcol] at hu
      exact (hker u).mpr hu
    exact mem_nonZeroDivisors_iff.mpr ⟨fun w hw => key w (by rw [mul_comm]; exact hw), key⟩
  · -- `(E.comap ι)(V) = (ē)`
    rw [ideal_comap_of_le E ι U V le_rfl, hEe, Ideal.map_span, Set.image_singleton,
      Scheme.Hom.appLE_eq_app]

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### The strict transform is the blow-up of the closed subscheme -/

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry.Scheme

variable {X B B' : Scheme.{u}} {D J : X.IdealSheafData}

/-- **The strict transform is a blow-up** [Sta, Tag 080E]; [Hau14, Corollary 5.2 (a)]: for any
blow-up `π : B ⟶ X` of `X` along `D` and any blow-up `π' : B' ⟶ V(J)` of the closed subscheme
`V(J)` along `D.comap ι` (in the sense of `IsBlowUp`), `B'` is isomorphic to the strict transform
`V(Jˢ) ⊆ B`, compatibly with the maps to `X`. Proof by the universal property alone (see the module
docstring): the lift `φ` of `π' ≫ ι` lands in `V(Jˢ)`; the lift `ψ` of `V(Jˢ) → V(J)`, admissible
because the exceptional ideal restricts to an invertible ideal on the saturated subscheme, is its
inverse by uniqueness of lifts. -/
theorem exists_iso_strictTransform_subscheme {π : B ⟶ X} {π' : B' ⟶ J.subscheme}
    (hπ : IsBlowUp D π) (hπ' : IsBlowUp (D.comap J.subschemeι) π') :
    ∃ e : B' ≅ (J.strictTransformAlong π (D.comap π)).subscheme,
      e.hom ≫ (J.strictTransformAlong π (D.comap π)).subschemeι ≫ π = π' ≫ J.subschemeι := by
  set ι := J.subschemeι with hι
  set E := D.comap π with hE
  set S := J.strictTransformAlong π E with hSdef
  set ιs := S.subschemeι with hιs
  have hEfg : ∀ U : B.affineOpens, (E.ideal U).FG := fun U =>
    (IdealSheafData.IsInvertible.ideal E hπ.admissible U).fg
  have hSsat : S.colon E = S := IdealSheafData.colon_saturate_of_fg (J.comap π) E hEfg
  -- Step 1: `π' ≫ ι` is admissible, so it lifts to `φ : B' ⟶ B`
  have hadm₁ : (D.comap (π' ≫ ι)).IsInvertible := by
    rw [IdealSheafData.comap_comp]; exact hπ'.admissible
  obtain ⟨φ, hφ⟩ := hπ.exists_lift (π' ≫ ι) hadm₁
  -- Step 2: `φ` lands in `V(S)`
  have hJφ : (J.comap π).comap φ = ⊥ := by
    rw [← IdealSheafData.comap_comp, hφ, IdealSheafData.comap_comp, hι,
      IdealSheafData.comap_subschemeι_eq_bot, IdealSheafData.comap_bot]
  have hEφ : E.comap φ = D.comap (π' ≫ ι) := by
    rw [hE, ← IdealSheafData.comap_comp, hφ]
  have hSφ : S.comap φ = ⊥ := by
    refine le_bot_iff.mp ((IdealSheafData.comap_saturate_le _ _ φ).trans ?_)
    rw [hJφ, hEφ, IdealSheafData.saturate_bot_of_isInvertible hadm₁]
  have hker₁ : ιs.ker ≤ φ.ker := by
    rw [hιs, IdealSheafData.ker_subschemeι, ← IdealSheafData.map_bot,
      IdealSheafData.le_map_iff_comap_le, hSφ]
  let φ' : B' ⟶ S.subscheme := IsClosedImmersion.lift ιs φ hker₁
  have hφ' : φ' ≫ ιs = φ := IsClosedImmersion.lift_fac ιs φ hker₁
  -- Step 3: `ιs ≫ π` factors through `ι` as `g`, admissible for `D.comap ι`; lift it to `ψ`
  have hker₂ : ι.ker ≤ (ιs ≫ π).ker := by
    rw [hι, IdealSheafData.ker_subschemeι, ← IdealSheafData.map_bot,
      IdealSheafData.le_map_iff_comap_le, IdealSheafData.comap_comp]
    exact (IdealSheafData.comap_mono ιs (IdealSheafData.le_saturate (J.comap π) E)).trans
      (IdealSheafData.comap_subschemeι_eq_bot S).le
  let g : S.subscheme ⟶ J.subscheme := IsClosedImmersion.lift ι (ιs ≫ π) hker₂
  have hg : g ≫ ι = ιs ≫ π := IsClosedImmersion.lift_fac ι (ιs ≫ π) hker₂
  have hEιs : (E.comap ιs).IsInvertible :=
    IdealSheafData.isInvertible_comap_subschemeι_of_colon_eq hπ.admissible hSsat
  have hadm₂ : ((D.comap ι).comap g).IsInvertible := by
    rw [← IdealSheafData.comap_comp, hg, IdealSheafData.comap_comp]; exact hEιs
  have hadm₃ : (D.comap (ιs ≫ π)).IsInvertible := by
    rw [IdealSheafData.comap_comp]; exact hEιs
  obtain ⟨ψ, hψ⟩ := hπ'.exists_lift g hadm₂
  -- Step 4: the two composites are identities, by uniqueness of lifts
  have hφ'g : φ' ≫ g = π' := by
    rw [← cancel_mono ι, Category.assoc, hg, ← Category.assoc, hφ', hφ]
  have h₁ : φ' ≫ ψ = 𝟙 B' :=
    hπ'.hom_ext π' hπ'.admissible (φ' ≫ ψ) (𝟙 B')
      (by rw [Category.assoc, hψ, hφ'g]) (Category.id_comp _)
  have hψφ : ψ ≫ φ = ιs :=
    hπ.hom_ext (ιs ≫ π) hadm₃ (ψ ≫ φ) ιs
      (by rw [Category.assoc, hφ, ← Category.assoc, hψ, hg]) rfl
  have h₂ : ψ ≫ φ' = 𝟙 S.subscheme := by
    rw [← cancel_mono ιs, Category.assoc, hφ', hψφ, Category.id_comp]
  refine ⟨⟨φ', ψ, h₁, h₂⟩, ?_⟩
  change φ' ≫ ιs ≫ π = π' ≫ ι
  rw [← Category.assoc, hφ', hφ]

end AlgebraicGeometry
