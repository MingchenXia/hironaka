/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Resolution.Algebraic.Balanced.GoingUpChain
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tools for the core lemma of the smooth case

The core lemma of `bed_eq_nil_of_smooth` — the first centre of `BMO_1(X, I_Y, 1, ∅)` for a smooth
`Y` contains a generic point of `Y` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`) — is
proved by the descent along closed embeddings of Kollár's Claim 71.2 ([Kol07, 71], proved in [Kol07,
108]) along a local cover carrying a smooth hypersurface of maximal contact (Step 3 of the proof of
[Kol07, Theorem 103]). This module holds its general tools:

* the order of the ideal of a smooth closed subscheme is at most `1` at every point where it is
  nonzero (`stalkIdeal_eq_bot_of_two_le_ord_of_smooth`: a regular quotient of a regular local ring
  is cut out by part of a regular system of parameters, [Sta, Tag 00NR];
  `maxOrd_le_one_of_smooth`), and `max-ord I ≥ 1` for `I ≠ 𝒪_X`;
* generic points of a support are carried by a surjective coproduct of open immersions
  (`mem_genericPoints_of_openImmersionCoprods`: an open embedding reflects specialization);
* the subscheme of `I.comap g` is smooth over `k` for a smooth `g` (`smooth_comap_subschemeι_comp`:
  Mathlib's `comapIso` and the base change), and `V(J) ≅ V(j_* J)` for a closed immersion `j`
  (`smooth_subschemeι_comp_of_map`);
* when no component of a smooth hypersurface `H ⊇ V(I)` lies in `V(I)` — `Z_{-1}(I, 1, H) = 𝒪_X`
  in the notation of the proof of [Kol07, Lemma 102] — the restriction `I|_H` is nonzero on every
  component of `H` (`isNonzeroEverywhere_comap_subschemeι_of_Zminus1_eq_top`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme.BlowUpSequence Hironaka.Sequence IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-! ### The order of the ideal of a smooth closed subscheme -/

/-- If `V(Z)` is smooth over `k` and `Z` has order `≥ 2` at `x`, then `Z_x = 0`: `Z_x` is generated
by an initial segment of a regular system of parameters (the quotient is regular,
[Sta, Tag 00NR]), none of which lies in `𝔪_x²`. -/
theorem stalkIdeal_eq_bot_of_two_le_ord_of_smooth {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] {x : X}
    (hx : ((2 : ℕ) : ℕ∞) ≤ Z.ord x) : Z.stalkIdeal x = ⊥ := by
  have hxs : x ∈ Z.support := by
    by_contra h
    have h0 : Z.ord x = 0 := (Scheme.IdealSheafData.ord_eq_zero_iff _ _).mpr h
    rw [h0] at hx
    exact absurd hx (by simp)
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  have hregq : IsRegularLocalRing (X.presheaf.stalk x ⧸ Z.stalkIdeal x) :=
    isRegularLocalRing_quotient_stalkIdeal Z f hxs
  have hle : Z.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
    rw [ord_eq_ord_stalkIdeal] at hx
    exact IsLocalRing.le_ord_iff.mp hx
  obtain ⟨m, c, y, hcle, hm, hmax, hK⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt
      (Z.stalkIdeal x)
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [hK]
    have : (y '' {i : Fin m | i.val < 0}) = ∅ := by
      ext a
      simp
    rw [this, Ideal.span_empty]
  · exfalso
    have hcm : 0 < m := lt_of_lt_of_le hc hcle
    have hmem : y ⟨0, hcm⟩ ∈ Z.stalkIdeal x := by
      rw [hK]
      exact Ideal.subset_span ⟨⟨0, hcm⟩, hc, rfl⟩
    exact notMem_sq_of_span_eq y hmax hm ⟨0, hcm⟩ (hle hmem)

/-- The ideal of a smooth closed subscheme, nonzero on every component, has maximal order
`≤ 1`. -/
theorem maxOrd_le_one_of_smooth {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] (hZ : IsNonzeroEverywhere Z) :
    Z.maxOrd ≤ ((1 : ℕ) : ℕ∞) := by
  rw [maxOrd_le_iff]
  intro x
  by_contra h
  have h1 : ((1 : ℕ) : ℕ∞) < Z.ord x := not_le.mp h
  have h2 := Order.add_one_le_of_lt h1
  rw [show ((1 : ℕ) : ℕ∞) + 1 = ((2 : ℕ) : ℕ∞) by norm_num] at h2
  exact hZ x (stalkIdeal_eq_bot_of_two_le_ord_of_smooth f Z h2)

/-- A point of the support of an ideal sheaf other than the unit ideal. -/
theorem exists_mem_support_of_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I ≠ ⊤) :
    ∃ x, x ∈ I.support := by
  by_contra h
  refine hI ?_
  rw [← support_eq_bot_iff]
  exact le_antisymm (fun y hy => (h ⟨y, hy⟩).elim) bot_le

/-- An ideal sheaf other than the unit ideal has maximal order `≥ 1`. -/
theorem one_le_maxOrd_of_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I ≠ ⊤) :
    ((1 : ℕ) : ℕ∞) ≤ I.maxOrd := by
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_top I hI
  rw [Nat.cast_one]
  exact ((one_le_ord_iff I x).mpr hx).trans (le_maxOrd I x)

/-- The ideal of a nonempty smooth closed subscheme, nonzero on every component, has maximal order
exactly `1`. -/
theorem maxOrd_eq_one_of_smooth_of_ne_top {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    (Z : X.IdealSheafData) [Smooth (Z.subschemeι ≫ f)] (hZ : IsNonzeroEverywhere Z) (hne : Z ≠ ⊤) :
    Z.maxOrd = ((1 : ℕ) : ℕ∞) :=
  le_antisymm (maxOrd_le_one_of_smooth f Z hZ) (one_le_maxOrd_of_ne_top Z hne)

/-! ### Generic points along a cover and along a closed immersion -/

/-- A surjective coproduct of open immersions `g` carries a generic point of `supp (g^* I)` to a
generic point of `supp I` — `g` restricted to the summand through the point is an open embedding,
whose range is closed under generization and which reflects specialization. -/
theorem mem_genericPoints_of_openImmersionCoprods {X Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : openImmersionCoprods g) (I : X.IdealSheafData) {y : Y}
    (hy : y ∈ (I.comap g).support.genericPoints) : g y ∈ I.support.genericPoints := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  obtain ⟨i, u, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
  refine ⟨(mem_support_comap_iff_apply I g _).mp hy.1, fun x hx hxs => ?_⟩
  have hoe : Topology.IsOpenEmbedding (ι i ≫ g) := have := hι i; (ι i ≫ g).isOpenEmbedding
  have hxr : x ∈ Set.range (ι i ≫ g) :=
    hxs.mem_open hoe.isOpen_range ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨u', hu'⟩ := hxr
  have h1 : (ι i ≫ g) u' ⤳ (ι i ≫ g) u := by
    rw [hu', Scheme.Hom.comp_apply]
    exact hxs
  have h2 : u' ⤳ u := hoe.toIsEmbedding.toIsInducing.specializes_iff.mp h1
  have hspec : ι i u' ⤳ ι i u := h2.map (ι i).continuous
  have hmemx : ι i u' ∈ (I.comap g).support := by
    rw [mem_support_comap_iff_apply, ← Scheme.Hom.comp_apply, hu']
    exact hx
  have := hy.2 hmemx hspec
  rw [← hu', Scheme.Hom.comp_apply, this]

/-- The image of a point of the support under a closed immersion lies in the support of the
pushed-forward ideal. -/
theorem mem_support_map_of_mem {X Y : Scheme.{u}} (j : Y ⟶ X) [IsClosedImmersion j]
    (J : Y.IdealSheafData) {y : Y} (hy : y ∈ J.support) : j y ∈ (J.map j).support := by
  rw [← SetLike.mem_coe, coe_support_map_of_isClosedImmersion]
  exact ⟨y, hy, rfl⟩

/-! ### Smoothness of the subscheme along a pullback and along a pushforward -/

/-- The subscheme of `g^* I` for a smooth `g : Y ⟶ X` is smooth over `k` when `V(I)` is — it is the
base change of `V(I)` along `g` (Mathlib's `comapIso`). -/
theorem smooth_comap_subschemeι_comp {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X)
    [Smooth g] (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] :
    Smooth ((I.comap g).subschemeι ≫ g ≫ f) := by
  have h : (I.comap g).subschemeι ≫ g ≫ f =
      (I.comapIso g).hom ≫ pullback.snd g I.subschemeι ≫ (I.subschemeι ≫ f) := by
    rw [← comapIso_hom_fst I g]
    simp only [Category.assoc, pullback.condition_assoc]
  rw [h]
  infer_instance

/-- For a closed immersion `j : Y ⟶ X` and `J` on `Y`, the subscheme `V(J)` is smooth over `k` when
`V(j_* J)` is — `V(J) ⟶ V(j_* J)` is an isomorphism (`j_* J` is the kernel of `V(J) ⟶ Y ⟶ X`,
Mathlib's `Hom.toImage`). -/
theorem smooth_subschemeι_comp_of_map {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : Y ⟶ X)
    [IsClosedImmersion j] (J : Y.IdealSheafData) [Smooth ((J.map j).subschemeι ≫ f)] :
    Smooth (J.subschemeι ≫ j ≫ f) := by
  have hiso : IsIso (J.subschemeι ≫ j).toImage :=
    IsClosedImmersion.isIso_of_ker_eq (J.subschemeι ≫ j) (J.subschemeι ≫ j).imageι
      (J.subschemeι ≫ j).toImage (Scheme.Hom.toImage_imageι _) (ker_subschemeι _).symm
  have hs : Smooth ((J.subschemeι ≫ j).imageι ≫ f) := ‹Smooth ((J.map j).subschemeι ≫ f)›
  have h : J.subschemeι ≫ j ≫ f =
      (J.subschemeι ≫ j).toImage ≫ (J.subschemeι ≫ j).imageι ≫ f := by
    rw [Scheme.Hom.toImage_imageι_assoc, Category.assoc]
  rw [h]
  infer_instance

/-! ### Nonvanishing of the restriction to a hypersurface without absorbed components -/

/-- If no irreducible component of the hypersurface `H` lies in `V(I)` — `Z_{-1}(I, 1, H) = 𝒪_X`
in the notation of the proof of [Kol07, Lemma 102] — then `I|_H` is nonzero on every irreducible
component of `V(H)`: at a generic point `η` of a component of `V(H)`, `(I|_H)_η = 0` would put
`I_{ι η}` inside `H_{ι η}`, hence `ι η ∈ supp I` with `ord_{ι η} I ≥ 1`, so `ι η` would be a
selected generic point of `Z_{-1}`. -/
theorem isNonzeroEverywhere_comap_subschemeι_of_Zminus1_eq_top {X : Scheme.{u}}
    (I H : X.IdealSheafData) (hZ : Hironaka.BD.Zminus1 I 1 H = ⊤) :
    IsNonzeroEverywhere (I.comap H.subschemeι) := by
  rw [isNonzeroEverywhere_iff_irreducibleComponents]
  intro W hW η hη hbot
  have hle : I.stalkIdeal (H.subschemeι η) ≤ H.stalkIdeal (H.subschemeι η) := by
    rw [stalkIdeal_comap, Ideal.map_eq_bot_iff_le_ker, ker_stalkMap_subschemeι] at hbot
    exact hbot
  have hmem : H.subschemeι η ∈ I.support := by
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
    exact hle.trans ((mem_support_iff_stalkIdeal_le_maximalIdeal H _).mp
      (subschemeι_mem_support H η))
  have hord : ((1 : ℕ) : ℕ∞) ≤ I.ord (H.subschemeι η) := by
    rw [Nat.cast_one]
    exact (one_le_ord_iff I _).mpr hmem
  have hgen :=
    Hironaka.Resolution.mem_genericPoints_support_of_isGenericPoint_of_mem_irreducibleComponents
      H hW hη
  have hin : H.subschemeι η ∈ (Hironaka.BD.Zminus1 I 1 H).support := by
    rw [Hironaka.BD.Zminus1, Hironaka.Sequence.support_vanishingIdeal_eq]
    have hle' : Closeds.closure {H.subschemeι η} ≤
        ⨆ ξ : {ξ : X // ξ ∈ H.support.genericPoints ∧ ((1 : ℕ) : ℕ∞) ≤ I.ord ξ},
          Closeds.closure {(ξ : X)} :=
      le_iSup (fun ξ : {ξ : X // ξ ∈ H.support.genericPoints ∧ ((1 : ℕ) : ℕ∞) ≤ I.ord ξ} =>
        Closeds.closure {(ξ : X)}) ⟨H.subschemeι η, hgen, hord⟩
    exact hle' (by
      rw [← SetLike.mem_coe, Closeds.coe_closure]
      exact subset_closure (Set.mem_singleton _))
  rw [hZ, support_top] at hin
  exact hin

end Hironaka.Resolution
