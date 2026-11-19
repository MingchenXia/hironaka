/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.TotalTransformData
public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Glue.RestrictOpen
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.ExceptionalDivisor
import Hironaka.Scheme.Smooth.StandardChart
import Hironaka.Scheme.Snc.ChartSncData
import Hironaka.Scheme.Snc.ChartStalk
import Hironaka.Scheme.Snc.RelativeDimension
import Hironaka.Scheme.Snc.SpreadSnc
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform at a point of the exceptional divisor

At a point `x'` of the exceptional divisor `F` of the blow-up `π : B_Z X → X` of a smooth variety
along a centre `Z` having simple normal crossings with a divisor `E`, the stalk `𝒪_{B,x'}` together
with the stalks of `F` and of the total transforms `π^{-1}(E^i)` has the shape `TotalTransformData`
(`exists_totalTransformData_of_mem_support`): a regular local ring, a regular system of parameters
`z`, `F = (z_j)`, each total transform of one of the four shapes of Hauser's chart computation. This
is the chart computation of the proof of [Hau14, Proposition 5.3] and of [Hau14, Proposition 5.4]
([Hau03, Appendix C]) read at an arbitrary, possibly non-closed, point;
`Hironaka.Scheme.Snc.TotalTransformSnc` reads Kollár's conditions off it.

**Why the theorem holds.** Let `x = π(x')`. A closed point `x₀` of the closure of `x` exists because
`X` is Jacobson (locally of finite type over a field), and `x₀ ∈ Z` as `Z` is closed.
[Kol07, Definition 24 (4)] gives snc coordinates at `x₀`; on an affine neighbourhood `V₀` of `x₀` on
which `f` has constant relative dimension they spread to a chart `U ∋ x₀` of étale coordinates
adapted to `Z` on which the components through `x₀` are coordinate hyperplanes and the others are
absent (`exists_etaleCoordinatesAdapted_of_snc` of `Hironaka.Scheme.Snc.SpreadSnc`); `U` contains
`x` because `x ⤳ x₀`. The point `x'` lies over `U`, hence in `B_{Z∩U} U ≅ π^{-1}(U)`
(`exists_restrictHom_eq`), in the chart of some `x_j` as a prime `p` of the chart ring
(`exists_chart_point_map_stalkIdeal_eq` of `Hironaka.Scheme.Snc.ChartStalk`), and the chart
computation (`totalTransformData_chart` of `Hironaka.Scheme.Snc.ChartSncData`) gives the shape in
`Γ(U)[J/x_j]_p`, which transports along the isomorphisms of stalks back to `𝒪_{B,x'}`
(`TotalTransformData.of_ringEquiv`, `TotalTransformData.of_comap_isOpenImmersion`).

Sources: [Hau14, Proposition 5.3] (the proof); [Hau14, Proposition 5.4]; [Hau03, Appendix C];
[Kol07, Definition 24; Definition 60].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal TopologicalSpace Scheme.IdealSheafData
  Scheme.Hom

namespace AlgebraicGeometry

section Transport

variable {Y X' : Scheme.{u}}

/-- The total-transform shape transports along an open immersion: the stalk map is an isomorphism
carrying the stalks of the inverse images to the stalks. -/
theorem TotalTransformData.of_comap_isOpenImmersion (ι : Y ⟶ X') [IsOpenImmersion ι]
    {κ : Type*} (F : X'.IdealSheafData) (T : κ → X'.IdealSheafData) (y : Y)
    {F' : Y.IdealSheafData} {T' : κ → Y.IdealSheafData} (hF : F.comap ι = F')
    (hT : ∀ i, (T i).comap ι = T' i)
    (h : TotalTransformData (F'.stalkIdeal y) fun i => (T' i).stalkIdeal y) :
    TotalTransformData (F.stalkIdeal (ι y)) fun i => (T i).stalkIdeal (ι y) := by
  have : IsIso (ι.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap ι y
  have hbij : Function.Bijective (ι.stalkMap y).hom := ConcreteCategory.bijective_of_isIso _
  refine TotalTransformData.of_ringEquiv (RingEquiv.ofBijective (ι.stalkMap y).hom hbij) ?_
    (fun i => ?_) h
  · rw [← hF]
    exact (Scheme.IdealSheafData.stalkIdeal_comap F ι y).symm
  · rw [← hT i]
    exact (Scheme.IdealSheafData.stalkIdeal_comap (T i) ι y).symm

end Transport

section Restrict

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)

/-- Every point of `B_I X` over `U` comes from `B_{I|_U} U` along `blowUpMap U.ι I`. -/
theorem exists_restrictHom_eq (x' : blowUp I) (hx' : blowUpπ I x' ∈ U) :
    ∃ b : blowUp (I.comap U.ι), blowUpMap U.ι I b = x' := by
  have hx'U : x' ∈ blowUpπ I ⁻¹ᵁ U := hx'
  let u : (blowUpπ I ⁻¹ᵁ U : Scheme.{u}) := ⟨x', hx'U⟩
  refine ⟨(blowUp.restrictIso I U).inv u, ?_⟩
  rw [← restrictHomToPreimage_ι, Scheme.Hom.comp_apply]
  change (blowUpπ I ⁻¹ᵁ U).ι ((blowUp.restrictIso I U).hom
    ((blowUp.restrictIso I U).inv u)) = x'
  rw [← Scheme.Hom.comp_apply (blowUp.restrictIso I U).inv (blowUp.restrictIso I U).hom,
    Iso.inv_hom_id]
  rfl

/-- The inverse image along `π` of an ideal sheaf `D`, pulled back to `B_{I|_U} U`, is the inverse
image of `D|_U` along `π_U` (`blowUpMap U.ι I ≫ π = π_U ≫ U.ι`; the general form of
`comap_restrictHom`). -/
theorem comap_π_comap_restrictHom (D : X.IdealSheafData) :
    (D.comap (blowUpπ I)).comap (blowUpMap U.ι I) =
      (D.comap U.ι).comap (blowUpπ (I.comap U.ι)) :=
  (Scheme.IdealSheafData.comap_comp D _ _).symm.trans
    ((congrArg (fun m => D.comap m) (blowUpMap_π U.ι I)).trans
      (Scheme.IdealSheafData.comap_comp D _ _))

end Restrict

section Local

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A smooth morphism to `Spec k` has, around every point, an affine open on which it is smooth of
a constant relative dimension — the dimension of a standard smooth presentation of the section
ring (Mathlib's `Smooth.exists_isStandardSmooth`, read with
`smoothOfRelativeDimension_of_forall_exists_affineOpen`). -/
theorem exists_affineOpen_smoothOfRelativeDimension (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ (V : X.affineOpens) (_ : x ∈ V.1) (m : ℕ), SmoothOfRelativeDimension m (V.1.ι ≫ f) := by
  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hU'top : U' = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim (α := PrimeSpectrum k) y (f x)]
    exact e hxV
  subst hU'top
  let _ := (f.appLE ⊤ V e).hom.toAlgebra
  have hstd' : Algebra.IsStandardSmooth Γ(Spec (.of k), ⊤) Γ(X, V) := hstd
  obtain ⟨ι', σ', hσ', hι', ⟨P⟩⟩ := hstd'.out
  refine ⟨⟨V, hV⟩, hxV, P.dimension, ?_⟩
  have hrel' : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Spec (.of k), ⊤)
      Γ(X, V) := ⟨ι', σ', hσ', hι', P, rfl⟩
  have hrel : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE ⊤ V e).hom := hrel'
  have : IsAffine (V : Scheme.{u}) := hV
  refine smoothOfRelativeDimension_of_forall_exists_affineOpen (V.ι ≫ f) P.dimension fun y => ?_
  refine ⟨⊤, isAffineOpen_top _, trivial, ?_⟩
  let _ := (V.ι ≫ f).sectionsAlgebra ⊤
  have e' : (⊤ : (V : Scheme.{u}).Opens) ≤ V.ι ⁻¹ᵁ V := fun w _ => w.2
  have happ : (V.ι ≫ f).appLE ⊤ ⊤ le_top = f.appLE ⊤ V e ≫ V.topIso.inv := by
    rw [← ι_appLE_top_eq_topIso_inv V e', Scheme.Hom.appLE_comp_appLE]
  have h1 : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V e ≫ V.topIso.inv).hom := by
    have hiso := RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := P.dimension)
    rw [CommRingCat.hom_comp, hiso.cancel_left_isIso, CommRingCat.hom_comp,
      hiso.cancel_right_isIso]
    exact hrel
  rw [← happ] at h1
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap P.dimension).mp h1

/-- Every point of a Jacobson space specializes to a closed point (Mathlib's
`nonempty_inter_closedPoints` on the closure of the point). -/
theorem exists_closedPoint_specializes {T : Type*} [TopologicalSpace T] [JacobsonSpace T] (x : T) :
    ∃ x₀ : T, x ⤳ x₀ ∧ IsClosed ({x₀} : Set T) := by
  obtain ⟨x₀, hx₀, hcl⟩ := nonempty_inter_closedPoints (X := T) (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact ⟨x₀, specializes_iff_mem_closure.mpr hx₀, hcl⟩

/-- Snc data at a point `x₀ = ι y₀` of `X` transport to the point `y₀` of an open `V ⊆ X` for the
restricted ideal sheaves. -/
theorem snc_data_comap_ι {ι : Type*} (D : ι → X.IdealSheafData) (Z : X.IdealSheafData)
    (V : X.Opens) (y₀ : (V : Scheme.{u})) {n : ℕ} {z : Fin n → X.presheaf.stalk (V.ι y₀)}
    (hz : span (Set.range z) = maximalIdeal (X.presheaf.stalk (V.ι y₀)) ∧
      (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (V.ι y₀)))
    {s : Finset (Fin n)} (hZ : Z.stalkIdeal (V.ι y₀) = span (z '' ↑s))
    (c : {i : ι // V.ι y₀ ∈ (D i).support} → Fin n) (hcinj : Function.Injective c)
    (hc : ∀ i, (D i.1).stalkIdeal (V.ι y₀) = span {z (c i)}) :
    ∃ z' : Fin n → (V : Scheme.{u}).presheaf.stalk y₀,
      (span (Set.range z') = maximalIdeal ((V : Scheme.{u}).presheaf.stalk y₀) ∧
        (n : WithBot ℕ∞) = ringKrullDim ((V : Scheme.{u}).presheaf.stalk y₀)) ∧
      (Z.comap V.ι).stalkIdeal y₀ = span (z' '' ↑s) ∧
      ∃ c' : {i : ι // y₀ ∈ ((D i).comap V.ι).support} → Fin n, Function.Injective c' ∧
        ∀ i, ((D i.1).comap V.ι).stalkIdeal y₀ = span {z' (c' i)} := by
  have : IsIso (V.ι.stalkMap y₀) := IsOpenImmersion.instIsIsoCommRingCatStalkMap V.ι y₀
  have hbij : Function.Bijective (V.ι.stalkMap y₀).hom := ConcreteCategory.bijective_of_isIso _
  set e : X.presheaf.stalk (V.ι y₀) ≃+* (V : Scheme.{u}).presheaf.stalk y₀ :=
    RingEquiv.ofBijective (V.ι.stalkMap y₀).hom hbij with hedef
  have hmem : ∀ i, y₀ ∈ ((D i).comap V.ι).support ↔ V.ι y₀ ∈ (D i).support := fun i => by
    rw [Scheme.IdealSheafData.support_comap]
    exact Iff.rfl
  have hmap : ∀ I : Ideal (X.presheaf.stalk (V.ι y₀)), I.map e = I.map (V.ι.stalkMap y₀).hom :=
    fun _ => rfl
  have hmax : (maximalIdeal (X.presheaf.stalk (V.ι y₀))).map (V.ι.stalkMap y₀).hom =
      maximalIdeal ((V : Scheme.{u}).presheaf.stalk y₀) := by
    rw [← hmap]
    have := map_maximalIdeal_ringEquiv e.symm
    rwa [RingEquiv.symm_symm] at this
  refine ⟨fun i => (V.ι.stalkMap y₀).hom (z i), ⟨?_, ?_⟩, ?_,
    fun i => c ⟨i.1, (hmem i.1).mp i.2⟩, ?_, fun i => ?_⟩
  · have h := congrArg (Ideal.map (V.ι.stalkMap y₀).hom) hz.1
    rw [Ideal.map_span, ← Set.range_comp, hmax] at h
    exact h
  · rw [hz.2]
    exact ringKrullDim_eq_of_ringEquiv e
  · rw [Scheme.IdealSheafData.stalkIdeal_comap, hZ, Ideal.map_span, Set.image_image]
  · intro i i' h
    have := hcinj h
    exact Subtype.ext (Subtype.mk.inj this)
  · rw [Scheme.IdealSheafData.stalkIdeal_comap, hc ⟨i.1, (hmem i.1).mp i.2⟩, Ideal.map_span,
      Set.image_singleton]

end Local

section Top

variable {X : Scheme.{u}}

/-- An ideal sheaf whose restriction to an affine open `U` is the unit ideal sheaf has
`D(U) = ⊤`. -/
theorem ideal_eq_top_of_comap_ι_eq_top (D : X.IdealSheafData) (U : X.affineOpens)
    (h : D.comap U.1.ι = ⊤) : D.ideal U = ⊤ := by
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  have e : (⊤ : (U.1 : Scheme.{u}).Opens) ≤ U.1.ι ⁻¹ᵁ U.1 := fun y _ => y.2
  have h1 : (D.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (D.ideal U).map U.1.topIso.inv.hom := by
    rw [D.ideal_comap_of_le U.1.ι U ⟨⊤, isAffineOpen_top _⟩ e]
    exact congrArg (fun φ : Γ(X, U) ⟶ Γ(U.1, ⊤) => (D.ideal U).map φ.hom)
      (ι_appLE_top_eq_topIso_inv U.1 e)
  rw [h, Scheme.IdealSheafData.ideal_top, Pi.top_apply] at h1
  have hbij : Function.Bijective U.1.topIso.inv.hom := ConcreteCategory.bijective_of_isIso _
  rw [← Ideal.comap_map_of_bijective U.1.topIso.inv.hom hbij (I := D.ideal U), ← h1,
    Ideal.comap_top]

end Top

section Main

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [Smooth f]

/-- Membership in the support of an inverse image. -/
theorem mem_support_comap_iff' {Y X' : Scheme.{u}} (K : X'.IdealSheafData) (φ : Y ⟶ X') (y : Y) :
    y ∈ (K.comap φ).support ↔ φ y ∈ K.support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact Iff.rfl

/-- Containments of stalk ideals transport along an open immersion (in both directions). -/
theorem stalkIdeal_le_iff_of_isOpenImmersion {Y : Scheme.{u}} (ι : Y ⟶ X) [IsOpenImmersion ι]
    (I J : X.IdealSheafData) (y : Y) :
    (I.comap ι).stalkIdeal y ≤ (J.comap ι).stalkIdeal y ↔
      I.stalkIdeal (ι y) ≤ J.stalkIdeal (ι y) := by
  have : IsIso (ι.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap ι y
  have hbij : Function.Bijective (ι.stalkMap y).hom := ConcreteCategory.bijective_of_isIso _
  have hI := Scheme.IdealSheafData.stalkIdeal_comap I ι y
  have hJ := Scheme.IdealSheafData.stalkIdeal_comap J ι y
  constructor
  · intro h
    have h' := Ideal.comap_mono (f := (ι.stalkMap y).hom) (hI.symm.le.trans (h.trans hJ.le))
    exact (Ideal.comap_map_of_bijective _ hbij (I := I.stalkIdeal (ι y))).symm.le.trans
      (h'.trans (Ideal.comap_map_of_bijective _ hbij (I := J.stalkIdeal (ι y))).le)
  · intro h
    exact hI.le.trans ((Ideal.map_mono h).trans hJ.symm.le)

include f in
/-- The chart computation of the proofs of [Hau14, Proposition 5.3] and [Hau14, Proposition 5.4]
([Hau03, Appendix C]) at a possibly non-closed point: at a point `x'` of the exceptional divisor of
the blow-up of `X` along a centre `Z` with simple normal crossings with the family `D`
([Kol07, Definition 24 (4)], given as data), the stalks of the exceptional divisor and of the total
transforms of the components have Hauser's chart shape `TotalTransformData`; moreover a component
whose total transform lies in the exceptional ideal at `x'` contains `Z` near `π(x')`.

The pointwise form: the snc data are needed only at the points of `Z` to which `π(x')` specializes —
the proof uses them at ONE closed point `x₀` with `π(x') ⤳ x₀` — so the hypothesis asks for them
there only; `exists_totalTransformData_of_mem_support` (data at every point of `Z`) is the corollary
below. -/
theorem exists_totalTransformData_of_mem_support_of_specializes {ι : Type*} [Finite ι]
    (D : ι → X.IdealSheafData) (Z : X.IdealSheafData)
    (x' : blowUp Z) (hx' : x' ∈ (Z.comap (blowUpπ Z)).support)
    (hZ : ∀ x ∈ Z.support, blowUpπ Z x' ⤳ x → ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ c : {i : ι // x ∈ (D i).support} → Fin n, Function.Injective c ∧
        ∀ i, (D i.1).stalkIdeal x = span {z (c i)}) ∧
      ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s)) :
    TotalTransformData ((Z.comap (blowUpπ Z)).stalkIdeal x')
      (fun i => ((D i).comap (blowUpπ Z)).stalkIdeal x') ∧
    ∀ i, ((D i).comap (blowUpπ Z)).stalkIdeal x' ≤ (Z.comap (blowUpπ Z)).stalkIdeal x' →
      (D i).stalkIdeal (blowUpπ Z x') ≤ Z.stalkIdeal (blowUpπ Z x') := by
  classical
  -- the image point lies on the centre; a closed point of its closure lies on the centre too
  have hxZ : blowUpπ Z x' ∈ Z.support := (mem_support_comap_iff' Z _ x').mp hx'
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hcl := exists_closedPoint_specializes (blowUpπ Z x')
  obtain ⟨x₀, hspec, hx₀cl⟩ := hcl
  have hx₀Z : x₀ ∈ Z.support := hspec.mem_closed Z.support.isClosed hxZ
  -- Kollár's snc data at the closed point
  have hdata := hZ x₀ hx₀Z hspec
  obtain ⟨n, z, hz, ⟨c, hcinj, hc⟩, s, hZs⟩ := hdata
  -- an affine neighbourhood `V₀` of `x₀` on which `f` has constant relative dimension `m`
  have hV := exists_affineOpen_smoothOfRelativeDimension f x₀
  obtain ⟨V₀, hx₀V, m, hm⟩ := hV
  let y₀ : (V₀.1 : Scheme.{u}) := ⟨x₀, hx₀V⟩
  have hy₀cl : IsClosed ({y₀} : Set (V₀.1 : Scheme.{u})) := by
    have hpre : ({y₀} : Set (V₀.1 : Scheme.{u})) = V₀.1.ι ⁻¹' {x₀} := by
      ext w
      constructor
      · rintro rfl
        rfl
      · intro hw
        exact Subtype.ext hw
    rw [hpre]
    exact hx₀cl.preimage V₀.1.ι.continuous
  -- the snc data at `y₀ ∈ V₀`
  have htr := snc_data_comap_ι D Z V₀.1 y₀ hz hZs c hcinj hc
  obtain ⟨z', hz', hZ', c', hc'inj, hc'⟩ := htr
  -- the number of parameters is the relative dimension
  have hnm : n = m := by
    have h1 := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed
      (V₀.1.ι ≫ f) m hy₀cl
    have h2 := hz'.2
    rw [h1] at h2
    exact_mod_cast h2
  subst hnm
  -- the chart of étale coordinates adapted to `Z` on which the components are coordinate
  -- hyperplanes
  have hE := exists_etaleCoordinatesAdapted_of_snc (V₀.1.ι ≫ f) n
    (fun i => (D i).comap V₀.1.ι) hy₀cl hz'.1.symm s hZ' c' hc'inj hc'
  obtain ⟨E, c'', hc''inj, -, hideal, htop⟩ := hE
  -- `x'` lies over `V₀` and over the chart `E.U`
  have hxV : blowUpπ Z x' ∈ V₀.1 := hspec.mem_open V₀.1.isOpen hx₀V
  have hlift₁ := exists_restrictHom_eq Z V₀.1 x' hxV
  obtain ⟨b₁, hb₁⟩ := hlift₁
  subst hb₁
  have hπb₁ : V₀.1.ι (blowUpπ (Z.comap V₀.1.ι) b₁) =
      blowUpπ Z (blowUpMap V₀.1.ι Z b₁) := by
    rw [← Scheme.Hom.comp_apply, ← blowUpMap_π, Scheme.Hom.comp_apply]
  have hspec₀ : blowUpπ (Z.comap V₀.1.ι) b₁ ⤳ y₀ := by
    rw [← V₀.1.ι.isOpenEmbedding.isInducing.specializes_iff, hπb₁]
    exact hspec
  have hπb₁U : blowUpπ (Z.comap V₀.1.ι) b₁ ∈ E.U.1 := hspec₀.mem_open E.U.1.isOpen E.mem
  have hlift₂ := exists_restrictHom_eq (Z.comap V₀.1.ι) E.U.1 b₁ hπb₁U
  obtain ⟨b₂, hb₂⟩ := hlift₂
  subst hb₂
  -- names for the three exceptional divisors and the restriction maps
  let Z₀ := Z.comap V₀.1.ι
  let ρ₁ := blowUpMap V₀.1.ι Z
  let ρ₂ := blowUpMap E.U.1.ι Z₀
  let FU := (Z₀.comap E.U.1.ι).comap (blowUpπ (Z₀.comap E.U.1.ι))
  -- the point lies on the exceptional divisor of `B_{Z∩U} U`
  have hb₂F : b₂ ∈ FU.support := by
    have h₁ : ρ₂ b₂ ∈ (Z₀.comap (blowUpπ Z₀)).support := by
      have := (mem_support_comap_iff' (Z.comap (blowUpπ Z)) ρ₁ (ρ₂ b₂)).mpr hx'
      rwa [comap_restrictHom] at this
    have := (mem_support_comap_iff' (Z₀.comap (blowUpπ Z₀)) ρ₂ b₂).mpr h₁
    rwa [comap_restrictHom] at this
  -- the chart point and the two ring isomorphisms
  have hchart := exists_chart_point_map_stalkIdeal_eq E b₂
  obtain ⟨j, hj, p, e₁, e₂, hQ⟩ := hchart
  have hp : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let A := affineBlowUpAlgebra E.centerIdeal (E.coord j hj)
  let alg := algebraMap Γ((V₀.1 : Scheme.{u}), E.U) A
  let alg' := algebraMap A (Localization.AtPrime p.asIdeal)
  -- the exceptional ideal read in the chart
  have hFchart : ((FU.stalkIdeal b₂).map e₁).map e₂ = span {alg' (alg (E.v j))} :=
    (hQ Z₀ E.centerIdeal (ideal_eq_centerIdeal E)).trans
      ((congrArg (Ideal.map alg')
        (affineBlowUpAlgebra.map_algebraMap_eq_span_singleton (E.coord j hj).2)).trans
        ((Ideal.map_span alg' _).trans (congrArg span Set.image_singleton)))
  have hmax : ∀ {S S' : Type u} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
      (e : S ≃+* S'), (maximalIdeal S).map e = maximalIdeal S' := fun e => by
    have := map_maximalIdeal_ringEquiv e.symm
    rwa [RingEquiv.symm_symm] at this
  -- `y_j` vanishes at `p`
  have hjq : chartCoord E hj j ∈ p.asIdeal := by
    have hle := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal (I := FU)
      (x := b₂)).mp hb₂F
    have h1 := Ideal.map_mono (f := e₂) (Ideal.map_mono (f := e₁) hle)
    have h1' : span {alg' (alg (E.v j))} ≤ maximalIdeal (Localization.AtPrime p.asIdeal) :=
      hFchart.symm.le.trans (h1.trans ((congrArg (Ideal.map e₂) (hmax e₁)).trans (hmax e₂)).le)
    have hmem := h1' (mem_span_singleton_self _)
    rw [chartCoord_self]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal _).mp hmem
  -- the total transforms read in the chart
  let Tb : ι → Ideal ((blowUp (Z₀.comap E.U.1.ι)).presheaf.stalk b₂) := fun i =>
    (((D i).comap V₀.1.ι).comap E.U.1.ι).comap (blowUpπ (Z₀.comap E.U.1.ι)) |>.stalkIdeal b₂
  let T' : ι → Ideal (Localization.AtPrime p.asIdeal) := fun i => ((Tb i).map e₁).map e₂
  have hT : ∀ i (h : y₀ ∈ ((D i).comap V₀.1.ι).support),
      T' i = span {alg' (alg (E.v (c'' ⟨i, h⟩)))} := fun i h =>
    (hQ ((D i).comap V₀.1.ι) _ (hideal ⟨i, h⟩)).trans
      ((congrArg (Ideal.map alg')
        ((Ideal.map_span alg _).trans (congrArg span Set.image_singleton))).trans
        ((Ideal.map_span alg' _).trans (congrArg span Set.image_singleton)))
  have hT' : ∀ i, y₀ ∉ ((D i).comap V₀.1.ι).support → T' i = ⊤ := fun i h =>
    (hQ ((D i).comap V₀.1.ι) ⊤ (ideal_eq_top_of_comap_ι_eq_top _ _ (htop i h))).trans
      ((congrArg (Ideal.map alg') (Ideal.map_top alg)).trans (Ideal.map_top alg'))
  -- the chart computation
  have hchartData := totalTransformData_chart E hj p.asIdeal hjq (fun i => (D i).comap V₀.1.ι) c''
    hc''inj T' hT hT'
  obtain ⟨hshape, hlt⟩ := hchartData
  -- back along the ring isomorphisms and the two restrictions
  have h₂ := TotalTransformData.of_ringEquiv e₂ hFchart (fun i => rfl) hshape
  have h₁ := TotalTransformData.of_ringEquiv e₁ rfl (fun i => rfl) h₂
  have h₀ := TotalTransformData.of_comap_isOpenImmersion ρ₂ (Z₀.comap (blowUpπ Z₀))
    (fun i => ((D i).comap V₀.1.ι).comap (blowUpπ Z₀)) b₂ (comap_restrictHom _ _)
    (fun i => comap_π_comap_restrictHom _ _ _) h₁
  refine ⟨TotalTransformData.of_comap_isOpenImmersion ρ₁ (Z.comap (blowUpπ Z))
    (fun i => (D i).comap (blowUpπ Z)) _ (comap_restrictHom _ _)
    (fun i => comap_π_comap_restrictHom _ _ _) h₀, fun i hTF => ?_⟩
  -- a component whose total transform lies in the exceptional ideal contains the centre near `x`
  have hTF₁ := (stalkIdeal_le_iff_of_isOpenImmersion ρ₁ _ _ _).mpr hTF
  have hTF₁' : (((D i).comap V₀.1.ι).comap (blowUpπ Z₀)).stalkIdeal (ρ₂ b₂) ≤
      (Z₀.comap (blowUpπ Z₀)).stalkIdeal (ρ₂ b₂) :=
    (congrArg (fun K : (blowUp Z₀).IdealSheafData => K.stalkIdeal (ρ₂ b₂))
      (comap_π_comap_restrictHom Z V₀.1 (D i))).symm.le.trans
      (hTF₁.trans (congrArg (fun K : (blowUp Z₀).IdealSheafData => K.stalkIdeal (ρ₂ b₂))
        (comap_restrictHom Z V₀.1)).le)
  have hTF₂ := (stalkIdeal_le_iff_of_isOpenImmersion ρ₂ _ _ _).mpr hTF₁'
  have hTF₂' : Tb i ≤ FU.stalkIdeal b₂ :=
    (congrArg (fun K : (blowUp (Z₀.comap E.U.1.ι)).IdealSheafData => K.stalkIdeal b₂)
      (comap_π_comap_restrictHom Z₀ E.U.1 ((D i).comap V₀.1.ι))).symm.le.trans
      (hTF₂.trans (congrArg (fun K : (blowUp (Z₀.comap E.U.1.ι)).IdealSheafData =>
        K.stalkIdeal b₂) (comap_restrictHom Z₀ E.U.1)).le)
  have hTF₃ : T' i ≤ span {alg' (alg (E.v j))} :=
    (Ideal.map_mono (Ideal.map_mono hTF₂')).trans hFchart.le
  -- the component passes through `x₀`
  have hy₀ : y₀ ∈ ((D i).comap V₀.1.ι).support := by
    by_contra hno
    have htopT := hT' i hno
    have hFtop : (span {alg' (alg (E.v j))} : Ideal (Localization.AtPrime p.asIdeal)) = ⊤ :=
      top_le_iff.mp (htopT.symm.le.trans hTF₃)
    have hunit := Ideal.span_singleton_eq_top.mp hFtop
    have hmem : alg (E.v j) ∈ p.asIdeal := by
      have h := hjq
      rwa [chartCoord_self] at h
    have hmem' := (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal _).mpr hmem
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem') hunit
  have hcr := hlt i hy₀ hTF₃
  -- on the chart, `(x_c) ⊆ J = Z(U)`; hence at the stalk of `π₀ b₁ ∈ U`, and back on `X`
  have hUle : ((D i).comap V₀.1.ι).ideal E.U ≤ Z₀.ideal E.U := by
    rw [hideal ⟨i, hy₀⟩, ideal_eq_centerIdeal E, Ideal.span_le, Set.singleton_subset_iff]
    exact E.v_mem_centerIdeal hcr
  have hstalk : ((D i).comap V₀.1.ι).stalkIdeal (blowUpπ Z₀ (ρ₂ b₂)) ≤
      Z₀.stalkIdeal (blowUpπ Z₀ (ρ₂ b₂)) :=
    (Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ E.U hπb₁U).le.trans
      ((Ideal.map_mono hUle).trans
        (Scheme.IdealSheafData.stalkIdeal_eq_map_germ Z₀ E.U hπb₁U).symm.le)
  have := (stalkIdeal_le_iff_of_isOpenImmersion V₀.1.ι (D i) Z _).mp hstalk
  rwa [hπb₁] at this

include f in
/-- The chart computation of the proofs of [Hau14, Proposition 5.3] and [Hau14, Proposition 5.4]
([Hau03, Appendix C]) at a possibly non-closed point: at a point `x'` of the exceptional divisor of
the blow-up of `X` along a centre `Z` with simple normal crossings with the family `D`
([Kol07, Definition 24 (4)], given as data at every point of `Z`), the stalks of the exceptional
divisor and of the total transforms of the components have Hauser's chart shape
`TotalTransformData`; moreover a component whose total transform lies in the exceptional ideal at
`x'` contains `Z` near `π(x')`. The corollary of the pointwise
`exists_totalTransformData_of_mem_support_of_specializes`. -/
theorem exists_totalTransformData_of_mem_support {ι : Type*} [Finite ι]
    (D : ι → X.IdealSheafData) (Z : X.IdealSheafData)
    (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ c : {i : ι // x ∈ (D i).support} → Fin n, Function.Injective c ∧
        ∀ i, (D i.1).stalkIdeal x = span {z (c i)}) ∧
      ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s))
    (x' : blowUp Z) (hx' : x' ∈ (Z.comap (blowUpπ Z)).support) :
    TotalTransformData ((Z.comap (blowUpπ Z)).stalkIdeal x')
      (fun i => ((D i).comap (blowUpπ Z)).stalkIdeal x') ∧
    ∀ i, ((D i).comap (blowUpπ Z)).stalkIdeal x' ≤ (Z.comap (blowUpπ Z)).stalkIdeal x' →
      (D i).stalkIdeal (blowUpπ Z x') ≤ Z.stalkIdeal (blowUpπ Z x') :=
  exists_totalTransformData_of_mem_support_of_specializes f D Z x' hx' fun x hx _ => hZ x hx

end Main

end AlgebraicGeometry
