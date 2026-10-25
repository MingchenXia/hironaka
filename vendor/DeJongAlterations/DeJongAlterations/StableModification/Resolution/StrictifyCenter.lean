import DeJongAlterations.StableModification.Resolution.StrictifyDefs
import DeJongAlterations.StableModification.Resolution.StrictifyDerivation
import DeJongAlterations.Geometry.NodeCompletedLocalFiberFieldSection
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Topology.JacobsonSpace
import DeJongAlterations.Geometry.RegularSmooth
import DeJongAlterations.Algebra.CompletionRegularityAscent

/-!
# The deepest stratum of a normal crossings family

Let `X` be smooth over an algebraically closed field `k` and `(F_l)` a normal crossings family
(`IsNCFamily`) whose member `F_{l₀}` has multiplicity at most `m ≥ 1` at every closed point. The
*`m`-fold locus* of `F_{l₀}` is the closure `C` of the set of closed points where `F_{l₀}` has `m`
branches (`mFoldLocus`). This file shows (`mFoldLocus_spec`) that at a closed point `x` with a
chart `(t, A)`:

* if `|A_{l₀}| = m` then `x ∈ C` and `I(C)_x Ô_{X,x} = (t_i : i ∈ A_{l₀})`: near `x`, `C` is the
  regular stratum where all branches of `F_{l₀}` through `x` meet;
* if `|A_{l₀}| < m` then `x ∉ C`.

This is the centre of the first blowup in de Jong's strictification (de Jong 1996, 2.4,
`references/dejong96-alterations/tex/page-0006.tex`: "first blow up the points where `D` has three
branches").

The proof cuts out `C` on an affine open `U = Spec A` by derivatives: with
`Δ(J) = J + (D f : f ∈ J, D ∈ Der_k(A))`, `C ∩ U = V(Δ^{m-1}(I(F_{l₀})(U)))`. At a closed point
`x ∈ U` the derivations of `A` extend to `Ô_{X,x}` and separate the parameters
(`hasDualDerivations_completion`), so that `Δ^{m-1}(I(F_{l₀})(U)) Ô_{X,x}` is the ideal generated
by the products of `|A_{l₀}| - m + 1` of the `t_i`, `i ∈ A_{l₀}` (`deltaIdeal_iterate_span_prod`);
it is the unit ideal if `|A_{l₀}| < m` and `(t_i : i ∈ A_{l₀})` if `|A_{l₀}| = m`. Since `X` is a
Jacobson space, these closed-point computations determine `C ∩ U`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Algebra.NodeFittingIdealSheaf

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The `k`-algebra structure on the sections over an open subset. -/
def sectionStructure (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem germ_comp_sectionStructure (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (sectionStructure p U) = (Scheme.baseToStalk p x).hom := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U le_top ≫
      X.presheaf.germ U x hx = Scheme.baseToStalk p x := by
    rw [Scheme.baseToStalk, Scheme.Modules.baseRingHom, Scheme.Hom.appLE, Category.assoc,
      Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  rw [← h]
  rfl

/-- On an affine open subset, the sections of a smooth `k`-scheme are formally smooth. -/
theorem formallySmooth_sectionStructure [Smooth p] (U : X.affineOpens) :
    (sectionStructure p U.1).FormallySmooth := by
  apply RingHom.FormallySmooth.comp
  · exact RingHom.FormallySmooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv)
  · exact (Smooth.smooth_appLE p (isAffineOpen_top _) U.2 le_top).formallySmooth

/-- **Nullstellensatz at a closed point** (as in `Resolution.LocalSmoothPoint`): over an
algebraically closed field, `k → κ(x)` is surjective at a closed point. -/
theorem residue_comp_baseToStalk_surjective' [IsAlgClosed k] [LocallyOfFiniteType p] (z : X)
    (hz : IsClosed ({z} : Set X)) :
    Function.Surjective ((X.residue z).hom.comp (Scheme.baseToStalk p z).hom) := by
  let q := X.fromSpecResidueField z
  let e := residueFieldIsoBase p z hz
  have h : q ≫ p = Spec.map e.inv := (SpecMap_residueFieldIsoBase_inv p z hz).symm
  have key := Geometry.NodeCompletedLocalMap.baseToStalk_stalkClosedPointTo
    q p e.inv h
  have hw : q (closedPoint (X.residueField z)) = z := Scheme.fromSpecResidueField_apply z _
  suffices H : Function.Surjective ((X.residue (q (closedPoint (X.residueField z)))).hom.comp
      (Scheme.baseToStalk p (q (closedPoint (X.residueField z)))).hom) by
    rw [hw] at H
    exact H
  intro c
  have : IsLocalHom (Scheme.stalkClosedPointTo q).hom := Scheme.isLocalHom_stalkClosedPointTo q
  let d := X.descResidueField (Scheme.stalkClosedPointTo q)
  have hd : X.residue _ ≫ d = Scheme.stalkClosedPointTo q :=
    X.residue_descResidueField (Scheme.stalkClosedPointTo q)
  have hsurj : Function.Surjective e.inv.hom :=
    (ConcreteCategory.bijective_of_isIso e.inv).2
  obtain ⟨k', hk⟩ := hsurj (d.hom c)
  refine ⟨k', d.hom.injective ?_⟩
  rw [← hk, ← key, ← hd]
  rfl

/-- The derivative operator `Δ(J) = J + (D f : f ∈ J, D ∈ Der_k(Γ(X, U)))` on ideals of sections. -/
def sectionDelta (U : X.Opens) : Ideal Γ(X, U) → Ideal Γ(X, U) :=
  letI := (sectionStructure p U).toAlgebra
  deltaIdeal (Set.univ : Set (Derivation k Γ(X, U) Γ(X, U)))

variable [IsLocallyNoetherian X]

/-- **The derivative ideals at a closed point.** If `I(F)_x Ô_{X,x} = (∏_{i ∈ A} t_i)` for part `t`
of a regular system of parameters, then `Δ^j(I(F)(U)) Ô_{X,x}` is generated by the products of
`|A| - j` of the `t_i`, `i ∈ A`. -/
theorem map_sectionDelta_iterate [IsAlgClosed k] [LocallyOfFiniteType p] [Smooth p]
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : IsClosed ({x} : Set X)) (F : Closeds X)
    {n : ℕ} (t : Fin n → maximalIdeal (X.completedLocalRing x))
    (hli : LinearIndependent (ResidueField (X.completedLocalRing x))
      fun i ↦ (maximalIdeal (X.completedLocalRing x)).toCotangent (t i))
    (A : Finset (Fin n)) (hF : formalIdeal F x = Ideal.span {∏ i ∈ A, (t i : X.completedLocalRing x)})
    (j : ℕ) :
    ((sectionDelta p U.1)^[j] ((Scheme.IdealSheafData.vanishingIdeal F).ideal U)).map
      ((X.toCompletedLocalRing x).comp (X.presheaf.germ U.1 x hxU).hom) =
      layerIdeal (fun i ↦ (t i : X.completedLocalRing x)) A (A.card - j) := by
  classical
  let iA : Algebra k Γ(X, U.1) := (sectionStructure p U.1).toAlgebra
  let iAO : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let iO : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ U.1 x hxU).hom.comp (sectionStructure p U.1)).toAlgebra
  have : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.FormallySmooth k Γ(X, U.1) := (formallySmooth_sectionStructure p U).toAlgebra
  have hres : Function.Bijective (algebraMap k (ResidueField (X.presheaf.stalk x))) := by
    refine ⟨(algebraMap k _).injective, ?_⟩
    have h := residue_comp_baseToStalk_surjective' p x hx
    rw [← germ_comp_sectionStructure p U.1 x hxU] at h
    exact h
  let M := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let ext : Derivation k Γ(X, U.1) Γ(X, U.1) → Derivation k (X.completedLocalRing x)
      (X.completedLocalRing x) := fun D ↦ completeDerivation (localizeDerivation M D)
  let ι := (X.toCompletedLocalRing x).comp (X.presheaf.germ U.1 x hxU).hom
  have hext : ∀ D a, ext D (ι a) = ι (D a) := by
    intro D a
    change completeDerivation (localizeDerivation M D)
      (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)
        (algebraMap Γ(X, U.1) (X.presheaf.stalk x) a)) =
      algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)
        (algebraMap Γ(X, U.1) (X.presheaf.stalk x) (D a))
    rw [completeDerivation_algebraMap, localizeDerivation_algebraMap]
  change ((deltaIdeal (Set.univ : Set (Derivation k Γ(X, U.1) Γ(X, U.1))))^[j] _).map ι = _
  rw [deltaIdeal_iterate_map ι Set.univ ext hext]
  have hJ : ((Scheme.IdealSheafData.vanishingIdeal F).ideal U).map ι =
      Ideal.span {∏ i ∈ A, (t i : X.completedLocalRing x)} := by
    rw [← hF, formalIdeal, localIdeal, stalkIdeal_eq_map_germ _ U hxU, Ideal.map_map]
  rw [hJ, Set.image_univ]
  have hdual := hasDualDerivations_completion (k := k) M hres t hli
  have hdual' : HasDualDerivations (Set.range ext) (fun i ↦ (t i : X.completedLocalRing x)) A := by
    intro i _
    obtain ⟨E, hE, hEv⟩ := hdual i (Finset.mem_univ i)
    exact ⟨E, hE, fun l _ ↦ hEv l (Finset.mem_univ l)⟩
  exact deltaIdeal_iterate_span_prod _ _ A hdual' j

/-- A layer ideal of positive rank is proper. -/
theorem layerIdeal_le_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (t : Fin n → maximalIdeal R) (A : Finset (Fin n)) {r : ℕ} (hr : 1 ≤ r) :
    layerIdeal (fun i ↦ (t i : R)) A r ≤ maximalIdeal R := by
  rw [layerIdeal, Ideal.span_le]
  rintro _ ⟨V, ⟨-, hc⟩, rfl⟩
  obtain ⟨i, hi⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  dsimp only
  rw [← Finset.mul_prod_erase V _ hi]
  exact Ideal.mul_mem_right _ _ (t i).property

/-- A closed point lies on `V(Δ^{m-1}(I(F)(U)))` iff `F` has at least `m` branches there. -/
theorem mem_zeroLocus_sectionDelta_iff [IsAlgClosed k] [LocallyOfFiniteType p] [Smooth p]
    (U : X.affineOpens) (y : X) (hyU : y ∈ U.1) (hy : IsClosed ({y} : Set X)) (F : Closeds X)
    {n : ℕ} (t : Fin n → maximalIdeal (X.completedLocalRing y))
    (hli : LinearIndependent (ResidueField (X.completedLocalRing y))
      fun i ↦ (maximalIdeal (X.completedLocalRing y)).toCotangent (t i))
    (A : Finset (Fin n)) (hF : formalIdeal F y = Ideal.span {∏ i ∈ A, (t i : X.completedLocalRing y)})
    {m : ℕ} (hm : 1 ≤ m) :
    y ∈ X.zeroLocus (U := U.1)
      (((sectionDelta p U.1)^[m - 1] ((Scheme.IdealSheafData.vanishingIdeal F).ideal U)) :
        Set Γ(X, U.1)) ↔ m ≤ A.card := by
  set J := (sectionDelta p U.1)^[m - 1] ((Scheme.IdealSheafData.vanishingIdeal F).ideal U)
  have hmap := map_sectionDelta_iterate p U y hyU hy F t hli A hF (m - 1)
  have h1 : y ∈ X.zeroLocus (U := U.1) (J : Set Γ(X, U.1)) ↔
      J.map (X.presheaf.germ U.1 y hyU).hom ≤ maximalIdeal (X.presheaf.stalk y) := by
    rw [Scheme.mem_zeroLocus_iff, Ideal.map_le_iff_le_comap]
    refine forall₂_congr fun f _ ↦ ?_
    rw [Scheme.mem_basicOpen X f y hyU, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have h2 : J.map (X.presheaf.germ U.1 y hyU).hom ≤ maximalIdeal (X.presheaf.stalk y) ↔
      (J.map (X.presheaf.germ U.1 y hyU).hom).map (X.toCompletedLocalRing y) ≠ ⊤ := by
    constructor
    · intro h htop
      have hle : (J.map (X.presheaf.germ U.1 y hyU).hom).map (X.toCompletedLocalRing y) ≤
          maximalIdeal (X.completedLocalRing y) := by
        rw [Ideal.map_le_iff_le_comap]
        exact h.trans (fun a ha ↦ map_nonunit (algebraMap (X.presheaf.stalk y) (X.completedLocalRing y)) a ha)
      exact (maximalIdeal.isMaximal _).ne_top (top_unique (htop ▸ hle))
    · intro h
      by_contra hn
      apply h
      have : J.map (X.presheaf.germ U.1 y hyU).hom = ⊤ := by
        by_contra hne
        exact hn (le_maximalIdeal hne)
      rw [this, Ideal.map_top]
  rw [h1, h2, Ideal.map_map]
  change Ideal.map ((X.toCompletedLocalRing y).comp (X.presheaf.germ U.1 y hyU).hom) J ≠ ⊤ ↔ _
  rw [hmap]
  constructor
  · intro h
    by_contra hlt
    apply h
    rw [show A.card - (m - 1) = 0 by omega, layerIdeal_zero]
  · intro h htop
    have hle := layerIdeal_le_maximalIdeal t A (r := A.card - (m - 1)) (by omega)
    exact (maximalIdeal.isMaximal _).ne_top (top_unique (htop ▸ hle))

/-- The `m`-fold locus of the member `F l₀` of a family: the closure of the closed points at
which some chart gives `F l₀` exactly `m` branches. -/
def mFoldLocus {ι : Type*} (F : ι → Closeds X) (l₀ : ι) (m : ℕ) : Closeds X :=
  ⟨closure {x | IsClosed ({x} : Set X) ∧ ∃ c : NCChart F x, (c.A l₀).card = m},
    isClosed_closure⟩

/-- The `m`-fold locus of `F l₀` lies in `F l₀` for `m ≥ 1`. -/
theorem mFoldLocus_le {ι : Type*} (F : ι → Closeds X) (l₀ : ι) {m : ℕ} (hm : 1 ≤ m) :
    mFoldLocus F l₀ m ≤ F l₀ := by
  change closure _ ⊆ (F l₀ : Set X)
  apply closure_minimal _ (F l₀).isClosed
  rintro x ⟨-, c, hc⟩
  apply (formalIdeal_ne_top_iff (F l₀) x).mp
  rw [c.formalIdeal_eq l₀]
  intro htop
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (c.A l₀).card by omega)
  have hmem : ∏ i ∈ c.A l₀, (c.t i : X.completedLocalRing x) ∈
      maximalIdeal (X.completedLocalRing x) := by
    rw [← Finset.mul_prod_erase _ _ hi]
    exact Ideal.mul_mem_right _ _ (c.t i).2
  exact (maximalIdeal.isMaximal _).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (Ideal.span_singleton_eq_top.mp htop))

/-- **The deepest stratum.** For a normal crossings family `F` with multiplicities at most `b`,
the `b l₀`-fold locus `C` of `F l₀` satisfies, at every closed point `x` with a chart `(t, A)`:
if `|A l₀| = b l₀ ≥ 1` then `x ∈ C` and `I(C)_x Ô_{X,x} = (t_i : i ∈ A l₀)`; if
`|A l₀| < b l₀` then `x ∉ C`. -/
theorem mFoldLocus_spec [IsAlgClosed k] [LocallyOfFiniteType p] [Smooth p] {ι : Type*}
    (F : ι → Closeds X) (b : ι → ℕ) (hF : IsNCFamily F b) (l₀ : ι) (hb : 1 ≤ b l₀)
    (x : X) (hx : IsClosed ({x} : Set X)) (c : NCChart F x) :
    ((c.A l₀).card = b l₀ → x ∈ mFoldLocus F l₀ (b l₀) ∧
      formalIdeal (mFoldLocus F l₀ (b l₀)) x =
        Ideal.span ((fun i ↦ (c.t i : X.completedLocalRing x)) '' (c.A l₀ : Set (Fin c.n)))) ∧
    ((c.A l₀).card < b l₀ → x ∉ mFoldLocus F l₀ (b l₀)) := by
  classical
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  set m := b l₀
  set C := mFoldLocus F l₀ m
  set W := {x : X | IsClosed ({x} : Set X) ∧ ∃ c : NCChart F x, (c.A l₀).card = m}
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  set J := (sectionDelta p U.1)^[m - 1] ((Scheme.IdealSheafData.vanishingIdeal (F l₀)).ideal U)
  set Z := X.zeroLocus (U := U.1) (J : Set Γ(X, U.1))
  have hKP : ∀ y (hyU : y ∈ U.1) (hy : IsClosed ({y} : Set X)) (c' : NCChart F y),
      y ∈ Z ↔ m ≤ (c'.A l₀).card := fun y hyU hy c' ↦
    mem_zeroLocus_sectionDelta_iff p U y hyU hy (F l₀) c'.t c'.indep (c'.A l₀)
      (c'.formalIdeal_eq l₀) hb
  -- `C ⊆ Z`
  have hCZ : (C : Set X) ⊆ Z := by
    apply closure_minimal _ (Scheme.zeroLocus_isClosed X _)
    rintro w ⟨hw, c', hc'⟩
    by_cases hwU : w ∈ U.1
    · exact (hKP w hwU hw c').mpr hc'.ge
    · have := Scheme.codisjoint_zeroLocus (X := X) (U := U.1) (J : Set Γ(X, U.1))
      rw [codisjoint_iff_le_sup] at this
      rcases this (Set.mem_univ w) with h | h
      · exact h
      · exact absurd h hwU
  -- `Z ∩ U ⊆ C`
  have hZC : Z ∩ U.1 ⊆ C := by
    have hlc : IsLocallyClosed (Z ∩ U.1) :=
      (Scheme.zeroLocus_isClosed X _).isLocallyClosed.inter U.1.isOpen.isLocallyClosed
    have h1 : Z ∩ U.1 ⊆ closure (Z ∩ U.1 ∩ closedPoints X) := by
      rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hlc]
      exact subset_closure
    refine h1.trans (closure_minimal ?_ isClosed_closure)
    rintro y ⟨⟨hyZ, hyU⟩, hy⟩
    obtain ⟨c', hc'⟩ := hF y hy
    exact subset_closure ⟨hy, c', le_antisymm (hc' l₀) ((hKP y hyU hy c').mp hyZ)⟩
  refine ⟨fun hA ↦ ⟨subset_closure ⟨hx, c, hA⟩, ?_⟩, fun hA hxC ↦ ?_⟩
  · -- the ideal of `C` at `x`
    have hpre : U.2.fromSpec ⁻¹' (C : Set X) = PrimeSpectrum.zeroLocus (J : Set Γ(X, U.1)) := by
      rw [← U.2.fromSpec_preimage_zeroLocus]
      ext z
      simp only [Set.mem_preimage]
      have hzU : U.2.fromSpec z ∈ U.1 := by
        have h : U.2.fromSpec z ∈ Set.range U.2.fromSpec := Set.mem_range_self z
        rwa [U.2.range_fromSpec] at h
      exact ⟨fun h ↦ hCZ h, fun h ↦ hZC ⟨h, hzU⟩⟩
    have hloc : localIdeal C x = (J.radical).map (X.presheaf.germ U.1 x hxU).hom := by
      rw [localIdeal, stalkIdeal_eq_map_germ _ U hxU, Scheme.IdealSheafData.vanishingIdeal_ideal,
        hpre, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    have hmap := map_sectionDelta_iterate p U x hxU hx (F l₀) c.t c.indep (c.A l₀)
      (c.formalIdeal_eq l₀) (m - 1)
    rw [show (c.A l₀).card - (m - 1) = 1 by omega, layerIdeal_one] at hmap
    have : IsRegularLocalRing (X.presheaf.stalk x) :=
      Geometry.RegularSmooth.isRegularScheme_of_smooth p x
    have : IsRegularLocalRing (X.completedLocalRing x) :=
      Algebra.CompletionRegularityAscent.isRegularLocalRing_completion _
    have hprime : (Ideal.span ((fun i ↦ (c.t i : X.completedLocalRing x)) ''
        (c.A l₀ : Set (Fin c.n)))).IsPrime :=
      Algebra.CompletionIntersectionRegularityHeight.parameterIdeal_isPrime c.t c.indep (c.A l₀)
    rw [formalIdeal, hloc, Ideal.map_map, map_radical_eq_of_isRadical _ _ ?_, hmap]
    rw [hmap]
    exact hprime.isRadical
  · have := (hKP x hxU hx c).mp (hCZ hxC)
    omega

end DeJongAlterations.StableModification.Resolution.Strictify
