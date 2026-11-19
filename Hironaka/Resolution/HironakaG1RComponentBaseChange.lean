import Hironaka.Resolution.HironakaG1RClosedSubsetDimension
import Hironaka.Resolution.HironakaG1RComponentDimension
import Hironaka.Resolution.HironakaG1RVanishingIdealBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.NoetherianSpace

/-!
# Irreducible components and their dimensions under field extension (ALG14 layers F2 and F1)

Let `k` be a field, `L / k` ANY field extension and
`IsPullback p fL f (Spec.map (k → L))` a cartesian square, i.e. `X_L = X ×_k L` with projection
`p : X_L → X`, where `f : X → Spec k` is locally of finite type.

**Main results.**
* `topologicalKrullDim_closure_map_of_isPullback` (dimension of components): if `η'` is the generic
  point of an irreducible component of `X_L`, then `dim (closure {p η'}) = dim (closure {η'})`;
* `closure_singleton_mem_irreducibleComponents`, `exists_component_over_point`: along a
  generalizing map (e.g. the flat `p`), generic points of irreducible components map to generic
  points of irreducible components, and every point over a component `C` lies on a component lying
  over `C`;
* **F2** `preimage_complementarySet`: `p⁻¹ (complementarySet X d) = complementarySet X_L d` for every
  `d`, where `complementarySet X d` is the union of the irreducible components of dimension `≠ d`
  (the set underlying the dependency's `complementaryClosed X d`); and `range_componentDimension`:
  the set of component dimensions of `X_L` equals that of `X` (`dimensionIndex X_L = dimensionIndex X`);
* **F1** `comap_separationIdeal_of_isPullback` (`k` perfect, `X`, `X_L` noetherian spaces):
  `(separationIdeal X).comap p = separationIdeal X_L`.

`componentDimension`, `complementaryClosed` and `separationIdeal` below have VERBATIM the bodies of the
dependency's `Hironaka.Resolution.Algebraic.ActualIntrinsicComponentDimensions.componentDimension`
(`ActualIntrinsicComponentDimensions.lean:33`) and
`ActualGlobalDimensionSeparationIdeal.complementaryClosed`/`separationIdeal`
(`ActualGlobalDimensionSeparationIdeal.lean:26,40`); the bridge to those names is definitional
(not built here: the Hironaka.Algebra project is not built in this container).

Proof of the dimension statement: choose an affine open `U ∋ p η'` of `X`; the square restricts to
`p⁻¹ U → U` over `Spec L → Spec k`, whose rings of sections form a pushout `Γ(p⁻¹ U) = Γ(U) ⊗[k] L`
(`isPushout_appTop_of_isPullback`).  Dimensions of point closures are local
(`HironakaG1RClosedSubsetDimension.topologicalKrullDim_closure_of_isOpenImmersion`) and computed on
affine charts (`topologicalKrullDim_closure_eq`); the prime of `η'` is minimal (η' is a maximal
point) and contracts to the prime of `p η'`, so `HironakaG1RComponentDimension.
ringKrullDim_quotient_of_mem_minimalPrimes` (transported along the pushout,
`ringKrullDim_quotient_of_isPushout`) gives the equality.

Only Mathlib and lane G1's modules are imported; no named input.
Blueprint: `hironaka-g1-r-integral-scheme-dimension.tex` (nodes `g1r:components-generalizing`,
`g1r:component-dimension-scheme`, `g1r:separation-ideal-base-change`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace Hironaka.HironakaG1RComponentBaseChange

open AlgebraicGeometry HironakaG1RClosedSubsetDimension HironakaG1RComponentDimension
open HironakaG1RVanishingIdealBaseChange

universe u

/-! ### Ring level: pushouts -/

section Ring

/-- `HironakaG1RComponentDimension.ringKrullDim_quotient_of_mem_minimalPrimes` for an arbitrary
pushout `B = A ⊗[k] L`. -/
theorem ringKrullDim_quotient_of_isPushout {k L A B : Type*} [Field k] [Field L] [CommRing A]
    [CommRing B] [Algebra k L] [Algebra k A] [Algebra A B] [Algebra L B] [Algebra k B]
    [IsScalarTower k A B] [IsScalarTower k L B] [Algebra.IsPushout k A L B]
    [Algebra.FiniteType k A] {Q : Ideal B} (hQ : Q ∈ minimalPrimes B) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap (algebraMap A B)) := by
  let e : A ⊗[k] L ≃+* B := (Algebra.IsPushout.equiv k A L B).toRingEquiv
  let φ : A ⊗[k] L →+* B := e.toRingHom
  have hQ' : Q.comap φ ∈ minimalPrimes (A ⊗[k] L) := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := φ) e.surjective hQ
    rwa [Ideal.comap_bot_of_injective φ e.injective] at h
  have h2 : (Q.comap φ).comap (algebraMap A (A ⊗[k] L)) = Q.comap (algebraMap A B) := by
    rw [Ideal.comap_comap]
    congr 1
    ext a
    exact (Algebra.IsPushout.equiv k A L B).commutes a
  have h1 : ringKrullDim ((A ⊗[k] L) ⧸ Q.comap φ) = ringKrullDim (B ⧸ Q) :=
    ringKrullDim_quotient_comap_equiv e Q
  rw [← h1, ringKrullDim_quotient_of_mem_minimalPrimes hQ', h2]

end Ring

/-! ### Topology: components along generalizing maps -/

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The generic point of an irreducible component has no proper generalization. -/
theorem eq_of_specializes_of_isGenericPoint [T0Space α] {C : Set α}
    (hC : C ∈ irreducibleComponents α) {η ξ : α} (hη : IsGenericPoint η C) (h : ξ ⤳ η) :
    ξ = η := by
  have h1 : C ⊆ closure {ξ} := by
    rw [← hη.def]
    exact h.closure_subset
  have h2 : closure {ξ} ⊆ C := hC.2 isIrreducible_singleton.closure h1
  have h3 : η ⤳ ξ := hη.specializes (h2 (subset_closure rfl))
  exact (h.antisymm h3).eq

/-- **Generic points of components go to generic points of components** along a generalizing
continuous map. -/
theorem closure_singleton_mem_irreducibleComponents [T0Space α] [QuasiSober β] {p : α → β}
    (hp : GeneralizingMap p) {C' : Set α} (hC' : C' ∈ irreducibleComponents α) {η' : α}
    (hη' : IsGenericPoint η' C') : closure {p η'} ∈ irreducibleComponents β := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hle ↦ ?_⟩
  have hgen := hT.isGenericPoint_genericPoint_closure
  have hsp : hT.genericPoint ⤳ p η' := hgen.specializes (subset_closure (hle (subset_closure rfl)))
  obtain ⟨ξ', hξ', hpξ'⟩ := hp hsp
  have := eq_of_specializes_of_isGenericPoint hC' hη' hξ'
  subst this
  rw [hpξ'] at *
  calc T ⊆ closure T := subset_closure
    _ = closure {hT.genericPoint} := hgen.def.symm

/-- **Every point over a component lies on a component over it**, along a generalizing map. -/
theorem exists_component_over_point [QuasiSober α] [T0Space β] {p : α → β} (hpc : Continuous p)
    (hp : GeneralizingMap p) {C : Set β} (hC : C ∈ irreducibleComponents β) {η : β}
    (hη : IsGenericPoint η C) {y : α} (hy : p y ∈ C) :
    ∃ η' : α, closure {η'} ∈ irreducibleComponents α ∧ y ∈ closure {η'} ∧ p η' = η := by
  obtain ⟨ξ, hξy, hpξ⟩ := hp (hη.specializes hy)
  have hirr : IsIrreducible (irreducibleComponent ξ) := isIrreducible_irreducibleComponent
  have hgen : IsGenericPoint hirr.genericPoint (irreducibleComponent ξ) :=
    hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent
  have hηξ : hirr.genericPoint ⤳ ξ := hgen.specializes mem_irreducibleComponent
  have hmap : p hirr.genericPoint = η :=
    eq_of_specializes_of_isGenericPoint hC hη (hpξ ▸ hηξ.map hpc)
  refine ⟨hirr.genericPoint, ?_, ?_, hmap⟩
  · rw [hgen.def]
    exact irreducibleComponent_mem_irreducibleComponents ξ
  · exact specializes_iff_mem_closure.mp (hηξ.trans hξy)

end Topology

/-! ### The dependency's component data (verbatim bodies) -/

section Defs

variable {X : Scheme.{u}}

/-- The dimension of an irreducible component (verbatim body of the dependency's
`ActualIntrinsicComponentDimensions.componentDimension`). -/
noncomputable def componentDimension (C : irreducibleComponents X) : WithBot ℕ∞ :=
  topologicalKrullDim C.val

/-- The union of the irreducible components of dimension `≠ d` (the set underlying the
dependency's `ActualGlobalDimensionSeparationIdeal.complementaryClosed X d`). -/
def complementarySet (X : Scheme.{u}) (d : WithBot ℕ∞) : Set X :=
  ⋃ C : irreducibleComponents X, ⋃ (_ : componentDimension C ≠ d), C.val

theorem mem_complementarySet (d : WithBot ℕ∞) (x : X) :
    x ∈ complementarySet X d ↔ ∃ C : irreducibleComponents X, componentDimension C ≠ d ∧ x ∈ C.val := by
  simp only [complementarySet, Set.mem_iUnion, exists_prop]

/-- `complementarySet` as a closed set (verbatim body of the dependency's `complementaryClosed`). -/
def complementaryClosed (X : Scheme.{u}) [NoetherianSpace X] (d : WithBot ℕ∞) : Closeds X :=
  ⟨⋃ C : irreducibleComponents X, ⋃ (_ : componentDimension C ≠ d), C.val, by
    have : Finite (irreducibleComponents X) :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact isClosed_iUnion_of_finite fun C ↦ isClosed_iUnion_of_finite fun _ ↦
      isClosed_of_mem_irreducibleComponents _ C.2⟩

/-- The dimension-separation ideal (verbatim body of the dependency's
`ActualGlobalDimensionSeparationIdeal.separationIdeal`). -/
noncomputable def separationIdeal (X : Scheme.{u}) [NoetherianSpace X] : X.IdealSheafData :=
  ⨆ d : WithBot ℕ∞, Scheme.IdealSheafData.vanishingIdeal (complementaryClosed X d)

end Defs

/-! ### Field extensions -/

section BaseChange

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X XL : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {fL : XL ⟶ Spec (.of L)} {p : XL ⟶ X}

theorem flat_of_isPullback (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    Flat p := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact MorphismProperty.of_isPullback h.flip this

theorem surjective_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) : Surjective p := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x⟩ : Nonempty (Spec (.of L)) := inferInstance
    exact ⟨x, Subsingleton.elim _ _⟩
  exact MorphismProperty.of_isPullback h.flip this

/-- **Dimension of components under field extension.**  If `η'` has no proper generalization in
`X_L` (generic point of an irreducible component), then `dim (closure {p η'}) = dim (closure {η'})`. -/
theorem topologicalKrullDim_closure_map_of_isPullback
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] {η' : XL} (hη' : ∀ ξ : XL, ξ ⤳ η' → ξ = η') :
    topologicalKrullDim (closure {p η'} : Set X) = topologicalKrullDim (closure {η'} : Set XL) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : LocallyOfFiniteType fL := MorphismProperty.of_isPullback h ‹_›
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p η')) isOpen_univ
  change X.Opens at U
  have : IsAffine U := hU
  have h₁ : IsPullback (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ fL) (U.ι ≫ f) g :=
    (isPullback_morphismRestrict p U).paste_vert h
  have : IsAffine (p ⁻¹ᵁ U) := .of_isPullback h₁
  let η'₀ : (p ⁻¹ᵁ U).toScheme := ⟨η', hηU⟩
  let η₀ : U.toScheme := (p ∣_ U) η'₀
  have hη₀ : U.ι η₀ = p η' := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have e1 := topologicalKrullDim_closure_of_isOpenImmersion f U.ι η₀
  have e2 := topologicalKrullDim_closure_of_isOpenImmersion fL (p ⁻¹ᵁ U).ι η'₀
  rw [hη₀] at e1
  rw [e1, show η' = (p ⁻¹ᵁ U).ι η'₀ from rfl, e2,
    topologicalKrullDim_closure_eq (U.ι ≫ f) η₀ (isAffineOpen_top _) trivial,
    topologicalKrullDim_closure_eq ((p ⁻¹ᵁ U).ι ≫ fL) η'₀ (isAffineOpen_top _) trivial]
  have hfst : (⊤ : (p ⁻¹ᵁ U).toScheme.Opens) ≤ (p ∣_ U) ⁻¹ᵁ ⊤ := le_top
  rw [← IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top U.toScheme) ⊤
    (isAffineOpen_top _) hfst trivial, HironakaG1RSmoothLocusPullback.appLE_top_top]
  -- the pushout of rings
  set A := Γ(U.toScheme, ⊤)
  set B := Γ((p ⁻¹ᵁ U).toScheme, ⊤)
  let φA : k →+* A := (U.ι ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let φL : L →+* B := ((p ⁻¹ᵁ U).ι ≫ fL).appTop.hom.comp (Scheme.ΓSpecIso (.of L)).inv.hom
  let ψ : A →+* B := (p ∣_ U).appTop.hom
  let _ : Algebra k A := φA.toAlgebra
  let _ : Algebra L B := φL.toAlgebra
  let _ : Algebra A B := ψ.toAlgebra
  let _ : Algebra k B := (ψ.comp φA).toAlgebra
  have hcomm' : (Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop ≫ (p ∣_ U).appTop =
      CommRingCat.ofHom (algebraMap k L) ≫ (Scheme.ΓSpecIso (.of L)).inv ≫
        ((p ⁻¹ᵁ U).ι ≫ fL).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, h₁.w]
  have hcomm : ψ.comp φA = φL.comp (algebraMap k L) := congrArg CommRingCat.Hom.hom hcomm'
  have : IsScalarTower k A B := .of_algebraMap_eq' rfl
  have : IsScalarTower k L B := .of_algebraMap_eq' hcomm
  have : Algebra.IsPushout k A L B := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    refine (isPushout_appTop_of_isPullback h₁).of_iso' (Scheme.ΓSpecIso (.of k)).symm (Iso.refl _)
      (Scheme.ΓSpecIso (.of L)).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k L))).symm
    · rfl
    · rfl
  have : Algebra.FiniteType k A := by
    have hle : (⊤ : U.toScheme.Opens) ≤ (U.ι ≫ f) ⁻¹ᵁ ⊤ := le_top
    have h1 := (U.ι ≫ f).finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top U.toScheme) hle
    rw [HironakaG1RSmoothLocusPullback.appLE_top_top] at h1
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  -- the prime of `η'` is minimal
  have hq0 := IsAffineOpen.fromSpec_primeIdealOf (isAffineOpen_top (p ⁻¹ᵁ U).toScheme)
    ⟨η'₀, trivial⟩
  generalize (isAffineOpen_top (p ⁻¹ᵁ U).toScheme).primeIdealOf ⟨η'₀, trivial⟩ = q at hq0 ⊢
  have hqmin : q.asIdeal ∈ minimalPrimes B := by
    refine ⟨⟨q.isPrime, bot_le⟩, fun Q₀ hQ₀ hle ↦ ?_⟩
    let z : Spec B := ⟨Q₀, hQ₀.1⟩
    let j := (isAffineOpen_top (p ⁻¹ᵁ U).toScheme).fromSpec ≫ (p ⁻¹ᵁ U).ι
    have hz : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).mp hle
    have hq : j q = η' := congrArg (p ⁻¹ᵁ U).ι hq0
    have hjz : j z = η' := hη' _ (hq ▸ hz.map j.continuous)
    have : z = q := j.isOpenEmbedding.injective (hjz.trans hq.symm)
    rw [← this]
  rw [ringKrullDim_quotient_of_isPushout (k := k) (L := L) (A := A) (B := B) hqmin,
    PrimeSpectrum.comap_asIdeal]
  rfl

/-- **F2: the components of dimension `≠ d` pull back to those of `X_L`.** -/
theorem preimage_complementarySet
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] (d : WithBot ℕ∞) :
    p ⁻¹' complementarySet X d = complementarySet XL d := by
  have : Flat p := flat_of_isPullback h
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  ext x'
  rw [Set.mem_preimage, mem_complementarySet, mem_complementarySet]
  constructor
  · rintro ⟨C, hCd, hxC⟩
    have hC := C.2
    have hη := C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
    obtain ⟨η', hη'C, hx'η', hpη'⟩ := exists_component_over_point p.continuous hgen hC hη hxC
    refine ⟨⟨_, hη'C⟩, fun hd ↦ hCd ?_, hx'η'⟩
    have hmax : ∀ ξ : XL, ξ ⤳ η' → ξ = η' := fun ξ hξ ↦
      eq_of_specializes_of_isGenericPoint hη'C isGenericPoint_closure hξ
    have hdim := topologicalKrullDim_closure_map_of_isPullback h hmax
    rw [hpη', hη.def] at hdim
    exact hdim.trans hd
  · rintro ⟨C', hC'd, hxC'⟩
    have hη' := C'.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C'.2)
    have hcomp := closure_singleton_mem_irreducibleComponents hgen C'.2 hη'
    refine ⟨⟨_, hcomp⟩, fun hd ↦ hC'd ?_, ?_⟩
    · have hmax : ∀ ξ : XL, ξ ⤳ C'.2.1.genericPoint → ξ = C'.2.1.genericPoint := fun ξ hξ ↦
        eq_of_specializes_of_isGenericPoint C'.2 hη' hξ
      have hdim := topologicalKrullDim_closure_map_of_isPullback h hmax
      rw [hη'.def] at hdim
      exact hdim.symm.trans hd
    · exact specializes_iff_mem_closure.mp ((hη'.specializes hxC').map p.continuous)

/-- **The set of component dimensions is invariant under field extension**
(`dimensionIndex X_L = dimensionIndex X`). -/
theorem range_componentDimension
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] :
    Set.range (componentDimension (X := XL)) = Set.range (componentDimension (X := X)) := by
  have : Flat p := flat_of_isPullback h
  have : Surjective p := surjective_of_isPullback h
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  ext e
  constructor
  · rintro ⟨C', rfl⟩
    have hη' := C'.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C'.2)
    have hcomp := closure_singleton_mem_irreducibleComponents hgen C'.2 hη'
    have hmax : ∀ ξ : XL, ξ ⤳ C'.2.1.genericPoint → ξ = C'.2.1.genericPoint := fun ξ hξ ↦
      eq_of_specializes_of_isGenericPoint C'.2 hη' hξ
    have hdim := topologicalKrullDim_closure_map_of_isPullback h hmax
    rw [hη'.def] at hdim
    exact ⟨⟨_, hcomp⟩, hdim⟩
  · rintro ⟨C, rfl⟩
    have hη := C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
    obtain ⟨x', hx'⟩ := p.surjective C.2.1.genericPoint
    obtain ⟨η', hη'C, -, hpη'⟩ :=
      exists_component_over_point p.continuous hgen C.2 hη (hx' ▸ hη.mem)
    have hmax : ∀ ξ : XL, ξ ⤳ η' → ξ = η' := fun ξ hξ ↦
      eq_of_specializes_of_isGenericPoint hη'C isGenericPoint_closure hξ
    have hdim := topologicalKrullDim_closure_map_of_isPullback h hmax
    rw [hpη', hη.def] at hdim
    exact ⟨⟨_, hη'C⟩, hdim.symm⟩

/-- **F2, closed form.** -/
theorem preimage_complementaryClosed
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] (d : WithBot ℕ∞) :
    (complementaryClosed X d).preimage p.continuous = complementaryClosed XL d :=
  Closeds.ext (preimage_complementarySet h d)

/-- **F1: the dimension-separation ideal under field extension** (`k` perfect, e.g. of
characteristic zero; `X`, `X_L` noetherian spaces). -/
theorem comap_separationIdeal_of_isPullback [PerfectField k]
    (h : IsPullback p fL f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace XL] :
    (separationIdeal X).comap p = separationIdeal XL := by
  rw [separationIdeal, comap_iSup_vanishingIdeal_of_isPullback h, separationIdeal]
  exact iSup_congr fun d ↦ congrArg _ (preimage_complementaryClosed h d)

end BaseChange

end Hironaka.HironakaG1RComponentBaseChange
