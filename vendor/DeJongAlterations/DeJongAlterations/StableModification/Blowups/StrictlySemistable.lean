import DeJongAlterations.StableModification.Curves.StandardModels

/-!
# Locality of strict semi-stability

Strict semi-stability (`Curves.IsStrictlySemistable`, M. Temkin, *Stable modification of
relative curves*, §4.3, T:2949–2953) is defined by local étale charts to the two standard
models. This file proves the formal properties used when blow-ups of the standard models are
spread over a curve (Temkin, proof of Prop 4.3.1, T:2976–2983, "`C' := C̄' ×_C̄ C` is a
strictly semi-stable blow up of `C`"):

* `IsStrictlySemistable.etale_comp`: strict semi-stability pulls back along étale maps
  `φ : C' ⟶ C` (with the pulled-back marks);
* `IsStrictlySemistable.of_openCover`: it is local on the source;
* `IsStrictlySemistable.of_iso`: in particular it is invariant under isomorphisms;
* `isStrictlySemistable_nodeModel`, `isStrictlySemistable_smoothModel`: the standard models
  without marks are strictly semi-stable (for the smooth model `Spec A[T]` without marks one
  uses the charts `D(T - c)`, `c ∈ {0, 1}`, with the coordinate `T - c`).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Curves

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C C' S : Scheme.{u}}

/-- An ideal sheaf pulls back to the unit ideal sheaf along a morphism whose image avoids its
support. -/
theorem comap_eq_top_of_forall_notMem_support {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) (h : ∀ x : X, f x ∉ (I.support : Set Y)) : I.comap f = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext x
  simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact h x

/-- **Strict semi-stability pulls back along étale maps.** If `(C, D)` is strictly
semi-stable over `S` and `φ : C' ⟶ C` is étale, then `(C', φ⁻¹D)` is strictly semi-stable
over `S`. -/
theorem IsStrictlySemistable.etale_comp {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) (φ : C' ⟶ C) [Etale φ] :
    IsStrictlySemistable (φ ≫ g) (D.comap φ) := by
  intro x
  obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hs (φ x)
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  have hφU : Etale (φ ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Etale) inferInstance U
  refine ⟨φ ⁻¹ᵁ U, hxU, A, inferInstance, ι, inferInstance, (φ ∣_ U) ≫ h, ?_, ?_⟩
  · rw [Category.assoc, hh, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  · have hmarks : (D.comap φ).comap (φ ⁻¹ᵁ U).ι = (D.comap U.ι).comap (φ ∣_ U) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        morphismRestrict_ι]
    rcases hcase with ⟨e, he, rfl, hD⟩ | ⟨a, e, he, rfl, hD⟩
    · refine Or.inl ⟨(φ ∣_ U) ≫ e, inferInstance, Category.assoc _ _ _, ?_⟩
      rw [hmarks, hD, Scheme.IdealSheafData.comap_comp]
    · refine Or.inr ⟨a, (φ ∣_ U) ≫ e, inferInstance, Category.assoc _ _ _, ?_⟩
      rw [hmarks, hD, Scheme.IdealSheafData.comap_top]

/-- **Strict semi-stability is local on the source.** -/
theorem IsStrictlySemistable.of_openCover {g : C ⟶ S} {D : C.IdealSheafData}
    (h : ∀ x : C, ∃ U : C.Opens, x ∈ U ∧ IsStrictlySemistable (U.ι ≫ g) (D.comap U.ι)) :
    IsStrictlySemistable g D := by
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨U', hxU', A, _, ι, _, h', hh', hcase⟩ := hU ⟨x, hxU⟩
  let e := U.ι.isoImage U'
  have he : e.inv ≫ U'.ι ≫ U.ι = (U.ι ''ᵁ U').ι := Scheme.Hom.isoImage_inv_ι _ _
  have hx : x ∈ U.ι ''ᵁ U' := ⟨⟨x, hxU⟩, hxU', rfl⟩
  have hmarks : D.comap (U.ι ''ᵁ U').ι = ((D.comap U.ι).comap U'.ι).comap e.inv := by
    rw [← he, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  refine ⟨U.ι ''ᵁ U', hx, A, inferInstance, ι, inferInstance, e.inv ≫ h', ?_, ?_⟩
  · rw [Category.assoc, hh', ← he, Category.assoc, Category.assoc]
  · rcases hcase with ⟨f, hf, rfl, hD⟩ | ⟨a, f, hf, rfl, hD⟩
    · refine Or.inl ⟨e.inv ≫ f, inferInstance, Category.assoc _ _ _, ?_⟩
      rw [hmarks, hD, Scheme.IdealSheafData.comap_comp]
    · refine Or.inr ⟨a, e.inv ≫ f, inferInstance, Category.assoc _ _ _, ?_⟩
      rw [hmarks, hD, Scheme.IdealSheafData.comap_top]

/-- Strict semi-stability is invariant under isomorphisms of the source. -/
theorem IsStrictlySemistable.of_iso {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) (φ : C' ≅ C) :
    IsStrictlySemistable (φ.hom ≫ g) (D.comap φ.hom) :=
  hs.etale_comp φ.hom

/-- **The nodal standard model is strictly semi-stable** (without marks). -/
theorem isStrictlySemistable_nodeModel {A : Type u} [CommRing A] (a : A) :
    IsStrictlySemistable (nodeModel a) ⊤ := by
  intro x
  have : IsIso (⊤ : (Spec (.of (Algebra.NodeBlowupChart.Node A a))).Opens).ι :=
    inferInstanceAs (IsIso (Scheme.topIso _).hom)
  refine ⟨⊤, trivial, A, inferInstance, 𝟙 _, inferInstance,
    (⊤ : (Spec (.of (Algebra.NodeBlowupChart.Node A a))).Opens).ι ≫ nodeModel a,
    Category.comp_id _, Or.inr ⟨a, (⊤ : (Spec (.of (Algebra.NodeBlowupChart.Node A a))).Opens).ι,
      inferInstance, rfl, Scheme.IdealSheafData.comap_top _⟩⟩

/-- The marks `{T = 0}` of the smooth model lie in the vanishing locus of `T`. -/
theorem X_mem_of_mem_support_smoothModelMarks (A : Type u) [CommRing A]
    {p : Spec (.of A[X])} (hp : p ∈ ((smoothModelMarks A).support : Set (Spec (.of A[X])))) :
    (X : A[X]) ∈ p.asIdeal := by
  have hcl : IsClosed (PrimeSpectrum.zeroLocus ({X} : Set A[X])) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hsub : Set.range (smoothModelZeroSection A) ⊆
      PrimeSpectrum.zeroLocus ({X} : Set A[X]) := by
    rintro _ ⟨q, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    change X ∈ Ideal.comap (Polynomial.evalRingHom (0 : A)) q.asIdeal
    rw [Ideal.mem_comap]
    simp
  have hsupp : ((smoothModelMarks A).support : Set (Spec (.of A[X]))) =
      closure (Set.range (smoothModelZeroSection A)) :=
    Scheme.Hom.support_ker _
  rw [hsupp] at hp
  have := (closure_minimal hsub hcl) hp
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at this
  exact this

/-- **The smooth standard model without marks is strictly semi-stable**: `Spec A[T]` is covered
by the opens `D(T - c)`, `c ∈ {0, 1}`, each étale over the smooth model via the coordinate
`T - c` and disjoint from the pulled-back marks. -/
theorem isStrictlySemistable_smoothModel (A : Type u) [CommRing A] :
    IsStrictlySemistable (smoothModel A) ⊤ := by
  intro x
  -- choose `c ∈ {0, 1}` with `T - c ∉ x`
  obtain ⟨c, hc⟩ : ∃ c : A, (X - C c : A[X]) ∉ x.asIdeal := by
    by_cases h0 : (X - C 0 : A[X]) ∈ x.asIdeal
    · refine ⟨1, fun h1 => x.isPrime.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one]
      have : (1 : A[X]) = (X - C 0) - (X - C 1) := by simp
      rw [this]
      exact x.asIdeal.sub_mem h0 h1
    · exact ⟨0, h0⟩
  let U : (Spec (.of A[X])).Opens := PrimeSpectrum.basicOpen (X - C c)
  let τ : A[X] ≃ₐ[A] A[X] := Polynomial.taylorEquiv (-c)
  let σ : Spec (.of A[X]) ⟶ Spec (.of A[X]) := Spec.map (CommRingCat.ofHom τ.toRingHom)
  have hσ : IsIso σ := inferInstanceAs (IsIso (Spec.map τ.toRingEquiv.toCommRingCatIso.hom))
  have hσg : σ ≫ smoothModel A = smoothModel A := by
    dsimp only [σ, smoothModel]
    rw [← Spec.map_comp]
    congr 1
    ext a : 2
    exact τ.commutes a
  refine ⟨U, hc, A, inferInstance, 𝟙 _, inferInstance, U.ι ≫ smoothModel A, Category.comp_id _,
    Or.inl ⟨U.ι ≫ σ, inferInstance, by rw [Category.assoc, hσg], ?_⟩⟩
  rw [Scheme.IdealSheafData.comap_top]
  symm
  apply comap_eq_top_of_forall_notMem_support
  intro y hy
  have hX := X_mem_of_mem_support_smoothModelMarks A hy
  apply y.2
  change (X - C c : A[X]) ∈ y.1.asIdeal
  have hτ : τ X = X - C c := by
    change Polynomial.taylor (-c) X = X - C c
    rw [Polynomial.taylor_X, map_neg, ← sub_eq_add_neg]
  change X ∈ Ideal.comap τ.toRingHom y.1.asIdeal at hX
  rw [Ideal.mem_comap] at hX
  change τ X ∈ y.1.asIdeal at hX
  rwa [hτ] at hX

end DeJongAlterations.StableModification.Curves
