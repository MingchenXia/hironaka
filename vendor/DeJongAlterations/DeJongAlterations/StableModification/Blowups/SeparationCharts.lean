import DeJongAlterations.StableModification.Blowups.SeparationSections
import DeJongAlterations.Geometry.NodeFamilySmooth

/-!
# Charts at points of the closed fibre

For a strictly semi-stable curve `(C, ∅)` over the spectrum of a local ring `A`
(M. Temkin, *Stable modification of relative curves*, §4.3, T:2949–2953), the charts of
`Curves.IsStrictlySemistable` at a point `x` of the closed fibre can be taken over `A` itself
(`exists_chart`); a node chart at a point off the origin `u = v = 0` gives a *smooth chart*, an
étale coordinate to `𝔸¹_A` (`hasSmoothChart_of_node`); and at the origin of a node chart the
parameter is nonzero when `C` has local domains (`node_param_ne_zero`). Blueprint
`sm-boundary-separation.tex`, `lem:sm-separation-charts`.

## Main definitions and results

* `HasSmoothChart g y`: an open immersion `ι : Y ⟶ C` through `y` and an étale
  `e : Y ⟶ Spec A[T]` over `A`; `HasSmoothChart.isSmoothAt`, `HasSmoothChart.restrict`,
  `HasSmoothChart.of_isOpenImmersion`.
* `nodeCoordinateChart`: `D(u)` and `D(v)` in `Spec A[u,v]/(uv - a)` are étale over `𝔸¹_A`
  (they are isomorphic to `Spec A[t, t⁻¹]`).
* `exists_chart`, `node_param_ne_zero`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section SmoothChart

variable {A : Type u} [CommRing A] {C : Scheme.{u}}

/-- A *smooth chart* at `y`: an open immersion `ι : Y ⟶ C` whose image contains `y` together with
an étale `e : Y ⟶ Spec A[T]` such that `ι ≫ g` is `e` followed by the smooth model. -/
def HasSmoothChart (g : C ⟶ Spec (.of A)) (y : C) : Prop :=
  ∃ (Y : Scheme.{u}) (ι : Y ⟶ C) (_ : IsOpenImmersion ι) (e : Y ⟶ Spec (.of A[X])) (_ : Etale e),
    y ∈ Set.range ι ∧ e ≫ smoothModel A = ι ≫ g

/-- An étale chart on an open to the smooth model is a smooth chart. -/
theorem hasSmoothChart_of_etale (g : C ⟶ Spec (.of A)) (U : C.Opens)
    (e : U.toScheme ⟶ Spec (.of A[X])) [Etale e] (he : e ≫ smoothModel A = U.ι ≫ g) (y : C)
    (hy : y ∈ U) : HasSmoothChart g y :=
  ⟨U, U.ι, inferInstance, e, inferInstance, ⟨⟨y, hy⟩, rfl⟩, he⟩

/-- Smooth charts are transported along open immersions over the base. -/
theorem HasSmoothChart.of_isOpenImmersion {C' : Scheme.{u}} {g : C ⟶ Spec (.of A)}
    {g' : C' ⟶ Spec (.of A)} (k : C ⟶ C') [IsOpenImmersion k] (hk : g = k ≫ g') {y : C}
    (h : HasSmoothChart g y) : HasSmoothChart g' (k y) := by
  obtain ⟨Y, ι, _, e, _, ⟨y₀, rfl⟩, he⟩ := h
  exact ⟨Y, ι ≫ k, inferInstance, e, inferInstance, ⟨y₀, rfl⟩, by rw [he, hk, Category.assoc]⟩

/-- Smooth charts restrict to opens. -/
theorem HasSmoothChart.restrict {g : C ⟶ Spec (.of A)} (W : C.Opens) (y : W.toScheme)
    (h : HasSmoothChart g y.1) : HasSmoothChart (W.ι ≫ g) y := by
  obtain ⟨Y, ι, _, e, _, ⟨y₀, hy₀⟩, he⟩ := h
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι) (g := W.ι) y₀ y
    (by rw [hy₀]; rfl)
  refine ⟨pullback ι W.ι, pullback.snd ι W.ι, inferInstance, pullback.fst ι W.ι ≫ e,
    inferInstance, ⟨z, hz2⟩, ?_⟩
  rw [Category.assoc, he, ← Category.assoc, pullback.condition, Category.assoc]

/-- A smooth chart gives smoothness at the point. -/
theorem HasSmoothChart.isSmoothAt {g : C ⟶ Spec (.of A)} {y : C} (h : HasSmoothChart g y) :
    DeJong.IsSmoothAt g y := by
  obtain ⟨Y, ι, _, e, _, ⟨y₀, rfl⟩, he⟩ := h
  have : Smooth (ι ≫ g) := by rw [← he]; infer_instance
  exact isSmoothAt_of_isOpenImmersion_comp ι (isSmoothAt_of_smooth (ι ≫ g) y₀)

end SmoothChart

section NodeCoordinate

variable {A : Type u} [CommRing A]

open Algebra.NodeFamilyLocalization Geometry.NodeFamilySmooth

/-- The localization of the node at a coordinate is the Laurent polynomial ring. -/
def nodeCoordinateEquiv (a : A) : (i : Fin 2) →
    Localization.Away (coordinate a i) ≃ₐ[A] PolynomialTorus A
  | 0 => coordinateLocalizationEquiv a
  | 1 => (swapLocalizationEquiv a).symm.trans (coordinateLocalizationEquiv a)

/-- **The coordinate opens of the node are étale over the affine line**: `D(u)` and `D(v)` in
`Spec A[u,v]/(uv - a)` are isomorphic over `A` to `Spec A[t, t⁻¹] ⊆ 𝔸¹_A`. -/
theorem nodeCoordinateChart (a : A) (i : Fin 2) :
    ∃ e₀ : (coordinateOpen a i).toScheme ⟶ Spec (.of A[X]), Etale e₀ ∧
      e₀ ≫ smoothModel A = (coordinateOpen a i).ι ≫ nodeModel a := by
  let E := nodeCoordinateEquiv a i
  let iso := basicOpenIsoSpecAway (R := CommRingCat.of (Node A a)) (coordinate a i)
  refine ⟨iso.hom ≫ Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A[X] (PolynomialTorus A))), ?_, ?_⟩
  · have : IsIso (Spec.map (CommRingCat.ofHom E.symm.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map E.symm.toRingEquiv.toCommRingCatIso.hom))
    infer_instance
  · have hι : iso.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (Node A a) (Localization.Away (coordinate a i)))) = (coordinateOpen a i).ι :=
      basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of (Node A a)) (coordinate a i)
    change _ = (coordinateOpen a i).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Node A a)))
    rw [← hι]
    simp only [smoothModel, Category.assoc, ← Spec.map_comp]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change E.symm (algebraMap A[X] (PolynomialTorus A) (algebraMap A A[X] r)) =
      algebraMap (Node A a) (Localization.Away (coordinate a i)) (algebraMap A (Node A a) r)
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

/-- **A node chart off the origin gives a smooth chart.** -/
theorem hasSmoothChart_of_node {C Y : Scheme.{u}} (g : C ⟶ Spec (.of A)) (ι : Y ⟶ C)
    [IsOpenImmersion ι] (a : A) (e : Y ⟶ Spec (.of (Node A a))) [Etale e]
    (he : e ≫ nodeModel a = ι ≫ g) (y : Y) (i : Fin 2) (hy : e y ∈ coordinateOpen a i) :
    HasSmoothChart g (ι y) := by
  obtain ⟨e₀, he₀, he₀m⟩ := nodeCoordinateChart a i
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (coordinateOpen a i).ι) (g := e) ⟨e y, hy⟩ y rfl
  refine ⟨pullback (coordinateOpen a i).ι e, pullback.snd _ e ≫ ι, inferInstance,
    pullback.fst _ e ≫ e₀, inferInstance, ⟨z, by rw [Scheme.Hom.comp_apply, hz2]⟩, ?_⟩
  rw [Category.assoc, he₀m, ← Category.assoc, pullback.condition, Category.assoc, he,
    Category.assoc]

end NodeCoordinate

section BaseCharts

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Scheme.{u}}

omit [IsLocalRing A] in
/-- The node model is functorial in ring isomorphisms. -/
def nodeRingEquiv {A' : Type u} [CommRing A'] (E : A ≃+* A') (a' : A') :
    Node A (E.symm a') ≃+* Node A' a' :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv (Fin 2) E) (by
    rw [Algebra.NodeChart.uChartIdeal, Algebra.NodeChart.uChartIdeal, Ideal.map_span,
      Set.image_singleton]
    congr 2
    simp)

omit [IsLocalRing A] in
theorem nodeRingEquiv_algebraMap {A' : Type u} [CommRing A'] (E : A ≃+* A') (a' : A') (r : A) :
    nodeRingEquiv E a' (algebraMap A (Node A (E.symm a')) r) = algebraMap A' (Node A' a') (E r) := by
  change Ideal.quotientEquiv _ _ _ _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
    Ideal.Quotient.mk _ (MvPolynomial.C (E r))
  rw [Ideal.quotientEquiv_apply]
  simp

/-- **Charts over the base.** If `(C, ∅)` is strictly semi-stable over the local `Spec A` and
`x` lies over the closed point, there is an open `U ∋ x` with an étale `A`-morphism to
`Spec A[T]` or to some `Spec A[u,v]/(uv - a)`: the open `Spec A' ⊆ Spec A` of the chart contains
the closed point, hence is all of `Spec A`, and `A ≅ A'`. -/
theorem exists_chart {g : C ⟶ Spec (.of A)} (hC : IsStrictlySemistable g ⊤) (x : C)
    (hx : g x = closedPoint A) :
    ∃ U : C.Opens, x ∈ U ∧
      ((∃ e : U.toScheme ⟶ Spec (.of A[X]), Etale e ∧ e ≫ smoothModel A = U.ι ≫ g) ∨
       (∃ (a : A) (e : U.toScheme ⟶ Spec (.of (Node A a))), Etale e ∧
          e ≫ nodeModel a = U.ι ≫ g)) := by
  obtain ⟨U, hxU, A', _, ι', _, h, hh, hcase⟩ := hC x
  -- the open `Spec A'` is all of `Spec A`
  have hsurj : Function.Surjective ι' := by
    intro t
    have hmem : closedPoint A ∈ Set.range ι' := by
      refine ⟨h ⟨x, hxU⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, hh, Scheme.Hom.comp_apply]
      exact hx
    exact (specializes_closedPoint t).mem_open ι'.isOpenEmbedding.isOpen_range hmem
  have : Epi ι'.base := (TopCat.epi_iff_surjective _).mpr hsurj
  have : IsIso ι' := IsOpenImmersion.isIso ι'
  -- the ring isomorphism `A ≅ A'`
  let ψ : CommRingCat.of A ⟶ CommRingCat.of A' := Spec.preimage ι'
  let ψ' : CommRingCat.of A' ⟶ CommRingCat.of A := Spec.preimage (inv ι')
  have hψ : Spec.map ψ = ι' := Spec.map_preimage _
  have hψ' : Spec.map ψ' = inv ι' := Spec.map_preimage _
  have h1 : ψ ≫ ψ' = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, hψ', Spec.map_id, IsIso.inv_hom_id]
  have h2 : ψ' ≫ ψ = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, hψ', Spec.map_id, IsIso.hom_inv_id]
  let E : A ≃+* A' := RingEquiv.ofRingHom ψ.hom ψ'.hom (by
      ext r; exact congr($h2 r)) (by ext r; exact congr($h1 r))
  have hE : ∀ r, E r = ψ r := fun _ ↦ rfl
  refine ⟨U, hxU, ?_⟩
  rcases hcase with ⟨e, he, rfl, -⟩ | ⟨a', e, he, rfl, -⟩
  · -- smooth model
    let P : A[X] ≃+* A'[X] := Polynomial.mapEquiv E
    refine Or.inl ⟨e ≫ Spec.map (CommRingCat.ofHom P.toRingHom), ?_, ?_⟩
    · have : IsIso (Spec.map (CommRingCat.ofHom P.toRingHom)) :=
        inferInstanceAs (IsIso (Spec.map P.toCommRingCatIso.hom))
      infer_instance
    · rw [← hh, Category.assoc, ← hψ]
      simp only [smoothModel, Category.assoc, ← Spec.map_comp]
      congr 2
      refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
      change P (Polynomial.C r) = Polynomial.C (ψ r)
      simp [P, hE]
  · -- node model
    let N := nodeRingEquiv E a'
    refine Or.inr ⟨E.symm a', e ≫ Spec.map (CommRingCat.ofHom N.toRingHom), ?_, ?_⟩
    · have : IsIso (Spec.map (CommRingCat.ofHom N.toRingHom)) :=
        inferInstanceAs (IsIso (Spec.map N.toCommRingCatIso.hom))
      infer_instance
    · rw [← hh, Category.assoc, ← hψ]
      change e ≫ Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Node A (E.symm a')))) =
        e ≫ Spec.map (CommRingCat.ofHom (algebraMap A' (Node A' a'))) ≫ Spec.map ψ
      simp only [← Spec.map_comp]
      congr 2
      refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
      change N (algebraMap A _ r) = algebraMap A' (Node A' a') (ψ r)
      rw [nodeRingEquiv_algebraMap, hE]

end BaseCharts

section NonzeroParameter

variable {A : Type u} [CommRing A] [IsDomain A]

/-- In `A[u,v]/(uv)`, the annihilator of `u` is contained in `(v)`. -/
theorem mem_span_coordinate1_of_mul_coordinate0_eq_zero {s : Node A 0}
    (hs : s * coordinate (0 : A) 0 = 0) :
    s ∈ Ideal.span {coordinate (0 : A) 1} := by
  obtain ⟨S, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [coordinate, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Algebra.NodeChart.uChartIdeal,
    Ideal.mem_span_singleton, map_zero, sub_zero] at hs
  obtain ⟨Q, hQ⟩ := hs
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) A) ≠ 0 := MvPolynomial.X_ne_zero _
  have hS : S = MvPolynomial.X 1 * Q := by
    apply mul_right_cancel₀ hX
    rw [hQ]
    ring
  rw [hS, map_mul, Ideal.mem_span_singleton]
  exact ⟨Ideal.Quotient.mk _ Q, rfl⟩

/-- In `A[u,v]/(uv)`, the annihilator of `v` is contained in `(u)`. -/
theorem mem_span_coordinate0_of_mul_coordinate1_eq_zero {s : Node A 0}
    (hs : s * coordinate (0 : A) 1 = 0) :
    s ∈ Ideal.span {coordinate (0 : A) 0} := by
  obtain ⟨S, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [coordinate, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Algebra.NodeChart.uChartIdeal,
    Ideal.mem_span_singleton, map_zero, sub_zero] at hs
  obtain ⟨Q, hQ⟩ := hs
  have hX : (MvPolynomial.X 1 : MvPolynomial (Fin 2) A) ≠ 0 := MvPolynomial.X_ne_zero _
  have hS : S = MvPolynomial.X 0 * Q := by
    apply mul_right_cancel₀ hX
    rw [hQ]
    ring
  rw [hS, map_mul, Ideal.mem_span_singleton]
  exact ⟨Ideal.Quotient.mk _ Q, rfl⟩

/-- **The parameter of a node chart at its origin is nonzero** when the source has a local domain
there: otherwise `u v = 0` with `u, v ≠ 0` in the local ring of `A[u,v]/(uv)` at the origin,
which embeds into the local ring of the source by flatness. -/
theorem node_param_ne_zero {Y : Scheme.{u}} (a : A) (e : Y ⟶ Spec (.of (Node A a))) [Flat e]
    (y : Y) [IsDomain (Y.presheaf.stalk y)] (h0 : coordinate a 0 ∈ (e y).asIdeal)
    (h1 : coordinate a 1 ∈ (e y).asIdeal) : a ≠ 0 := by
  rintro rfl
  set p := e y
  -- the local ring of the node at `p` is a domain
  let φ := e.stalkMap y
  have : (φ.hom).Flat := Flat.stalkMap e y
  algebraize [φ.hom]
  have : IsLocalHom (algebraMap ((Spec (.of (Node A 0))).presheaf.stalk p) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom φ.hom)
  have : Module.FaithfullyFlat ((Spec (.of (Node A 0))).presheaf.stalk p) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := FaithfulSMul.algebraMap_injective
    ((Spec (.of (Node A 0))).presheaf.stalk p) (Y.presheaf.stalk y)
  have : IsDomain ((Spec (.of (Node A 0))).presheaf.stalk p) := hinj.isDomain _
  let L := Localization.AtPrime p.asIdeal
  have : IsDomain L := (Spec.stalkIso (.of (Node A 0)) p).commRingCatIsoToRingEquiv.symm.injective.isDomain _
  -- `u v = 0` in `L` with `u, v ≠ 0`
  have hprod : algebraMap (Node A 0) L (coordinate 0 0) * algebraMap (Node A 0) L (coordinate 0 1) = 0 := by
    rw [← map_mul]
    have : coordinate (0 : A) 0 * coordinate 0 1 = algebraMap A (Node A 0) 0 :=
      Algebra.NodeDomain.nodeCoordinateProduct 0
    rw [this, map_zero, map_zero]
  rcases mul_eq_zero.mp hprod with h | h
  · rw [IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl] at h
    obtain ⟨⟨s, hs⟩, hsu⟩ := h
    apply hs
    have := mem_span_coordinate1_of_mul_coordinate0_eq_zero (A := A) hsu
    exact (Ideal.span_singleton_le_iff_mem _).mpr h1 this
  · rw [IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl] at h
    obtain ⟨⟨s, hs⟩, hsv⟩ := h
    apply hs
    have := mem_span_coordinate0_of_mul_coordinate1_eq_zero (A := A) hsv
    exact (Ideal.span_singleton_le_iff_mem _).mpr h0 this

end NonzeroParameter

end DeJongAlterations.StableModification.Blowups
