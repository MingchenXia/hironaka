import DeJongAlterations.StableModification.Blowups.Transport

/-!
# Sections of curves over a local base

Auxiliary facts on sections `σ : S ⟶ C` of a morphism `g : C ⟶ S = Spec A` over a local ring
`A`, used to separate the boundary of a strictly semi-stable curve (M. Temkin, *Stable
modification of relative curves*, Lemma 4.3.2, T:3019–3046; blueprint
`sm-boundary-separation.tex`, `lem:sm-separation-sections`):

* `range_subset_of_closedPoint_mem`, `factorThruOpen`: a section whose closed point lies in an
  open `U` factors through `U`;
* `fromSpecResidueField_comp_eq`: two sections through the same point `σ t = σ' t` agree on
  `Spec κ(t)` (both induce the inverse of the residue field map of `g`);
* `apply_closedPoint_eq_of_apply_eq`: over a separated `g`, two sections whose images meet
  agree at the closed point; hence sections with distinct closed points are disjoint;
* `eq_of_comp_eq_of_apply_eq`: two sections through a common point with the same composite with
  an étale separated map `e` are equal;
* `exists_eq_specMap_evalRingHom`, `exists_eq_specMap_nodePoint`: the `A`-points of the standard
  models are given by `T ↦ c`, respectively `(u, v) ↦ (c, d)` with `cd = a`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Local

variable {A : Type u} [CommRing A] [IsLocalRing A] {C : Scheme.{u}}

/-- Every point of the spectrum of a local ring specializes to the closed point. -/
theorem specializes_closedPoint (t : Spec (.of A)) : t ⤳ closedPoint A := by
  rw [← PrimeSpectrum.le_iff_specializes]
  exact IsLocalRing.le_maximalIdeal t.isPrime.ne_top

/-- A morphism from the spectrum of a local ring whose closed point lies in an open `U` has
image in `U`. -/
theorem range_subset_of_closedPoint_mem (σ : Spec (.of A) ⟶ C) (U : C.Opens)
    (h : σ (closedPoint A) ∈ U) : Set.range σ ⊆ U := by
  rintro _ ⟨t, rfl⟩
  exact ((specializes_closedPoint t).map σ.continuous).mem_open U.isOpen h

/-- The factorization of `σ` through an open containing the image of the closed point. -/
def factorThruOpen (σ : Spec (.of A) ⟶ C) (U : C.Opens) (h : σ (closedPoint A) ∈ U) :
    Spec (.of A) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι σ (by
    rw [Scheme.Opens.range_ι]
    exact range_subset_of_closedPoint_mem σ U h)

@[reassoc (attr := simp)]
theorem factorThruOpen_ι (σ : Spec (.of A) ⟶ C) (U : C.Opens) (h : σ (closedPoint A) ∈ U) :
    factorThruOpen σ U h ≫ U.ι = σ :=
  IsOpenImmersion.lift_fac _ _ _

end Local

section ResidueField

variable {C S : Scheme.{u}}

/-- **Sections through a common point agree on its residue field.** If `σ, σ'` are sections of
`g : C ⟶ S` with `σ t = σ' t`, then `Spec κ(t) ⟶ S ⟶ C` is the same through `σ` and `σ'`:
both residue field maps `κ(σ t) ⟶ κ(t)` are inverse to the one of `g`. -/
theorem fromSpecResidueField_comp_eq (g : C ⟶ S) (σ σ' : S ⟶ C) (hσ : σ ≫ g = 𝟙 S)
    (hσ' : σ' ≫ g = 𝟙 S) (t : S) (ht : σ t = σ' t) :
    S.fromSpecResidueField t ≫ σ = S.fromSpecResidueField t ≫ σ' := by
  -- both composites factor through `Spec κ(σ t)`
  have h1 : S.fromSpecResidueField t ≫ σ =
      Spec.map (σ.residueFieldMap t) ≫ C.fromSpecResidueField (σ t) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField σ t).symm
  have h2 : S.fromSpecResidueField t ≫ σ' =
      Spec.map ((C.residueFieldCongr ht).hom ≫ σ'.residueFieldMap t) ≫
        C.fromSpecResidueField (σ t) := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField σ' t).symm
  rw [h1, h2]
  congr 2
  -- the residue field maps are both left inverse to `κ(t) ⟶ κ(σ t)` induced by `g`
  have hgt : g (σ t) = t := by rw [← Scheme.Hom.comp_apply, hσ]; rfl
  let G : S.residueField t ⟶ C.residueField (σ t) :=
    (S.residueFieldCongr hgt).inv ≫ g.residueFieldMap (σ t)
  have key : ∀ (φ : C.residueField (σ t) ⟶ S.residueField t),
      Spec.map φ ≫ C.fromSpecResidueField (σ t) ≫ g = S.fromSpecResidueField t →
      G ≫ φ = 𝟙 _ := by
    intro φ hφ
    have h3 : C.fromSpecResidueField (σ t) ≫ g =
        Spec.map G ≫ S.fromSpecResidueField t := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g (σ t),
        ← Scheme.residueFieldCongr_fromSpecResidueField hgt]
      simp only [G, Spec.map_comp, Category.assoc]
      rw [← Category.assoc (Spec.map (S.residueFieldCongr hgt).inv), ← Spec.map_comp,
        Iso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [h3, ← Category.assoc, ← Spec.map_comp] at hφ
    have : Spec.map (G ≫ φ) = 𝟙 _ := by
      rw [← cancel_mono (S.fromSpecResidueField t), Category.id_comp]
      exact hφ
    rw [← Spec.map_id, Spec.map_inj] at this
    exact this
  have k1 := key (σ.residueFieldMap t) (by
    rw [← Category.assoc, ← h1, Category.assoc, hσ, Category.comp_id])
  have k2 := key ((C.residueFieldCongr ht).hom ≫ σ'.residueFieldMap t) (by
    rw [← Category.assoc, ← h2, Category.assoc, hσ', Category.comp_id])
  -- left inverses of a field embedding coincide
  ext y
  have e1 := congr($k1 (σ.residueFieldMap t y))
  have e2 : ∀ z, ((C.residueFieldCongr ht).hom ≫ σ'.residueFieldMap t) (G z) = z :=
    fun z ↦ congr($k2 z)
  have hinj : Function.Injective (σ.residueFieldMap t).hom := RingHom.injective _
  have hy : G (σ.residueFieldMap t y) = y := by
    apply hinj
    exact e1
  conv_rhs => rw [← hy]
  rw [e2]

/-- **Sections of a separated morphism over a local base meet at the closed point if they
meet at all.** -/
theorem apply_closedPoint_eq_of_apply_eq {A : Type u} [CommRing A] [IsLocalRing A]
    (g : C ⟶ Spec (.of A)) [IsSeparated g] (σ σ' : Spec (.of A) ⟶ C) (hσ : σ ≫ g = 𝟙 _)
    (hσ' : σ' ≫ g = 𝟙 _) (t : Spec (.of A)) (ht : σ t = σ' t) :
    σ (closedPoint A) = σ' (closedPoint A) := by
  let p : Spec (.of A) ⟶ pullback g g := pullback.lift σ σ' (by rw [hσ, hσ'])
  have hclosed : IsClosed (p ⁻¹' Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range.preimage p.continuous
  have hfS := fromSpecResidueField_comp_eq g σ σ' hσ hσ' t ht
  have hpt : p t ∈ Set.range (pullback.diagonal g) := by
    let f := (Spec (.of A)).fromSpecResidueField t
    obtain ⟨z⟩ : Nonempty (Spec ((Spec (.of A)).residueField t)) := inferInstance
    have hfz : f z = t := Scheme.fromSpecResidueField_apply _ _
    have : f ≫ p = (f ≫ σ) ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · simp [p]
      · simp only [p, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
        exact hfS.symm
    refine ⟨(f ≫ σ) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← this, Scheme.Hom.comp_apply, hfz]
  have hs : p (closedPoint A) ∈ Set.range (pullback.diagonal g) :=
    (specializes_closedPoint t).mem_closed hclosed hpt
  obtain ⟨y, hy⟩ := hs
  have e1 : σ (closedPoint A) = y := by
    rw [← pullback.lift_fst σ σ' (by rw [hσ, hσ'] : σ ≫ g = σ' ≫ g), Scheme.Hom.comp_apply]
    change pullback.fst g g (p (closedPoint A)) = y
    rw [← hy, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  have e2 : σ' (closedPoint A) = y := by
    rw [← pullback.lift_snd σ σ' (by rw [hσ, hσ'] : σ ≫ g = σ' ≫ g), Scheme.Hom.comp_apply]
    change pullback.snd g g (p (closedPoint A)) = y
    rw [← hy, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]
    rfl
  rw [e1, e2]

/-- **Sections with distinct closed points are disjoint.** -/
theorem disjoint_range_of_apply_closedPoint_ne {A : Type u} [CommRing A] [IsLocalRing A]
    (g : C ⟶ Spec (.of A)) [IsSeparated g] (σ σ' : Spec (.of A) ⟶ C) (hσ : σ ≫ g = 𝟙 _)
    (hσ' : σ' ≫ g = 𝟙 _) (h : σ (closedPoint A) ≠ σ' (closedPoint A)) :
    Disjoint (Set.range σ) (Set.range σ') := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
  have htt : t' = t := by
    have := congr(g $ht')
    rwa [← Scheme.Hom.comp_apply, hσ', ← Scheme.Hom.comp_apply, hσ] at this
  subst htt
  exact h (apply_closedPoint_eq_of_apply_eq g σ σ' hσ hσ' t' ht'.symm)

/-- **Uniqueness of sections with a given étale image.** Let `h : U ⟶ S` be a morphism over a
preconnected base, `e : U ⟶ M` étale and separated, and `σ, σ'` sections of `h` through a common
point with `σ ≫ e = σ' ≫ e`. Then `σ = σ'`. -/
theorem eq_of_comp_eq_of_apply_eq [PreconnectedSpace S] {U M : Scheme.{u}} (h : U ⟶ S)
    (e : U ⟶ M) [Etale e] [IsSeparated e] (σ σ' : S ⟶ U) (hσ : σ ≫ h = 𝟙 S)
    (hσ' : σ' ≫ h = 𝟙 S) (t : S) (ht : σ t = σ' t) (he : σ ≫ e = σ' ≫ e) : σ = σ' := by
  let p₁ : S ⟶ pullback e (σ ≫ e) := pullback.lift σ (𝟙 S) (by simp)
  let p₂ : S ⟶ pullback e (σ ≫ e) := pullback.lift σ' (𝟙 S) (by simp [he])
  have hfS := fromSpecResidueField_comp_eq h σ σ' hσ hσ' t ht
  have hp : S.fromSpecResidueField t ≫ p₁ = S.fromSpecResidueField t ≫ p₂ := by
    apply pullback.hom_ext <;> simp [p₁, p₂, hfS]
  have hmeet : (Set.range p₁ ∩ Set.range p₂).Nonempty := by
    obtain ⟨z⟩ : Nonempty (Spec (S.residueField t)) := inferInstance
    refine ⟨p₁ (S.fromSpecResidueField t z), ⟨_, rfl⟩, S.fromSpecResidueField t z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
  have heq := DeJong.eq_of_sections_of_range_inter_nonempty (pullback.snd e (σ ≫ e)) p₁ p₂
    (by simp [p₁]) (by simp [p₂]) hmeet
  have := congr($heq ≫ pullback.fst e (σ ≫ e))
  simpa [p₁, p₂] using this

end ResidueField

section Points

variable {A : Type u} [CommRing A]

/-- **The `A`-points of `Spec A[T]`** are `T ↦ c`. -/
theorem exists_eq_specMap_evalRingHom (f : Spec (.of A) ⟶ Spec (.of A[X]))
    (hf : f ≫ smoothModel A = 𝟙 _) :
    ∃ c : A, f = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ⟨φ.hom X, ?_⟩
  have hC : CommRingCat.ofHom (algebraMap A A[X]) ≫ φ = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_id]
    exact hf
  congr 1
  ext1
  refine Polynomial.ringHom_ext (fun a ↦ ?_) (by simp)
  have := congr($hC a)
  simpa [Polynomial.algebraMap_apply] using this

/-- The `A`-point `(u, v) ↦ (c, d)` of the node model `A[u, v]/(uv - a)`, `cd = a`. -/
def nodePoint (a c d : A) (h : c * d = a) : Node A a →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![c, d]) (by
    intro p hp
    rw [Algebra.NodeChart.uChartIdeal, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp [h])

@[simp]
theorem nodePoint_coordinate0 (a c d : A) (h : c * d = a) :
    nodePoint a c d h (coordinate a 0) = c := by
  simp [nodePoint, coordinate]

@[simp]
theorem nodePoint_coordinate1 (a c d : A) (h : c * d = a) :
    nodePoint a c d h (coordinate a 1) = d := by
  simp [nodePoint, coordinate]

/-- `A`-algebra maps out of the node are determined by the images of the coordinates. -/
theorem node_algHom_ext {B : Type*} [CommRing B] [Algebra A B] (a : A)
    {f₁ f₂ : Node A a →ₐ[A] B} (h0 : f₁ (coordinate a 0) = f₂ (coordinate a 0))
    (h1 : f₁ (coordinate a 1) = f₂ (coordinate a 1)) : f₁ = f₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- **The `A`-points of the node model** are `(u, v) ↦ (c, d)` with `cd = a`. -/
theorem exists_eq_specMap_nodePoint (a : A) (f : Spec (.of A) ⟶ Spec (.of (Node A a)))
    (hf : f ≫ nodeModel a = 𝟙 _) :
    ∃ (c d : A) (h : c * d = a), f = Spec.map (CommRingCat.ofHom (nodePoint a c d h).toRingHom) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hC : CommRingCat.ofHom (algebraMap A (Node A a)) ≫ φ = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_id]
    exact hf
  let ψ : Node A a →ₐ[A] A :=
    { φ.hom with commutes' := fun r ↦ congr($hC r) }
  have hcd : ψ (coordinate a 0) * ψ (coordinate a 1) = a := by
    rw [← map_mul]
    have : coordinate a 0 * coordinate a 1 = algebraMap A (Node A a) a :=
      Algebra.NodeDomain.nodeCoordinateProduct a
    rw [this, AlgHom.commutes]
    rfl
  refine ⟨ψ (coordinate a 0), ψ (coordinate a 1), hcd, ?_⟩
  congr 1
  ext1
  have : ψ = nodePoint a _ _ hcd := node_algHom_ext a (by simp) (by simp)
  exact congrArg AlgHom.toRingHom this

end Points

end DeJongAlterations.StableModification.Blowups
