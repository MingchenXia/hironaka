import DeJongAlterations.StableModification.Limits.SpreadDimension
import DeJongAlterations.StableModification.Limits.SpreadFlat
import DeJongAlterations.StableModification.Limits.Descent
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Spreading out nodal curves along the system of quasi-alterations

Let `k` be a field, `A` a finitely generated `k`-algebra, `L` a field over `A` and `R ⊆ L` an
`A`-subalgebra (for instance a valuation ring `V` of `L = K(S)^s` centred on an affine open
`Spec A` of a variety `S`). By lane LIM1 (`Limits.Descent`) every scheme of finite presentation
over `Spec R` comes from a scheme of finite presentation over `Spec B` for some finitely
generated `A`-subalgebra `B ⊆ R`, `Spec R` being the limit of the affine schemes `Spec B`. This
file proves that **nodal curves spread out** (`exists_isNodalCurve_baseChange`): if `X ⟶ Spec R`
is a nodal curve (`DeJong.IsNodalCurve`) and `Y ⟶ Spec B₀` a model of finite presentation, then
`Y ×_{Spec B₀} Spec B ⟶ Spec B` is a nodal curve for some `B ⊇ B₀`.

This is the semi-stable half of Temkin's Remark 3.1.1 (`prem`, M. Temkin, *Stable modification of
relative curves*, `semi-stable.tex` T:2283–2300) as used in the proofs of Theorems 1.2 and 1.5
(T:3347–3352, T:3384–3389) to spread a semi-stable curve over `Spec 𝒪_{𝔖,𝔵}` to a
quasi-alteration of the base. Since `D(f) ⊆ Spec B` for `f ∈ B` a unit of `R` is again a member
`Spec B[1/f]` of the system, "over some `Spec B`" is the same as "over a neighbourhood of the
centre in some `Spec B`".

## Proof

* Flatness at some level `B₁` (`Spread.exists_flat_pullback_snd`, lane FD).
* Pure one-dimensionality of all geometric fibres of `Y₁ = Y ×_{B₀} B₁ ⟶ Spec B₁`: the geometric
  generic fibre of `Y₁` is a geometric fibre of `X`, so the generic fibre of `Y₁` has pure
  dimension one (`Spread.pure_fiber_of_pure_pullback`); by Codex's
  `DeJong.flatFamilyPureFiberDimension` (EGA IV 6.1.2 over the variety `Spec B₁`) every fibre has
  pure dimension one, hence every geometric fibre
  (`Spread.pureOneDimensionalFibres_of_hasPureFiberDimension`).
* Every point of `X` maps into the nodal locus of `Y₁ ⟶ Spec B₁`: the geometric fibres of `X`
  are geometric fibres of `Y₁` and are nodal, and lane SS2's
  `Curves.SemistableOpen.fst_mem_nodalLocus_of_isNodalFiber` applies.
* The nodal locus is an open of `Y₁` containing the image of the limit `X`, so it contains the
  image of some `Y₂ = Y ×_{B₀} B₂` (Mathlib's `exists_map_eq_top`, EGA IV 8.3.3); the nodal locus
  is stable under base change (`preimage_nodalLocus_le`), so `Y₂ ⟶ Spec B₂` is nodal.

No properness is used (Temkin's argument uses openness of the semi-stable locus, Lemma 5.1(i),
and approximation; the `nodalBase` route of the lane brief would need properness of the model,
which is not available by LIM1's descent).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

open DeJong (IsNodalCurve)
open Curves.SemistableOpen (nodalLocus)

section NodalLocus

variable {C S C' S' : Scheme.{u}} {g : C ⟶ S} {ψ : S' ⟶ S} {fst' : C' ⟶ C} {snd' : C' ⟶ S'}

/-- **The nodal locus is stable under base change.** For a pullback square `C' = C ×_S S'`, the
preimage of the nodal locus of `C ⟶ S` lies in the nodal locus of `C' ⟶ S'`. -/
theorem preimage_nodalLocus_le (h : IsPullback fst' snd' g ψ) :
    fst' ⁻¹ᵁ nodalLocus g ≤ nodalLocus snd' := by
  set N := nodalLocus g
  have hN : IsNodalCurve (N.ι ≫ g) := Curves.SemistableOpen.isNodalCurve_nodalLocus g
  have hsq : IsPullback (fst' ∣_ N) ((fst' ⁻¹ᵁ N).ι ≫ snd') (N.ι ≫ g) ψ :=
    (isPullback_morphismRestrict fst' N).paste_vert h
  have : IsNodalCurve ((fst' ⁻¹ᵁ N).ι ≫ snd') := by
    rw [← hsq.isoPullback_hom_snd]
    exact Curves.IsNodalCurve.etale_comp _ _
  exact Curves.SemistableOpen.le_nodalLocus snd' this

/-- If the base change square maps everything into the nodal locus, the base change is nodal. -/
theorem isNodalCurve_of_isPullback (h : IsPullback fst' snd' g ψ)
    (htop : fst' ⁻¹ᵁ nodalLocus g = ⊤) : IsNodalCurve snd' := by
  rw [Curves.SemistableOpen.isNodalCurve_iff_nodalLocus_eq_top]
  exact top_unique (htop ▸ preimage_nodalLocus_le h)

end NodalLocus

section QASystem

variable {A L : Type u} [CommRing A] [Field L] [Algebra A L]

/-- An `A`-subalgebra `B ⊇ B₀` of `L`, regarded as a `B₀`-subalgebra. -/
def toSubalgebra (B₀ B : Subalgebra A L) (h : B₀ ≤ B) : Subalgebra B₀ L where
  toSubsemiring := B.toSubsemiring
  algebraMap_mem' b := h b.2

@[simp]
lemma mem_toSubalgebra {B₀ B : Subalgebra A L} {h : B₀ ≤ B} {x : L} :
    x ∈ toSubalgebra B₀ B h ↔ x ∈ B :=
  Iff.rfl

variable (k : Type u) [Field k] [Algebra k A] [Algebra.FiniteType k A] (R : Subalgebra A L)

/-- The spectrum of a member of the approximating system is a variety over `k`. -/
theorem isVariety_spec (B : FGSubalgebra A R) :
    IsVariety (Spec.map (CommRingCat.ofHom ((algebraMap A B.1).comp (algebraMap k A)))) := by
  have : Algebra.FiniteType A B.1 := (Subalgebra.fg_iff_finiteType _).1 B.2.1
  have hft : ((algebraMap A B.1).comp (algebraMap k A)).FiniteType :=
    RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.2 inferInstance)
      (RingHom.finiteType_algebraMap.2 inferInstance)
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom ((algebraMap A B.1).comp (algebraMap k A)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact hft
  exact {}

variable {R}

/-- The image of the generic point of `Spec R` in `Spec B` is the generic point. -/
theorem π_app_genericPoint (B : FGSubalgebra A R) :
    (fgSpecCone R).π.app (op B) (genericPoint (Spec (.of R))) = genericPoint (Spec (.of B.1)) := by
  have h1 : genericPoint (Spec (.of R)) = (⊥ : PrimeSpectrum R) :=
    genericPoint_eq_bot_of_affine (.of R)
  have h2 : genericPoint (Spec (.of B.1)) = (⊥ : PrimeSpectrum B.1) :=
    genericPoint_eq_bot_of_affine (.of B.1)
  change Spec.map (CommRingCat.ofHom (Subalgebra.inclusion B.2.2).toRingHom) _ = _
  rw [h1, h2, Spec.map_apply]
  refine PrimeSpectrum.ext (Ideal.ext fun x ↦ ?_)
  change (Subalgebra.inclusion B.2.2) x = 0 ↔ x = 0
  constructor
  · intro hx
    exact Subtype.ext (congrArg Subtype.val hx :)
  · rintro rfl
    exact map_zero _

include k in
/-- **Nodal curves spread out along the approximating system** (Temkin, Rem. 3.1.1, semi-stable
part, for the base `Spec R`, `R = ⋃ B`, `B` finitely generated over `A`, `A` of finite type over
a field `k`). Let `f : X ⟶ Spec R` be a nodal curve and `m` a model of finite presentation of
`X` over `Spec B₀`. Then the base change of `m` to some `Spec B`, `B ⊇ B₀`, is a nodal curve
over `Spec B`. -/
theorem exists_isNodalCurve_baseChange {X : Scheme.{u}} {f : X ⟶ (fgSpecCone R).pt}
    [IsNodalCurve f] {B₀ : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f B₀) (hm : m.IsFP) :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ) (h : B ⟶ B₀), IsNodalCurve (m.baseChange h).fY := by
  obtain ⟨_, _, _⟩ := hm
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set B0 := B₀.unop
  have hnoethB : ∀ B : FGSubalgebra A R, IsNoetherianRing B.1 := fun B ↦ by
    have : Algebra.FiniteType A B.1 := (Subalgebra.fg_iff_finiteType _).1 B.2.1
    exact Algebra.FiniteType.isNoetherianRing A B.1
  have : IsNoetherianRing B0.1 := hnoethB B0
  -- Step 1: flatness at some level `B₁`
  let ι := {B : FGSubalgebra A R // B0 ≤ B}
  have : IsDirected ι (· ≤ ·) := ⟨fun B B' ↦
    ⟨⟨⟨B.1.1 ⊔ B'.1.1, B.1.2.1.sup B'.1.2.1, sup_le B.1.2.2 B'.1.2.2⟩,
      B.2.trans (le_sup_left (a := B.1.1))⟩, le_sup_left (a := B.1.1),
      le_sup_right (a := B.1.1)⟩⟩
  have : Nonempty ι := ⟨⟨B0, le_rfl⟩⟩
  let F : ι →o Subalgebra B0.1 L :=
    ⟨fun B ↦ toSubalgebra B0.1 B.1.1 B.2, fun _ _ h x hx ↦ h hx⟩
  let R' := toSubalgebra B0.1 R B0.2.2
  have hF : ∀ i, F i ≤ R' := fun i x hx ↦ i.1.2.2 hx
  have hR : ∀ x ∈ R', ∃ i, x ∈ F i := fun x hx ↦ by
    classical
    obtain ⟨B, hB, hxB⟩ := exists_finset_subset {x} (by simpa using (show x ∈ R from hx)) B0
    exact ⟨⟨B, hB⟩, hxB (by simp)⟩
  have hnoeth : ∀ i, IsNoetherianRing (F i) := fun i ↦ hnoethB i.1
  have hflat : Flat (pullback.snd (m.fY : m.Y ⟶ Spec (.of B0.1))
      (Spec.map (CommRingCat.ofHom (algebraMap B0.1 R')))) := by
    change Flat (pullback.snd m.fY ((fgSpecCone R).π.app B₀))
    rw [← m.isPullback.isoPullback_inv_snd]
    infer_instance
  obtain ⟨i₁, hi₁⟩ := exists_flat_pullback_snd F R' hF hR hnoeth
    (m.fY : m.Y ⟶ Spec (.of B0.1)) hflat
  set B1 := i₁.1
  let h₁ : op B1 ⟶ B₀ := (homOfLE i₁.2).op
  set m₁ := m.baseChange h₁
  set g := m₁.fY
  have : Flat g := hi₁ i₁ le_rfl
  have : LocallyOfFinitePresentation g := inferInstanceAs (LocallyOfFinitePresentation
    (pullback.snd _ _))
  have : QuasiCompact g := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  -- geometric fibres of `Y₁` at geometric points of `Spec R` are geometric fibres of `X`
  have hsq : ∀ {K : Type u} [Field K] (a : Spec (.of K) ⟶ (fgSpecCone R).pt),
      IsPullback (pullback.fst f a ≫ m₁.g) (pullback.snd f a) g
        (a ≫ (fgSpecCone R).π.app (op B1)) :=
    fun a ↦ (IsPullback.of_hasPullback f a).paste_horiz m₁.isPullback
  -- Step 2: the geometric fibres of `Y₁ ⟶ Spec B₁` have pure dimension one
  have hpure : Curves.SemistableOpen.PureOneDimensionalFibres g := by
    apply pureOneDimensionalFibres_of_hasPureFiberDimension
    let pS := Spec.map (CommRingCat.ofHom ((algebraMap A B1.1).comp (algebraMap k A)))
    have : IsVariety pS := isVariety_spec k R B1
    refine DeJong.FlatDimension.flatFamilyPureFiberDimension k (Spec (.of B1.1)) m₁.Y pS g 1 ?_
    let v₀ := genericPoint (Spec (.of R))
    let Ω := AlgebraicClosure ((Spec (.of R)).residueField v₀)
    let aInf : Spec (.of Ω) ⟶ (fgSpecCone R).pt :=
      Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField v₀) Ω)) ≫
        (Spec (.of R)).fromSpecResidueField v₀
    have ha : (aInf ≫ (fgSpecCone R).π.app (op B1)) (IsLocalRing.closedPoint Ω) =
        genericPoint (Spec (.of B1.1)) := by
      rw [Scheme.Hom.comp_apply]
      have : aInf (IsLocalRing.closedPoint Ω) = v₀ := by
        rw [Scheme.Hom.comp_apply]
        exact Scheme.fromSpecResidueField_apply _ _
      rw [this]
      exact π_app_genericPoint B1
    have hgeo : ∀ Z ∈ irreducibleComponents
        (pullback (C := Scheme.{u}) g (aInf ≫ (fgSpecCone R).π.app (op B1))),
        topologicalKrullDim Z = 1 :=
      pure_of_homeomorph (hsq aInf).isoPullback.schemeIsoToHomeo
        ((inferInstance : IsNodalCurve f).pureGeometricFibers Ω aInf)
    have := pure_fiber_of_pure_pullback g _ hgeo
    rwa [ha] at this
  -- Step 3: every point of `X` maps into the nodal locus of `Y₁ ⟶ Spec B₁`
  have hloc : ∀ x : X, m₁.g x ∈ nodalLocus g := by
    intro x
    let K := AlgebraicClosure (X.residueField x)
    let b : Spec (.of K) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
    let e := (hsq (b ≫ f)).isoPullback
    have hfib : Curves.IsNodalFiber (pullback.snd g ((b ≫ f) ≫ (fgSpecCone R).π.app (op B1))) := by
      rw [← (hsq (b ≫ f)).isoPullback_inv_snd]
      exact Curves.IsNodalFiber.of_etale e.inv (Curves.IsNodalCurve.isNodalFiber f K (b ≫ f))
    let z := pullback.lift (f := f) (g := b ≫ f) b (𝟙 _) (by simp) (IsLocalRing.closedPoint K)
    have hmem := Curves.SemistableOpen.fst_mem_nodalLocus_of_isNodalFiber g hpure K _ hfib
      (e.hom z)
    have hz : pullback.fst g ((b ≫ f) ≫ (fgSpecCone R).π.app (op B1)) (e.hom z) = m₁.g x := by
      rw [← Scheme.Hom.comp_apply, (hsq (b ≫ f)).isoPullback_hom_fst, Scheme.Hom.comp_apply]
      congr 1
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rwa [hz] at hmem
  -- Step 4: the nodal locus contains the image of some later level
  have hc' := isLimitBaseChangeCone _ _ (isLimitFGSpecCone R) m.isPullback
  obtain ⟨j, fj, hj⟩ := exists_map_eq_top _ _ hc'
    (i := Over.mk h₁) (nodalLocus g) (by
      rw [eq_top_iff]
      intro x _
      exact hloc x)
  refine ⟨j.left, j.hom, ?_⟩
  exact isNodalCurve_of_isPullback (isPullback_baseChangeDiagram_map _ m.fY fj) hj

end QASystem

end DeJongAlterations.StableModification.Limits.Spread
