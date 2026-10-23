import DeJongAlterations.StableModification.Limits.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Descent of flatness for schemes of finite type along directed unions

Let `R₀` be a noetherian ring, `L` an `R₀`-algebra, `F i` a directed family of noetherian
`R₀`-subalgebras of `L` and `R ⊆ L` their union. Let `Y` be a scheme of finite type and
quasi-compact over `Spec R₀`. If the base change `Y ×_{Spec R₀} Spec R` is flat over `Spec R`,
then `Y ×_{Spec R₀} Spec (F j)` is flat over `Spec (F j)` for all large `j`
(`exists_flat_pullback_snd`). This is the scheme form of lane FD's algebraic descent of flatness
`Limits.FlatDescent.flat_tensor_of_flat_tensor_union` (EGA IV₃ 11.2.6 in the case used by
Temkin, *Stable modification of relative curves*, §3.1, T:2262–2275): cover `Y` by finitely many
affine opens `Spec C_k`; the base changes are `Spec (S ⊗_{R₀} C_k)`
(`flat_pullback_snd_spec_iff`), and flatness is local on the source.

Blueprint: `sm-spread.tex`, `lem:sm-spread-flat`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

/-- **Flatness of an affine base change.** `Spec (S ⊗_{R₀} C) ⟶ Spec S` is the base change of
`Spec C ⟶ Spec R₀`; it is flat iff `S ⊗_{R₀} C` is a flat `S`-module. -/
theorem flat_pullback_snd_spec_iff (R₀ S C : Type u) [CommRing R₀] [CommRing S] [CommRing C]
    [Algebra R₀ S] [Algebra R₀ C] :
    Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R₀ C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))) ↔ Module.Flat S (S ⊗[R₀] C) := by
  have e : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R₀ C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₀ S))) =
      (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R₀ S C).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R₀] C))) := by
    rw [pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]
  rw [e, MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
    HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]

/-- Precomposing with an isomorphism does not change flatness of a base change. -/
theorem flat_pullback_snd_iso_comp_iff {V W S T : Scheme.{u}} (e : V ≅ W) (w : W ⟶ S)
    (t : T ⟶ S) : Flat (pullback.snd (e.hom ≫ w) t) ↔ Flat (pullback.snd w t) := by
  have h : pullback.snd (e.hom ≫ w) t =
      pullback.map (e.hom ≫ w) t w t e.hom (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd w t := by
    simp
  rw [h, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]

/-- **Affine pieces.** For an affine scheme `V` with a morphism `v : V ⟶ Spec R₀` and an
`R₀`-algebra `S`, the base change `V ×_{Spec R₀} Spec S ⟶ Spec S` is flat iff
`S ⊗_{R₀} Γ(V)` is `S`-flat, for the `R₀`-algebra structure on `Γ(V)` defined by `v`. -/
theorem flat_pullback_snd_affine_iff {R₀ S : Type u} [CommRing R₀] [CommRing S] [Algebra R₀ S]
    {V : Scheme.{u}} [IsAffine V] (v : V ⟶ Spec (.of R₀)) :
    letI : Algebra R₀ Γ(V, ⊤) := (Spec.preimage (V.isoSpec.inv ≫ v)).hom.toAlgebra
    Flat (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))) ↔
      Module.Flat S (S ⊗[R₀] Γ(V, ⊤)) := by
  let : Algebra R₀ Γ(V, ⊤) := (Spec.preimage (V.isoSpec.inv ≫ v)).hom.toAlgebra
  have hv : v = V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ Γ(V, ⊤))) := by
    have : CommRingCat.ofHom (algebraMap R₀ Γ(V, ⊤)) = Spec.preimage (V.isoSpec.inv ≫ v) := rfl
    rw [this, Spec.map_preimage, Iso.hom_inv_id_assoc]
  have h := (flat_pullback_snd_iso_comp_iff V.isoSpec
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ Γ(V, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))).trans
    (flat_pullback_snd_spec_iff R₀ S Γ(V, ⊤))
  rw [← hv] at h
  exact h

/-- `Spec.preimage` of a morphism `Spec C ⟶ Spec R₀` locally of finite type is of finite type. -/
theorem finiteType_preimage {R₀ : Type u} [CommRing R₀] {V : Scheme.{u}} [IsAffine V]
    (v : V ⟶ Spec (.of R₀)) [LocallyOfFiniteType v] :
    (Spec.preimage (V.isoSpec.inv ≫ v)).hom.FiniteType := by
  have : LocallyOfFiniteType (Spec.map (Spec.preimage (V.isoSpec.inv ≫ v))) := by
    rw [Spec.map_preimage]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this

variable {R₀ L : Type u} [CommRing R₀] [CommRing L] [Algebra R₀ L]
  {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (F : ι →o Subalgebra R₀ L) (R : Subalgebra R₀ L) (hF : ∀ i, F i ≤ R)
  (hR : ∀ x ∈ R, ∃ i, x ∈ F i)

include hF hR in
/-- **Descent of flatness along a directed union of noetherian subalgebras** (EGA IV₃ 11.2.6,
lane FD). Let `fY : Y ⟶ Spec R₀` be locally of finite type and quasi-compact, `R₀` noetherian,
and `R = ⋃ F i` a directed union of noetherian `R₀`-subalgebras of `L`. If the base change of
`fY` to `Spec R` is flat, so is its base change to `Spec (F j)` for all large `j`. -/
theorem exists_flat_pullback_snd [IsNoetherianRing R₀] (hnoeth : ∀ i, IsNoetherianRing (F i))
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of R₀)) [LocallyOfFiniteType fY] [QuasiCompact fY]
    (hflat : Flat (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))))) :
    ∃ i, ∀ j, F i ≤ F j →
      Flat (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap R₀ (F j))))) := by
  classical
  have : CompactSpace Y :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := fY) |>.mp inferInstance
  let 𝒰 := Y.affineCover.finiteSubcover
  have hfin : Finite 𝒰.I₀ := inferInstanceAs (Finite (Subtype _))
  -- flatness of `pullback.snd fY t` is checked on the pieces `𝒰.X k ×_{R₀} Spec S`
  have hloc : ∀ {S : Type u} [CommRing S] [Algebra R₀ S],
      Flat (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))) ↔
        ∀ k, Flat (pullback.snd (𝒰.f k ≫ fY) (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))) := by
    intro S _ _
    set t := Spec.map (CommRingCat.ofHom (algebraMap R₀ S))
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (𝒰.pullback₁ (pullback.fst fY t))]
    refine forall_congr' fun k ↦ ?_
    have : (𝒰.pullback₁ (pullback.fst fY t)).f k ≫ pullback.snd fY t =
        ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso fY t (𝒰.f k)).hom) ≫
          pullback.snd (𝒰.f k ≫ fY) t := by
      change pullback.fst (pullback.fst fY t) (𝒰.f k) ≫ _ = _
      simp
    rw [this, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
  -- the algebras of the pieces
  let C : 𝒰.I₀ → Type u := fun k ↦ Γ(𝒰.X k, ⊤)
  let _ : ∀ k, Algebra R₀ (C k) := fun k ↦
    (Spec.preimage ((𝒰.X k).isoSpec.inv ≫ (𝒰.f k ≫ fY))).hom.toAlgebra
  have hft : ∀ k, Algebra.FiniteType R₀ (C k) := fun k ↦
    finiteType_preimage (𝒰.f k ≫ fY)
  have hpiece : ∀ {S : Type u} [CommRing S] [Algebra R₀ S] (k : 𝒰.I₀),
      Flat (pullback.snd (𝒰.f k ≫ fY) (Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))) ↔
        Module.Flat S (S ⊗[R₀] C k) := fun k ↦ flat_pullback_snd_affine_iff (𝒰.f k ≫ fY)
  have hR' : ∀ k, Module.Flat R (R ⊗[R₀] C k) := fun k ↦ (hpiece k).mp ((hloc.mp hflat) k)
  -- descend flatness of each piece, then take a common index
  have hk : ∀ k : 𝒰.I₀, ∃ i, ∀ j, F i ≤ F j → Module.Flat (F j) (F j ⊗[R₀] C k) := fun k ↦
    FlatDescent.flat_tensor_of_flat_tensor_union F R hF hR hnoeth (C k)
  choose i hi using hk
  have : Fintype 𝒰.I₀ := Fintype.ofFinite _
  obtain ⟨i₀, hi₀⟩ := Finset.exists_le (α := ι) (Finset.univ.image i)
  refine ⟨i₀, fun j hj ↦ hloc.mpr fun k ↦ (hpiece k).mpr (hi k j ?_)⟩
  exact (F.monotone (hi₀ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))).trans hj

end DeJongAlterations.StableModification.Limits.Spread
