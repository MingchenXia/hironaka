import DeJongAlterations.StableModification.Curves.SemistableNormalSmooth
import DeJongAlterations.StableModification.Curves.SemistableOpen
import DeJongAlterations.Geometry.NormalCurveModification

/-!
# Semi-stable curves with smooth generic fibre over a normal base are normal

Let `S` be an integral normal scheme and `g : X → S` a nodal curve (`DeJong.IsNodalCurve`) which is
smooth at every point over the generic point of `S`. Then `X` is normal
(`isNormalScheme_of_isNodalCurve`; Temkin, *Stable modification of relative curves*,
T:2966–2967, stated there without proof; blueprint `sm-semistable-normal.tex`,
`thm:sm-semistable-normal`).

The proof is local. A point `x ∈ X` lies in an affine chart `Spec B → X` over `Spec R → S`, with
`R` an integrally closed domain; `x` is the image of a closed point `z` of a geometric fibre
`K ⊗_R B` (`K` an algebraic closure of `κ(x)`). By the nodal hypothesis `z` is a smooth point or a
node. In the first case `exists_away_isIntegrallyClosed_of_spanFinrank_le_one`, in the second
`exists_away_isIntegrallyClosed_of_isFormalNode` show that the local ring of a smaller chart
`Spec B_f` at `x` is an integrally closed domain, and the stalk of `X` at `x` is this local ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace DeJongAlterations.StableModification.Curves.SemistableNormal

open SemistableOpen
open DeJong (IsNodalCurve IsSmoothAt)
open Geometry (IsGeometricOrdinaryDoublePoint)

universe u

section GeometricPoint

/-- Every prime `𝔭` of an `R`-algebra `B` lies under a closed point of the geometric fibre
`K ⊗_R B`, for `K` an algebraic closure of `κ(𝔭)`: the kernel of `k ⊗ b ↦ k · b(𝔭)`. -/
theorem exists_geometricPoint {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra R K) (z : Ideal (K ⊗[R] B)),
      z.IsMaximal ∧
        z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom = 𝔭 := by
  let K := AlgebraicClosure 𝔭.ResidueField
  let ι : B →+* K := (algebraMap 𝔭.ResidueField K).comp (algebraMap B 𝔭.ResidueField)
  let : Algebra R K := (ι.comp (algebraMap R B)).toAlgebra
  let ιR : B →ₐ[R] K := { ι with commutes' := fun _ => rfl }
  let ρ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) ιR (fun _ _ => Commute.all _ _)
  have hρ : Function.Surjective ρ := fun k => ⟨k ⊗ₜ 1, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.id_apply]⟩
  refine ⟨K, inferInstance, inferInstance, inferInstance, RingHom.ker ρ.toRingHom,
    RingHom.ker_isMaximal_of_surjective _ hρ, ?_⟩
  ext b
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change ρ ((1 : K) ⊗ₜ b) = 0 ↔ b ∈ 𝔭
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
  change algebraMap 𝔭.ResidueField K (algebraMap B 𝔭.ResidueField b) = 0 ↔ b ∈ 𝔭
  rw [map_eq_zero_iff _ (algebraMap 𝔭.ResidueField K).injective,
    Ideal.algebraMap_residueField_eq_zero]

end GeometricPoint

section Stalk

/-- The stalk of a scheme at a point of an affine open `W` is the local ring of `Γ(W)` there. -/
theorem isDomain_isIntegrallyClosed_stalk {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    (x : X) (hx : x ∈ W)
    (h : IsDomain (Localization.AtPrime (hW.primeIdealOf ⟨x, hx⟩).asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime (hW.primeIdealOf ⟨x, hx⟩).asIdeal)) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hW.isLocalization_stalk ⟨x, hx⟩
  exact isDomain_isIntegrallyClosed_of_ringEquiv
    (IsLocalization.algEquiv (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hW.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv h

end Stalk

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  SemistableOpen.locallyOfFinitePresentation_spec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- **Semi-stable curves with smooth generic fibre are normal** (Temkin, T:2966–2967;
`thm:sm-semistable-normal`). Let `S` be an integral normal scheme and `g : X → S` a nodal curve
which is smooth at every point over the generic point of `S`. Then `X` is normal. -/
theorem isNormalScheme_of_isNodalCurve {X S : Scheme.{u}} (g : X ⟶ S) [IsNodalCurve g]
    [IsIntegral S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, g x = genericPoint S → IsSmoothAt g x) : IsNormalScheme X := by
  intro x
  -- affine charts `Spec B = W ⊆ X` over `Spec R = V ⊆ S`
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := g ⁻¹ᵁ V) hxV
  have hle : W ≤ g ⁻¹ᵁ V := hWV
  let : Algebra Γ(S, V) Γ(X, W) := (g.appLE V W hle).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, W) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation g inferInstance ⟨V, hV⟩ ⟨W, hW⟩ hle
  have hsq : hW.fromSpec ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g hV hW hle).symm
  have : Nonempty V := ⟨⟨g x, hxV⟩⟩
  have : IsIntegrallyClosed Γ(S, V) :=
    Geometry.NormalCurveModification.affineSections_isIntegrallyClosed hS V hV
  -- generic smoothness on the chart
  have hgenB : ∀ (𝔮 : Ideal Γ(X, W)) [𝔮.IsPrime],
      𝔮.comap (algebraMap Γ(S, V) Γ(X, W)) = ⊥ →
      Algebra.FormallySmooth Γ(S, V) (Localization.AtPrime 𝔮) := by
    intro 𝔮 _ h𝔮
    set q : PrimeSpectrum Γ(X, W) := ⟨𝔮, inferInstance⟩
    have hx' : hW.fromSpec q ∈ W := by
      have h := Set.mem_range_self (f := hW.fromSpec) q
      rw [hW.range_fromSpec] at h
      exact h
    have hq : hW.primeIdealOf ⟨hW.fromSpec q, hx'⟩ = q :=
      hW.fromSpec.isOpenEmbedding.injective (hW.fromSpec_primeIdealOf _)
    have hgx' : g (hW.fromSpec q) = genericPoint S := by
      rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
      have : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) q =
          genericPoint (Spec Γ(S, V)) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h𝔮
      exact (congrArg (fun p => hV.fromSpec p) this).trans
        (genericPoint_eq_of_isOpenImmersion hV.fromSpec)
    have hsm := (formallySmooth_stalkMap_iff V hV W hW hle hx').mp (hgen _ hgx')
    rw [hq] at hsm
    exact hsm
  -- a closed point of a geometric fibre over `x`
  set 𝔭 := hW.primeIdealOf ⟨x, hxW⟩
  have hx𝔭 : hW.fromSpec 𝔭 = x := hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  obtain ⟨K, _, _, _, z, hzmax, hz𝔭⟩ := exists_geometricPoint (R := Γ(S, V)) 𝔭.asIdeal
  set a : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec = a := rfl
  set zp : PrimeSpectrum (K ⊗[Γ(S, V)] Γ(X, W)) := ⟨z, hzmax.isPrime⟩
  have hzc : IsClosed ({zp} : Set (Spec (.of (K ⊗[Γ(S, V)] Γ(X, W))))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hzmax
  set y := tensorChart g hsq ha zp
  have hyx : pullback.fst g a y = x := by
    rw [← jB_comap_eq g hsq ha zp]
    have : PrimeSpectrum.comap (algebraMap Γ(X, W) (K ⊗[Γ(S, V)] Γ(X, W))) zp = 𝔭 :=
      PrimeSpectrum.ext hz𝔭
    rw [this, hx𝔭]
  have hy : IsClosed ({y} : Set (pullback (C := Scheme.{u}) g a)) :=
    isClosed_image_of_isClosed (tensorChart g hsq ha) (tensorChart_snd g hsq ha) hzc
  have hpure := IsNodalCurve.pureGeometricFibers (g := g) K a
  -- it suffices to find a smaller chart `Spec B_f` over which the local ring at `x` is normal
  have key : ∀ f : Γ(X, W), f ∉ 𝔭.asIdeal →
      (∀ z₁ : PrimeSpectrum (K ⊗[Γ(S, V)] Localization.Away f),
        IsClosed ({z₁} : Set (Spec (.of (K ⊗[Γ(S, V)] Localization.Away f)))) →
        tensorChart g (localization_chart_sq g hsq f) ha z₁ = y →
        IsDomain (Localization.AtPrime (z₁.asIdeal.comap (Algebra.TensorProduct.includeRight :
            Localization.Away f →ₐ[Γ(S, V)] K ⊗[Γ(S, V)] Localization.Away f).toRingHom)) ∧
        IsIntegrallyClosed (Localization.AtPrime (z₁.asIdeal.comap
          (Algebra.TensorProduct.includeRight : Localization.Away f →ₐ[Γ(S, V)]
            K ⊗[Γ(S, V)] Localization.Away f).toRingHom))) →
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro f hf hnorm
    have hsq₁ := localization_chart_sq g hsq f
    have hxB₁ : pullback.fst g a y ∈ Set.range
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (Localization.Away f))) ≫
          hW.fromSpec) := by
      rw [hyx, ← hx𝔭]
      exact mem_range_localization_chart f 𝔭 hf
    obtain ⟨z₁, hz₁y, hz₁c⟩ := exists_tensorChart_eq g hsq₁ ha y hy hxB₁
    have h₁ := hnorm z₁ hz₁c hz₁y
    have h₂ := isDomain_isIntegrallyClosed_localization_localization (Submonoid.powers f) _ h₁
    apply isDomain_isIntegrallyClosed_stalk hW x hxW
    refine isDomain_isIntegrallyClosed_of_eq ?_ h₂
    have hxz₁ := jB_comap_eq g hsq₁ ha z₁
    rw [hz₁y, hyx, ← hx𝔭, Scheme.Hom.comp_apply] at hxz₁
    have := hW.fromSpec.isOpenEmbedding.injective hxz₁
    exact congrArg PrimeSpectrum.asIdeal this
  rcases IsNodalCurve.geometricNodes (g := g) K a y hy with hs | hn
  · -- a smooth point
    have hpureT := pure_of_etale (q' := pullback.snd g a) (tensorChart g hsq ha) hpure
    have hdim := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT zp hzc
    have hzs := mem_smoothLocus_of_tensorChart g hsq ha zp hs
    have h1 := (mem_smoothLocus_spec_iff zp hdim).mp hzs
    obtain ⟨f, hf, hnext⟩ := exists_away_isIntegrallyClosed_of_spanFinrank_le_one z h1
    refine key f (hz𝔭 ▸ hf) fun z₁ hz₁c hz₁y => ?_
    have : z₁.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
    have : Module.Flat Γ(S, V) (Localization.Away f) := Module.Flat.trans _ Γ(X, W) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f) :=
      Algebra.FinitePresentation.trans _ Γ(X, W) _
    have hpureT₁ := pure_of_etale (q' := pullback.snd g a)
      (tensorChart g (localization_chart_sq g hsq f) ha) hpure
    have hdim₁ := Resolution.ringKrullDim_stalk_eq_one_of_isClosed hpureT₁ z₁ hz₁c
    let := Scheme.stalkAlgebra
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[Γ(S, V)] Localization.Away f)))) z₁
    let ε := (Geometry.NodeCompletedLocalSpecLocalization.stalkEquiv K
      (K ⊗[Γ(S, V)] Localization.Away f) z₁).toRingEquiv
    have hdimL : ringKrullDim (Localization.AtPrime z₁.asIdeal) = 1 := by
      rw [← ringKrullDim_eq_of_ringEquiv ε]
      exact hdim₁
    exact hnext K z₁.asIdeal hdimL
  · -- a node
    have hzn := isGeometricOrdinaryDoublePoint_of_tensorChart g hsq ha zp hzc hn
    obtain ⟨f, hf, hnext⟩ := exists_away_isIntegrallyClosed_of_isFormalNode hgenB z
      ((isGeometricOrdinaryDoublePoint_spec_iff zp).mp hzn)
    refine key f (hz𝔭 ▸ hf) fun z₁ hz₁c hz₁y => ?_
    have : z₁.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₁).mp hz₁c
    have : Module.Flat Γ(S, V) (Localization.Away f) := Module.Flat.trans _ Γ(X, W) _
    have : Algebra.FinitePresentation Γ(S, V) (Localization.Away f) :=
      Algebra.FinitePresentation.trans _ Γ(X, W) _
    have hz₁n := isGeometricOrdinaryDoublePoint_of_tensorChart g (localization_chart_sq g hsq f)
      ha z₁ hz₁c (hz₁y ▸ hn)
    exact hnext K z₁.asIdeal ((isGeometricOrdinaryDoublePoint_spec_iff z₁).mp hz₁n)

/-- **Semi-stable curves with smooth generic fibre over a normal domain are normal**: the case
`S = Spec R` (for instance `R` a valuation ring, Temkin's situation). -/
theorem isNormalScheme_of_isNodalCurve_spec {X : Scheme.{u}} {R : Type u} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] (g : X ⟶ Spec (.of R)) [IsNodalCurve g]
    (hgen : ∀ x : X, (g x).asIdeal = ⊥ → IsSmoothAt g x) : IsNormalScheme X :=
  isNormalScheme_of_isNodalCurve g (isNormalScheme_spec R) fun x hx => hgen x (by
    rw [hx, genericPoint_eq_bot_of_affine]
    rfl)

end Main

end DeJongAlterations.StableModification.Curves.SemistableNormal
