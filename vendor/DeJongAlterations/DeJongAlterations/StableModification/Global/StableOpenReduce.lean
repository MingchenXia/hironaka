/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Global.StableOpenAscent
import DeJongAlterations.StableModification.Global.SetupModel
import DeJongAlterations.Geometry.NormalizationFiniteArbitraryField

/-!
# Reduction of `StableOpenNbhdConn` to a rational point of a normal variety

Node G4 of `PLAN-T5.md` (Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Lemma 5.1 (ii) `openloclem`, T:3282–3311; ERRATA DJA-O36). We reduce the corrected
spreading statement `StableOpenNbhdConn k` to its special case `StableOpenNbhdRational K`: a
`K`-rational point of a *normal* variety over an *algebraically closed* field `K` (the ω step,
left as a hypothesis).

Let `U` be a variety over `k`, `(q, β, D')` a family over `U` as in `StableOpenNbhdConn`, and `a`
a geometric point over `z ∈ U` with value field `K`.

1. **Base change to `U_K = U ×_k Spec K`** (`stableOpenNbhdConn_of_rational`). The point `a` gives
   a section `σ` of `U_K ⟶ Spec K` with `σ ≫ pr₁ = a`; the base-changed family is projective
   relative to `K` (`Projectivity.isRelativelyProjective_comp_specMap_iff`) and semi-stable, and
   its fibre at `σ` is that of `(q, β, D')` at `a`. The projection `U_K ⟶ U` is universally open
   (a base change of `Spec K ⟶ Spec k`), so the image of an open neighbourhood of `σ` is an open
   neighbourhood of `z`; numerical stability descends by `isNumericallyStableAt_of_pullback`
   (one geometric fibre suffices, `isNumericallyStableAt_of_numericallyStableFibre`).
2. **Normalization of the components** (`exists_open_of_stableOpenNbhdRational`). `U_K` is of
   finite type over `K`, so it has finitely many irreducible components `closure {v}`. For each
   of them let `ν_v : N_v ⟶ U_K` be the normalization of the reduced closure, a normal variety
   over `K` with `ν_v` finite and onto `closure {v}`. Every point `w` of `N_v` over `σ(*)` is
   closed (the fibre is finite, `N_v` is Jacobson), hence carries a `K`-point `σ_w` with
   `σ_w ≫ ν_v = σ` (`pointOfClosedPoint`, `ext_of_apply_closedPoint_eq`); the base change of the
   family to `N_v` has at `σ_w` the fibre at `σ`, so `StableOpenNbhdRational K` gives an open
   `O_w ∋ w` of `N_v` over which the family is numerically stable (`exists_open_normalization`).
   The images `ν_v(N_v ∖ ⋃_w O_w)` are closed (`ν_v` is finite) and miss `σ(*)`; the complement of
   their finite union is the required neighbourhood.

Blueprint: `sm-global-stable-open.tex`, `lem:sm-gso-normalization-open`,
`prop:sm-gso-rational-finite-type`, `thm:sm-gso-reduction`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsRelativelyProjective)
open Curves (pullbackCompMap)
open Geometry.NormalizationGluing (normalization normalizationStructure
  normalization_isNormalScheme)
open BlowDown.ClosureComponent (closureScheme closureι range_closureι)

section Helpers

variable {C C' S S' : Scheme.{u}}

/-- **Base change of relative projectivity of `β`**: if `β : C' ⟶ C` is projective relative to
`q ≫ pU`, its base change `C' ×_U T ⟶ C ×_U T` along `p : T ⟶ U` is projective relative to
`C ×_U T ⟶ T ⟶ U ⟶ Spec k`. -/
theorem isRelativelyProjective_pullbackCompMap {k : Type u} [CommRing k] {U T : Scheme.{u}}
    {pU : U ⟶ Spec (.of k)} {q : C ⟶ U} {β : C' ⟶ C} (hβ : IsRelativelyProjective (q ≫ pU) β)
    (p : T ⟶ U) :
    IsRelativelyProjective (pullback.snd q p ≫ p ≫ pU) (pullbackCompMap β q p) := by
  have H := Limits.SpreadModification.isPullback_pullbackCompMap β q p
  have h₁ := hβ.pullback_snd (pullback.fst q p)
  rw [← H.isoPullback_hom_snd]
  have h₂ := IsRelativelyProjective.iso_comp h₁ H.isoPullback.hom
  rwa [pullback.condition_assoc] at h₂

/-- Every point of a scheme lies under a geometric point (over the algebraic closure of its
residue field). -/
theorem exists_geometricPoint {Y : Scheme.{u}} (y : Y) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (b : Spec (.of Ω) ⟶ Y), ∀ x, b x = y :=
  ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y,
    fun x ↦ by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

/-- **Numerical stability descends along any base change** (for `β ≫ g` proper and `g` locally of
finite type): if the base change along `ψ : S' ⟶ S` is numerically stable over `s'`, then
`(β, g, D')` is numerically stable over `ψ(s')` (one geometric fibre over `ψ(s')` is numerically
stable, `isNumericallyStableAt_of_numericallyStableFibre`). -/
theorem isNumericallyStableAt_of_pullback {β : C' ⟶ C} {g : C ⟶ S} {D' : C'.IdealSheafData}
    [IsProper (β ≫ g)] [LocallyOfFiniteType g] (ψ : S' ⟶ S) {s' : S'}
    (h : IsNumericallyStableAt (pullbackCompMap β g ψ) (pullback.snd g ψ)
      (D'.comap (pullback.fst (β ≫ g) ψ)) s') :
    IsNumericallyStableAt β g D' (ψ s') := by
  obtain ⟨Ω, _, _, b, hb⟩ := exists_geometricPoint s'
  refine isNumericallyStableAt_of_numericallyStableFibre β g D' (b ≫ ψ)
    (fun x ↦ by rw [Scheme.Hom.comp_apply, hb]) ?_
  exact (numericallyStableFibre_pullback_iff β g D' ψ b).mp (h Ω b hb)

/-- In a Jacobson space, the points of a finite closed set are closed. -/
theorem isClosed_singleton_of_finite {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {F : Set X} (hF : IsClosed F) (hfin : F.Finite) {y : X} (hy : y ∈ F) :
    IsClosed ({y} : Set X) := by
  have hcl : IsClosed (F ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (F ∩ closedPoints X)]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion fun x hx => hx.2
  have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed
  rw [hcl.closure_eq, hF.closure_eq] at h1
  rw [← h1] at hy
  exact hy.2

end Helpers

section Normalization

variable {K : Type u} [Field K] {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K))

/-- The reduced closure of a point of a variety-like `K`-scheme is a variety. -/
theorem isVariety_closureι [IsSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY] (v : Y) :
    IsVariety (closureι v ≫ pY) :=
  .mk

/-- The normalization of the reduced closure of `v`, mapped to `Y`, is finite. -/
theorem isFinite_normalization_closure [LocallyOfFiniteType pY] (v : Y) :
    IsFinite (normalizationStructure (closureScheme v) ≫ closureι v) := by
  have : IsFinite (normalizationStructure (closureScheme v)) :=
    Geometry.NormalizationFiniteArbitraryField.normalizationStructure_isFinite (closureι v ≫ pY)
  infer_instance

/-- The normalization of the reduced closure of `v` maps onto `closure {v}`. -/
theorem range_normalization_closure [LocallyOfFiniteType pY] (v : Y) :
    Set.range (normalizationStructure (closureScheme v) ≫ closureι v) = closure {v} := by
  have : IsFinite (normalizationStructure (closureScheme v)) :=
    Geometry.NormalizationFiniteArbitraryField.normalizationStructure_isFinite (closureι v ≫ pY)
  have : IsDominant (normalizationStructure (closureScheme v)) :=
    Geometry.NormalizationFinite.normalizationStructure_isDominant
  have hs : Function.Surjective (normalizationStructure (closureScheme v)) :=
    (Surjective.of_universallyClosed_of_isDominant _).surj
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs,
    Set.image_univ, range_closureι]

/-- The normalization of the reduced closure of `v` is a variety over `K`. -/
theorem isVariety_normalization_closure [IsSeparated pY] [LocallyOfFiniteType pY]
    [QuasiCompact pY] (v : Y) :
    IsVariety ((normalizationStructure (closureScheme v) ≫ closureι v) ≫ pY) := by
  have : IsVariety (closureι v ≫ pY) := isVariety_closureι pY v
  have := Geometry.NormalizationFiniteArbitraryField.normalization_isVariety (closureι v ≫ pY)
  rwa [← Category.assoc] at this

end Normalization

section Rational

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **The open set over one normalized component** (blueprint `lem:sm-gso-normalization-open`).
Let `Y` be separated and of finite type over the algebraically closed field `K`, `(q, β, D')` a
family over `Y` as in `StableOpenNbhdConn`, and `σ` a `K`-rational point of `Y` at which the
geometric fibre is numerically stable without contracted clopen subsets. For a point `v` of `Y`
let `ν : N ⟶ Y` be the normalization of the reduced closure of `v`. Assuming the ω step
`StableOpenNbhdRational K`, there is an open `O ⊆ N` containing every point over `σ(*)` such that
`(q, β, D')` is numerically stable over `ν(O)`. -/
theorem exists_open_normalization (hR : StableOpenNbhdRational K) {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) [IsSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    {C : Scheme.{u}} (q : C ⟶ Y) (hq : IsRelativelyProjective pY q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : IsRelativelyProjective (q ≫ pY) β)
    (D' : X.IdealSheafData) (hss : IsSemistablePair (β ≫ q) D')
    (σ : Spec (.of K) ⟶ Y) (hσ : σ ≫ pY = 𝟙 _)
    (hst : NumericallyStableFibre β q D' σ) (hnc : NoContractedClopen β q σ) (v : Y) :
    ∃ O : (normalization (closureScheme v)).Opens,
      (∀ w, (normalizationStructure (closureScheme v) ≫ closureι v) w =
        σ (IsLocalRing.closedPoint K) → w ∈ O) ∧
      ∀ w ∈ O, IsNumericallyStableAt β q D'
        ((normalizationStructure (closureScheme v) ≫ closureι v) w) := by
  set N := normalization (closureScheme v)
  set ν : N ⟶ Y := normalizationStructure (closureScheme v) ≫ closureι v with hν
  set y₀ := σ (IsLocalRing.closedPoint K)
  have : IsProper q := hq.isProper
  have : IsProper β := hβ.isProper
  have : IsFinite ν := isFinite_normalization_closure pY v
  have hvar : IsVariety (ν ≫ pY) := isVariety_normalization_closure pY v
  have hnorm : IsNormalScheme N := normalization_isNormalScheme _
  -- the family over `N`
  have hqN : IsRelativelyProjective (ν ≫ pY) (pullback.snd q ν) := hq.pullback_snd ν
  have hβN : IsRelativelyProjective (pullback.snd q ν ≫ ν ≫ pY) (pullbackCompMap β q ν) :=
    isRelativelyProjective_pullbackCompMap hβ ν
  have hssN : IsSemistablePair (pullbackCompMap β q ν ≫ pullback.snd q ν)
      (D'.comap (pullback.fst (β ≫ q) ν)) := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hss ν
  -- the largest open of `N` over which `(q, β, D')` is numerically stable
  let P : N → Prop := fun w ↦ IsNumericallyStableAt β q D' (ν w)
  let O : N.Opens := ⟨{w | ∃ O' : N.Opens, w ∈ O' ∧ ∀ w' ∈ O', P w'},
    isOpen_iff_forall_mem_open.mpr fun w ⟨O', hw, hO'⟩ ↦
      ⟨O', fun w'' hw'' ↦ ⟨O', hw'', hO'⟩, O'.isOpen, hw⟩⟩
  refine ⟨O, fun w hw ↦ ?_, fun w ⟨O', hw, hO'⟩ ↦ hO' w hw⟩
  -- `w` is a closed point
  have : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace (ν ≫ pY)
  have hy₀ : IsClosed ({y₀} : Set Y) := ((pointEquivClosedPoint pY) ⟨σ, hσ⟩).2
  have hwc : IsClosed ({w} : Set N) := by
    have hfin := ν.finite_preimage_singleton y₀
    have hsub : closure {w} ⊆ ν ⁻¹' {y₀} := by
      intro w' hw'
      have h1 : ν w ⤳ ν w' := (specializes_iff_mem_closure.mpr hw').map ν.continuous
      rw [hw] at h1
      have h2 := specializes_iff_mem_closure.mp h1
      rw [hy₀.closure_eq] at h2
      exact h2
    exact isClosed_singleton_of_finite isClosed_closure (hfin.subset hsub) (subset_closure rfl)
  -- the `K`-point at `w`, lying over `σ`
  let σw := pointOfClosedPoint (ν ≫ pY) w hwc
  have hσw : σw ≫ ν ≫ pY = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hσwpt : σw (IsLocalRing.closedPoint K) = w := pointOfClosedPoint_apply _ _ _ _
  have hσwν : σw ≫ ν = σ := by
    refine ext_of_apply_closedPoint_eq pY (by rw [Category.assoc]; exact hσw) hσ ?_
    change ν (σw (IsLocalRing.closedPoint K)) = _
    rw [hσwpt]
    exact hw
  have hstN : NumericallyStableFibre (pullbackCompMap β q ν) (pullback.snd q ν)
      (D'.comap (pullback.fst (β ≫ q) ν)) σw := by
    rw [numericallyStableFibre_pullback_iff, hσwν]
    exact hst
  have hncN : NoContractedClopen (pullbackCompMap β q ν) (pullback.snd q ν) σw := by
    rw [noContractedClopen_pullback_iff, hσwν]
    exact hnc
  -- the ω step at `σw`
  obtain ⟨Ow, hwOw, hOw⟩ := hR N (ν ≫ pY) hvar hnorm _ (pullback.snd q ν) hqN _
    (pullbackCompMap β q ν) hβN _ hssN σw hσw hstN hncN
  refine ⟨Ow, ?_, fun w' hw' ↦ isNumericallyStableAt_of_pullback ν (hOw w' hw')⟩
  rwa [hσwpt] at hwOw

/-- **The reduction over an algebraically closed field** (blueprint
`prop:sm-gso-rational-finite-type`). Let `Y` be separated and of finite type over the
algebraically closed field `K` (not necessarily integral or normal), `(q, β, D')` a family over
`Y` as in `StableOpenNbhdConn` and `σ` a `K`-rational point of `Y` at which the geometric fibre is
numerically stable without contracted clopen subsets. Assuming the ω step
`StableOpenNbhdRational K`, there is an open neighbourhood of `σ(*)` over which `(q, β, D')` is
numerically stable. -/
theorem exists_open_of_stableOpenNbhdRational (hR : StableOpenNbhdRational K) {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) [IsSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    {C : Scheme.{u}} (q : C ⟶ Y) (hq : IsRelativelyProjective pY q)
    {X : Scheme.{u}} (β : X ⟶ C) (hβ : IsRelativelyProjective (q ≫ pY) β)
    (D' : X.IdealSheafData) (hss : IsSemistablePair (β ≫ q) D')
    (σ : Spec (.of K) ⟶ Y) (hσ : σ ≫ pY = 𝟙 _)
    (hst : NumericallyStableFibre β q D' σ) (hnc : NoContractedClopen β q σ) :
    ∃ O : Y.Opens, σ (IsLocalRing.closedPoint K) ∈ O ∧
      ∀ y ∈ O, IsNumericallyStableAt β q D' y := by
  classical
  set y₀ := σ (IsLocalRing.closedPoint K)
  choose Ov hOv₁ hOv₂ using exists_open_normalization hR pY q hq β hβ D' hss σ hσ hst hnc
  -- `Y` is Noetherian, so it has finitely many irreducible components
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  have : CompactSpace Y := BlowDown.compactSpace_of_quasiCompact pY
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  set G : Set Y := {v | closure {v} ∈ irreducibleComponents Y} with hG
  have hGfin : G.Finite := by
    refine Set.Finite.of_finite_image (f := fun v : Y ↦ closure ({v} : Set Y))
      ((finite_irreducibleComponents_of_isNoetherian (X := Y)).subset ?_) ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact hv
    · intro v _ v' _ h
      exact (inseparable_iff_closure_eq.mpr h).eq
  -- the bad closed sets
  let F : Y → Set Y := fun v ↦
    (normalizationStructure (closureScheme v) ≫ closureι v) '' ((Ov v : Set _)ᶜ)
  have hFcl : ∀ v, IsClosed (F v) := fun v ↦ by
    have : IsFinite (normalizationStructure (closureScheme v) ≫ closureι v) :=
      isFinite_normalization_closure pY v
    exact Scheme.Hom.isClosedMap _ _ (Ov v).isOpen.isClosed_compl
  have hy₀F : ∀ v, y₀ ∉ F v := by
    rintro v ⟨w, hw, hwy⟩
    exact hw (hOv₁ v w hwy)
  have hBad : IsClosed (⋃ v ∈ G, F v) := hGfin.isClosed_biUnion fun v _ ↦ hFcl v
  refine ⟨⟨(⋃ v ∈ G, F v)ᶜ, hBad.isOpen_compl⟩, ?_, fun y hy ↦ ?_⟩
  · change y₀ ∉ ⋃ v ∈ G, F v
    intro h
    obtain ⟨v, -, hvF⟩ := Set.mem_iUnion₂.mp h
    exact hy₀F v hvF
  · have hy' : y ∉ ⋃ v ∈ G, F v := hy
    obtain ⟨T, hT, hyT⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    obtain ⟨v, hv⟩ := QuasiSober.sober hT.1 (isClosed_of_mem_irreducibleComponents T hT)
    have hvT : closure {v} = T := hv
    have hvG : v ∈ G := by
      change closure {v} ∈ irreducibleComponents Y
      rw [hvT]
      exact hT
    have hyv : y ∈ Set.range (normalizationStructure (closureScheme v) ≫ closureι v) := by
      rw [range_normalization_closure pY v, hvT]
      exact hyT rfl
    obtain ⟨w, rfl⟩ := hyv
    by_cases hw : w ∈ Ov v
    · exact hOv₂ v w hw
    · exact absurd (Set.mem_biUnion (t := F) hvG ⟨w, hw, rfl⟩) hy'

end Rational

section Reduction

/-- **Reduction of the corrected spreading statement to the ω step** (blueprint
`thm:sm-gso-reduction`; ERRATA DJA-O36): if `StableOpenNbhdRational K` holds for every
algebraically closed field `K`, then `StableOpenNbhdConn k` holds for every field `k`. The family
is base changed to `U ×_k Spec K` along the field `K` of the given geometric point, which becomes
a `K`-rational point (`exists_open_of_stableOpenNbhdRational`), and the open neighbourhood is
mapped back to `U` by the universally open projection. -/
theorem stableOpenNbhdConn_of_rational (k : Type u) [Field k]
    (hR : ∀ (K : Type u) [Field K] [IsAlgClosed K], StableOpenNbhdRational K) :
    StableOpenNbhdConn k := by
  intro U pU hU C q hq X β hβ D' hss z K _ _ a ha hst hnc
  have : IsProper q := hq.isProper
  have : IsProper β := hβ.isProper
  let κ : CommRingCat.of k ⟶ CommRingCat.of K := Spec.preimage (a ≫ pU)
  have hκ : Spec.map κ = a ≫ pU := Spec.map_preimage _
  let p : pullback pU (Spec.map κ) ⟶ U := pullback.fst pU (Spec.map κ)
  let pK : pullback pU (Spec.map κ) ⟶ Spec (.of K) := pullback.snd pU (Spec.map κ)
  let σ : Spec (.of K) ⟶ pullback pU (Spec.map κ) :=
    pullback.lift a (𝟙 _) (by rw [Category.id_comp, hκ])
  have hσp : σ ≫ p = a := pullback.lift_fst _ _ _
  have hσK : σ ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  have hcond : p ≫ pU = pK ≫ Spec.map (CommRingCat.ofHom κ.hom) := by
    rw [CommRingCat.ofHom_hom]
    exact pullback.condition
  -- the family over `U_K`
  have hqK : IsRelativelyProjective pK (pullback.snd q p) := by
    have h1 := hq.pullback_snd p
    rw [hcond] at h1
    exact (Projectivity.isRelativelyProjective_comp_specMap_iff κ.hom pK _).mp h1
  have hβK : IsRelativelyProjective (pullback.snd q p ≫ pK) (pullbackCompMap β q p) := by
    have h1 := isRelativelyProjective_pullbackCompMap hβ p
    rw [hcond, ← Category.assoc] at h1
    exact (Projectivity.isRelativelyProjective_comp_specMap_iff κ.hom _ _).mp h1
  have hssK : IsSemistablePair (pullbackCompMap β q p ≫ pullback.snd q p)
      (D'.comap (pullback.fst (β ≫ q) p)) := by
    rw [Curves.pullbackCompMap_snd]
    exact Curves.IsSemistablePair.pullback hss p
  have hstK : NumericallyStableFibre (pullbackCompMap β q p) (pullback.snd q p)
      (D'.comap (pullback.fst (β ≫ q) p)) σ := by
    rw [numericallyStableFibre_pullback_iff, hσp]
    exact hst
  have hncK : NoContractedClopen (pullbackCompMap β q p) (pullback.snd q p) σ := by
    rw [noContractedClopen_pullback_iff, hσp]
    exact hnc
  obtain ⟨OK, hσOK, hOK⟩ := exists_open_of_stableOpenNbhdRational (hR K) pK (pullback.snd q p)
    hqK (pullbackCompMap β q p) hβK _ hssK σ hσK hstK hncK
  -- the image of `OK` in `U`
  have : UniversallyOpen p := inferInstance
  refine ⟨⟨p '' (OK : Set _), p.isOpenMap _ OK.isOpen⟩,
    ⟨σ (IsLocalRing.closedPoint K), hσOK, ?_⟩, ?_⟩
  · have h := ha (IsLocalRing.closedPoint K)
    rw [← hσp] at h
    exact h
  · rintro _ ⟨u, hu, rfl⟩
    exact isNumericallyStableAt_of_pullback p (hOK u hu)

end Reduction

end DeJongAlterations.StableModification.Global
