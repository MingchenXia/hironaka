import DeJongAlterations.StableModification.Resolution.GlobalFinal
import DeJongAlterations.StableModification.Resolution.Local

/-!
# Local inputs of the initial charts: completion, the singular locus, sections

Auxiliary results for the formal charts of a nodal curve `g : C → Y` at the closed points of `C`
(de Jong 1996, 3.3–3.5, 4.23–4.25, `references/dejong96-alterations/tex/page-0013.tex`–`page-0015.tex`,
`page-0026.tex`; blueprint chapter `sm-dj-resolution-global.tex`, `lem:sm-dj-initial-charts`):

* `ringKrullDim_completion_eq`: `dim Ô = dim O` for a Noetherian local ring (Matsumura 13.B);
* `stalkIdeal_fitting_eq_top_of_fiberSmooth`: the first Fitting ideal of `Ω_{C/Y}` (the
  singular-locus ideal `N`) is trivial at points whose fibre point is smooth;
* `ker_stalkMap_of_isClosedImmersion`, `localIdeal_rangeCloseds`: the ideal of the image of a
  closed immersion (a section) at `τ(y)` is the kernel of the stalk map;
* `section_coordinate`: if `Ô_{C,x} ≅ Ô_{Y,g x}[[w]]` carries the kernel of the completed
  retraction of a section to `(w)` (lane END-LOC, `exists_local_model`), then the ideal of the
  section extends to `(w)` and is generated, up to a unit of `Ô_{C,x}`, by one element of `𝒪_{C,x}`
  (`exists_unit_of_sub_X_mem_sq`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf
open Algebra.CompletionRegularityBasics
open DeJong (IsNodalCurve IsSmoothAt)

universe u

section Completion

/-- **Completion preserves the Krull dimension** of a Noetherian local ring (the closed fibre of
`R → R̂` is a field; Matsumura 13.B, Theorem 19). -/
theorem ringKrullDim_completion_eq (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  refine le_antisymm ?_ (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion R)
  let Rh := AdicCompletion (maximalIdeal R) R
  let P : Ideal Rh := maximalIdeal Rh
  have : P.LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R Rh)).symm⟩
  have hfl : Module.Flat R Rh := by
    have := faithfullyFlat R
    infer_instance
  have hP := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) P
  have hmap : (maximalIdeal R).map (algebraMap R Rh) = P :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have h0 : (P.map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R Rh)))).height = 0 := by
    rw [hmap, Ideal.map_quotient_self]
    have : IsField (Rh ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp inferInstance
    let := this.toField
    exact Ideal.height_eq_zero_iff_eq_bot.mpr rfl
  rw [h0, add_zero] at hP
  rw [← maximalIdeal_height_eq_ringKrullDim (R := R),
    ← maximalIdeal_height_eq_ringKrullDim (R := Rh)]
  exact_mod_cast hP.le

end Completion

section Fitting

variable {C Y : Scheme.{u}} (g : C ⟶ Y)

/-- **The singular-locus ideal is trivial at fibre-smooth points.** If the fibre point of `x` is a
smooth point of the fibre of the nodal curve `g` (with algebraically closed residue field), then
the first Fitting ideal of `Ω_{C/Y}` is trivial at `x` (compare `not_mem_fittingSupport_of_mem_smoothLocus`
of lane END-LOC, which assumes `g` smooth at `x`). -/
theorem stalkIdeal_fitting_eq_top_of_fiberSmooth [IsNodalCurve g] (x : C)
    [IsAlgClosed (Y.residueField (g x))]
    (hsm : Geometry.NodeCompletedLocalMap.originalFiberPoint g x ∈
      (g.fiberToSpecResidueField (g x)).smoothLocus) :
    stalkIdeal (Algebra.NodeFittingOmegaGluing.idealSheaf g 1) x = ⊤ := by
  by_contra hne
  have hxs : x ∈ (Algebra.NodeFittingOmegaGluing.idealSheaf g 1).support :=
    (mem_support_iff_stalkIdeal_ne_top _ x).mpr hne
  let K := Y.residueField (g x)
  let a := Geometry.NodeCompletedLocalGeometricChart.originalFieldMap (g x) K
  have ha : a = Y.fromSpecResidueField (g x) := by
    change Spec.map (𝟙 _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  let e := pullback.congrHom (rfl : g = g) ha
  let w : g.fiber (g x) := Geometry.NodeCompletedLocalMap.originalFiberPoint g x
  let z := e.inv w
  have hfst : e.inv ≫ pullback.fst g a = pullback.fst g (Y.fromSpecResidueField (g x)) := by
    rw [pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]
  have hsnd : e.hom ≫ pullback.snd g (Y.fromSpecResidueField (g x)) = pullback.snd g a := by
    rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have hz1 : pullback.fst g a z = x := by
    change (e.inv ≫ pullback.fst g a) _ = x
    rw [hfst]
    exact Geometry.NodeCompletedLocalMap.originalFiberPoint_source g x
  have hzs' : z ∈ (e.hom ≫ pullback.snd g (Y.fromSpecResidueField (g x))).smoothLocus := by
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    change e.hom (e.inv w) ∈ (pullback.snd g (Y.fromSpecResidueField (g x))).smoothLocus
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    exact hsm
  have hzs : z ∈ (pullback.snd g a).smoothLocus := by
    convert hzs' using 2 <;> first | rfl | exact hsnd.symm
  exact Algebra.NodeFittingGeometricIdealSheaf.not_mem_originalPullback_support_of_mem_smoothLocus
    g (g x) K (geometricFiber_dimension_le_one g K a) z hzs
    (Algebra.NodeFittingSupportPullback.mem_comap_support_of_mem_support _ _ z
      (by rw [hz1]; exact hxs))

end Fitting

section PowerSeriesUnit

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The ideal of power series whose constant and linear coefficients lie in `𝔪_A`. -/
def lowCoeffIdeal : Ideal (PowerSeries A) where
  carrier := {F | PowerSeries.coeff 0 F ∈ maximalIdeal A ∧ PowerSeries.coeff 1 F ∈ maximalIdeal A}
  add_mem' := by
    rintro F G ⟨hF0, hF1⟩ ⟨hG0, hG1⟩
    exact ⟨by rw [map_add]; exact Ideal.add_mem _ hF0 hG0,
      by rw [map_add]; exact Ideal.add_mem _ hF1 hG1⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro r F ⟨hF0, hF1⟩
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact Ideal.mul_mem_left _ _ hF0
    · rw [smul_eq_mul, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hF1) (Ideal.mul_mem_left _ _ hF0)

/-- Squares of the maximal ideal of `A[[X]]` have linear coefficient in `𝔪_A`. -/
theorem sq_maximalIdeal_powerSeries_le : maximalIdeal (PowerSeries A) ^ 2 ≤ lowCoeffIdeal := by
  have hm : ∀ F ∈ maximalIdeal (PowerSeries A), PowerSeries.coeff 0 F ∈ maximalIdeal A := by
    intro F hF
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    intro hu
    exact hF (PowerSeries.isUnit_iff_constantCoeff.mpr hu)
  rw [pow_two, Ideal.mul_le]
  intro F hF G hG
  refine ⟨?_, ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Ideal.mul_mem_right _ _ (hm F hF)
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hm F hF)) (Ideal.mul_mem_left _ _ (hm G hG))

/-- **A power series congruent to `X` modulo `𝔪²`**: `F - C(F₀) = X G` with `G` a unit. -/
theorem exists_unit_of_sub_X_mem_sq {F : PowerSeries A}
    (hF : F - PowerSeries.X ∈ maximalIdeal (PowerSeries A) ^ 2) :
    ∃ G : PowerSeries A, IsUnit G ∧
      F - PowerSeries.C (PowerSeries.constantCoeff F) = PowerSeries.X * G := by
  refine ⟨PowerSeries.mk fun p ↦ PowerSeries.coeff (p + 1) F, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk, zero_add]
    have h1 := (sq_maximalIdeal_powerSeries_le hF).2
    rw [map_sub, PowerSeries.coeff_X, if_pos rfl] at h1
    by_contra hnu
    have : PowerSeries.coeff 1 F ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hnu
    have := Ideal.sub_mem _ this h1
    rw [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · ext p
    rcases p with _ | p
    · simp
    · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero p), sub_zero,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

end PowerSeriesUnit

section Sections

variable {X Y : Scheme.{u}}

/-- The kernel of the stalk map of a closed immersion is the stalk of its ideal sheaf (adapted
from Codex's `Algebra.NodeFittingIdealSheaf.ker_stalkMap_subschemeι`). -/
theorem ker_stalkMap_of_isClosedImmersion (τ : Y ⟶ X) [IsClosedImmersion τ] (y : Y) :
    RingHom.ker (τ.stalkMap y).hom = stalkIdeal τ.ker (τ y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (τ y)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have hV : IsAffineOpen (τ ⁻¹ᵁ U) := hU.preimage τ
  have hzV : y ∈ τ ⁻¹ᵁ U := hxU
  let := X.presheaf.algebra_section_stalk ⟨τ y, hxU⟩
  let := Y.presheaf.algebra_section_stalk ⟨y, hzV⟩
  have hlocX := hU.isLocalization_stalk ⟨τ y, hxU⟩
  have hlocZ := hV.isLocalization_stalk ⟨y, hzV⟩
  set p := (hU.primeIdealOf ⟨τ y, hxU⟩).asIdeal with hp
  set q := (hV.primeIdealOf ⟨y, hzV⟩).asIdeal with hq
  set g := (τ.app U).hom with hg
  have hgs : Function.Surjective g := τ.app_surjective U hU
  have hker : RingHom.ker g = τ.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply τ ⟨U, hU⟩).symm
  have hcomap : q.comap g = p := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU (τ ⁻¹ᵁ U) hV le_rfl hzV
    have h' := congrArg PrimeSpectrum.asIdeal h
    rw [PrimeSpectrum.comap_asIdeal] at h'
    rw [hg, Scheme.Hom.app_eq_appLE]
    exact h'
  have hT : Submonoid.map g p.primeCompl = q.primeCompl := by
    have h := Ideal.map_primeCompl_comap_of_surjective g hgs q
    convert h using 3
    exact hcomap.symm
  have hmap : (τ.stalkMap y).hom =
      IsLocalization.map (Y.presheaf.stalk y) g (hT.symm ▸ p.primeCompl.le_comap_map) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact τ.germ_stalkMap_apply U y hxU s
  rw [hmap, IsLocalization.ker_map (Q := Y.presheaf.stalk y) (g := g) (M := p.primeCompl)
    (T := q.primeCompl) hT, hker, stalkIdeal_eq_map_germ τ.ker ⟨U, hU⟩ hxU]
  rfl

/-- The closed subset `τ(Y)` of a closed immersion. -/
def rangeCloseds (τ : Y ⟶ X) [IsClosedImmersion τ] : Closeds X :=
  ⟨Set.range τ, τ.isClosedEmbedding.isClosed_range⟩

/-- **The vanishing ideal of the image of a closed immersion with integral source** is, at a
point `τ y`, the kernel of the stalk map. -/
theorem localIdeal_rangeCloseds (τ : Y ⟶ X) [IsClosedImmersion τ] [IsIntegral Y] (y : Y) :
    localIdeal (rangeCloseds τ) (τ y) = RingHom.ker (τ.stalkMap y).hom := by
  have hsupp : τ.ker.support = rangeCloseds τ := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, τ.isClosedEmbedding.isClosed_range.closure_eq]
    rfl
  rw [localIdeal, ← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, stalkIdeal_radical,
    ← ker_stalkMap_of_isClosedImmersion]
  exact (RingHom.ker_isPrime _).isRadical.radical

end Sections

section SectionCoordinate

open Geometry.NodeCompletedLocalMap

attribute [local instance] completedAlgebra

variable {C Y : Scheme.{u}} (g : C ⟶ Y) [LocallyOfFiniteType g] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian C]

/-- **The formal coordinate of a section.** Let `ρ` be a retraction of `g^♯ : 𝒪_{Y,g x} → 𝒪_{C,x}`
and `φ : Ô_{C,x} ≃ Ô_{Y,g x}[[X]]` carry the kernel of the completed retraction onto `(X)` (lane
END-LOC). Then the kernel of `ρ` extends to `(φ⁻¹ X)`, and is generated, up to a unit in the
completion, by one element of `ker ρ`. -/
theorem section_coordinate (x : C) (ρ : C.presheaf.stalk x →+* Y.presheaf.stalk (g x))
    (hρ : ∀ a, ρ (g.stalkMap x a) = a)
    (φ : C.completedLocalRing x ≃ₐ[Y.completedLocalRing (g x)]
      PowerSeries (Y.completedLocalRing (g x)))
    (hφ : (RingHom.ker (completedRetraction g x ρ hρ).toRingHom).map φ =
      Ideal.span {PowerSeries.X}) :
    (RingHom.ker ρ).map (C.toCompletedLocalRing x) = Ideal.span {φ.symm PowerSeries.X} ∧
      ∃ s ∈ RingHom.ker ρ, Ideal.span {C.toCompletedLocalRing x s} =
        Ideal.span {φ.symm PowerSeries.X} := by
  classical
  set Φ := completedRetraction g x ρ hρ
  set w : C.completedLocalRing x := φ.symm PowerSeries.X
  have : IsLocalHom ρ := IsLocalHom.of_surjective ρ (fun a ↦ ⟨g.stalkMap x a, hρ a⟩)
  have hΦ : ∀ o, Φ (C.toCompletedLocalRing x o) = Y.toCompletedLocalRing (g x) (ρ o) :=
    fun o ↦ Algebra.CompletionLocalMap.completionMap_algebraMap ρ o
  have hkerΦ : RingHom.ker Φ.toRingHom = Ideal.span {w} := by
    have h1 : RingHom.ker Φ.toRingHom =
        (Ideal.span {PowerSeries.X}).comap φ.toRingEquiv.toRingHom := by
      rw [← hφ]
      exact (Ideal.comap_map_of_bijective _ φ.bijective).symm
    rw [h1]
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      apply φ.injective
      change φ (φ.symm c * φ.symm PowerSeries.X) = φ z
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hc
    · rintro ⟨c, rfl⟩
      refine ⟨φ c, ?_⟩
      change φ c * PowerSeries.X = φ (c * φ.symm PowerSeries.X)
      rw [map_mul, AlgEquiv.apply_symm_apply]
  have hwker : Φ w = 0 := by
    have : w ∈ RingHom.ker Φ.toRingHom := hkerΦ ▸ Ideal.mem_span_singleton_self w
    exact this
  have hΦconst : ∀ z, Φ z = PowerSeries.constantCoeff (φ z) := by
    intro z
    have hz := PowerSeries.eq_X_mul_shift_add_const (φ z)
    have := congrArg (fun F ↦ Φ (φ.symm F)) hz
    simp only [AlgEquiv.symm_apply_apply, map_add, map_mul] at this
    have hC : φ.symm (PowerSeries.C (PowerSeries.constantCoeff (φ z))) =
        algebraMap (Y.completedLocalRing (g x)) (C.completedLocalRing x)
          (PowerSeries.constantCoeff (φ z)) := by
      rw [← AlgEquiv.commutes φ.symm]
      rfl
    rw [hC, AlgHom.commutes] at this
    rw [this, show Φ (φ.symm PowerSeries.X) = 0 from hwker, zero_mul, zero_add]
    rfl
  -- a lift of `w` modulo `𝔪²`
  have hwm : w ∈ maximalIdeal (C.completedLocalRing x) := by
    by_contra hnu
    have hu : IsUnit w := by
      by_contra h; exact hnu ((mem_maximalIdeal _).mpr h)
    exact (hu.map Φ).ne_zero hwker
  have hmax : maximalIdeal (C.completedLocalRing x) =
      (maximalIdeal (C.presheaf.stalk x)).map (C.toCompletedLocalRing x) :=
    AdicCompletion.maximalIdeal_eq_map
  rw [hmax] at hwm
  obtain ⟨n, c, a, ha, hw⟩ := exists_sum_of_mem_map _ hwm
  have hd : ∀ i, ∃ d : C.presheaf.stalk x,
      c i - C.toCompletedLocalRing x d ∈ maximalIdeal (C.completedLocalRing x) := by
    intro i
    obtain ⟨r, hr⟩ := (residueField_map_bijective (C.presheaf.stalk x)).2
      (residue (C.completedLocalRing x) (c i))
    obtain ⟨d, rfl⟩ := residue_surjective r
    refine ⟨d, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hr, ResidueField.map_residue]
    rfl
  choose d hd using hd
  set f : C.presheaf.stalk x := ∑ i, a i * d i
  have hfw : C.toCompletedLocalRing x f - w ∈ maximalIdeal (C.completedLocalRing x) ^ 2 := by
    have : C.toCompletedLocalRing x f - w =
        ∑ i, C.toCompletedLocalRing x (a i) * (C.toCompletedLocalRing x (d i) - c i) := by
      rw [hw, map_sum]
      simp only [map_mul, Algebra.smul_def, mul_sub, Finset.sum_sub_distrib]
      rfl
    rw [this, pow_two]
    refine sum_mem fun i _ ↦ Ideal.mul_mem_mul ?_ ?_
    · rw [hmax]; exact Ideal.mem_map_of_mem _ (ha i)
    · rw [← neg_sub]; exact neg_mem (hd i)
  -- the element of the kernel
  set s : C.presheaf.stalk x := f - g.stalkMap x (ρ f)
  have hs : s ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, hρ, sub_self]
  set F := φ (C.toCompletedLocalRing x f)
  have hφs : φ (C.toCompletedLocalRing x s) = F - PowerSeries.C (PowerSeries.constantCoeff F) := by
    rw [map_sub, map_sub, ← completedMap_coefficient]
    congr 1
    change φ (algebraMap (Y.completedLocalRing (g x)) (C.completedLocalRing x)
      (Y.toCompletedLocalRing (g x) (ρ f))) = _
    rw [AlgEquiv.commutes, ← hΦ, hΦconst]
    rfl
  have hFX : F - PowerSeries.X ∈ maximalIdeal (PowerSeries (Y.completedLocalRing (g x))) ^ 2 := by
    have h1 : F - PowerSeries.X = φ (C.toCompletedLocalRing x f - w) := by
      rw [map_sub, AlgEquiv.apply_symm_apply]
    rw [h1, ← IsLocalRing.map_ringEquiv_maximalIdeal φ.toRingEquiv, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hfw
  obtain ⟨G, hG, hFG⟩ := exists_unit_of_sub_X_mem_sq hFX
  have hspan : Ideal.span {C.toCompletedLocalRing x s} = Ideal.span {w} := by
    have : C.toCompletedLocalRing x s = w * φ.symm G := by
      apply φ.injective
      rw [hφs, hFG, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [this]
    exact Ideal.span_singleton_mul_right_unit (hG.map φ.symm) w
  refine ⟨le_antisymm ?_ ?_, s, hs, hspan⟩
  · rw [← hkerΦ, Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Φ (C.toCompletedLocalRing x k) = 0
    rw [hΦ, RingHom.mem_ker.mp hk, map_zero]
  · rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hs

end SectionCoordinate

end DeJongAlterations.StableModification.Resolution.Global
