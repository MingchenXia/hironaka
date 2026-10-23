/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalReduced
import DeJongAlterations.StableModification.BlowDown.ExcSpecialize
import DeJongAlterations.StableModification.BlowDown.ContractionDimension
import DeJongAlterations.StableModification.BlowDown.StabilityCriterion

/-!
# The étale-local part of the closure-component lemma

This file proves `ExcSpecialize.ClosureComponentLocal` (`closureComponentLocal`), the named
hypothesis of lanes T44A3–T44E: the étale-local part of Temkin's closure-component lemma (M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, proof of Lemma 4.4.4,
T:3164–3166; blueprint `lem:sm-bd-closure-component`(2)–(3), `def:sm-bde-closure-local-hyp`).

Let `V` be a valuation ring with finitely many primes and all `Frac(V/𝔭)` separably closed,
`(q : X → Spec V, D')` a proper semi-stable pair, `t ∈ Spec V`, `ζ` a generic point of the fibre
`X_t` with image `z ∈ X`, `W = V ⧸ 𝔭_t` and `X_W = X ×_V Spec W` (a nodal curve over the
integrally closed local domain `W`, in which `z` is a generic point, `exists_isGeneric_baseChange`).

* **Reducedness** (`isReduced_fibreAt_closedPoint`): the closure `Ȳ` of `z` is a reduced closed
  subscheme of `X_W` with support the closure of `z`, so its closed fibre is reduced by
  `ClosureLocal.isReduced_closedFibre_of_isClosedImmersion`; the residue field of `W` is
  `κ(s₀)` (`residueFieldEquiv`).
* **Boundary points** (`exists_boundary_image`): a double point `y` of `X_{s₀}` on `Ȳ` with a
  branch on a component of `X_{s₀}` off `Ȳ` gives, by `ClosureLocal.exists_node` in `X_W`, a point
  `n` of `X_t` on `closure {ζ}` specializing to `y` and lying on a second component of `X_t`;
  `n` is not a smooth point of `X_t` (`ClosureLocal.eq_of_isSmoothAt`), it is not a generic point,
  hence closed in the curve `X_t` and algebraic over `κ(t)`.
* **Marks** (`exists_mark_image`): a point `y` of `D'` on `Ȳ` over `s₀` has a generization `d` on
  `D'` over `t` (`D' → Spec V` is flat); `y` is a smooth point, so `d` lies on the closure of `z`
  (`ClosureLocal.eq_of_isSmoothAt` in `X_W`), and `d` is algebraic over `κ(t)` (`D'` is étale).
* **The count**: points algebraic over `κ(t)` have closures meeting the closed fibre in one point
  (`ExcSpecialize.eq_of_mem_closure_of_isAlgebraicAt`), so `y ↦ n`, `y ↦ d` are injective, with
  disjoint images (double points are not smooth, marks are).

Blueprint: `sm-blow-down-closure-local.tex`, `thm:sm-bdcl-closure-local`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Topology

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open ClosureComponent ExcSpecialize ValCurves

section Topology

variable {T : Type*} [TopologicalSpace T] [QuasiSober T] [T0Space T]

/-- **Every point is a specialization of a generic point** (the generic point of an irreducible
component through it). -/
theorem exists_isGeneric_specializes (x : T) : ∃ η : T, (∀ ξ, ξ ⤳ η → ξ = η) ∧ η ⤳ x := by
  have hC := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
  refine ⟨η, (CurvesField.Genus.mem_genericPoints_iff η).mp ?_, ?_⟩
  · change closure {η} ∈ irreducibleComponents T
    rw [hη.def]
    exact hC
  · rw [specializes_iff_mem_closure, hη.def]
    exact mem_irreducibleComponent

end Topology

section BaseChange

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of V)) (z : X)

/-- The closed point of `W = V ⧸ 𝔭` lies over the closed point of `V`. -/
theorem baseι_closedPoint : baseι q z (closedPoint (BaseRing q z)) = closedPoint V := by
  apply PrimeSpectrum.ext
  change (maximalIdeal (BaseRing q z)).comap (Ideal.Quotient.mk (basePrime q z)) = maximalIdeal V
  have : ((maximalIdeal (BaseRing q z)).comap (Ideal.Quotient.mk (basePrime q z))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  exact IsLocalRing.eq_maximalIdeal this

omit [IsDomain V] [ValuationRing V] in
/-- Points of `X_W` over the generic point of `Spec W` are the points over `q z`. -/
theorem snd_eq_bot_iff (x : pullback (C := Scheme.{u}) q (baseι q z)) :
    pullback.snd q (baseι q z) x = (⊥ : PrimeSpectrum (BaseRing q z)) ↔
      q (pullback.fst q (baseι q z) x) = q z := by
  rw [← baseι_bot q z, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact (baseι_injective q z).eq_iff.symm

omit [IsDomain V] [ValuationRing V] in
/-- A generization of a point of `X_W` over the generic point lies over the generic point. -/
theorem snd_eq_bot_of_specializes {x x' : pullback (C := Scheme.{u}) q (baseι q z)} (h : x' ⤳ x)
    (hx : pullback.snd q (baseι q z) x = (⊥ : PrimeSpectrum (BaseRing q z))) :
    pullback.snd q (baseι q z) x' = (⊥ : PrimeSpectrum (BaseRing q z)) := by
  have h' := (PrimeSpectrum.le_iff_specializes _ _).mpr
    (h.map (pullback.snd q (baseι q z)).continuous)
  rw [hx] at h'
  exact PrimeSpectrum.ext (le_bot_iff.mp h')

omit [IsDomain V] [ValuationRing V] in
/-- **`z` is a generic point of `X_W`** if it is maximal in its fibre `q⁻¹(q z)`. -/
theorem exists_isGeneric_baseChange (hz : ∀ x, x ⤳ z → q x = q z → x = z) :
    ∃ zY : pullback (C := Scheme.{u}) q (baseι q z), pullback.fst q (baseι q z) zY = z ∧
      pullback.snd q (baseι q z) zY = (⊥ : PrimeSpectrum (BaseRing q z)) ∧
        ∀ ξ, ξ ⤳ zY → ξ = zY := by
  obtain ⟨zY, hzY, hzYg⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z) z
    (⊥ : PrimeSpectrum (BaseRing q z)) (baseι_bot q z).symm
  refine ⟨zY, hzY, hzYg, fun ξ hξ => ?_⟩
  have hξg := snd_eq_bot_of_specializes q z hξ hzYg
  rw [snd_eq_bot_iff] at hξg
  have h1 : pullback.fst q (baseι q z) ξ ⤳ z :=
    (hξ.map (pullback.fst q (baseι q z)).continuous).trans (specializes_of_eq hzY)
  have h2 := hz _ h1 hξg
  exact (pullback.fst q (baseι q z)).isClosedEmbedding.injective (h2.trans hzY.symm)

end BaseChange

section Reduced

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of V)) (z : X)

/-- The field point `W → κ(s₀)` is surjective. -/
theorem fieldPt_surjective :
    Function.Surjective (fieldPt q z (ExcSpecialize.specializes_closedPoint (q z))) := by
  intro c
  have : (closedPoint V).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal V
  obtain ⟨v, rfl⟩ := Ideal.algebraMap_residueField_surjective (closedPoint V).asIdeal c
  exact ⟨Ideal.Quotient.mk _ v, rfl⟩

/-- **The residue field of `W = V ⧸ 𝔭` is `κ(s₀)`**, compatibly with `fieldPt`. -/
def residueFieldEquiv : ResidueField (BaseRing q z) ≃+* (closedPoint V).asIdeal.ResidueField :=
  (Ideal.quotEquivOfEq (IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fieldPt_surjective q z))).symm).trans
    (RingHom.quotientKerEquivOfSurjective (fieldPt_surjective q z))

theorem residueFieldEquiv_residue (w : BaseRing q z) :
    residueFieldEquiv q z (residue (BaseRing q z) w) =
      fieldPt q z (ExcSpecialize.specializes_closedPoint (q z)) w :=
  rfl

/-- `Spec κ(s₀) → Spec W` is the closed point of `Spec W` up to `residueFieldEquiv`. -/
theorem specMap_residueFieldEquiv_comp :
    Spec.map (CommRingCat.ofHom (residueFieldEquiv q z).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (residue (BaseRing q z))) =
      Spec.map (CommRingCat.ofHom (fieldPt q z (ExcSpecialize.specializes_closedPoint (q z)))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

variable [CompactSpace X]

/-- **The closed fibre of the closure of `z` is reduced** (blueprint `thm:sm-bdcl-closure-local`
(1); `ClosureComponentLocal`(1)): for a nodal `q` and `z` maximal in its fibre `q⁻¹(q z)`, the
fibre `Ȳ ×_W κ(s₀)` of the reduced closure `Ȳ` of `z` over `W = V ⧸ 𝔭_{q z}` is reduced. -/
theorem isReduced_fibreAt_closedPoint [DeJong.IsNodalCurve q]
    (hz : ∀ x, x ⤳ z → q x = q z → x = z) :
    IsReduced (fibreAt q z (ExcSpecialize.specializes_closedPoint (q z))) := by
  obtain ⟨zY, hzY, -, hzYgen⟩ := exists_isGeneric_baseChange q z hz
  set j := pullback.fst q (baseι q z)
  set g := pullback.snd q (baseι q z)
  let i : closureScheme z ⟶ pullback (C := Scheme.{u}) q (baseι q z) :=
    pullback.lift (closureι z) (closureToBase q z) (closureToBase_baseι q z).symm
  have hij : i ≫ j = closureι z := pullback.lift_fst _ _ _
  have hig : i ≫ g = closureToBase q z := pullback.lift_snd _ _ _
  have : IsClosedImmersion (i ≫ j) := by rw [hij]; infer_instance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i j
  have hrange : Set.range i = closure {zY} := by
    have h1 : j '' Set.range i = closure {z} := by
      rw [← range_closureι z, ← hij, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have h2 : closure {zY} = j ⁻¹' closure {z} := by
      rw [j.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
        hzY]
    rw [h2, ← h1, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
  have h := isReduced_closedFibre_of_isClosedImmersion g hzYgen i hrange
  rw [hig] at h
  exact BlowDown.isReduced_pullback_of_iso (closureToBase q z) _ _
    (Scheme.Spec.mapIso (residueFieldEquiv q z).toCommRingCatIso.op)
    (specMap_residueFieldEquiv_comp q z)

end Reduced

section Dimension

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of V))

/-- **The residue-field fibres of a nodal curve have dimension at most one** (from the fibres
`q.fiber t`, `pure_fiber_of_nodal`, along `Spec κ(t) ≅ Spec (Spec V).residueField t`). -/
theorem topologicalKrullDim_residuePt_le_one [DeJong.IsNodalCurve q] [QuasiCompact q]
    (t : PrimeSpectrum V) :
    topologicalKrullDim (pullback (C := Scheme.{u}) q (residuePt t)) ≤ 1 := by
  obtain ⟨φ, ⟨e⟩⟩ := Limits.Spread.exists_pullback_iso_fiber q (residuePt t)
  refine BlowDown.topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW => ?_
  exact (Limits.Spread.pure_of_homeomorph e.schemeIsoToHomeo
    (Limits.Spread.pure_pullback _ (Spec.map φ) (pure_fiber_of_nodal q _)) W hW).le

end Dimension

section Count

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of V)) {t : PrimeSpectrum V}
  (ζ : pullback (C := Scheme.{u}) q (residuePt t))

omit [IsDomain V] [ValuationRing V] in
/-- The image `z ∈ X` of a generic point `ζ` of `X_t` is maximal in its fibre `q⁻¹(t)`. -/
theorem isGeneric_fst_residuePt (hζ : ∀ ξ, ξ ⤳ ζ → ξ = ζ) :
    ∀ x, x ⤳ pullback.fst q (residuePt t) ζ → q x = q (pullback.fst q (residuePt t) ζ) →
      x = pullback.fst q (residuePt t) ζ := by
  intro x hx hqx
  rw [apply_fst_residuePt q ζ] at hqx
  obtain ⟨ξ, rfl⟩ : x ∈ Set.range (pullback.fst q (residuePt t)) := by
    rw [range_fst_residuePt]
    exact hqx
  rw [hζ ξ ((isEmbedding_fst_residuePt q t).isInducing.specializes_iff.mp hx)]

omit [IsDomain V] [ValuationRing V] in
/-- **Generic points of `X_W` over `t` are generic points of `X_t`.** -/
theorem isGeneric_of_isGeneric_baseChange (z : X) (hzt : q z = t)
    {w : pullback (C := Scheme.{u}) q (baseι q z)} (hw : ∀ ξ, ξ ⤳ w → ξ = w)
    {ω : pullback (C := Scheme.{u}) q (residuePt t)}
    (hω : pullback.fst q (residuePt t) ω = pullback.fst q (baseι q z) w) :
    ∀ ξ, ξ ⤳ ω → ξ = ω := by
  intro ξ hξ
  obtain ⟨ξY, hξY, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z)
    (pullback.fst q (residuePt t) ξ) (⊥ : PrimeSpectrum (BaseRing q z))
    (by rw [baseι_bot, apply_fst_residuePt q ξ, hzt])
  have h1 : pullback.fst q (baseι q z) ξY ⤳ pullback.fst q (baseι q z) w :=
    (specializes_of_eq hξY).trans
      ((hξ.map (pullback.fst q (residuePt t)).continuous).trans (specializes_of_eq hω))
  have h2 := hw _ ((pullback.fst q (baseι q z)).isClosedEmbedding.isInducing.specializes_iff.mp h1)
  apply (isEmbedding_fst_residuePt q t).injective
  rw [hω, ← h2, hξY]

variable [IsProper q] [DeJong.IsNodalCurve q]

/-- **The image of a boundary point** (blueprint `thm:sm-bdcl-closure-local`(2), boundary part):
for a point `y` of `∂(Ȳ_{s₀})` (`closedBoundaryPoints`) there is a point `n` of `X_t` on
`closure {ζ}` which is not a smooth point of `X_t`, is algebraic over `κ(t)` and specializes to
`y`. -/
theorem exists_boundary_image (hζ : ∀ ξ, ξ ⤳ ζ → ξ = ζ)
    {y : pullback (C := Scheme.{u}) q (residuePt (closedPoint V))}
    (hy : y ∈ closedBoundaryPoints q (pullback.fst q (residuePt t) ζ)) :
    ∃ n : pullback (C := Scheme.{u}) q (residuePt t), n ∈ closure {ζ} ∧
      ¬ DeJong.IsSmoothAt (pullback.snd q (residuePt t)) n ∧
      IsAlgebraicAt q (pullback.fst q (residuePt t) n) ∧
      pullback.fst q (residuePt (closedPoint V)) y ∈
        closure {pullback.fst q (residuePt t) n} := by
  set z := pullback.fst q (residuePt t) ζ with hz_def
  have hzt : q z = t := apply_fst_residuePt q ζ
  obtain ⟨hyz, -, -, w, -, hwz, hyw⟩ := hy
  obtain ⟨zY, hzY, -, hzYgen⟩ := exists_isGeneric_baseChange q z (isGeneric_fst_residuePt q ζ hζ)
  set j := pullback.fst q (baseι q z)
  set g := pullback.snd q (baseι q z)
  have hjemb := j.isClosedEmbedding.isInducing
  set x := pullback.fst q (residuePt (closedPoint V)) y
  set x' := pullback.fst q (residuePt (closedPoint V)) w
  have hqx : q x = closedPoint V := apply_fst_residuePt q y
  have hqx' : q x' = closedPoint V := apply_fst_residuePt q w
  obtain ⟨xY, hxY, hxYg⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z) x
    (closedPoint (BaseRing q z)) (by rw [hqx, baseι_closedPoint])
  obtain ⟨wY, hwY, hwYg⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z) x'
    (closedPoint (BaseRing q z)) (by rw [hqx', baseι_closedPoint])
  have hzxY : zY ⤳ xY := hjemb.specializes_iff.mp (by
    rw [hzY, hxY]
    exact specializes_iff_mem_closure.mpr hyz)
  have hwxY : wY ⤳ xY := hjemb.specializes_iff.mp (by
    rw [hwY, hxY]
    exact (specializes_iff_mem_closure.mpr hyw).map (pullback.fst q _).continuous)
  have hzwY : ¬ zY ⤳ wY := by
    intro h
    apply hwz
    have h' := h.map j.continuous
    rw [hzY, hwY] at h'
    exact specializes_iff_mem_closure.mp h'
  obtain ⟨nY, hzn, hnx, hnbot, z₂, hz₂gen, hz₂ne, hz₂n⟩ := exists_node g
    (by rw [hxYg]; rfl) hzYgen hzxY (by rw [hwYg]; exact le_rfl) hwxY hzwY
  have hgn : g nY = (⊥ : PrimeSpectrum (BaseRing q z)) := PrimeSpectrum.ext hnbot
  have hqn : q (j nY) = t := by
    rw [← hzt]
    exact (snd_eq_bot_iff q z nY).mp hgn
  have hqz₂ : q (j z₂) = t := by
    rw [← hzt]
    exact (snd_eq_bot_iff q z z₂).mp (snd_eq_bot_of_specializes q z hz₂n hgn)
  obtain ⟨nt, hnt⟩ : j nY ∈ Set.range (pullback.fst q (residuePt t)) := by
    rw [range_fst_residuePt]
    exact hqn
  obtain ⟨ζ₂, hζ₂⟩ : j z₂ ∈ Set.range (pullback.fst q (residuePt t)) := by
    rw [range_fst_residuePt]
    exact hqz₂
  have hembt := (isEmbedding_fst_residuePt q t).isInducing
  have hzn' : z ⤳ j nY := (specializes_of_eq hzY.symm).trans (hzn.map j.continuous)
  have hζn : ζ ⤳ nt := hembt.specializes_iff.mp (by rw [hnt]; exact hzn')
  have hζ₂n : ζ₂ ⤳ nt := hembt.specializes_iff.mp (by
    rw [hnt, hζ₂]
    exact hz₂n.map j.continuous)
  have hζ₂gen := isGeneric_of_isGeneric_baseChange q z hzt hz₂gen hζ₂
  have hne : ζ ≠ ζ₂ := by
    intro h
    apply hz₂ne
    apply j.isClosedEmbedding.injective
    rw [← hζ₂, ← h, hzY]
  have hns : ¬ DeJong.IsSmoothAt (pullback.snd q (residuePt t)) nt := fun hsm =>
    hne (eq_of_isSmoothAt (pullback.snd q (residuePt t)) hsm hζ hζ₂gen hζn hζ₂n)
  have hntg : nt ∉ genericPoints (pullback (C := Scheme.{u}) q (residuePt t)) := by
    intro hg
    have hg' := (CurvesField.Genus.mem_genericPoints_iff nt).mp hg
    exact hne ((hg' ζ hζn).trans (hg' ζ₂ hζ₂n).symm)
  have : CompactSpace (pullback (C := Scheme.{u}) q (residuePt t)) :=
    compactSpace_of_quasiCompact (pullback.snd q (residuePt t))
  have hcl := CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints
    (topologicalKrullDim_residuePt_le_one q t) hntg
  refine ⟨nt, ?_, hns, isAlgebraicAt_of_isClosed q t nt hcl, ?_⟩
  · rw [closure_singleton_eq_preimage q t ζ, Set.mem_preimage, hnt]
    exact specializes_iff_mem_closure.mp hzn'
  · rw [hnt]
    have h := hnx.map j.continuous
    rw [hxY] at h
    exact specializes_iff_mem_closure.mp h

omit [IsProper q] in
/-- **The image of a mark** (blueprint `thm:sm-bdcl-closure-local`(2), mark part): for a point
`y` of `D' ∩ Ȳ_{s₀}` (`closedMarkPoints`) there is a point `d` of `X_t` on `closure {ζ}` and on
`D'`, algebraic over `κ(t)`, specializing to `y`. -/
theorem exists_mark_image (hζ : ∀ ξ, ξ ⤳ ζ → ξ = ζ) {D' : X.IdealSheafData}
    (hpair : DeJong.IsSemistablePair q D')
    {y : pullback (C := Scheme.{u}) q (residuePt (closedPoint V))}
    (hy : y ∈ closedMarkPoints q D' (pullback.fst q (residuePt t) ζ)) :
    ∃ d : pullback (C := Scheme.{u}) q (residuePt t), d ∈ closure {ζ} ∧
      pullback.fst q (residuePt t) d ∈ (D'.support : Set X) ∧
      IsAlgebraicAt q (pullback.fst q (residuePt t) d) ∧
      pullback.fst q (residuePt (closedPoint V)) y ∈
        closure {pullback.fst q (residuePt t) d} := by
  set z := pullback.fst q (residuePt t) ζ with hz_def
  have hzt : q z = t := apply_fst_residuePt q ζ
  obtain ⟨hyz, hyD⟩ := hy
  set x := pullback.fst q (residuePt (closedPoint V)) y
  have hqx : q x = closedPoint V := apply_fst_residuePt q y
  -- a generization of the mark over `t` on `D'`
  obtain ⟨xD, hxD⟩ : x ∈ Set.range D'.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hyD
  have := hpair.etale
  have hts : t ⤳ (D'.subschemeι ≫ q) xD := by
    rw [Scheme.Hom.comp_apply, hxD, hqx]
    exact ExcSpecialize.specializes_closedPoint t
  obtain ⟨dD, hdx, hdt⟩ := Flat.generalizingMap (D'.subschemeι ≫ q) hts
  set d := D'.subschemeι dD
  have hqd : q d = t := by
    rw [Scheme.Hom.comp_apply] at hdt
    exact hdt
  have hdD : d ∈ (D'.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨dD, rfl⟩
  have hdx' : d ⤳ x := by
    have h := hdx.map D'.subschemeι.continuous
    rw [hxD] at h
    exact h
  -- `d` lies on the closure of `z`: `x` is a smooth point of `X_W`
  obtain ⟨zY, hzY, -, hzYgen⟩ := exists_isGeneric_baseChange q z (isGeneric_fst_residuePt q ζ hζ)
  set j := pullback.fst q (baseι q z)
  set g := pullback.snd q (baseι q z)
  have hjemb := j.isClosedEmbedding.isInducing
  obtain ⟨xY, hxY, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z) x
    (closedPoint (BaseRing q z)) (by rw [hqx, baseι_closedPoint])
  obtain ⟨dY, hdY, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := baseι q z) d
    (⊥ : PrimeSpectrum (BaseRing q z)) (by rw [hqd, baseι_bot, hzt])
  have hdxY : dY ⤳ xY := hjemb.specializes_iff.mp (by rw [hdY, hxY]; exact hdx')
  have hzxY : zY ⤳ xY := hjemb.specializes_iff.mp (by
    rw [hzY, hxY]
    exact specializes_iff_mem_closure.mpr hyz)
  have hsmY : DeJong.IsSmoothAt g xY :=
    DeJong.isSmoothAt_pullback_snd q (baseι q z) xY (by rw [hxY]; exact hpair.smoothAlong x hyD)
  obtain ⟨η, hηgen, hηd⟩ := exists_isGeneric_specializes dY
  have hηz : η = zY := eq_of_isSmoothAt g hsmY hηgen hzYgen (hηd.trans hdxY) hzxY
  have hzd : z ⤳ d := by
    have h := hηd.map j.continuous
    rw [hηz, hzY, hdY] at h
    exact h
  obtain ⟨dt, hdt'⟩ : d ∈ Set.range (pullback.fst q (residuePt t)) := by
    rw [range_fst_residuePt]
    exact hqd
  -- `d` is algebraic over `κ(t)`: `D' → Spec V` is étale
  have halgD : IsAlgebraicAt (D'.subschemeι ≫ q) dD := by
    let := ((D'.subschemeι ≫ q).residueFieldMap dD).hom.toAlgebra
    have : Algebra.IsIntegral _ _ :=
      Algebra.IsAlgebraic.isIntegral (K := (Spec (CommRingCat.of V)).residueField
        ((D'.subschemeι ≫ q) dD)) (A := D'.subscheme.residueField dD)
    exact fun a => Algebra.IsIntegral.isIntegral a
  have halg : IsAlgebraicAt q d := isAlgebraicAt_of_comp halgD
  refine ⟨dt, ?_, ?_, ?_, ?_⟩
  · rw [closure_singleton_eq_preimage q t ζ, Set.mem_preimage, hdt']
    exact specializes_iff_mem_closure.mp hzd
  · rw [hdt']
    exact hdD
  · rw [hdt']
    exact halg
  · rw [hdt']
    exact specializes_iff_mem_closure.mp hdx'

end Count

end DeJongAlterations.StableModification.BlowDown.ClosureLocal

namespace DeJongAlterations.StableModification.BlowDown.ExcSpecialize

universe u

open ClosureComponent ClosureLocal ValCurves

/-- **The étale-local part of the closure-component lemma holds** (`ClosureComponentLocal`;
blueprint `thm:sm-bdcl-closure-local`, Temkin, proof of Lemma 4.4.4, T:3164–3166): for a proper
semi-stable pair `(q : X → Spec V, D')` over a valuation ring `V` with all `Frac(V/𝔭)` separably
closed, a point `t` of `Spec V` and a generic point `ζ` of `X_t` with image `z ∈ X`, the closed
fibre of the reduced closure of `z` is reduced, and the boundary points and marks of its trace on
`X_{s₀}` are at most as many as the special points of `X_t` on `closure {ζ}`. -/
theorem closureComponentLocal : ClosureComponentLocal.{u} := by
  intro V _ _ _ _ hsep X _ q D' _ _ hpair t ζ hζ
  have := hpair.nodal
  have hζgen := (CurvesField.Genus.mem_genericPoints_iff ζ).mp hζ
  refine ⟨isReduced_fibreAt_closedPoint q _ (isGeneric_fst_residuePt q ζ hζgen), ?_⟩
  set A := closedBoundaryPoints q (pullback.fst q (residuePt t) ζ)
  set B := closedMarkPoints q D' (pullback.fst q (residuePt t) ζ)
  set C := closure {ζ} ∩ specialPoints q D' (residuePt t)
  have hA : ∀ y ∈ A, _ := fun y (hy : y ∈ A) => exists_boundary_image q ζ hζgen hy
  have hB : ∀ y ∈ B, _ := fun y (hy : y ∈ B) => exists_mark_image q ζ hζgen hpair hy
  have : Nonempty (pullback (C := Scheme.{u}) q (residuePt t)) := ⟨ζ⟩
  choose! F hF using hA
  choose! G hG using hB
  have hinj : ∀ (f : pullback (C := Scheme.{u}) q (residuePt (IsLocalRing.closedPoint V)) →
      pullback (C := Scheme.{u}) q (residuePt t)) (S : Set _),
      (∀ y ∈ S, IsAlgebraicAt q (pullback.fst q (residuePt t) (f y)) ∧
        pullback.fst q (residuePt (IsLocalRing.closedPoint V)) y ∈
          closure {pullback.fst q (residuePt t) (f y)}) → Set.InjOn f S := by
    intro f S h y₁ hy₁ y₂ hy₂ heq
    obtain ⟨ha₁, hc₁⟩ := h y₁ hy₁
    obtain ⟨-, hc₂⟩ := h y₂ hy₂
    rw [← heq] at hc₂
    exact (isEmbedding_fst_residuePt q _).injective (eq_of_mem_closure_of_isAlgebraicAt hsep q ha₁
      hc₁ hc₂ (apply_fst_residuePt q y₁) (apply_fst_residuePt q y₂))
  have hFinj : Set.InjOn F A := hinj F A fun y hy => ⟨(hF y hy).2.2.1, (hF y hy).2.2.2⟩
  have hGinj : Set.InjOn G B := hinj G B fun y hy => ⟨(hG y hy).2.2.1, (hG y hy).2.2.2⟩
  have hFC : F '' A ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(hF y hy).1, Or.inr (hF y hy).2.1⟩
  have hGC : G '' B ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(hG y hy).1, Or.inl (hG y hy).2.1⟩
  have hdisj : Disjoint (F '' A) (G '' B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, h⟩
    apply (hF y₁ hy₁).2.1
    apply DeJong.isSmoothAt_pullback_snd q (residuePt t)
    rw [← h]
    exact hpair.smoothAlong _ (hG y₂ hy₂).2.1
  calc A.encard + B.encard = (F '' A).encard + (G '' B).encard := by
        rw [hFinj.encard_image, hGinj.encard_image]
    _ = (F '' A ∪ G '' B).encard := (Set.encard_union_eq hdisj).symm
    _ ≤ C.encard := Set.encard_le_encard (Set.union_subset hFC hGC)

end DeJongAlterations.StableModification.BlowDown.ExcSpecialize
