import Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
import Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover

/-!
# Lemma 4.4.5, first half of the support germs: from flatness over the germ strict transform (G10-03-09.d)

Lane G10SB, run 0081.  Hironaka 1975 Lemma 4.4.5, proof (printed p. 537): "(F,f)/Z_p is flat … hence
(F₁, f₁)/Z_p^* is also flat …"; the local flattener `Z_{p1}` then contains `Z_p^*`.  Natively:

* `strictIdeal_le_vanishingIdealAt` — at a point `x'` of the transported support `T(Z)`, the WHOLE germ strict ideal
  (for the local exceptional generator) consists of germs of sections vanishing on `T(Z)` near `x'`;
* `eventually_mem_support_of_flat_strict` — **(G1)**: if the strict-transform family is flat over the germ strict
  transform at `x'` (Hironaka's (i)), every local flattener of the next stage through `x'` contains `T(Z)` near `x'`.

Remaining for the support germs (G10-03-09.c/.e, see `G10SB/G10-02-09r-lemma445-route.md`): Hironaka's (i) itself
(flatness of the strict transform over `Z_p^*`) and the reverse inclusion (G2).  No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SbTransportGermUpper

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership
  Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
  Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep

noncomputable section

/-- **The germ strict ideal vanishes on the transported support.**  At `x' ∈ T(Z)`, for the local exceptional
section `sG` of the strict-membership criterion, every element of the germ strict ideal is the germ of a section
vanishing at every point of `T(Z)` near `x'`. -/
theorem strictIdeal_le_vanishingIdealAt (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    (x' : (nextWith s c).X.obj.left) (hx' : x' ∈ transportedSupport s c Z)
    (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
    (sG : (nextWith s c).X.obj.left.presheaf.obj (op U))
    (hcrit : ∀ (y : (nextWith s c).X.obj.left) (hy : y ∈ U),
      ∀ I : Ideal (s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base y)),
        OnStrictTransform (stepσ s c) y I (centreIdeal c ((stepσ s c).hom.left.base y)) ↔
          strictIdeal ((stepσ s c).hom.left.stalkMap y).hom I
            (centreIdeal c ((stepσ s c).hom.left.base y))
            ((nextWith s c).X.obj.left.presheaf.germ U y hy sG) ≠ ⊤) :
    strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
        (germFlattener s.f ((stepσ s c).hom.left.base x'))
        (centreIdeal c ((stepσ s c).hom.left.base x'))
        ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) ≤
      vanishingIdealAt (nextWith s c).X.obj.left (transportedSupport s c Z) x' := by
  have hft := c.finiteType
  have hcont : Continuous (stepσ s c).hom.left.base := (stepσ s c).hom.left.base.hom.continuous
  refine Ideal.span_le.mpr ?_
  rintro g ⟨k, h, hmem, heq⟩
  have hsupp := hx'.1
  have hhZ : h ∈ Z.H ((stepσ s c).hom.left.base x') := by
    rw [Z.H_eq_germFlattener hsupp]
    exact hmem.1
  obtain ⟨U₁, hxU₁, hh, hhgerm, hhmem⟩ := spreads_inf (spreads_localFlattener Z _ hsupp.1 h hhZ)
    (spreads_pow (spreads_centreIdeal c _) k h hmem.2)
  obtain ⟨V₁, hxV₁, gg, hgg⟩ := exists_section x' g
  have hE1 := eventually_germ_eq (T := (nextWith s c).X.obj.left) (U := (Opens.map
      (stepσ s c).hom.left.base).obj U₁) (V := U ⊓ V₁) hxU₁ ⟨hxU, hxV₁⟩
    (((stepσ s c).hom.left.c.app (op U₁)).hom hh)
    (((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_left).op).hom sG ^ k *
      ((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_right).op).hom gg) (by
        rw [← stalkMap_germ_hom, hhgerm, map_mul, map_pow, germ_res_hom, germ_res_hom, hgg]
        exact heq)
  have hU₁ : ∀ᶠ y' in 𝓝 x', (stepσ s c).hom.left.base y' ∈ U₁ :=
    hcont.continuousAt.preimage_mem_nhds (U₁.isOpen.mem_nhds hxU₁)
  have hUe : ∀ᶠ y' in 𝓝 x', y' ∈ U := U.isOpen.mem_nhds hxU
  have hVe : ∀ᶠ y' in 𝓝 x', y' ∈ V₁ := V₁.isOpen.mem_nhds hxV₁
  obtain ⟨N, hN, hNo, hxN⟩ := eventually_nhds_iff.mp (hE1.and (hU₁.and (hUe.and hVe)))
  let W : Opens (nextWith s c).X.obj.left := ⟨N, hNo⟩ ⊓ V₁
  refine Ideal.subset_span ⟨W, ⟨hxN, hxV₁⟩,
    ((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_right).op).hom gg, ?_, fun y hy hyT => ?_⟩
  · exact (germ_res_hom (homOfLE inf_le_right) x' ⟨hxN, hxV₁⟩ gg).trans hgg
  · obtain ⟨e1, hy₁, hyU, -⟩ := hN y hy.1
    show ((nextWith s c).X.obj.left.presheaf.germ W y hy).hom
      (((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_right).op).hom gg) ∈ _
    rw [germ_res_hom]
    have e1' := e1 hy₁ ⟨hyU, hy.2⟩
    rw [map_mul, map_pow, germ_res_hom, germ_res_hom, ← stalkMap_germ_hom] at e1'
    have hy_strict : strictIdeal ((stepσ s c).hom.left.stalkMap y).hom
        (germFlattener s.f ((stepσ s c).hom.left.base y)) (centreIdeal c ((stepσ s c).hom.left.base y))
        ((nextWith s c).X.obj.left.presheaf.germ U y hyU sG) ≠ ⊤ :=
      (hcrit y hyU _).mp hyT.2
    have hmem' : ((nextWith s c).X.obj.left.presheaf.germ V₁ y hy.2).hom gg ∈
        strictIdeal ((stepσ s c).hom.left.stalkMap y).hom
          (germFlattener s.f ((stepσ s c).hom.left.base y)) (centreIdeal c ((stepσ s c).hom.left.base y))
          ((nextWith s c).X.obj.left.presheaf.germ U y hyU sG) := by
      refine Ideal.subset_span ⟨k, (s.X.obj.left.presheaf.germ U₁ _ hy₁).hom hh, ?_, e1'⟩
      have hm := hhmem _ hy₁
      refine ⟨?_, hm.2⟩
      rw [← Z.H_eq_germFlattener hyT.1]
      exact hm.1
    exact IsLocalRing.le_maximalIdeal hy_strict hmem'

/-- **(G1) — Hironaka Lemma 4.4.5, first inclusion.**  If, at a point `x'` of the transported support, the
strict-transform family is flat over the germ strict transform (for the local exceptional generator), then every
local flattener of the next stage through `x'` contains the transported support near `x'`. -/
theorem eventually_mem_support_of_flat_strict (s : Stage) (c : AdmissibleCentre s.f)
    (Z : LocalFlattener s.f) (x' : (nextWith s c).X.obj.left) (hx' : x' ∈ transportedSupport s c Z)
    (hflat : ∀ (U : Opens (nextWith s c).X.obj.left) (hxU : x' ∈ U)
      (sG : (nextWith s c).X.obj.left.presheaf.obj (op U)),
      IsRegular ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG) →
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom (centreIdeal c ((stepσ s c).hom.left.base x')) =
        Ideal.span {(nextWith s c).X.obj.left.presheaf.germ U x' hxU sG} →
      FlatOverAt (nextWith s c).f x'
        (strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
          (germFlattener s.f ((stepσ s c).hom.left.base x'))
          (centreIdeal c ((stepσ s c).hom.left.base x'))
          ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG)))
    (Z₁ : LocalFlattener (nextWith s c).f) (hx₁ : x' ∈ Z₁.support) :
    ∀ᶠ y' in 𝓝 x', y' ∈ transportedSupport s c Z → y' ∈ Z₁.support := by
  have hft := c.finiteType
  obtain ⟨U, hxU, sG, hcrit⟩ := exists_local_projection_strict_criterion c.B c.b c.dense x'
  obtain ⟨hreg, hspan, -⟩ := hcrit x' hxU
  have hflat' := (hflat U hxU sG.val hreg hspan).mono
    (strictIdeal_le_vanishingIdealAt s c Z x' hx' U hxU sG.val (fun y hy => (hcrit y hy).2.2))
  filter_upwards [eventually_mem_support_of_flat Z₁ hx₁ hflat'] with y' hy' hyT
  refine ⟨hy'.1, fun htop => ?_⟩
  have hle := hy'.2
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (top_le_iff.mp (hle.trans (vanishingIdealAt_le_maximalIdeal _ hyT)))

end

end Hironaka.Analytic.Unibranch.HironakaG10SbTransportGermUpper
