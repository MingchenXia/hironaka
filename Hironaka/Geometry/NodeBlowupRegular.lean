import Hironaka.Geometry.NodeBlowupCover
import Hironaka.Geometry.RegularNode
import Hironaka.Geometry.AffineBlowupAlteration
import Hironaka.Geometry.AffineBlowupProjective

/-!
# Regularity of the genuine two-chart node blowup

The native blowup of `A[u,v]/(uv-t*q)` in `(u,t)` has the two actual
smaller-node charts. If both coefficients are local parameters on the regular
base, both charts are regular, so the blowup itself is a regular projective
alteration. This is a local case of de Jong Proposition 3.6, not its global
semistable resolution statement.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Hironaka

universe u v

/-- Regularity of actual scheme stalks is local for native open covers. -/
theorem IsRegularScheme.of_openCover {Y : Scheme.{u}} (𝒰 : Y.OpenCover.{v})
    (h : ∀ i, IsRegularScheme (𝒰.X i)) : IsRegularScheme Y := by
  intro y
  obtain ⟨x, hx⟩ := 𝒰.covers y
  let : IsRegularLocalRing ((𝒰.X (𝒰.idx y)).presheaf.stalk x) := h _ x
  have hr : IsRegularLocalRing (Y.presheaf.stalk ((𝒰.f (𝒰.idx y)) x)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((𝒰.f (𝒰.idx y)).stalkMap x)).symm.commRingCatIsoToRingEquiv
  have heq : (𝒰.f (𝒰.idx y)) x = y := hx
  rw [heq] at hr
  exact hr

namespace NodeBlowupRegular

open Algebra.NodeBlowupChart NodeBlowupCover Geometry.RegularNode

variable {A : Type u} [CommRing A] [IsDomain A] (t q : A)
  [Fact (t ≠ 0)] [Fact (q ≠ 0)]

omit [IsDomain A] [Fact (t ≠ 0)] [Fact (q ≠ 0)] in
/-- The actual two-generator node center is finitely generated. -/
theorem centerIdeal_fg : (centerIdeal t q).FG := by
  classical
  exact ⟨{coordinate (t * q) 0, algebraMap A (Node A (t * q)) t}, by
    simp [centerIdeal]⟩

/-- The actual center contains the nonzero original node coordinate. -/
theorem centerIdeal_ne_bot : centerIdeal t q ≠ ⊥ := by
  intro h
  have hz : coordinate (t * q) 0 = 0 := by
    have hm : coordinate (t * q) 0 ∈ centerIdeal t q :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at hm
    exact hm
  exact Algebra.NodeDomain.nodeCoordinate_ne_zero (t * q)
    (mul_ne_zero (Fact.out : t ≠ 0) (Fact.out : q ≠ 0)) 0 hz

omit [IsDomain A] [Fact (t ≠ 0)] [Fact (q ≠ 0)] in
/-- The actual blowup structure map is projective, with its native center. -/
theorem nodeBlowup_isProjective :
    IsProjectiveOver (affineBlowupStructure (centerIdeal t q)) :=
  affineBlowupStructure_isProjective _ (centerIdeal_fg t q)

/-- The actual blowup structure map is an alteration of the original node. -/
theorem nodeBlowup_isAlteration :
    IsAlteration (affineBlowupStructure (centerIdeal t q)) :=
  affineBlowupStructure_isAlteration _ (centerIdeal_ne_bot t q) (centerIdeal_fg t q)

variable [IsRegularRing A]

/-- The native coordinate-chart open is regular if `t` is a local parameter. -/
theorem coordinateChart_isRegular
    (ht : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (coordinateChartOpen t q).toScheme := by
  exact (isRegularScheme_nodeQuotient t ht).of_isOpenImmersion (uChartSchemeIso t q).hom

/-- The native parameter-chart open is regular if `q` is a local parameter. -/
theorem parameterChart_isRegular
    (hq : ∀ (p : Ideal A) [p.IsPrime], q ∈ p →
      algebraMap A (Localization.AtPrime p) q ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (parameterChartOpen t q).toScheme := by
  exact (isRegularScheme_nodeQuotient q hq).of_isOpenImmersion (tChartSchemeIso t q).hom

/-- Blowing up `(u,t)` resolves the actual `uv=t*q` node when both coefficients
are local parameters on the regular base. The cover is constructed internally. -/
theorem nodeBlowup_isRegular
    (ht : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2)
    (hq : ∀ (p : Ideal A) [p.IsPrime], q ∈ p →
      algebraMap A (Localization.AtPrime p) q ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (affineBlowup (centerIdeal t q)) := by
  apply IsRegularScheme.of_openCover (nodeBlowupOpenCover t q)
  intro b
  cases b
  · exact isRegularScheme_nodeQuotient t ht
  · exact isRegularScheme_nodeQuotient q hq

end NodeBlowupRegular

end Hironaka
