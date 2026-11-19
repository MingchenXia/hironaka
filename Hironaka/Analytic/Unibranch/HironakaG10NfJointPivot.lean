import Hironaka.Analytic.Unibranch.HironakaG10NfJointLocal
import Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
import Hironaka.Resolution.HironakaG10ChowRatioGeneration
import Hironaka.Analytic.Unibranch.HironakaG10NfTorsionSpread
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
import Hironaka.Blowup.BlowupSpaceRatio

/-!
# H3.4 (centre generator, generic part): the joint pivot class and the torsion of a generator

Lane G10H3, run 0081 (field `T_w₀` of `HironakaG10NfGeoFibreModel.GeoFibreModel`; also the `g`-field of G10GL's pulled
presentations).  On a real-open blowup chart with the joint ideal (TN `HironakaG10JointStrictTorsion`):

* `targetStalkToJoint_germ` — the joint target scalar map sends the class of a target function germ `h` to the class of
  `h ∘ f`;
* `targetStalkToJoint_pivot` — if `h ∘ f` is the pivot coordinate near `y`, the class of `h` goes to the pivot class;
* `exists_unit_of_span_eq` — two generators of the same principal ideal, one regular, differ by a unit;
* `powerSat_bot_unit_mul` — the whole `u·p`-torsion (`u` a unit) is the `p`-power torsion;
* **`pivotTorsion_eq_powerSat`** — if `ψ g = u · pivotClass` with `u` a unit, the joint pivot torsion is
  `powerSat ⊥ (ψ g)`;
* `lift_coordinates`, `lift_pivot_flatCoord` — the monomial lift of a product chart keeps the normal coordinates; in
  particular the pivot flat coordinate of the target base of the lift is the pivot coordinate of the source point.

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfJointPivot

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaG10ChowRatioGeneration Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation

noncomputable section

section Algebra

variable {A : Type*} [CommRing A]

/-- Two generators of the same principal ideal, the first regular, differ by a unit. -/
theorem exists_unit_of_span_eq {a c : A} (ha : IsRegular a) (h : Ideal.span {a} = Ideal.span {c}) :
    ∃ s : A, IsUnit s ∧ a = s * c := by
  have hc : c ∈ Ideal.span {a} := h ▸ Ideal.subset_span rfl
  have ha' : a ∈ Ideal.span {c} := h ▸ Ideal.subset_span rfl
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hc
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp ha'
  have h1 : a * (s * r) = a * 1 := by
    calc a * (s * r) = s * (r * a) := by ring
      _ = s * c := by rw [hr]
      _ = a := hs
      _ = a * 1 := (mul_one a).symm
  have hsr : s * r = 1 := ha.1 h1
  exact ⟨s, IsUnit.of_mul_eq_one r hsr, hs.symm⟩

/-- The whole `u·p`-power torsion (`u` a unit) is the `p`-power torsion. -/
theorem powerSat_bot_unit_mul {u p : A} (hu : IsUnit u) :
    powerSat (⊥ : Ideal A) (u * p) = Submodule.torsion' A A (Submonoid.powers p) := by
  ext a
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨⟨p ^ m, m, rfl⟩, ?_⟩
    change p ^ m * a = 0
    have h0 : (u * p) ^ m * a = 0 := hm
    rw [mul_pow, mul_assoc] at h0
    exact (hu.pow m).mul_right_eq_zero.mp h0
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    refine ⟨m, ?_⟩
    change (u * p) ^ m * a = 0
    have h0 : p ^ m * a = 0 := hm
    rw [mul_pow, mul_assoc, h0, mul_zero]

end Algebra

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
  (hV : IsComplexAnalyticSubset (n := n) V)

/-- The joint target scalar map on the class of a target function germ. -/
theorem targetStalkToJoint_germ (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V) (h : Y → ℂ)
    (hh : HolomorphicAt n h (f y)) :
    targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV
        ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y, hyV⟩ (actualOriginalFunctionGerm (f y) h hh)) =
      Ideal.Quotient.mk (jointIdeal (n := n) d t j b U W f V y)
        (actualOriginalFunctionGerm y (h ∘ f) (hh.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt))) := by
  rw [targetStalkToJoint_inclusion]
  exact congrArg _ (stalkMap_originalGerm hf y h hh)

/-- **The class of a target function whose pull-back is the pivot coordinate goes to the pivot class.** -/
theorem targetStalkToJoint_pivot (y : realOpenChartDomain d t j b U) (hyV : f y ∈ V) (h : Y → ℂ)
    (hh : HolomorphicAt n h (f y)) (heq : ∀ᶠ y' in 𝓝 y, h (f y') = y'.val (j.natAdd d)) :
    targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV
        ((actualSubspaceInclusion (n := n) V).stalkMap ⟨f y, hyV⟩ (actualOriginalFunctionGerm (f y) h hh)) =
      pivotClass (n := n) d t j b U W f V y := by
  rw [targetStalkToJoint_germ]
  unfold pivotClass exceptionalGerm
  congr 1
  exact Hironaka.Analytic.Unibranch.HironakaG10NfTorsionSpread.germ_congr y _ _ _ _ heq

omit [IsComplexManifold n Y] in
/-- **The joint pivot torsion is the whole torsion of `ψ g`** when `ψ g` is a unit times the pivot class. -/
theorem pivotTorsion_eq_powerSat (y : realOpenChartDomain d t j b U)
    {u : JointQuotient (n := n) d t j b U W f V y} (hu : IsUnit u) :
    pivotTorsion (n := n) d t j b U W f V y =
      powerSat (⊥ : Ideal (JointQuotient (n := n) d t j b U W f V y)) (u * pivotClass (n := n) d t j b U W f V y) :=
  (powerSat_bot_unit_mul hu).symm

section LiftCoordinates

open BlowupConstruction BlowupMonomialCharts Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
open scoped Hironaka.ProductComplexManifold

variable {m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel d) P] [IsComplexManifold d P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]

/-- The coordinates of the monomial lift (the public form of the private `lift_coordinates`). -/
theorem lift_coordinates (a : ProductNormalCharts d r P) (b' : ProductNormalCharts m r Q) {g : P → Q}
    (hg : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel m) ∞ g)
    (L : BlowupSpace (d+r) {q : P × ComplexModel r | q.2=0} → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map g id ∘ blowupProj (d+r) {q : P × ComplexModel r | q.2=0})
    (j' : Fin r) (z : productChartOpen a j') :
    productChartCoordinates b' j' (monomialLiftOnChart a b' hg L hL hπ j' z) =
      monomialCandidateCoordinates a b' g j' z := by
  change (productNormalChart (n := m) b'.base j').toFun (L z.val) = _
  rw [allambient_lift_formula a b' hg L hL hπ]
  apply (productNormalChart (n := m) b'.base j').right_inv
  change monomial m (j'.natAdd m) _ ∈ (productNormalChart (n := m) b'.base j').Φ.target
  rw [product_monomial_covariance]
  have hd : (g z.val.base.1, z.val.base.2) ∈ (productNormalChart (n := m) b'.base j').dom := by
    rw [b'.domain j']
    trivial
  exact hd.2

/-- **The pivot flat coordinate of the lift is the pivot coordinate of the source point.** -/
theorem lift_pivot_flatCoord (a : ProductNormalCharts d r P) (b' : ProductNormalCharts m r Q) {g : P → Q}
    (hg : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel m) ∞ g)
    (L : BlowupSpace (d+r) {q : P × ComplexModel r | q.2=0} → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2=0})
    (hL : ContMDiff 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞ L)
    (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} ∘ L =
      Prod.map g id ∘ blowupProj (d+r) {q : P × ComplexModel r | q.2=0})
    (j' : Fin r) (z : productChartOpen a j') :
    (productNormalChart (n := m) b'.base j').τ (j'.natAdd m)
        (blowupProj (m+r) {q : Q × ComplexModel r | q.2=0} (monomialLiftOnChart a b' hg L hL hπ j' z).val) =
      productChartCoordinates a j' z (j'.natAdd d) := by
  set cb := productNormalChart (n := m) b'.base j'
  have hz : (monomialLiftOnChart a b' hg L hL hπ j' z).val ∈ cb.source :=
    (monomialLiftOnChart a b' hg L hL hπ j' z).property
  have hp := congrArg (fun w : ComplexModel (m+r) => w cb.j) (cb.monomial_toFun hz)
  simp only at hp
  rw [cb.monomial_apply_j] at hp
  have hlift : cb.toFun (monomialLiftOnChart a b' hg L hL hπ j' z).val cb.j =
      productChartCoordinates a j' z (j'.natAdd d) := by
    change productChartCoordinates b' j' (monomialLiftOnChart a b' hg L hL hπ j' z) (j'.natAdd m) = _
    rw [lift_coordinates]
    simp [monomialCandidateCoordinates, ProductComplexManifold.prodModelEquiv, EuclideanSpace.finAddEquivProd,
      EuclideanSpace.sumEquivProd]
  exact hp.symm.trans hlift

end LiftCoordinates

end

end Hironaka.Analytic.Unibranch.HironakaG10NfJointPivot
