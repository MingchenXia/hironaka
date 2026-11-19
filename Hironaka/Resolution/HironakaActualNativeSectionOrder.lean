import Hironaka.Resolution.HironakaActualNativeSectionColon
import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality
import Hironaka.MarkedIdeal.CoefficientRestrictionTower
/-! Original scalar vanishing order, ideal order and cosupport commute with
an actual native regular inclusion. Native point-ideal powers are internally
identified using genuine germ extension. No chronological value comparison
or desired order identity is among the hypotheses. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves GermIdealOrder
  GermIdealPullbackCalculus RelativePrincipalizationSpan SubmanifoldChartedSpace
  HironakaActualSubmanifoldGermExtension HironakaActualNativeSectionColon
  CoefficientRestrictionTower IdealWeightPowers InvertibleIdealQuotient
variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

private theorem vanishes_iff_restricted_span {r : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel r) M] [IsComplexManifold r M]
    (A : Set M) (p : M) (q : ℕ) (g : M→ℂ) :
    VanishesToOrderOn r A p q g ↔
      IsInSpanOnAt (n := r) A ((idealPow (pointIdeal r p) q).mem p) p g := by
  constructor
  · rintro ⟨h,hh,he⟩
    exact IsInSpanOnAt.congr_right (W := A) (IsInSpanAt.restrict (isInSpanAt_self hh (holomorphicAt_of_mem_idealPow hh))) he
  · intro hg
    exact vanishesToOrderOn_of_isInSpanOnAt hg
      (fun a ha => ⟨a,ha,Eventually.of_forall fun _ _ => rfl⟩)

theorem pullback_native_pointIdeal_power (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(p : W) (q : ℕ),
      GermIdeal.pullback (m := k) (Subtype.val : W→X) (idealPow (pointIdeal n p.val) q)=
        idealPow (pointIdeal k p) q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p q
  rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow (contMDiff_val hk hW)
    (fun hg => holomorphicAt_of_mem_pointIdeal hg)]
  have hpoint : GermIdeal.pullback (m := k) (Subtype.val : W→X) (pointIdeal n p.val)=pointIdeal k p := by
    have himage : (Subtype.val : W→X) '' ({p} : Set W)=({p.val} : Set X):=Set.image_singleton
    simpa only [pointIdeal,himage] using pullback_vanishing_image hk hW ({p} : Set W)
  rw [hpoint]

theorem vanishesToOrderOn_native_iff (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (p : W) (q : ℕ) (g : X→ℂ),
      VanishesToOrderOn n ((Subtype.val : W→X) '' A) p.val q g ↔
        VanishesToOrderOn k A p q (g ∘ Subtype.val) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A p q g
  rw [vanishes_iff_restricted_span,vanishes_iff_restricted_span]
  have h:=restrictedSpan_native_iff hk hW A (idealPow (pointIdeal n p.val) q)
    (fun _ _ hg => holomorphicAt_of_mem_idealPow hg) p g
  rw [pullback_native_pointIdeal_power hk hW p q] at h
  exact h

theorem orderGE_native_iff (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (p : W) (q : ℕ),
      OrderGE n ((Subtype.val : W→X) '' A) J p.val q ↔
        OrderGE k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) p q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ p q
  constructor
  · intro h g hg
    apply vanishesToOrderOn_of_isInSpanOnAt (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨a,ha,rfl⟩
    exact (vanishesToOrderOn_native_iff hk hW A p q a).mp (h a ha)
  · intro h g hg
    have hgPull : (GermIdeal.pullback (m := k) (Subtype.val : W→X) J).mem p (g ∘ Subtype.val):=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
        ((hJ _ _ hg).comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hW).contMDiffAt)))
    exact (vanishesToOrderOn_native_iff hk hW A p q g).mpr (h _ hgPull)

theorem order_native_eq (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (p : W),
      order n ((Subtype.val : W→X) '' A) J p.val =
        order k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ p
  simp only [order,orderGE_native_iff hk hW A J hJ p]

theorem cosupport_native_preimage (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (d : ℕ),
      (Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A) J d =
        cosupport k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) d := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ d
  ext p
  change (p.val∈(Subtype.val : W→X) '' A ∧ OrderGE n ((Subtype.val : W→X) '' A) J p.val d) ↔
    (p∈A ∧ OrderGE k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) p d)
  rw [orderGE_native_iff hk hW A J hJ p d]
  have hm : p.val∈(Subtype.val : W→X) '' A ↔ p∈A :=by
    constructor
    · rintro ⟨y,hy,he⟩
      exact (Subtype.val_injective he) ▸ hy
    · intro hp
      exact ⟨p,hp,rfl⟩
  rw [hm]

theorem cosupport_native_image (hk : k≤n)
    (hW : ∀x∈W,RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀(A : Set W) (J : GermIdeal n X)
      (_hJ : ∀z g,J.mem z g → HolomorphicAt n g z) (d : ℕ),
      (Subtype.val : W→X) '' cosupport k A (GermIdeal.pullback (m := k) (Subtype.val : W→X) J) d =
        cosupport n ((Subtype.val : W→X) '' A) J d := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ d
  apply Set.Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    have hh : p∈(Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A) J d:=by
      rw [cosupport_native_preimage hk hW A J hJ d]
      exact hp
    exact hh
  · intro x hx
    obtain ⟨p,_hpA,rfl⟩:=hx.1
    refine ⟨p,?_,rfl⟩
    have hh : p∈(Subtype.val : W→X) ⁻¹' cosupport n ((Subtype.val : W→X) '' A) J d:=hx
    rwa [cosupport_native_preimage hk hW A J hJ d] at hh

end
end Hironaka.HironakaActualNativeSectionOrder
