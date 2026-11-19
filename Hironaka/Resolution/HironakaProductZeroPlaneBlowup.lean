import Hironaka.Analytic.ProductComplexManifold
import Hironaka.Blowup.BlowupExistence
import Hironaka.Blowup.BlowupExistenceOriginIdeal

/-! The literal product-zero-plane geometry internally supplies an actual
ambient blowup. Existing Demailly existence/UP and origin thinness are reused
without duplicate proof credit. Blueprint FIRST:
`hironaka-product-zero-plane-blowup.tex`. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaProductZeroPlaneBlowup

open Hironaka.BlowupSequences ProductComplexManifold

open scoped ProductComplexManifold

noncomputable section

variable {n r : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem regularAtDim_product_zero_plane (p : M) :
    RegularAtDim (n := n+r) {q : M × ComplexModel r | q.2 = 0} (p,0) n := by
  let c := complexChartAt (n := n+r) ((p,0) : M × ComplexModel r)
  let a := chartAt (ComplexModel n) p
  have hc (q : M × ComplexModel r) : c.val q = prodModelEquiv n r (a q.1,q.2) := by
    change prodModelEquiv n r (a q.1,(chartAt (ComplexModel r) (0 : ComplexModel r)) q.2) = _
    rw [chartAt_self_eq]
    rfl
  refine ⟨Nat.le_add_right n r,rfl,?_,?_,?_,?_⟩
  · exact {
      source := c.val.target
      target := (fun q : ComplexModel (n+r) => q+c.val (p,0)) ⁻¹' c.val.target
      isOpen_source := c.val.open_target
      isOpen_target := c.val.open_target.preimage (continuous_id.add continuous_const)
      center_mem_source := c.val.map_source (mem_complexChartAt_source _)
      toFun := fun q => q-c.val (p,0)
      invFun := fun q => q+c.val (p,0)
      toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
      invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
      mapsTo_toFun := fun q hq => by
        change (q-c.val (p,0))+c.val (p,0) ∈ c.val.target
        simpa only [sub_add_cancel] using hq
      mapsTo_invFun := fun _ hq => hq
      left_inv := fun q _ => sub_add_cancel q _
      right_inv := fun q _ => add_sub_cancel_right q _ }
  · exact Subset.rfl
  · exact sub_self _
  · intro q _hq _hq'
    change q.2 = 0 ↔ c.val q-c.val (p,0) ∈ complexCoordinatePlane (n+r) n
    rw [hc q,hc (p,0),← map_sub]
    change q.2 = 0 ↔ prodModelEquiv n r (a q.1-a p,q.2-0) ∈ complexCoordinatePlane (n+r) n
    rw [sub_zero,prodModelEquiv_mem_complexCoordinatePlane_iff]

omit [IsComplexManifold n M] in
/-- The literal actual product zero-plane is closed smooth, including r=0. -/
theorem isClosedSubmanifold_product_zero_plane :
    IsClosedSubmanifold (n+r) {q : M × ComplexModel r | q.2 = 0} := by
  refine ⟨isClosed_eq continuous_snd continuous_const,?_⟩
  rintro ⟨p,v⟩ (hv : v = 0)
  subst v
  exact ⟨n,regularAtDim_product_zero_plane p⟩

/-- Positive actual normal dimension derives nowhere density in the SAME topology. -/
theorem interior_product_zero_plane_eq_empty (hr : 0 < r) :
    interior {q : M × ComplexModel r | q.2 = 0} = ∅ := by
  have hC : {q : M × ComplexModel r | q.2 = 0} =
      (univ : Set M) ×ˢ ({0} : Set (ComplexModel r)) := by ext q; simp
  rw [hC,interior_prod_eq,BlowupExistenceOriginIdeal.interior_zero_eq_empty hr]
  simp

/-- ONLY the actual native ambient and r>0 are input: internally construct
the actual blowup manifold/topology/atlas/projection and existing predicate. -/
theorem exists_product_zero_plane_blowup (hr : 0 < r) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (n+r)) Y)
      (_ : IsComplexManifold (n+r) Y) (π : Y → M × ComplexModel r),
      IsBlowupAlong (n+r) {q : M × ComplexModel r | q.2 = 0} π := by
  exact BlowupExistence.exists_isBlowupAlong {q : M × ComplexModel r | q.2 = 0}
    isClosedSubmanifold_product_zero_plane (interior_product_zero_plane_eq_empty hr)

end
end Hironaka.HironakaProductZeroPlaneBlowup
