import Hironaka.Resolution.HironakaActualFreePlaneRegularity
import Hironaka.Resolution.HironakaActualZeroSectionCentreGeometry
import Hironaka.Manifold.LocalHolomorphicInverse

/-! A genuine free-only product flattening of the SAME actual centre.
The free chart is internally extracted by zero-section regularity reflection.
The ambient chart is a finite actual restriction of the existing public
product extension, with both whole functions unchanged. No supplied free
flattening, linear complement, target HS or compatibility certificate.
Blueprint: hir:actual-same-centre-free-product-flattening.
Complete source draft only; no elaboration or kernel acceptance is claimed. -/

set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Manifold

namespace Hironaka.HironakaActualFreeProductFlattening
noncomputable section

open HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualZeroSectionCentreGeometry HironakaActualFreePlaneRegularity

/-- The public mother equivalence has this literal whole forward function.
No private coordinate lemma from its implementation is invoked. -/
theorem actualFreeProduct_toFun_eq (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) :
    (actual_zeroSection_localEquiv m e 0 χ).toFun z =
      tangentInclusion m e (χ.toFun (tangentProjection m e z)) +
        (z - tangentInclusion m e (tangentProjection m e z)) := rfl

/-- The public mother equivalence has this literal whole inverse function. -/
theorem actualFreeProduct_invFun_eq (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) :
    (actual_zeroSection_localEquiv m e 0 χ).invFun z =
      tangentInclusion m e (χ.invFun (tangentProjection m e z)) +
        (z - tangentInclusion m e (tangentProjection m e z)) := rfl

/-- The actual forward product changes exactly the free projection. -/
theorem actualFreeProduct_toFun_freeProjection (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) :
    tangentProjection m e ((actual_zeroSection_localEquiv m e 0 χ).toFun z) =
      χ.toFun (tangentProjection m e z) := by
  rw [actualFreeProduct_toFun_eq]
  simp only [map_add, map_sub, tangentProjection_tangentInclusion, sub_self, add_zero]

/-- The actual inverse product changes exactly the free projection. -/
theorem actualFreeProduct_invFun_freeProjection (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) :
    tangentProjection m e ((actual_zeroSection_localEquiv m e 0 χ).invFun z) =
      χ.invFun (tangentProjection m e z) := by
  rw [actualFreeProduct_invFun_eq]
  simp only [map_add, map_sub, tangentProjection_tangentInclusion, sub_self, add_zero]

/-- Every essential coordinate is fixed as a WHOLE forward function,
including points outside the actual local source. -/
theorem actualFreeProduct_toFun_essentialCoordinate (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) (j : Fin e) :
    (actual_zeroSection_localEquiv m e 0 χ).toFun z (j.natAdd m) = z (j.natAdd m) := by
  rw [actualFreeProduct_toFun_eq]
  simp only [PiLp.add_apply, PiLp.sub_apply, tangentInclusion_normal, sub_zero, zero_add]

/-- Every essential coordinate is fixed as a WHOLE inverse function. -/
theorem actualFreeProduct_invFun_essentialCoordinate (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (z : ComplexModel (m+e)) (j : Fin e) :
    (actual_zeroSection_localEquiv m e 0 χ).invFun z (j.natAdd m) = z (j.natAdd m) := by
  rw [actualFreeProduct_invFun_eq]
  simp only [PiLp.add_apply, PiLp.sub_apply, tangentInclusion_normal, sub_zero, zero_add]

/-- A centred free chart makes its actual whole product fix the origin. -/
theorem actualFreeProduct_toFun_zero (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) :
    (actual_zeroSection_localEquiv m e 0 χ).toFun 0 = 0 := by
  rw [actualFreeProduct_toFun_eq]
  simp only [map_zero, hχ0, sub_self, add_zero]

/-- The actual inverse identity forces the free inverse, and hence its
whole product extension, to fix the same origin. -/
theorem actualFreeProduct_invFun_zero (m e : ℕ)
    (χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m))
    (hχ0 : χ.toFun 0 = 0) :
    (actual_zeroSection_localEquiv m e 0 χ).invFun 0 = 0 := by
  rw [actualFreeProduct_invFun_eq]
  simp only [map_zero, local_invFun_zero χ hχ0, sub_self, add_zero]

private theorem model_regular_iff (n k : ℕ) (C : Set (ComplexModel n)) :
    RegularAtDim (n := n) C 0 k ↔
      k ≤ n ∧ (0 : ComplexModel n) ∈ C ∧
        ∃ Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n),
          Φ.toFun 0 = 0 ∧ ∀ {y}, y ∈ Φ.source →
            (y ∈ C ↔ Φ.toFun y ∈ complexCoordinatePlane n k) := by
  simp [RegularAtDim, complexChartAt, chartAt_self_eq]
  intro _ _
  rfl

private theorem regular_inter_open {n k : ℕ} {C U : Set (ComplexModel n)}
    (hreg : RegularAtDim (n := n) C 0 k) (hU : IsOpen U)
    (h0U : (0 : ComplexModel n) ∈ U) :
    RegularAtDim (n := n) (C ∩ U) 0 k := by
  obtain ⟨hkn, h0C, Φ, hΦ0, hflat⟩ := (model_regular_iff n k C).mp hreg
  apply (model_regular_iff n k (C ∩ U)).mpr
  refine ⟨hkn, ⟨h0C, h0U⟩, Φ.restrict U hU 0 ⟨Φ.center_mem_source, h0U⟩, hΦ0, ?_⟩
  intro y hy
  change y ∈ Φ.source ∩ U at hy
  change (y ∈ C ∩ U ↔ Φ.toFun y ∈ complexCoordinatePlane n k)
  constructor
  · intro hyC
    exact (hflat hy.1).mp hyC.1
  · intro hyflat
    exact ⟨(hflat hy.1).mpr hyflat, hy.2⟩

/-- Actual regularity and genuine SOURCE plane containment internally
construct a free chart and a restricted product flattening of the SAME C.
Both total maps are exactly the original public product maps. Its genuine
source is restricted once to the actual plane-containment neighbourhood;
the unrestricted product cylinder is not claimed to flatten C. -/
theorem exists_actual_same_centre_free_product_flattening (m e k : ℕ)
    (C : Set (ComplexModel (m+e)))
    (hreg : RegularAtDim (n := m+e) C 0 k)
    (hplane : ∀ᶠ z in 𝓝 (0 : ComplexModel (m+e)),
      z ∈ C → z ∈ complexCoordinatePlane (m+e) m) :
    ∃ χ : LocalHolomorphicEquivAt (n := m) (0 : ComplexModel m),
      χ.toFun 0 = 0 ∧
      ∃ Ψ : LocalHolomorphicEquivAt (n := m+e) (0 : ComplexModel (m+e)),
        Ψ.toFun 0 = 0 ∧
        Ψ.toFun = (actual_zeroSection_localEquiv m e 0 χ).toFun ∧
        Ψ.invFun = (actual_zeroSection_localEquiv m e 0 χ).invFun ∧
        Ψ.source ⊆ (actual_zeroSection_localEquiv m e 0 χ).source ∧
        (∀ z ∈ Ψ.source, z ∈ C ↔ Ψ.toFun z ∈ complexCoordinatePlane (m+e) k) ∧
        (∀ (z : ComplexModel (m+e)) (j : Fin e),
          Ψ.toFun z (j.natAdd m) = z (j.natAdd m)) ∧
        ∀ (z : ComplexModel (m+e)) (j : Fin e),
          Ψ.invFun z (j.natAdd m) = z (j.natAdd m) := by
  obtain ⟨U, hUplane, hU, h0U⟩ := mem_nhds_iff.mp hplane
  let C0 : Set (ComplexModel (m+e)) := C ∩ U
  let D : Set (ComplexModel m) := (tangentInclusion m e) ⁻¹' C0
  have hC0plane : C0 ⊆ complexCoordinatePlane (m+e) m := by
    intro z hz
    exact hUplane hz.2 hz.1
  have hImage : (tangentInclusion m e) '' D = C0 := by
    apply le_antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact hu
    · intro z hz
      refine ⟨tangentProjection m e z, ?_,
        tangentInclusion_projection_eq_of_mem_plane m e (hC0plane hz)⟩
      change tangentInclusion m e (tangentProjection m e z) ∈ C0
      rw [tangentInclusion_projection_eq_of_mem_plane m e (hC0plane hz)]
      exact hz
  have hC0reg : RegularAtDim (n := m+e) C0 0 k := regular_inter_open hreg hU h0U
  have hImageReg : RegularAtDim (n := m+e) ((tangentInclusion m e) '' D) 0 k := by
    rw [hImage]
    exact hC0reg
  have hDreg : RegularAtDim (n := m) D 0 k := regularAtDim_zeroSection_reflects hImageReg
  obtain ⟨hkm, _h0D, χ, hχ0, hχflat⟩ := (model_regular_iff m k D).mp hDreg
  let P := actual_zeroSection_localEquiv m e 0 χ
  have h0P : (0 : ComplexModel (m+e)) ∈ P.source := by
    simpa only [map_zero] using P.center_mem_source
  let Ψ := P.restrict U hU 0 ⟨h0P, h0U⟩
  have hPflat (z : ComplexModel (m+e)) (hz : z ∈ P.source) :
      z ∈ C0 ↔ P.toFun z ∈ complexCoordinatePlane (m+e) k := by
    have hzχ : tangentProjection m e z ∈ χ.source := hz
    rw [actual_zeroSection_localEquiv_plane_iff m e k hkm 0 χ z]
    rw [← hImage, actual_zeroSection_image_eq]
    change (tangentProjection m e z ∈ D ∧ z ∈ complexCoordinatePlane (m+e) m) ↔
      z ∈ complexCoordinatePlane (m+e) m ∧
        χ.toFun (tangentProjection m e z) ∈ complexCoordinatePlane m k
    rw [hχflat hzχ]
    exact and_comm
  refine ⟨χ, hχ0, Ψ, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact actualFreeProduct_toFun_zero m e χ hχ0
  · intro z hz
    exact hz.1
  · intro z hz
    change z ∈ P.source ∩ U at hz
    change (z ∈ C ↔ P.toFun z ∈ complexCoordinatePlane (m+e) k)
    have hCC0 : z ∈ C ↔ z ∈ C0 := by
      change z ∈ C ↔ z ∈ C ∩ U
      exact ⟨fun hzC => ⟨hzC, hz.2⟩, fun hzC => hzC.1⟩
    exact hCC0.trans (hPflat z hz.1)
  · intro z j
    exact actualFreeProduct_toFun_essentialCoordinate m e χ z j
  · intro z j
    exact actualFreeProduct_invFun_essentialCoordinate m e χ z j

end
end Hironaka.HironakaActualFreeProductFlattening
