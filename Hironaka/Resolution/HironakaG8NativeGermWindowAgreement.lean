import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualIdealPresheaf
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism

/-! Equality of genuine adapted ideals produces equality of whole coherent
marked records on a smaller native open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeGermWindowAgreement
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient MarkedIdeals
  MarkedIdealBiholomorphism HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothSubmersionGermIdealColon

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

private theorem eventual_mem_inclusion {A B : GermIdeal n X}
    (hA : A.IsCoherent) (hB : B.IsCoherent) {x : X}
    (h : ∀ f, A.mem x f → B.mem x f) :
    ∀ᶠ z in 𝓝 x, ∀ f, A.mem z f → B.mem z f := by
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hA x
  have hg (i : Fin s) : A.mem x (G i) := by
    apply (hgen x hx (G i)).mpr
    exact isInSpanAt_self ⟨i,rfl⟩
      (CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hx)
  have hAll : ∀ᶠ z in 𝓝 x, ∀ i, B.mem z (G i) :=
    eventually_all.mpr fun i => coherent_original_membership_eventually B hB x _ (h _ (hg i))
  filter_upwards [hU.mem_nhds hx, hAll] with z hz hMembers f hf
  apply HomogenizedIdeal.mem_of_isInSpanAt hB
  refine ((hgen z hz f).mp hf).mono ?_
    -- The local finite generators of A belong to B throughout this window.
  rintro _ ⟨i,rfl⟩
  exact hMembers i

/-- For two actual coherent ideals in exactly the same adapted chart, an
equality of entire adapted stalks persists on an actual ambient open. -/
theorem exists_open_whole_ideal_agreement_of_adaptedIdeal_eq
    {A B : GermIdeal n X} (hA : A.IsCoherent) (hB : B.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (h : adaptedIdeal A x Φ hΦ0 = adaptedIdeal B x Φ hΦ0)
    (U : Opens X) (hx : x ∈ U) :
    ∃ D : Opens X, x ∈ D ∧ D ≤ U ∧
      ∀ z ∈ D, ∀ f, A.mem z f ↔ B.mem z f := by
  have hAB (f : X → ℂ) (hf : A.mem x f) : B.mem x f := by
    have hHol := holomorphicAt_of_mem_coherent A hA hf
    exact (mem_adaptedIdeal_iff B hB x Φ hΦ0 f hHol).mp
      (h ▸ (mem_adaptedIdeal_iff A hA x Φ hΦ0 f hHol).mpr hf)
  have hBA (f : X → ℂ) (hf : B.mem x f) : A.mem x f := by
    have hHol := holomorphicAt_of_mem_coherent B hB hf
    exact (mem_adaptedIdeal_iff A hA x Φ hΦ0 f hHol).mp
      (h.symm ▸ (mem_adaptedIdeal_iff B hB x Φ hΦ0 f hHol).mpr hf)
  obtain ⟨V,hV,hOpen,hxV⟩ := mem_nhds_iff.mp
    ((eventual_mem_inclusion hA hB hAB).and (eventual_mem_inclusion hB hA hBA))
  refine ⟨⟨V ∩ U, hOpen.inter U.isOpen⟩, ⟨hxV,hx⟩, fun z hz => hz.2, ?_⟩
  exact fun z hz f => ⟨(hV hz.1).1 f, (hV hz.1).2 f⟩

/-- Equality in a common adapted chart gives literal equality of the two
restricted records, with all carrier and boundary positions retained. -/
theorem exists_open_marked_record_agreement_of_adaptedIdeal_eq
    {Q P : MarkedIdeal n X} (hQ : Q.ideal.IsCoherent) (hP : P.ideal.IsCoherent)
    (hN : Q.N = P.N) (hE : Q.E = P.E) (hd : Q.d = P.d) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (h : adaptedIdeal Q.ideal x Φ hΦ0 = adaptedIdeal P.ideal x Φ hΦ0)
    (U : Opens X) (hx : x ∈ U) :
    ∃ D : Opens X, x ∈ D ∧ D ≤ U ∧
      MarkedIdeal.pullback (Subtype.val : D → X) Q =
        MarkedIdeal.pullback (Subtype.val : D → X) P := by
  obtain ⟨D,hxD,hDU,hEq⟩ := exists_open_whole_ideal_agreement_of_adaptedIdeal_eq
    hQ hP x Φ hΦ0 h U hx
  refine ⟨D,hxD,hDU,?_⟩
  have hI : GermIdeal.pullback (m := n) (Subtype.val : D → X) Q.ideal =
      GermIdeal.pullback (m := n) (Subtype.val : D → X) P.ideal := by
    apply GermIdeal.ext
    funext z f
    apply propext
    rw [GermIdeal.mem_pullback_iff, GermIdeal.mem_pullback_iff]
    exact ⟨fun hf => hf.mono (by rintro _ ⟨g,hg,rfl⟩; exact ⟨g,(hEq _ z.property _).mp hg,rfl⟩),
      fun hf => hf.mono (by rintro _ ⟨g,hg,rfl⟩; exact ⟨g,(hEq _ z.property _).mpr hg,rfl⟩)⟩
  cases Q
  cases P
  simp only [MarkedIdeal.pullback] at *
  congr

end
end Hironaka.HironakaG8NativeGermWindowAgreement
