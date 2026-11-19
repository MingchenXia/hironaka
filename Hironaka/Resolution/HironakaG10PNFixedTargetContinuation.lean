import Hironaka.Resolution.HironakaG10PNFinalDomain

/-! Fixed-target uniform continuation for an ordinary original finitely presented module (lane G10P,
run 0080; the endpoints of `G10.PN.8.assemble`, `G10.PN.9` and `G10.PN.10`).  Blueprint:
`hironaka-g10-pn-fixed-target-continuation.tex`.

From ONLY an original open `U`, a natively finitely presented `F` on `U` and a point `p ∈ U`: the stalk
prime series, ALL prime models `B_i` (repetitions kept), the algebraic domain `Ω₀` of PN.5 and then the
final common open `V` of PN.6 are chosen; on the literal restriction `F|V` the restricted exact chain
with quotients the prime targets of the SAME `B_i` on `V` holds (PN.8), every prime target is
zero-stalk rigid at `p` on `V` (PN.7 on the fixed `V`), and hence (extension induction, PN.9) EVERY
map from ANY natively finite-type source to `F|V` whose stalk at `p` vanishes is zero.  `V` depends on
`F` and `p` only and precedes every source and every map.  No point evaluation is used on the
(possibly nilpotent) `F`; torsion, embedded and repeated primes and the zero module (`ℓ = 0`) are
included. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaG10PNFixedTargetContinuation

open HironakaChowNativePrimeSupportContinuation HironakaChowNativeModuleStalkExact
  HironakaNativeCyclicCokernelRestriction HironakaG10PNLayerStep HironakaG10PNRestrictionExact
  HironakaG10PNLayerIso HironakaG10PNExtensionInduction HironakaG10PNFinalDomain

noncomputable section

variable {n : ℕ}

/-- **Generic assembly on the final open.**  For a selected series `d`, prime models `B`, an original
open `Ω₀ ∋ p` inside every old domain and modules `Fr Ω` on every `Ω ⊆ Ω₀` carrying the restricted
chain onto the prime targets of the SAME `B_i` on `Ω`: ONE final open `p ∈ V ⊆ Ω₀` is chosen, on which
the chain holds, every support is irreducible, every prime target and `Fr V` itself are zero-stalk rigid
at `p` for the finite-type sources. -/
theorem fixed_target_continuation_of_chains {U : Opens (ComplexModel n)} {p : U}
    {M : ModuleCat.{0} (OriginalRingStalk U p)}
    (d : SelectedPrimeSeries (OriginalRingStalk U p) M)
    (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
    (Ω₀ : Opens (ComplexModel n)) (hpΩ₀ : p.val ∈ Ω₀)
    (hΩ₀B : ∀ j : Fin d.s.length, Ω₀ ≤ (B j).old.U)
    (Fr : ∀ Ω : Opens (ComplexModel n), Ω ≤ Ω₀ → OriginalModules Ω)
    (hall : ∀ (Ω : Opens (ComplexModel n)) (hΩ : Ω ≤ Ω₀),
      RestrictedChainOn d B Ω (fun j => hΩ.trans (hΩ₀B j)) d.s.length le_rfl (Fr Ω hΩ)) :
    ∃ (V : Opens (ComplexModel n)) (hpV : p.val ∈ V) (hVΩ₀ : V ≤ Ω₀),
      RestrictedChainOn d B V (fun j => hVΩ₀.trans (hΩ₀B j)) d.s.length le_rfl (Fr V hVΩ₀) ∧
      (∀ j : Fin d.s.length, IsComplexAnalyticallyIrreducible (n := n)
        (domainSupport (B j) V (hVΩ₀.trans (hΩ₀B j)))) ∧
      (∀ j : Fin d.s.length, ZeroStalkRigid V ⟨p.val, hpV⟩ (fun G => G.IsFiniteType)
        (primeTargetOnDomain (B j) V (hVΩ₀.trans (hΩ₀B j)))) ∧
      ZeroStalkRigid V ⟨p.val, hpV⟩ (fun G => G.IsFiniteType) (Fr V hVΩ₀) := by
  have hP : ∀ j : Fin d.s.length,
      (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1).IsPrime :=
    fun j => Ideal.comap_isPrime _ _
  obtain ⟨V, hfin⟩ := exists_final_common_domain hP B Ω₀ hpΩ₀ hΩ₀B
  obtain ⟨hpV, hfin⟩ := hfin
  obtain ⟨hVΩ₀, hV⟩ := hfin
  exact ⟨V, hpV, hVΩ₀, hall V hVΩ₀, fun j => (hV j).1, fun j => (hV j).2,
    rigid_of_restrictedChainOn d B V _ ⟨p.val, hpV⟩ (fun G => G.IsFiniteType)
      (fun j => (hV j).2) d.s.length le_rfl _ (hall V hVΩ₀)⟩

/-- **Fixed-target uniform continuation (G10.PN.10, with the assembled chain of G10.PN.8 and the
extension induction of G10.PN.9 on the final open).**  For an ordinary original natively finitely
presented `F` on `U` and `p ∈ U`: the series `d`, the prime models `B`, the algebraic domain
`p ∈ Ω₀ ⊆ U` (inside every old domain) and then ONE final original open `p ∈ V ⊆ Ω₀` are chosen before
any source, such that the literal restriction `F|V` carries the restricted exact chain onto the prime
targets of the SAME `B_i` on `V`; every support is irreducible on `V`; every prime target is
zero-stalk rigid at `p`; and every map `f : G ⟶ F|V` from a natively finite-type `G` with zero stalk at
`p` is zero. -/
theorem exists_original_fixed_target_continuation
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (d : SelectedPrimeSeries (OriginalRingStalk U p)
        ((nativeStalkFunctor (originalOpenStructureSheaf U) p).obj F))
      (B : ∀ j : Fin d.s.length, NativePrimeAllOpenCokernelData p.val
        (Ideal.comap (originalRestrictionStalkEquiv U p).toRingHom (d.P j).1))
      (Ω₀ : Opens (ComplexModel n)) (hΩ₀U : Ω₀ ≤ U) (hΩ₀B : ∀ j : Fin d.s.length, Ω₀ ≤ (B j).old.U)
      (V : Opens (ComplexModel n)) (hpV : p.val ∈ V) (hVΩ₀ : V ≤ Ω₀),
      RestrictedChainOn d B V (fun j => hVΩ₀.trans (hΩ₀B j)) d.s.length le_rfl
        ((restrictTo U V (hVΩ₀.trans hΩ₀U)).obj F) ∧
      (∀ j : Fin d.s.length, IsComplexAnalyticallyIrreducible (n := n)
        (domainSupport (B j) V (hVΩ₀.trans (hΩ₀B j)))) ∧
      (∀ j : Fin d.s.length, ZeroStalkRigid V ⟨p.val, hpV⟩ (fun G => G.IsFiniteType)
        (primeTargetOnDomain (B j) V (hVΩ₀.trans (hΩ₀B j)))) ∧
      ∀ (G : OriginalModules V), G.IsFiniteType →
        ∀ f : G ⟶ (restrictTo U V (hVΩ₀.trans hΩ₀U)).obj F,
          (nativeStalkFunctor (originalOpenStructureSheaf V) ⟨p.val, hpV⟩).map f = 0 → f = 0 := by
  obtain ⟨d, B, D, -, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, hall⟩ :=
    exists_original_restricted_chain_on n U F p
  exact ⟨d, B, Ω₀, hΩ₀D.trans hDU, fun j => hΩ₀D.trans (hDB j),
    fixed_target_continuation_of_chains d B Ω₀ hpΩ₀ (fun j => hΩ₀D.trans (hDB j))
      (fun Ω hΩ => (restrictTo U Ω (hΩ.trans (hΩ₀D.trans hDU))).obj F) hall⟩

/-- **Uniform continuation, compact form (G10.PN.10).**  For an ordinary original natively finitely
presented `F` on `U` and `p ∈ U` there is ONE original open `p ∈ V ⊆ U`, depending only on `F` and
`p`, such that every map from a natively finite-type module to the literal `F|V` whose stalk at `p`
vanishes is zero. -/
theorem exists_original_uniform_continuation
    (n : ℕ) (U : Opens (ComplexModel n)) (F : OriginalModules U)
    [hF : F.IsFinitePresentation] (p : U) :
    ∃ (V : Opens (ComplexModel n)) (hpV : p.val ∈ V) (hVU : V ≤ U),
      ∀ (G : OriginalModules V), G.IsFiniteType → ∀ f : G ⟶ (restrictTo U V hVU).obj F,
        (nativeStalkFunctor (originalOpenStructureSheaf V) ⟨p.val, hpV⟩).map f = 0 → f = 0 := by
  obtain ⟨d, B, D, -, hDU, hDB, Ω₀, hpΩ₀, hΩ₀D, hall⟩ :=
    exists_original_restricted_chain_on n U F p
  obtain ⟨V, hfin⟩ := fixed_target_continuation_of_chains d B Ω₀ hpΩ₀
    (fun j => hΩ₀D.trans (hDB j)) (fun Ω hΩ => (restrictTo U Ω (hΩ.trans (hΩ₀D.trans hDU))).obj F)
    hall
  obtain ⟨hpV, hfin⟩ := hfin
  obtain ⟨hVΩ₀, hfin⟩ := hfin
  exact ⟨V, hpV, hVΩ₀.trans (hΩ₀D.trans hDU), hfin.2.2.2⟩

end

end Hironaka.HironakaG10PNFixedTargetContinuation
