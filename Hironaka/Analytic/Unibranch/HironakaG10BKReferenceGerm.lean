import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianSchurMatrixFlat

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10BKReferenceGerm
open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart
  HironakaG10LocSheafExact HironakaG10FlatPrivilegedEuclidean
  Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
noncomputable section

theorem directExact_bk_germ_exact {n a r c : ℕ}
    {K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K]
    (hK : K ∈ closedPolydiscs n) (hU : IsOpen U) (hKU : K ⊆ U)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (G : Fin r → Fin c → holSubalgebra K)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hex : DirectExact G (restrictMatrix K hKU F hF))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ interior K)
    (u : Fin r → HolGerm (EuclideanSpace ℂ (Fin n)))
    (hu : Matrix.mulVecLin (fun i j => germAt z (F i j)) u = 0) :
    ∃ w, Matrix.mulVecLin (fun j l => germAt z (bkFun K G j l)) w = u := by
  classical
  have hzU : z ∈ U := hKU (interior_subset hz)
  have hFz (i j) : HolAt (F i j) z := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hF i j x hx).differentiableAt (hU.mem_nhds hx)
  have hGz (j l) : HolAt (bkFun K G j l) z := holAt_bkFun K G j l hz
  choose v hvh hvg using fun j => exists_germAt_eq (u j) z
  have hrel : IsRelationAt F z v := by
    refine ⟨hvh, fun i => ?_⟩
    have hh : HolAt (fun x => ∑ j, v j x * F i j x) z :=
      HolAt.sum Finset.univ (fun j _ => (hvh j).mul (hFz i j))
    apply (germAt_eq_zero_iff hh).mp
    rw [germAt_sum Finset.univ (fun j _ => (hvh j).mul (hFz i j))]
    simp only [germAt_mul (hvh _) (hFz i _), hvg]
    have hui := congrFun hu i
    change (∑ j, germAt z (F i j) * u j) = 0 at hui
    simpa [mul_comm] using hui
  obtain ⟨W, _hW, hKW, hWU, μ, _inst, σ, hσ⟩ :=
    (relationsTheoremA_closedPolydiscs n) K hK U hU hKU _ _ F hF
  obtain ⟨w, hwh, hw⟩ := isCombinationAt_of_bK_exact hKW
    (fun i j => (hF i j).mono hWU) hσ G hex.exact hz v hrel
  refine ⟨fun l => germAt z (w l), ?_⟩
  funext j
  have hh : HolAt (fun x => ∑ l, w l x * bkFun K G j l x) z :=
    HolAt.sum Finset.univ (fun l _ => (hwh l).mul (hGz j l))
  have heq := (germAt_eq_germAt_iff (hvh j) hh).mpr (by simpa [columns] using hw j)
  rw [germAt_sum Finset.univ (fun l _ => (hwh l).mul (hGz j l))] at heq
  simp only [germAt_mul (hwh _) (hGz j _), hvg] at heq
  change (∑ l, germAt z (bkFun K G j l) * germAt z (w l)) = u j
  simpa [mul_comm] using heq.symm
theorem directExact_bk_germ_comp {n a r c : ℕ}
    {K U : Set (EuclideanSpace ℂ (Fin n))} [CompactSpace K]
    (hU : IsOpen U) (hKU : K ⊆ U)
    (F : Fin a → Fin r → EuclideanSpace ℂ (Fin n) → ℂ)
    (G : Fin r → Fin c → holSubalgebra K)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hex : DirectExact G (restrictMatrix K hKU F hF))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ interior K)
    (w : Fin c → HolGerm (EuclideanSpace ℂ (Fin n))) :
    Matrix.mulVecLin (fun i j => germAt z (F i j))
      (Matrix.mulVecLin (fun j l => germAt z (bkFun K G j l)) w) = 0 := by
  classical
  have hzU : z ∈ U := hKU (interior_subset hz)
  have hFz (i j) : HolAt (F i j) z := by
    filter_upwards [hU.mem_nhds hzU] with x hx
    exact (hF i j x hx).differentiableAt (hU.mem_nhds hx)
  have hGz (j l) : HolAt (bkFun K G j l) z := holAt_bkFun K G j l hz
  have hprod (i l) : ∑ j, germAt z (F i j) * germAt z (bkFun K G j l) = 0 := by
    have hh : HolAt (fun x => ∑ j, F i j x * bkFun K G j l x) z :=
      HolAt.sum Finset.univ (fun j _ => (hFz i j).mul (hGz j l))
    have hv : ∀ᶠ x in 𝓝 z, (∑ j, F i j x * bkFun K G j l x) = 0 := by
      filter_upwards [isOpen_interior.mem_nhds hz] with x hx
      have hc := congrArg (fun q : holSubalgebra K => (q : C(K,ℂ)) ⟨x, interior_subset hx⟩) (hex.comp i l)
      simpa [restrictMatrix, bkFun, extendZero_of_mem K _ (interior_subset hx)] using hc
    have hg := (germAt_eq_zero_iff hh).mpr hv
    rw [germAt_sum Finset.univ (fun j _ => (hFz i j).mul (hGz j l))] at hg
    simpa only [germAt_mul (hFz i _) (hGz _ l)] using hg
  funext i
  change (∑ j, germAt z (F i j) * ∑ l, germAt z (bkFun K G j l) * w l) = 0
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← mul_assoc, hprod, zero_mul, Finset.sum_const_zero]
end
end Hironaka.Analytic.Unibranch.HironakaG10BKReferenceGerm
