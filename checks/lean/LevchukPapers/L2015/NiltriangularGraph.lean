import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Defs

/- th:l2015-niltriangular-lie-enumeration: three elementary steps of
   the central quotient construction. No ideal enumeration or Lie
   classification is formalized here. -/
namespace LevchukPapers2015Niltriangular

variable {K S W : Type*} [Field K]
  [AddCommGroup S] [Module K S] [AddCommGroup W] [Module K W]

theorem graph_has_trivial_vertical_kernel (f : S →ₗ[K] W) (w : W)
    (h : (0, w) ∈ f.graph) : w = 0 := by
  rw [LinearMap.mem_graph_iff] at h
  simpa only [map_zero] using h

theorem graph_maps_are_distinct (f g : S →ₗ[K] W)
    (h : f.graph = g.graph) : f = g := by
  ext s
  have hs : (s, f s) ∈ g.graph := by
    rw [← h, LinearMap.mem_graph_iff]
  exact (LinearMap.mem_graph_iff g (s, f s)).mp hs

theorem quotient_kernel_mem_iff (N : Submodule K W) (w : W) :
    N.mkQ w = 0 ↔ w ∈ N := by
  rw [Submodule.mkQ_apply]
  exact Submodule.Quotient.mk_eq_zero (p := N) (x := w)

end LevchukPapers2015Niltriangular

#print axioms LevchukPapers2015Niltriangular.graph_has_trivial_vertical_kernel
#print axioms LevchukPapers2015Niltriangular.graph_maps_are_distinct
#print axioms LevchukPapers2015Niltriangular.quotient_kernel_mem_iff
