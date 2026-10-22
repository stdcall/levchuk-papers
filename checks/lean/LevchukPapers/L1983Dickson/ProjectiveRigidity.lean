import Mathlib.Tactic.LinearCombination

/- Printed pp.422–423, fixed-point equation (2) and property Д).
The determinant restriction of PGL2 is unnecessary for the polynomial
calculation. For an invertible matrix the scalar obtained is nonzero.
The second lemma handles a triple containing infinity, including F2. -/
namespace LevchukPapers.L1983Dickson

theorem three_affine_fixed_points {F : Type*} [Field F]
    (a b c d x y z : F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : c*x^2+(d-a)*x-b=0)
    (hy : c*y^2+(d-a)*y-b=0)
    (hz : c*z^2+(d-a)*z-b=0) : c=0 ∧ d=a ∧ b=0 := by
  have hxy' : (x-y)*(c*(x+y)+(d-a))=0 := by
    linear_combination hx-hy
  have hxz' : (x-z)*(c*(x+z)+(d-a))=0 := by
    linear_combination hx-hz
  have hp := (mul_eq_zero.mp hxy').resolve_left (sub_ne_zero.mpr hxy)
  have hq := (mul_eq_zero.mp hxz').resolve_left (sub_ne_zero.mpr hxz)
  have hcprod : c*(y-z)=0 := by linear_combination hp-hq
  have hc : c=0 := (mul_eq_zero.mp hcprod).resolve_right (sub_ne_zero.mpr hyz)
  have hd : d=a := by
    apply sub_eq_zero.mp
    linear_combination hp-(x+y)*hc
  have hb : b=0 := by simpa [hc,hd] using hx
  exact ⟨hc,hd,hb⟩

theorem infinity_two_fixed_points {F : Type*} [Field F]
    (a b c d x y : F) (hc : c=0) (hxy : x ≠ y)
    (hx : c*x^2+(d-a)*x-b=0)
    (hy : c*y^2+(d-a)*y-b=0) : c=0 ∧ d=a ∧ b=0 := by
  have hprod : (d-a)*(x-y)=0 := by
    linear_combination hx-hy-(x^2-y^2)*hc
  have hd : d=a := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxy))
  have hb : b=0 := by simpa [hc,hd] using hx
  exact ⟨hc,hd,hb⟩

end LevchukPapers.L1983Dickson

#print axioms LevchukPapers.L1983Dickson.three_affine_fixed_points
#print axioms LevchukPapers.L1983Dickson.infinity_two_fixed_points
