import Mathlib.Tactic.Ring

-- Exact affine coordinates for the corrected A_i=(-i+1,n-i).
theorem c_path_start_coordinates (n i : ℤ) :
    n - (-i + 1) + (n - i) = 2*n - 1 ∧
    n - (-i + 1) - (n - i) = 2*i - 1 := by
  constructor <;> ring

-- A right/down rectangular lattice step becomes an allowed diagonal step.
theorem c_right_step (n x y : ℤ) :
    n - (x+1) + y = (n-x+y)-1 ∧
    n - (x+1) - y = (n-x-y)-1 := by
  constructor <;> ring

theorem c_down_step (n x y : ℤ) :
    n - x + (y-1) = (n-x+y)-1 ∧
    n - x - (y-1) = (n-x-y)+1 := by
  constructor <;> ring

#print axioms c_path_start_coordinates
#print axioms c_right_step
#print axioms c_down_step
