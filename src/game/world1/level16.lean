import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 15: `calc` keyword

The following exercise is a little more challenging.
You can use the theorems listed underneath.
-/

variables a b c d : ℝ

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example16 (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
begin [maths_in_lean_game]




    sorry
end

/-
```#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a```
-/

end calculating -- hide