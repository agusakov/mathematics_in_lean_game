import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 11: Variable declarations outside of theorems

Another trick is that we can declare variables once and forall outside
an example or theorem.
When Lean sees them mentioned in the statement of the theorem,
it includes them automatically.
-/

/-
Try proving this using what you know about multiple rewrites.
-/

variables a b c d e f : ℝ

/- Example : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
example (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin [maths_in_lean_game]
  



    sorry
end

end calculating -- hide