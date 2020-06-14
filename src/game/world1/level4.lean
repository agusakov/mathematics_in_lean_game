import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 4: `rw` with no arguments

You can also use identities like `mul_assoc` and `mul_comm` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example4 (a b c : ℝ) : a * b * c = b * c * a :=
begin [maths_in_lean_game]
  rw mul_assoc,
  rw mul_comm
  
end

end calculating -- hide