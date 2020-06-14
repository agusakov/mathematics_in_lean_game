import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 10: Multiple rewrites

We now introduce some useful features of Lean.
First, multiple rewrite commands can be carried out
with a single command,
by listing the relevant identities within square brackets.

The command we want is 
`rw [h', ←mul_assoc, h, mul_assoc]`.

-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example10 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
        a * (b * e) = c * (d * f) :=
begin [maths_in_lean_game]
        
        rw [h', ←mul_assoc, h, mul_assoc]

end

/-
You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.
-/

end calculating -- hide