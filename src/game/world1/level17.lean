import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 15: Rewriting at hypothesis, `exact` tactic

We can also perform rewriting in an assumption in the context.
For example, `rw mul_comm a b at hyp` replaces `a*b` by `b*a`
in the assumption `hyp`.
-/

variables a b c d : ℝ

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example17 (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin [maths_in_lean_game]

  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a*d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp
  
end

/-
In the last step, the `exact` tactic can use `hyp` to solve the goal
because at that point `hyp` matches the goal exactly.
-/

end calculating -- hide