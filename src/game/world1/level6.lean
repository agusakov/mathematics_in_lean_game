import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 6: `rw` with partial information

You can also provide *partial* information.
For example, `mul_comm a` matches any pattern of the form
`a * ?` and rewrites it to `? * a`.

Try doing this example with only one argument.
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example6 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin [maths_in_lean_game]




  sorry
end

end calculating -- hide