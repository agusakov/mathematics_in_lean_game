import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 15: `calc` keyword

Now try proving the same theorem you proved in Level 14,
only this time using a more structured `calc` proof:
-/

variables a b c d : ℝ

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example15 : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin [maths_in_lean_game]




  sorry
end

end calculating -- hide