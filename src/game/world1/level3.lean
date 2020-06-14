import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 3: Another identity
-/

-- begin hide
/-
You can type the `ℝ` character as `\R` or `\real`
in the VS Code editor.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If your keyboard does not have a backslash,
you can change the leading character by changing the
`lean.input.leader` setting in VS Code. 
-/
-- end hide

/- Try proving these identities,
in each case replacing `sorry` by a tactic proof.
With the `rw` tactic, you can use a left arrow (`\l`)
to reverse an identity.
For example, `rw ← mul_assoc a b c`
replaces `a * (b * c)` by `a * b * c` in the current goal.
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example3 (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin [maths_in_lean_game]




  sorry
end

end calculating -- hide