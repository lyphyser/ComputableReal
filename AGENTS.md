# General Lean instructions
- Always check that your changes compile, even if not explicitly asked for, unless you are specifically told not to check
- To save time, only compile the specific file that is being changed, unless you are changing an API and need to use compilation errors elsewhere to find uses to change as well
- Try to solve all errors before compiling again, since compilation is slow
- Use lemmas and definitions from Std or Mathlib if possible
- If a proof is hard, you can temporarily replace it with a sorry. Fill out the sorry afterwards once it compiles
- Always fill out your sorries unless allowed to do otherwise
- Never replace value terms with 0 or default just to make things compile
- If you are doing a complex proof or filling out sorries, use the "trace_state" tactic to print the hypotheses and goal where you insert it (e.g. just before a sorry). If you don't see the output, add "-v" to the lake build command line
- Always run lake with TERM=dumb so it doesn't print redundant progress lines
- Name new definitions/theorems/variables according to Mathlib style and in general write code that would be suitable for inclusion in Std or Mathlib
- ALWAYS polish the code as described below once it compiles correctly and before showing it to me

## Polishing
After the change compiles, look for opportunities to polish, improve and simplify the code, and continue until the code seems perfect and terse. In particular:
- Replace non-terminal simps with simp only using the simp? tactic
- Replace identical match cases with a single one with multiple patterns
- Replace identical starts in goal proofs with <;> or all_goals
- Try to remove all dsimp and other defeq-only tactics, and see if it still compiles
- When there are some proof steps that are details or calculations, try to replace them with a single "grind" tactic invocation and see if it still compiles
- For each type ascriptions and type specifications for local variables and global aliases, try to remove it and see if it still compiles thanks to type inference
- Replace fun ... a => ... a with fun ... => ..., and do the same for defs and structure member functions
- For any specification of implicit parameters e.g. (a := ...), try to remove it and see if the code still compiles because the argument is inverted
- For each @, try to remive it in favor of haveI/letI or type ascriptions
- Remove "intro" tactics at the start of the proof, and instead name the argument in the declaration
- Inline local variables, helpers and lemmas used once if the definition is short or trivial
- Replace one-line tactic proofs with the term if it's shorter (especially the exact and rfl tactics)
- Replace refine with ?_ with an apply with just the lemma name
- Define helpers for remaining repeated code
- When multiple definitions have repeated instance or implicit parameters, or repeat complicated explicit parameters, reorder them so they are consecutive and wrap them in a section and replace them with a single variable line. Do this hierarchically if needed. Use "variable (a) in ..." or "variable {a} in ..." if parameters have the same name and types but different implicitness
- Use idiomatic letters for parameters matching Mathlib style
