# General Lean instructions
- Always check that your changes compile, even if not explicitly asked for, unless you are specifically told not to check
- To save time, only compile the specific file that is being changed, unless you are changing an API and need to use compilation errors elsewhere to find uses to change as well
- Try to solve all errors before compiling again, since compilation is slow
- Use lemmas and definitions from Std or Mathlib if possible
- If a proof is hard, you can temporarily replace it with a sorry. Fill out the sorry afterwards once it compiles
- Always fill out your sorries unless allowed to do otherwise
- Never replace value terms with 0 or default just to make things compile
- If you are doing a complex proof or filling out sorries in the middle of a proof, use the "trace_state" tactic to print the hypotheses and goal where you insert it (e.g. just before a sorry) so you can know what you need to prove. If you do't see the output, add "-v" to the lake build command line
- Try to follow the style guidelines right away
- After the change compiles, ALWAYS improve to code to make sure that it follows the style guidelines, and also look for opportunities to polish, improve and simplify the code until the code seems perfect and terse, like the code in the Lean project itself and in Mathlib

## Style guidelines

- Mathlib style: follow the Mathlib style guide
- Idiomatic names: name new definitions/theorems/variables according to Mathlib style and in general write code that would be suitable for inclusion in Std or Mathlib
- Idiomatic type parameter letters: follow Mathlib style
- Don't pollute the global namespace: lut defs and theorems about a type defined in a file in a namespace with the same name as the type
- No non-terminal simps: replace non-terminal simps with simp only using the simp? tactic
- No identical match cases: replace them with a single one with multiple patterns
- No goal proofs with duplicated starts: use <;> or all_goals to apply those tactics to all goals
- No unnecessary dsimp: try to remove all dsimps, and see if it still compiles
- No proof details or calculations that could just be done by "grind": try to replace proof parts that seem trivial or only involve numeric or logical manipulations with a single "grind" tactic invocation and see if it still compiles
- No unnecessary type ascriptions or type specifications for local variables and global aliases: try to remove them and see if it still compiles thanks to type inference
- Eta-normal form: replace fun ... a => ... a with fun ... => ..., and do the same for defs and structure member functions
- No implicit parameters specifications: For any specification of implicit arguments e.g. (a := ...), try to remove it and see if the code still compiles because the argument is inverted
- No @ form: for each @, try to remive it in favor of haveI/letI or type ascriptions
- No "intro" tactics at the start of the proof: remove them and instead name the arguments in the declaration
- No unnecessary local variables, helpers and lemmas: inline those used once if the definition is short or trivial and if they aren't expected to be used in other files
- No "by exact": replace it with just the term
- No "by rfl": just use rfl instead
- No refine: replace refine with apply, removing all trailing ?_
- No code duplication: define helpers for repeated code
- No repetition in parameters: when multiple definitions have repeated instance or implicit parameters, or repeat complicated explicit parameters, reorder them so they are consecutive and wrap them in a section and replace them with a single variable line. Do this hierarchically if needed. Use "variable (a) in ..." or "variable {a} in ..." if parameters have the same name and types but different implicitness
