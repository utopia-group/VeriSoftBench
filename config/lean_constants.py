"""
Lean language constants for static analysis.

This file contains centralized definitions of Lean language constructs:
- Keywords (syntax elements)
- Built-in constants (fundamental types)
- Tactic keywords (proof commands)
- Auto-generated name patterns (Lean-generated suffixes)

NOTE: This file contains ONLY known Lean language constructs, NOT heuristics.
Filtering based on name patterns or length has been removed in favor of
proper scope/environment tracking during resolution.
"""

# Lean language keywords - these are syntax elements, not user-defined identifiers
LEAN_KEYWORDS = {
    # Declaration keywords
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance", "class", "partial",
    "variable", "variables", "section", "namespace", "end", "mutual", "deriving",
    "import", "export", "private", "protected", "noncomputable", "unsafe", "opaque",
    "axiom", "constant", "extends", "example", "attribute", "local",
    # Notation/syntax keywords
    "macro", "notation", "syntax", "elab", "macro_rules", "declare_syntax_cat",
    "infix", "infixr", "infixl", "prefix", "postfix", "scoped",
    # Control flow
    "match", "with", "by", "where", "fun", "let", "in", "if", "then", "else",
    "for", "while", "ref",
    "do", "have", "case", "calc", "show", "from", "hiding", "renaming",
    "at", "using", "only", "termination_by", "decreasing_by",
    # Tactic keywords that appear as part of syntax
    "as", "to",
    # Built-in types/values
    "forall", "exists", "Prop", "Type", "Sort", "set_option", "open",
    "theory", "sorry", "admit", "rfl", "True", "False",
    # Note: `and`, `or`, `not`, `iff`, `eq` are kept as keywords because they're
    # Lean syntax/builtins that can't be user-defined at the same level.
    # `ne` was removed because it can be shadowed by user definitions (e.g., "neutral form")
    # and should be resolved via environment-aware resolution instead.
    "and", "or", "not", "iff", "eq",
    "return", "some", "none", "pure", "this", "self"
}

# Contextual keywords - these are only keywords in specific contexts (e.g., Aesop attributes)
# and can be valid user-defined identifiers elsewhere (e.g., `add` in `AddPCM.add`)
# These should NOT be filtered during identifier extraction, but may be filtered
# when detected in their specific syntactic contexts (e.g., inside @[aesop ...])
AESOP_CONTEXTUAL_KEYWORDS = {
    "add", "safe", "norm", "constructors", "forward", "destruct",
}
# Note: `unsafe`, `unfold`, `cases` are already true keywords/tactics and remain in their sets

# Built-in constants - fundamental Lean/Mathlib types that are not user-defined
LEAN_BUILTIN_CONSTANTS = {
    'and', 'or', 'not', 'iff', 'eq', 'true', 'false', 'ite',
    'True', 'False', 'Prop', 'Type', 'Sort'
}

# Tactic keywords - these are proof commands, not user-defined dependencies
TACTIC_KEYWORDS = {
    # Basic tactics
    "rw", "simp", "apply", "exact", "refine", "intro", "intros", "cases",
    "induction", "constructor", "left", "right", "split", "existsi", "use",
    "have", "show", "calc", "assumption", "trivial", "contradiction",
    # Advanced tactics
    "ring", "linarith", "omega", "decide", "native_decide", "norm_num", "norm_cast",
    "push_neg", "contrapose", "by_contra", "exfalso", "by_cases",
    "congr", "ext", "funext", "subst", "revert", "generalize", "specialize",
    "obtain", "rcases", "rintro", "unfold", "delta", "change", "convert",
    # Control tactics
    "swap", "rotate", "clear", "rename", "rename_i", "first", "repeat", "try",
    "all_goals", "any_goals", "focus", "done",
    # Simp variants
    "simp_all", "simp_rw", "dsimp", "simpa", "field_simp", "ring_nf",
    # Search tactics
    "rw_search", "library_search", "hint", "suggest", "finish", "aesop",
    # Logic tactics
    "tauto", "cc",
    # Arithmetic tactics
    "abel", "polyrith", "nlinarith", "positivity", "push_cast", "mod_cast",
    # Relation tactics
    "symm", "trans", "refl", "rel", "gcongr",
    # Instance tactics
    "infer_instance", "inferInstance",
    # Other tactics
    "set", "conv", "norm_num_ext", "interval_cases",
    "wlog", "choose", "contravariant", "covariant", "filter_upwards",
    # Additional tactics found in repos
    "generalizing", "suffices", "injection", "grind", "nth_rw", "reduceIte",
    "split_ifs", "solve_by_elim", "subst_eqs", "simp_wf", "prove_termination",
    "transitivity", "induction'", "cases'", "refine'", "congr!",
    "enter", "conv_lhs", "conv_rhs", "rotate_left", "rotate_right", "on_goal",
    "repeat'", "guard_msgs", "ac_rfl", "and_intros", "apply_assumption", "apply_fun",
    "injections", "subst_vars", "fin_cases", "classical", "split_ands",
    "nomatch", "maxHeartbeats", "linter", "print", "apply_rules",
    # Bang variants of tactics (Mathlib/Std)
    "apply!", "exact!", "simp!", "rfl!", "rw!",
    # Solver/convenience tactics
    "solve", "easy", "trivial!", "decide!", "aesop?",
    # Iris separation logic tactics
    "iintro", "iexact", "ispecialize", "istart", "istop", "irename", "iclear",
    "isplit", "isplitl", "isplitr", "icases", "ipose", "iassumption",
    # BitVector tactics
    "bv_generalize", "bv_multi_width", "bv_omega", "bv_decide", "bv_normalize",
    # MLIR/LLVM tactics
    "simp_alive_peephole", "simp_alive", "simp_llvm",
    # SLLVM tactics (lean-mlir)
    "simp_peephole", "simp_sllvm", "simp_sllvm_case_bash", "simp_sllvm_split",
}

# Patterns for auto-generated names that should be skipped
# These are generated by Lean for structures, inductives, etc. - NOT heuristics
AUTO_GENERATED_SUFFIXES = {
    ".eq_1", ".eq_2", ".eq_3",  # Structure equality
    ".rec", ".recOn", ".casesOn", ".below", ".brecOn",  # Recursors
    ".inj", ".injEq", ".noConfusion", ".noConfusionType",  # Injection
    ".sizeOf_spec",  # Size proofs
}
