"""
Regex patterns for parsing Lean declarations.

This module centralizes all regex patterns used for identifying and parsing
different types of Lean declarations.
"""

import re

# =============================================================================
# Lean Identifier Patterns
# =============================================================================

# Lean identifier character classes supporting Unicode
# Includes: subscripts (₀-₉ₐ-ₜᵢᵣᵥ), Greek (α-ωΑ-Ω), Mathematical symbols (ℝℂℕℤℚℓ𝕜),
# Mathematical Script (𝒜-𝓏, range U+1D49C-U+1D4CF, includes 𝒰), Mathematical Double-Struck (𝔸-𝕫)
LEAN_ID_CHAR = r"[A-Za-z0-9_'₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫?!]"
LEAN_ID_START = r"[A-Za-z_α-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫]"

# Quoted name pattern (for reserved words used as identifiers)
QUOTED_NAME = r'«[^»]+»'

# Regular identifier pattern (may include dots for qualified names)
REGULAR_NAME = rf'{LEAN_ID_START}{LEAN_ID_CHAR}*(?:\.{LEAN_ID_START}{LEAN_ID_CHAR}*)*'

# Simple identifier (no dots)
SIMPLE_NAME = rf'{LEAN_ID_START}{LEAN_ID_CHAR}*'


# =============================================================================
# Modifier Patterns
# =============================================================================

# Common visibility/behavior modifiers
# Note: 'local' is a valid Lean modifier for instances and other declarations
VISIBILITY_MODIFIERS = r'(?:private\s+|protected\s+|scoped\s+|local\s+)*'
BEHAVIOR_MODIFIERS = r'(?:partial\s+|noncomputable\s+|unsafe\s+)*'
ALL_MODIFIERS = r'(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+|scoped\s+|local\s+)*'

# Attribute pattern (e.g., @[simp], @[ext])
ATTRIBUTE_PREFIX = r'(?:@\[[^\]]+\]\s*)*'


# =============================================================================
# Declaration Patterns
# =============================================================================

def build_main_decl_pattern():
    """Build pattern for main declaration types (theorem, def, structure, etc.).

    Note: 'class abbrev' and 'class inductive' are combined keywords in Lean 4,
    so we need to match them before standalone 'class' to avoid capturing
    'abbrev'/'inductive' as the declaration name.
    """
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{ALL_MODIFIERS}'
        r'(theorem|lemma|def|abbrev|structure|inductive|class\s+inductive|class\s+abbrev|class|opaque|axiom|constant)\s+'
        rf'({QUOTED_NAME}|{REGULAR_NAME})'
    )


def build_instance_named_pattern():
    """Build pattern for named instances: instance foo : ..."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{ALL_MODIFIERS}'
        r'instance\s+'
        r'(?:\(priority\s*:=\s*[^)]+\)\s+)?'  # Optional (priority := ...)
        rf'({QUOTED_NAME}|{SIMPLE_NAME})'  # Instance name
        r'.*?:'  # Parameters until colon
    )


def build_instance_anon_pattern():
    """Build pattern for anonymous instances: instance : TypeClass ..."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{ALL_MODIFIERS}'
        r'instance\s*'
        r'(?:\(priority\s*:=\s*[^)]+\)\s*)?'
        r'(?:[\[\(\{]|:)'  # Must start with implicit param or colon
    )


def build_instance_multiline_pattern():
    """Build pattern for multi-line instances (colon on subsequent line)."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{ALL_MODIFIERS}'
        r'instance\s+'
        r'(?:\(priority\s*:=\s*[^)]+\)\s+)?'
        rf'({REGULAR_NAME})'  # Instance name (may have dots)
        r'(?![^:]*:)'  # Negative lookahead: no colon on this line
    )


def build_macro_pattern():
    """Build pattern for macro declarations."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{VISIBILITY_MODIFIERS}'
        r'macro(?::\w+)?\s+'  # Optional :precedence suffix
        r'(?:\(name\s*:=\s*(\w+)\)\s+)?'  # Optional (name := foo)
        r'(?:\(priority\s*:=\s*[^)]+\)\s+)?'  # Optional (priority := ...)
        r'(?:\w+(?::\w+(?::\d+)?)?(?:\s*,\s*\*?)?\s+)*'  # Variable bindings
        rf'(?:"([^"]+)"|({SIMPLE_NAME}))'  # String literal or identifier
    )


def build_syntax_pattern():
    """Build pattern for syntax declarations."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{VISIBILITY_MODIFIERS}'
        r'syntax(?::\w+)?\s+'  # Optional :max, :arg suffix
        r'(?:\(name\s*:=\s*(\w+)\)\s+)?'  # Optional (name := foo)
        rf'(?:\[[^\]]+\]\s+)?'  # Optional [priority]
        rf'(?:"([^"]+)"|({SIMPLE_NAME}))'  # String literal or identifier
    )


def build_syntax_multiline_name_pattern():
    """Build pattern for multi-line syntax with (name := ...) at end of line."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{VISIBILITY_MODIFIERS}'
        r'syntax(?::\w+)?\s+'
        r'\(name\s*:=\s*(\w+)\)\s*$'
    )


def build_notation_pattern():
    """Build pattern for notation/infix/prefix/postfix declarations."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        r'(?:scoped\s+)?'
        r'(notation|infix[rl]?|prefix|postfix)'
        r'(?:\s*:\s*\w+)?\s+'  # Optional : priority
        r'(?:\([^)]*\)\s+)?'  # Optional (priority := ...)
        r'(?:\w+(?::\w+)?\s+)*'  # Optional variable bindings
        r'"([^"]+)"'
    )


def build_notation_multiline_pattern():
    """Build pattern for multi-line notation (string on next line)."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        r'(?:scoped\s+)?'
        r'(notation|infix[rl]?|prefix|postfix)'
        r'(?:\s*:\s*(\w+))?\s*$'  # Priority at end of line
    )


def build_elab_pattern():
    """Build pattern for elab declarations."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{VISIBILITY_MODIFIERS}'
        r'elab(?::\w+)?\s+'
        r'(?:\([^)]*\)\s+)?'  # Optional (name := ...) attribute
        rf'(?:"([^"]+)"|({SIMPLE_NAME}))'
    )


def build_elab_multiline_pattern():
    """Build pattern for multi-line elab with (name := ...) at end of line."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{VISIBILITY_MODIFIERS}'
        r'elab(?::\w+)?\s+'
        r'\(name\s*:=\s*(\w+)\)\s*$'
    )


def build_macro_rules_pattern():
    """Build pattern for macro_rules declarations."""
    return re.compile(rf'^\s*{ATTRIBUTE_PREFIX}(?:scoped\s+)?macro_rules\b')


def build_elab_rules_pattern():
    """Build pattern for elab_rules declarations."""
    return re.compile(rf'^\s*{ATTRIBUTE_PREFIX}elab_rules\b')


def build_declare_syntax_cat_pattern():
    """Build pattern for declare_syntax_cat declarations."""
    return re.compile(rf'^\s*declare_syntax_cat\s+({SIMPLE_NAME})')


def build_initialize_named_pattern():
    """Build pattern for named initialize/builtin_initialize blocks."""
    return re.compile(rf'^\s*(builtin_initialize|initialize)\s+({SIMPLE_NAME})\s*')


def build_initialize_anon_pattern():
    """Build pattern for anonymous initialize/builtin_initialize blocks."""
    return re.compile(r'^\s*(builtin_initialize|initialize)\s*$')


def build_variable_pattern():
    """Build pattern for variable declarations."""
    return re.compile(r'^\s*variable\s+(.+)')


def build_import_pattern():
    """Build pattern for import declarations."""
    return re.compile(r'^\s*import\s+(.+)')


def build_open_pattern():
    """Build pattern for open declarations."""
    return re.compile(r'^\s*open\s+(.+)')


def build_namespace_pattern():
    """Build pattern for namespace declarations."""
    return re.compile(r'^\s*namespace\s+([\w.]+)')


def build_section_pattern():
    """Build pattern for section declarations.

    Handles:
    - `section` (anonymous)
    - `section Foo` (named)
    - `noncomputable section` (anonymous with modifier)
    - `noncomputable section Foo` (named with modifier)

    Requires whitespace or end-of-line after 'section' to avoid matching
    variables like 'sections'.
    """
    return re.compile(r'^\s*(?:noncomputable\s+)?section(?:\s+([\w.]+)|\s*$)')


def build_end_pattern():
    """Build pattern for end declarations.

    Requires whitespace or end-of-line after 'end' to avoid matching
    identifiers like 'endpoint'.
    """
    return re.compile(r'^\s*end(?:\s+([\w.]+)|\s*$)')


def build_multiline_decl_pattern():
    """Build pattern for multi-line declarations (keyword alone at end of line)."""
    return re.compile(
        rf'^\s*{ATTRIBUTE_PREFIX}'
        rf'{ALL_MODIFIERS}'
        r'(instance|syntax)\s*$'
    )


def build_attribute_only_pattern():
    """Build pattern for lines containing only attributes."""
    return re.compile(r"^\s*@\[[^\]]+\]\s*$")


def build_doc_comment_pattern():
    """Build pattern for doc comment starts."""
    return re.compile(r"^\s*/--")


def build_boundary_pattern():
    """Build pattern for declaration boundaries (things that terminate declarations).

    Note: import, open, namespace, section, end, variable are captured as chunks,
    not just boundaries. omit/include are boundaries because they belong to the
    NEXT declaration. export is now captured as a chunk for alias tracking.
    """
    return re.compile(
        r'^\s*(universe|set_option|omit|include|'
        r'#check|#eval|#print|#reduce|attribute|mutual|nonmutual)\b'
    )


def build_export_pattern():
    """Build pattern for export statements.

    Matches: export Namespace (name1 name2 ...)
    Used to track alias mappings where bare names resolve to qualified names.
    """
    return re.compile(
        rf'^\s*export\s+({REGULAR_NAME})\s*\(([^)]+)\)'
    )


def build_constructor_pattern():
    """Build pattern for inductive constructors."""
    return re.compile(rf'^\s*\|\s*({SIMPLE_NAME})', re.MULTILINE)


def build_field_pattern():
    """Build pattern for structure fields."""
    return re.compile(rf"^\s*({SIMPLE_NAME})\s*(?:[(<{{].*)?:", re.MULTILINE)


# =============================================================================
# Veil DSL Patterns (repo-specific)
# =============================================================================
# The following patterns are specific to the veil repository, which uses a custom
# DSL for defining distributed systems specifications. These patterns allow us to
# index the generated definitions so they can be resolved as dependencies.
#
# See: https://github.com/verse-lab/veil
# DSL definitions are in: Veil/DSL/Specification/Lang.lean

def build_veil_invariant_pattern():
    """Build pattern for veil invariant/safety declarations.

    Matches:
      invariant [name] prop
      safety [name] prop

    These generate definitions like:
      @[invDef, invSimp] def name ... : Prop := prop

    This is veil-specific DSL syntax for defining system invariants.
    """
    return re.compile(
        rf'^\s*(invariant|safety)\s+\[({SIMPLE_NAME})\]'
    )


def build_veil_action_pattern():
    """Build pattern for veil action declarations.

    Matches:
      action name (params) = { ... }
      action name = { ... }

    These generate definitions like:
      def name ... and def name.tr ...

    This is veil-specific DSL syntax for defining system actions/transitions.
    """
    return re.compile(
        rf'^\s*action\s+({SIMPLE_NAME})\s*(?:\([^)]*\))?\s*='
    )
