"""Shared utilities for file I/O and data processing."""

import json
import logging
from pathlib import Path
import re
from typing import Dict, List, Any, Optional
from config.paths import EVAL_INPUT_DIR, REPO_INDEX_DIR, RESULTS_DATA_DIR, LEAN_SRC_DIR


# ---------------------------------------------------------------------------
# Inlined helpers from analyze_results.py
# (prefixed with _ar_ or ar_ to avoid name clashes with utils' own helpers)
# ---------------------------------------------------------------------------

# Lean identifier character classes
LEAN_ID_CHARS = r"A-Za-z0-9_'?!₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒪"
LEAN_ID_START = r"A-Za-z_?!α-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒪"

_AR_LEAN_KEYWORDS = {
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance", "class", "partial",
    "match", "with", "by", "where", "fun", "let", "in", "if", "then", "else",
    "do", "have", "simp", "rw", "case", "intro", "intros", "exact", "apply",
    "refine", "forall", "exists", "Prop", "Type", "Sort", "set_option", "open",
    "namespace", "end", "attribute", "local", "macro", "notation", "example",
    "variable", "variables", "section", "mutual", "deriving", "hiding",
    "renaming", "calc", "show", "from", "theory", "sorry", "admit",
    "rfl", "True", "False", "and", "or", "not", "iff", "eq", "ne",
    "import", "export", "private", "protected", "noncomputable",
    "unsafe", "opaque", "axiom", "constant", "extends",
    "return", "some", "none", "pure"
}

_AR_TACTIC_KEYWORDS = {
    "rw", "simp", "apply", "exact", "refine", "intro", "intros", "cases",
    "induction", "constructor", "left", "right", "split", "existsi", "use",
    "have", "show", "calc", "ring", "linarith", "omega", "decide", "norm_num",
    "norm_cast", "push_neg", "contrapose", "by_contra", "exfalso", "trivial",
    "assumption", "contradiction", "congr", "ext", "funext", "subst", "revert",
    "generalize", "specialize", "obtain", "rcases", "rintro", "unfold", "delta",
    "change", "convert", "swap", "rotate", "clear", "rename", "simp_all", "simpa",
    "simp_rw", "rw_search", "library_search", "hint", "suggest", "finish", "classical",
    "tauto", "cc", "abel", "polyrith", "nlinarith", "positivity", "by_cases",
    "infer_instance", "rfl", "sorry", "admit", "auto", "aesop", "dsimp", "rewrite",
    "constructor", "refine", "exfalso", "congr", "grind", "try"
}


def _ar_collect_header_locals(header: str) -> set[str]:
    """Collect parameter names from the theorem header (before := or proof)."""
    names = set()
    # param_pattern matches identifiers in parameter positions
    param_pattern = re.compile(rf"[\(\{{]\s*([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)\s*:")
    for m in param_pattern.finditer(header):
        n = m.group(1)
        if n and n not in _AR_LEAN_KEYWORDS and n != "_":
            names.add(n)
    # Also capture standalone names before colon in header (e.g., theorem foo (x) : ...)
    tokens = re.findall(rf"\b([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)\b", header)
    for tok in tokens:
        if tok in _AR_LEAN_KEYWORDS or tok == "_":
            continue
        names.add(tok)
    return names


def _ar_collect_proof_locals(body: str) -> set[str]:
    """Collect names introduced by common binding tactics in the proof body."""
    locals_found = set()
    # intro / iintro / rintro
    for m in re.finditer(rf"\b(?:intro|iintro|rintro)\s+([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)", body):
        name = m.group(1)
        if name != "_" and name not in _AR_LEAN_KEYWORDS:
            locals_found.add(name)
    # cases / icases ... with ...
    for m in re.finditer(r"\b(?:cases|icases)\b[^\n]*?\bwith\b\s*([^\n;]+)", body):
        tail = m.group(1)
        parts = re.split(r"[,\s⟨⟩]+", tail)
        for p in parts:
            if re.match(rf"^[{LEAN_ID_START}][{LEAN_ID_CHARS}]*$", p) and p not in _AR_LEAN_KEYWORDS and p != "_":
                locals_found.add(p)
    # rename / irename ... => newname
    for m in re.finditer(rf"\b(?:rename|irename)\b[^\n]*?=>\s*([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)", body):
        name = m.group(1)
        if name != "_" and name not in _AR_LEAN_KEYWORDS:
            locals_found.add(name)
    # pose / ipose ... as name
    for m in re.finditer(rf"\b(?:pose|ipose)\b[^\n]*?\bas\s+([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)", body):
        name = m.group(1)
        if name != "_" and name not in _AR_LEAN_KEYWORDS:
            locals_found.add(name)
    # have h := / have h : ...
    for m in re.finditer(rf"\bhave\s+([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)\s*[:=]", body):
        name = m.group(1)
        if name != "_" and name not in _AR_LEAN_KEYWORDS:
            locals_found.add(name)
    # let h := / let h : ...
    for m in re.finditer(rf"\blet\s+([{LEAN_ID_START}][{LEAN_ID_CHARS}]*)\s*[:=]", body):
        name = m.group(1)
        if name != "_" and name not in _AR_LEAN_KEYWORDS:
            locals_found.add(name)
    # obtain <h1,h2> := ...
    for m in re.finditer(r"\bobtain\s+⟨([^⟩]+)⟩", body):
        names = re.split(r"[,\s]+", m.group(1))
        for n in names:
            if re.match(rf"^[{LEAN_ID_START}][{LEAN_ID_CHARS}]*$", n) and n != "_" and n not in _AR_LEAN_KEYWORDS:
                locals_found.add(n)
    return locals_found


def _ar_remove_comments(text: str) -> str:
    """Remove line and block comments from Lean code."""
    def _replace_block(match: re.Match) -> str:
        content = match.group(0)
        # Preserve line count
        return "\n" * content.count("\n")

    text = re.sub(r"/-.*?-/", _replace_block, text, flags=re.DOTALL)
    lines = []
    for line in text.splitlines():
        lines.append(line.split("--", 1)[0])
    return "\n".join(lines)


def ar_find_unwrapped_assign(text: str) -> int:
    """Find := that's not wrapped in parentheses. Returns -1 if not found."""
    paren_depth = 0
    i = 0
    while i < len(text) - 1:
        if text[i] == '(':
            paren_depth += 1
        elif text[i] == ')':
            paren_depth -= 1
        elif text[i:i+2] == ':=' and paren_depth == 0:
            return i
        i += 1
    return -1


def ar_extract_identifiers(header, body) -> set[str]:
    """Extract identifiers (including dotted) from Lean code, skipping keywords and tactics."""
    if not header:
        return set()

    cleaned = _ar_remove_comments(body)

    scope = set()
    scope.update(_ar_collect_header_locals(header))
    scope.update(_ar_collect_proof_locals(cleaned))

    # Pattern for dotted identifiers including special Unicode characters
    pattern = rf"\b[{LEAN_ID_START}][{LEAN_ID_CHARS}]*(?:\.[{LEAN_ID_START}][{LEAN_ID_CHARS}]*)*\b"
    ids = set()
    for m in re.finditer(pattern, cleaned):
        tok = m.group(0)
        # Skip both Lean keywords and tactic keywords
        if tok in _AR_LEAN_KEYWORDS or tok in _AR_TACTIC_KEYWORDS or tok in scope:
            continue
        ids.add(tok)
    return ids


def ar_get_proof_body(full_proof_str):
    start = ar_find_unwrapped_assign(full_proof_str)
    if start == -1:
        return full_proof_str.strip()
    return full_proof_str[start + 2 :].strip()


def ar_get_lemma_list(aux_lemmas_str):
    """Split aux_lemmas string into individual lemma/theorem declarations.
    Returns a list of strings, each containing one complete lemma/theorem."""
    if not aux_lemmas_str:
        return []

    # Find all positions where 'lemma' or 'theorem' keywords start
    lemmas = []
    pattern = r'\b(lemma|theorem)\b'
    matches = list(re.finditer(pattern, aux_lemmas_str))

    if not matches:
        return []

    # Extract each lemma/theorem from start position to next start position
    for i, match in enumerate(matches):
        start = match.start()
        # End is either the start of next lemma/theorem, or end of string
        end = matches[i + 1].start() if i + 1 < len(matches) else len(aux_lemmas_str)
        lemma_text = aux_lemmas_str[start:end].strip()
        if lemma_text:
            lemmas.append(lemma_text)

    return lemmas


# ---------------------------------------------------------------------------
# I/O helpers
# ---------------------------------------------------------------------------

def load_jsonl(filepath: Path) -> List[Dict[str, Any]]:
    """Load JSONL file into list of dictionaries."""
    data = []
    with open(filepath, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():  # Skip empty lines
                data.append(json.loads(line))
    return data

def save_jsonl(data: List[Dict[str, Any]], filepath: Path) -> None:
    """Save list of dictionaries to JSONL file."""
    with open(filepath, 'w', encoding='utf-8') as f:
        for entry in data:
            f.write(json.dumps(entry) + '\n')

def save_json(data: Dict[str, Any], filepath: Path) -> None:
    """Save dictionary to JSON file."""
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=4)

def load_txt_file(filepath: Path) -> str:
    """Load a text file and return its content as a string."""
    with open(filepath, 'r', encoding='utf-8') as f:
        return f.read()

def load_prompt_template(template_name: str, prompts_dir: Path) -> str:
    """Load a prompt template from Prompts/ directory."""
    return load_txt_file(prompts_dir / template_name)


# ---------------------------------------------------------------------------
# LLM output parsing
# ---------------------------------------------------------------------------

def get_lemmas_from_llm_output(output: str) -> str:
    # Find the LAST opening tag to avoid capturing garbage if LLM accidentally
    # mentioned the tag earlier (e.g., in reasoning section)
    opening_tag = "<lean4_invented_lemmas>"
    closing_tag = "</lean4_invented_lemmas>"

    last_open = output.rfind(opening_tag)
    if last_open == -1:
        return ""

    close_pos = output.find(closing_tag, last_open)
    if close_pos == -1:
        return ""

    content = output[last_open + len(opening_tag):close_pos]
    return content.strip()

def get_proof_from_llm_output(output: str) -> str:
    # Use LAST opening tag to avoid issues if LLM mentions tag in content
    opening_tag = "<lean4_proof>"
    closing_tag = "</lean4_proof>"

    last_open = output.rfind(opening_tag)
    if last_open == -1:
        return ""

    close_pos = output.find(closing_tag, last_open)
    if close_pos == -1:
        return ""

    content = output[last_open + len(opening_tag):close_pos]
    return content

def get_reasoning_from_llm_output(output: str) -> str:
    # Use LAST opening tag to avoid issues if LLM mentions tag in content
    opening_tag = "<reasoning>"
    closing_tag = "</reasoning>"

    last_open = output.rfind(opening_tag)
    if last_open == -1:
        return ""

    close_pos = output.find(closing_tag, last_open)
    if close_pos == -1:
        return ""

    content = output[last_open + len(opening_tag):close_pos]
    return content.strip()

def get_fixed_lemmas_from_llm_output(output: str) -> str:
    lemmas_pattern = r"<fixed_lean4_lemmas>(.*?)</fixed_lean4_lemmas>"
    lemmas_match = re.search(lemmas_pattern, output, re.DOTALL)
    if lemmas_match:
        return lemmas_match.group(1).strip()

    logging.warning("No fixed lemmas tags found in LLM output.")
    return ""

def get_fixed_proof_from_llm_output(output: str) -> str:
    # Extract and write the generated proof (from [LEAN4_PROOF] ... [/LEAN4_PROOF])
    proof_pattern = r'<fixed_lean4_thm_proof>(.*?)</fixed_lean4_thm_proof>'
    proof_match = re.search(proof_pattern, output, re.DOTALL)
    if proof_match:
        return proof_match.group(1)
    # If no tags found, assume entire generated_proof is the proof body
    logging.warning("No fixed proof tags found in LLM output.")
    return ""


# ---------------------------------------------------------------------------
# Lean assembly helpers
# ---------------------------------------------------------------------------

def _remove_comments(content: str) -> str:
    """
    Remove both single-line (--) and multi-line (/- ... -/) comments from Lean code.
    Handles nested multi-line comments correctly.
    """
    result = []
    i = 0
    n = len(content)

    while i < n:
        # Check for multi-line comment start
        if i < n - 1 and content[i:i+2] == '/-':
            # Skip the nested multi-line comment
            depth = 1
            i += 2
            while i < n and depth > 0:
                if i < n - 1 and content[i:i+2] == '/-':
                    depth += 1
                    i += 2
                elif i < n - 1 and content[i:i+2] == '-/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
        # Check for single-line comment
        elif i < n - 1 and content[i:i+2] == '--':
            # Skip to end of line
            while i < n and content[i] != '\n':
                i += 1
        else:
            result.append(content[i])
            i += 1

    return ''.join(result)


def _strip_lean_modifiers(line: str) -> str:
    """Strip leading Lean modifiers (noncomputable, private, protected) from a line."""
    modifiers = ('noncomputable', 'private', 'protected')
    changed = True
    while changed:
        changed = False
        for mod in modifiers:
            if line.startswith(mod + ' ') or line.startswith(mod + '\t'):
                line = line[len(mod):].lstrip()
                changed = True
    return line


def compute_required_ends(content: str) -> str:
    """
    Analyze content to find unclosed namespace/section blocks
    and return the required 'end' statements.

    Handles dotted namespace names correctly: ``namespace Foo.Bar`` is
    equivalent to ``namespace Foo`` then ``namespace Bar``, so each
    component is pushed individually.  Likewise ``end Foo.Bar`` closes
    ``Bar`` then ``Foo``.

    Args:
        content: Lean code that may contain unclosed blocks

    Returns:
        String containing the required 'end' statements, one per line
    """
    # Remove comments first to avoid false matches
    content = _remove_comments(content)

    # Track open blocks as a stack: each entry is (block_type, name)
    open_blocks = []

    # Process line by line to handle order correctly
    lines = content.split('\n')
    for line in lines:
        stripped = _strip_lean_modifiers(line.strip())

        # Check for namespace opening: "namespace Foo" or "namespace Foo.Bar"
        ns_match = re.match(r'^namespace\s+([\w.]+)', stripped)
        if ns_match:
            # Split dotted names: namespace Foo.Bar ≡ namespace Foo; namespace Bar
            for part in ns_match.group(1).split('.'):
                open_blocks.append(('namespace', part))
            continue

        # Check for section opening: "section Foo" or bare "section"
        sec_match = re.match(r'^section(?:\s+([\w.]+))?(?:\s|$)', stripped)
        if sec_match:
            name = sec_match.group(1)  # Could be None for bare section
            open_blocks.append(('section', name))
            continue

        # Check for mutual block opening (for mutually recursive definitions)
        if stripped == 'mutual' or stripped.startswith('mutual '):
            open_blocks.append(('mutual', None))
            continue

        # Check for end statement: "end Foo" or "end Foo.Bar" or bare "end"
        end_match = re.match(r'^end(?:\s+([\w.]+))?(?:\s|$)', stripped)
        if end_match:
            end_name = end_match.group(1)  # Could be None for bare end

            if end_name:
                # First try matching the full dotted name (for sections named "Foo.Bar")
                full_matched = False
                for i in range(len(open_blocks) - 1, -1, -1):
                    if open_blocks[i][1] == end_name:
                        open_blocks.pop(i)
                        full_matched = True
                        break
                if not full_matched:
                    # end Foo.Bar ≡ end Bar; end Foo — process parts in reverse
                    parts = end_name.split('.')
                    for part in reversed(parts):
                        for i in range(len(open_blocks) - 1, -1, -1):
                            if open_blocks[i][1] == part:
                                open_blocks.pop(i)
                                break
            else:
                # Bare "end" closes the most recent block
                if open_blocks:
                    open_blocks.pop()

    # Generate closing statements in reverse order (LIFO)
    ends = []
    for block_type, name in reversed(open_blocks):
        if name:
            ends.append(f"end {name}")
        else:
            ends.append("end")

    return "\n".join(ends)


def _has_unclosed_mutual(content: str) -> bool:
    """
    Check if content has an unclosed 'mutual' block.

    Uses proper stack-based tracking (same logic as compute_required_ends)
    to correctly handle cases where bare 'end' statements close other
    block types (like sections) before the mutual block.
    """
    content = _remove_comments(content)

    # Track open blocks as a stack
    open_blocks = []

    lines = content.split('\n')
    for line in lines:
        stripped = _strip_lean_modifiers(line.strip())

        # Check for namespace opening
        ns_match = re.match(r'^namespace\s+([\w.]+)', stripped)
        if ns_match:
            for part in ns_match.group(1).split('.'):
                open_blocks.append(('namespace', part))
            continue

        # Check for section opening
        sec_match = re.match(r'^section(?:\s+([\w.]+))?(?:\s|$)', stripped)
        if sec_match:
            name = sec_match.group(1)
            open_blocks.append(('section', name))
            continue

        # Check for mutual block opening
        if stripped == 'mutual' or stripped.startswith('mutual '):
            open_blocks.append(('mutual', None))
            continue

        # Check for end statement
        end_match = re.match(r'^end(?:\s+([\w.]+))?(?:\s|$)', stripped)
        if end_match:
            end_name = end_match.group(1)

            if end_name:
                # First try matching the full dotted name (for sections named "Foo.Bar")
                full_matched = False
                for i in range(len(open_blocks) - 1, -1, -1):
                    if open_blocks[i][1] == end_name:
                        open_blocks.pop(i)
                        full_matched = True
                        break
                if not full_matched:
                    parts = end_name.split('.')
                    for part in reversed(parts):
                        for i in range(len(open_blocks) - 1, -1, -1):
                            if open_blocks[i][1] == part:
                                open_blocks.pop(i)
                                break
            else:
                # Bare "end" closes the most recent block
                if open_blocks:
                    open_blocks.pop()

    # Check if any unclosed mutual blocks remain
    return any(block_type == 'mutual' for block_type, _ in open_blocks)


def _insert_before_unclosed_mutual(local_context: str, aux_lemmas: str) -> str:
    """
    Insert aux_lemmas before the unclosed 'mutual' keyword in local_context.

    When local_context ends with an unclosed mutual block, we need to insert
    aux_lemmas BEFORE the mutual keyword, not inside it. This is because:
    1. 'variable' declarations can't be inside mutual blocks
    2. Helper lemmas don't need to be mutually recursive with the target theorem

    Args:
        local_context: The local context ending with an unclosed mutual
        aux_lemmas: The auxiliary lemmas to insert

    Returns:
        Modified local_context with aux_lemmas inserted before the mutual keyword
    """
    lines = local_context.split('\n')

    # Find the line index of the unclosed mutual using stack tracking
    # We need to find the LAST mutual that isn't closed
    stack = []
    mutual_positions = []  # (line_idx, stack_depth_when_opened)

    for i, line in enumerate(lines):
        stripped = _remove_comments(line).strip()
        if not stripped:
            continue

        # Check for scope openers
        if stripped == 'mutual' or stripped.startswith('mutual '):
            mutual_positions.append((i, len(stack)))
            stack.append('mutual')
        elif stripped.startswith('section') and (len(stripped) == 7 or stripped[7:8].isspace()):
            stack.append('section')
        elif stripped.startswith('namespace') and (len(stripped) == 9 or stripped[9:10].isspace()):
            stack.append('namespace')
        # Check for end
        elif stripped == 'end' or stripped.startswith('end '):
            if stack:
                stack.pop()

    # Find the unclosed mutual (one where stack wasn't popped back to its level)
    unclosed_mutual_idx = -1
    for line_idx, depth in reversed(mutual_positions):
        # If current stack depth is greater than depth when this mutual was opened,
        # this mutual is still open
        if len(stack) > depth and 'mutual' in stack[depth:]:
            unclosed_mutual_idx = line_idx
            break

    if unclosed_mutual_idx == -1:
        # Fallback: just find the last 'mutual' line
        for i in range(len(lines) - 1, -1, -1):
            stripped = _remove_comments(lines[i]).strip()
            if stripped == 'mutual' or stripped.startswith('mutual '):
                unclosed_mutual_idx = i
                break

    if unclosed_mutual_idx == -1:
        # No mutual found, just return original with aux_lemmas appended
        return local_context + "\n\n" + aux_lemmas

    # Insert aux_lemmas before the mutual line
    before_mutual = '\n'.join(lines[:unclosed_mutual_idx])
    mutual_and_after = '\n'.join(lines[unclosed_mutual_idx:])

    return before_mutual + "\n\n" + aux_lemmas + "\n\n" + mutual_and_after


def _strip_organizational_wrappers(aux_lemmas: str) -> str:
    """
    Remove section and namespace wrappers from aux_lemmas.

    These are purely organizational and not needed for aux_lemmas to work.
    Note: mutual blocks are NOT stripped here because they may be semantically
    required (for mutually recursive lemmas).

    Args:
        aux_lemmas: The auxiliary lemmas content, possibly with scope wrappers

    Returns:
        The content with section/namespace wrappers removed
    """
    result = aux_lemmas

    # Keep stripping until no more changes
    changed = True
    while changed:
        changed = False
        for scope_type in ['section', 'namespace']:
            new_result = _unwrap_scope_block(result, scope_type)
            if new_result != result:
                result = new_result
                changed = True

    return result


def _strip_mutual_wrappers(aux_lemmas: str) -> str:
    """
    Remove all mutual wrappers from aux_lemmas.

    This should only be called when aux_lemmas will be inserted into a context
    that already has an unclosed mutual block (to avoid nested mutuals).
    The lemmas will still be in the outer mutual block, so mutual recursion
    will still work.

    Args:
        aux_lemmas: The auxiliary lemmas content, possibly with mutual wrappers

    Returns:
        The content with mutual wrappers removed
    """
    result = aux_lemmas

    # Keep stripping until no more changes
    changed = True
    while changed:
        changed = False
        new_result = _unwrap_scope_block(result, 'mutual')
        if new_result != result:
            result = new_result
            changed = True

    return result


def _unwrap_scope_block(content: str, scope_type: str) -> str:
    """
    Find and unwrap the first complete scope block of the given type.

    Args:
        content: The content possibly containing a scope block
        scope_type: One of 'mutual', 'section', 'namespace'

    Returns:
        The content with the first matching scope block unwrapped (or original if none found)
    """
    stripped = content.strip()
    if not stripped:
        return content

    lines = stripped.split('\n')

    # Find the first line matching the scope type
    scope_idx = -1
    for i, line in enumerate(lines):
        line_no_comment = _remove_comments(line).strip()
        if line_no_comment == scope_type or line_no_comment.startswith(scope_type + ' '):
            scope_idx = i
            break

    if scope_idx == -1:
        return content  # No matching scope block found

    # Find the matching 'end' using stack-based tracking
    stack = [scope_type]  # Start with the scope we found

    end_idx = -1
    for i in range(scope_idx + 1, len(lines)):
        line_no_comment = _remove_comments(lines[i]).strip()
        if not line_no_comment:
            continue

        # Check for scope openers that need explicit 'end'
        if line_no_comment == 'mutual' or line_no_comment.startswith('mutual '):
            stack.append('mutual')
        elif line_no_comment.startswith('section') and (len(line_no_comment) == 7 or line_no_comment[7:8].isspace()):
            stack.append('section')
        elif line_no_comment.startswith('namespace') and (len(line_no_comment) == 9 or line_no_comment[9:10].isspace()):
            stack.append('namespace')
        # Check for 'end'
        elif line_no_comment == 'end' or line_no_comment.startswith('end '):
            if stack:
                closed = stack.pop()
                if not stack and closed == scope_type:
                    # Found the matching end for our target scope
                    end_idx = i
                    break

    if end_idx == -1:
        return content  # Couldn't find matching end

    # Unwrap: remove the scope line and the matching 'end' line
    unwrapped_lines = lines[:scope_idx] + lines[scope_idx + 1:end_idx] + lines[end_idx + 1:]
    return '\n'.join(unwrapped_lines)


def get_remaining_mutual_content(full_file_content: str, thm_stmt: str, local_context: str) -> str:
    """
    Extract the remaining content of a mutual block after the target theorem.
    Replaces proof bodies with 'sorry' to avoid compilation issues while preserving
    the theorem signatures for forward reference resolution.

    Args:
        full_file_content: The complete Lean file content
        thm_stmt: The target theorem statement (used to find position)
        local_context: The content before the theorem (used to check if in mutual block)

    Returns:
        The remaining mutual block content with proofs replaced by 'sorry',
        or empty string if not in a mutual block
    """
    # Check if we're inside a mutual block
    if not _has_unclosed_mutual(local_context):
        return ""

    # Normalize
    full_file_content = full_file_content.replace("\\n", "\n")
    thm_stmt = thm_stmt.replace("\\n", "\n")

    # Find where the target theorem starts
    # Try to find the theorem statement in the file
    thm_stmt_clean = thm_stmt.strip()
    if thm_stmt_clean.endswith(":="):
        thm_stmt_clean = thm_stmt_clean[:-2].strip()

    thm_pos = full_file_content.find(thm_stmt_clean)
    if thm_pos == -1:
        # Try finding just the theorem name
        match = re.search(r'\b(theorem|lemma|def)\s+([\w.]+)', thm_stmt)
        if match:
            thm_name = match.group(2)
            pattern = rf'\b(theorem|lemma|def)\s+{re.escape(thm_name)}\b'
            thm_match = re.search(pattern, full_file_content)
            if thm_match:
                thm_pos = thm_match.start()
            else:
                return ""
        else:
            return ""

    # Find the end of this theorem's proof
    # Look for the next theorem/lemma/def declaration or 'end' at the same or lower indentation
    after_thm = full_file_content[thm_pos:]

    # Find the indentation of the target theorem
    line_start = full_file_content.rfind('\n', 0, thm_pos) + 1
    thm_indent = len(full_file_content[line_start:thm_pos]) - len(full_file_content[line_start:thm_pos].lstrip())

    # Find where this theorem's proof ends (next declaration at same indent level or 'end')
    lines = after_thm.split('\n')
    thm_end_line_idx = 0
    in_first_thm = True

    for i, line in enumerate(lines):
        if i == 0:
            continue  # Skip the first line (theorem declaration)

        stripped = line.strip()
        if not stripped:
            continue

        # Calculate indentation
        line_indent = len(line) - len(line.lstrip())

        # Check if this is a new declaration at the same or lower indentation level
        if line_indent <= thm_indent:
            decl_match = re.match(r'^(theorem|lemma|def|end)\b', stripped)
            if decl_match:
                thm_end_line_idx = i
                in_first_thm = False
                break

    if in_first_thm:
        # Couldn't find the end of the theorem, return empty
        return ""

    # Get everything from after the target theorem to 'end' (exclusive)
    remaining_lines = lines[thm_end_line_idx:]

    # Find where 'end' closes the mutual block
    end_idx = -1
    for i, line in enumerate(remaining_lines):
        stripped = line.strip()
        if stripped == 'end' or stripped.startswith('end '):
            # Check if this 'end' is at the mutual block level
            line_indent = len(line) - len(line.lstrip())
            if line_indent <= thm_indent:
                end_idx = i
                break

    if end_idx == -1:
        return ""

    # Extract the content between target theorem and 'end'
    mutual_content_lines = remaining_lines[:end_idx]
    mutual_content = '\n'.join(mutual_content_lines)

    # Replace proof bodies with 'sorry'
    # Pattern: := by ... (tactic proof) or := term (term proof)
    # We need to replace everything after := until the next theorem/lemma/def/end

    def replace_proofs_with_sorry(content: str) -> str:
        """Replace proof bodies with sorry while preserving theorem signatures."""
        result_lines = []
        lines = content.split('\n')
        i = 0
        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            # Check if this line starts a theorem/lemma/def
            decl_match = re.match(r'^(\s*)(theorem|lemma|def)\s+', line)
            if decl_match:
                indent = decl_match.group(1)
                # Collect the full declaration (might span multiple lines until :=)
                decl_lines = [line]
                while ':=' not in decl_lines[-1] and i + 1 < len(lines):
                    i += 1
                    decl_lines.append(lines[i])

                full_decl = '\n'.join(decl_lines)

                # Check if it has := by or just :=
                if ':= by' in full_decl or ':=by' in full_decl:
                    # Tactic proof - replace with := by sorry
                    decl_part = full_decl.split(':= by')[0] if ':= by' in full_decl else full_decl.split(':=by')[0]
                    result_lines.append(decl_part.rstrip() + ' := by sorry')
                elif ':=' in full_decl:
                    # Term proof - replace with := sorry
                    decl_part = full_decl.split(':=')[0]
                    result_lines.append(decl_part.rstrip() + ' := sorry')
                else:
                    # No proof body found, keep as is
                    result_lines.append(full_decl)
            else:
                # Not a declaration, skip (this could be continuation of a proof we're replacing)
                pass

            i += 1

        return '\n'.join(result_lines)

    result = replace_proofs_with_sorry(mutual_content)
    return result


def format_generated_lean(local_context: str, theorem_stmt: str, theorem_proof: str, aux_lemmas: str, suffix: str = "", remaining_mutual_content: str = "") -> str:
    local_context = local_context.replace("\\n", "\n")  # Normalize line endings
    theorem_stmt = theorem_stmt.replace("\\n", "\n")  # Normalize line endings
    lean_file_content = ""

    # if last non empty line of local_context is an attribute, paste the attribute before the theorem
    local_lines = local_context.splitlines()
    end_line_num = len(local_lines) - 1
    attr_line = ""
    for line in reversed(local_lines):
        if line.strip() == "":
            end_line_num -= 1
            continue
        if line.strip().startswith("@") and line.strip().endswith("]"):
            # end at current line
            local_context, attr_line = "\n".join(local_lines[:end_line_num]), "\n".join(local_lines[end_line_num:])
        break

    # Check if local_context has unclosed mutual BEFORE we modify it
    has_unclosed_mutual = _has_unclosed_mutual(local_context)

    # Process aux_lemmas
    processed_aux_lemmas = ""
    if aux_lemmas.strip():
        # Always strip section/namespace wrappers - these are purely organizational
        processed_aux_lemmas = _strip_organizational_wrappers(aux_lemmas)

        # NOTE: We do NOT strip mutual wrappers anymore when has_unclosed_mutual is true.
        # Instead, we insert aux_lemmas BEFORE the unclosed mutual, so they're outside it.
        # This way, if aux_lemmas have their own mutual block (for mutually recursive helpers),
        # it will be preserved and work correctly.

    # If local_context has unclosed mutual, insert aux_lemmas BEFORE the mutual keyword
    # This is because aux_lemmas may contain 'variable' declarations or other content
    # that can't be inside a mutual block
    if has_unclosed_mutual and processed_aux_lemmas.strip():
        # Find the last 'mutual' keyword in local_context and insert aux_lemmas before it
        local_context = _insert_before_unclosed_mutual(local_context, processed_aux_lemmas)
        lean_file_content += local_context
        lean_file_content += "\n\n"
    else:
        lean_file_content += local_context
        lean_file_content += "\n\n"

        if processed_aux_lemmas.strip():
            lean_file_content += processed_aux_lemmas
            lean_file_content += "\n\n"

    if attr_line:
        lean_file_content += attr_line

    # Write the theorem statement into file
    lean_file_content += theorem_stmt
    lean_file_content += "\n"

    # Extract and write the generated proof (from [LEAN4_PROOF] ... [/LEAN4_PROOF])
    # Fix column-0 tactic blocks: when the proof starts with `:= by\n` and the
    # first tactic is at column 0, re-indent the entire tactic block by 2 spaces.
    # Otherwise the `#check True` sentinel at column 0 would be parsed as part of
    # the tactic block, causing "No goals to be solved" errors.
    proof_stripped = theorem_proof.strip()
    if proof_stripped.startswith(':= by\n') or proof_stripped.startswith(':= by\r\n'):
        by_idx = proof_stripped.index('\n') + 1
        rest = proof_stripped[by_idx:]
        # Check if the first non-empty line is at column 0
        first_line = ''
        for line in rest.split('\n'):
            if line.strip():
                first_line = line
                break
        if first_line and not first_line[0].isspace():
            # Re-indent: add 2 spaces to every non-empty line after `:= by`
            indented_lines = []
            for line in rest.split('\n'):
                if line.strip():
                    indented_lines.append('  ' + line)
                else:
                    indented_lines.append(line)
            theorem_proof = proof_stripped[:by_idx] + '\n'.join(indented_lines)
    lean_file_content += theorem_proof
    lean_file_content += "\n"

    # Add remaining mutual block content (with sorry proofs) if provided
    # This allows forward references to resolve for theorems inside mutual blocks
    if remaining_mutual_content and remaining_mutual_content.strip():
        lean_file_content += "\n"
        lean_file_content += remaining_mutual_content
        lean_file_content += "\n"

    # Always compute required 'end' statements from the actual local_context
    # (The pre-computed suffix may not match when verif_local_context differs from local_ctxs)
    suffix = compute_required_ends(local_context)

    if suffix:
        lean_file_content += suffix
        lean_file_content += "\n"

    # Add a sentinel command at column 0 so Lean's parser can properly
    # delimit the last tactic block (otherwise files ending with an
    # indented tactic like `sby ...` produce "unexpected end of input").
    lean_file_content += "\n#check True\n"

    return lean_file_content


def get_content_before_theorem(
    file_content: str,
    theorem_stmt: str,
    thm_name: str = "",
) -> Optional[str]:
    """
    Extract file content from the beginning up to (but not including) the theorem statement.

    Args:
        file_content: Full content of the Lean file
        theorem_stmt: Theorem statement (may have normalized whitespace)
        thm_name: Fully qualified theorem name (e.g. "PMF.probOutput_eq"),
                  used to disambiguate when the same statement appears in
                  multiple namespaces.

    Returns:
        Content before the theorem, or None if theorem not found
    """
    # Step 1: Convert literal \n to actual newlines
    normalized_stmt = theorem_stmt.replace('\\n', '\n')

    # Step 2: Escape special regex characters
    # After escaping, make arrows flexible
    escaped_stmt = re.escape(normalized_stmt)

    # Step 3: Replace escaped whitespace with flexible pattern
    # Any single whitespace in stmt can match one or more whitespace in file
    pattern = re.sub(r'\\ ', r'\\s+', escaped_stmt)

    # Search in the original file — collect ALL matches
    matches = list(re.finditer(pattern, file_content))

    if matches:
        match = _pick_best_match(matches, file_content, thm_name)
        result = file_content[:match.start()]
        return _downgrade_docstrings_except_guard_msgs(result)

    # If stmt has `omit ... in` prefix, try matching without it (the omit block
    # may differ between dataset and container versions).
    omit_match = re.match(r'omit\b.*?\bin\s+', normalized_stmt, re.DOTALL)
    if omit_match and not matches:
        core_stmt = normalized_stmt[omit_match.end():]
        core_escaped = re.escape(core_stmt)
        core_pattern = re.sub(r'\\ ', r'\\s+', core_escaped)
        core_matches = list(re.finditer(core_pattern, file_content))
        if core_matches:
            match = _pick_best_match(core_matches, file_content, thm_name)
            result = file_content[:match.start()]
            return _downgrade_docstrings_except_guard_msgs(result)

    # Debug: print the pattern and first match attempt
    print(normalized_stmt)
    print(escaped_stmt)
    print("No match found by theorem stmt, falling back to theorem name")
    # search by theorem name only
    tokens = [token for token in normalized_stmt.split(" ") if token.strip() != ""]
    # Find the theorem/lemma keyword and take the next token as the name.
    # This handles `omit ... in theorem/lemma name` patterns.
    theorem_name = None
    for idx, tok in enumerate(tokens):
        if tok.strip() in ('theorem', 'lemma') and idx + 1 < len(tokens):
            theorem_name = tokens[idx + 1].strip()
            break
    if theorem_name is None:
        theorem_name = tokens[1].strip()

    theorem_name_pattern = r'\b(theorem|lemma)\s+' + re.escape(theorem_name) + r'\s+'
    matches = list(re.finditer(theorem_name_pattern, file_content))
    if matches:
        match = _pick_best_match(matches, file_content, thm_name)
        result = file_content[:match.start()]
        return _downgrade_docstrings_except_guard_msgs(result)

    # If full dotted name failed, try the last component (handles namespaced names)
    if '.' in theorem_name:
        short_name = theorem_name.rsplit('.', 1)[1]
        short_pattern = r'\b(theorem|lemma)\s+' + re.escape(short_name) + r'\s+'
        matches = list(re.finditer(short_pattern, file_content))
        if matches:
            match = _pick_best_match(matches, file_content, thm_name)
            result = file_content[:match.start()]
            return _downgrade_docstrings_except_guard_msgs(result)

    # Final fallback: use thm_name parameter (fully qualified name from dataset)
    if thm_name and thm_name != theorem_name:
        short_name = thm_name.rsplit('.', 1)[-1]
        if short_name != theorem_name:
            fallback_pattern = r'\b(theorem|lemma)\s+' + re.escape(short_name) + r'\s+'
            matches = list(re.finditer(fallback_pattern, file_content))
            if matches:
                match = _pick_best_match(matches, file_content, thm_name)
                result = file_content[:match.start()]
                return _downgrade_docstrings_except_guard_msgs(result)

    return None


def _pick_best_match(matches: list, file_content: str, thm_name: str):
    """Pick the best match when multiple occurrences exist, using namespace info."""
    if len(matches) == 1 or not thm_name:
        return matches[0]

    # Extract the namespace prefix from thm_name (e.g. "PMF" from "PMF.probOutput_eq")
    ns_parts = thm_name.rsplit('.', 1)
    if len(ns_parts) < 2:
        return matches[0]
    expected_ns_suffix = ns_parts[0]  # e.g. "PMF", "SignedRay"

    # For each match, compute the active namespace from the content before it
    for m in matches:
        content_before = file_content[:m.start()]
        ns = _compute_namespace_from_text(content_before)
        # Check if the computed namespace ends with the expected prefix
        if ns == expected_ns_suffix or ns.endswith('.' + expected_ns_suffix):
            return m

    # Fallback: return first match
    return matches[0]


# ---------------------------------------------------------------------------
# Conflict resolution
# ---------------------------------------------------------------------------

def find_conflicting_names_from_local_context(local_ctxs: str, aux_lemmas: str) -> Dict[str, str]:
    """
    Find conflicting lemma/theorem names between aux_lemmas and local_ctxs.

    Args:
        local_ctxs: The local file context containing existing lemmas/theorems
        aux_lemmas: The auxiliary lemmas that may conflict with local_ctxs

    Returns:
        Dictionary mapping old_name -> new_name for conflicting names
    """
    if not aux_lemmas.strip():
        return {}

    # Extract all lemma/theorem names from aux_lemmas (including qualified names with dots)
    aux_pattern = r'\b(theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_\.\u0080-\uFFFF\']*)'
    aux_matches = re.findall(aux_pattern, aux_lemmas)
    aux_names = [match[1] for match in aux_matches]

    if not aux_names:
        return {}

    # Extract all existing lemma/theorem names from local_ctxs
    local_matches = re.findall(aux_pattern, local_ctxs)
    local_names = set([match[1] for match in local_matches])

    # Collect all names from aux_lemmas to check against
    all_aux_names = set(aux_names)

    # Build a mapping of old names to new names for conflicts
    name_mapping = {}

    for aux_name in aux_names:
        if aux_name in local_names or aux_name in name_mapping.values():
            # Find a new name by appending _<id>
            base_name = aux_name
            counter = 1
            new_name = f"{base_name}_{counter}"

            # Keep incrementing until we find a name that doesn't conflict
            while new_name in local_names or new_name in all_aux_names or new_name in name_mapping.values():
                counter += 1
                new_name = f"{base_name}_{counter}"

            name_mapping[aux_name] = new_name
            # Add the new name to local_names to avoid future conflicts
            local_names.add(new_name)

    return name_mapping


def find_conflicting_names_from_error(error_msg: str, aux_lemmas: str) -> Dict[str, str]:
    """
    Find conflicting lemma/theorem names from compiler error message.

    Args:
        error_msg: Compiler error message containing "has already been declared" errors
        aux_lemmas: The auxiliary lemmas to search for matching names

    Returns:
        Dictionary mapping old_name -> new_name for conflicting names
    """
    if not error_msg or not aux_lemmas.strip():
        return {}

    # Find all "has already been declared" errors
    # Example: "'Capless.CaptureSet.rename_union' has already been declared"
    already_declared_pattern = r"'([^']+)'\s+has already been declared"
    error_matches = re.findall(already_declared_pattern, error_msg)

    if not error_matches:
        return {}

    # Extract all lemma/theorem names from aux_lemmas (including qualified names with dots)
    aux_pattern = r'\b(theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_\.\u0080-\uFFFF\']*)'
    aux_matches = re.findall(aux_pattern, aux_lemmas)
    aux_names = [match[1] for match in aux_matches]

    if not aux_names:
        return {}

    # Collect all names from aux_lemmas to check against
    all_aux_names = set(aux_names)

    name_mapping = {}
    used_new_names = set()

    for error_name in error_matches:
        # Try to find matching lemma in aux_lemmas
        # Start with full name, then gradually remove leftmost tokens
        tokens = error_name.split('.')
        matched_aux_name = None

        for i in range(len(tokens)):
            # Try matching with tokens[i:]
            partial_name = '.'.join(tokens[i:])

            # Check if any aux_name matches this partial name
            for aux_name in aux_names:
                if aux_name == partial_name:
                    matched_aux_name = aux_name
                    break

            if matched_aux_name:
                break

        if matched_aux_name and matched_aux_name not in name_mapping:
            # Generate new unique name
            base_name = matched_aux_name
            counter = 1
            new_name = f"{base_name}_{counter}"

            while new_name in all_aux_names or new_name in used_new_names or new_name in name_mapping.values():
                counter += 1
                new_name = f"{base_name}_{counter}"

            name_mapping[matched_aux_name] = new_name
            used_new_names.add(new_name)

    return name_mapping


def apply_name_replacements(aux_lemmas: str, theorem_proof: str, name_mapping: Dict[str, str]) -> tuple[str, str]:
    """
    Apply name replacements to aux_lemmas and theorem_proof.

    Args:
        aux_lemmas: The auxiliary lemmas
        theorem_proof: The proof body
        name_mapping: Dictionary mapping old_name -> new_name

    Returns:
        Tuple of (updated_aux_lemmas, updated_theorem_proof)
    """
    if not name_mapping:
        return aux_lemmas, theorem_proof

    updated_aux_lemmas = aux_lemmas
    updated_theorem_proof = theorem_proof

    for old_name, new_name in name_mapping.items():
        # Replace all usages (declarations and references) in aux_lemmas
        # Use word boundary at start, and ensure not followed by identifier/namespace continuation characters
        pattern = r'\b' + re.escape(old_name) + r'(?![a-zA-Z0-9_\.\u0080-\uFFFF\'])'
        updated_aux_lemmas = re.sub(pattern, new_name, updated_aux_lemmas)

        # Replace all usages in the theorem proof
        updated_theorem_proof = re.sub(pattern, new_name, updated_theorem_proof)

    return updated_aux_lemmas, updated_theorem_proof


def update_proof_and_lemma_to_avoid_name_conflicts(local_ctxs: str, aux_lemmas: str, theorem_proof: str) -> tuple[str, str]:
    """
    Update aux_lemmas and theorem_proof to avoid name conflicts with local_ctxs.

    Args:
        local_ctxs: The local file context containing existing lemmas/theorems
        aux_lemmas: The auxiliary lemmas that may conflict with local_ctxs
        theorem_proof: The proof body that may reference lemmas

    Returns:
        Tuple of (updated_aux_lemmas, updated_theorem_proof)
    """
    name_mapping = find_conflicting_names_from_local_context(local_ctxs, aux_lemmas)
    return apply_name_replacements(aux_lemmas, theorem_proof, name_mapping)


# ---------------------------------------------------------------------------
# Import resolution
# ---------------------------------------------------------------------------

def _compute_namespace_from_text(text: str) -> str:
    """
    Compute the current namespace from Lean source text.

    Parses namespace/section/end statements to determine the active namespace context.

    Args:
        text: Lean source code text

    Returns:
        Current namespace as dot-separated string (e.g., "X.Y.Z" or "")
    """
    # Remove comments
    cleaned = re.sub(r'/-.*?-/', ' ', text, flags=re.DOTALL)
    lines = cleaned.split('\n')

    ns_stack = []
    non_ns_stack = []  # Track section/mutual blocks

    for line in lines:
        lc = line.split('--')[0]

        # namespace X.Y adds X, Y to stack
        m = re.match(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_\.]*)', lc)
        if m:
            for part in m.group(1).split('.'):
                ns_stack.append(part)
            continue

        # Track sections and mutual blocks (but don't add to namespace)
        m = re.match(r'^\s*section\s+([A-Za-z_][A-Za-z0-9_\.]*)', lc)
        if m:
            non_ns_stack.append(('section', m.group(1)))
            continue

        if re.match(r'^\s*section\s*$', lc):
            non_ns_stack.append(('section', None))
            continue

        if re.match(r'^\s*mutual\s*$', lc):
            non_ns_stack.append(('mutual', None))
            continue

        # end X.Y or end pops from stack
        m = re.match(r'^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_\.]*))?', lc)
        if m:
            end_name = m.group(1)
            if end_name:
                # Check if it closes a section/mutual first
                if non_ns_stack and non_ns_stack[-1][1] == end_name:
                    non_ns_stack.pop()
                    continue
                # Otherwise, pop matching namespace parts
                end_parts = end_name.split('.')
                for i in range(len(ns_stack) - len(end_parts) + 1):
                    if ns_stack[i:i+len(end_parts)] == end_parts:
                        ns_stack = ns_stack[:i]
                        break
            else:
                # Anonymous end - pop section/mutual first, then namespace
                if non_ns_stack:
                    non_ns_stack.pop()
                elif ns_stack:
                    ns_stack.pop()

    return '.'.join(ns_stack)


def get_add_imports_needed(
    theorem_entry: Dict[str, Any],
    lemmas: str,
    proof: str,
    local_context: str
) -> str:
    """
    Determine necessary import statements to add based on fixed lemmas and proof.

    Uses IdentifierExtractor from analysis module and namespace-aware resolution.

    Args:
        theorem_entry: The theorem entry dictionary
        lemmas: The fixed lemmas string
        proof: The fixed proof string
        local_context: The local file context (content before theorem)
    """
    import_list = set()

    # Import from analysis module here to avoid circular import
    from analysis.identifier_extractor import IdentifierExtractor
    from analysis.scope_tracker import ScopeTracker

    # Use IdentifierExtractor and ScopeTracker from the analysis module
    extractor = IdentifierExtractor()
    scope_tracker = ScopeTracker()

    # Extract identifiers from theorem statement and proof
    identifiers = extractor.extract(proof)

    # Extract identifiers from auxiliary lemmas
    for lemma in ar_get_lemma_list(lemmas):
        identifiers.update(extractor.extract(lemma))

    # Use ScopeTracker to extract opened namespaces
    opened_namespaces = list(scope_tracker.extract_opened_namespaces(local_context))

    # Compute current namespace from local_context
    current_ns = _compute_namespace_from_text(local_context)

    # Build set of already-used identifiers to skip
    # These fields may contain dicts with "name" key or plain strings
    def extract_names(items):
        names = set()
        for item in items:
            if isinstance(item, dict):
                name = item.get("name", "")
                if name:
                    names.add(name)
            elif isinstance(item, str):
                names.add(item)
        return names

    used_repo_defs = extract_names(theorem_entry.get("used_repo_defs", []))
    used_repo_lemmas = extract_names(theorem_entry.get("used_repo_lemmas", []))
    used_local_defs = extract_names(theorem_entry.get("used_local_defs", []))
    used_local_lemmas = extract_names(theorem_entry.get("used_local_lemmas", []))
    skip_set = used_repo_defs | used_repo_lemmas | used_local_defs | used_local_lemmas

    # For each extracted identifier, try to resolve it
    for ident in identifiers:
        # Normalize _root_. prefix
        name = ident
        root_override = False
        if name.startswith('_root_.'):
            name = name[len('_root_.'):]
            root_override = True

        # Build resolution candidates
        candidates = []  # Always try the bare name first
        if not root_override:
            # Try with current namespace
            if current_ns:
                candidates.append(f"{current_ns}.{name}")
            # Try with opened namespaces
            for ns in opened_namespaces:
                candidates.append(f"{ns}.{name}")
            if not current_ns:
                # Also try with leading dot (global namespace)
                candidates.append(f"{name}")
        else:
            candidates.append(name)

        # Try to resolve each candidate
        matched_name = None
        matched_path = None
        for cand in candidates:
            # Skip if this candidate is already in our dependency lists
            if cand in skip_set:
                continue

            # Try to find the file path for this candidate
            path = find_path_for_repo_def(cand, theorem_entry["lean_root"])
            if path:
                matched_name = cand
                matched_path = path
                break

        if not matched_path:
            continue

        # Don't import the current file
        if matched_path == theorem_entry.get("rel_path"):
            continue

        # Generate import statement
        import_stmt = f"import {path_to_module(theorem_entry['lean_root'], matched_path)}"
        import_pattern = re.escape(import_stmt).replace(r'\ ', r'\s+')
        if not re.search(import_pattern, local_context):
            import_list.add(import_stmt)

    return "\n".join(sorted(import_list)) if import_list else ""


def find_path_for_repo_def(identifier: str, lean_root: str) -> Optional[str]:
    """Find the file path for a repo definition by identifier, checking aliases.

    Uses data/repo_index/<repo>.json with namespace-aware matching.

    Args:
        identifier: The identifier to search for (can be fully qualified or simple name)
        lean_root: The repository name

    Returns:
        Relative file path if found, None otherwise
    """
    repo_index_path = REPO_INDEX_DIR / f"{lean_root}.json"
    if not repo_index_path.exists():
        return None

    try:
        with open(repo_index_path, 'r', encoding='utf-8') as f:
            repo_data = json.load(f)
    except Exception:
        return None

    # Search in definitions_by_file
    for file_path, defs in repo_data.get('definitions_by_file', {}).items():
        if 'lakefile.lean' in file_path:
            continue
        for entry in defs:
            if identifier == entry.get('name'):
                return file_path

    # Search in theorems_by_file
    for file_path, theorems in repo_data.get('theorems_by_file', {}).items():
        if 'lakefile.lean' in file_path:
            continue
        for entry in theorems:
            if identifier == entry.get('name'):
                return file_path

    return None


# ---------------------------------------------------------------------------
# Leaked identifier support
# ---------------------------------------------------------------------------

def load_local_theorems(lean_root: str, rel_path: str):
    """
    Load all local theorems from a specific file in a repository.

    Args:
        lean_root: The lean repository root
        rel_path: Relative path to the source file

    Returns:
        List of theorem records with keys: name, aliases, kind, namespace, line, end_line, text
    """
    repo_index_path = REPO_INDEX_DIR / f"{lean_root}.json"

    if not repo_index_path.exists():
        print(f"Warning: repo index not found for {lean_root} at {repo_index_path}")
        return []

    with open(repo_index_path, 'r') as f:
        repo_data = json.load(f)

    theorems_by_file = repo_data.get('theorems_by_file', {})

    return theorems_by_file.get(rel_path, [])


def find_target_theorem(theorems, thm_name):
    """
    Find the target theorem by name in the list of theorems.

    Args:
        theorems: List of theorem records
        thm_name: Name of the theorem to find

    Returns:
        Theorem record or None if not found
    """
    for thm in theorems:
        # Check if thm_name matches the theorem name or any of its aliases
        if thm['name'] == thm_name or thm_name in thm.get('aliases', []):
            return thm
    return None


def filter_theorems_before_line(theorems, target_line):
    """
    Filter theorems to keep only those that end before the target line.

    Args:
        theorems: List of theorem records
        target_line: Line number to filter by

    Returns:
        List of theorems whose end_line <= target_line
    """
    return [thm for thm in theorems if thm.get('end_line', float('inf')) <= target_line]



def clean_leaked_identifiers(locator_entry: dict, proof: str, aux_lemmas: str) -> tuple[str, str]:
    """
    Clean leaked local theorem identifiers from proof and aux_lemmas by renaming them.

    For each leaked identifier, replaces it with a renamed version where the last component
    is prefixed with 'my_'. For example:
    - 'B.C' becomes 'B.my_C'
    - 'Z' becomes 'my_Z'

    Args:
        locator_entry: Locator JSON entry containing thm_name, lean_root, rel_path, etc.
        proof: The generated proof text
        aux_lemmas: The auxiliary lemmas text

    Returns:
        Tuple of (cleaned_proof, cleaned_aux_lemmas)
    """
    thm_name = locator_entry['thm_name']
    lean_root = locator_entry['lean_root']
    rel_path = locator_entry['rel_path']
    thm_stmt = locator_entry.get('thm_stmt', '')

    # Get all local theorems from the file
    all_local_theorems = load_local_theorems(lean_root, rel_path)

    # Find target theorem
    target_thm = find_target_theorem(all_local_theorems, thm_name)
    if target_thm is None:
        return proof, aux_lemmas

    # Filter to get theorems before the target
    target_line = target_thm['line']
    local_theorems_before = filter_theorems_before_line(all_local_theorems, target_line)

    # Extract identifiers from proof and aux_lemmas
    identifiers = ar_extract_identifiers(thm_stmt, proof)
    for lemma in ar_get_lemma_list(aux_lemmas):
        lem_body = ar_get_proof_body(lemma)
        lem_header = lemma[: ar_find_unwrapped_assign(lemma)]
        identifiers.update(ar_extract_identifiers(lem_header, lem_body))

    # Build set of available local lemma names from aliases (already fully qualified)
    available_local_lemmas = set()
    for thm in local_theorems_before:
        available_local_lemmas.update(thm.get('aliases', []))
        available_local_lemmas.add(thm.get('name', ''))

    # Get target theorem's namespace for resolving bare identifiers
    target_ns = target_thm.get('namespace', '')

    # Find problematic identifiers that need to be renamed
    leaked_identifiers = []
    for identifier in identifiers:
        # Check if identifier directly matches any available local lemma alias
        if identifier in available_local_lemmas:
            leaked_identifiers.append(identifier)
            continue

        # Try with target namespace prefix
        if target_ns:
            fq_identifier = f"{target_ns}.{identifier}"
            if fq_identifier in available_local_lemmas:
                leaked_identifiers.append(identifier)

    # Now perform replacements in proof and aux_lemmas
    cleaned_proof = proof
    cleaned_aux_lemmas = aux_lemmas

    for identifier in leaked_identifiers:
        parts = identifier.split('.')
        if len(parts) > 1:
            renamed = '.'.join(parts[:-1]) + '.my_' + parts[-1]
        else:
            renamed = 'my_' + identifier

        escaped_id = re.escape(identifier)
        id_char_class = r"A-Za-z0-9_'?!₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒪"
        pattern = rf'(?<![{id_char_class}.\'])' + escaped_id + r'(?!\.)'

        cleaned_proof = re.sub(pattern, renamed, cleaned_proof)
        cleaned_aux_lemmas = re.sub(pattern, renamed, cleaned_aux_lemmas)

    if not cleaned_proof.lstrip().startswith("by"):
        cleaned_proof = "by\n" + cleaned_proof

    return cleaned_proof, cleaned_aux_lemmas


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------

def check_generated_content_for_incomplete_proofs(theorem_name: str, theorem_proof: str, aux_lemmas: str) -> list[str]:
    """
    Check if generated proof or aux lemmas contain sorry/admit keywords.

    Identifies which specific declaration (theorem/lemma/def) contains the incomplete proof.
    Matches Lean's native error format: "declaration uses 'sorry'"

    Returns:
        List of error messages
    """
    errors = []

    # Helper to extract declaration name from content up to position
    def get_declaration_name(content: str, pos: int) -> str:
        """Find the theorem/lemma/def name that encloses the position."""
        # Search backwards from position for the most recent theorem/lemma/def
        preceding = content[:pos]
        # Pattern matches: lemma/theorem/def followed by identifier (handles unicode, ?, !, ', dots)
        # Use finditer to get ALL matches and take the last one (most recent declaration)
        pattern = r'(?:theorem|lemma|def)\s+([a-zA-Z_][a-zA-Z0-9_.\u0080-\uFFFF\'?!]*)'
        matches = list(re.finditer(pattern, preceding))
        if matches:
            return matches[-1].group(1)  # Last match is the most recent declaration
        return "unknown"

    # Check aux_lemmas
    if aux_lemmas.strip():
        content_clean = _remove_comments(aux_lemmas)
        for keyword in ['sorry', 'admit']:
            match = re.search(rf'\b{keyword}\b', content_clean)
            if match:
                decl_name = get_declaration_name(content_clean, match.start())
                errors.append(f"declaration '{decl_name}' uses '{keyword}'")
                break  # One error per content chunk

    # Check theorem_proof
    if theorem_proof.strip():
        content_clean = _remove_comments(theorem_proof)
        for keyword in ['sorry', 'admit']:
            match = re.search(rf'\b{keyword}\b', content_clean)
            if match:
                decl_name = theorem_name
                errors.append(f"declaration '{decl_name}' uses '{keyword}'")
                break

    return errors


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def clean_thm_name(thm_name: str) -> str:
    """Clean theorem name to be Lean-compile compatible."""
    out = []

    for c in thm_name:
        # keep safe characters
        if c.isalnum() or c == "_":
            out.append(c)
        # dot -> underscore (common + readable)
        elif c == ".":
            out.append("_")
        # prime
        elif c == "'":
            out.append("_prime")
        # everything else -> unicode escape
        else:
            out.append(f"_u{ord(c):04x}")

    name = "".join(out)

    # trim underscores
    return name


def remove_lean_comments(content: str, ignore_strings: bool = False) -> str:
    """Remove Lean 4 line and block comments from content.

    Args:
        content: Lean source code

    Returns:
        Content with comments removed
    """
    result = []
    i = 0

    while i < len(content):
        # Check for block comment start
        if i < len(content) - 1 and content[i:i+2] == '/-':
            # Find matching closing -/
            depth = 1
            i += 2
            while i < len(content) - 1 and depth > 0:
                if content[i:i+2] == '/-':
                    depth += 1
                    i += 2
                elif content[i:i+2] == '-/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
            # Skip the comment, replace with space to maintain positions somewhat
            if not ignore_strings:
                result.append(' ')
            continue

        # Check for line comment
        if i < len(content) - 1 and content[i:i+2] == '--':
            # Skip until end of line
            if "\\n" in content:
                # If we have literal \n, skip until that
                while i < len(content) - 1 and content[i:i+2] != '\\n':
                    i += 1
            else:
                while i < len(content) and content[i] != '\n':
                    i += 1
            # Keep the newline
            if i < len(content):
                result.append(content[i])
                i += 1
            continue

        # Normal character
        result.append(content[i])
        i += 1

    return ''.join(result)


def elide_proofs(code: str) -> str:
    """
    Replace proof bodies in Lean code with 'admit /- proof elided -/' according to specified rules.

    Handles these patterns:
    - := by (unwrapped) -> replace everything after "by" with "admit /- proof elided -/"
    - := by (wrapped in () or <>) -> replace content between "by" and closing bracket with "admit /- proof elided -/"
    - => by -> replace until next branch (|) or end with "admit /- proof elided -/"
    - by { ... } -> replace { ... } with "admit /- proof elided -/"
    - <..., by ... > -> replace content after "by" and before > with "admit /- proof elided -/"

    Args:
        code: Lean definition statement and body

    Returns:
        Code with proof bodies elided
    """
    # First, remove comments to avoid processing them, but track their positions
    # We'll work on the comment-free version and reconstruct later

    def find_matching_bracket(s: str, start: int, open_char: str, close_char: str) -> Optional[int]:
        """Find the matching closing bracket, accounting for nesting."""
        depth = 1
        i = start + 1
        while i < len(s) and depth > 0:
            if s[i] == open_char:
                depth += 1
            elif s[i] == close_char:
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return None

    def find_matching_unicode_bracket(s: str, start: int) -> Optional[int]:
        """Find the matching > for <, accounting for nesting."""
        depth = 1
        i = start + 1
        while i < len(s) and depth > 0:
            if s[i] == '\u27e8':
                depth += 1
            elif s[i] == '\u27e9':
                depth -= 1
                if depth == 0:
                    return i
            i += 1
        return None

    def get_column(s: str, pos: int) -> int:
        """Get the column number (0-indexed) of a position in the string."""
        line_start = s.rfind('\n', 0, pos)
        if line_start == -1:
            return pos
        return pos - line_start - 1

    def find_next_branch(s: str, start: int, by_column: int) -> Optional[int]:
        """Find the next | at a lower indentation level than by_column."""
        i = start
        while i < len(s):
            if s[i] == '|':
                col = get_column(s, i)
                if col < by_column:
                    return i
            elif s[i] == '\n':
                # Check if next non-whitespace is |
                j = i + 1
                # Store the start of whitespace
                ws_start = j
                while j < len(s) and s[j] in ' \t':
                    j += 1
                if j < len(s) and s[j] == '|':
                    col = get_column(s, j)
                    if col < by_column:
                        # Return the index of the first whitespace, not the |
                        return ws_start
            i += 1
        return None

    def is_wrapped_in_brackets(s: str, by_pos: int) -> tuple[bool, Optional[int], Optional[str]]:
        """Check if 'by' at by_pos is wrapped in () or <>, return (is_wrapped, close_pos, bracket_type)."""
        # Look backwards to find if we're inside brackets
        depth_paren = 0
        depth_angle = 0
        k = by_pos - 1

        while k >= 0:
            if s[k] == ')':
                depth_paren += 1
            elif s[k] == '(':
                depth_paren -= 1
                if depth_paren < 0:
                    # Found opening paren before us
                    close = find_matching_bracket(s, k, '(', ')')
                    if close is not None and close > by_pos:
                        return True, close, '('
            elif s[k] == '\u27e9':
                depth_angle += 1
            elif s[k] == '\u27e8':
                depth_angle -= 1
                if depth_angle < 0:
                    # Found opening angle before us
                    close = find_matching_unicode_bracket(s, k)
                    if close is not None and close > by_pos:
                        return True, close, '\u27e8'
            k -= 1

        return False, None, None

    # Work with comment-free code to avoid processing comments
    code_no_comments = remove_lean_comments(code)
    result = code_no_comments

    # Process multiple times until no more changes
    max_iterations = 100
    for iteration in range(max_iterations):
        changed = False
        i = 0

        while i < len(result):
            # Look for 'by' keyword
            if (result[i:i+2] == 'by' and
                (i == 0 or not result[i-1].isalnum() and result[i-1] not in '_\'') and
                (i+2 >= len(result) or not result[i+2].isalnum() and result[i+2] not in '_\'')):

                # Skip whitespace after 'by'
                j = i + 2
                while j < len(result) and result[j] in ' \t':
                    j += 1

                # Pattern 1: by {
                if j < len(result) and result[j] == '{':
                    close = find_matching_bracket(result, j, '{', '}')
                    if close is not None:
                        replacement = " admit /- proof elided -/"
                        result = result[:i+2] + replacement + result[close+1:]
                        changed = True
                        i = i + 2 + len(replacement)  # Continue from after replacement
                        continue

                # Check if 'by' is wrapped in parentheses or angle brackets
                is_wrapped, close_pos, bracket_type = is_wrapped_in_brackets(result, i)

                if is_wrapped and close_pos is not None:
                    # Pattern: (by ...) or <by ...>
                    # Find the indentation of the closing bracket's line and preserve it
                    line_start = result.rfind('\n', 0, close_pos)
                    if line_start == -1:
                        line_start = 0
                    else:
                        line_start += 1  # Move past the newline

                    # Extract indentation before the closing bracket
                    indent = ""
                    for idx in range(line_start, close_pos):
                        if result[idx] in ' \t':
                            indent += result[idx]
                        else:
                            break

                    replacement = " admit /- proof elided -/\n" + indent
                    result = result[:i+2] + replacement + result[close_pos:]
                    changed = True
                    i = close_pos  # Continue from the closing bracket
                    continue
                else:
                    # Check for => by pattern (for pattern matching)
                    # Look backwards for => (with flexible whitespace/newlines between => and by)
                    k = i - 1
                    while k >= 0 and result[k] in ' \t\n':
                        k -= 1

                    if k >= 1 and result[k-1:k+1] == '=>':
                        # Pattern: => by
                        by_col = get_column(result, i)
                        next_branch = find_next_branch(result, i+2, by_col)

                        if next_branch is not None:
                            replacement = " admit /- proof elided -/\n"
                            result = result[:i+2] + replacement + result[next_branch:]
                            changed = True
                            i = i + 2 + len(replacement)  # Continue from after replacement
                            continue
                        else:
                            # No more branches, replace to end
                            replacement = " admit /- proof elided -/"
                            result = result[:i+2] + replacement
                            changed = True
                            break
                    else:
                        # Look backwards for := to check unwrapped := by pattern
                        # (with flexible whitespace/newlines between := and by)
                        m = i - 1
                        while m >= 0 and result[m] in ' \t\n':
                            m -= 1

                        if m >= 1 and result[m-1:m+1] == ':=':
                            # Pattern: := by (unwrapped)
                            replacement = " admit /- proof elided -/"
                            result = result[:i+2] + replacement
                            changed = True
                            break

            i += 1

        if not changed:
            break

    return result


def path_to_module(lean_root: str, path: str) -> str:
    """Convert file path to Lean module name by replacing / with . and removing .lean extension."""
    if path.endswith('.lean'):
        path = path[:-5]
    module_name = path.replace('/', ".")
    if str(lean_root) == 'lean-mlir':
        if module_name.startswith('Blase.Blase.'):
            module_name = module_name.replace('Blase.Blase.', 'Blase.', 1)
        elif module_name.startswith('LeanMLIR.LeanMLIR.'):
            module_name = module_name.replace('LeanMLIR.LeanMLIR.', 'LeanMLIR.', 1)
    if str(lean_root) == "iris-lean":
        if module_name.startswith('src'):
            module_name = module_name.replace('src.', '', 1)
    return module_name


def find_decl_body_separator(code: str) -> tuple[int, str]:
    """
    Find the index of the separator between declaration and body in a Lean declaration.
    Returns the index of the separator, and the separator string itself.
    """
    def get_depth_at_position(code: str, pos: int) -> int:
        """Calculate bracket depth at a given position."""
        depth = 0
        for i in range(pos):
            if code[i] in '[({':
                depth += 1
            elif code[i] in '])}':
                depth -= 1
        return depth

    def find_unwrapped_pattern(pattern: str, code: str) -> Optional[int]:
        """Find first occurrence of regex pattern at depth 0."""
        for match in re.finditer(pattern, code):
            if get_depth_at_position(code, match.start()) == 0:
                return match.start()
        return None

    def find_unwrapped_patterns(code: str) -> Optional[tuple[int, str]]:
        """Find the smallest index of unwrapped patterns, return (position, pattern) tuple."""
        # Dictionary mapping position -> pattern
        positions = {}

        # Find all "have" keywords at depth 0 to skip subsequent ":= by"
        have_positions = []
        for match in re.finditer(r'\bhave\b', code):
            if get_depth_at_position(code, match.start()) == 0:
                have_positions.append(match.start())

        # Pattern 1: ":= by" (with whitespace/newlines between := and by)
        for match in re.finditer(r':=\s+by\b', code):
            if get_depth_at_position(code, match.start()) == 0:
                # Check if this ":= by" is part of a "have" statement
                skip = False
                for have_pos in have_positions:
                    if have_pos < match.start():
                        between_code = code[have_pos:match.start()]
                        # Skip if "have" is nearby (simple heuristic)
                        if '\n\n' not in between_code and len(between_code) < 200:
                            skip = True
                            break
                if not skip:
                    positions[match.start()] = r':=\s+by\b'

        # Pattern 2-4: ":= begin", ":= calc", etc. (with whitespace/newlines)
        for keyword in ['begin', 'calc', 'match', 'fun', '\u03bb']:
            pattern = rf':=\s+{keyword}\b'
            pos = find_unwrapped_pattern(pattern, code)
            if pos is not None:
                positions[pos] = pattern

        # Pattern 5: "where"
        pattern = r'\bwhere\b'
        pos = find_unwrapped_pattern(pattern, code)
        if pos is not None:
            positions[pos] = pattern

        # Pattern 6: "| <pattern>" (pipe followed by whitespace/newlines and any pattern)
        # This matches pattern matching syntax: | 0, | n+1, | (), | _, | (x,y), etc.
        # Avoid matching "<|" (Lean's pipe operator) using negative lookbehind
        # and avoid matching "| <" using negative lookahead
        pattern = r'(?<!<)\|\s+(?!<)\S'
        pos = find_unwrapped_pattern(pattern, code)
        if pos is not None:
            positions[pos] = pattern

        if positions:
            min_pos = min(positions.keys())
            return (min_pos, positions[min_pos])
        return None

    # Step 1 & 2: Find unwrapped patterns and return up to the match start + ":= by"
    match_result = find_unwrapped_patterns(code)
    if match_result is not None:
        match_index, match_pat = match_result
        return match_index, match_pat

    # Step 3: Fallback to first unwrapped ":="
    pos = find_unwrapped_pattern(r':=', code)
    if pos is not None:
        return pos, ':='

    # Step 4: Fallback to first unwrapped ":"
    pos = find_unwrapped_pattern(r':', code)
    if pos is not None:
        return pos, ':'

    return -1, ""


def _downgrade_docstrings_except_guard_msgs(text: str) -> str:
    """
    Convert Lean docstrings (`/-- ... -/`) into regular block comments unless they
    are immediately followed (ignoring whitespace/newlines) by a `#guard_msgs`
    directive, in which case the docstring is preserved.

    Handles nested block comments correctly by tracking nesting depth.
    Both `/-` and `/--` are treated as block starts (they nest).
    """
    result = []
    i = 0
    while i < len(text):
        # Look for start of docstring
        if i < len(text) - 2 and text[i:i+3] == "/--":
            # Found docstring start, find its end (handling nesting)
            block_start = i
            i += 3
            depth = 1

            while i < len(text) - 1 and depth > 0:
                # Check for block start: both /-- and /- increment depth
                if i < len(text) - 1 and text[i:i+2] == "/-":
                    depth += 1
                    i += 2
                # Check for block end
                elif text[i:i+2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1

            # Extract the full block
            block_end = i
            docstring = text[block_start:block_end]

            # Check if followed by #guard_msgs
            after = text[block_end:]
            if re.match(r"\s*#guard_msgs\b", after):
                result.append(docstring)  # Keep as is
            else:
                result.append(docstring.replace("/--", "/-", 1))  # Downgrade
        else:
            result.append(text[i])
            i += 1

    return "".join(result)
