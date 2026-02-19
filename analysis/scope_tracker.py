"""
Scope tracking for variable declarations and local bindings.

ScopeTracker: Tracks variable scopes and opened namespaces
LocalBindingCollector: Collects locally-bound variables from theorem headers and proofs
"""

import re
from typing import Dict, Set

from config.lean_constants import LEAN_KEYWORDS
from utils.utils import find_decl_body_separator

from analysis.comment_remover import CommentRemover
from analysis.lean_patterns import LEAN_ID_CHAR, LEAN_ID_START


class ScopeTracker:
    """Tracks variable scopes and opened namespaces."""

    def __init__(self):
        self._var_pattern = re.compile(r'^\s*variable\s+(.+)')
        self._universe_pattern = re.compile(r'^\s*universe\s+(.+)')
        self._binder_pattern = re.compile(
            rf'[\(\{{\[]\s*([^:\)\]\}}]+)\s*:\s*({LEAN_ID_START}{LEAN_ID_CHAR}*)'
        )

    def extract_opened_namespaces(self, file_text: str) -> Set[str]:
        """Extract namespaces opened via 'open' statements."""
        cleaned = CommentRemover.remove_comments(file_text)
        namespaces = set()
        pattern = r'\bopen\s+(?:scoped\s+)?([A-Z][A-Za-z0-9_.]*(?:\s+[A-Z][A-Za-z0-9_.]*)*)'
        for match in re.finditer(pattern, cleaned):
            for name in match.group(1).split():
                if name and name[0].isupper() and name not in {'in', 'hiding', 'renaming', 'only'}:
                    namespaces.add(name)
        return namespaces

    def parse_variable_declaration(self, var_text: str) -> Dict[str, str]:
        """Parse a single variable declaration and return {name: type} mapping.

        Args:
            var_text: Variable declaration text like "variable {p : ℕ} [Fact p.Prime]"

        Returns:
            Dictionary mapping variable names to their types
        """
        result: Dict[str, str] = {}

        # Remove 'variable' keyword if present
        m = self._var_pattern.match(var_text)
        if m:
            binders_str = m.group(1)
        else:
            binders_str = var_text

        # Extract binders like {p : ℕ} or (x : Type)
        for binder_match in self._binder_pattern.finditer(binders_str):
            names_part = binder_match.group(1).strip()
            base_type = binder_match.group(2)
            for name_match in re.finditer(rf'({LEAN_ID_START}{LEAN_ID_CHAR}*)', names_part):
                var_name = name_match.group(1)
                if var_name and var_name not in LEAN_KEYWORDS and var_name != '_':
                    result[var_name] = base_type

        return result

    def parse_scoped_variables(self, file_text: str) -> Dict[int, Dict[str, str]]:
        """Parse variable declarations with proper section/namespace scoping."""
        cleaned = CommentRemover.remove_comments(file_text)
        lines = cleaned.split('\n')

        scope_stack = [{'type': 'file', 'name': None, 'start': 0, 'vars': {}}]
        completed_scopes = []

        section_start = re.compile(r'^\s*section\s*(\S*)')
        section_end = re.compile(r'^\s*end\s*(\S*)')
        namespace_start = re.compile(r'^\s*namespace\s+(\S+)')

        for line_num, line in enumerate(lines, 1):
            m = section_start.match(line)
            if m and not namespace_start.match(line):
                scope_stack.append({
                    'type': 'section', 'name': m.group(1) if m.group(1) else None,
                    'start': line_num, 'vars': {}
                })
                continue

            m = namespace_start.match(line)
            if m:
                scope_stack.append({
                    'type': 'namespace', 'name': m.group(1),
                    'start': line_num, 'vars': {}
                })
                continue

            m = section_end.match(line)
            if m:
                end_name = m.group(1) if m.group(1) else None
                for i in range(len(scope_stack) - 1, 0, -1):
                    scope = scope_stack[i]
                    if scope['name'] == end_name or (end_name is None and scope['type'] == 'section'):
                        closed = scope_stack.pop(i)
                        completed_scopes.append((closed['start'], line_num, closed['vars']))
                        break
                continue

            m = self._var_pattern.match(line)
            if m:
                binders_str = m.group(1)
                for binder_match in self._binder_pattern.finditer(binders_str):
                    names_part = binder_match.group(1).strip()
                    base_type = binder_match.group(2)
                    for name_match in re.finditer(rf'({LEAN_ID_START}{LEAN_ID_CHAR}*)', names_part):
                        var_name = name_match.group(1)
                        if var_name and var_name not in LEAN_KEYWORDS and var_name != '_':
                            scope_stack[-1]['vars'][var_name] = base_type

            m = self._universe_pattern.match(line)
            if m:
                for name_match in re.finditer(rf'({LEAN_ID_START}{LEAN_ID_CHAR}*)', m.group(1)):
                    univ_name = name_match.group(1)
                    if univ_name and univ_name not in LEAN_KEYWORDS:
                        scope_stack[0]['vars'][univ_name] = 'Universe'

        for scope in scope_stack[1:]:
            completed_scopes.append((scope['start'], len(lines), scope['vars']))
        completed_scopes.append((1, len(lines), scope_stack[0]['vars']))

        line_to_vars: Dict[int, Dict[str, str]] = {}
        for line_num in range(1, len(lines) + 1):
            vars_in_scope = {}
            for start, end, scope_vars in completed_scopes:
                if start <= line_num <= end:
                    vars_in_scope.update(scope_vars)
            line_to_vars[line_num] = vars_in_scope
        return line_to_vars


class LocalBindingCollector:
    """Collects locally-bound variables from theorem headers and proof bodies."""

    def collect_header_locals(self, theorem_text: str) -> Set[str]:
        """Collect parameter names and type variables from the theorem header."""
        header_end_idx, _ = find_decl_body_separator(theorem_text)
        header = theorem_text[:header_end_idx] if header_end_idx != -1 else theorem_text.split(":=", 1)[0]

        names = set()
        depth = 0
        params_end_idx = len(header)
        for i, ch in enumerate(header):
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif ch == ':' and depth == 0:
                params_end_idx = i
                break
        params_section = header[:params_end_idx]

        # Extract parameter names from binders with type annotation
        param_pattern = re.compile(rf"[\(\{{\[]\s*({LEAN_ID_START}{LEAN_ID_CHAR}*)\s*:")
        for m in param_pattern.finditer(params_section):
            n = m.group(1)
            if n and n not in LEAN_KEYWORDS and n != "_":
                names.add(n)

        # Multi-parameter binders with type annotation
        multi_param_pattern = re.compile(rf"[\(\{{\[]\s*([^:\)\]\}}]+)\s*:")
        for m in multi_param_pattern.finditer(params_section):
            for param_match in re.finditer(rf"\b({LEAN_ID_START}{LEAN_ID_CHAR}*)\b", m.group(1)):
                n = param_match.group(1)
                if n and n not in LEAN_KEYWORDS and n != "_":
                    names.add(n)

        # Bare parameters without type annotation: (f) or {s}
        bare_param_pattern = re.compile(rf"[\(\{{\[]\s*({LEAN_ID_START}{LEAN_ID_CHAR}*)\s*[\)\}}\]]")
        for m in bare_param_pattern.finditer(params_section):
            n = m.group(1)
            if n and n not in LEAN_KEYWORDS and n != "_":
                names.add(n)

        return names

    def collect_proof_locals(self, theorem_text: str) -> Set[str]:
        """Collect names introduced by binding tactics in the proof body."""
        body = self._proof_body(CommentRemover.remove_comments(theorem_text))
        locals_found = set()

        def add_if_valid(name: str):
            if name and name != "_" and name not in LEAN_KEYWORDS:
                if re.match(rf"^{LEAN_ID_START}{LEAN_ID_CHAR}*$", name):
                    locals_found.add(name)

        def extract_names_from_pattern(pattern_str: str):
            for p in re.split(r"[,\s⟨⟩\(\)\[\]\{\}|]+", pattern_str):
                add_if_valid(p.strip())

        # intro variants
        for m in re.finditer(rf"\b(?:intro|iintro|rintro)\s+([^\n;{{}}⟨]+?)(?:\n|;|{{|⟨|$)", body):
            for nm in re.finditer(rf"({LEAN_ID_START}{LEAN_ID_CHAR}*)", m.group(1)):
                add_if_valid(nm.group(1))

        # rintro patterns
        for m in re.finditer(r"\brintro\b[^\n]*", body):
            for bracket_match in re.finditer(r"⟨([^⟩]+)⟩", m.group(0)):
                extract_names_from_pattern(bracket_match.group(1))

        # have/let bindings - simple form: have foo := ...
        for m in re.finditer(rf"\b(?:have|let)\s+({LEAN_ID_START}{LEAN_ID_CHAR}*)\s*[:=]", body):
            add_if_valid(m.group(1))

        # have/let bindings - destructured form: have ⟨a, b, c⟩ := ...
        for m in re.finditer(r"\b(?:have|let)\s+⟨([^⟩]+)⟩\s*:=", body):
            extract_names_from_pattern(m.group(1))

        # rename_i - introduces names for anonymous hypotheses
        for m in re.finditer(rf"\brename_i\s+([^\n;]+?)(?:\n|;|$)", body):
            for nm in re.finditer(rf"({LEAN_ID_START}{LEAN_ID_CHAR}*)", m.group(1)):
                add_if_valid(nm.group(1))

        # obtain patterns
        for m in re.finditer(r"\bobtain\s+⟨([^⟩]+)⟩", body):
            extract_names_from_pattern(m.group(1))

        # rcases patterns
        for m in re.finditer(r"\brcases\b[^\n]*?\bwith\b\s*⟨([^⟩]+)⟩", body):
            extract_names_from_pattern(m.group(1))

        # fun/λ binders
        for m in re.finditer(rf"\b(?:fun|λ)\s+([^=↦\n]+?)(?:=>|↦)", body):
            for nm in re.finditer(rf"({LEAN_ID_START}{LEAN_ID_CHAR}*)", m.group(1)):
                add_if_valid(nm.group(1))

        # Match/induction case patterns
        case_pattern = re.compile(r'\|\s*([^=\n]+?)\s*(?:=>|with\b)')
        for m in case_pattern.finditer(body):
            case_content = m.group(1).strip()
            parts = case_content.split()
            for i, part in enumerate(parts):
                if i == 0 and ('.' in part or (part and part[0].isupper())):
                    continue
                if part.lower() == 'with':
                    continue
                add_if_valid(part)

        # Case tactic patterns
        case_tactic_pattern = re.compile(rf'\bcase\s+({LEAN_ID_START}{LEAN_ID_CHAR}*)\s+([^=\n]+?)\s*=>')
        for m in case_tactic_pattern.finditer(body):
            var_part = m.group(2).strip()
            for nm in re.finditer(rf"({LEAN_ID_START}{LEAN_ID_CHAR}*)", var_part):
                add_if_valid(nm.group(1))

        return locals_found

    def collect_statement_binders(self, theorem_text: str) -> Set[str]:
        """Collect bound variable names from the theorem statement."""
        header_end_idx = len(theorem_text)
        for sep in [" := ", " :=\n", "\n:= ", " by ", " by\n"]:
            idx = theorem_text.rfind(sep)
            if idx != -1 and idx < header_end_idx:
                header_end_idx = idx

        if header_end_idx == len(theorem_text):
            fallback_idx, _ = find_decl_body_separator(theorem_text)
            if fallback_idx != -1:
                header_end_idx = fallback_idx

        depth = 0
        return_type_start = 0
        for i, ch in enumerate(theorem_text[:header_end_idx]):
            if ch in '([{':
                depth += 1
            elif ch in ')]}':
                depth -= 1
            elif ch == ':' and depth == 0:
                return_type_start = i + 1
                break

        statement = theorem_text[return_type_start:header_end_idx]
        binders = set()

        def add_if_valid(name: str):
            if name and name != "_" and name not in LEAN_KEYWORDS:
                if re.match(rf"^{LEAN_ID_START}{LEAN_ID_CHAR}*$", name):
                    binders.add(name)

        # ∀/∃ binders
        for m in re.finditer(rf"(?:∀|forall|∃|exists)\s+([^,]+?)\s*,", statement):
            bp = m.group(1)
            names_part = bp[:bp.find(':')] if ':' in bp else bp
            for nm in re.finditer(rf"({LEAN_ID_START}{LEAN_ID_CHAR}*)", names_part):
                add_if_valid(nm.group(1))

        return binders

    def build_local_scope(self, theorem_text: str) -> Set[str]:
        """Combine header, statement, and proof bindings into a per-theorem local scope."""
        scope = set()
        scope.update(self.collect_header_locals(theorem_text))
        scope.update(self.collect_statement_binders(theorem_text))
        scope.update(self.collect_proof_locals(theorem_text))
        return scope

    def _proof_body(self, text: str) -> str:
        """Return the proof portion after ':=' or 'by' if present."""
        separator_idx, separator = find_decl_body_separator(text)
        if separator_idx != -1 and separator:
            match = re.search(separator, text[separator_idx:])
            if match:
                return text[separator_idx + match.end():]
        return text
