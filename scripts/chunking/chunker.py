"""
ProofChunker: Parse Lean files into individual declaration chunks.

This is the main chunking logic that breaks down Lean source files into
individual declarations (theorems, lemmas, defs, structures, etc.) with
accurate line number tracking.
"""

import hashlib
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .comment_remover import CommentRemover
from .data_classes import Chunk, ChunkResult
from . import patterns


class ProofChunker:
    """
    Chunks Lean proof files into independent declarations.

    This class provides methods to:
    - Parse a Lean file/string into individual chunks
    - Track line number mappings for each chunk
    - Extract child declarations (constructors, fields)
    - Cache results for repeated calls

    Usage:
        chunker = ProofChunker()
        result = chunker.chunk_file(Path("my_file.lean"))
        for chunk in result.chunks:
            print(f"{chunk.kind} {chunk.name} @ lines {chunk.start_line}-{chunk.end_line}")
    """

    def __init__(self, cache_enabled: bool = True):
        """Initialize the chunker.

        Args:
            cache_enabled: Whether to cache chunking results in memory
        """
        self.cache_enabled = cache_enabled
        self._cache: Dict[str, ChunkResult] = {}
        self._init_patterns()

    def _init_patterns(self):
        """Initialize all regex patterns for parsing."""
        # Main declaration patterns
        self._decl_pattern = patterns.build_main_decl_pattern()
        self._decl_multiline_pattern = patterns.build_multiline_decl_pattern()

        # Instance patterns
        self._instance_named_pattern = patterns.build_instance_named_pattern()
        self._instance_anon_pattern = patterns.build_instance_anon_pattern()
        self._instance_multiline_pattern = patterns.build_instance_multiline_pattern()

        # Macro/syntax patterns
        self._macro_pattern = patterns.build_macro_pattern()
        self._syntax_pattern = patterns.build_syntax_pattern()
        self._syntax_multiline_name_pattern = patterns.build_syntax_multiline_name_pattern()
        self._macro_rules_pattern = patterns.build_macro_rules_pattern()
        self._elab_rules_pattern = patterns.build_elab_rules_pattern()

        # Notation patterns
        self._notation_pattern = patterns.build_notation_pattern()
        self._notation_multiline_pattern = patterns.build_notation_multiline_pattern()

        # Elab patterns
        self._elab_pattern = patterns.build_elab_pattern()
        self._elab_multiline_pattern = patterns.build_elab_multiline_pattern()

        # Other declaration patterns
        self._declare_syntax_cat_pattern = patterns.build_declare_syntax_cat_pattern()
        self._initialize_named_pattern = patterns.build_initialize_named_pattern()
        self._initialize_anon_pattern = patterns.build_initialize_anon_pattern()

        # Scope-related patterns
        self._variable_pattern = patterns.build_variable_pattern()
        self._import_pattern = patterns.build_import_pattern()
        self._open_pattern = patterns.build_open_pattern()
        self._namespace_pattern = patterns.build_namespace_pattern()
        self._section_pattern = patterns.build_section_pattern()
        self._end_pattern = patterns.build_end_pattern()
        self._export_pattern = patterns.build_export_pattern()

        # Boundary and utility patterns
        self._attr_pattern = patterns.build_attribute_only_pattern()
        self._doc_comment_pattern = patterns.build_doc_comment_pattern()
        self._boundary_pattern = patterns.build_boundary_pattern()

        # Child declaration patterns
        self._constructor_pattern = patterns.build_constructor_pattern()
        self._field_pattern = patterns.build_field_pattern()

        # Veil DSL patterns (repo-specific, see patterns.py for documentation)
        self._veil_invariant_pattern = patterns.build_veil_invariant_pattern()
        self._veil_action_pattern = patterns.build_veil_action_pattern()

    def _compute_hash(self, text: str) -> str:
        """Compute a short hash of the text for caching."""
        return hashlib.sha256(text.encode('utf-8')).hexdigest()[:16]

    def _is_declaration_start(self, line: str) -> Optional[Tuple[str, str]]:
        """Check if a line starts a declaration.

        Args:
            line: A single line of Lean code (should be stripped/cleaned)

        Returns:
            Tuple of (kind, name) if this is a declaration start, None otherwise
        """
        stripped = line.strip()
        if not stripped:
            return None

        # Main declarations (theorem, lemma, def, structure, etc.)
        m = self._decl_pattern.match(stripped)
        if m:
            return (m.group(1), m.group(2))

        # Named instance: instance foo : ...
        m = self._instance_named_pattern.match(stripped)
        if m:
            return ('instance', m.group(1))

        # Anonymous instance: instance : ...
        m = self._instance_anon_pattern.match(stripped)
        if m:
            # Generate name based on type class being implemented
            colon_idx = stripped.find(':')
            if colon_idx != -1:
                type_str = stripped[colon_idx + 1:].strip()
                type_match = re.match(rf'({patterns.SIMPLE_NAME})', type_str)
                type_part = type_match.group(1) if type_match else 'anon'
                return ('instance', f'_inst_{type_part}')
            return ('instance', '_inst_anon')

        # Multi-line instance (colon on subsequent line)
        m = self._instance_multiline_pattern.match(stripped)
        if m:
            return ('instance', m.group(1))

        # Macro
        m = self._macro_pattern.match(stripped)
        if m:
            name = m.group(1) or m.group(2) or m.group(3)
            if name:
                return ('macro', name)

        # Syntax
        m = self._syntax_pattern.match(stripped)
        if m:
            name = m.group(1) or m.group(2) or m.group(3)
            if name:
                return ('syntax', name)

        # Multi-line syntax with (name := ...) at end of line
        m = self._syntax_multiline_name_pattern.match(stripped)
        if m:
            return ('syntax', m.group(1))

        # Notation/infix/prefix/postfix
        m = self._notation_pattern.match(stripped)
        if m:
            return (m.group(1), f'«{m.group(2)}»')

        # Multi-line notation
        m = self._notation_multiline_pattern.match(stripped)
        if m:
            kind = m.group(1)
            priority = m.group(2) if m.group(2) else 'default'
            return (kind, f'_multiline_{kind}_{priority}')

        # Elab
        m = self._elab_pattern.match(stripped)
        if m:
            name = m.group(1) or m.group(2)
            if name:
                return ('elab', name)

        # Multi-line elab with (name := ...) at end of line
        m = self._elab_multiline_pattern.match(stripped)
        if m:
            return ('elab', m.group(1))

        # macro_rules
        m = self._macro_rules_pattern.match(stripped)
        if m:
            return ('macro_rules', '_macro_rules')

        # elab_rules
        m = self._elab_rules_pattern.match(stripped)
        if m:
            return ('elab_rules', '_elab_rules')

        # declare_syntax_cat
        m = self._declare_syntax_cat_pattern.match(stripped)
        if m:
            return ('declare_syntax_cat', m.group(1))

        # Named initialize/builtin_initialize
        m = self._initialize_named_pattern.match(stripped)
        if m:
            return (m.group(1), m.group(2))

        # Anonymous initialize/builtin_initialize
        m = self._initialize_anon_pattern.match(stripped)
        if m:
            return (m.group(1), '_anon_init')

        # Variable declarations
        m = self._variable_pattern.match(stripped)
        if m:
            binders = m.group(1)
            name_match = re.search(rf'[\(\[\{{\s]({patterns.SIMPLE_NAME})', binders)
            if name_match:
                return ('variable', f'_var_{name_match.group(1)}')
            return ('variable', '_var')

        # Import declarations
        m = self._import_pattern.match(stripped)
        if m:
            return ('import', m.group(1).strip())

        # Open declarations
        m = self._open_pattern.match(stripped)
        if m:
            open_target = m.group(1).strip()
            if open_target.endswith(' in'):
                open_target = open_target[:-3].strip()
            return ('open', open_target)

        # Namespace declarations
        m = self._namespace_pattern.match(stripped)
        if m:
            return ('namespace', m.group(1))

        # Section declarations
        m = self._section_pattern.match(stripped)
        if m:
            section_name = m.group(1) if m.group(1) else '_anonymous'
            return ('section', section_name)

        # End declarations
        m = self._end_pattern.match(stripped)
        if m:
            end_name = m.group(1) if m.group(1) else '_anonymous'
            return ('end', end_name)

        # Export declarations: export Namespace (name1 name2 ...)
        # We track these as 'export' chunks to capture alias mappings
        m = self._export_pattern.match(stripped)
        if m:
            namespace = m.group(1)
            names = m.group(2).strip()
            # Store as "namespace:name1,name2,..." for later parsing
            return ('export', f'{namespace}:{names}')

        # Veil DSL: invariant [name] / safety [name]
        # These generate defs, so we index them as 'def' kind
        m = self._veil_invariant_pattern.match(stripped)
        if m:
            name = m.group(2)  # group 1 is invariant/safety, group 2 is the name
            return ('def', name)

        # Veil DSL: action name (params) = { ... }
        # These generate defs (name and name.tr), so we index them as 'def' kind
        m = self._veil_action_pattern.match(stripped)
        if m:
            name = m.group(1)
            return ('def', name)

        # Multi-line declarations (keyword alone at end of line)
        m = self._decl_multiline_pattern.match(stripped)
        if m:
            kind = m.group(1)
            return (kind, f'_multiline_{kind}')

        return None

    def _is_boundary(self, line: str) -> bool:
        """Check if a line is a boundary that terminates a declaration.

        Boundaries include:
        - Attribute-only lines (@[simp], @[ext]) - they belong to NEXT declaration
        - Doc comments (/--) - they belong to NEXT declaration
        - Other declaration starts
        - Directives like export, universe, set_option, etc.
        """
        stripped = line.strip()
        if not stripped:
            return False

        # Attributes are boundaries - they belong to the next declaration
        if self._attr_pattern.match(stripped):
            return True

        # Doc comments are boundaries - they belong to the next declaration
        if self._doc_comment_pattern.match(stripped):
            return True

        # Other declarations are boundaries
        if self._is_declaration_start(stripped):
            return True

        # Directives are boundaries
        if self._boundary_pattern.match(stripped):
            return True

        return False

    def _find_declaration_end(self, lines: List[str], start_idx: int,
                              original_lines: List[str] = None,
                              decl_kind: str = None) -> int:
        """Find the end line index of a declaration.

        Scans forward from start_idx until a boundary is found.

        Args:
            lines: Comment-removed lines (for boundary detection)
            start_idx: Starting line index (0-indexed)
            original_lines: Original lines (for doc comment detection)
            decl_kind: Kind of declaration being parsed (for special handling)

        Returns:
            End line index (0-indexed, inclusive)
        """
        if original_lines is None:
            original_lines = lines

        end_idx = len(lines) - 1

        # Check if this is a 'where'-style declaration (class, structure, inductive)
        # For these, doc comments inside the body are field documentation, not boundaries
        start_line = lines[start_idx] if start_idx < len(lines) else ""
        is_where_style = decl_kind in {'class', 'class abbrev', 'class inductive', 'structure', 'inductive'} or 'where' in start_line

        for j in range(start_idx + 1, len(lines)):
            # Check for doc comments in ORIGINAL lines (before comment removal)
            # But only treat as boundary if NOT inside a where-style declaration
            if self._doc_comment_pattern.match(original_lines[j].strip()):
                if not is_where_style:
                    end_idx = j - 1
                    break
                # For where-style, continue scanning

            # Check for boundaries in cleaned lines
            check_line = lines[j].split("--", 1)[0].strip()
            if self._is_boundary(check_line):
                end_idx = j - 1
                break

        # Trim trailing blank lines
        while end_idx > start_idx and not lines[end_idx].strip():
            end_idx -= 1

        return end_idx

    def _extract_syntax_symbols(self, text: str, kind: str) -> List[str]:
        """Extract operator symbols from syntax/macro/notation definition text.

        Handles various syntax definition patterns:
        1. Composite: `syntax foo := "□" <|> "◇" <|> "◯"` → ["□", "◇", "◯"]
        2. Prefix: `syntax "□" term:40 : cat` → ["□"]
        3. Infix: `syntax:20 cat:21 " ↝ " cat:20 : cat` → ["↝"]
        4. Postfix: `syntax term "!" : cat` → ["!"]
        5. Macro: `macro "tla_simp" : tactic => ...` → ["tla_simp"]
        6. Notation: `notation "⟨" x "⟩" => ...` → ["⟨", "⟩"]

        Args:
            text: The full text of the syntax/macro/notation definition
            kind: The kind of declaration (syntax, macro, notation, etc.)

        Returns:
            List of distinct operator symbols found in the definition
        """
        symbols = []
        seen = set()

        # Pattern for string literals in syntax definitions
        # Matches: "symbol" or " symbol " (with surrounding spaces)
        string_literal_pattern = re.compile(r'"([^"]*)"')

        for match in string_literal_pattern.finditer(text):
            sym = match.group(1).strip()
            # Skip empty strings, pure whitespace, and common non-operator strings
            if not sym or sym.isspace():
                continue
            # Skip category/precedence references like "term" that appear in some contexts
            # but keep actual operator symbols
            if sym in seen:
                continue
            # Skip very long strings (likely not operators)
            if len(sym) > 20:
                continue
            seen.add(sym)
            symbols.append(sym)

        return symbols

    def _extract_child_declarations(self, chunk: Chunk, namespace: str) -> List[Chunk]:
        """Extract child declarations (constructors, fields) from a structure/inductive.

        Child chunks have:
        - Empty text (they share the parent's text)
        - Same line range as parent
        - Parent reference set to parent's name

        Args:
            chunk: Parent chunk (structure, inductive, or class)
            namespace: Current namespace

        Returns:
            List of child chunks
        """
        children = []

        if chunk.kind == 'inductive':
            # Extract constructors
            for m in self._constructor_pattern.finditer(chunk.text):
                children.append(Chunk(
                    kind='constructor',
                    name=f"{chunk.name}.{m.group(1)}",
                    simple_name=m.group(1),
                    namespace=namespace,
                    text='',  # Empty - shares parent's text
                    start_line=chunk.start_line,
                    end_line=chunk.end_line,
                    parent=chunk.name
                ))

        elif chunk.kind in {'structure', 'class', 'class abbrev', 'class inductive'}:
            # Extract fields from structure body
            struct_body = chunk.text
            where_idx = struct_body.find('where')
            if where_idx != -1:
                struct_body = struct_body[where_idx:]

            # Stop at 'deriving' if present
            deriving_idx = struct_body.find('deriving')
            if deriving_idx != -1:
                struct_body = struct_body[:deriving_idx]

            for m in self._field_pattern.finditer(struct_body):
                fname = m.group(1)
                # Skip keywords that look like field names
                if fname and fname not in {'extends', 'where', 'mk', 'deriving'}:
                    children.append(Chunk(
                        kind='field',
                        name=f"{chunk.name}.{fname}",
                        simple_name=fname,
                        namespace=namespace,
                        text='',  # Empty - shares parent's text
                        start_line=chunk.start_line,
                        end_line=chunk.end_line,
                        parent=chunk.name
                    ))

        return children

    def chunk_string(self, text: str, source_name: str = "<string>") -> ChunkResult:
        """Chunk a Lean source string into declarations.

        Args:
            text: Lean source code
            source_name: Name for error messages/debugging

        Returns:
            ChunkResult containing all extracted chunks
        """
        text_hash = self._compute_hash(text)
        if self.cache_enabled and text_hash in self._cache:
            return self._cache[text_hash]

        cleaned_text, original_lines = CommentRemover.remove_with_original(text)
        cleaned_lines = cleaned_text.splitlines()
        chunks: List[Chunk] = []
        # Scope stack tracks both namespaces and sections as (kind, name) tuples
        # This allows proper matching of `end` statements to their corresponding scope
        scope_stack: List[Tuple[str, str]] = []

        # Kinds that use syntax-style names (not normal identifiers)
        syntax_related_kinds = {
            'syntax', 'macro', 'elab', 'notation', 'prefix', 'postfix',
            'infixl', 'infixr', 'infix'
        }
        # Kinds that don't get namespace prefixes
        scope_related_kinds = {'import', 'open', 'namespace', 'section', 'end', 'export'}

        idx = 0
        while idx < len(cleaned_lines):
            line = cleaned_lines[idx]
            stripped = line.strip()

            if not stripped:
                idx += 1
                continue

            decl_info = self._is_declaration_start(stripped)
            if decl_info:
                kind, name = decl_info

                # Update scope stack for namespace/section/end declarations
                if kind == 'namespace':
                    scope_stack.append(('namespace', name))
                elif kind == 'section':
                    scope_stack.append(('section', name))
                elif kind == 'end':
                    if scope_stack:
                        top_kind, top_name = scope_stack[-1]
                        if name == '_anonymous':
                            # Anonymous `end` only closes anonymous sections
                            if top_kind == 'section' and top_name == '_anonymous':
                                scope_stack.pop()
                        elif top_name == name:
                            # Named `end Foo` closes matching namespace or section
                            scope_stack.pop()

                # Validate name format
                is_valid_id = re.match(
                    rf'^_?{patterns.LEAN_ID_START}{patterns.LEAN_ID_CHAR}*'
                    rf'(?:\.{patterns.LEAN_ID_START}{patterns.LEAN_ID_CHAR}*)*$',
                    name
                )
                is_quoted = name.startswith('«') and name.endswith('»')
                is_inst = name.startswith('_inst_')
                is_syntax_kind = kind in syntax_related_kinds
                is_scope_kind = kind in scope_related_kinds

                if not is_valid_id and not is_quoted and not is_inst and \
                   not is_syntax_kind and not is_scope_kind:
                    idx += 1
                    continue

                # Wrap syntax-related names in special quotes
                if is_syntax_kind and not is_valid_id and not is_quoted:
                    name = f'«{name}»'

                # Determine namespace and qualified name
                # Only namespaces contribute to the qualified name prefix, not sections
                if is_scope_kind:
                    namespace = ""
                    qual_name = name
                else:
                    namespace = ".".join(n for k, n in scope_stack if k == 'namespace')
                    qual_name = f"{namespace}.{name}" if namespace else name

                # Look backwards for attributes
                start_line = idx
                while start_line > 0:
                    prev_line = cleaned_lines[start_line - 1].strip()
                    if self._attr_pattern.match(prev_line):
                        start_line -= 1
                    elif prev_line.startswith('omit') or prev_line.startswith('include'):
                        start_line -= 1
                    elif not prev_line:
                        break
                    else:
                        break

                # Find declaration end (pass kind for special handling of where-style decls)
                end_line = self._find_declaration_end(cleaned_lines, idx, original_lines, kind)
                body = "\n".join(original_lines[start_line:end_line + 1])

                # Extract syntax symbols for syntax-related declarations
                syntax_symbols = []
                if kind in syntax_related_kinds or kind in {'declare_syntax_cat', 'macro_rules', 'elab_rules'}:
                    syntax_symbols = self._extract_syntax_symbols(body, kind)

                # Create chunk
                chunk = Chunk(
                    kind=kind,
                    name=qual_name,
                    simple_name=name,
                    namespace=namespace,
                    text=body,
                    start_line=start_line + 1,  # Convert to 1-indexed
                    end_line=end_line + 1,
                    syntax_symbols=syntax_symbols
                )
                chunks.append(chunk)

                # Extract child declarations (constructors, fields)
                chunks.extend(self._extract_child_declarations(chunk, namespace))

                idx = end_line + 1
            else:
                idx += 1

        # Build line-to-chunk mapping
        line_to_chunk: Dict[int, Chunk] = {}
        for chunk in chunks:
            for line_num in range(chunk.start_line, chunk.end_line + 1):
                line_to_chunk[line_num] = chunk

        result = ChunkResult(
            chunks=chunks,
            source_hash=text_hash,
            line_to_chunk=line_to_chunk
        )

        if self.cache_enabled:
            self._cache[text_hash] = result

        return result

    def chunk_file(self, file_path: Path) -> ChunkResult:
        """Chunk a Lean file into declarations.

        Args:
            file_path: Path to the Lean file

        Returns:
            ChunkResult containing all extracted chunks
        """
        text = file_path.read_text(encoding='utf-8')
        return self.chunk_string(text, source_name=str(file_path))

    def clear_cache(self):
        """Clear the in-memory cache."""
        self._cache.clear()


# =============================================================================
# Convenience Functions
# =============================================================================

def chunk_lean_string(text: str) -> List[Chunk]:
    """Convenience function to chunk a Lean string.

    Args:
        text: Lean source code

    Returns:
        List of chunks
    """
    return ProofChunker(cache_enabled=False).chunk_string(text).chunks


def chunk_lean_file(file_path: Path) -> List[Chunk]:
    """Convenience function to chunk a Lean file.

    Args:
        file_path: Path to the Lean file

    Returns:
        List of chunks
    """
    return ProofChunker(cache_enabled=False).chunk_file(file_path).chunks
