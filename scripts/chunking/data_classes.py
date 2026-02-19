"""
Data classes for representing Lean code chunks.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass
class Chunk:
    """Represents a single declaration chunk from a Lean file.

    Attributes:
        kind: Declaration type (theorem, lemma, def, structure, instance, etc.)
        name: Fully qualified name including namespace
        simple_name: Simple name without namespace prefix
        namespace: Namespace path (empty string if none)
        text: Full text of the declaration including doc comments and attributes
        start_line: 1-indexed start line in source file
        end_line: 1-indexed end line (inclusive) in source file
        parent: Parent declaration name (for constructors, fields only)
        syntax_symbols: List of operator symbols extracted from syntax definitions
            (e.g., ["□", "◇", "◯"] from `syntax foo := "□" <|> "◇" <|> "◯"`).
            Empty for non-syntax chunks.
    """
    kind: str
    name: str
    simple_name: str
    namespace: str
    text: str
    start_line: int
    end_line: int
    parent: Optional[str] = None
    syntax_symbols: List[str] = field(default_factory=list)

    def __hash__(self):
        return hash((self.kind, self.name, self.start_line))

    def __eq__(self, other):
        if not isinstance(other, Chunk):
            return False
        return (self.kind == other.kind and
                self.name == other.name and
                self.start_line == other.start_line)

    def __repr__(self):
        return f"Chunk({self.kind} {self.name} @ {self.start_line}-{self.end_line})"


@dataclass
class ChunkResult:
    """Result of chunking a Lean file.

    Attributes:
        chunks: List of all chunks extracted from the file
        source_hash: Hash of the source file for cache validation
        line_to_chunk: Mapping from line numbers to chunks (for quick lookup)
    """
    chunks: List[Chunk]
    source_hash: str
    line_to_chunk: Dict[int, Chunk] = field(default_factory=dict)

    def get_chunk_at_line(self, line: int) -> Optional[Chunk]:
        """Get the chunk containing the specified line number."""
        return self.line_to_chunk.get(line)

    def get_chunks_by_kind(self, kind: str) -> List[Chunk]:
        """Get all chunks of a specific kind."""
        return [c for c in self.chunks if c.kind == kind]

    def get_theorems_and_lemmas(self) -> List[Chunk]:
        """Get all theorem and lemma chunks."""
        return [c for c in self.chunks if c.kind in {'theorem', 'lemma'}]

    def get_definitions(self) -> List[Chunk]:
        """Get all definition-like chunks (def, structure, class, etc.)."""
        return [c for c in self.chunks if c.kind in {
            'def', 'abbrev', 'structure', 'inductive', 'class', 'instance',
            'opaque', 'axiom', 'constant'
        }]

    def get_scope_chunks(self) -> List[Chunk]:
        """Get all scope-related chunks (namespace, section, end, import, open)."""
        return [c for c in self.chunks if c.kind in {
            'namespace', 'section', 'end', 'import', 'open', 'variable'
        }]
