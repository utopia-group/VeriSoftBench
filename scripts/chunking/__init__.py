"""
Chunking module for parsing Lean files into individual declarations.

Vendored from PLProofBenchEval/src/preprocessing/extraction/chunking/.
Only ProofChunker and its dependencies are needed here.
"""

from .data_classes import Chunk, ChunkResult
from .chunker import ProofChunker
from .comment_remover import CommentRemover

__all__ = [
    'Chunk',
    'ChunkResult',
    'ProofChunker',
    'CommentRemover',
]
