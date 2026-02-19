"""
IdentifierExtractor: Extracts identifiers from Lean code.
"""

import re
from typing import Dict, Optional, Set

from config.lean_constants import LEAN_KEYWORDS

from analysis.comment_remover import CommentRemover
from analysis.lean_patterns import LEAN_ID_CHAR, LEAN_ID_START


class IdentifierExtractor:
    """Extracts identifiers from Lean code."""

    def extract(self, text: str, notation_map: Optional[Dict[str, str]] = None) -> Set[str]:
        """Extract identifiers (including dotted) from Lean code, skipping keywords."""
        if not text:
            return set()
        cleaned = CommentRemover.remove_comments(text)
        # Use character class from patterns.py, but need explicit lookbehind/lookahead
        # Includes Mathematical Script (𝒜-𝓏) for identifiers like wne𝒰
        pattern = (
            rf"(?<![A-Za-z0-9_'₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫])"
            rf"{LEAN_ID_START}{LEAN_ID_CHAR}*(?:\.{LEAN_ID_START}{LEAN_ID_CHAR}*)*"
            rf"(?![A-Za-z0-9_'₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫])"
        )

        # Detect projections to skip
        projection_pattern = re.compile(r'[}\)\]]\s*\.\s*(' + LEAN_ID_START + LEAN_ID_CHAR + r'*)')
        projection_identifiers = {m.group(1) for m in projection_pattern.finditer(cleaned)}

        # Detect named arguments to skip
        named_arg_pattern = re.compile(r'\(\s*(' + LEAN_ID_START + LEAN_ID_CHAR + r'*)\s*:=')
        named_arg_identifiers = {m.group(1) for m in named_arg_pattern.finditer(cleaned)}

        ids = set()
        for m in re.finditer(pattern, cleaned):
            tok = m.group(0)
            # Skip Lean keywords
            if tok in LEAN_KEYWORDS:
                continue
            # Skip wildcard pattern `_` - it's a pattern matcher, not a definition reference
            if tok == '_':
                continue
            if '.' not in tok and tok in projection_identifiers:
                continue
            if '.' not in tok and tok in named_arg_identifiers:
                continue
            ids.add(tok)
            # Add prefixes for qualified names (e.g., for Foo.bar.baz, add Foo and Foo.bar)
            # This helps track dependencies when Foo.bar is a definition and .baz is a field.
            # Prefixes that don't exist in the index will be filtered during resolution.
            if '.' in tok:
                parts = tok.split('.')
                for i in range(1, len(parts)):
                    prefix = '.'.join(parts[:i])
                    if prefix and prefix not in LEAN_KEYWORDS:
                        ids.add(prefix)

        # Extract notation symbols from the notation_map
        # Notations like ⤳⋆ contain Unicode operators not matched by the identifier pattern
        if notation_map:
            for symbol in notation_map.keys():
                # Skip macro: prefixed entries
                if symbol.startswith('macro:'):
                    continue
                # Check if the symbol appears in the cleaned text
                if symbol in cleaned:
                    ids.add(symbol)

        return ids

    def extract_projection_chains(self, text: str) -> Set[tuple]:
        """Extract projection chains like hM.1.nonsingular_inv.

        These are patterns where a local binding is followed by one or more
        numeric projections (.1, .2), then optionally a method call.

        Returns:
            Set of tuples: (base_identifier, method_name) or (base_identifier, None)
            For hM.1.nonsingular_inv -> ('hM', 'nonsingular_inv')
            For hM.1 -> ('hM', None)
        """
        if not text:
            return set()
        cleaned = CommentRemover.remove_comments(text)

        # Pattern: identifier followed by .digit(s), optionally followed by .method
        # Examples: hM.1, hM.1.nonsingular_inv, foo.2.3.bar
        projection_chain_pattern = re.compile(
            rf'({LEAN_ID_START}{LEAN_ID_CHAR}*)'  # base identifier
            rf'(?:\.\d+)+'                         # one or more numeric projections
            rf'(?:\.({LEAN_ID_START}{LEAN_ID_CHAR}*))?'  # optional method name
        )

        results = set()
        for m in projection_chain_pattern.finditer(cleaned):
            base = m.group(1)
            method = m.group(2)  # May be None if no method after projection
            if base not in LEAN_KEYWORDS:
                results.add((base, method))
        return results
