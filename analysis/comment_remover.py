"""
Utility for removing Lean comments while preserving line structure.
"""

import re
from typing import List, Tuple


class CommentRemover:
    """Removes Lean comments from source code while preserving line numbers.

    Lean has two types of comments:
    - Line comments: -- comment text
    - Block comments: /- comment text -/ (can be nested)

    This class removes both types while maintaining the same number of lines,
    allowing line number references to remain valid.
    """

    @staticmethod
    def remove_comments(text: str) -> str:
        """Remove line and block comments from Lean code, preserving line count.

        Block comments are removed FIRST because they may contain `--` sequences
        that would otherwise be incorrectly treated as line comment starts.
        For example: `/- Frame Rule ---- comment -/` has `--` inside a block comment.

        Args:
            text: Lean source code

        Returns:
            Source code with comments removed, preserving line structure
        """
        # First, remove block comments (they may contain `--` sequences)
        # Use a function to handle nested block comments
        def replace_block(match: re.Match) -> str:
            """Replace block comment with same number of newlines."""
            return "\n" * match.group(0).count("\n")

        # Remove non-nested block comments first
        text = re.sub(r"/-.*?-/", replace_block, text, flags=re.DOTALL)

        # Now remove line comments (everything after `--` on each line)
        # Note: This doesn't handle `--` inside strings, but that's rare in Lean
        lines = text.splitlines()
        cleaned_lines = []
        for line in lines:
            cleaned_lines.append(line.split("--", 1)[0])
        text = "\n".join(cleaned_lines)

        return text

    @staticmethod
    def remove_with_original(text: str) -> Tuple[str, List[str]]:
        """Remove comments and return both cleaned text and original lines.

        This is useful when you need to check original content (e.g., for
        doc comments) while parsing the cleaned version.

        Args:
            text: Lean source code

        Returns:
            Tuple of (cleaned_text, original_lines)
        """
        original_lines = text.splitlines()
        cleaned = CommentRemover.remove_comments(text)
        return cleaned, original_lines

    @staticmethod
    def remove_line_comments_only(text: str) -> str:
        """Remove only line comments, preserving block comments.

        Args:
            text: Lean source code

        Returns:
            Source code with line comments removed
        """
        lines = text.splitlines()
        cleaned_lines = [line.split("--", 1)[0] for line in lines]
        return "\n".join(cleaned_lines)
