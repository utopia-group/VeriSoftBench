"""Simplified prompt builder for VeriSoftBench evaluation."""

import json
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Set

import utils.utils as utils


# Repos that have pre-generated full_limited prompts (too large for full context)
FULL_LIMITED_REPOS = {"ArkLib", "lean-mlir"}


class PromptBuilder:
    """Build and load prompts for theorem proving evaluation."""

    # Pre-generated prompt directories (relative to project root)
    # GENERATED_DIR is optional — if missing, prompts are built from JSONL entries
    GENERATED_DIR = Path("prompts/generated")
    FULL_LIMITED_DIR = Path("prompts/full_limited")

    def __init__(self, prompts_dir: Path, mode: str = "filtered_context"):
        """
        Initialize with path to prompts/ directory.

        Args:
            prompts_dir: Path to prompts/ folder containing templates/
            mode: Context mode - "filtered_context" (curated) or "full_context"
        """
        self.prompts_dir = prompts_dir
        self.mode = mode

        # Full context state (lazily loaded)
        self._wheels_helpers: Optional[Set[str]] = None
        self._repo_lib_items: Optional[Dict] = None
        self._repo_context: Dict[str, Dict[str, List[str]]] = {}

    # =========================================================================
    # System Prompt
    # =========================================================================

    def retrive_sys_prompt(self, template_name: str = "init.txt") -> str:
        """Load system prompt from template."""
        return utils.load_prompt_template(template_name, self.prompts_dir)

    # =========================================================================
    # User Prompt (Initial Proof Generation)
    # =========================================================================

    def build_user_prompt(
        self,
        theorem_entry: Dict[str, Any],
        mode: str = "filtered_context"
    ) -> str:
        """
        Build user prompt for initial proof generation.

        First tries to load a pre-generated prompt.
        If not found, builds from JSONL entry data using templates.

        Args:
            theorem_entry: Entry from verisoftbench.jsonl
            mode: Context mode - "filtered_context" or "full_context"

        Returns:
            Complete user prompt string
        """
        effective_mode = mode or self.mode

        if effective_mode == "full_context":
            return self._build_full_context_prompt(theorem_entry)

        # Filtered context: try pre-generated, then build from entry
        prompt = self._load_pregenerated_prompt(theorem_entry)
        if prompt is not None:
            if "### Input Information" in prompt:
                user_prompt = "### Input Information\n" + prompt.split("### Input Information")[1]
                return user_prompt
            return prompt

        return self._build_prompt_from_entry(theorem_entry)

    def _load_pregenerated_prompt(self, entry: Dict[str, Any]) -> Optional[str]:
        """Try to load a pre-generated prompt file."""
        lean_root = entry.get("lean_root", "")
        thm_name = entry.get("thm_name", "")
        rel_path = entry.get("rel_path", "")

        filename = self._get_safe_filename(thm_name, rel_path)
        prompt_path = self.GENERATED_DIR / lean_root / filename

        if prompt_path.exists():
            try:
                return prompt_path.read_text(encoding="utf-8")
            except Exception:
                pass
        return None

    def _build_prompt_from_entry(self, entry: Dict[str, Any]) -> str:
        """Build filtered_context prompt from JSONL entry data."""
        user_template = (self.prompts_dir / "user.txt").read_text(encoding="utf-8")
        examples = self._load_examples(self.prompts_dir)

        task_prompt = (
            self._format_section("used_lib_defs", self._render_lib_items(entry.get("used_lib_defs", [])))
            + self._format_section("used_repo_defs", self._render_content_items(entry.get("used_repo_defs", [])))
            + self._format_section("lib_lemmas", self._render_lib_items(entry.get("lib_lemmas", [])))
            + self._format_section("repo_lemmas", self._render_content_items(entry.get("repo_lemmas", [])))
            + self._format_section("local_lemmas", "")  # always empty
            + self._format_section("local_ctx", entry.get("local_ctx", ""))
            + self._format_section("target_theorem", entry.get("target_theorem", ""))
        )

        full_prompt = user_template.format(examples, task_prompt)

        if "### Input Information" in full_prompt:
            return "### Input Information\n" + full_prompt.split("### Input Information")[1]
        return full_prompt

    # =========================================================================
    # Full Context Prompt Generation
    # =========================================================================

    def _build_full_context_prompt(self, entry: Dict[str, Any]) -> str:
        """Build a full_context prompt for a theorem entry."""
        # Try full_limited fallback for oversized repos
        full_limited = self._load_full_limited_prompt(entry)
        if full_limited is not None:
            if "### Input Information" in full_limited:
                return "### Input Information\n" + full_limited.split("### Input Information")[1]
            return full_limited

        repo_name = entry.get("lean_root", "")

        # Load template and examples
        user_template = (self.prompts_dir / "user_full_context.txt").read_text(encoding="utf-8")
        examples = self.format_examples()

        # Get repo-level context (cached)
        repo_items = self._get_repo_full_context_items(repo_name)
        all_defs_str = "\n\n".join(repo_items["all_defs"])
        all_lemmas_list = repo_items["all_lemmas"]

        # Per-theorem filtering of lemmas
        excluded_stmts = self._get_excluded_local_lemma_statements(entry)

        def should_exclude(lemma: str) -> bool:
            lemma_normalized = _normalize_lemma_stmt(
                _strip_theorem_proof(lemma, include_assign=False)
            )
            for excluded in excluded_stmts:
                if (lemma_normalized == excluded or
                        excluded.startswith(lemma_normalized) or
                        lemma_normalized.startswith(excluded)):
                    return True
            return False

        filtered_lemmas = [l for l in all_lemmas_list if l.strip() and not should_exclude(l)]
        all_lemmas_str = "\n\n".join(filtered_lemmas)

        # local_ctx and target_theorem from JSONL
        local_ctx = entry.get("local_ctx", "")
        target_theorem = entry.get("target_theorem", "")

        # Assemble sections
        task_prompt = (
            self._format_section("all_available_defs", all_defs_str)
            + self._format_section("all_available_lemmas", all_lemmas_str)
            + self._format_section("local_ctx", local_ctx)
            + self._format_section("target_theorem", target_theorem)
        )

        full_prompt = user_template.format(examples, task_prompt)

        if "### Input Information" in full_prompt:
            return "### Input Information\n" + full_prompt.split("### Input Information")[1]
        return full_prompt

    def _load_full_limited_prompt(self, entry: Dict[str, Any]) -> Optional[str]:
        """Try to load a pre-generated full_limited prompt for oversized repos."""
        repo_name = entry.get("lean_root", "")
        if repo_name not in FULL_LIMITED_REPOS:
            return None

        thm_name = entry.get("thm_name", "")
        rel_path = entry.get("rel_path", "")
        filename = self._get_safe_filename(thm_name, rel_path)
        prompt_path = self.FULL_LIMITED_DIR / repo_name / filename

        if prompt_path.exists():
            try:
                return prompt_path.read_text(encoding="utf-8")
            except Exception:
                pass
        return None

    def _load_wheels_helpers(self) -> Set[str]:
        """Load wheels_helpers_final.json - lemmas to exclude from full context."""
        if self._wheels_helpers is not None:
            return self._wheels_helpers

        from config.paths import DATA_DIR
        wheels_path = DATA_DIR / "wheels_helpers_final.json"
        helpers = set()
        if wheels_path.exists():
            with open(wheels_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
                for lemma_entry in data.get("lemmas", []):
                    if "name" in lemma_entry:
                        helpers.add(lemma_entry["name"])
        self._wheels_helpers = helpers
        return helpers

    def _load_repo_lib_items(self) -> Dict:
        """Load per-repo library items."""
        if self._repo_lib_items is not None:
            return self._repo_lib_items

        from config.paths import FULL_CONTEXT_DIR
        lib_items_path = FULL_CONTEXT_DIR / "repo_lib_items.json"
        if lib_items_path.exists():
            with open(lib_items_path, 'r', encoding='utf-8') as f:
                self._repo_lib_items = json.load(f)
        else:
            self._repo_lib_items = {}
        return self._repo_lib_items

    def _load_repo_index(self, repo_name: str) -> Dict:
        """Load the repo index JSON for a repository (cached)."""
        cache_key = f"_repo_index_{repo_name}"
        cached = getattr(self, cache_key, None)
        if cached is not None:
            return cached

        from config.paths import REPO_INDEX_DIR
        index_path = REPO_INDEX_DIR / f"{repo_name}.json"
        if index_path.exists():
            with open(index_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
        else:
            data = {}
        setattr(self, cache_key, data)
        return data

    def _get_repo_full_context_items(self, repo_name: str) -> Dict[str, List[str]]:
        """Get full context items (defs and lemmas lists) for a repo."""
        if repo_name in self._repo_context:
            return self._repo_context[repo_name]

        wheels_helpers = self._load_wheels_helpers()
        repo_lib_items = self._load_repo_lib_items()

        all_defs = []
        all_lemmas = []

        # 1. Collect from repo index
        repo_index = self._load_repo_index(repo_name)

        for _file_path, defs in sorted(repo_index.get("definitions_by_file", {}).items()):
            for entry in defs:
                kind = entry.get("kind", "")
                text = entry.get("text", "")
                if not text:
                    continue
                if kind in ["macro", "elab"]:
                    if not _is_tactic_macro(text):
                        all_defs.append(_strip_definition_proof(text))
                elif kind in ["def", "abbrev", "structure", "inductive", "class", "instance"]:
                    all_defs.append(_strip_definition_proof(text))

        for _file_path, thms in sorted(repo_index.get("theorems_by_file", {}).items()):
            for entry in thms:
                kind = entry.get("kind", "")
                text = entry.get("text", "")
                name = entry.get("name", "")
                if not text:
                    continue
                if kind in ["lemma", "theorem"]:
                    if name not in wheels_helpers:
                        all_lemmas.append(_strip_theorem_proof(text, include_assign=False))

        # 2. Add library items from repo_lib_items.json
        items = repo_lib_items.get(repo_name, {})
        for lib_def in items.get("lib_defs", []):
            name = lib_def.get("name", "")
            module = lib_def.get("module", "")
            if name and module:
                all_defs.append(f"{name} in {module}")

        for lib_lemma in items.get("lib_lemmas", []):
            name = lib_lemma.get("name", "")
            module = lib_lemma.get("module", "")
            if name and module and name not in wheels_helpers:
                all_lemmas.append(f"{name} in {module}")

        result = {"all_defs": all_defs, "all_lemmas": all_lemmas}
        self._repo_context[repo_name] = result
        return result

    def _get_excluded_local_lemma_statements(self, entry: Dict[str, Any]) -> Set[str]:
        """Get lemma statements to exclude for a specific theorem."""
        repo_name = entry.get("lean_root", "")
        rel_path = entry.get("rel_path", "")
        thm_name = entry.get("thm_name", "")

        excluded_statements = set()

        # Load theorems for the file from repo index
        repo_index = self._load_repo_index(repo_name)
        theorems = repo_index.get("theorems_by_file", {}).get(rel_path, [])

        if not theorems:
            return excluded_statements

        # Find target theorem position and collect exclusions
        target_found = False
        for thm in theorems:
            thm_kind = thm.get("kind", "")
            thm_entry_name = thm.get("name", "")
            thm_text = thm.get("text", "").strip()
            thm_aliases = thm.get("aliases", [])

            if thm_kind in ["lemma", "theorem"] and thm_text:
                lemma_stmt = _strip_theorem_proof(thm_text, include_assign=False)

                if thm_entry_name == thm_name or thm_name in thm_aliases:
                    target_found = True
                    excluded_statements.add(_normalize_lemma_stmt(lemma_stmt))
                elif target_found:
                    excluded_statements.add(_normalize_lemma_stmt(lemma_stmt))

        # Also exclude used_local_lemmas (information leakage prevention)
        used_local_lemmas = entry.get("used_local_lemmas", [])
        for local_lemma in used_local_lemmas:
            if isinstance(local_lemma, dict):
                content = local_lemma.get("content", "")
                if content:
                    lemma_stmt = _strip_theorem_proof(content, include_assign=False)
                    excluded_statements.add(_normalize_lemma_stmt(lemma_stmt))

        return excluded_statements

    # =========================================================================
    # Fix Prompt (Error Repair)
    # =========================================================================

    def build_fix_user_prompt(
        self,
        mode: str,
        theorem_entry: Dict[str, Any],
        thm_stmt: str,
        err_msg: str,
        generated_proof: str,
        aux_lemmas: str,
        file_content: str = "",
        compiled_file_path: Optional[Path] = None
    ) -> str:
        """
        Build prompt for proof fixing/repair.

        Args:
            mode: Context mode
            theorem_entry: Entry from verisoftbench.jsonl
            thm_stmt: Theorem statement
            err_msg: Error message from compilation
            generated_proof: The failed proof
            aux_lemmas: Auxiliary lemmas
            file_content: Local context for verification
            compiled_file_path: Path to compiled file (for error formatting)

        Returns:
            Complete fix prompt string
        """
        clean_name = utils.clean_thm_name(theorem_entry["thm_name"])
        rel_path_stem = theorem_entry["rel_path"].split('/')[-1].replace(".lean", ".txt")
        filename = f"{clean_name}__{rel_path_stem}"

        # Extract local_ctx from pre-generated prompt
        lean_root = theorem_entry.get("lean_root", "")
        prompt_path = self.GENERATED_DIR / lean_root / filename
        fix_ctxs = self._extract_local_ctx(prompt_path)

        # Load fix template
        prompt_template = utils.load_prompt_template("fix.txt", self.prompts_dir)

        # Get the compiled file content for error formatting
        compiled_content = ""
        if compiled_file_path:
            try:
                compiled_content = Path(compiled_file_path).read_text(encoding="utf-8")
            except Exception:
                compiled_content = ""

        if compiled_content:
            full_file_content = compiled_content
        else:
            full_file_content = utils.format_generated_lean(
                file_content, thm_stmt, generated_proof, aux_lemmas
            ) if file_content else ""

        formatted_err_msg = self.format_error_msg(err_msg, full_file_content) if full_file_content else err_msg

        full_thm_stmt_proof = f"{thm_stmt}\n{generated_proof}"

        def format_section(tag: str, content: str) -> str:
            if not content:
                return ""
            return f"<{tag}>\n{content}\n</{tag}>\n\n"

        task_prompt = (
            format_section("code_before_error", fix_ctxs)
            + format_section("potential_broken_lemmas", aux_lemmas)
            + format_section("potential_broken_theorem", full_thm_stmt_proof)
            + format_section("err_msg", formatted_err_msg)
        )

        return prompt_template.format(task_prompt)

    # =========================================================================
    # Error Message Formatting
    # =========================================================================

    def format_error_msg(self, err_msg: str, file_content: str) -> str:
        """Format error message with contextual information from the file."""
        if not err_msg:
            return ""
        lines = file_content.split('\n')
        formatted_errors = []

        # Handle incomplete proof errors (declaration uses 'sorry'/'admit')
        incomplete_errors = []
        remaining_msg_lines = []
        for line in err_msg.split('\n'):
            if re.match(r"declaration '.+' uses '(?:sorry|admit)'", line.strip()):
                incomplete_errors.append(line.strip())
            else:
                remaining_msg_lines.append(line)

        formatted_errors.extend(incomplete_errors)
        remaining_err_msg = '\n'.join(remaining_msg_lines)

        # Split error message into individual errors (each starts with "Line X:Y")
        error_blocks = re.split(r'(Line \d+:\d+)', remaining_err_msg)

        i = 1
        while i < len(error_blocks):
            if i + 1 < len(error_blocks):
                line_header = error_blocks[i]
                error_content = error_blocks[i + 1]
                full_error = line_header + error_content

                match = re.match(r'Line (\d+):(\d+)', line_header)
                if match:
                    line_num = int(match.group(1))
                    char_num = int(match.group(2))
                    error_lower = full_error.lower()

                    if "unsolved goals" in error_lower:
                        formatted_error = self._format_unsolved_goals(line_num, full_error, lines)
                    elif "expected token" in error_lower or "unexpected token" in error_lower:
                        formatted_error = self._format_token_error(line_num, char_num, full_error, lines)
                    elif "no goals to be solved" in error_lower:
                        formatted_error = self._format_no_goals(line_num, full_error, lines)
                    else:
                        formatted_error = self._format_general_error(line_num, char_num, full_error, lines)

                    if formatted_error:
                        formatted_errors.append(formatted_error)

                i += 2
            else:
                i += 1

        final_error = ""
        for idx, msg in enumerate(formatted_errors):
            remove_msg = "Some required targets logged failures"
            if remove_msg in msg:
                msg = msg.split(remove_msg)[0]
            remove_msg2 = "Some required builds logged failures"
            if remove_msg2 in msg:
                msg = msg.split(remove_msg2)[0]
            final_error += f"<err_{idx+1}>\n{msg}\n</err_{idx+1}>\n"
        return final_error.strip()

    def _remove_error_line_number(self, err_msg: str) -> str:
        """Remove line number prefix from error message."""
        return re.sub(r'Line \d+:\d+\s*-\s*', '', err_msg)

    def _format_unsolved_goals(self, line_num: int, error_msg: str, lines: List[str]) -> str:
        result = []
        if 1 <= line_num <= len(lines):
            line_content = lines[line_num - 1]
            if line_content:
                result.append(line_content)

        res = "\n".join(result) if any(r.strip() for r in result) else ""
        res += "\n" + f"ErrorMsg: {self._remove_error_line_number(error_msg)}"
        res = res.replace("\n\n", "\n")
        return res

    def _format_token_error(self, line_num: int, char_num: int, error_msg: str, lines: List[str]) -> str:
        result = []
        if 1 <= line_num <= len(lines):
            line_content = lines[line_num - 1]
            result.append(line_content)

            if char_num > 0 and char_num <= len(line_content):
                result.append(f"{' ' * (char_num - 1)}^ (error at)")
            remaining = line_content[char_num:] if char_num > 0 else line_content
            if not remaining.strip() and line_num < len(lines):
                if "unexpected token" in error_msg.lower():
                    next_line_idx = line_num
                    while next_line_idx < len(lines) and not lines[next_line_idx].strip():
                        next_line_idx += 1
                    if next_line_idx < len(lines):
                        result.append(f"term after error position:\n{lines[next_line_idx]}")

        res = "\n".join(result) if any(r.strip() and not r.startswith("Error:") for r in result) or "Error:" in "\n".join(result) else ""
        res += "\n" + f"ErrorMsg: {self._remove_error_line_number(error_msg)}"
        res = res.replace("\n\n", "\n")
        return res

    def _format_no_goals(self, line_num: int, error_msg: str, lines: List[str]) -> str:
        result = []
        if line_num > 1 and line_num - 1 <= len(lines):
            prev_line = lines[line_num - 2]
            if prev_line:
                result.append(f"{prev_line}")
        if 1 <= line_num <= len(lines):
            curr_line = lines[line_num - 1]
            if curr_line:
                result.append(f"{curr_line}")

        res = f"ErrorMsg: No goals to be solved after `{result[0]}`, but `{result[1]}` was given.\n"
        res = res.replace("\n\n", "\n")
        return res

    def _format_general_error(self, line_num: int, char_num: int, error_msg: str, lines: List[str]) -> str:
        result = []
        if 1 <= line_num <= len(lines):
            line_content = lines[line_num - 1]
            if line_content:
                result.append(line_content)
                if char_num > 0 and char_num <= len(line_content):
                    result.append(f"{' ' * (char_num - 1)}^ (error at)")

        res = "\n".join(result)
        res += "\n" + f"ErrorMsg: {self._remove_error_line_number(error_msg)}"
        res = res.replace("\n\n", "\n")
        return res

    # =========================================================================
    # Helper Methods
    # =========================================================================

    def _format_section(self, tag: str, content: str) -> str:
        """Wrap content in XML tags. Returns empty string if content is empty."""
        if not content or not content.strip():
            return ""
        return f"<{tag}>\n{content}\n</{tag}>\n\n"

    def _render_lib_items(self, items: list) -> str:
        """Render [{name, module}] → 'name in module' lines."""
        lines = []
        for item in items:
            name = item.get("name", "")
            module = item.get("module", "")
            if module:
                lines.append(f"{name} in {module}")
            elif name:
                lines.append(name)
        return "\n".join(lines)

    def _render_content_items(self, items: list) -> str:
        """Render [{name, content}] → content blocks separated by blank lines."""
        parts = [item.get("content", "") for item in items if item.get("content", "").strip()]
        return "\n\n".join(parts)

    def _load_examples(self, templates_dir: Path) -> str:
        """Load and format example prompts from templates/examples/."""
        example_dir = templates_dir / "examples"
        if not example_dir.exists():
            return ""
        examples = []
        for i, example_file in enumerate(sorted(example_dir.glob("*.txt")), 1):
            examples.append(
                f"Example {i} ------------------- \n"
                + example_file.read_text(encoding="utf-8")
            )
        return "\n\n".join(examples)

    def format_examples(self, fix_mode: bool = False) -> str:
        """Read all example files and format them."""
        if fix_mode:
            example_dir = "fix_examples"
        elif self.mode == "full_context":
            example_dir = "examples_full_context"
        else:
            example_dir = "examples"

        examples = []
        i = 1
        example_path = self.prompts_dir / example_dir
        if example_path.exists():
            for example_file in sorted(example_path.glob("*.txt")):
                examples.append(f"Example {i} ------------------- \n" + utils.load_txt_file(example_file))
                i += 1

        return "\n\n".join(examples)

    def _get_safe_filename(self, thm_name: str, rel_path: str) -> str:
        """Generate a safe filename from theorem name and relative path."""
        source_name = Path(rel_path).stem
        safe_name = thm_name.replace("'", "_prime").replace(".", "_").replace("/", "_").replace("\\", "_")
        safe_name = re.sub(r'[^\w\-.]', '_', safe_name)
        return f"{safe_name}__{source_name}.txt"

    def _extract_local_ctx(self, file_path: Path) -> Optional[str]:
        """Extract the content within the last <local_ctx> tag from a prompt file."""
        try:
            content = utils.load_txt_file(file_path)
            pattern = r'<local_ctx>(.*?)</local_ctx>'
            matches = re.findall(pattern, content, re.DOTALL)
            if matches:
                return matches[-1].strip()
            return None
        except Exception:
            return None


# =========================================================================
# Module-level helper functions for proof stripping/filtering
# =========================================================================

def _strip_definition_proof(definition: str) -> str:
    """Remove proof body from a definition."""
    pos, pattern = utils.find_decl_body_separator(definition)
    if pos >= 0 and (':= by' in pattern or pattern == r':=\s+by\b'):
        return definition[:pos].rstrip() + " :="
    return utils.elide_proofs(definition)


def _strip_theorem_proof(theorem: str, include_assign: bool = True) -> str:
    """Remove proof body from theorem/lemma, returning only the statement."""
    pos, separator = utils.find_decl_body_separator(theorem)
    suffix = " :=" if include_assign else ""

    if pos >= 0:
        if (separator.startswith(':=') or separator in ['where', r'\bwhere\b']
                or separator.startswith(r'\|') or '|' in separator):
            return theorem[:pos].rstrip() + suffix
        elif separator == ':':
            return theorem.rstrip() + suffix

    match = re.search(r':=', theorem)
    if match:
        result = theorem[:match.start()].rstrip()
        return result + suffix if include_assign else result

    return theorem.rstrip() + suffix


def _is_tactic_macro(text: str) -> bool:
    """Check if a macro/elab definition is a tactic macro."""
    if re.search(r'(?:macro|elab)\s+(?:\([^)]*\)\s*)?"[^"]*".*:\s*tactic\s*=>', text):
        return True
    if re.search(r'\belab\s+\w+:\w+.*:\s*tactic\s*=>', text):
        return True
    return False


def _normalize_lemma_stmt(stmt: str) -> str:
    """Normalize a lemma statement for comparison."""
    return ' '.join(stmt.split())


