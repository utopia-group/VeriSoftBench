"""Main evaluation orchestration."""

import asyncio
import os
from pathlib import Path
import re
from typing import Dict, List, Any, Optional
from concurrent.futures import ThreadPoolExecutor, as_completed
import logging

from prompts.prompt_builder import PromptBuilder
from core.prover_interface import ProverInterface
from core.lean_interface import LeanREPL
import utils.utils as utils

def _clean_thm_stmt(thm_stmt: str, gt_proof: str = "") -> str:
    """
    Strip proof body from thm_stmt if it was accidentally included,
    and append the correct proof separator.

    The separator is chosen based on the ground-truth proof:
      - ``where`` proofs  → no separator in thm_stmt (``where`` stays in proof)
      - ``|`` pattern-match proofs → no separator (``|`` stays in proof)
      - everything else   → ``:=`` appended to thm_stmt

    This way the proof token (``where``, ``|``, or tactic body after ``:=``)
    is always part of ``theorem_proof``, not ``theorem_stmt``.
    """
    sep_idx, sep_pat = utils.find_decl_body_separator(thm_stmt)
    _body_pats = {':=\\s+by\\b', ':=\\s+match\\b', ':=\\s+calc\\b',
                  ':=\\s+fun\\b', ':=\\s+λ\\b', ':=\\s+begin\\b',
                  '\\bwhere\\b', '(?<!<)\\|\\s+(?!<)\\S'}
    if sep_idx > 0 and sep_pat in _body_pats:
        thm_stmt = thm_stmt[:sep_idx].rstrip()
    elif sep_idx > 0 and thm_stmt[sep_idx:sep_idx+2] == ':=':
        # Term-mode proof embedded in statement (e.g. `:= rfl`)
        thm_stmt = thm_stmt[:sep_idx].rstrip()

    # Determine whether the proof uses a non-standard separator
    gt_stripped = gt_proof.strip()
    uses_where = gt_stripped.startswith('where')
    uses_pipe = gt_stripped.startswith('|')

    # Strip any existing trailing separator
    stripped = thm_stmt.rstrip()
    if stripped.endswith(':='):
        stripped = stripped[:-2].rstrip()
    elif stripped.endswith('where'):
        stripped = stripped[:-5].rstrip()

    # For where / pattern-match proofs, leave the separator to the proof side.
    # For everything else, append `:=` to the statement.
    if uses_where or uses_pipe:
        thm_stmt = stripped
    else:
        thm_stmt = stripped + ' :='

    return thm_stmt


class BenchmarkEvaluator:
    """Main class for running benchmark evaluation."""
    def __init__(
        self,
        locator_data_dir: Path,
        context_data_dir: Path,
        lean_src_dir: Path,
        prompts_dir: Path,
        output_dir: Path,
        model_config: Dict[str, Any],
        fix_enabled: bool,
        max_fix_workers: int = 4,
        log_file: Optional[Path] = None,
        debug_output_dir: Optional[Path] = None,
        docker_container: str = None
    ):
        """
        Initialize evaluator with all necessary components.

        Args:
            locator_data_dir: Path to LocatorData/
            context_data_dir: Path to ContextData/
            lean_src_dir: Path to LeanSrc/
            prompts_dir: Path to Prompts/
            output_dir: Where to save results
            model_config: Model configuration dict
            fix_enabled: Whether to enable proof fixing
            max_fix_workers: Max parallel workers for fixing samples per task (default: 4)
            log_file: Optional path to write logs; stdout/stderr only if None
            debug_output_dir: Directory to save postprocessed Lean files for debugging (default: None, disabled)
            docker_container: Docker container name for Lean compilation (default: None, local)
        """
        self.locator_data_dir = locator_data_dir
        self.output_dir = output_dir

        self.prompt_builder = PromptBuilder(prompts_dir, mode=model_config.get("mode", "filtered_context"))
        self.prover = ProverInterface(model_config)
        self.lean_src_dir = lean_src_dir
        self.docker_container = docker_container
        self.lean_repl = LeanREPL(lean_src_dir, docker_container=docker_container)
        self.num_samples = model_config.get("num_samples", 1)
        self.fix_enabled = fix_enabled
        self.max_fix_workers = max_fix_workers
        self.mode = model_config.get("mode", "filtered_context")
        self.debug_output_dir = debug_output_dir

        # Setup logger for this module
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.INFO)

        # Remove any existing handlers to avoid duplicates
        self.logger.handlers = []

        # Create formatter
        formatter = logging.Formatter("%(asctime)s %(levelname)s %(name)s: %(message)s")

        # Console handler
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        console_handler.setFormatter(formatter)
        self.logger.addHandler(console_handler)

        # File handler (if specified)
        if log_file:
            log_file.parent.mkdir(parents=True, exist_ok=True)
            file_handler = logging.FileHandler(log_file, mode="w", encoding="utf-8")
            file_handler.setLevel(logging.INFO)
            file_handler.setFormatter(formatter)
            self.logger.addHandler(file_handler)

        # Prevent propagation to root logger (avoids duplicate logs)
        self.logger.propagate = False

        # For real-time incremental saving (set by evaluate_full_benchmark)
        self._incremental_save_dir = None

    def _read_source_file(self, lean_root: str, rel_path: str) -> str:
        """Read a Lean source file, using Docker if configured."""
        if self.docker_container:
            from config.paths import DOCKER_LEAN_SRC_DIR
            container_path = f"{DOCKER_LEAN_SRC_DIR}/{lean_root}/{rel_path}"
            content = self.lean_repl._docker_read_file(container_path)
            if content is None:
                raise FileNotFoundError(
                    f"File not found in Docker container: {container_path}"
                )
            return content
        return utils.load_txt_file(self.lean_src_dir / lean_root / rel_path)

    def _build_verif_context(
        self,
        lean_root: str,
        rel_path: str,
        imports: List[str],
        local_ctx: str,
        thm_stmt: str,
        thm_name: str,
    ) -> str:
        """
        Build verification context from the full source file.

        Always reads the actual source file and extracts everything before
        the target theorem.  Falls back to imports + local_ctx only when the
        file can't be read or the theorem can't be located.  This ensures a
        consistent verification environment regardless of prompt mode.
        """
        # Fix bad import prefixes (iris-lean uses srcDir="./src/")
        if lean_root == "iris-lean":
            imports = [imp.replace("import src.", "import ") for imp in imports]

        # Build fallback context
        fallback_ctx = "\n".join(imports) + "\n" + local_ctx

        # Try to read the full source file
        try:
            full_file_content = self._read_source_file(lean_root, rel_path)
        except (FileNotFoundError, Exception) as e:
            self.logger.warning(f"Could not read source file {lean_root}/{rel_path}: {e}")
            return fallback_ctx

        # Extract content before the theorem
        verif_ctx = utils.get_content_before_theorem(
            full_file_content, thm_stmt, thm_name=thm_name)

        if verif_ctx is None:
            # Theorem not found in file — try inserting before the last
            # closing 'end <Namespace>' so it stays in the right scope.
            ns_parts = thm_name.rsplit('.', 1)
            if len(ns_parts) > 1:
                ns_name = ns_parts[0]
                last_component = ns_name.rsplit('.', 1)[-1]
                end_pattern = re.compile(
                    r'^end\s+' + re.escape(ns_name) + r'\s*$|^end\s+'
                    + re.escape(last_component) + r'\s*$',
                    re.MULTILINE)
                matches = list(end_pattern.finditer(full_file_content))
                if matches:
                    verif_ctx = full_file_content[:matches[-1].start()]
                else:
                    verif_ctx = fallback_ctx
            else:
                verif_ctx = fallback_ctx

        # Strip 'noncomputable' from lemma/theorem declarations in context
        verif_ctx = re.sub(
            r'^noncomputable\s+(theorem|lemma)\b',
            r'\1',
            verif_ctx, flags=re.MULTILINE)

        # Sorry-out prove_correct tactic blocks that may fail in isolation
        verif_ctx = re.sub(
            r'(prove_correct\??\s+\w+)\s+by\n.*?(?=\n\n|\n(?:prove_correct|theorem|lemma|def|--[^\n]*\n\n))',
            r'\1 by sorry',
            verif_ctx, flags=re.DOTALL)

        # Handle @[attr] duplication: if thm_stmt starts with @[attr] and the
        # context already ends with the same attribute line, strip it from
        # thm_stmt won't help here (thm_stmt is not ours to modify), so strip
        # the trailing duplicate from context instead.
        stmt_lines = thm_stmt.split('\n')
        if stmt_lines and stmt_lines[0].strip().startswith('@[') and stmt_lines[0].strip().endswith(']'):
            attr = stmt_lines[0].strip()
            ctx_lines = verif_ctx.rstrip().split('\n')
            if ctx_lines and ctx_lines[-1].strip() == attr:
                verif_ctx = '\n'.join(ctx_lines[:-1]) + '\n'

        # Fix maxRecDepth for BLAKE3/ApplyRounds
        if "BLAKE3/ApplyRounds" in rel_path or "BLAKE3.ApplyRounds" in thm_name:
            lines = verif_ctx.split('\n')
            last_import = -1
            for i, line in enumerate(lines):
                if line.strip().startswith('import '):
                    last_import = i
            if last_import >= 0:
                lines.insert(last_import + 1, '\nset_option maxRecDepth 16384\nset_option maxHeartbeats 0')
            else:
                lines.insert(0, 'set_option maxRecDepth 16384\nset_option maxHeartbeats 0')
            verif_ctx = '\n'.join(lines)
            # Sorry-out expensive (by ...) proof blocks in context
            verif_ctx = re.sub(
                r'\(by\b\n.*?\)', '(by sorry)',
                verif_ctx, flags=re.DOTALL)

        return verif_ctx

    def _save_result_now(self, result: Dict[str, Any]) -> None:
        """Save a result immediately to disk (for real-time incremental saving)."""
        if not self._incremental_save_dir:
            return

        try:
            details_dir = self._incremental_save_dir / "details"
            details_dir.mkdir(parents=True, exist_ok=True)

            thm_name = result.get("thm_name", "unknown")
            safe_name = thm_name.replace("/", "_").replace("\\", "_")

            # Save JSON
            detail_file = details_dir / f"{safe_name}.json"
            utils.save_json(result, detail_file)

            # Save text files
            self._save_samples_as_text(result, details_dir, safe_name)

            self.logger.info(f"[SAVED] {thm_name} -> {detail_file}")
        except Exception as e:
            self.logger.error(f"Failed to save result for {result.get('thm_name', 'unknown')}: {e}")

    def _run_async_in_thread(self, coro):
        """Helper to properly run async coroutines in thread pool context."""
        # Create a new event loop for this thread
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            return loop.run_until_complete(coro)
        finally:
            loop.close()

    def fix_single_theorem(
        self,
        theorem_entry: Dict[str, Any],
        failed_attempt: Dict[str, Any],
        attempt_id: str,
        # retrieved_lemmas: List[str],
        max_fix_attempts: int = 3,
        result_for_saving: Dict[str, Any] = None,
        generated_res_dict_for_saving: List[Dict[str, Any]] = None
    ) -> List[Dict[str, Any]]:
        """
        Generate multiple fix samples for a single failed proof attempt.

        Args:
            theorem_entry: Original theorem entry from LocatorData JSONL
            failed_attempt: Single dict with 'proof', 'aux_lemmas', 'err_msg'
            retrieved_lemmas: Previously retrieved lemmas (for context continuity)
            max_fix_samples: Number of fix samples to generate

        Returns:
            List of fix sample dicts, each with 'proof', 'aux_lemmas', 'err_msg' (None if success)
        """
        thm_name = theorem_entry["thm_name"]
        thm_stmt = theorem_entry["thm_stmt"]
        rel_path = theorem_entry["rel_path"]
        imports = theorem_entry["imports"]
        lean_root = theorem_entry["lean_root"]
        suffix = theorem_entry.get("suffix", "")
        # Try 'local_ctxs' first, then fallback to 'local_ctx'
        local_context = theorem_entry.get("local_ctxs") or theorem_entry.get("local_ctx")
        if local_context is None:
            raise KeyError("Entry must have either 'local_ctxs' or 'local_ctx' key")

        # Always use full source file for verification context
        verif_local_context = theorem_entry.get('verif_local_ctxs')
        if verif_local_context is None:
            verif_local_context = self._build_verif_context(
                lean_root, rel_path, imports, local_context, thm_stmt, thm_name)
            theorem_entry['verif_local_ctxs'] = verif_local_context

        self.logger.info(f"Generating {max_fix_attempts} fix attempts for theorem: {thm_name}")

        fix_samples = []

        # Step 1: Build fix prompt with error feedback from failed_attempt
        sys_prompt = self.prompt_builder.retrive_sys_prompt()
        last_round_lemmas = failed_attempt['aux_lemmas']
        last_round_proof = failed_attempt['proof']
        last_round_err = failed_attempt['err_msg']
        last_round_debug_path = failed_attempt.get("debug_path")

        for i in range(max_fix_attempts):
            self.logger.info(f"Generating fix attempt {i+1}/{max_fix_attempts}")
            add_import_stmts = utils.get_add_imports_needed(theorem_entry, last_round_lemmas, last_round_proof, verif_local_context)
            if add_import_stmts:
                local_context_for_verification = add_import_stmts + "\n" + verif_local_context
            else:
                local_context_for_verification = verif_local_context
            user_prompt = self.prompt_builder.build_fix_user_prompt(
                self.mode,
                theorem_entry,
                thm_stmt,
                last_round_err,
                last_round_proof,
                last_round_lemmas,
                local_context_for_verification,
                compiled_file_path=last_round_debug_path
            )

            # Step 2: Generate multiple fix samples using neural prover
            # generated_fixes = asyncio.run(self.prover.generate_proof(sys_prompt, user_prompt, theorem_entry, num_samples=max_fix_samples))
            generated_fix = asyncio.run(self.prover.generate_proof(sys_prompt, user_prompt, theorem_entry, num_samples=1))[0]
            fixed_lemmas = utils.get_fixed_lemmas_from_llm_output(generated_fix)
            if "verina" in str(lean_root) and fixed_lemmas.strip():
                # replace all "lemma " with "theorem "
                fixed_lemmas = re.sub(r'lemma\b', 'theorem', fixed_lemmas)
            fixed_proof = utils.get_fixed_proof_from_llm_output(generated_fix)
            if not fixed_lemmas:
                fixed_lemmas = last_round_lemmas
            if not fixed_proof:
                fixed_proof = last_round_proof

            name_mapping = utils.find_conflicting_names_from_local_context(verif_local_context, fixed_lemmas)
            self.logger.info(f"Name conflicts from local context: {name_mapping}")
            fixed_lemmas, fixed_proof = utils.apply_name_replacements(fixed_lemmas, fixed_proof, name_mapping)
            while "axiom " in fixed_lemmas:
                fixed_lemmas = fixed_lemmas.replace("axiom ", "theorem ")
            # fixed_lemmas, fixed_proof = utils.update_proof_and_lemma_to_avoid_name_conflicts(verif_local_context, fixed_lemmas, fixed_proof)
            fixed_proof, fixed_lemmas = utils.clean_leaked_identifiers(theorem_entry, fixed_proof, fixed_lemmas)

            # PLACEHOLDER: Additional logic for full_context mode before verification
            local_context_for_verification = verif_local_context
            if self.mode in ("full_context", "full_context_limited"):
                # For example: modify local_context_for_verification, add additional checks, etc.
                add_import_stmts = utils.get_add_imports_needed(theorem_entry, fixed_lemmas, fixed_proof, local_context_for_verification)
                if add_import_stmts:
                    local_context_for_verification = add_import_stmts + "\n" + verif_local_context
                else:
                    local_context_for_verification = verif_local_context
            debug_path = self.debug_output_dir / f"{utils.clean_thm_name(thm_name)}_fix_{attempt_id}.lean" if self.debug_output_dir else None
            success, error_msg = self.lean_repl.verify_proof(
                thm_name=thm_name,
                repo_name=lean_root,
                rel_path=rel_path,
                local_context=local_context_for_verification,
                theorem_stmt=thm_stmt,
                theorem_proof=fixed_proof,
                proof_id=attempt_id, #fix is sequential, doesn't matter
                aux_lemmas=fixed_lemmas,
                suffix=suffix,
                debug_output_path=debug_path
            )

            # Step 4: Iteratively resolve "has already been declared" errors using compiler feedback
            max_conflict_resolution_attempts = 10
            attempt = 0
            while not success and error_msg and "has already been declared" in error_msg and attempt < max_conflict_resolution_attempts:
                attempt += 1
                self.logger.info(f"Attempting conflict resolution (attempt {attempt}/{max_conflict_resolution_attempts})")

                # Find conflicting names from error message
                name_mapping = utils.find_conflicting_names_from_error(error_msg, fixed_lemmas)

                if not name_mapping:
                    self.logger.info("No conflicting names found in error message, stopping conflict resolution")
                    break

                # Apply name replacements
                self.logger.info(f"Name conflicts from error message: {name_mapping}")
                fixed_lemmas, fixed_proof = utils.apply_name_replacements(fixed_lemmas, fixed_proof, name_mapping)
                while "axiom " in fixed_lemmas:
                    fixed_lemmas = fixed_lemmas.replace("axiom ", "theorem ")
                fixed_proof, fixed_lemmas = utils.clean_leaked_identifiers(theorem_entry, fixed_proof, fixed_lemmas)

                # Verify again
                debug_path = self.debug_output_dir / f"{utils.clean_thm_name(thm_name)}_fix_{attempt_id}_retry{attempt}.lean" if self.debug_output_dir else None
                success, error_msg = self.lean_repl.verify_proof(
                    thm_name=thm_name,
                    repo_name=lean_root,
                    rel_path=rel_path,
                    local_context=local_context_for_verification,
                    theorem_stmt=thm_stmt,
                    theorem_proof=fixed_proof,
                    proof_id=attempt_id, #fix is sequential, doesn't matter
                    aux_lemmas=fixed_lemmas,
                    suffix=suffix,
                    debug_output_path=debug_path
                )

                if success:
                    self.logger.info(f"Conflict resolution succeeded after {attempt} attempt(s)")
                elif "has already been declared" not in error_msg:
                    self.logger.info("No more 'has already been declared' errors")
                    break

            # Record result
            record = {
                "proof": fixed_proof,
                "aux_lemmas": fixed_lemmas,
                "err_msg": error_msg if not success else None,
                "debug_path": str(debug_path) if debug_path else None
            }
            fix_samples.append(record)

            # Update failed_attempt in place and save immediately
            failed_attempt["fixed"] = fix_samples.copy()
            if result_for_saving is not None and generated_res_dict_for_saving is not None:
                result_for_saving["generated_proofs"] = generated_res_dict_for_saving
                if success:
                    result_for_saving["fix_success"] = True
                self._save_result_now(result_for_saving)
                self.logger.info(f"[FIX SAVED] {thm_name} fix attempt {len(fix_samples)}")

            if success:
                self.logger.info(f"Fix sample succeeded for {thm_name}, stop further fix attempts")
                break
            else:
                self.logger.info(f"Fix sample failed: {error_msg}, continueing to next fix attempt")
                # update last round proof, lemmas, err for next fix attempt
                last_round_lemmas = fixed_lemmas
                last_round_proof = fixed_proof
                last_round_err = error_msg
                last_round_debug_path = str(debug_path) if debug_path else None

        return fix_samples

    def evaluate_single_theorem(
        self,
        theorem_entry: Dict[str, Any],
        use_retrieval: bool = True,
        retrieve_top_k: int = 20
    ) -> Dict[str, Any]:
        """
        Evaluate a single theorem.

        Args:
            theorem_entry: Entry from LocatorData JSONL
            use_retrieval: Whether to use lemma retrieval
            retrieve_top_k: Number of lemmas to retrieve

        Returns:
            Result dict with success status and metadata
        """
        thm_name = theorem_entry["thm_name"]
        thm_stmt = _clean_thm_stmt(
            theorem_entry["thm_stmt"],
            gt_proof=theorem_entry.get("ground_truth_proof", ""),
        )
        theorem_entry["thm_stmt"] = thm_stmt  # update for downstream use
        lean_root = theorem_entry["lean_root"]
        rel_path = theorem_entry["rel_path"]
        imports = theorem_entry["imports"]
        suffix = theorem_entry.get("suffix", "")
        # Try 'local_ctxs' first, then fallback to 'local_ctx'
        local_context = theorem_entry.get("local_ctxs") or theorem_entry.get("local_ctx")
        if local_context is None:
            raise KeyError("Entry must have either 'local_ctxs' or 'local_ctx' key")

        # Always use full source file for verification context (consistent
        # across all prompt modes).  Fall back to imports + local_ctx only
        # when the file can't be read or the theorem can't be located.
        verif_local_context = self._build_verif_context(
            lean_root, rel_path, imports, local_context, thm_stmt, thm_name)
        theorem_entry['verif_local_ctxs'] = verif_local_context

        self.logger.info(f"Evaluating theorem: {thm_name}")

        result = {
            "thm_name": thm_name,
            "thm_stmt": thm_stmt,
            "lean_root": lean_root,
            "rel_path": rel_path,
            "retrieved_lemmas": None,
            "success": False,
            "fix_success": False,
            "generated_proofs": None, # contain a list of dict, each with "proof", "aux_lemmas", and "err_msg"
        }

        try:
            # Step 1: Load available lemmas from imports
            # self.logger.info(f"Loading available lemmas from {len(imports)} imports")
            available_lemmas = [] # self.retriever.load_available_lemmas(imports)
            # self.logger.info(f"Loaded {len(available_lemmas)} available lemmas")

            # Step 2: Retrieve relevant lemmas (if enabled)
            # Step 3: Build prompt
            self.logger.info("Building prompt")
            sys_prompt = self.prompt_builder.retrive_sys_prompt()
            user_prompt = self.prompt_builder.build_user_prompt(
                theorem_entry=theorem_entry,
                mode = self.mode
            )

            # Step 4: Generate proof using neural prover
            self.logger.info("Generating proof with neural prover")
            generated_output = self._run_async_in_thread(self.prover.generate_proof(sys_prompt, user_prompt, theorem_entry, num_samples=self.num_samples))

            # Step 5: Verify proof in Lean
            self.logger.info("Verifying proof in Lean")

            # Extract repo name from path (e.g., "LeroyCompilerVerificationCourse/Fixpoints.lean")
            repo_name = lean_root

            # Helper function to verify a single proof
            def verify_single_proof(proof_output, proof_id):
                # need to record the error message for each proof attempt
                lemmas = utils.get_lemmas_from_llm_output(proof_output)
                reasoning = utils.get_reasoning_from_llm_output(proof_output)
                proof = utils.get_proof_from_llm_output(proof_output)
                if "verina" in str(lean_root) and lemmas.strip():
                    # replace all "lemma " with "theorem "
                    lemmas = re.sub(r'lemma\b', 'theorem', lemmas)

                name_mapping = utils.find_conflicting_names_from_local_context(verif_local_context, lemmas)
                self.logger.info(f"Name conflicts from local context: {name_mapping}")
                lemmas, proof = utils.apply_name_replacements(lemmas, proof, name_mapping)
                # lemmas, proof = utils.update_proof_and_lemma_to_avoid_name_conflicts(verif_local_context, lemmas, proof)

                # if local_lemmas is not empty, we need to use full verification mode
                # Use local copy to avoid UnboundLocalError when reassigning in nested scope
                local_context_to_verify = verif_local_context

                if self.mode in ("full_context", "full_context_limited"):
                    # TODO: Add full_context specific logic before compile_file/verify_proof
                    # For example: modify local_context_to_verify, add additional checks, etc.
                    add_import_stmts = utils.get_add_imports_needed(theorem_entry, lemmas, proof, local_context_to_verify)
                    if add_import_stmts:
                        local_context_for_verification = add_import_stmts + "\n" + verif_local_context
                    else:
                        local_context_for_verification = verif_local_context
                    pass

                while "axiom " in lemmas:
                    lemmas = lemmas.replace("axiom ", "theorem ")
                proof, lemmas = utils.clean_leaked_identifiers(theorem_entry, proof, lemmas)
                debug_path = self.debug_output_dir / f"{utils.clean_thm_name(thm_name)}_sample_{proof_id}.lean" if self.debug_output_dir else None
                success, error_msg = self.lean_repl.verify_proof(
                    thm_name=thm_name,
                    repo_name=repo_name,
                    rel_path=rel_path,
                    local_context=local_context_to_verify,
                    theorem_stmt=thm_stmt,
                    theorem_proof=proof,
                    proof_id=str(proof_id),
                    aux_lemmas=lemmas,
                    suffix = suffix,
                    debug_output_path=debug_path
                )

                # Iteratively resolve "has already been declared" errors using compiler feedback
                max_conflict_resolution_attempts = 1
                attempt = 0
                while not success and error_msg and "has already been declared" in error_msg and attempt < max_conflict_resolution_attempts:
                    attempt += 1
                    self.logger.info(f"Proof {proof_id}: Attempting conflict resolution (attempt {attempt}/{max_conflict_resolution_attempts})")

                    # Find conflicting names from error message
                    name_mapping = utils.find_conflicting_names_from_error(error_msg, lemmas)

                    if not name_mapping:
                        self.logger.info(f"Proof {proof_id}: No conflicting names found in error message, stopping conflict resolution")
                        break

                    # Apply name replacements
                    self.logger.info(f"Name conflicts from error message: {name_mapping}")
                    lemmas, proof = utils.apply_name_replacements(lemmas, proof, name_mapping)

                    # Verify again
                    while "axiom " in lemmas:
                        lemmas = lemmas.replace("axiom ", "theorem ")
                    proof, lemmas = utils.clean_leaked_identifiers(theorem_entry, proof, lemmas)
                    debug_path = self.debug_output_dir / f"{utils.clean_thm_name(thm_name)}_sample_{proof_id}_retry{attempt}.lean" if self.debug_output_dir else None
                    success, error_msg = self.lean_repl.verify_proof(
                        thm_name=thm_name,
                        repo_name=repo_name,
                        rel_path=rel_path,
                        local_context=local_context_to_verify,
                        theorem_stmt=thm_stmt,
                        theorem_proof=proof,
                        proof_id=str(proof_id),
                        aux_lemmas=lemmas,
                        suffix=suffix,
                        debug_output_path=debug_path
                    )

                    if success:
                        self.logger.info(f"Proof {proof_id}: Conflict resolution succeeded after {attempt} attempt(s)")
                    elif "has already been declared" not in error_msg:
                        self.logger.info(f"Proof {proof_id}: No more 'has already been declared' errors")
                        break

                record = {
                    "proof_id": proof_id,
                    "proof": proof,
                    "aux_lemmas": lemmas,
                    "reasoning": reasoning,
                    "err_msg": None if success else error_msg,
                    "debug_path": str(debug_path) if debug_path else None
                }

                if success:
                    self.logger.info(f"Theorem {thm_name} proof {proof_id} proved successfully!")
                else:
                    self.logger.info(f"Theorem {thm_name} proof {proof_id} failed: {error_msg}")

                return record, success

            # Parallelize proof verification using ThreadPoolExecutor
            generated_res_dict = []
            with ThreadPoolExecutor(max_workers=min(len(generated_output), 8)) as executor:
                future_to_proof = {
                    executor.submit(verify_single_proof, proof, idx): (proof, idx)
                    for idx, proof in enumerate(generated_output)
                }

                for future in as_completed(future_to_proof):
                    record, success = future.result()
                    generated_res_dict.append(record)
                    if success:
                        result["success"] = True

                    # Save after each sample verification (real-time)
                    result["generated_proofs"] = generated_res_dict.copy()
                    self._save_result_now(result)

            if not result["success"]:
                result["success"] = False

            if result["success"]:
                result["generated_proofs"] = generated_res_dict
                self.logger.info(f"Theorem {thm_name} proved successfully!")
            else:
                self.logger.info(f"Theorem {thm_name} failed")
                if self.fix_enabled:
                    self.logger.info(f"Fixing procedure triggered")

                    # Generate fix samples for each failed attempt in parallel
                    failed_attempts = [fa for fa in generated_res_dict if fa["err_msg"] is not None]

                    if failed_attempts:
                        with ThreadPoolExecutor(max_workers=self.max_fix_workers) as executor:
                            # Submit all fix tasks
                            future_to_attempt = {
                                executor.submit(
                                    self.fix_single_theorem,
                                    theorem_entry=theorem_entry,
                                    failed_attempt=failed_attempt,
                                    attempt_id=f"fix_{failed_attempt['proof_id']}",
                                    result_for_saving=result,
                                    generated_res_dict_for_saving=generated_res_dict
                                ): failed_attempt
                                for failed_attempt in failed_attempts
                            }

                            # Collect results as they complete
                            for future in as_completed(future_to_attempt):
                                failed_attempt = future_to_attempt[future]
                                try:
                                    fix_samples = future.result()
                                    failed_attempt["fixed"] = fix_samples

                                    # Check if any fix succeeded
                                    for fix in fix_samples:
                                        if fix["err_msg"] is None:
                                            result["fix_success"] = True
                                            self.logger.info(f"Theorem {thm_name} fixed successfully!")
                                            break

                                    # Save after each fix attempt (real-time)
                                    result["generated_proofs"] = generated_res_dict
                                    self._save_result_now(result)

                                except Exception as exc:
                                    self.logger.error(f"Fix attempt generated an exception: {exc}")
                                    failed_attempt["fixed"] = []

                    # Set empty fix list for successful attempts
                    for failed_attempt in generated_res_dict:
                        if failed_attempt["err_msg"] is None and "fixed" not in failed_attempt:
                            failed_attempt["fixed"] = []
                result["generated_proofs"] = generated_res_dict


        except Exception as e:
            self.logger.error(f"Error evaluating theorem {thm_name}: {e}")
            result["error_message"] = str(e)
            # print traceback
            import traceback
            traceback.print_exc()

        return result

    def evaluate_full_benchmark(
        self,
        entries,
        use_retrieval: bool = True,
        retrieve_top_k: int = 20,
        max_workers: int = 8,
        incremental_save_dir: Path = None
    ) -> Dict[str, Any]:
        """
        Evaluate all theorems in benchmark.

        Args:
            entries: List of theorem entries to evaluate
            use_retrieval: Whether to use lemma retrieval
            retrieve_top_k: Number of lemmas to retrieve
            max_workers: Number of parallel workers
            incremental_save_dir: If provided, save results incrementally to this directory

        Returns:
            Aggregated results with statistics
        """
        accumulated_results = []
        succeeded_thms = []

        # Setup incremental save directory if provided
        details_dir = None
        if incremental_save_dir:
            self._incremental_save_dir = incremental_save_dir
            details_dir = incremental_save_dir / "details"
            details_dir.mkdir(parents=True, exist_ok=True)
            self.logger.info(f"Incremental saving enabled: {details_dir}")

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Submit all tasks
            future_to_entry = {
                executor.submit(
                    self.evaluate_single_theorem,
                    entry,
                    use_retrieval,
                    retrieve_top_k
                ): entry for entry in entries
            }

            # Collect results as they complete
            for future in as_completed(future_to_entry):
                result = future.result()
                accumulated_results.append(result)
                if result["success"] or result.get("fix_success", False):
                    succeeded_thms.append(result["thm_name"])

                # Save result incrementally
                if details_dir:
                    try:
                        thm_name = result.get("thm_name", "unknown")
                        # Sanitize theorem name for filename
                        safe_name = thm_name.replace("/", "_").replace("\\", "_")

                        # Save JSON result
                        detail_file = details_dir / f"{safe_name}.json"
                        utils.save_json(result, detail_file)

                        # Save text files for each sample
                        self._save_samples_as_text(result, details_dir, safe_name)

                        self.logger.info(f"Saved result for {thm_name} to {detail_file}")
                    except Exception as e:
                        self.logger.error(f"Failed to save incremental result for {thm_name}: {e}")

        # Compute overall statistics
        total = len(accumulated_results)
        proved_wo_fix = sum(1 for r in accumulated_results if r["success"])
        proved_w_fix = sum(1 for r in accumulated_results if r["success"] or r["fix_success"])

        summary = {
            "total_theorems": total,
            "theorems_proved_wo_fix": proved_wo_fix,
            "theorems_proved_w_fix": proved_w_fix,
            "proof_success_rate_wo_fix": proved_wo_fix / total if total > 0 else 0.0,
            "proof_success_rate_w_fix": proved_w_fix / total if total > 0 else 0.0,
            "succeeded_theorems": succeeded_thms,
        }

        return summary, accumulated_results

    def _save_samples_as_text(self, result: Dict[str, Any], details_dir: Path, safe_name: str) -> None:
        """
        Save each sample and its fix attempts as readable text files.

        Creates a directory structure like:
            details/
            ├── theorem_name.json
            └── theorem_name/
                ├── sample_0.txt
                ├── sample_0_fix_0.txt
                ├── sample_0_fix_1.txt
                ├── sample_1.txt
                └── ...
        """
        generated_proofs = result.get("generated_proofs", [])
        if not generated_proofs:
            return

        # Create subdirectory for this theorem's samples
        samples_dir = details_dir / safe_name
        samples_dir.mkdir(parents=True, exist_ok=True)

        thm_name = result.get("thm_name", "unknown")

        for sample in generated_proofs:
            proof_id = sample.get("proof_id", 0)
            proof = sample.get("proof", "")
            aux_lemmas = sample.get("aux_lemmas", "")
            reasoning = sample.get("reasoning", "")
            err_msg = sample.get("err_msg")

            # Build sample content
            status = "SUCCESS" if err_msg is None else "FAILED"
            content = f"-- Theorem: {thm_name}\n"
            content += f"-- Sample: {proof_id}\n"
            content += f"-- Status: {status}\n"
            content += "-- " + "=" * 60 + "\n\n"

            if reasoning:
                content += f"/-\nReasoning:\n{reasoning}\n-/\n\n"

            if aux_lemmas:
                content += f"-- Auxiliary Lemmas:\n{aux_lemmas}\n\n"

            content += f"-- Proof:\n{proof}\n"

            if err_msg:
                content += f"\n/-\nError:\n{err_msg}\n-/\n"

            # Save sample file
            sample_file = samples_dir / f"sample_{proof_id}.txt"
            with open(sample_file, 'w', encoding='utf-8') as f:
                f.write(content)

            # Save fix attempts if any
            fixes = sample.get("fixed", [])
            for fix_idx, fix in enumerate(fixes):
                fix_proof = fix.get("proof", "")
                fix_lemmas = fix.get("aux_lemmas", "")
                fix_err = fix.get("err_msg")

                fix_status = "SUCCESS" if fix_err is None else "FAILED"
                fix_content = f"-- Theorem: {thm_name}\n"
                fix_content += f"-- Sample: {proof_id}, Fix Attempt: {fix_idx}\n"
                fix_content += f"-- Status: {fix_status}\n"
                fix_content += "-- " + "=" * 60 + "\n\n"

                if fix_lemmas:
                    fix_content += f"-- Fixed Auxiliary Lemmas:\n{fix_lemmas}\n\n"

                fix_content += f"-- Fixed Proof:\n{fix_proof}\n"

                if fix_err:
                    fix_content += f"\n/-\nError:\n{fix_err}\n-/\n"

                fix_file = samples_dir / f"sample_{proof_id}_fix_{fix_idx}.txt"
                with open(fix_file, 'w', encoding='utf-8') as f:
                    f.write(fix_content)

    def save_results(self, summary: dict, results: List[Dict[str, Any]], output_dir: Path) -> None:
        """Save evaluation results to file."""
        summary_file = output_dir / "summary.json"
        # write summary file
        utils.save_json(summary, summary_file)

        details_dir = output_dir / "details"
        details_dir.mkdir(parents=True, exist_ok=True)
        for result in results:
            thm_name = result["thm_name"]
            rel_path = result.get("rel_path", "")
            file_stem = Path(rel_path).stem if rel_path else ""
            # Use same naming as prompt files: thm_name__file_stem.json to avoid collisions
            if file_stem:
                detail_file = details_dir / f"{thm_name}__{file_stem}.json"
            else:
                detail_file = details_dir / f"{thm_name}.json"
            utils.save_json(result, detail_file)
