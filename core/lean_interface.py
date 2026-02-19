"""Interface to Lean REPL for proof verification."""

import logging
from pathlib import Path
import re
from typing import Dict, Any, Tuple
import subprocess

import utils.utils as utils

DOCKER_LEAN_REPOS_DIR = "/workspace/lean_repos"


class LeanREPL:
    """Interface to Lean 4 REPL for proof compilation and verification."""

    def __init__(self, lean_src_dir: Path, docker_container: str = None):
        """
        Initialize Lean REPL interface.

        Args:
            lean_src_dir: Path to LeanSrc/ directory (host path for local
                          mode; used as reference for container path mapping
                          in Docker mode)
            docker_container: If set, run lake/lean commands inside this
                              Docker container via `docker exec`. File I/O
                              (read/write/delete) is piped through docker
                              exec — no bind mounts required.
        """
        self.lean_src_dir = lean_src_dir
        self.docker_container = docker_container

    def get_initial_proof_state(
        self,
        repo_name: str,
        file_path: str,
        theorem_name: str
    ) -> str:
        """
        Extract initial proof state for a theorem.

        Args:
            repo_name: Name of repo in LeanSrc/
            file_path: Relative path to Lean file
            theorem_name: Name of theorem

        Returns:
            Initial proof state string
        """
        pass


    def verify_proof(
        self,
        thm_name: str,
        repo_name: str,
        rel_path: str,
        local_context: str,
        theorem_stmt: str,
        theorem_proof: str,
        proof_id: str,
        aux_lemmas: str,
        suffix: str,
        debug_output_path: Path = None,
    ) -> Tuple[bool, str]:
        """
        Replace proof body and attempt compilation.

        Args:
            repo_name: Name of repo in LeanSrc/
            file_path: Relative path to Lean file
            theorem_name: Name of theorem
            generated_proof: Generated proof body to test

        Returns:
            Tuple of (success: bool, error_message: str)
        """
        use_docker = self.docker_container is not None

        # Create a new file in the same file_path, but replace the last part of name with <name>_llm_gen.lean
        path_obj = Path(rel_path)
        original_name = path_obj.stem  # Gets filename without extension
        new_filename = f"{original_name}_{utils.clean_thm_name(thm_name)}_v{proof_id}.lean"

        # In Docker mode, file I/O targets the container filesystem
        if use_docker:
            container_new_file = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}/{path_obj.parent / new_filename}"
            container_source_file = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}/{rel_path}"
        # Host path (used for local mode and debug output)
        new_file_path = self.lean_src_dir / repo_name / path_obj.parent / new_filename

        local_context = local_context.replace("\\n", "\n")  # Normalize line endings
        theorem_stmt = theorem_stmt.replace("\\n", "\n")  # Normalize line endings

        # change the aux_lemmas names and their usage in the theorem proof if they collapse with local_content
        if "verina" in str(repo_name) and aux_lemmas.strip():
            # replace all "lemma " with "theorem "
            aux_lemmas = re.sub(r'lemma\b', 'theorem', aux_lemmas)

        # Compute remaining mutual content for forward reference resolution
        remaining_mutual_content = ""
        try:
            if use_docker:
                full_file_content = self._docker_read_file(container_source_file)
                if full_file_content is not None:
                    remaining_mutual_content = utils.get_remaining_mutual_content(
                        full_file_content, theorem_stmt, local_context
                    )
            else:
                full_file_path = self.lean_src_dir / repo_name / rel_path
                if full_file_path.exists():
                    full_file_content = full_file_path.read_text(encoding='utf-8')
                    remaining_mutual_content = utils.get_remaining_mutual_content(
                        full_file_content, theorem_stmt, local_context
                    )
        except Exception as e:
            # If we can't get the remaining content, continue without it
            pass

        content = utils.format_generated_lean(
            local_context, theorem_stmt, theorem_proof, aux_lemmas, suffix, remaining_mutual_content
        )

        # Write temp file to the appropriate filesystem
        if use_docker:
            self._docker_write_file(container_new_file, content)
        else:
            with open(new_file_path, 'w', encoding='utf-8') as f:
                f.write(content)

        # Save postprocessed content for debugging if path provided
        if debug_output_path:
            debug_output_path.parent.mkdir(parents=True, exist_ok=True)
            with open(debug_output_path, 'w', encoding='utf-8') as f:
                f.write(content)

        # Check for sorry/admit in generated content (semantic validation)
        incomplete_errors = utils.check_generated_content_for_incomplete_proofs(thm_name, theorem_proof, aux_lemmas)

        # Compile file (mutual stubs can safely have sorry)
        success, compile_error = self.compile_file(lean_root=repo_name, rel_path=path_obj.parent / new_filename)

        # Combine all errors: incomplete first, then compilation
        all_errors = incomplete_errors
        if not success:
            all_errors.append(compile_error)

        # Clean up temp file
        if use_docker:
            self._docker_rm_file(container_new_file)
        else:
            new_file_path.unlink(missing_ok=True)

        if all_errors:
            return False, "\n".join(all_errors)

        return success, ""

    def _docker_exec(self, cmd: list, cwd: Path, timeout: int):
        """Run a command inside the Docker container via `docker exec`."""
        # Map host project_root to container path via path arithmetic
        # (lean_src_dir need not exist on the host)
        repo_name = cwd.relative_to(self.lean_src_dir)
        container_cwd = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}"
        docker_cmd = [
            "docker", "exec", "-w", container_cwd,
            self.docker_container
        ] + cmd
        return subprocess.run(
            docker_cmd,
            capture_output=True,
            text=True,
            timeout=timeout
        )

    def _docker_write_file(self, container_path: str, content: str, timeout: int = 30):
        """Write file content into the Docker container via docker exec."""
        docker_cmd = [
            "docker", "exec", "-i", self.docker_container,
            "tee", container_path
        ]
        return subprocess.run(
            docker_cmd,
            input=content,
            capture_output=True,
            text=True,
            timeout=timeout
        )

    def _docker_read_file(self, container_path: str, timeout: int = 30) -> str | None:
        """Read file content from the Docker container. Returns None if file doesn't exist."""
        docker_cmd = [
            "docker", "exec", self.docker_container,
            "cat", container_path
        ]
        result = subprocess.run(
            docker_cmd,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        if result.returncode != 0:
            return None
        return result.stdout

    def _docker_rm_file(self, container_path: str, timeout: int = 10):
        """Remove a file inside the Docker container."""
        docker_cmd = [
            "docker", "exec", self.docker_container,
            "rm", "-f", container_path
        ]
        subprocess.run(docker_cmd, capture_output=True, timeout=timeout)

    def _run_compile(self, project_root: Path, module_name: str, rel_path: Path, lake_build_okay: bool):
        """Run the appropriate compile command and return (result, early_error).

        If a direct file compile is required and the file doesn't exist, returns (None, error_msg).
        """
        use_docker = self.docker_container is not None
        run = self._docker_exec if use_docker else None

        if lake_build_okay:
            if use_docker:
                # In Docker, deps are pre-built; use `lake env lean` to compile
                # only the single file (avoids `lake build` triggering a full
                # dependency rebuild when source .lean files were cleaned up).
                repo_name = project_root.relative_to(self.lean_src_dir)
                container_file = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}/{rel_path}"
                return self._docker_exec(
                    ["lake", "env", "lean", container_file],
                    project_root, timeout=600
                )
            cmd = ["lake", "build", module_name]
            result = subprocess.run(
                cmd,
                cwd=project_root,
                capture_output=True,
                text=True,
                timeout=600
            )
            return result
        elif "verina" in str(project_root):
            if use_docker:
                repo_name = project_root.relative_to(self.lean_src_dir)
                container_file = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}/{rel_path}"
                return self._docker_exec(
                    ["lake", "env", "lean", container_file],
                    project_root, timeout=600
                )
            file_path = project_root / rel_path
            result = subprocess.run(
                ["lake", "env", "lean", str(file_path.resolve())],
                cwd=project_root,
                capture_output=True,
                text=True,
                timeout=60
            )
            return result
        else:
            if use_docker:
                repo_name = project_root.relative_to(self.lean_src_dir)
                container_file = f"{DOCKER_LEAN_REPOS_DIR}/{repo_name}/{rel_path}"
                return self._docker_exec(
                    ["lake", "env", "lean", container_file],
                    project_root, timeout=600
                )
            file_path = project_root / rel_path
            result = subprocess.run(
                ["lean", str(file_path.resolve())],
                cwd=project_root,
                capture_output=True,
                text=True,
                timeout=60
            )
            return result

    def compile_file(self, lean_root: Path, rel_path: Path, validate_benchmark: bool = False) -> Tuple[bool, str]:
        """
        Compile Lean file and return success status.

        Args:
            lean_root: Path to the Lean project root (where lakefile.lean is)
            rel_path: Relative path to the Lean file (e.g., "ExprEval/Basic.lean")
            validate_benchmark: If True, allow 'sorry' in proofs

        Returns:
            Tuple of (success: bool, error_message: str)
        """
        import subprocess

        # Convert file path from "X/Y/Z.lean" to "X.Y.Z" format for lake build
        module_name = str(rel_path)
        if module_name.endswith('.lean'):
            module_name = module_name[:-5]  # Remove .lean extension
        module_name = module_name.replace('/', '.')

        # Fix for lean-mlir repo: Blase and LeanMLIR libraries have duplicate directory structure
        # e.g., Blase/Blase/AutoStructs/... should be Blase.AutoStructs...
        # not Blase.Blase.AutoStructs...
        if str(lean_root) == 'lean-mlir':
            if module_name.startswith('Blase.Blase.'):
                module_name = module_name.replace('Blase.Blase.', 'Blase.', 1)
            elif module_name.startswith('LeanMLIR.LeanMLIR.'):
                module_name = module_name.replace('LeanMLIR.LeanMLIR.', 'LeanMLIR.', 1)
        if str(lean_root) == "iris-lean":
            if module_name.startswith('src'):
                module_name = module_name.replace('src.', '', 1)

        # Check if project has a lakefile (lakefile.lean or lakefile.toml)
        project_root = self.lean_src_dir / lean_root
        # has_lakefile = (project_root / "lakefile.lean").exists() or (project_root / "lakefile.toml").exists()
        lake_build_okay = (str(lean_root) != "TaPLean" and str(lean_root) != "verified-compiler" and str(lean_root) != "verina")

        # Run compilation command
        try:
            # Convert module name to path format for matching
            expected_file_path = module_name.replace('.', '/') + '.lean'

            # One-time retry if missing file error is detected
            result = self._run_compile(project_root, module_name, rel_path, lake_build_okay)
            # Combine stdout and stderr for analysis
            output = result.stdout + result.stderr

            # Detect missing file error patterns from tool output
            missing_file = ("no such file or directory" in output.lower()) or ("file not found" in output.lower())

            # Check if build failed (non-zero exit or "build failed" message)
            build_failed = result.returncode != 0 or "build failed" in output.lower()

            early_rerun_attempts = 3
            if build_failed and missing_file and early_rerun_attempts > 0:
                # Short delay then retry once
                import time
                time.sleep(0.25)
                result = self._run_compile(project_root, module_name, rel_path, lake_build_okay)
                # Combine stdout and stderr for analysis
                output = result.stdout + result.stderr
                missing_file = ("no such file or directory" in output.lower()) or ("file not found" in output.lower())
                build_failed = result.returncode != 0 or "build failed" in output.lower()
                early_rerun_attempts -= 1

            # Parse text output for errors and warnings
            errors = []

            # Convert module name to path format for matching
            # e.g., "VCVio.OracleComp.Seq" -> "VCVio/OracleComp/Seq.lean"
            expected_file_path = module_name.replace('.', '/') + '.lean'

            # Pattern to match multiple error/warning formats:
            # Format 1: "warning: path/file.lean:line:col: message"
            # Format 2: "path/file.lean:line:col: error: message"
            # Format 3: "error: path/file.lean:line:col: message" (rare but possible)
            # Format 4: "error: path/file.lean:line:col-line:col: message" (range format)
            msg_pattern = re.compile(
                r'(?:^|\n)(error|warning):\s+([^\s:]+?\.lean):(\d+):(\d+):\s*(.+?)(?=\n(?:(?:error|warning):|[^\s:]+?\.lean:\d+:\d+:|$))',
                re.DOTALL | re.MULTILINE
            )

            # Extract errors and warnings, filtering by file path
            for match in msg_pattern.finditer(output):
                msg_type = match.group(1)  # "error" or "warning"
                file_path_in_msg = match.group(2)  # e.g., "././././VCVio/OracleComp/Seq.lean"
                line_num = match.group(3)
                col_num = match.group(4)
                msg_content = match.group(5).strip()

                # Normalize the file path by removing leading "./"
                normalized_path = file_path_in_msg.lstrip('./')

                # Check if this error/warning is from the file we're compiling
                # Match if the expected path is a suffix of the normalized path
                if normalized_path.endswith(expected_file_path):
                    full_msg = f"{file_path_in_msg}:{line_num}:{col_num}: {msg_type}: {msg_content}"

                    if msg_type == "error":
                        errors.append(full_msg)
                    # Ignore sorry warnings - handled syntactically before compilation

            # Check if build failed (non-zero exit or "build failed" message)
            build_failed = result.returncode != 0 or "build failed" in output.lower()

            if build_failed:
                if errors:
                    error_msg = self._format_lake_build_errors(errors)
                else:
                    # Try a multiline path-first parse to avoid truncating continuation lines
                    fallback_block_pattern = re.compile(
                        r'(?:^|\n)([^\s:]+?\.lean):(\d+):(\d+):\s*(warning|error):\s*(.+?)(?=\n(?:(?:error|warning):|[^\s:]+?\.lean:\d+:\d+:|$))',
                        re.DOTALL | re.MULTILINE
                    )
                    block_matches = list(fallback_block_pattern.finditer(output))
                    if block_matches:
                        formatted_lines = []
                        for m in block_matches:
                            file_path_in_msg = m.group(1)
                            line_num = m.group(2)
                            col_num = m.group(3)
                            msg_type = m.group(4).lower()
                            message = m.group(5).strip()

                            normalized_path = file_path_in_msg.lstrip('./')
                            if not normalized_path.endswith(expected_file_path):
                                continue
                            if msg_type == "error":
                                formatted_lines.append(f"Line {line_num}:{col_num} - error: {message}")
                            # Ignore sorry warnings - handled syntactically before compilation

                        if formatted_lines:
                            return False, "\n".join(formatted_lines)

                    # Try to extract just the relevant error lines, not the entire build log
                    # Look for lines with errors without build progress markers
                    error_lines = []
                    for line in output.split('\n'):
                        # Skip build progress lines
                        if re.match(r'^\[\d+/\d+\]', line) or 'Fetching' in line or 'Computing build jobs' in line:
                            continue
                        # Include lines with errors or that look like file paths with line numbers
                        if 'error:' in line.lower() or re.search(r'\.lean:\d+:\d+', line):
                            error_lines.append(line.strip())

                    if error_lines:
                        # Format the extracted error lines nicely
                        formatted_lines = []
                        location_pattern = re.compile(r'error:\s+([^\s:]+?\.lean):(\d+):(\d+)(?:-\d+:\d+)?:\s*(.+)', re.DOTALL)
                        warning_pattern = re.compile(r'warning:\s+([^\s:]+?\.lean):(\d+):(\d+)(?:-\d+:\d+)?:\s*(.+)', re.DOTALL)
                        fallback_pattern = re.compile(r'([^\s:]+?\.lean):(\d+):(\d+):\s*(warning|error):\s*(.+)', re.IGNORECASE | re.DOTALL)
                        for line in error_lines[-10:]:  # Last 10 error-related lines
                            match = location_pattern.search(line)
                            warning_match = warning_pattern.search(line)
                            if match or warning_match:
                                if match:
                                    line_num = match.group(2)
                                    col_num = match.group(3)
                                    message = match.group(4).strip()
                                    formatted_lines.append(f"Line {line_num}:{col_num} - error: {message}")
                                # Ignore sorry warnings - handled syntactically before compilation
                            else:
                                fb_match = fallback_pattern.search(line)
                                if fb_match:
                                    line_num = fb_match.group(2)
                                    col_num = fb_match.group(3)
                                    msg_type = fb_match.group(4).lower()
                                    message = fb_match.group(5).strip()
                                    if msg_type == "error":
                                        formatted_lines.append(f"Line {line_num}:{col_num} - error: {message}")
                                    # Ignore sorry warnings - handled syntactically before compilation
                                else:
                                    # Keep other error lines but clean them up
                                    if line.strip() and not line.startswith('['):
                                        formatted_lines.append(line.strip())
                        error_msg = '\n'.join(formatted_lines) if formatted_lines else "Compilation failed"
                    else:
                        error_msg = "Compilation failed"
                return False, error_msg

            # Note: sorry warnings are now handled syntactically before compilation
            # in verify_proof() via check_generated_content_for_incomplete_proofs()

            # Success: build succeeded with no actual errors
            return True, ""

        except subprocess.TimeoutExpired:
            return False, "Compilation timeout (>300s)"
        except FileNotFoundError:
            return False, "lake command not found. Is Lean installed?"
        except Exception as e:
            return False, f"Compilation error: {str(e)}"

    def _format_lake_build_errors(self, errors: list[str]) -> str:
        """Format lake build error messages into readable string."""
        if not errors:
            return "Unknown compilation error"

        formatted = []
        # Pattern to extract file:line:column: message from lake build errors
        # Example: "ExprEval/Basic.lean:6:50: Unknown identifier `val`"
        # Also handles range format: "file.lean:119:8-119:37: message"
        # Use DOTALL flag to match newlines in the message portion
        location_pattern = re.compile(r'([^:]+):(\d+):(\d+):\s*(.+)', re.DOTALL)

        for err in errors:
            match = location_pattern.search(err)
            if match:
                line = match.group(2)
                column = match.group(3)
                message = match.group(4).strip()
                formatted.append(f"Line {line}:{column} - {message}")
            else:
                # If pattern doesn't match, just use the error as-is
                formatted.append(err.strip())

        return "\n".join(formatted)

    def _format_lean_errors(self, errors: list[Dict[str, Any]]) -> str:
        """Format Lean error messages into readable string (legacy JSON format)."""
        if not errors:
            return "Unknown compilation error"

        formatted = []
        for err in errors:
            line = err.get("pos", {}).get("line", "?")
            column = err.get("pos", {}).get("column", "?")
            message = err.get("data", "")
            formatted.append(f"Line {line}:{column} - {message}")

        return "\n".join(formatted)
