"""Interface to neural theorem provers."""

import asyncio
from google import genai
from google.oauth2 import service_account
from google.genai import types
from anthropic import Anthropic
from pathlib import Path
from typing import Dict, Any, Optional, List
import openai
import os
import utils.utils as utils
import threading
import time
import random
from datetime import datetime
from config.paths import PROJECT_ROOT, RESULTS_DATA_DIR, CONFIGS_DIR, get_debug_prompt_dir, get_debug_output_dir


class RateLimiter:
    """Thread-safe rate limiter for API calls."""

    def __init__(self, requests_per_minute: int = 60):
        """
        Initialize rate limiter.

        Args:
            requests_per_minute: Maximum number of requests allowed per minute
        """
        self.requests_per_minute = requests_per_minute
        self.min_interval = 60.0 / requests_per_minute  # seconds between requests
        self.last_request_time = 0
        self.lock = threading.Lock()

    def acquire(self):
        """Block until a request can be made while respecting rate limits."""
        with self.lock:
            current_time = time.time()
            time_since_last = current_time - self.last_request_time

            if time_since_last < self.min_interval:
                sleep_time = self.min_interval - time_since_last
                time.sleep(sleep_time)

            self.last_request_time = time.time()


class ProverInterface:
    """Unified interface for calling different neural provers."""

    def __init__(self, model_config: Dict[str, Any]):
        """
        Initialize prover with model configuration.

        Args:
            model_config: Dict containing model_name, api_key, etc.
                Example for OpenAI: {
                    "model_name": "openai",
                    "model_id": "gpt-4",
                    "api_key": "sk-...",
                    "rate_limit_rpm": 60  # optional, requests per minute
                }
        """
        self.model_name = model_config.get("model_name")
        self.model_id = model_config.get("model_id")
        self.run_name = model_config.get("run_name", "default_run")
        self.api_key = model_config.get("api_key")

        # Prepare debug directories for prompts and outputs
        self.prompts_dir = get_debug_prompt_dir(self.run_name)
        self.outputs_dir = get_debug_output_dir(self.run_name)
        self.prompts_dir.mkdir(parents=True, exist_ok=True)
        self.outputs_dir.mkdir(parents=True, exist_ok=True)

        # Initialize rate limiter for API-based models
        # Use 60 as default, but allow None to disable rate limiting
        rate_limit_rpm = model_config.get("rate_limit_rpm")
        if rate_limit_rpm is None:
            rate_limit_rpm = 60
        self.rate_limiter = RateLimiter(requests_per_minute=rate_limit_rpm)

        # Initialize API clients based on model_name
        if self.model_name == "openai":
            self.api_key = self.api_key or os.environ.get("OPENAI_API_KEY")
            if not self.api_key:
                raise ValueError("OpenAI API key is not set; provide api_key in config or set OPENAI_API_KEY")
            self.client = openai.OpenAI(api_key=self.api_key, timeout=3600)
        elif self.model_name == "claude":
            self.api_key = self.api_key or os.environ.get("ANTHROPIC_API_KEY")
            if not self.api_key:
                raise ValueError("Anthropic API key is not set; provide api_key in config or set ANTHROPIC_API_KEY")
            self.client = Anthropic(
                api_key=self.api_key,
                timeout=600.0
            )
        elif self.model_name == "gemini":
            self.api_key = self.api_key or os.environ.get("GOOGLE_API_KEY")
            if self.api_key is not None:
                self.client = genai.Client(api_key=self.api_key)
            else:
                KEY_PATH = str(CONFIGS_DIR / "gemini-service-account.json")
                if not Path(KEY_PATH).exists():
                    raise ValueError(
                        "Gemini API key not set and service account file not found. "
                        "Set GOOGLE_API_KEY env var, provide api_key in config, "
                        "or place service account JSON at configs/gemini-service-account.json"
                    )
                SCOPES = ["https://www.googleapis.com/auth/cloud-platform"]
                credentials = service_account.Credentials.from_service_account_file(KEY_PATH, scopes=SCOPES)
                self.client = genai.Client(
                    vertexai=True,
                    project=credentials.project_id,
                    location="global",
                    credentials=credentials
                )
        else:
            raise ValueError(f"Unsupported model_name: {self.model_name}")

    def _log_prompt(self, prompt_text: str) -> str:
        """Persist prompt text and return timestamp used for paired output logging."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        prompt_path = self.prompts_dir / f"{timestamp}.txt"
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(prompt_text)
        return timestamp

    def _log_outputs(self, timestamp: str, outputs: List[str]) -> None:
        """Persist raw model outputs for the matching prompt timestamp."""
        output_path = self.outputs_dir / f"{timestamp}.txt"
        with open(output_path, "w", encoding="utf-8") as f:
            f.write("\n\n".join([str(o) for o in outputs]))

    async def generate_proof(
        self,
        sys_prompt: str,
        user_prompt: str,
        theorem_entry: dict,
        max_tokens: int = 32768,
        temperature: float = 1.0,
        num_samples: int = 1
    ) -> List[str]:
        """
        Generate proof using the configured model.

        Args:
            sys_prompt: System prompt
            user_prompt: User prompt with theorem context
            max_tokens: Maximum tokens to generate
            temperature: Sampling temperature
            num_samples: Number of proof samples to generate

        Returns:
            Generated proof text (single string if num_samples=1, list otherwise)
        """
        if self.model_name == "openai" and self.model_id == "gpt-5.2-pro-2025-12-11":
            return self._call_openai_response(sys_prompt, user_prompt, max_tokens=max_tokens,
                                             temperature=temperature, num_samples=num_samples)
        elif self.model_name == "openai":
            return self._call_openai(sys_prompt, user_prompt, max_tokens=max_tokens,
                                    temperature=temperature, num_samples=num_samples)
        elif self.model_name == "claude":
            return self._call_claude(sys_prompt, user_prompt, max_tokens=max_tokens,
                                   temperature=temperature, num_samples=num_samples)
        elif self.model_name == "gemini":
            return self._call_gemini(sys_prompt, user_prompt, max_tokens=max_tokens,
                                   temperature=temperature, num_samples=num_samples)
        else:
            raise ValueError(f"Unsupported model_name: {self.model_name}")

    def _call_openai_response(self, sys_prompt: str, user_prompt: str, **kwargs) -> List[str]:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        num_samples = kwargs.get("num_samples", 1)
        temperature = kwargs.get("temperature", 1.0)

        timestamp = self._log_prompt(user_prompt)

        def make_api_call():
            max_retries = 10
            retry_delay = 2  # seconds

            for attempt in range(max_retries):
                try:
                    # Respect the shared rate limit across API-based models
                    self.rate_limiter.acquire()

                    print(f"model: {self.model_id}")
                    response = self.client.responses.create(
                        model=self.model_id,
                        input=sys_prompt + "\n\n" + user_prompt
                    )

                    return response.output_text
                except Exception as e:
                    if attempt < max_retries - 1:
                        print(f"API call failed (attempt {attempt + 1}/{max_retries}): {e}")
                        time.sleep(retry_delay)
                    else:
                        print(f"API call failed after {max_retries} attempts: {e}")
                        raise

        results: List[Optional[str]] = [None] * num_samples
        with ThreadPoolExecutor(max_workers=min(8, num_samples)) as executor:
            future_to_idx = {
                executor.submit(make_api_call): idx for idx in range(num_samples)
            }

            for future in as_completed(future_to_idx, timeout=3660):
                idx = future_to_idx[future]
                try:
                    results[idx] = future.result(timeout=3660)
                except Exception as e:
                    print(f"OpenAI API call {idx} failed: {e}")
                    results[idx] = None

        # results is fully populated because each future returns before exiting the context
        finalized_results = [r for r in results if r is not None]

        self._log_outputs(timestamp, finalized_results)
        return finalized_results

    def _call_gemini(self, sys_prompt: str, user_prompt: str, **kwargs) -> List[str]:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        num_samples = kwargs.get("num_samples", 1)
        temperature = kwargs.get("temperature", 1.0)

        # Backoff parameters
        max_retries = 6  # total attempts = max_retries
        base_delay = 1.0
        backoff_factor = 2.0
        max_delay = 32.0

        timestamp = self._log_prompt(user_prompt)

        error_log_path = self.outputs_dir / f"{timestamp}_gemini_errors.log"

        def log_error(attempt, status, retry_after, message):
            """Append structured error info for easier sharing/debugging."""
            with open(error_log_path, "a", encoding="utf-8") as f:
                f.write(
                    f"{datetime.utcnow().isoformat()}Z\t"
                    f"attempt={attempt}/{max_retries}\t"
                    f"status={status}\t"
                    f"retry_after={retry_after}\t"
                    f"model={self.model_id}\t"
                    f"message={message}\n"
                )

        def make_api_call():
            for attempt in range(1, max_retries + 1):
                # Respect the shared rate limit across API-based models
                self.rate_limiter.acquire()

                try:
                    print(f"model: {self.model_id} attempt {attempt}/{max_retries}")
                    response = self.client.models.generate_content(
                        model=self.model_id,
                        contents=user_prompt,
                        config=types.GenerateContentConfig(
                            system_instruction=sys_prompt,
                            temperature=temperature
                        )
                    )

                    return response.text
                except Exception as e:
                    # Extract retry-after if present
                    retry_after = None
                    if hasattr(e, "response") and e.response is not None:
                        # Some transports provide headers dict
                        retry_after = getattr(e.response, "headers", {}).get("Retry-After") if hasattr(e.response, "headers") else None
                    elif hasattr(e, "headers"):
                        retry_after = getattr(e, "headers", {}).get("Retry-After")

                    status = getattr(e, "code", None) or getattr(e, "status", None) or getattr(e, "http_status", None)
                    message = getattr(e, "message", None) or str(e)

                    print(f"Gemini API call failed (attempt {attempt}/{max_retries}): status={status} retry_after={retry_after} error={message}")
                    log_error(attempt, status, retry_after, message)

                    if attempt == max_retries:
                        raise

                    # Determine sleep time
                    if retry_after:
                        try:
                            delay = float(retry_after)
                        except Exception:
                            delay = base_delay * (backoff_factor ** (attempt - 1))
                    else:
                        delay = base_delay * (backoff_factor ** (attempt - 1))

                    delay = min(delay, max_delay)
                    # Add full jitter
                    delay = random.uniform(0.5 * delay, 1.5 * delay)
                    time.sleep(delay)

        results: List[Optional[str]] = [None] * num_samples
        with ThreadPoolExecutor(max_workers=min(8, num_samples)) as executor:
            future_to_idx = {
                executor.submit(make_api_call): idx for idx in range(num_samples)
            }

            for future in as_completed(future_to_idx, timeout=660):
                idx = future_to_idx[future]
                try:
                    results[idx] = future.result(timeout=660)
                except Exception as e:
                    print(f"Gemini API call {idx} failed: {e}")
                    results[idx] = None

        # results is fully populated because each future returns before exiting the context
        finalized_results = [r for r in results if r is not None]

        self._log_outputs(timestamp, finalized_results)
        return finalized_results

    def _call_claude(self, sys_prompt: str, user_prompt: str, **kwargs) -> List[str]:
        from concurrent.futures import ThreadPoolExecutor, as_completed

        api_key = kwargs.get("api_key") or self.api_key
        if not api_key:
            raise ValueError("ANTHROPIC_API_KEY is not set")

        num_samples = kwargs.get("num_samples", 1)
        temperature = kwargs.get("temperature", 1.0)
        max_tokens = kwargs.get("max_tokens", 8192)

        timestamp = self._log_prompt(user_prompt)

        def make_api_call():
            # Respect the shared rate limit across API-based models
            self.rate_limiter.acquire()

            response = self.client.messages.create(
                model=self.model_id,
                system=sys_prompt,
                messages=[{"role": "user", "content": user_prompt}],
                max_tokens=max_tokens,
                temperature=temperature,
            )

            text_parts = []
            for block in response.content:
                if getattr(block, "type", "") == "text":
                    text_parts.append(block.text)
            return "".join(text_parts)

        results: List[Optional[str]] = [None] * num_samples
        with ThreadPoolExecutor(max_workers=min(8, num_samples)) as executor:
            future_to_idx = {
                executor.submit(make_api_call): idx for idx in range(num_samples)
            }

            for future in as_completed(future_to_idx, timeout=660):
                idx = future_to_idx[future]
                try:
                    results[idx] = future.result(timeout=660)
                except Exception as e:
                    print(f"Claude API call {idx} failed: {e}")
                    results[idx] = None

        # results is fully populated because each future returns before exiting the context
        finalized_results = [r for r in results if r is not None]

        self._log_outputs(timestamp, finalized_results)
        return finalized_results

    def _call_openai(self, sys_prompt: str, user_prompt: str, **kwargs) -> List[str]:
        """Call OpenAI models, automatically batching if num_samples > 8."""
        from concurrent.futures import ThreadPoolExecutor, as_completed

        num_samples = kwargs.get("num_samples", 1)
        max_per_call = 8
        timestamp = self._log_prompt(user_prompt)

        # Compute how many batches needed
        batches = (num_samples + max_per_call - 1) // max_per_call

        # Helper function to make a single API call
        def make_api_call(batch_size):
            # Apply rate limiting before making the API call
            self.rate_limiter.acquire()

            response = self.client.chat.completions.create(
                model=self.model_id,
                messages=[
                    {"role": "system", "content": sys_prompt},
                    {"role": "user", "content": user_prompt}
                ],
                n=batch_size,
            )

            # Return results from this batch
            return [choice.message.content for choice in response.choices]

        # Calculate batch sizes
        batch_sizes = []
        remaining = num_samples
        for _ in range(batches):
            n = min(max_per_call, remaining)
            batch_sizes.append(n)
            remaining -= n

        # Parallelize API calls using ThreadPoolExecutor
        all_results = []
        with ThreadPoolExecutor(max_workers=batches) as executor:
            future_to_batch = {
                executor.submit(make_api_call, size): size
                for size in batch_sizes
            }

            for future in as_completed(future_to_batch, timeout=3660):
                try:
                    batch_results = future.result(timeout=3660)
                    all_results.extend(batch_results)
                except Exception as e:
                    print(f"OpenAI batch API call failed: {e}")

        self._log_outputs(timestamp, all_results)

        return all_results
