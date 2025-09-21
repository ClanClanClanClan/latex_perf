#!/usr/bin/env python3
"""
LaTeX Perfectionist v25 - Python Client Library
High-performance LaTeX tokenization via REST API
"""

import json
import requests
from typing import Dict, List, Optional, Union
import time


class LaTeXTokenizer:
    """Client for LaTeX Perfectionist v25 tokenization service."""

    def __init__(self, host: str = "localhost", port: int = 8080, timeout: float = 30.0):
        """
        Initialize the LaTeX tokenizer client.

        Args:
            host: REST API server hostname
            port: REST API server port
            timeout: Request timeout in seconds
        """
        self.base_url = f"http://{host}:{port}"
        self.timeout = timeout
        self.session = requests.Session()

    def tokenize(self, latex_content: str) -> Dict:
        """
        Tokenize LaTeX content using ARM NEON SIMD optimization.

        Args:
            latex_content: LaTeX source code to tokenize

        Returns:
            Dictionary containing tokens and metadata

        Raises:
            ConnectionError: If service is unavailable
            ValueError: If request is invalid
        """
        url = f"{self.base_url}/tokenize"
        payload = {"latex": latex_content}

        try:
            response = self.session.post(
                url,
                json=payload,
                timeout=self.timeout
            )

            if response.status_code == 200:
                return response.json()
            elif response.status_code == 400:
                raise ValueError(f"Invalid request: {response.json().get('error', 'Unknown error')}")
            elif response.status_code == 413:
                raise ValueError("LaTeX content too large (max 10MB)")
            elif response.status_code == 503:
                raise ConnectionError("Tokenization service unavailable")
            else:
                raise Exception(f"Unexpected status code: {response.status_code}")

        except requests.exceptions.RequestException as e:
            raise ConnectionError(f"Failed to connect to tokenizer service: {e}")

    def tokenize_file(self, filepath: str) -> Dict:
        """
        Tokenize LaTeX content from a file.

        Args:
            filepath: Path to LaTeX file

        Returns:
            Dictionary containing tokens and metadata
        """
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        return self.tokenize(content)

    def batch_tokenize(self, documents: List[str], max_workers: int = 4) -> List[Dict]:
        """
        Tokenize multiple LaTeX documents in parallel.

        Args:
            documents: List of LaTeX documents
            max_workers: Maximum parallel requests

        Returns:
            List of tokenization results
        """
        from concurrent.futures import ThreadPoolExecutor, as_completed

        results = [None] * len(documents)

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_to_index = {
                executor.submit(self.tokenize, doc): i
                for i, doc in enumerate(documents)
            }

            for future in as_completed(future_to_index):
                index = future_to_index[future]
                try:
                    results[index] = future.result()
                except Exception as e:
                    results[index] = {"error": str(e)}

        return results

    def health_check(self) -> Dict:
        """
        Check if the tokenization service is healthy.

        Returns:
            Health status dictionary
        """
        url = f"{self.base_url}/health"

        try:
            response = self.session.get(url, timeout=5.0)
            return response.json()
        except:
            return {"status": "unhealthy", "service": "not responding"}

    def get_metrics(self) -> str:
        """
        Get Prometheus metrics from the service.

        Returns:
            Prometheus metrics text
        """
        url = f"{self.base_url}/metrics"

        try:
            response = self.session.get(url, timeout=5.0)
            return response.text
        except:
            return ""

    def benchmark(self, latex_content: str, iterations: int = 100) -> Dict:
        """
        Benchmark tokenization performance.

        Args:
            latex_content: LaTeX content to benchmark
            iterations: Number of iterations

        Returns:
            Performance statistics
        """
        latencies = []
        errors = 0

        for _ in range(iterations):
            start = time.perf_counter()
            try:
                self.tokenize(latex_content)
                latencies.append((time.perf_counter() - start) * 1000)  # ms
            except:
                errors += 1

        if latencies:
            latencies.sort()
            return {
                "iterations": iterations,
                "errors": errors,
                "error_rate": errors / iterations,
                "latency_ms": {
                    "min": latencies[0],
                    "p50": latencies[len(latencies) // 2],
                    "p90": latencies[int(len(latencies) * 0.9)],
                    "p99": latencies[int(len(latencies) * 0.99)],
                    "max": latencies[-1],
                    "mean": sum(latencies) / len(latencies)
                }
            }
        else:
            return {"error": "All requests failed"}

    def close(self):
        """Close the HTTP session."""
        self.session.close()

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()


# Example usage
if __name__ == "__main__":
    # Create tokenizer client
    tokenizer = LaTeXTokenizer()

    # Check health
    health = tokenizer.health_check()
    print(f"Service health: {health}")

    # Tokenize sample LaTeX
    sample_latex = r"""
    \documentclass{article}
    \begin{document}
    \section{Introduction}
    This is a test document with $x^2 + y^2 = z^2$ math.
    \end{document}
    """

    try:
        result = tokenizer.tokenize(sample_latex)
        print(f"Tokenization result: {result}")

        # Benchmark performance
        perf = tokenizer.benchmark(sample_latex, iterations=10)
        print(f"Performance: P50={perf['latency_ms']['p50']:.2f}ms")

    except Exception as e:
        print(f"Error: {e}")

    tokenizer.close()