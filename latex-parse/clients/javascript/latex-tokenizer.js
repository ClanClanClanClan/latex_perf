/**
 * LaTeX Perfectionist v25 - JavaScript Client Library
 * High-performance LaTeX tokenization via REST API
 */

class LaTeXTokenizer {
    /**
     * Create a LaTeX tokenizer client
     * @param {string} host - REST API server hostname
     * @param {number} port - REST API server port
     * @param {number} timeout - Request timeout in milliseconds
     */
    constructor(host = 'localhost', port = 8080, timeout = 30000) {
        this.baseUrl = `http://${host}:${port}`;
        this.timeout = timeout;
    }

    /**
     * Tokenize LaTeX content
     * @param {string} latexContent - LaTeX source code to tokenize
     * @returns {Promise<Object>} Tokenization result
     */
    async tokenize(latexContent) {
        const url = `${this.baseUrl}/tokenize`;

        try {
            const controller = new AbortController();
            const timeoutId = setTimeout(() => controller.abort(), this.timeout);

            const response = await fetch(url, {
                method: 'POST',
                headers: {
                    'Content-Type': 'application/json',
                },
                body: JSON.stringify({ latex: latexContent }),
                signal: controller.signal
            });

            clearTimeout(timeoutId);

            if (response.status === 200) {
                return await response.json();
            } else if (response.status === 400) {
                const error = await response.json();
                throw new Error(`Invalid request: ${error.error || 'Unknown error'}`);
            } else if (response.status === 413) {
                throw new Error('LaTeX content too large (max 10MB)');
            } else if (response.status === 503) {
                throw new Error('Tokenization service unavailable');
            } else {
                throw new Error(`Unexpected status code: ${response.status}`);
            }
        } catch (error) {
            if (error.name === 'AbortError') {
                throw new Error('Request timeout');
            }
            throw error;
        }
    }

    /**
     * Tokenize LaTeX content from a file (Node.js only)
     * @param {string} filepath - Path to LaTeX file
     * @returns {Promise<Object>} Tokenization result
     */
    async tokenizeFile(filepath) {
        if (typeof window !== 'undefined') {
            throw new Error('tokenizeFile is only available in Node.js');
        }

        const fs = require('fs').promises;
        const content = await fs.readFile(filepath, 'utf-8');
        return this.tokenize(content);
    }

    /**
     * Tokenize multiple LaTeX documents in parallel
     * @param {string[]} documents - Array of LaTeX documents
     * @param {number} maxConcurrent - Maximum concurrent requests
     * @returns {Promise<Object[]>} Array of tokenization results
     */
    async batchTokenize(documents, maxConcurrent = 4) {
        const results = [];
        const queue = [...documents];
        const inProgress = [];

        while (queue.length > 0 || inProgress.length > 0) {
            // Start new requests up to the limit
            while (inProgress.length < maxConcurrent && queue.length > 0) {
                const doc = queue.shift();
                const promise = this.tokenize(doc)
                    .then(result => ({ success: true, result }))
                    .catch(error => ({ success: false, error: error.message }));
                inProgress.push(promise);
            }

            // Wait for at least one to complete
            if (inProgress.length > 0) {
                const completed = await Promise.race(inProgress);
                const index = inProgress.indexOf(completed);
                inProgress.splice(index, 1);
                results.push(await completed);
            }
        }

        return results;
    }

    /**
     * Check service health
     * @returns {Promise<Object>} Health status
     */
    async healthCheck() {
        const url = `${this.baseUrl}/health`;

        try {
            const response = await fetch(url, {
                method: 'GET',
                timeout: 5000
            });

            return await response.json();
        } catch (error) {
            return {
                status: 'unhealthy',
                service: 'not responding',
                error: error.message
            };
        }
    }

    /**
     * Get Prometheus metrics
     * @returns {Promise<string>} Prometheus metrics text
     */
    async getMetrics() {
        const url = `${this.baseUrl}/metrics`;

        try {
            const response = await fetch(url, {
                method: 'GET',
                timeout: 5000
            });

            return await response.text();
        } catch (error) {
            return '';
        }
    }

    /**
     * Benchmark tokenization performance
     * @param {string} latexContent - LaTeX content to benchmark
     * @param {number} iterations - Number of iterations
     * @returns {Promise<Object>} Performance statistics
     */
    async benchmark(latexContent, iterations = 100) {
        const latencies = [];
        let errors = 0;

        for (let i = 0; i < iterations; i++) {
            const start = performance.now();
            try {
                await this.tokenize(latexContent);
                latencies.push(performance.now() - start);
            } catch (error) {
                errors++;
            }
        }

        if (latencies.length > 0) {
            latencies.sort((a, b) => a - b);

            return {
                iterations,
                errors,
                errorRate: errors / iterations,
                latencyMs: {
                    min: latencies[0],
                    p50: latencies[Math.floor(latencies.length * 0.5)],
                    p90: latencies[Math.floor(latencies.length * 0.9)],
                    p99: latencies[Math.floor(latencies.length * 0.99)],
                    max: latencies[latencies.length - 1],
                    mean: latencies.reduce((a, b) => a + b, 0) / latencies.length
                }
            };
        } else {
            return { error: 'All requests failed' };
        }
    }
}

// Export for Node.js
if (typeof module !== 'undefined' && module.exports) {
    module.exports = LaTeXTokenizer;
}

// Example usage
if (typeof require !== 'undefined' && require.main === module) {
    (async () => {
        const tokenizer = new LaTeXTokenizer();

        // Check health
        const health = await tokenizer.healthCheck();
        console.log('Service health:', health);

        // Tokenize sample LaTeX
        const sampleLatex = `
\\documentclass{article}
\\begin{document}
\\section{Introduction}
This is a test document with $x^2 + y^2 = z^2$ math.
\\end{document}
        `;

        try {
            const result = await tokenizer.tokenize(sampleLatex);
            console.log('Tokenization result:', result);

            // Benchmark performance
            const perf = await tokenizer.benchmark(sampleLatex, 10);
            console.log(`Performance: P50=${perf.latencyMs.p50.toFixed(2)}ms`);

        } catch (error) {
            console.error('Error:', error.message);
        }
    })();
}