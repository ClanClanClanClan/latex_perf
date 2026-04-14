# LaTeX Perfectionist v25 — multi-stage OCaml build
# Produces a minimal runtime image with validators_cli + rest_api_server

# Stage 1: Build
FROM ocaml/opam:ubuntu-22.04-ocaml-5.1 AS builder

USER opam
WORKDIR /home/opam/src
COPY --chown=opam:opam . .

RUN opam install -y . --deps-only && \
    opam exec -- dune build \
      latex-parse/src/validators_cli.exe \
      latex-parse/src/rest_api_server.exe \
      latex-parse/src/main_service.exe

# Stage 2: Runtime
FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y --no-install-recommends ca-certificates && \
    rm -rf /var/lib/apt/lists/*

COPY --from=builder /home/opam/src/_build/default/latex-parse/src/validators_cli.exe /usr/local/bin/validators_cli
COPY --from=builder /home/opam/src/_build/default/latex-parse/src/rest_api_server.exe /usr/local/bin/rest_api_server
COPY --from=builder /home/opam/src/_build/default/latex-parse/src/main_service.exe /usr/local/bin/main_service

# Copy macro catalogues for expander
COPY --from=builder /home/opam/src/latex-parse/data/ /usr/share/latex-perfectionist/data/

EXPOSE 8080

# Default: REST API server on port 8080
ENTRYPOINT ["rest_api_server"]
CMD ["-p", "8080"]
