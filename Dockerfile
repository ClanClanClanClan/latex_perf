# LaTeX Perfectionist — multi-stage OCaml build.
# Produces a minimal runtime image with validators_cli, rest_api_server and
# main_service, plus every data file those executables read at run time.
#
# Runtime data (each located through the env var its loader reads FIRST, so
# the lookup never depends on the working directory the user runs from):
#   specs/rules/rule_contracts.json   Rule_contract_loader  LP_RULE_CONTRACTS_JSON
#                                     (MANDATORY: without it every CLI run
#                                     exits 2 with Rule_contracts_missing —
#                                     the defect of the v27.1.63 image)
#   specs/rules/rules_v3.yaml         Rule_rationale        LP_RULES_YAML
#                                     (--explain and the `# why` lines)
#   governance/rule_remediation.yaml  Rule_rationale        LP_RULE_REMEDIATION_YAML
#   latex-parse/data/*.json           rest_api_server       L0_CATALOGUE_V25R2,
#                                                           L0_CATALOGUE_ARGSAFE
# scripts/tools/docker_smoke.sh asserts each of these from the built image;
# docker-push.yml runs it before any push.

# Stage 1: Build
FROM ocaml/opam:ubuntu-22.04-ocaml-5.1 AS builder

USER root
RUN apt-get update && \
    apt-get install -y --no-install-recommends libgmp-dev pkg-config && \
    rm -rf /var/lib/apt/lists/*

USER opam
WORKDIR /home/opam/src

# Only the executables' dependencies (latex-parse/latex_parse.opam: dune,
# ocaml, re, uutf, yojson). The root opam file also pulls Coq 8.18 for the
# proof tree, which this image never ships; building Coq here only cost time
# and disk (a local build ran out of space compiling coq-core). The opam file
# is copied alone first so this layer is cached across source changes.
COPY --chown=opam:opam latex-parse/latex_parse.opam latex-parse/latex_parse.opam
RUN opam update -y && opam install -y ./latex-parse --deps-only

COPY --chown=opam:opam . .
RUN opam exec -- dune build \
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

# Runtime data (see the header for which loader reads each file).
ARG LP_SHARE=/usr/share/latex-perfectionist
COPY --from=builder /home/opam/src/specs/rules/rule_contracts.json ${LP_SHARE}/specs/rules/rule_contracts.json
COPY --from=builder /home/opam/src/specs/rules/rules_v3.yaml ${LP_SHARE}/specs/rules/rules_v3.yaml
COPY --from=builder /home/opam/src/governance/rule_remediation.yaml ${LP_SHARE}/governance/rule_remediation.yaml
COPY --from=builder /home/opam/src/latex-parse/data/ ${LP_SHARE}/data/

ENV LP_RULE_CONTRACTS_JSON=/usr/share/latex-perfectionist/specs/rules/rule_contracts.json \
    LP_RULES_YAML=/usr/share/latex-perfectionist/specs/rules/rules_v3.yaml \
    LP_RULE_REMEDIATION_YAML=/usr/share/latex-perfectionist/governance/rule_remediation.yaml \
    L0_CATALOGUE_V25R2=/usr/share/latex-perfectionist/data/macro_catalogue.v25r2.json \
    L0_CATALOGUE_ARGSAFE=/usr/share/latex-perfectionist/data/macro_catalogue.argsafe.v25r1.json

COPY scripts/docker_entrypoint.sh /usr/local/bin/lp-serve

EXPOSE 8080

# Default: REST API server on port 8080. lp-serve starts main_service first —
# rest_api_server alone exits 1 ("SIMD service not running"), so the previous
# ENTRYPOINT ["rest_api_server"] could never serve a request.
# For the CLI: docker run --rm -v "$PWD:/w" -w /w --entrypoint validators_cli IMAGE paper.tex
ENTRYPOINT ["lp-serve"]
CMD ["-p", "8080"]
