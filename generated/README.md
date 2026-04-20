# generated/

CI-regenerated mirrors. Do not hand-edit.

| File | Source | Regenerator |
|------|--------|-------------|
| `project_facts.json` | `governance/project_facts.yaml` | `scripts/tools/generate_project_facts.py` |

The YAML at `governance/project_facts.yaml` is the authoritative source consumed by `scripts/tools/check_repo_facts.py`. The JSON mirror here is emitted alongside for external tooling that prefers JSON (dashboards, release-notes generators, third-party badges). Per memo §16.1.
