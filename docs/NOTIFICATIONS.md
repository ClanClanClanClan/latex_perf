Notifications (Slack and Email)
===============================

This repo can notify on proof and performance regressions via Slack and email.

Secrets to configure
--------------------

Add these repository secrets (Settings → Secrets and variables → Actions → New repository secret):

- Slack
  - SLACK_WEBHOOK_URL — Incoming Webhook URL for your Slack channel
- Email (via SMTP)
  - SMTP_HOST — SMTP server host (e.g., smtp.sendgrid.net)
  - SMTP_PORT — SMTP server port (e.g., 587)
  - SMTP_USERNAME — SMTP username
  - SMTP_PASSWORD — SMTP password (store securely)
  - EMAIL_FROM — From address (e.g., ci@yourdomain)
  - EMAIL_TO — Comma-separated recipients

Where notifications fire
------------------------

- Proof regressions
  - Workflow: .github/workflows/proof-alert.yml
  - Trigger: completion of “Proof CI (Coq)” with failure
  - Actions: opens GitHub issue (label: proof-regression), Slack/email notifications (if secrets present).

- Performance regressions (nightly)
  - Workflow: .github/workflows/perf-nightly.yml
  - Trigger: scheduled nightly (03:00 UTC) or manual
  - Actions: opens GitHub issue (label: perf-regression), Slack/email notifications (if secrets present), publishes badges/history to gh-pages.

- Performance CI (PR/push) failures
  - Workflow: .github/workflows/perf-ci.yml
  - Trigger: PR/push runs of quick gates
  - Actions: Slack/email notifications on failure (if secrets present).

Notes
-----

- Notifications are optional: if corresponding secrets are unset, steps are skipped.
- Branch protection with required checks is driven by .github/required-status-checks.json and applied by the “Configure Branch Protection” workflow when REPO_ADMIN_TOKEN is set.

